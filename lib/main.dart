import 'package:flutter/material.dart';
import 'package:http/http.dart' as http;
import 'package:xml_map_converter/src/types.dart';
import 'package:xml_map_converter/xml_map_converter.dart';
import 'package:provider/provider.dart';

import 'package:html_unescape/html_unescape.dart';

import 'dart:async';

import 'package:audio_service/audio_service.dart';
import 'package:audio_session/audio_session.dart';
//import 'package:audio_service_example/common.dart';
import 'package:just_audio/just_audio.dart';
import 'package:rxdart/rxdart.dart';
import 'dart:typed_data';
import 'dart:io';
import 'dart:ui' as ui;
import 'dart:developer' as developer;
import 'package:crypto/crypto.dart';
import 'dart:convert';
import 'package:path_provider/path_provider.dart';
import 'package:intl/intl.dart';
import 'package:scrollable_positioned_list/scrollable_positioned_list.dart';

import 'package:flutter/services.dart' show rootBundle;

final unescape = HtmlUnescape();

// Returns a hex-encoded SHA-256 hash of a byte list
String imageHash(List<int> bytes) {
  final digest = sha256.convert(bytes);
  return digest.toString();
}

Future<bool> hasInternetConnection() async {
  HttpClient? client;
  final probes = <Uri>[
    Uri.parse('https://clients3.google.com/generate_204'),
    Uri.parse('https://www.cloudflare.com/cdn-cgi/trace'),
    Uri.parse('https://www.msftconnecttest.com/connecttest.txt'),
  ];

  try {
    client = HttpClient()
      ..connectionTimeout = const Duration(seconds: 2)
      ..idleTimeout = const Duration(seconds: 2);

    for (final probe in probes) {
      try {
        final request = await client
            .getUrl(probe)
            .timeout(const Duration(seconds: 2));
        request.followRedirects = true;
        final response =
            await request.close().timeout(const Duration(seconds: 2));
        await response.drain<void>();

        if (response.statusCode >= 200 && response.statusCode < 400) {
          return true;
        }
      } catch (_) {
        // Try next probe endpoint.
      }
    }

    return false;
  } catch (_) {
    return false;
  } finally {
    client?.close(force: true);
  }
}

class PodcastStorage {
  late File _file;
  Map<String, dynamic> podcasts = {};

  Future<void> init() async {
    final dir = await getApplicationDocumentsDirectory();
    _file = File('${dir.path}/podcasts.json');

    if (await _file.exists()) {
      final content = await _file.readAsString();
      podcasts = jsonDecode(content);
    } else {
      // create empty file
      await _file.writeAsString(jsonEncode({}));
    }
  }

  Future<void> save() async {
    await _file.writeAsString(jsonEncode(podcasts));
  }

  void addPodcast(String id, Map<String, dynamic> data) {
    podcasts[id] = data;
    save();
  }

  void removePodcast(String id) {
    podcasts.remove(id);
    save();
  }
}

class MediaState {
  final MediaItem? mediaItem;
  final Duration position;

  MediaState(this.mediaItem, this.position);
}

/// An [AudioHandler] for playing a single item.
class AudioPlayerHandler extends BaseAudioHandler with SeekHandler {
  static const Duration _headsetSeekForward = Duration(seconds: 30);
  static const Duration _headsetSeekBackward = Duration(seconds: 10);
  final _player = AudioPlayer(handleInterruptions: false);
  List<dynamic> _episodes = [];
  int _currentIndex = -1;
  final Map<String, int> _savedPositionsMs = {};
  Duration? _pendingRestorePosition;
  bool _isHandlingCompletion = false;
  Future<void> Function(String audioUrl, String? feedUrl)? onEpisodeCompleted;
  void Function(String message)? onPlaybackError;
  Future<String?> Function(String feedUrl, String audioUrl, bool autoCache)?
      onRequestDownloadAudio;
  Future<void> Function(String feedUrl, String audioUrl, bool onlyAutoCached)?
      onDeleteDownloadedAudio;
  final Set<String> _prefetchTriggeredFor = <String>{};
  Future<void> Function(String audioUrl, int positionMs, String? feedUrl)? onSaveProgress;
  Future<void> Function(MediaItem item)? onEpisodeStarted;
  bool _wasPlayingBeforeInterruption = false;
  DateTime? _lastPeriodicSaveTime;

  /// Called when the app returns to foreground. If we were playing before an
  /// interruption whose end-event was never delivered, resume now.
  void tryResumeAfterInterruption() {
    if (!_wasPlayingBeforeInterruption) return;
    _wasPlayingBeforeInterruption = false;
    AudioSession.instance.then((session) {
      session.setActive(true).then((_) {
        if (!_player.playing && mediaItem.value != null) {
          _player.play();
        }
      });
    });
  }

  String _shortId(String url) {
    if (url.length <= 72) return url;
    return '${url.substring(0, 36)}...${url.substring(url.length - 24)}';
  }

  void _cacheLog(String message) {
    final line = '[LocalCache][Handler] $message';
    developer.log(line, name: 'LocalCache');
  }

  void setSavedPosition(String audioUrl, int positionMs) {
    if (audioUrl.isEmpty) return;
    _savedPositionsMs[audioUrl] = positionMs < 0 ? 0 : positionMs;
  }

  MediaItem? _toMediaItem(dynamic episode) {
    if (episode is MediaItem) return episode;
    if (episode is Map) {
      final map = Map<String, dynamic>.from(episode);
      final id = (map['id'] ?? map['audioUrl'] ?? '').toString();
      if (id.isEmpty) return null;
      final art = map['artUri'];
      Uri? artUri;
      if (art is Uri) {
        artUri = art;
      } else if (art is String && art.isNotEmpty) {
        artUri = Uri.tryParse(art);
      }
      return MediaItem(
        id: id,
        album: (map['album'] ?? map['podcastTitle'] ?? 'Podcast').toString(),
        title: (map['title'] ?? 'Untitled').toString(),
        artist: (map['artist'] ?? 'Unknown').toString(),
        artUri: artUri,
        extras: {
          'lastPositionMs': map['lastPositionMs'] ?? 0,
          'played': map['played'] ?? false,
          'feedUrl': map['feedUrl'] ?? '',
          'localAudioPath': map['localAudioPath'] ?? '',
          'autoCachedAudio': map['autoCachedAudio'] ?? false,
        },
      );
    }
    return null;
  }

  /// Initialise our audio handler.
  AudioPlayerHandler() {
    // Forward just_audio state changes to audio_service
    _player.playbackEventStream.map(_transformEvent).pipe(playbackState);
    _player.durationStream.listen((duration) {
      if (duration == null || !mediaItem.hasValue) return;
      final current = mediaItem.value;
      if (current == null) return;
      if (current.duration != duration) {
        mediaItem.add(current.copyWith(duration: duration));
      }
    });
    _player.positionStream.listen(_maybePrefetchNext);
    // Auto-next
    _player.processingStateStream.listen((state) {
      if (state == ProcessingState.completed) {
        _handleEpisodeCompleted();
      }
    });
    // Save progress on pause/stop (lock screen, Bluetooth, media controls, manual)
    _player.playingStream.listen((isPlaying) {
      _onPlayingStateChanged(isPlaying);
    });
    // Handle interruptions and headphones from within the audio service so it
    // works reliably even when the app is backgrounded or the phone is locked.
    // just_audio's built-in handling is disabled (handleInterruptions: false)
    // to prevent double-handling race conditions where just_audio pauses the
    // player before we can read the playing state.
    AudioSession.instance.then((session) {
      session.interruptionEventStream.listen((event) {
        if (event.begin) {
          // Read playing state BEFORE any pause — we are the sole handler.
          _wasPlayingBeforeInterruption = _player.playing;
          if (_wasPlayingBeforeInterruption) {
            _player.pause();
          }
        } else {
          // Resume for all interruption types (pause, duck, unknown).
          // For a podcast app we always want to resume after any interruption.
          if (_wasPlayingBeforeInterruption) {
            // Re-activate the audio session to re-request audio focus,
            // then resume playback after a short settle delay.
            // Keep _wasPlayingBeforeInterruption true until the delay fires
            // so a new interruption begin during the delay cancels the resume.
            session.setActive(true).then((_) {
              Future.delayed(const Duration(milliseconds: 500), () {
                if (_wasPlayingBeforeInterruption && !_player.playing) {
                  _player.play();
                }
                _wasPlayingBeforeInterruption = false;
              });
            });
          }
        }
      });
      // Pause when headphones are unplugged (e.g. Bluetooth disconnects)
      session.becomingNoisyEventStream.listen((_) {
        _wasPlayingBeforeInterruption = false;
        _player.pause();
      });
    });
  }

  Future<void> _onPlayingStateChanged(bool isPlaying) async {
    if (isPlaying) return; // Only handle pause/stop
    await _saveCurrentProgress();
  }

  Future<void> _saveCurrentProgress() async {
    final current = mediaItem.value;
    if (current == null || onSaveProgress == null) return;

    try {
      final position = _player.position;
      final feedUrl = current.extras?['feedUrl']?.toString() ?? '';
      await onSaveProgress!(
        current.id,
        position.inMilliseconds,
        feedUrl.isNotEmpty ? feedUrl : null,
      );
    } catch (e) {
      _cacheLog('Save progress failed: $e');
    }
  }

  bool _isAutoCached(MediaItem item) {
    final raw = item.extras?['autoCachedAudio'];
    if (raw is bool) return raw;
    if (raw is String) return raw.toLowerCase() == 'true';
    return false;
  }

  void _setEpisodeLocalPath(
    String audioUrl,
    String localPath, {
    required bool autoCachedAudio,
  }) {
    for (int i = 0; i < _episodes.length; i++) {
      final entry = _episodes[i];
      final media = _toMediaItem(entry);
      if (media == null || media.id != audioUrl) continue;

      if (entry is MediaItem) {
        _episodes[i] = entry.copyWith(
          extras: {
            ...?entry.extras,
            'localAudioPath': localPath,
            'autoCachedAudio': autoCachedAudio,
          },
        );
      } else if (entry is Map) {
        entry['localAudioPath'] = localPath;
        entry['autoCachedAudio'] = autoCachedAudio;
      }
      break;
    }
  }

  AudioSource _audioSourceForMediaItem(MediaItem item) {
    final localAudioPath = (item.extras?['localAudioPath'] ?? '').toString();
    final hasLocalAudio =
        localAudioPath.isNotEmpty && File(localAudioPath).existsSync();

    if (hasLocalAudio) {
      return AudioSource.uri(Uri.file(localAudioPath));
    }

    return AudioSource.uri(
      Uri.parse(item.id.replaceAll('&amp;', '&')),
      headers: {
        'User-Agent': 'UlticastPodcastApp/1.0',
        'Accept': '*/*',
        'Referer': 'https://www.patreon.com/',
      },
    );
  }

  Future<void> restorePausedEpisode(
    MediaItem item, {
    Duration initialPosition = Duration.zero,
  }) async {
    _episodes = <dynamic>[item];
    _currentIndex = 0;
    _savedPositionsMs[item.id] =
        initialPosition.inMilliseconds < 0 ? 0 : initialPosition.inMilliseconds;
    _pendingRestorePosition = initialPosition;

    queue.add(<MediaItem>[item]);
    mediaItem.add(item);
  }

  void _maybePrefetchNext(Duration position) {
    // Periodic progress save every 30 seconds while playing.
    // This ensures progress is saved even if pause events are missed
    // (e.g., phone call while backgrounded, OS-level audio interruptions).
    if (_player.playing) {
      final now = DateTime.now();
      if (_lastPeriodicSaveTime == null ||
          now.difference(_lastPeriodicSaveTime!) >= const Duration(seconds: 30)) {
        _lastPeriodicSaveTime = now;
        _saveCurrentProgress(); // fire-and-forget
      }
    }

    final current = mediaItem.value;
    if (current == null) return;
    if (_prefetchTriggeredFor.contains(current.id)) return;

    final duration = _player.duration;
    if (duration == null || duration <= Duration.zero) return;
    final remaining = duration - position;
    if (remaining > const Duration(minutes: 10)) return;

    _prefetchTriggeredFor.add(current.id);
    final nextIndex = _currentIndex + 1;
    if (nextIndex < 0 || nextIndex >= _episodes.length) return;

    final nextItem = _toMediaItem(_episodes[nextIndex]);
    if (nextItem == null) return;

    final nextFeed = nextItem.extras?['feedUrl']?.toString() ?? '';
    final nextLocalPath = (nextItem.extras?['localAudioPath'] ?? '').toString();
    if (nextFeed.isEmpty) return;
    if (nextLocalPath.isNotEmpty && File(nextLocalPath).existsSync()) {
      _cacheLog(
        'Prefetch skipped (already local): ${_shortId(nextItem.id)} path=$nextLocalPath',
      );
      return;
    }
    if (onRequestDownloadAudio == null) return;

    _cacheLog(
      'Prefetch trigger for next episode: ${_shortId(nextItem.id)}; remaining=${remaining.inSeconds}s',
    );

    onRequestDownloadAudio!(nextFeed, nextItem.id, true).then((localPath) {
      if (localPath == null || localPath.isEmpty) {
        _cacheLog('Prefetch did not return a local file: ${_shortId(nextItem.id)}');
        return;
      }
      _setEpisodeLocalPath(
        nextItem.id,
        localPath,
        autoCachedAudio: true,
      );
      _cacheLog(
        'Prefetch complete: ${_shortId(nextItem.id)} saved at $localPath',
      );
    }).catchError((e) {
      _cacheLog('Prefetch failed for ${_shortId(nextItem.id)}: $e');
    });
  }

  void _startBackgroundDownloadForCurrent(
    MediaItem item,
    String feedUrl,
  ) {
    if (onRequestDownloadAudio == null) return;

    _cacheLog('Background download started while streaming: ${_shortId(item.id)}');

    onRequestDownloadAudio!(feedUrl, item.id, true).then((localPath) async {
      if (localPath == null || localPath.isEmpty) {
        _cacheLog(
          'Background download returned no local file: ${_shortId(item.id)}',
        );
        return;
      }

      _cacheLog(
        'Background download completed: ${_shortId(item.id)} saved at $localPath',
      );

      _setEpisodeLocalPath(item.id, localPath, autoCachedAudio: true);

      final active = mediaItem.value;
      if (active == null || active.id != item.id) {
        _cacheLog('Switch skipped, episode is no longer active: ${_shortId(item.id)}');
        return;
      }
      if (_player.processingState == ProcessingState.completed) {
        _cacheLog('Switch skipped, episode already completed: ${_shortId(item.id)}');
        return;
      }

      final currentLocalPath = (active.extras?['localAudioPath'] ?? '').toString();
      if (currentLocalPath.isNotEmpty && File(currentLocalPath).existsSync()) {
        _cacheLog(
          'Switch skipped, active episode already local: ${_shortId(item.id)} path=$currentLocalPath',
        );
        return;
      }

      final currentPosition = _player.position;
      final wasPlaying = _player.playing;

      _cacheLog(
        'Switching active playback to local source: ${_shortId(item.id)} at ${currentPosition.inSeconds}s',
      );

      try {
        await _player.setAudioSource(
          AudioSource.uri(Uri.file(localPath)),
          initialPosition: currentPosition,
        );
        mediaItem.add(
          active.copyWith(
            extras: {
              ...?active.extras,
              'localAudioPath': localPath,
              'autoCachedAudio': true,
            },
          ),
        );
        if (wasPlaying) {
          await _player.play();
        }

        _cacheLog(
          'Switched to local playback: ${_shortId(item.id)} (resumed=${wasPlaying ? 'playing' : 'paused'})',
        );
      } catch (e) {
        _cacheLog('Failed to switch to local source: $e');
      }
    }).catchError((e) {
      _cacheLog('Background download failed: $e');
    });
  }

  bool _isMarkedPlayed(MediaItem item) {
    final raw = item.extras?['played'];
    if (raw is bool) return raw;
    if (raw is String) return raw.toLowerCase() == 'true';
    return false;
  }

  void _markQueueEpisodePlayedAt(int index) {
    if (index < 0 || index >= _episodes.length) return;
    final entry = _episodes[index];
    if (entry is MediaItem) {
      final updatedExtras = <String, dynamic>{
        ...?entry.extras,
        'played': true,
        'lastPositionMs': 0,
      };
      _episodes[index] = entry.copyWith(extras: updatedExtras);
    } else if (entry is Map) {
      entry['played'] = true;
      entry['lastPositionMs'] = 0;
    }

    queue.add(
      _episodes
          .map(_toMediaItem)
          .whereType<MediaItem>()
          .toList(),
    );
  }

  Future<void> _handleEpisodeCompleted() async {
    if (_isHandlingCompletion) return;
    _isHandlingCompletion = true;

    try {
      final completedItem = mediaItem.value;
      if (completedItem != null) {
        _savedPositionsMs[completedItem.id] = 0;
        _markQueueEpisodePlayedAt(_currentIndex);
        if (onEpisodeCompleted != null) {
          final feedUrl = completedItem.extras?['feedUrl']?.toString();
          try {
            await onEpisodeCompleted!(completedItem.id, feedUrl);
          } catch (e) {
            _cacheLog('onEpisodeCompleted callback error: $e');
          }
        }
      }

      final startNextIndex = _currentIndex + 1;
      if (_episodes.isEmpty || startNextIndex >= _episodes.length) {
        await stop();
        return;
      }

      var targetIndex = startNextIndex;
      while (targetIndex < _episodes.length) {
        final candidate = _toMediaItem(_episodes[targetIndex]);
        if (candidate == null) {
          targetIndex++;
          continue;
        }
        if (!_isMarkedPlayed(candidate)) {
          break;
        }
        targetIndex++;
      }

      if (targetIndex >= _episodes.length) {
        await stop();
        return;
      }

      final nextItem = _toMediaItem(_episodes[targetIndex]);
      if (nextItem == null) {
        await stop();
        return;
      }

      _currentIndex = targetIndex;
      final resumeMs = _savedPositionsMs[nextItem.id] ??
          (() {
            final rawMs = nextItem.extras?['lastPositionMs'];
            if (rawMs is int) return rawMs;
            if (rawMs is String) return int.tryParse(rawMs) ?? 0;
            return 0;
          })();

      await playEpisode(
        nextItem,
        initialPosition: resumeMs > 0 ? Duration(milliseconds: resumeMs) : null,
      );
    } catch (e) {
      _cacheLog('Episode completion handler error: $e');
    } finally {
      _isHandlingCompletion = false;
    }
  }

  /// Play a specific episode (dynamic MediaItem)
  Future<void> playEpisode(MediaItem item, {Duration? initialPosition}) async {
    final previousItem = mediaItem.value;
    final queueIndex = _episodes.indexWhere((ep) {
      final media = _toMediaItem(ep);
      return media?.id == item.id;
    });
    if (queueIndex >= 0) {
      _currentIndex = queueIndex;
    }

    mediaItem.add(item); // broadcast to UI
    final localAudioPath = (item.extras?['localAudioPath'] ?? '').toString();
    final hasLocalAudio =
        localAudioPath.isNotEmpty && File(localAudioPath).existsSync();
    final feedUrl = item.extras?['feedUrl']?.toString() ?? '';

    _cacheLog(
      'Play request: ${_shortId(item.id)} source=${hasLocalAudio ? 'local' : 'stream'}',
    );

    if (!hasLocalAudio) {
      final online = await hasInternetConnection();
      if (!online) {
        _cacheLog('Playback blocked (offline, no local file): ${_shortId(item.id)}');
        onPlaybackError?.call(
          "Can't play this episode offline. Download it first while online.",
        );
        return;
      }
    }

    final audioSource = hasLocalAudio
        ? AudioSource.uri(Uri.file(localAudioPath))
        : AudioSource.uri(
            Uri.parse(item.id.replaceAll('&amp;', '&')),
            headers: {
              "User-Agent": "UlticastPodcastApp/1.0",
              "Accept": "*/*",
              "Referer": "https://www.patreon.com/",
            },
          );

    try {
      await _player.setAudioSource(audioSource, initialPosition: initialPosition);
      _pendingRestorePosition = null;
      play();
    } catch (e) {
      _pendingRestorePosition = null;
      _cacheLog('Playback failed for ${_shortId(item.id)}: $e');
      onPlaybackError?.call(
        "Can't play this episode right now. Check your internet connection.",
      );
      return;
    }

    // Notify that a new episode has started so storage can update the
    // 'last played' record. This is critical for correct restore after
    // background auto-advance when the app is killed.
    try {
      onEpisodeStarted?.call(item);
    } catch (e) {
      _cacheLog('onEpisodeStarted callback error: $e');
    }

    if (!hasLocalAudio && feedUrl.isNotEmpty) {
      _startBackgroundDownloadForCurrent(item, feedUrl);
    }

    if (previousItem != null && previousItem.id != item.id) {
      final previousFeed = previousItem.extras?['feedUrl']?.toString() ?? '';
      if (previousFeed.isNotEmpty && _isAutoCached(previousItem)) {
        _cacheLog(
          'Auto-delete previous auto-cached episode: ${_shortId(previousItem.id)}',
        );
        onDeleteDownloadedAudio?.call(previousFeed, previousItem.id, true);
        _setEpisodeLocalPath(previousItem.id, '', autoCachedAudio: false);
      }
    }
  }

  Future<void> setEpisodeQueue(
    List<MediaItem> episodes, {
    int initialIndex = 0,
  }) async {
    _episodes = List<dynamic>.from(episodes);
    _savedPositionsMs.clear();
    for (final item in episodes) {
      final rawMs = item.extras?['lastPositionMs'];
      final ms = rawMs is int
          ? rawMs
          : (rawMs is String ? int.tryParse(rawMs) ?? 0 : 0);
      _savedPositionsMs[item.id] = ms;
    }
    if (_episodes.isEmpty) {
      _currentIndex = -1;
      queue.add(const <MediaItem>[]);
      return;
    }

    _currentIndex = initialIndex.clamp(0, _episodes.length - 1);
    queue.add(
      _episodes
          .map(_toMediaItem)
          .whereType<MediaItem>()
          .toList(),
    );
  }

  Future<void> syncEpisodeQueuePreservingCurrent(
    List<MediaItem> episodes,
  ) async {
    final currentItem = mediaItem.value;
    final nextEpisodes = List<dynamic>.from(episodes);

    final currentId = currentItem?.id ?? '';
    final currentExistsInQueue = currentId.isNotEmpty &&
        nextEpisodes.any((ep) {
          final media = _toMediaItem(ep);
          return media?.id == currentId;
        });
    if (currentItem != null && !currentExistsInQueue) {
      nextEpisodes.insert(0, currentItem);
    }

    _episodes = nextEpisodes;

    final nextSavedPositions = <String, int>{};
    for (final entry in _episodes) {
      final item = _toMediaItem(entry);
      if (item == null) continue;
      final rawMs = item.extras?['lastPositionMs'];
      final extrasMs = rawMs is int
          ? rawMs
          : (rawMs is String ? int.tryParse(rawMs) ?? 0 : 0);
      nextSavedPositions[item.id] = _savedPositionsMs[item.id] ?? extrasMs;
    }
    _savedPositionsMs
      ..clear()
      ..addAll(nextSavedPositions);

    if (_episodes.isEmpty) {
      _currentIndex = -1;
      queue.add(const <MediaItem>[]);
      return;
    }

    final currentQueueIndex = currentId.isEmpty
        ? -1
        : _episodes.indexWhere((ep) {
            final media = _toMediaItem(ep);
            return media?.id == currentId;
          });

    if (currentQueueIndex >= 0) {
      _currentIndex = currentQueueIndex;
    } else if (_currentIndex < 0 || _currentIndex >= _episodes.length) {
      _currentIndex = 0;
    }

    queue.add(
      _episodes
          .map(_toMediaItem)
          .whereType<MediaItem>()
          .toList(),
    );
  }

  Future<void> setAudioSources(
    List<AudioSource> sources, {
    int initialIndex = 0,
    Duration initialPosition = Duration.zero,
    bool preload = false,
  }) async {
    await _player.setAudioSources(
      sources,
      initialIndex: initialIndex,
      initialPosition: initialPosition,
      preload: false,
    );
  }

  @override
  Future<void> play() async {
    final current = mediaItem.value;
    if (_player.audioSource == null && current != null) {
      try {
        await _player.setAudioSource(
          _audioSourceForMediaItem(current),
          initialPosition: _pendingRestorePosition,
        );
        _pendingRestorePosition = null;
      } catch (e) {
        _cacheLog('Resume prepare failed for ${_shortId(current.id)}: $e');
        onPlaybackError?.call(
          "Can't resume this episode right now. Check your internet connection.",
        );
        return;
      }
    } else if (_player.audioSource == null) {
      return;
    }
    await _player.play();
  }

  @override
  Future<void> pause() async {
    await _saveCurrentProgress();
    await _player.pause();
  }

  @override
  Future<void> seek(Duration position) => _player.seek(position);

  @override
  Future<void> stop() async {
    await _saveCurrentProgress();
    await _player.stop();
    _pendingRestorePosition = null;
    _currentIndex = -1;
    mediaItem.add(null);
  }

  @override
  Future<void> skipToPrevious() async {
    final target = _player.position - _headsetSeekBackward;
    await seek(target < Duration.zero ? Duration.zero : target);
  }

  Future<void> skipToPreviousEpisode() async {
    if (_episodes.isEmpty) return;
    final prevIndex = _currentIndex - 1;
    if (prevIndex < 0 || prevIndex >= _episodes.length) return;
    final previousItem = _toMediaItem(_episodes[prevIndex]);
    if (previousItem == null) return;
    _currentIndex = prevIndex;
    final resumeMs = _savedPositionsMs[previousItem.id] ??
        (() {
          final rawMs = previousItem.extras?['lastPositionMs'];
          if (rawMs is int) return rawMs;
          if (rawMs is String) return int.tryParse(rawMs) ?? 0;
          return 0;
        })();
    await playEpisode(
      previousItem,
      initialPosition: resumeMs > 0 ? Duration(milliseconds: resumeMs) : null,
    );
  }

  @override
  Future<void> skipToNext() async {
    final duration = _player.duration;
    final rawTarget = _player.position + _headsetSeekForward;
    final target = duration != null && duration > Duration.zero
        ? (rawTarget > duration ? duration : rawTarget)
        : rawTarget;
    await seek(target);
  }

  Future<void> skipToNextEpisode() async {
    if (_episodes.isEmpty) return;
    final nextIndex = _currentIndex + 1;
    if (nextIndex < 0 || nextIndex >= _episodes.length) return;
    final nextItem = _toMediaItem(_episodes[nextIndex]);
    if (nextItem == null) return;
    _currentIndex = nextIndex;
    final resumeMs = _savedPositionsMs[nextItem.id] ??
        (() {
          final rawMs = nextItem.extras?['lastPositionMs'];
          if (rawMs is int) return rawMs;
          if (rawMs is String) return int.tryParse(rawMs) ?? 0;
          return 0;
        })();
    await playEpisode(
      nextItem,
      initialPosition: resumeMs > 0 ? Duration(milliseconds: resumeMs) : null,
    );
  }

  /// Transform a just_audio event into an audio_service state.
  PlaybackState _transformEvent(PlaybackEvent event) {
    return PlaybackState(
      controls: [
        MediaControl.rewind,
        if (_player.playing) MediaControl.pause else MediaControl.play,
        MediaControl.stop,
        MediaControl.fastForward,
      ],
      systemActions: const {
        MediaAction.seek,
        MediaAction.seekForward,
        MediaAction.seekBackward,
      },
      androidCompactActionIndices: const [0, 1, 3],
      processingState: const {
        ProcessingState.idle: AudioProcessingState.idle,
        ProcessingState.loading: AudioProcessingState.loading,
        ProcessingState.buffering: AudioProcessingState.buffering,
        ProcessingState.ready: AudioProcessingState.ready,
        ProcessingState.completed: AudioProcessingState.completed,
      }[_player.processingState]!,
      playing: _player.playing,
      updatePosition: _player.position,
      bufferedPosition: _player.bufferedPosition,
      speed: _player.speed,
      queueIndex: event.currentIndex,
    );
  }
}

class MediaControlOverlay extends StatelessWidget {
  Future<void> _saveCurrentPositionAndSkip(
    BuildContext context,
    MediaItem mediaItem,
    PlaybackState? playbackState,
    bool next,
  ) async {
    final provider = Provider.of<PodcastAppState>(context, listen: false);
    final position = playbackState?.updatePosition ?? Duration.zero;
    await provider.savePlaybackProgressByAudioUrl(
      mediaItem.id,
      position.inMilliseconds,
      durationMs: mediaItem.duration?.inMilliseconds,
      feedUrl: mediaItem.extras?['feedUrl']?.toString(),
    );
    if (next) {
      await _audioHandler.skipToNext();
    } else {
      await _audioHandler.skipToPrevious();
    }
  }

  void _openNowPlaying(BuildContext context, MediaItem currentItem) {
    final podcastState = Provider.of<PodcastAppState>(context, listen: false);

    Map<String, dynamic>? matchedPodcast;
    Map<String, dynamic>? matchedEpisode;

    for (final podcast in podcastState.podcasts.values) {
      final episodes = (podcast['episodes'] as List<dynamic>? ?? const []);
      for (final ep in episodes) {
        if (ep is! Map) continue;
        final episodeMap = Map<String, dynamic>.from(ep);
        final audioUrl = (episodeMap['audioUrl'] ?? '').toString();
        if (audioUrl == currentItem.id) {
          matchedPodcast = podcast;
          matchedEpisode = episodeMap;
          break;
        }
      }
      if (matchedEpisode != null) break;
    }

    if (matchedPodcast == null || matchedEpisode == null) {
      final fallbackEpisode = {
        'title': currentItem.title,
        'audioUrl': currentItem.id,
        'imageUrl': currentItem.artUri?.toString(),
        'localImagePath':
            currentItem.artUri != null && currentItem.artUri!.scheme == 'file'
                ? currentItem.artUri!.toFilePath()
                : null,
      };
      matchedEpisode = fallbackEpisode;
      matchedPodcast = {
        'title': currentItem.album ?? 'Podcast',
        'author': currentItem.artist,
        'episodes': [fallbackEpisode],
      };
    }

    _appNavigatorKey.currentState?.pushNamed(
      '/audio',
      arguments: {
        'podcast': matchedPodcast,
        'episode': matchedEpisode,
        'play': false,
      },
    );
  }

  @override
  Widget build(BuildContext context) {
    return StreamBuilder<PlaybackState>(
      stream: _audioHandler.playbackState,
      builder: (context, playbackSnapshot) {
        final playbackState = playbackSnapshot.data;
        return StreamBuilder<MediaItem?>(
          stream: _audioHandler.mediaItem,
          builder: (context, mediaSnapshot) {
            final mediaItem = mediaSnapshot.data;
            if (mediaItem == null) return const SizedBox.shrink();

            final isPlaying = playbackState?.playing ?? false;
            final screenWidth = MediaQuery.of(context).size.width;

            return Positioned(
              left: 0,
              right: 0,
              bottom: 0,
              child: GestureDetector(
                behavior: HitTestBehavior.opaque,
                onTap: () => _openNowPlaying(context, mediaItem),
                child: Container(
                  width: screenWidth,
                  color: Colors.black87,
                  padding: EdgeInsets.fromLTRB(
                    12,
                    8,
                    12,
                    8 + MediaQuery.of(context).viewPadding.bottom,
                  ),
                  child: Column(
                    mainAxisSize: MainAxisSize.min,
                    children: [
                      Row(
                        crossAxisAlignment: CrossAxisAlignment.center,
                        children: [
                          if (mediaItem.artUri != null)
                            SizedBox(
                              width: 48,
                              height: 48,
                              child: _OverlayArtwork(artUri: mediaItem.artUri!),
                            )
                          else
                            Container(width: 48, height: 48, color: Colors.grey),

                          const SizedBox(width: 10),

                          Flexible(
                            child: Column(
                              crossAxisAlignment: CrossAxisAlignment.start,
                              mainAxisSize: MainAxisSize.min,
                              children: [
                                SizedBox(
                                  height: 20,
                                  child: _LoopingMarqueeText(
                                    text: mediaItem.title,
                                    style: const TextStyle(
                                      color: Colors.white,
                                      fontSize: 14,
                                      fontWeight: FontWeight.w600,
                                    ),
                                  ),
                                ),
                                if ((mediaItem.album ?? '').isNotEmpty)
                                  Text(
                                    mediaItem.album ?? '',
                                    style: const TextStyle(color: Colors.white70, fontSize: 12),
                                    maxLines: 1,
                                    overflow: TextOverflow.ellipsis,
                                  ),
                              ],
                            ),
                          ),

                          const SizedBox(width: 8),

                          SizedBox(
                            width: 40,
                            height: 40,
                            child: IconButton(
                              padding: EdgeInsets.zero,
                              iconSize: 20,
                              icon: const Icon(Icons.skip_previous, color: Colors.white),
                              onPressed: () => _saveCurrentPositionAndSkip(
                                context,
                                mediaItem,
                                playbackState,
                                false,
                              ),
                            ),
                          ),

                          SizedBox(
                            width: 40,
                            height: 40,
                            child: IconButton(
                              padding: EdgeInsets.zero,
                              iconSize: 22,
                              icon: Icon(isPlaying ? Icons.pause : Icons.play_arrow, color: Colors.white),
                              onPressed: () async {
                                if (isPlaying) {
                                  final provider = Provider.of<PodcastAppState>(
                                    context,
                                    listen: false,
                                  );
                                  final position = playbackState?.updatePosition ?? Duration.zero;
                                  await provider.savePlaybackProgressByAudioUrl(
                                    mediaItem.id,
                                    position.inMilliseconds,
                                    durationMs: mediaItem.duration?.inMilliseconds,
                                    feedUrl: mediaItem.extras?['feedUrl']?.toString(),
                                  );
                                  await provider.rememberLastPlayedEpisode(
                                    mediaItem,
                                    position.inMilliseconds,
                                  );
                                  await _audioHandler.pause();
                                } else {
                                  await _audioHandler.play();
                                }
                              },
                            ),
                          ),

                          SizedBox(
                            width: 40,
                            height: 40,
                            child: IconButton(
                              padding: EdgeInsets.zero,
                              iconSize: 20,
                              icon: const Icon(Icons.skip_next, color: Colors.white),
                              onPressed: () => _saveCurrentPositionAndSkip(
                                context,
                                mediaItem,
                                playbackState,
                                true,
                              ),
                            ),
                          ),
                        ],
                      ),
                      if (mediaItem.duration != null && mediaItem.duration! > Duration.zero) ...[
                        const SizedBox(height: 6),
                        LinearProgressIndicator(
                          minHeight: 2,
                          backgroundColor: Colors.white24,
                          valueColor: const AlwaysStoppedAnimation<Color>(Colors.white),
                          value: ((playbackState?.updatePosition.inMilliseconds ?? 0) /
                                  mediaItem.duration!.inMilliseconds)
                              .clamp(0.0, 1.0),
                        ),
                      ],
                    ],
                  ),
                ),
              ),
            );
          },
        );
      },
    );
  }
}

class _OverlayArtwork extends StatelessWidget {
  final Uri artUri;

  const _OverlayArtwork({required this.artUri});

  @override
  Widget build(BuildContext context) {
    final isOffline = context.select<PodcastAppState, bool>((s) => s.isOffline);
    if (artUri.scheme == 'file') {
      return Image.file(
        File.fromUri(artUri),
        fit: BoxFit.cover,
        errorBuilder: (c, e, s) => Container(color: Colors.grey),
      );
    }

    if (isOffline) {
      return Container(
        color: Colors.grey.shade400,
        alignment: Alignment.center,
        child: const Icon(Icons.cloud_off, color: Colors.white),
      );
    }

    return Image.network(
      artUri.toString(),
      fit: BoxFit.cover,
      errorBuilder: (c, e, s) => Container(color: Colors.grey),
    );
  }
}

class _LoopingMarqueeText extends StatefulWidget {
  final String text;
  final TextStyle style;

  const _LoopingMarqueeText({required this.text, required this.style});

  @override
  State<_LoopingMarqueeText> createState() => _LoopingMarqueeTextState();
}

class _LoopingMarqueeTextState extends State<_LoopingMarqueeText>
    with SingleTickerProviderStateMixin {
  static const double _pixelsPerSecond = 30;
  static const double _gap = 32;

  late final AnimationController _controller;
  ui.TextDirection _textDirection = ui.TextDirection.ltr;
  TextScaler _textScaler = TextScaler.noScaling;

  @override
  void initState() {
    super.initState();
    _controller = AnimationController(vsync: this);
  }

  @override
  void didChangeDependencies() {
    super.didChangeDependencies();
    _textDirection = Directionality.of(context);
    _textScaler = MediaQuery.textScalerOf(context);
  }

  @override
  void didUpdateWidget(covariant _LoopingMarqueeText oldWidget) {
    super.didUpdateWidget(oldWidget);
    if (oldWidget.text != widget.text) {
      _controller.stop();
      _controller.value = 0;
    }
  }

  @override
  void dispose() {
    _controller.dispose();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) {
    _controller.stop();
    return Text(
      widget.text,
      style: widget.style,
      maxLines: 1,
      overflow: TextOverflow.ellipsis,
    );
  }
}


class PodcastAppState extends ChangeNotifier {
    String _shortAudioUrl(String url) {
      if (url.length <= 72) return url;
      return '${url.substring(0, 36)}...${url.substring(url.length - 24)}';
    }

    void _cacheLog(String message) {
      final line = '[LocalCache][State] $message';
      developer.log(line, name: 'LocalCache');
    }
  // Store all podcasts.
  // Key: feed URL
  // Value: podcast metadata (name, image, url, episodes, etc.)
  final Map<String, Map<String, dynamic>> _podcasts = {};
  Map<String, Map<String, dynamic>> get podcasts => _podcasts;

  final Map<String, String> _cachedImages = {}; // feedUrl → path

  Map<String, String> get imageCache => _cachedImages;

  final Map<String, bool> _loading = {};
  bool isLoading(String feedUrl) => _loading[feedUrl] ?? false;

  final Map<List, bool> _combining = {};
  bool isCombining(List feeds) => _combining[feeds] ?? false;

  final Map<String, String?> _errors = {};
  String? error(String feedUrl) => _errors[feedUrl];

  final Map<List, String?> _combiningErrors = {};
  String? combiningError(List feeds) => _combiningErrors[feeds];
  final Map<String, bool> _downloadingAudio = {};
  final Map<String, bool> _audioFileExistsCache = {};
  final Map<String, String> _episodeSortPrefs = {};
  final Map<String, String> _episodeFilterPrefs = {};
  final Map<String, String> _episodeSearchPrefs = {};
  Map<String, dynamic>? _lastPlayedEpisode;
  Timer? _connectivityTimer;
  bool _isOffline = false;
  bool _isRefreshingConnectivity = false;
  DateTime? _lastConnectivityRefreshAt;
  bool _isFeedSyncInProgress = false;
  bool get isOffline => _isOffline;

  bool _isDarkMode = false;
  bool get isDarkMode => _isDarkMode;

  late File _storageFile;
  static const int _playedThresholdMs = 10000;

  String _normalizeAudioUrl(String url) =>
      url.trim().replaceAll('&amp;', '&');

  int _readInt(dynamic value) {
    if (value is int) return value;
    if (value is num) return value.toInt();
    if (value is String) return int.tryParse(value) ?? 0;
    return 0;
  }

  bool _fileExistsCached(String path) {
    if (path.isEmpty) return false;
    final cached = _audioFileExistsCache[path];
    if (cached != null) return cached;
    final exists = File(path).existsSync();
    _audioFileExistsCache[path] = exists;
    return exists;
  }

  bool _syncLocalAudioStateAcrossPodcasts(
    String audioUrl, {
    String? localAudioPath,
    bool? autoCachedAudio,
  }) {
    final normalizedTarget = _normalizeAudioUrl(audioUrl);
    var changed = false;

    for (final podcast in _podcasts.values) {
      final episodes = podcast['episodes'] as List<dynamic>?;
      if (episodes == null || episodes.isEmpty) continue;

      final updatedEpisodes = episodes.map((entry) {
        if (entry is! Map) return entry;
        final map = Map<String, dynamic>.from(entry as Map);
        final episodeAudioUrl =
            _normalizeAudioUrl((map['audioUrl'] ?? '').toString());
        if (episodeAudioUrl != normalizedTarget) return map;

        if (localAudioPath != null &&
            (map['localAudioPath'] ?? '').toString() != localAudioPath) {
          map['localAudioPath'] = localAudioPath;
          changed = true;
        }
        if (autoCachedAudio != null && map['autoCachedAudio'] != autoCachedAudio) {
          map['autoCachedAudio'] = autoCachedAudio;
          changed = true;
        }
        return map;
      }).toList();

      podcast['episodes'] = updatedEpisodes;
    }

    return changed;
  }

  String? _existingLocalAudioPathForAudioUrl(String audioUrl) {
    final normalizedTarget = _normalizeAudioUrl(audioUrl);

    for (final podcast in _podcasts.values) {
      final episodes = podcast['episodes'] as List<dynamic>?;
      if (episodes == null || episodes.isEmpty) continue;

      for (final raw in episodes) {
        if (raw is! Map) continue;
        final episode = Map<String, dynamic>.from(raw as Map);
        final episodeAudioUrl =
            _normalizeAudioUrl((episode['audioUrl'] ?? '').toString());
        if (episodeAudioUrl != normalizedTarget) continue;

        final localPath = (episode['localAudioPath'] ?? '').toString();
        if (localPath.isNotEmpty && _fileExistsCached(localPath)) {
          return localPath;
        }
      }
    }

    return null;
  }

  MediaItem _mediaItemFromEpisode(
    Map<String, dynamic> episode,
    Map<String, dynamic> podcast,
  ) {
    final localImagePath = (episode['localImagePath'] ?? '').toString();
    final imageUrl = (episode['imageUrl'] ?? '').toString();

    Uri? artUri;
    if (localImagePath.isNotEmpty && File(localImagePath).existsSync()) {
      artUri = Uri.file(localImagePath);
    } else if (imageUrl.isNotEmpty) {
      artUri = Uri.tryParse(imageUrl);
    }

    int? durationMs;
    final rawDurationMs = episode['durationMs'];
    if (rawDurationMs is int) {
      durationMs = rawDurationMs;
    } else if (rawDurationMs is String) {
      durationMs = int.tryParse(rawDurationMs);
    }

    final audioUrl = (episode['audioUrl'] ?? '').toString();

    return MediaItem(
      id: audioUrl,
      album: (episode['podcastTitle'] ?? podcast['title'] ?? 'Podcast').toString(),
      title: (episode['title'] ?? 'Untitled').toString(),
      artist: (episode['author'] ?? podcast['author'] ?? 'Unknown').toString(),
      artUri: artUri,
      duration: durationMs != null && durationMs > 0
          ? Duration(milliseconds: durationMs)
          : null,
      extras: {
        'feedUrl': (podcast['feedUrl'] ?? '').toString(),
        'lastPositionMs': _readInt(episode['lastPositionMs']),
        'played': (episode['played'] ?? false) == true,
        'localAudioPath': (episode['localAudioPath'] ?? '').toString(),
        'autoCachedAudio': (episode['autoCachedAudio'] ?? false) == true,
      },
    );
  }

  Future<void> rememberLastPlayedEpisode(
    MediaItem item,
    int positionMs,
  ) async {
    final clampedPositionMs = positionMs < 0 ? 0 : positionMs;
    final feedUrl = (item.extras?['feedUrl'] ?? '').toString();
    final art = item.artUri?.toString() ?? '';

    _lastPlayedEpisode = {
      'audioUrl': item.id,
      'feedUrl': feedUrl,
      'positionMs': clampedPositionMs,
      'title': item.title,
      'album': item.album,
      'artist': item.artist,
      'durationMs': item.duration?.inMilliseconds,
      'artUri': art,
      'localAudioPath': (item.extras?['localAudioPath'] ?? '').toString(),
      'played': (item.extras?['played'] ?? false) == true,
      'lastUpdatedAt': DateTime.now().toIso8601String(),
    };

    await saveToStorage();
  }

  Future<void> captureCurrentPlaybackAsLastPlayed() async {
    final item = await _audioHandler.mediaItem.first;
    if (item == null) return;

    final position = await AudioService.position.first;
    await savePlaybackProgressByAudioUrl(
      item.id,
      position.inMilliseconds,
      durationMs: item.duration?.inMilliseconds,
      feedUrl: item.extras?['feedUrl']?.toString(),
    );
    await rememberLastPlayedEpisode(item, position.inMilliseconds);
  }

  Future<void> restoreLastPlayedEpisodeIntoHandler(
    AudioPlayerHandler handler,
  ) async {
    final record = _lastPlayedEpisode;
    if (record == null) return;

    final audioUrl = (record['audioUrl'] ?? '').toString();
    if (audioUrl.isEmpty) return;

    final preferredFeedUrl = (record['feedUrl'] ?? '').toString();

    Map<String, dynamic>? foundPodcast;
    Map<String, dynamic>? foundEpisode;

    Iterable<Map<String, dynamic>> podcastsToSearch;
    if (preferredFeedUrl.isNotEmpty && _podcasts.containsKey(preferredFeedUrl)) {
      podcastsToSearch = <Map<String, dynamic>>[_podcasts[preferredFeedUrl]!];
    } else {
      podcastsToSearch = _podcasts.values;
    }

    for (final podcast in podcastsToSearch) {
      final episodes = (podcast['episodes'] as List<dynamic>? ?? const []);
      for (final raw in episodes) {
        if (raw is! Map) continue;
        final episode = Map<String, dynamic>.from(raw as Map);
        final episodeAudioUrl =
            _normalizeAudioUrl((episode['audioUrl'] ?? '').toString());
        if (episodeAudioUrl == _normalizeAudioUrl(audioUrl)) {
          foundPodcast = podcast;
          foundEpisode = episode;
          break;
        }
      }
      if (foundEpisode != null) break;
    }

    MediaItem itemToRestore;
    int positionMs = _readInt(record['positionMs']);

    if (foundPodcast != null && foundEpisode != null) {
      itemToRestore = _mediaItemFromEpisode(foundEpisode, foundPodcast);
      if (positionMs <= 0) {
        positionMs = _readInt(foundEpisode['lastPositionMs']);
      }
    } else {
      final artUriRaw = (record['artUri'] ?? '').toString();
      Uri? artUri;
      if (artUriRaw.isNotEmpty) {
        artUri = Uri.tryParse(artUriRaw);
      }

      itemToRestore = MediaItem(
        id: audioUrl,
        album: (record['album'] ?? 'Podcast').toString(),
        title: (record['title'] ?? 'Last played episode').toString(),
        artist: (record['artist'] ?? '').toString(),
        artUri: artUri,
        duration: _readInt(record['durationMs']) > 0
            ? Duration(milliseconds: _readInt(record['durationMs']))
            : null,
        extras: {
          'feedUrl': preferredFeedUrl,
          'lastPositionMs': positionMs,
          'played': record['played'] == true,
          'localAudioPath': (record['localAudioPath'] ?? '').toString(),
          'autoCachedAudio': false,
        },
      );
    }

    await handler.restorePausedEpisode(
      itemToRestore,
      initialPosition: positionMs > 0
          ? Duration(milliseconds: positionMs)
          : Duration.zero,
    );

    // Populate the full sorted queue so auto-advance works after app restart.
    if (foundPodcast != null) {
      final feedUrl = (foundPodcast['feedUrl'] ?? '').toString();
      final allEpisodes = (foundPodcast['episodes'] as List<dynamic>? ?? const [])
          .whereType<Map>()
          .map((e) => Map<String, dynamic>.from(e))
          .toList();
      if (allEpisodes.length > 1) {
        final sortPref = episodeSortForPodcast(feedUrl);
        _sortEpisodesByPref(allEpisodes, sortPref);
        final mediaItems = allEpisodes
            .map((ep) => _mediaItemFromEpisode(ep, foundPodcast!))
            .where((item) => item.id.isNotEmpty)
            .toList(growable: false);
        await handler.syncEpisodeQueuePreservingCurrent(mediaItems);
      }
    }
  }

  bool isAudioDownloading(String audioUrl) => _downloadingAudio[audioUrl] ?? false;

  Future<void> refreshConnectivityStatus() async {
    if (_isRefreshingConnectivity) return;
    final now = DateTime.now();
    if (_lastConnectivityRefreshAt != null &&
        now.difference(_lastConnectivityRefreshAt!) < const Duration(seconds: 3)) {
      return;
    }

    _isRefreshingConnectivity = true;
    final online = await hasInternetConnection();
    _lastConnectivityRefreshAt = DateTime.now();
    _isRefreshingConnectivity = false;
    final nextOffline = !online;
    if (_isOffline == nextOffline) return;
    _isOffline = nextOffline;
    notifyListeners();
  }

  void _startConnectivityMonitor() {
    _connectivityTimer?.cancel();
    _connectivityTimer = Timer.periodic(const Duration(seconds: 15), (_) {
      refreshConnectivityStatus();
    });
  }

  String _audioFileNameFromUrl(String url) {
    final hash = sha256.convert(utf8.encode(url)).toString();
    final uri = Uri.tryParse(url);
    final path = uri?.path ?? '';
    final dotIndex = path.lastIndexOf('.');
    final ext = (dotIndex >= 0 && dotIndex < path.length - 1)
        ? path.substring(dotIndex)
        : '.mp3';
    return '$hash$ext';
  }

  bool isEpisodeDownloaded(Map<String, dynamic> episode) {
    final localPath = (episode['localAudioPath'] ?? '').toString();
    if (localPath.isEmpty) return false;
    return _fileExistsCached(localPath);
  }

  /// Initialize storage and load saved podcasts
  Future<void> initStorage() async {
    final dir = await getApplicationDocumentsDirectory();
    _storageFile = File('${dir.path}/podcasts.json');
    await refreshConnectivityStatus();
    _startConnectivityMonitor();

    if (await _storageFile.exists()) {
      final content = await _storageFile.readAsString();
      final saved = jsonDecode(content) as Map<String, dynamic>;
      // 1️⃣ Load podcasts
      if (saved.containsKey('podcasts')) {
        final podcastsData = saved['podcasts'] as Map<String, dynamic>;
        podcastsData.forEach((key, value) {
          final rawPodcast = Map<String, dynamic>.from(value);
          final episodesRaw = rawPodcast['episodes'] as List<dynamic>?;
          final normalizedEpisodes = episodesRaw
              ?.map((e) => Map<String, dynamic>.from(e as Map))
              .toList();
          final persistedSort = (rawPodcast['episodeSort'] ??
                  _episodeSortPrefs[key] ??
                  'newest')
              .toString();
          _podcasts[key] = {
            ...rawPodcast,
            'episodes': normalizedEpisodes ?? <Map<String, dynamic>>[],
            'episodeSort': persistedSort,
          };
        });
      }

      if (saved.containsKey('episode_sort_prefs')) {
        final prefs = saved['episode_sort_prefs'] as Map<String, dynamic>;
        prefs.forEach((key, value) {
          _episodeSortPrefs[key] = value.toString();
        });
      }

      if (saved.containsKey('episode_filter_prefs')) {
        final prefs = saved['episode_filter_prefs'] as Map<String, dynamic>;
        prefs.forEach((key, value) {
          _episodeFilterPrefs[key] = value.toString();
        });
      }

      if (saved.containsKey('episode_search_prefs')) {
        final prefs = saved['episode_search_prefs'] as Map<String, dynamic>;
        prefs.forEach((key, value) {
          _episodeSearchPrefs[key] = value.toString();
        });
      }

      if (saved.containsKey('dark_mode')) {
        _isDarkMode = saved['dark_mode'] == true;
      }

      if (saved.containsKey('last_played_episode')) {
        final rawLast = saved['last_played_episode'];
        if (rawLast is Map) {
          _lastPlayedEpisode = Map<String, dynamic>.from(rawLast as Map);
        }
      }

      // 2️⃣ Load cached images (or old name like "image_cache")
      if (saved.containsKey('cached_images')) {
        final cached = saved['cached_images'] as Map<String, dynamic>;
        cached.forEach((hash, path) {
          _cachedImages[hash] = path.toString();
        });
      } else if (saved.containsKey('image_cache')) {
        final cached = saved['image_cache'] as Map<String, dynamic>;
        cached.forEach((hash, path) {
          _cachedImages[hash] = path.toString();
        });
      }
    } else {
      await _storageFile.writeAsString(
        jsonEncode({
          'podcasts': {},
          'cached_images': {},
          'dark_mode': false,
          'episode_sort_prefs': {},
        }),
      );
    }

    notifyListeners();
  }

  @override
  void dispose() {
    _connectivityTimer?.cancel();
    super.dispose();
  }

  /// Save the current podcasts to storage
  Future<void> saveToStorage() async {
    final data = {
      'podcasts': _podcasts,
      'cached_images': _cachedImages,
      'dark_mode': _isDarkMode,
      'episode_sort_prefs': _episodeSortPrefs,
      'episode_filter_prefs': _episodeFilterPrefs,
      'episode_search_prefs': _episodeSearchPrefs,
      'last_played_episode': _lastPlayedEpisode,
    };
    await _storageFile.writeAsString(jsonEncode(data));
  }

  String episodeSortForPodcast(String feedUrl) {
    return (_episodeSortPrefs[feedUrl] ??
            _podcasts[feedUrl]?['episodeSort'] ??
            'newest')
        .toString();
  }

  String episodeFilterForPodcast(String feedUrl) {
    return (_episodeFilterPrefs[feedUrl] ?? 'all').toString();
  }

  String episodeSearchForPodcast(String feedUrl) {
    return (_episodeSearchPrefs[feedUrl] ?? '').toString();
  }

  Future<void> setDarkMode(bool enabled) async {
    if (_isDarkMode == enabled) return;
    _isDarkMode = enabled;
    await saveToStorage();
    notifyListeners();
  }

  Future<void> setEpisodeSortForPodcast(
    String feedUrl,
    String episodeSort,
  ) async {
    _episodeSortPrefs[feedUrl] = episodeSort;
    final podcast = _podcasts[feedUrl];
    if (podcast != null) {
      podcast['episodeSort'] = episodeSort;
    }
    await saveToStorage();
    notifyListeners();
  }

  Future<void> setEpisodeFilterForPodcast(
    String feedUrl,
    String episodeFilter,
  ) async {
    _episodeFilterPrefs[feedUrl] = episodeFilter;
    await saveToStorage();
    notifyListeners();
  }

  Future<void> setEpisodeSearchForPodcast(
    String feedUrl,
    String searchQuery,
  ) async {
    _episodeSearchPrefs[feedUrl] = searchQuery;
    await saveToStorage();
    notifyListeners();
  }

  Future<void> savePlaybackProgressByAudioUrl(
    String audioUrl,
    int positionMs,
    {int? durationMs, String? feedUrl}
  ) async {
    if (audioUrl.isEmpty) return;
    final normalizedAudioUrl = _normalizeAudioUrl(audioUrl);
    var anyUpdated = false;

    bool tryUpdateInPodcast(Map<String, dynamic> podcast) {
      final episodes = podcast['episodes'] as List<dynamic>?;
      if (episodes == null) return false;

      var podcastUpdated = false;

      for (final ep in episodes) {
        if (ep is! Map) continue;
        final episode = ep;
        final episodeAudioUrl = _normalizeAudioUrl(
          (episode['audioUrl'] ?? '').toString(),
        );
        if (episodeAudioUrl != normalizedAudioUrl) continue;

        final safePositionMs = positionMs < 0 ? 0 : positionMs;
        final knownDurationMs = (durationMs != null && durationMs > 0)
            ? durationMs
            : _readInt(episode['durationMs']);
        final isNearEnd = knownDurationMs > 0 &&
            (knownDurationMs - safePositionMs) <= _playedThresholdMs;

        if (isNearEnd) {
          episode['played'] = true;
          episode['lastPositionMs'] = 0;
          _audioHandler.setSavedPosition(audioUrl, 0);
        } else {
          if (episode['played'] != true) {
            episode['played'] = false;
          }
          episode['lastPositionMs'] = safePositionMs;
          _audioHandler.setSavedPosition(audioUrl, safePositionMs);
        }

        podcastUpdated = true;
      }

      return podcastUpdated;
    }

    if (feedUrl != null && feedUrl.isNotEmpty) {
      final targetPodcast = _podcasts[feedUrl];
      if (targetPodcast != null) {
        anyUpdated = tryUpdateInPodcast(targetPodcast) || anyUpdated;
      }
    }

    final targetPodcastRef =
        (feedUrl != null && feedUrl.isNotEmpty) ? _podcasts[feedUrl] : null;
    for (final podcast in _podcasts.values) {
      if (targetPodcastRef != null &&
          (podcast['feedUrl'] ?? '') == (targetPodcastRef['feedUrl'] ?? '')) {
        continue;
      }
      anyUpdated = tryUpdateInPodcast(podcast) || anyUpdated;
    }

    if (anyUpdated) {
      await saveToStorage();
      notifyListeners();
    }

  }

  Future<void> markEpisodePlayedByAudioUrl(
    String audioUrl, {
    bool played = true,
    String? feedUrl,
  }) async {
    if (audioUrl.isEmpty) return;
    final normalizedAudioUrl = _normalizeAudioUrl(audioUrl);
    var anyUpdated = false;

    bool tryMarkInPodcast(Map<String, dynamic> podcast) {
      final episodes = podcast['episodes'] as List<dynamic>?;
      if (episodes == null) return false;

      var podcastUpdated = false;

      for (final ep in episodes) {
        if (ep is! Map) continue;
        final episode = ep;
        final episodeAudioUrl = _normalizeAudioUrl(
          (episode['audioUrl'] ?? '').toString(),
        );
        if (episodeAudioUrl != normalizedAudioUrl) continue;

        episode['played'] = played;
        if (played) {
          // Completed episodes should replay from the beginning.
          episode['lastPositionMs'] = 0;
          _audioHandler.setSavedPosition(audioUrl, 0);
        }
        podcastUpdated = true;
      }

      return podcastUpdated;
    }

    if (feedUrl != null && feedUrl.isNotEmpty) {
      final targetPodcast = _podcasts[feedUrl];
      if (targetPodcast != null) {
        anyUpdated = tryMarkInPodcast(targetPodcast) || anyUpdated;
      }
    }

    final targetPodcastRef =
        (feedUrl != null && feedUrl.isNotEmpty) ? _podcasts[feedUrl] : null;
    for (final podcast in _podcasts.values) {
      if (identical(podcast, targetPodcastRef)) continue;
      anyUpdated = tryMarkInPodcast(podcast) || anyUpdated;
    }

    if (anyUpdated) {
      await saveToStorage();
      notifyListeners();
    }

  }


  Future<void> markEpisodeUnplayedByAudioUrl(
    String audioUrl, {
    String? feedUrl,
  }) async {
    await markEpisodePlayedByAudioUrl(
      audioUrl,
      played: false,
      feedUrl: feedUrl,
    );
  }


  Future<void> resetEpisodeProgressByAudioUrl(
    String audioUrl, {
    String? feedUrl,
  }) async {
    if (audioUrl.isEmpty) return;
    await savePlaybackProgressByAudioUrl(
      audioUrl,
      0,
      durationMs: 1,
      feedUrl: feedUrl,
    );
    await markEpisodePlayedByAudioUrl(
      audioUrl,
      played: false,
      feedUrl: feedUrl,
    );
  }

  Future<bool> updateEpisodeMetadataByAudioUrl(
    String feedUrl,
    String audioUrl,
    Map<String, dynamic> updates,
  ) async {
    final podcast = _podcasts[feedUrl];
    if (podcast == null || audioUrl.isEmpty) return false;

    final episodes = podcast['episodes'] as List<dynamic>?;
    if (episodes == null || episodes.isEmpty) return false;

    final normalizedAudioUrl = _normalizeAudioUrl(audioUrl);
    var updated = false;
    final nextEpisodes = episodes.map((entry) {
      if (entry is! Map) return entry;
      final episode = Map<String, dynamic>.from(entry as Map);
      final episodeAudio = _normalizeAudioUrl(
        (episode['audioUrl'] ?? '').toString(),
      );
      if (!updated && episodeAudio == normalizedAudioUrl) {
        episode.addAll(updates);
        updated = true;
      }
      return episode;
    }).toList();

    if (!updated) return false;

    podcast['episodes'] = nextEpisodes;
    await saveToStorage();
    notifyListeners();
    return true;
  }

  Future<bool> removeEpisodeFromPodcast(
    String feedUrl,
    Map<String, dynamic> episodeRef,
  ) async {
    final podcast = _podcasts[feedUrl];
    if (podcast == null) return false;

    final episodes = podcast['episodes'] as List<dynamic>?;
    if (episodes == null || episodes.isEmpty) return false;

    final targetAudioUrl = _normalizeAudioUrl(
      (episodeRef['audioUrl'] ?? '').toString(),
    );
    final targetGuid = (episodeRef['guid'] ?? '').toString();
    final targetTitle = (episodeRef['title'] ?? '').toString();
    final targetPubDate = (episodeRef['pubDate'] ?? '').toString();
    final targetPodcastTitle = (episodeRef['podcastTitle'] ?? '').toString();

    int removeIndex = -1;
    for (int i = 0; i < episodes.length; i++) {
      final raw = episodes[i];
      if (raw is! Map) continue;
      final episode = Map<String, dynamic>.from(raw as Map);

      final audioUrl = _normalizeAudioUrl((episode['audioUrl'] ?? '').toString());
      final guid = (episode['guid'] ?? '').toString();
      final title = (episode['title'] ?? '').toString();
      final pubDate = (episode['pubDate'] ?? '').toString();
      final podcastTitle = (episode['podcastTitle'] ?? '').toString();

      final audioMatches = targetAudioUrl.isNotEmpty && audioUrl == targetAudioUrl;
      final guidMatches = targetGuid.isNotEmpty && guid == targetGuid;
      final titleMatches = targetTitle.isNotEmpty && title == targetTitle;
      final dateMatches = targetPubDate.isNotEmpty && pubDate == targetPubDate;
      final podcastMatches =
          targetPodcastTitle.isNotEmpty && podcastTitle == targetPodcastTitle;

      // Prefer a strict match, but allow looser fallback when some fields are missing.
      final strictMatch = (audioMatches || guidMatches) &&
          (titleMatches || targetTitle.isEmpty) &&
          (dateMatches || targetPubDate.isEmpty) &&
          (podcastMatches || targetPodcastTitle.isEmpty);

      final fallbackMatch = audioMatches || guidMatches || (titleMatches && dateMatches);

      if (strictMatch || fallbackMatch) {
        removeIndex = i;
        break;
      }
    }

    if (removeIndex < 0) return false;

    final nextEpisodes = List<dynamic>.from(episodes)..removeAt(removeIndex);
    podcast['episodes'] = nextEpisodes;
    await saveToStorage();
    notifyListeners();
    return true;
  }

  Map<String, List<Map<String, dynamic>>> tesd_podcasts = {};

  Future<void> loadTESDData() async {
    final jsonString = await rootBundle.loadString('assets/data/tesd.json');
    final Map<String, dynamic> data = json.decode(jsonString);
    tesd_podcasts = data.map((key, value) {
      final List<Map<String, dynamic>> list = (value as List)
          .map((e) => Map<String, dynamic>.from(e))
          .toList();
      return MapEntry(key, list);
    });
    notifyListeners();
  }

  dynamic parseString(dynamic field, {String? attribute}) {
    if (field == null) return '';
    if (field is String) return field;

    if (field is Map) {
      if (field.containsKey('#text')) return field['#text'] as String;
      if (field.containsKey('#cdata')) return field['#cdata'].toString();

      // Handle attributes like @href or custom key
      if (attribute != null && field.containsKey(attribute)) {
        return field[attribute].toString();
      }

      // Fallback: if map only has one key, return that value
      if (field.length == 1) {
        return field.values.first.toString();
      }
    }

    return '';
  }

  String? parseUrl(dynamic field) {
    if (field == null) return null;

    if (field is String) return field;

    if (field is Map) {
      return field['@url'] ??
          field['url'] ??
          field['@href'] ??
          field['href'] ??
          field['link'] ??
          null;
    }

    if (field is List && field.isNotEmpty) {
      return parseUrl(field.first); // recurse on first element
    }

    return null;
  }

  Duration? parseItunesDuration(dynamic field) {
    final raw = parseString(field).toString().trim();
    if (raw.isEmpty) return null;

    if (RegExp(r'^\d+$').hasMatch(raw)) {
      return Duration(seconds: int.parse(raw));
    }

    final parts = raw.split(':').map((p) => int.tryParse(p)).toList();
    if (parts.any((p) => p == null)) return null;

    if (parts.length == 3) {
      return Duration(hours: parts[0]!, minutes: parts[1]!, seconds: parts[2]!);
    }
    if (parts.length == 2) {
      return Duration(minutes: parts[0]!, seconds: parts[1]!);
    }
    if (parts.length == 1) {
      return Duration(seconds: parts[0]!);
    }

    return null;
  }

  DateTime? _parseEpisodeDate(dynamic raw) {
    final value = (raw ?? '').toString().trim();
    if (value.isEmpty) return null;

    final direct = DateTime.tryParse(value);
    if (direct != null) return direct;

    final formats = [
      DateFormat("EEE, dd MMM yyyy HH:mm:ss 'GMT'", 'en_US'),
      DateFormat('EEE, dd MMM yyyy HH:mm:ss Z', 'en_US'),
      DateFormat('yyyy-MM-dd HH:mm:ss', 'en_US'),
    ];

    for (final format in formats) {
      try {
        return format.parse(value, true).toLocal();
      } catch (_) {}
    }

    return null;
  }

  void _sortEpisodesNewestFirst(List<Map<String, dynamic>> episodes) {
    _sortEpisodesByPref(episodes, 'newest');
  }

  void _sortEpisodesByPref(List<Map<String, dynamic>> episodes, String sortPref) {
    if (sortPref == 'titleAsc') {
      episodes.sort((a, b) => (a['title'] ?? '').toString().toLowerCase()
          .compareTo((b['title'] ?? '').toString().toLowerCase()));
      return;
    }
    final parsedDateCache = <Map<String, dynamic>, DateTime>{};
    DateTime cachedDate(Map<String, dynamic> episode) {
      return parsedDateCache.putIfAbsent(
        episode,
        () => _parseEpisodeDate(episode['pubDate']) ??
            DateTime.fromMillisecondsSinceEpoch(0),
      );
    }
    if (sortPref == 'oldest') {
      episodes.sort((a, b) => cachedDate(a).compareTo(cachedDate(b)));
    } else {
      episodes.sort((a, b) => cachedDate(b).compareTo(cachedDate(a)));
    }
  }

  String _episodeIdentityKey(Map<String, dynamic> episode) {
    final normalizedUrl = _normalizeAudioUrl(
      (episode['audioUrl'] ?? '').toString(),
    );
    if (normalizedUrl.isNotEmpty) return 'url:$normalizedUrl';

    final guid = (episode['guid'] ?? '').toString().trim();
    if (guid.isNotEmpty) return 'guid:$guid';

    final title = (episode['title'] ?? '').toString().trim().toLowerCase();
    final pubDate = (episode['pubDate'] ?? '').toString().trim();
    return 'fallback:$title|$pubDate';
  }

  List<Map<String, dynamic>> _mergeFetchedEpisodesWithExisting(
    List<dynamic> existingEpisodes,
    List<Map<String, dynamic>> fetchedEpisodes,
  ) {
    final existingByKey = <String, Map<String, dynamic>>{};
    for (final raw in existingEpisodes) {
      if (raw is! Map) continue;
      final existing = Map<String, dynamic>.from(raw as Map);
      existingByKey[_episodeIdentityKey(existing)] = existing;
    }

    final merged = <Map<String, dynamic>>[];
    final seenKeys = <String>{};

    for (final fetched in fetchedEpisodes) {
      final key = _episodeIdentityKey(fetched);
      final existing = existingByKey[key];
      if (existing != null) {
        merged.add({
          ...existing,
          ...fetched,
          'lastPositionMs': existing['lastPositionMs'] ?? fetched['lastPositionMs'] ?? 0,
          'played': existing['played'] ?? fetched['played'] ?? false,
          'localAudioPath': existing['localAudioPath'] ?? fetched['localAudioPath'],
          'autoCachedAudio': existing['autoCachedAudio'] ?? fetched['autoCachedAudio'] ?? false,
          'localImagePath': existing['localImagePath'] ?? fetched['localImagePath'],
        });
      } else {
        merged.add(Map<String, dynamic>.from(fetched));
      }
      seenKeys.add(key);
    }

    for (final entry in existingByKey.entries) {
      if (!seenKeys.contains(entry.key)) {
        merged.add(Map<String, dynamic>.from(entry.value));
      }
    }

    _sortEpisodesNewestFirst(merged);
    return merged;
  }

  List<String> _resolvedCombinedSources(
    String combinedFeedKey,
    Map<String, dynamic> combinedPodcast,
  ) {
    final explicitSources = (combinedPodcast['sourceFeedUrls'] as List<dynamic>? ?? const [])
        .map((e) => e.toString())
        .where((feed) => _podcasts.containsKey(feed))
        .where((feed) => feed.startsWith('http://') || feed.startsWith('https://'))
        .toList();
    if (explicitSources.isNotEmpty) {
      return explicitSources;
    }

    final title = (combinedPodcast['title'] ?? combinedFeedKey).toString();
    final pieces = title
        .split(' + ')
        .map((s) => s.trim())
        .where((s) => s.isNotEmpty)
        .toList();
    if (pieces.length < 2) return const [];

    final inferred = <String>[];
    for (final piece in pieces) {
      for (final entry in _podcasts.entries) {
        final key = entry.key;
        if (!(key.startsWith('http://') || key.startsWith('https://'))) continue;
        final sourceTitle = (entry.value['title'] ?? '').toString().trim();
        if (sourceTitle == piece && !inferred.contains(key)) {
          inferred.add(key);
          break;
        }
      }
    }
    return inferred.length >= 2 ? inferred : const [];
  }

  void _rebuildCombinedPodcastFromSources(
    String combinedFeedKey,
    Map<String, dynamic> combinedPodcast,
  ) {
    final sources = _resolvedCombinedSources(combinedFeedKey, combinedPodcast);
    if (sources.isEmpty) return;

    final existingCombinedEpisodes =
        (combinedPodcast['episodes'] as List<dynamic>? ?? const []);
    final combinedStateByKey = <String, Map<String, dynamic>>{};
    for (final raw in existingCombinedEpisodes) {
      if (raw is! Map) continue;
      final episode = Map<String, dynamic>.from(raw as Map);
      combinedStateByKey[_episodeIdentityKey(episode)] = episode;
    }

    final sourceEpisodes = <Map<String, dynamic>>[];
    for (final sourceFeed in sources) {
      final sourcePodcast = _podcasts[sourceFeed];
      if (sourcePodcast == null) continue;
      final sourceTitle = (sourcePodcast['title'] ?? 'Podcast').toString();
      final episodes = (sourcePodcast['episodes'] as List<dynamic>? ?? const []);
      for (final raw in episodes) {
        if (raw is! Map) continue;
        final episode = Map<String, dynamic>.from(raw as Map);
        episode['podcastTitle'] =
            (episode['podcastTitle'] ?? sourceTitle).toString();

        final preserved = combinedStateByKey[_episodeIdentityKey(episode)];
        if (preserved != null) {
          final preservedPosition = _readInt(preserved['lastPositionMs']);
          final sourcePosition = _readInt(episode['lastPositionMs']);
          if (preservedPosition > sourcePosition) {
            episode['lastPositionMs'] = preservedPosition;
          }
          if ((preserved['played'] ?? false) == true) {
            episode['played'] = true;
            episode['lastPositionMs'] = 0;
          }
          final preservedLocalPath =
              (preserved['localAudioPath'] ?? '').toString();
          final sourceLocalPath = (episode['localAudioPath'] ?? '').toString();
          if (sourceLocalPath.isEmpty && preservedLocalPath.isNotEmpty) {
            episode['localAudioPath'] = preservedLocalPath;
            episode['autoCachedAudio'] =
                (preserved['autoCachedAudio'] ?? false) == true;
          }
        }

        sourceEpisodes.add(episode);
      }
    }

    _sortEpisodesNewestFirst(sourceEpisodes);

    combinedPodcast['episodes'] = sourceEpisodes;
    combinedPodcast['sourceFeedUrls'] = List<String>.from(sources);
  }

  Future<void> syncFeedsOnStartup() async {
    if (_isFeedSyncInProgress) return;
    _isFeedSyncInProgress = true;
    final online = await hasInternetConnection();
    if (!online) {
      _isFeedSyncInProgress = false;
      return;
    }

    try {
      final normalFeedUrls = _podcasts.keys
          .where((feed) => feed.startsWith('http://') || feed.startsWith('https://'))
          .toList(growable: false);

      for (final feedUrl in normalFeedUrls) {
        await loadPodcast(feedUrl, showLoading: false);
      }

      final combinedKeys = _podcasts.keys
          .where((feed) => !(feed.startsWith('http://') || feed.startsWith('https://')))
          .toList(growable: false);

      for (final combinedKey in combinedKeys) {
        final combinedPodcast = _podcasts[combinedKey];
        if (combinedPodcast == null) continue;
        _rebuildCombinedPodcastFromSources(combinedKey, combinedPodcast);
      }

      await saveToStorage();
      notifyListeners();
    } finally {
      _isFeedSyncInProgress = false;
    }
  }

  String normalizeTitle(String title) {
    return title
        // apostrophes
        .replaceAll('‘', "'")
        .replaceAll('’', "'")
        // quotes
        .replaceAll('“', '"')
        .replaceAll('”', '"')
        // dashes
        .replaceAll('–', '-') // en dash
        .replaceAll('—', '-') // em dash
        .replaceAll('−', '-') // minus sign
        // collapse whitespace
        .replaceAll(RegExp(r'\s+'), ' ')
        .trim();
  }

  String fileNameFromUrl(String url) {
    final uri = Uri.parse(url);

    // Take the full path without query params
    // e.g. /podcasts/.../image/a30be7f.jpg
    final cleanPath = uri.path;

    // Replace "/" with "-" so it’s filesystem safe
    final safePath = cleanPath.replaceAll("/", "-");

    return safePath;
  }

  Future<String?> downloadAndSaveImage(String? url, String fileName) async {
    if (url == null || url.isEmpty) return null;

    final online = await hasInternetConnection();
    if (!online) {
      _cacheLog('Image download skipped (offline): $url');
      return null;
    }

    try {
      final dir = await getApplicationDocumentsDirectory();
      final file = File('${dir.path}/$fileName');

      if (await file.exists()) return file.path; // Already cached?

      final response = await http.get(Uri.parse(url));
      if (response.statusCode == 200) {
        var hash = imageHash(response.bodyBytes);
        if (_cachedImages.containsKey(hash)) {
          return _cachedImages[hash];
        }
        await file.writeAsBytes(response.bodyBytes);
        _cachedImages[hash] = file.path;
        await saveToStorage();
        return file.path;
      }
    } catch (e) {
      _cacheLog('Image download failed: $url error=$e');
    }
    return null;
  }

  Future<void> downloadEpisodeImage(Map<String, dynamic> episode) async {
    var imageUrl = episode?['imageUrl'];
    var imageFileName = fileNameFromUrl(imageUrl);
    if (episode['localImagePath'] == null) {
      episode['localImagePath'] = await downloadAndSaveImage(
        imageUrl,
        imageFileName,
      );
      notifyListeners();
    }
  }

  Future<String?> ensureEpisodeAudioDownloadedByUrl(
    String feedUrl,
    String audioUrl, {
    bool autoCache = false,
  }) async {
    if (audioUrl.isEmpty) return null;
    final podcast = _podcasts[feedUrl];
    if (podcast == null) return null;

    final episodes = podcast['episodes'] as List<dynamic>?;
    if (episodes == null) return null;

    final normalizedTarget = _normalizeAudioUrl(audioUrl);
    Map<String, dynamic>? targetEpisode;
    for (final raw in episodes) {
      if (raw is! Map) continue;
      final ep = Map<String, dynamic>.from(raw as Map);
      final epUrl = _normalizeAudioUrl((ep['audioUrl'] ?? '').toString());
      if (epUrl == normalizedTarget) {
        targetEpisode = ep;
        break;
      }
    }
    if (targetEpisode == null) return null;

    final existingGlobalPath = _existingLocalAudioPathForAudioUrl(audioUrl);
    if (existingGlobalPath != null && existingGlobalPath.isNotEmpty) {
      final synced = _syncLocalAudioStateAcrossPodcasts(
        audioUrl,
        localAudioPath: existingGlobalPath,
        autoCachedAudio: autoCache,
      );
      if (synced) {
        await saveToStorage();
        notifyListeners();
      }
      _cacheLog(
        'Download skipped (reused existing file): ${_shortAudioUrl(audioUrl)} path=$existingGlobalPath auto=$autoCache',
      );
      return existingGlobalPath;
    }

    final existingPath = (targetEpisode['localAudioPath'] ?? '').toString();
    if (existingPath.isNotEmpty && _fileExistsCached(existingPath)) {
      _cacheLog(
        'Download skipped (already on disk): ${_shortAudioUrl(audioUrl)} path=$existingPath auto=$autoCache',
      );
      final synced = _syncLocalAudioStateAcrossPodcasts(
        audioUrl,
        localAudioPath: existingPath,
        autoCachedAudio: autoCache ? true : null,
      );
      if (synced) {
        await saveToStorage();
        notifyListeners();
      }
      return existingPath;
    }

    final online = await hasInternetConnection();
    if (!online) {
      _cacheLog('Download skipped (offline): ${_shortAudioUrl(audioUrl)}');
      return null;
    }

    if (_downloadingAudio[audioUrl] == true) {
      _cacheLog('Download already in progress: ${_shortAudioUrl(audioUrl)}');
      return null;
    }

    _cacheLog(
      'Download started: ${_shortAudioUrl(audioUrl)} auto=$autoCache',
    );
    _downloadingAudio[audioUrl] = true;
    notifyListeners();

    try {
      final dir = await getApplicationDocumentsDirectory();
      final fileName = _audioFileNameFromUrl(audioUrl);
      final file = File('${dir.path}/$fileName');

      if (!await file.exists()) {
        final response = await http.get(
          Uri.parse(audioUrl),
          headers: {
            'User-Agent': 'UlticastPodcastApp/1.0',
            'Accept': '*/*',
            'Referer': 'https://www.patreon.com/',
          },
        );
        if (response.statusCode != 200) {
          throw Exception('Download failed: ${response.statusCode}');
        }
        await file.writeAsBytes(response.bodyBytes);
      }

      final freshPodcast = _podcasts[feedUrl];
      final freshEpisodes = freshPodcast?['episodes'] as List<dynamic>?;
      if (freshPodcast == null || freshEpisodes == null) return null;

      _syncLocalAudioStateAcrossPodcasts(
        audioUrl,
        localAudioPath: file.path,
        autoCachedAudio: autoCache,
      );
      _audioFileExistsCache[file.path] = true;
      await saveToStorage();
      notifyListeners();
      _cacheLog(
        'Download completed: ${_shortAudioUrl(audioUrl)} saved at ${file.path} auto=$autoCache',
      );
      return file.path;
    } catch (e) {
      _cacheLog('Download failed: ${_shortAudioUrl(audioUrl)} error=$e');
      return null;
    } finally {
      _downloadingAudio[audioUrl] = false;
      notifyListeners();
    }
  }

  Future<void> deleteEpisodeAudioByUrl(
    String feedUrl,
    String audioUrl, {
    bool onlyAutoCached = false,
  }) async {
    if (audioUrl.isEmpty) return;
    final podcast = _podcasts[feedUrl];
    if (podcast == null) return;

    final episodes = podcast['episodes'] as List<dynamic>?;
    if (episodes == null) return;

    final normalizedTarget = _normalizeAudioUrl(audioUrl);
    var changed = false;

    final updatedEpisodes = episodes.map((entry) {
      if (entry is! Map) return entry;
      final map = Map<String, dynamic>.from(entry as Map);
      final episodeAudioUrl =
          _normalizeAudioUrl((map['audioUrl'] ?? '').toString());
      if (episodeAudioUrl != normalizedTarget) return map;

      final isAutoCached = map['autoCachedAudio'] == true;
      if (onlyAutoCached && !isAutoCached) return map;

      final localPath = (map['localAudioPath'] ?? '').toString();
      if (localPath.isNotEmpty) {
        final file = File(localPath);
        if (file.existsSync()) {
          try {
            file.deleteSync();
          } catch (_) {}
        }
        _audioFileExistsCache[localPath] = false;
      }

      map['localAudioPath'] = null;
      map['autoCachedAudio'] = false;
      changed = true;
      return map;
    }).toList();

    if (!changed) return;

    podcast['episodes'] = updatedEpisodes;

    var syncedOthers = false;
    if (!onlyAutoCached) {
      syncedOthers = _syncLocalAudioStateAcrossPodcasts(
            audioUrl,
            localAudioPath: '',
            autoCachedAudio: false,
          ) ||
          syncedOthers;
    } else {
      syncedOthers = _syncLocalAudioStateAcrossPodcasts(
            audioUrl,
            autoCachedAudio: false,
          ) ||
          syncedOthers;
    }

    changed = changed || syncedOthers;
    if (!changed) return;

    await saveToStorage();
    notifyListeners();
    _cacheLog(
      'Deleted local audio: ${_shortAudioUrl(audioUrl)} onlyAuto=$onlyAutoCached',
    );
  }

  Future<void> downloadEpisodeAudio(
    String feedUrl,
    Map<String, dynamic> episode,
  ) async {
    final audioUrl = (episode['audioUrl'] ?? '').toString();
    await ensureEpisodeAudioDownloadedByUrl(
      feedUrl,
      audioUrl,
      autoCache: false,
    );
  }

  Future<void> combinePodcasts(List feedUrls) async {
    _combining[feedUrls] = true;
    _combiningErrors[feedUrls] = null;
    notifyListeners();

    try {
      // Build podcast object
      var title = "";
      int index = 0;
      for (var feed in feedUrls) {
        var thisTitle = _podcasts[feed]!['title'];
        if (index == feedUrls.length - 1) {
          title += "$thisTitle";
        } else {
          title += "$thisTitle + ";
        }
        index++;
      }
      List<Map<String, dynamic>> episodes = [];
      for (var feed in feedUrls) {
        final sourcePodcastTitle = (_podcasts[feed]!['title'] ?? 'Podcast').toString();
        final sourceEpisodes = (_podcasts[feed]!['episodes'] as List)
            .cast<Map<String, dynamic>>();
        episodes.addAll(
          sourceEpisodes.map((episode) {
            final copy = Map<String, dynamic>.from(episode);
            copy['podcastTitle'] =
                (copy['podcastTitle'] ?? sourcePodcastTitle).toString();
            return copy;
          }),
        );
      }

      DateTime? parsePubDate(String raw) {
        final formats = [
          DateFormat("EEE, dd MMM yyyy HH:mm:ss 'GMT'", "en_US"), // ... GMT
          DateFormat(
            "EEE, dd MMM yyyy HH:mm:ss Z",
            "en_US",
          ), // ... +0000 / -0000
        ];

        for (var f in formats) {
          try {
            return f.parse(raw);
          } catch (_) {}
        }

        return null;
      }

      final parsedPubDates = <Map<String, dynamic>, DateTime?>{};
      for (final episode in episodes) {
        parsedPubDates[episode] =
            parsePubDate((episode['pubDate'] ?? '').toString());
      }

      episodes.sort((a, b) {
        final dateA = parsedPubDates[a];
        final dateB = parsedPubDates[b];

        if (dateA == null || dateB == null) return 0;
        return dateB.compareTo(dateA); // newest first
      });

      // 3. HANDLE THE IMAGE CORRECTLY
      // Get the URL of the first podcast's image
      String? sourceImageUrl = _podcasts[feedUrls[0]]!['image'];
      
      // Generate a filename for this new combined podcast
      // We use the title to create a safe filename so it doesn't clash with existing files
      String combinedImageFileName = fileNameFromUrl(title);
      
      // IMPORTANT: Download the image locally
      String? combinedImagePath = await downloadAndSaveImage(sourceImageUrl, combinedImageFileName);


      final podcastData = {
        'title': title,
        'feedUrl': title,
        'localImagePath': combinedImagePath,
        'episodes': episodes,
        'sourceFeedUrls': feedUrls.map((e) => e.toString()).toList(),
        'episodeSort': 'newest',
        'error': null,
      };

      _podcasts[title] = podcastData;
      _episodeSortPrefs[title] = 'newest';
      await saveToStorage();
    } on Exception catch (e) {
      _combiningErrors[feedUrls] = 'Error: ${e.toString()}';
    } finally {
      _combining[feedUrls] = false;
      notifyListeners();
    }
  }

  Future<void> loadPodcast(String feedUrl, {bool showLoading = true}) async {
    if (showLoading) {
      _loading[feedUrl] = true;
      _errors[feedUrl] = null;
      notifyListeners();
    }

    final online = await hasInternetConnection();
    if (!online) {
      if (showLoading) {
        _errors[feedUrl] = 'Offline: can\'t refresh this feed right now.';
        _loading[feedUrl] = false;
        notifyListeners();
      }
      return;
    }

    try {
      final response = await http.get(Uri.parse(feedUrl))
          .timeout(const Duration(seconds: 30));

      if (response.statusCode == 200) {
        final converter = Xml2Map(response.body);
        final data = await converter.transform();
        final channel = data?['rss']?['channel'];
        if (channel == null) {
          _errors[feedUrl] = 'Invalid RSS feed structure';
          _loading[feedUrl] = false;
          notifyListeners();
          return;
        }
        final existingEpisodeSort = episodeSortForPodcast(feedUrl);
        final existingEpisodes =
            (_podcasts[feedUrl]?['episodes'] as List<dynamic>? ?? const []);
        final Map<String, Map<String, dynamic>> existingByAudioUrl = {};
        final Map<String, Map<String, dynamic>> existingByGuid = {};
        for (final raw in existingEpisodes) {
          if (raw is! Map) continue;
          final ep = Map<String, dynamic>.from(raw as Map);
          final existingAudioUrl = _normalizeAudioUrl(
            (ep['audioUrl'] ?? '').toString(),
          );
          final existingGuid = (ep['guid'] ?? '').toString();
          if (existingAudioUrl.isNotEmpty) {
            existingByAudioUrl[existingAudioUrl] = ep;
          }
          if (existingGuid.isNotEmpty) {
            existingByGuid[existingGuid] = ep;
          }
        }
        var title = parseString(channel['title']);
        var author = parseString(channel['itunes:author']);
        if (author.toString().trim().isEmpty) {
          author = parseString(channel['author']);
        }
        var podcastImage =
            channel['image']?['url'] ?? channel['itunes:image']?['@href'];
        var podcastImageFilename =
            podcastImage != null ? fileNameFromUrl(podcastImage.toString()) : '';
        var podcastImagePath = await downloadAndSaveImage(
          podcastImage?.toString(),
          podcastImageFilename,
        );
        final rawItem = channel['item'];
        final List<dynamic> rawEpisodes = rawItem is List
            ? rawItem
            : (rawItem != null ? <dynamic>[rawItem] : <dynamic>[]);
        final fetchedEpisodes = rawEpisodes.map((item) {
          var pubDate = parseString(item['pubDate']);
          if (parseString(channel['title']).trim() ==
              "Tell 'Em Steve Dave EP. 1-299") {
            final List<Map<String, dynamic>> tesd1To299 =
                tesd_podcasts['TESD'] ?? [];
            String? extractEpisodeNumber(String title) {
              final match = RegExp(r'#(\d+(\.\d+)?)').firstMatch(title);
              return match != null ? match.group(0) : null;
            }

            Map<String, dynamic>? thisEpisode = tesd1To299.firstWhere(
              (ep) {
                final epNumA = extractEpisodeNumber(
                  normalizeTitle(ep['title'].toLowerCase()),
                );
                final epNumB = extractEpisodeNumber(
                  normalizeTitle(
                    parseString(item['title']).trim().toLowerCase(),
                  ),
                );
                return epNumA != null && epNumB != null && epNumA == epNumB;
              },
              orElse: () => {}, // empty map if not found
            );

            /*Map<String, dynamic>? thisEpisode = tesd1To299.firstWhere(
              (ep) => normalizeTitle(ep['title'].toLowerCase()).substring(0,5) == normalizeTitle(parseString(item['title']).trim().toLowerCase()).substring(0,5),
              orElse: () => {}, // returns empty map if not found
            );*/

            if (thisEpisode.isNotEmpty) {
              pubDate = thisEpisode['date'];
              pubDate = DateFormat("yyyy-MM-dd HH:mm:ss").parse(pubDate);
              pubDate = DateFormat(
                "EEE, dd MMM yyyy HH:mm:ss 'GMT'",
              ).format(pubDate);
            }
          }
          if (channel['title'] == "Tell ‘Em Steve-Dave! Bonus Episodes") {
            final List<Map<String, dynamic>> overkill =
                tesd_podcasts['Overkill'] ?? [];
            Map<String, dynamic>? thisEpisode = overkill.firstWhere(
              (ep) =>
                  normalizeTitle(ep['title'].toLowerCase()) ==
                  normalizeTitle(item['title'].toLowerCase()),
              orElse: () => {}, // returns empty map if not found
            );

            if (thisEpisode.isNotEmpty) {
              pubDate = thisEpisode['date'];
              pubDate = DateFormat("yyyy-MM-dd HH:mm:ss").parse(pubDate);
              pubDate = DateFormat(
                "EEE, dd MMM yyyy HH:mm:ss 'GMT'",
              ).format(pubDate);
            }
            final List<Map<String, dynamic>> tesdBonus =
                tesd_podcasts['TESD_Bonus'] ?? [];
            Map<String, dynamic>? thisEpisodeToo = tesdBonus.firstWhere(
              (ep) =>
                  normalizeTitle(ep['title'].toLowerCase()) ==
                  unescape.convert((item['title'].toLowerCase())),
              orElse: () => {}, // returns empty map if not found
            );
            if (thisEpisodeToo.isNotEmpty) {
              pubDate = thisEpisodeToo['date'];
              pubDate = DateFormat("yyyy-MM-dd HH:mm:ss").parse(pubDate);
              pubDate = DateFormat(
                "EEE, dd MMM yyyy HH:mm:ss 'GMT'",
              ).format(pubDate);
            }
          }
          var title = unescape.convert(parseString(item['title']).trim());
          final parsedDuration = parseItunesDuration(item['itunes:duration']);
          var url = item['enclosure']?['@url'] ?? item['enclosure']?['url'];
            final normalizedUrl = _normalizeAudioUrl((url ?? '').toString());
            final guid = parseString(item['guid']);
            final previousEpisode = normalizedUrl.isNotEmpty
              ? existingByAudioUrl[normalizedUrl]
              : null;
            final fallbackEpisode = previousEpisode ??
              (guid.toString().isNotEmpty
                ? existingByGuid[guid.toString()]
                : null);
          var imageUrl =
              item['itunes:image']?['@href'] ??
              item['itunes:image']?['href'] ??
              podcastImage;
          var localImagePath = null;
          if (imageUrl == podcastImage) {
            localImagePath = podcastImagePath;
          }
          return {
            'title': title,
            'description': unescape
                .convert(parseString(item['description']))
                .replaceAll(RegExp(r'<[^>]*>'), ''),
            'pubDate': pubDate,
            'guid': guid,
            'audioUrl': url,
            'durationMs': parsedDuration?.inMilliseconds,
            'lastPositionMs': fallbackEpisode?['lastPositionMs'] ?? 0,
            'podcastTitle':
                fallbackEpisode?['podcastTitle'] ?? parseString(channel['title']),
            'author': parseString(item['itunes:author']).toString().trim().isNotEmpty
              ? parseString(item['itunes:author'])
              : author,
            'imageUrl': imageUrl,
            'localAudioPath': fallbackEpisode?['localAudioPath'],
            'autoCachedAudio': fallbackEpisode?['autoCachedAudio'] ?? false,
            'localImagePath': localImagePath,
            'played': fallbackEpisode?['played'] ?? false,
            'playing': false,
          };
        }).toList();

        final mergedEpisodes = _mergeFetchedEpisodesWithExisting(
          existingEpisodes,
          fetchedEpisodes.cast<Map<String, dynamic>>(),
        );

        // Build podcast object

        final podcastData = {
          'title': title,
          'author': author,
          'feedUrl': feedUrl,
          'image': podcastImage,
          'localImagePath': podcastImagePath,
          'episodes': mergedEpisodes,
          'episodeSort': existingEpisodeSort,
          'error': null,
        };

        _podcasts[feedUrl] = podcastData;
        _episodeSortPrefs[feedUrl] = existingEpisodeSort;
        await saveToStorage();
      } else {
        _errors[feedUrl] = 'Failed to load podcast: ${response.statusCode}';
      }
    } on Exception catch (e) {
      if (showLoading) {
        _errors[feedUrl] = 'Error: ${e.toString()}';
      }
    } finally {
      if (showLoading) {
        _loading[feedUrl] = false;
        notifyListeners();
      }
    }
  }

  void clearAll() {
    _podcasts.clear();
    _loading.clear();
    _errors.clear();
    saveToStorage();
    notifyListeners();
  }

  void clearPodcast(String feedUrl) {
    _podcasts.remove(feedUrl);
    _loading.remove(feedUrl);
    _errors.remove(feedUrl);
    _episodeSortPrefs.remove(feedUrl);
    _episodeFilterPrefs.remove(feedUrl);
    _episodeSearchPrefs.remove(feedUrl);
    saveToStorage();
    notifyListeners();
  }
}

late AudioPlayerHandler _audioHandler;
final GlobalKey<NavigatorState> _appNavigatorKey = GlobalKey<NavigatorState>();
final RouteObserver<ModalRoute<void>> _routeObserver =
  RouteObserver<ModalRoute<void>>();

Future<void> main() async {
  // Required when using async in main()
  WidgetsFlutterBinding.ensureInitialized();

  // Configure the audio session for media/podcast playback.
  // Using 'media' usage (not 'voiceCommunication') so the system treats this
  // as media playback — correct Bluetooth routing (A2DP, not SCO) and proper
  // audio focus transitions with phone calls and other apps.
  final session = await AudioSession.instance;
  await session.configure(const AudioSessionConfiguration(
    avAudioSessionCategory: AVAudioSessionCategory.playback,
    avAudioSessionMode: AVAudioSessionMode.spokenAudio,
    avAudioSessionRouteSharingPolicy:
        AVAudioSessionRouteSharingPolicy.defaultPolicy,
    avAudioSessionSetActiveOptions: AVAudioSessionSetActiveOptions.none,
    androidAudioAttributes: AndroidAudioAttributes(
      contentType: AndroidAudioContentType.speech,
      usage: AndroidAudioUsage.media,
    ),
    androidAudioFocusGainType: AndroidAudioFocusGainType.gain,
  ));
  // Initialize audio service
  _audioHandler = await AudioService.init(
    builder: () => AudioPlayerHandler(),
    config: const AudioServiceConfig(
      androidNotificationChannelId: 'com.ryanheise.myapp.channel.audio',
      androidNotificationChannelName: 'Audio playback',
      androidNotificationOngoing: true,
    ),
  );

  // Create the PodcastAppState
  final podcastState = PodcastAppState();
  await podcastState.initStorage(); // Load saved podcasts
  _audioHandler.onEpisodeCompleted = (audioUrl, feedUrl) {
    return podcastState.markEpisodePlayedByAudioUrl(
      audioUrl,
      played: true,
      feedUrl: feedUrl,
    );
  };
  _audioHandler.onRequestDownloadAudio =
      (feedUrl, audioUrl, autoCached) async {
        return podcastState.ensureEpisodeAudioDownloadedByUrl(
          feedUrl,
          audioUrl,
          autoCache: autoCached,
        );
      };
  _audioHandler.onDeleteDownloadedAudio =
      (feedUrl, audioUrl, onlyAutoCached) {
        return podcastState.deleteEpisodeAudioByUrl(
          feedUrl,
          audioUrl,
          onlyAutoCached: onlyAutoCached,
        );
      };
  _audioHandler.onPlaybackError = (message) {
    final context = _appNavigatorKey.currentContext;
    if (context == null) return;
    final messenger = ScaffoldMessenger.maybeOf(context);
    messenger?.hideCurrentSnackBar();
    messenger?.showSnackBar(SnackBar(content: Text(message)));
  };
  _audioHandler.onSaveProgress = (audioUrl, positionMs, feedUrl) {
    return podcastState.savePlaybackProgressByAudioUrl(
      audioUrl,
      positionMs,
      feedUrl: feedUrl,
    );
  };
  _audioHandler.onEpisodeStarted = (item) {
    // Keep 'last played' record current so app restart restores the right
    // episode even when auto-advance happens while the app is backgrounded.
    return podcastState.rememberLastPlayedEpisode(item, 0);
  };

  final startupLog =
      '[LocalCache][Main] Logging active. Play an episode and search logs for LocalCache';
  developer.log(startupLog, name: 'LocalCache');

  // Load the TESD pod data
  podcastState.loadTESDData();
  await podcastState.restoreLastPlayedEpisodeIntoHandler(_audioHandler);
  //podcastState.clearAll();

  runApp(ChangeNotifierProvider(create: (_) => podcastState, child: MyApp()));
  unawaited(podcastState.syncFeedsOnStartup());
  // Interruption handling (phone calls, headphones) is managed inside
  // AudioPlayerHandler so it works in background and when phone is locked.
}

class MyApp extends StatefulWidget {
  @override
  State<MyApp> createState() => _MyAppState();
}

class _MyAppState extends State<MyApp> with WidgetsBindingObserver {
  PodcastAppState? _podcastState;

  @override
  void initState() {
    super.initState();
    WidgetsBinding.instance.addObserver(this);
    WidgetsBinding.instance.addPostFrameCallback((_) {
      _podcastState?.refreshConnectivityStatus();
    });
  }

  @override
  void didChangeDependencies() {
    super.didChangeDependencies();
    _podcastState ??= Provider.of<PodcastAppState>(context, listen: false);
  }

  @override
  void dispose() {
    WidgetsBinding.instance.removeObserver(this);
    super.dispose();
  }

  @override
  void didChangeAppLifecycleState(AppLifecycleState state) {
    if (state == AppLifecycleState.resumed) {
      _podcastState?.refreshConnectivityStatus();
      unawaited(_podcastState?.syncFeedsOnStartup());
      // Fallback: if we were playing before an interruption and the
      // interruption-end event was never delivered (some OEMs don't send
      // AUDIOFOCUS_GAIN after permanent focus loss), try to resume now
      // that the user has returned to the app.
      _audioHandler.tryResumeAfterInterruption();
      return;
    }

    if (state == AppLifecycleState.inactive ||
        state == AppLifecycleState.paused ||
        state == AppLifecycleState.detached) {
      final stateRef = _podcastState;
      if (stateRef != null) {
        unawaited(stateRef.captureCurrentPlaybackAsLastPlayed());
      }
    }
  }

  @override
  Widget build(BuildContext context) {
    final podcastState = Provider.of<PodcastAppState>(context);

    return MaterialApp(
      navigatorKey: _appNavigatorKey,
      navigatorObservers: [_routeObserver],
      title: 'Ulticast Podcast App',
      themeMode: podcastState.isDarkMode ? ThemeMode.dark : ThemeMode.light,
      theme: ThemeData(
        colorScheme: ColorScheme.fromSeed(seedColor: Colors.blueGrey),
        useMaterial3: true,
      ),
      darkTheme: ThemeData(
        colorScheme: ColorScheme.fromSeed(
          seedColor: Colors.blueGrey,
          brightness: Brightness.dark,
        ),
        useMaterial3: true,
      ),
      builder: (context, child) {
        return Stack(
          children: [
            if (child != null) child,
            MediaControlOverlay(),
          ],
        );
      },
      home: PodcastsPage(),
      routes: {
        '/search': (context) => HomePage(),
        '/episodes': (context) => EpisodesPage(),
        '/podcasts': (context) => PodcastsPage(),
        '/audio': (context) => AudioPage(),
      },
    );
  }
}

// Async function to fetch and parse podcast feed
Future<List<String>> fetchPodcast(String feedUrl) async {
  final response = await http.get(Uri.parse(feedUrl));

  if (response.statusCode == 200) {
    final converter = Xml2Map(response.body);
    final data = await converter.transform();

    final List<String> episodeTitles = [];
    final List<dynamic> episodes = data!['rss']!['channel']!['item'];
    for (var episode in episodes) {
      episodeTitles.add(episode['title']);
    }
    return episodeTitles;
  } else {
    throw Exception('Failed to load podcast');
  }
}

class HomePage extends StatefulWidget {
  const HomePage({Key? key}) : super(key: key);

  @override
  _HomePageState createState() => _HomePageState();
}

class _HomePageState extends State<HomePage> {
  final TextEditingController _controller = TextEditingController();
  Timer? _debounce;
  List<Map<String, dynamic>> _searchResults = [];
  bool _isSearching = false;
  bool _isAdding = false;
  String _searchError = '';

  @override
  void initState() {
    super.initState();
    _controller.addListener(_onSearchChanged);
  }

  @override
  void dispose() {
    _controller.removeListener(_onSearchChanged);
    _controller.dispose();
    _debounce?.cancel();
    super.dispose();
  }

  void _onSearchChanged() {
    final text = _controller.text.trim();
    if (_debounce?.isActive ?? false) _debounce!.cancel();
    // If it looks like a URL, skip iTunes search
    if (text.startsWith('http://') || text.startsWith('https://')) {
      setState(() {
        _searchResults = [];
        _isSearching = false;
        _searchError = '';
      });
      return;
    }
    if (text.length < 2) {
      setState(() {
        _searchResults = [];
        _isSearching = false;
        _searchError = '';
      });
      return;
    }
    setState(() => _isSearching = true);
    _debounce = Timer(const Duration(milliseconds: 500), () => _runSearch(text));
  }

  Future<void> _runSearch(String query) async {
    try {
      final uri = Uri.https('itunes.apple.com', '/search', {
        'term': query,
        'media': 'podcast',
        'entity': 'podcast',
        'limit': '20',
      });
      final response = await http.get(uri);
      if (!mounted) return;
      if (response.statusCode == 200) {
        final decoded = json.decode(response.body) as Map<String, dynamic>;
        final results = (decoded['results'] as List<dynamic>)
            .map((e) => e as Map<String, dynamic>)
            .toList();
        setState(() {
          _searchResults = results;
          _isSearching = false;
          _searchError = '';
        });
      } else {
        setState(() {
          _isSearching = false;
          _searchError = 'iTunes search failed (${response.statusCode})';
        });
      }
    } catch (e) {
      if (!mounted) return;
      setState(() {
        _isSearching = false;
        _searchError = 'Could not reach iTunes search';
      });
    }
  }

  Future<void> _addPodcastByUrl(String feedUrl) async {
    setState(() => _isAdding = true);
    final provider = Provider.of<PodcastAppState>(context, listen: false);
    await provider.loadPodcast(feedUrl);
    if (!mounted) return;
    setState(() => _isAdding = false);
    final loadError = provider.error(feedUrl);
    if (loadError != null && loadError.isNotEmpty) {
      ScaffoldMessenger.of(context).showSnackBar(
        SnackBar(content: Text(loadError)),
      );
      return;
    }
    Navigator.pop(context);
  }

  @override
  Widget build(BuildContext context) {
    final text = _controller.text.trim();
    final bool isUrlMode = text.startsWith('http');
    return Scaffold(
      appBar: AppBar(title: const Text('Add Podcast')),
      body: _isAdding
          ? const Center(
              child: Column(
                mainAxisSize: MainAxisSize.min,
                children: [
                  CircularProgressIndicator(),
                  SizedBox(height: 16),
                  Text('Loading podcast...'),
                ],
              ),
            )
          : Column(
              children: [
                Padding(
                  padding: const EdgeInsets.fromLTRB(16, 16, 16, 8),
                  child: TextField(
                    controller: _controller,
                    autofocus: true,
                    decoration: InputDecoration(
                      labelText: isUrlMode ? 'RSS feed URL' : 'Search podcasts',
                      hintText: 'Search by name or paste an RSS URL',
                      border: const OutlineInputBorder(),
                      prefixIcon: const Icon(Icons.search),
                      suffixIcon: text.isNotEmpty
                          ? IconButton(
                              icon: const Icon(Icons.clear),
                              onPressed: () {
                                _controller.clear();
                                setState(() {
                                  _searchResults = [];
                                  _searchError = '';
                                });
                              },
                            )
                          : null,
                    ),
                  ),
                ),
                if (isUrlMode)
                  Padding(
                    padding: const EdgeInsets.symmetric(horizontal: 16),
                    child: SizedBox(
                      width: double.infinity,
                      child: ElevatedButton(
                        onPressed: () => _addPodcastByUrl(text),
                        child: const Text('Add by RSS URL'),
                      ),
                    ),
                  ),
                if (_isSearching)
                  const Padding(
                    padding: EdgeInsets.all(24),
                    child: CircularProgressIndicator(),
                  )
                else if (_searchError.isNotEmpty)
                  Padding(
                    padding: const EdgeInsets.all(16),
                    child: Text(
                      _searchError,
                      style: TextStyle(
                          color: Theme.of(context).colorScheme.error),
                    ),
                  )
                else if (_searchResults.isNotEmpty)
                  Expanded(
                    child: ListView.builder(
                      itemCount: _searchResults.length,
                      itemBuilder: (context, index) {
                        final result = _searchResults[index];
                        final name = (result['collectionName'] ??
                                result['trackName'] ??
                                'Unknown')
                            .toString();
                        final artist =
                            (result['artistName'] ?? '').toString();
                        final artworkUrl =
                            (result['artworkUrl100'] ?? '').toString();
                        final feedUrl =
                            (result['feedUrl'] ?? '').toString();
                        return ListTile(
                          leading: artworkUrl.isNotEmpty
                              ? ClipRRect(
                                  borderRadius: BorderRadius.circular(6),
                                  child: Image.network(
                                    artworkUrl,
                                    width: 50,
                                    height: 50,
                                    fit: BoxFit.cover,
                                    errorBuilder: (c, e, s) => const Icon(
                                        Icons.podcasts,
                                        size: 40),
                                  ),
                                )
                              : const Icon(Icons.podcasts, size: 40),
                          title: Text(name,
                              maxLines: 1,
                              overflow: TextOverflow.ellipsis),
                          subtitle: artist.isNotEmpty
                              ? Text(artist,
                                  maxLines: 1,
                                  overflow: TextOverflow.ellipsis)
                              : null,
                          trailing: feedUrl.isNotEmpty
                              ? const Icon(Icons.add_circle_outline)
                              : const Icon(Icons.block, color: Colors.grey),
                          onTap: feedUrl.isNotEmpty
                              ? () => _addPodcastByUrl(feedUrl)
                              : null,
                        );
                      },
                    ),
                  )
                else if (text.length >= 2 && !isUrlMode)
                  const Padding(
                    padding: EdgeInsets.all(24),
                    child: Text('No results found'),
                  ),
              ],
            ),
    );
  }
}

class PodcastsPage extends StatefulWidget {
  @override
  _PodcastsPageState createState() => _PodcastsPageState();
}

class _PodcastsPageState extends State<PodcastsPage> {
  bool selectionMode = false;
  List<String> selectedFeeds = [];

  Future<bool> _confirmDeletePodcast(String title) async {
    final confirmed = await showDialog<bool>(
      context: context,
      builder: (dialogContext) {
        return AlertDialog(
          title: const Text('Delete Podcast?'),
          content: Text(
            'Remove "$title" and its saved episode state from the app?',
          ),
          actions: [
            TextButton(
              onPressed: () => Navigator.of(dialogContext).pop(false),
              child: const Text('Cancel'),
            ),
            TextButton(
              onPressed: () => Navigator.of(dialogContext).pop(true),
              style: TextButton.styleFrom(foregroundColor: Colors.red),
              child: const Text('Delete'),
            ),
          ],
        );
      },
    );
    return confirmed == true;
  }

  Widget _offlineArtwork({double size = 50}) {
    return Container(
      width: size,
      height: size,
      color: Colors.grey.shade300,
      alignment: Alignment.center,
      child: const Icon(Icons.cloud_off, size: 18),
    );
  }

  Widget _podcastArtwork(Map<String, dynamic> podcast, bool isOffline) {
    final localImagePath = (podcast['localImagePath'] ?? '').toString();
    final networkImage = (podcast['imageUrl'] ??
            'https://podcastaddict.com/res/images/apple-icon-57x57.png')
        .toString();

    final networkFallback = isOffline
        ? _offlineArtwork()
        : Image.network(
            networkImage,
            width: 50,
            height: 50,
            fit: BoxFit.cover,
            errorBuilder: (c, e, s) => _offlineArtwork(),
          );

    if (localImagePath.isEmpty) return networkFallback;

    return Image.file(
      File(localImagePath),
      width: 50,
      height: 50,
      fit: BoxFit.cover,
      errorBuilder: (c, e, s) => networkFallback,
    );
  }

  int _readPositionMs(dynamic value) {
    if (value is int) return value;
    if (value is num) return value.toInt();
    if (value is String) return int.tryParse(value) ?? 0;
    return 0;
  }

  List<Map<String, dynamic>> _episodeMaps(Map<String, dynamic> podcast) {
    final raw = (podcast['episodes'] as List<dynamic>?) ?? const [];
    final episodes = <Map<String, dynamic>>[];
    for (final entry in raw) {
      if (entry is Map<String, dynamic>) {
        episodes.add(entry);
      } else if (entry is Map) {
        episodes.add(Map<String, dynamic>.from(entry));
      }
    }
    return episodes;
  }

  DateTime? _parseEpisodeDate(dynamic raw) {
    final value = (raw ?? '').toString().trim();
    if (value.isEmpty) return null;

    final direct = DateTime.tryParse(value);
    if (direct != null) return direct;

    final formats = [
      DateFormat("EEE, dd MMM yyyy HH:mm:ss 'GMT'", 'en_US'),
      DateFormat("EEE, dd MMM yyyy HH:mm:ss Z", 'en_US'),
      DateFormat('yyyy-MM-dd HH:mm:ss', 'en_US'),
    ];

    for (final format in formats) {
      try {
        return format.parse(value, true).toLocal();
      } catch (_) {}
    }
    return null;
  }

  List<Map<String, dynamic>> _sortedEpisodesForPodcast(
    String feedUrl,
    Map<String, dynamic> podcast,
    PodcastAppState podcastState,
  ) {
    final episodes = _episodeMaps(podcast)
        .map((episode) => Map<String, dynamic>.from(episode))
        .toList();

    final sortPref = podcastState.episodeSortForPodcast(feedUrl);
    if (sortPref == 'titleAsc') {
      episodes.sort(
        (a, b) => (a['title'] ?? '')
            .toString()
            .toLowerCase()
            .compareTo((b['title'] ?? '').toString().toLowerCase()),
      );
      return episodes;
    }

    final parsedDateCache = <Map<String, dynamic>, DateTime>{};
    DateTime cachedDate(Map<String, dynamic> episode) {
      return parsedDateCache.putIfAbsent(
        episode,
        () => _parseEpisodeDate(episode['pubDate']) ??
            DateTime.fromMillisecondsSinceEpoch(0),
      );
    }

    episodes.sort((a, b) {
      final dateA = cachedDate(a);
      final dateB = cachedDate(b);
      if (sortPref == 'oldest') {
        return dateA.compareTo(dateB);
      }
      return dateB.compareTo(dateA);
    });

    return episodes;
  }

  int? _episodeIndexToPlay(List<Map<String, dynamic>> episodes) {
    if (episodes.isEmpty) return null;

    // 1) Resume the first in-progress episode.
    for (int i = 0; i < episodes.length; i++) {
      final ep = episodes[i];
      final isPlayed = (ep['played'] ?? false) == true;
      final isInProgress = !isPlayed && _readPositionMs(ep['lastPositionMs']) > 0;
      if (isInProgress) return i;
    }

    // 2) Continue with the episode after the last played entry.
    int lastPlayedIndex = -1;
    for (int i = 0; i < episodes.length; i++) {
      final isPlayed = (episodes[i]['played'] ?? false) == true;
      if (isPlayed) lastPlayedIndex = i;
    }
    final nextIndex = lastPlayedIndex + 1;
    if (lastPlayedIndex >= 0 && nextIndex < episodes.length) {
      return nextIndex;
    }

    // 3) Default to the first episode.
    return 0;
  }

  void _playPodcastFromList(
    String feedUrl,
    Map<String, dynamic> podcast,
    PodcastAppState podcastState,
  ) {
    final episodes = _sortedEpisodesForPodcast(feedUrl, podcast, podcastState);
    final initialIndex = _episodeIndexToPlay(episodes);
    if (initialIndex == null) {
      ScaffoldMessenger.of(context).showSnackBar(
        const SnackBar(content: Text('No episodes available to play.')),
      );
      return;
    }

    var selectedIndex = initialIndex;
    var selectedEpisode = episodes[selectedIndex];
    var selectedAudioUrl = (selectedEpisode['audioUrl'] ?? '').toString();

    if (selectedAudioUrl.isEmpty) {
      final fallbackIndex = episodes.indexWhere(
        (ep) => (ep['audioUrl'] ?? '').toString().isNotEmpty,
      );
      if (fallbackIndex < 0) {
        ScaffoldMessenger.of(context).showSnackBar(
          const SnackBar(content: Text('No playable episode found.')),
        );
        return;
      }
      selectedIndex = fallbackIndex;
      selectedEpisode = episodes[selectedIndex];
      selectedAudioUrl = (selectedEpisode['audioUrl'] ?? '').toString();
      if (selectedAudioUrl.isEmpty) {
        ScaffoldMessenger.of(context).showSnackBar(
          const SnackBar(content: Text('No playable episode found.')),
        );
        return;
      }
    }

    Navigator.pushNamed(
      context,
      '/audio',
      arguments: {
        'podcast': {
          ...podcast,
          'episodes': episodes,
        },
        'episode': selectedEpisode,
        'queueEpisodes': episodes,
        'play': true,
      },
    );
  }

  
  @override
  Widget build(BuildContext context) {
    final podcastState = Provider.of<PodcastAppState>(context);

    return Scaffold(
      appBar: AppBar(
        title: Text(selectionMode ? "Select Podcasts" : "Podcasts"),
        actions: [
          if (podcastState.isOffline)
            Padding(
              padding: const EdgeInsets.symmetric(horizontal: 6),
              child: Container(
                padding: const EdgeInsets.symmetric(horizontal: 8, vertical: 4),
                decoration: BoxDecoration(
                  color: Colors.orange.withValues(alpha: 0.2),
                  borderRadius: BorderRadius.circular(999),
                ),
                child: const Row(
                  mainAxisSize: MainAxisSize.min,
                  children: [
                    Icon(Icons.cloud_off, size: 14, color: Colors.orange),
                    SizedBox(width: 4),
                    Text('Offline', style: TextStyle(fontSize: 12)),
                  ],
                ),
              ),
            ),
          if (!selectionMode)
            IconButton(
              icon: Icon(Icons.video_collection),
              tooltip: 'Select Podcasts',
              onPressed: () {
                setState(() {
                  selectionMode = true;
                  selectedFeeds.clear();
                });
              },
            ),
          if (selectionMode) ...[
            IconButton(
              icon: Icon(Icons.done),
              onPressed: () {
                // Do something with selectedFeeds
                final provider = Provider.of<PodcastAppState>(
                  context,
                  listen: false,
                );
                provider.combinePodcasts(selectedFeeds);
                setState(() {
                  selectionMode = false;
                  selectedFeeds.clear();
                });
              },
            ),
            IconButton(
              icon: Icon(Icons.close),
              onPressed: () {
                setState(() {
                  selectionMode = false;
                  selectedFeeds.clear();
                });
              },
            ),
          ],
          IconButton(
            icon: Icon(Icons.add),
            tooltip: 'Add Podcast',
            onPressed: () {
              Navigator.pushNamed(context, '/search');
            },
          ),
          IconButton(
            icon: Icon(
              podcastState.isDarkMode ? Icons.light_mode : Icons.dark_mode,
            ),
            tooltip: podcastState.isDarkMode
                ? 'Switch to light mode'
                : 'Switch to dark mode',
            onPressed: () {
              podcastState.setDarkMode(!podcastState.isDarkMode);
            },
          ),
        ],
      ),
      body: ListView.builder(
        itemCount: podcastState.podcasts.length,
        itemBuilder: (context, index) {
          final feedUrl = podcastState.podcasts.keys.elementAt(index);
          final podcast = podcastState.podcasts[feedUrl]!;
          final isSelected = selectedFeeds.contains(feedUrl);
          return ListTile(
            leading: selectionMode
                ? Checkbox(
                    value: isSelected,
                    onChanged: (checked) {
                      setState(() {
                        if (checked == true) {
                          selectedFeeds.add(feedUrl);
                        } else {
                          selectedFeeds.remove(feedUrl);
                        }
                      });
                    },
                  )
                : _podcastArtwork(podcast, podcastState.isOffline),
            title: Text(podcast['title'] ?? "Untitled"),
            trailing: selectionMode
                ? null
                : Row(
                    mainAxisSize: MainAxisSize.min,
                    children: [
                      IconButton(
                        tooltip: 'Play',
                        onPressed: () {
                          _playPodcastFromList(
                            feedUrl,
                            podcast,
                            podcastState,
                          );
                        },
                        icon: const Icon(Icons.play_arrow),
                      ),
                      IconButton(
                        tooltip: 'Delete',
                        onPressed: () async {
                          final title = (podcast['title'] ?? 'this podcast')
                              .toString();
                          final confirmed = await _confirmDeletePodcast(title);
                          if (!confirmed) return;
                          podcastState.clearPodcast(feedUrl);
                        },
                        icon: const Icon(Icons.delete_outline),
                      ),
                    ],
                  ),
            onTap: () {
              if (selectionMode) {
                setState(() {
                  if (isSelected) {
                    selectedFeeds.remove(feedUrl);
                  } else {
                    selectedFeeds.add(feedUrl);
                  }
                });
              } else {
                Navigator.pushNamed(context, '/episodes', arguments: feedUrl);
              }
            },
          );
        },
      ),
    );
  }
}

enum EpisodeFilter { all, inProgress, played, unplayed }

enum EpisodeSort { newest, oldest, titleAsc }

class EpisodesPage extends StatefulWidget {
  static const double _overlayReservedHeight = 96;

  @override
  State<EpisodesPage> createState() => _EpisodesPageState();
}

class _EpisodesPageState extends State<EpisodesPage>
  with WidgetsBindingObserver, RouteAware {
  EpisodeFilter _filter = EpisodeFilter.all;
  EpisodeSort _sort = EpisodeSort.newest;
  bool _isSearchOpen = false;
  String _searchQuery = '';
  final TextEditingController _searchController = TextEditingController();
  bool _sortLoadedFromMetadata = false;
  String? _viewPrefsLoadedForFeed;
  bool _initialAutoScrollDone = false;
  bool _pendingAutoScrollToCurrent = false;
  final ItemScrollController _itemScrollController = ItemScrollController();
  String? _cachedFeedUrl;
  List<dynamic>? _cachedEpisodesSource;
  EpisodeFilter? _cachedFilter;
  EpisodeSort? _cachedSort;
  String? _cachedSearchQuery;
  bool? _cachedIsOffline;
  int _cachedTotalCount = 0;
  List<Map<String, dynamic>> _cachedVisibleEpisodes = const [];
  final Set<String> _expandedEpisodeDescriptions = <String>{};
  PodcastAppState? _podcastState;
  ModalRoute<dynamic>? _subscribedRoute;

  @override
  void initState() {
    super.initState();
    WidgetsBinding.instance.addObserver(this);
    _searchController.addListener(_onSearchChanged);
    WidgetsBinding.instance.addPostFrameCallback((_) {
      _podcastState?.refreshConnectivityStatus();
    });
  }

  @override
  void dispose() {
    WidgetsBinding.instance.removeObserver(this);
    final route = _subscribedRoute;
    if (route is ModalRoute<void>) {
      _routeObserver.unsubscribe(this);
    }
    _searchController.removeListener(_onSearchChanged);
    _searchController.dispose();
    super.dispose();
  }

  @override
  void didChangeDependencies() {
    super.didChangeDependencies();
    _podcastState ??= Provider.of<PodcastAppState>(context, listen: false);
    final route = ModalRoute.of(context);
    if (!identical(route, _subscribedRoute) && route is ModalRoute<void>) {
      if (_subscribedRoute is ModalRoute<void>) {
        _routeObserver.unsubscribe(this);
      }
      _routeObserver.subscribe(this, route);
      _subscribedRoute = route;
    }
  }

  @override
  void didChangeAppLifecycleState(AppLifecycleState state) {
    if (state == AppLifecycleState.resumed) {
      _requestAutoScrollToCurrent();
    }
  }

  @override
  void didPopNext() {
    _requestAutoScrollToCurrent();
  }

  void _requestAutoScrollToCurrent() {
    _pendingAutoScrollToCurrent = true;
    if (mounted) {
      setState(() {});
    }
  }

  int _readPositionMs(dynamic value) {
    if (value is int) return value;
    if (value is num) return value.toInt();
    if (value is String) return int.tryParse(value) ?? 0;
    return 0;
  }

  String _formatDuration(Duration duration) {
    final hours = duration.inHours;
    final minutes = duration.inMinutes.remainder(60);
    final seconds = duration.inSeconds.remainder(60);
    return '${hours.toString().padLeft(2, '0')}:${minutes.toString().padLeft(2, '0')}:${seconds.toString().padLeft(2, '0')}';
  }

  DateTime? _parseEpisodeDate(dynamic raw) {
    final value = (raw ?? '').toString().trim();
    if (value.isEmpty) return null;

    final direct = DateTime.tryParse(value);
    if (direct != null) return direct;

    final formats = [
      DateFormat("EEE, dd MMM yyyy HH:mm:ss 'GMT'", 'en_US'),
      DateFormat("EEE, dd MMM yyyy HH:mm:ss Z", 'en_US'),
      DateFormat('yyyy-MM-dd HH:mm:ss', 'en_US'),
    ];

    for (final format in formats) {
      try {
        return format.parse(value, true).toLocal();
      } catch (_) {}
    }
    return null;
  }

  bool _matchesFilter(Map<String, dynamic> episode) {
    final isPlayed = (episode['played'] ?? false) == true;
    final lastPositionMs = _readPositionMs(episode['lastPositionMs']);
    final isInProgress = !isPlayed && lastPositionMs > 0;

    switch (_filter) {
      case EpisodeFilter.all:
        return true;
      case EpisodeFilter.inProgress:
        return isInProgress;
      case EpisodeFilter.played:
        return isPlayed;
      case EpisodeFilter.unplayed:
        return !isPlayed;
    }
  }

  bool _matchesSearch(Map<String, dynamic> episode) {
    final query = _searchQuery.trim().toLowerCase();
    if (query.isEmpty) return true;

    final title = (episode['title'] ?? '').toString().toLowerCase();
    final description = (episode['description'] ?? '').toString().toLowerCase();
    return title.contains(query) || description.contains(query);
  }

  void _onSearchChanged() {
    final next = _searchController.text.trim();
    if (next == _searchQuery) return;
    setState(() {
      _searchQuery = next;
      _isSearchOpen = next.isNotEmpty;
    });

    final feedUrl = ModalRoute.of(context)?.settings.arguments as String?;
    final podcastState = _podcastState;
    if (feedUrl == null || podcastState == null) return;
    final podcast = podcastState.podcasts[feedUrl];
    if (podcast == null) return;
    final episodesSource = (podcast['episodes'] as List<dynamic>?) ?? const [];
    final isOffline = podcastState.isOffline;

    unawaited(podcastState.setEpisodeSearchForPodcast(feedUrl, next));
    unawaited(
      _syncAudioQueueForCurrentPodcastIfActive(
        feedUrl,
        podcast,
        episodesSource,
        podcastState,
        isOffline,
      ),
    );
  }

  List<InlineSpan> _buildHighlightedSpans(String text, TextStyle baseStyle) {
    final query = _searchQuery.trim();
    if (query.isEmpty || text.isEmpty) {
      return [TextSpan(text: text, style: baseStyle)];
    }

    final lowerText = text.toLowerCase();
    final lowerQuery = query.toLowerCase();
    final highlightStyle = baseStyle.copyWith(
      fontWeight: FontWeight.w700,
      backgroundColor: Colors.yellow.withValues(alpha: 0.35),
    );

    final spans = <InlineSpan>[];
    var start = 0;
    while (true) {
      final index = lowerText.indexOf(lowerQuery, start);
      if (index < 0) {
        if (start < text.length) {
          spans.add(TextSpan(text: text.substring(start), style: baseStyle));
        }
        break;
      }

      if (index > start) {
        spans.add(
          TextSpan(text: text.substring(start, index), style: baseStyle),
        );
      }

      final matchEnd = index + lowerQuery.length;
      spans.add(
        TextSpan(
          text: text.substring(index, matchEnd),
          style: highlightStyle,
        ),
      );
      start = matchEnd;
    }

    return spans;
  }

  Widget _buildHighlightedText(
    BuildContext context, {
    required String text,
    TextStyle? style,
    int? maxLines,
    TextOverflow overflow = TextOverflow.clip,
  }) {
    final baseStyle = DefaultTextStyle.of(context).style.merge(style);
    return RichText(
      text: TextSpan(
        style: baseStyle,
        children: _buildHighlightedSpans(text, baseStyle),
      ),
      maxLines: maxLines,
      overflow: overflow,
    );
  }

  String _sortLabel(EpisodeSort sort) {
    switch (sort) {
      case EpisodeSort.newest:
        return 'Newest';
      case EpisodeSort.oldest:
        return 'Oldest';
      case EpisodeSort.titleAsc:
        return 'Title';
    }
  }

  EpisodeSort _sortFromStorageValue(String value) {
    switch (value) {
      case 'oldest':
        return EpisodeSort.oldest;
      case 'titleAsc':
        return EpisodeSort.titleAsc;
      case 'newest':
      default:
        return EpisodeSort.newest;
    }
  }

  String _sortStorageValue(EpisodeSort sort) {
    switch (sort) {
      case EpisodeSort.newest:
        return 'newest';
      case EpisodeSort.oldest:
        return 'oldest';
      case EpisodeSort.titleAsc:
        return 'titleAsc';
    }
  }

  EpisodeFilter _filterFromStorageValue(String value) {
    switch (value) {
      case 'inProgress':
        return EpisodeFilter.inProgress;
      case 'played':
        return EpisodeFilter.played;
      case 'unplayed':
        return EpisodeFilter.unplayed;
      case 'all':
      default:
        return EpisodeFilter.all;
    }
  }

  String _filterStorageValue(EpisodeFilter filter) {
    switch (filter) {
      case EpisodeFilter.all:
        return 'all';
      case EpisodeFilter.inProgress:
        return 'inProgress';
      case EpisodeFilter.played:
        return 'played';
      case EpisodeFilter.unplayed:
        return 'unplayed';
    }
  }

  String _episodeStableKey(Map<String, dynamic> episode, int index) {
    final audioUrl = (episode['audioUrl'] ?? '').toString();
    if (audioUrl.isNotEmpty) return audioUrl;
    final guid = (episode['guid'] ?? '').toString();
    if (guid.isNotEmpty) return guid;
    return 'episode-$index';
  }

  Future<void> _handleEpisodeAction(
    BuildContext context,
    PodcastAppState podcastState,
    String feedUrl,
    Map<String, dynamic> episode,
    String action,
  ) async {
    final audioUrl = (episode['audioUrl'] ?? '').toString();
    if (audioUrl.isEmpty) return;

    if (action == 'mark_played') {
      await podcastState.markEpisodePlayedByAudioUrl(
        audioUrl,
        played: true,
        feedUrl: feedUrl,
      );
    } else if (action == 'mark_unplayed') {
      await podcastState.markEpisodeUnplayedByAudioUrl(
        audioUrl,
        feedUrl: feedUrl,
      );
    } else if (action == 'reset_progress') {
      await podcastState.resetEpisodeProgressByAudioUrl(
        audioUrl,
        feedUrl: feedUrl,
      );
    } else if (action == 'edit_episode') {
      await _showEditEpisodeDialog(
        context,
        podcastState,
        feedUrl,
        episode,
      );
      return;
    }

    if (!mounted) return;
    ScaffoldMessenger.of(context).showSnackBar(
      SnackBar(content: Text('Updated ${episode['title'] ?? 'episode'}')),
    );
  }

  Future<void> _showEditEpisodeDialog(
    BuildContext context,
    PodcastAppState podcastState,
    String feedUrl,
    Map<String, dynamic> episode,
  ) async {
    final titleController = TextEditingController(
      text: (episode['title'] ?? '').toString(),
    );
    final podcastTitleController = TextEditingController(
      text: (episode['podcastTitle'] ?? '').toString(),
    );
    final dateController = TextEditingController(
      text: (episode['pubDate'] ?? '').toString(),
    );
    final authorController = TextEditingController(
      text: (episode['author'] ?? '').toString(),
    );
    final descriptionController = TextEditingController(
      text: (episode['description'] ?? '').toString(),
    );

    final action = await showDialog<String>(
      context: context,
      builder: (dialogContext) {
        return AlertDialog(
          title: const Text('Edit Episode'),
          content: SizedBox(
            width: 560,
            child: SingleChildScrollView(
              child: Column(
                mainAxisSize: MainAxisSize.min,
                children: [
                  TextField(
                    controller: titleController,
                    decoration: const InputDecoration(labelText: 'Title'),
                  ),
                  TextField(
                    controller: podcastTitleController,
                    decoration: const InputDecoration(
                      labelText: 'Podcast Title',
                    ),
                  ),
                  TextField(
                    controller: dateController,
                    decoration: const InputDecoration(labelText: 'Date'),
                  ),
                  TextField(
                    controller: authorController,
                    decoration: const InputDecoration(labelText: 'Author'),
                  ),
                  TextField(
                    controller: descriptionController,
                    minLines: 3,
                    maxLines: 8,
                    decoration: const InputDecoration(labelText: 'Description'),
                  ),
                ],
              ),
            ),
          ),
          actions: [
            TextButton(
              onPressed: () async {
                final confirmed = await showDialog<bool>(
                  context: dialogContext,
                  builder: (confirmContext) {
                    return AlertDialog(
                      title: const Text('Delete Episode?'),
                      content: Text(
                        'Delete "${(episode['title'] ?? 'this episode').toString()}" from this podcast?',
                      ),
                      actions: [
                        TextButton(
                          onPressed: () => Navigator.of(confirmContext).pop(false),
                          child: const Text('Cancel'),
                        ),
                        TextButton(
                          onPressed: () => Navigator.of(confirmContext).pop(true),
                          style: TextButton.styleFrom(
                            foregroundColor: Colors.red,
                          ),
                          child: const Text('Delete'),
                        ),
                      ],
                    );
                  },
                );
                if (confirmed == true && dialogContext.mounted) {
                  Navigator.of(dialogContext).pop('delete');
                }
              },
              style: TextButton.styleFrom(foregroundColor: Colors.red),
              child: const Text('Delete'),
            ),
            TextButton(
              onPressed: () => Navigator.of(dialogContext).pop('cancel'),
              child: const Text('Cancel'),
            ),
            ElevatedButton(
              onPressed: () => Navigator.of(dialogContext).pop('save'),
              child: const Text('Save'),
            ),
          ],
        );
      },
    );

    if (action != 'save' && action != 'delete') {
      titleController.dispose();
      podcastTitleController.dispose();
      dateController.dispose();
      authorController.dispose();
      descriptionController.dispose();
      return;
    }

    if (action == 'delete') {
      final removed = await podcastState.removeEpisodeFromPodcast(
        feedUrl,
        episode,
      );

      titleController.dispose();
      podcastTitleController.dispose();
      dateController.dispose();
      authorController.dispose();
      descriptionController.dispose();

      if (!mounted) return;
      ScaffoldMessenger.of(context).showSnackBar(
        SnackBar(
          content: Text(
            removed ? 'Episode removed from this podcast' : 'Could not remove episode',
          ),
        ),
      );
      return;
    }

    final updates = <String, dynamic>{
      'title': titleController.text.trim(),
      'podcastTitle': podcastTitleController.text.trim(),
      'pubDate': dateController.text.trim(),
      'author': authorController.text.trim(),
      'description': descriptionController.text,
    };

    final success = await podcastState.updateEpisodeMetadataByAudioUrl(
      feedUrl,
      (episode['audioUrl'] ?? '').toString(),
      updates,
    );

    titleController.dispose();
    podcastTitleController.dispose();
    dateController.dispose();
    authorController.dispose();
    descriptionController.dispose();

    if (!mounted) return;
    ScaffoldMessenger.of(context).showSnackBar(
      SnackBar(
        content: Text(
          success ? 'Episode updated' : 'Episode not found for update',
        ),
      ),
    );
  }

  void _refreshVisibleEpisodesIfNeeded(
    String feedUrl,
    List<dynamic> episodesSource,
    PodcastAppState podcastState,
    bool isOffline,
  ) {
    final shouldRefresh = _cachedFeedUrl != feedUrl ||
        !identical(_cachedEpisodesSource, episodesSource) ||
        _cachedFilter != _filter ||
        _cachedSort != _sort ||
      _cachedSearchQuery != _searchQuery ||
        _cachedIsOffline != isOffline;
    if (!shouldRefresh) return;

    final episodeMaps = <Map<String, dynamic>>[];
    for (final entry in episodesSource) {
      if (entry is Map<String, dynamic>) {
        episodeMaps.add(entry);
      } else if (entry is Map) {
        episodeMaps.add(Map<String, dynamic>.from(entry));
      }
    }

    final filtered = episodeMaps.where((episode) {
      if (isOffline && !podcastState.isEpisodeDownloaded(episode)) {
        return false;
      }
      return _matchesFilter(episode) && _matchesSearch(episode);
    }).toList();
    if (_sort == EpisodeSort.titleAsc) {
      filtered.sort(
        (a, b) => (a['title'] ?? '')
            .toString()
            .toLowerCase()
            .compareTo((b['title'] ?? '').toString().toLowerCase()),
      );
    } else {
      final parsedDateCache = <Map<String, dynamic>, DateTime>{};
      DateTime cachedDate(Map<String, dynamic> episode) {
        return parsedDateCache.putIfAbsent(
          episode,
          () => _parseEpisodeDate(episode['pubDate']) ??
              DateTime.fromMillisecondsSinceEpoch(0),
        );
      }

      filtered.sort((a, b) {
        final dateA = cachedDate(a);
        final dateB = cachedDate(b);
        if (_sort == EpisodeSort.newest) {
          return dateB.compareTo(dateA);
        }
        return dateA.compareTo(dateB);
      });
    }

    _cachedFeedUrl = feedUrl;
    _cachedEpisodesSource = episodesSource;
    _cachedFilter = _filter;
    _cachedSort = _sort;
    _cachedSearchQuery = _searchQuery;
    _cachedIsOffline = isOffline;
    _cachedTotalCount = episodeMaps.length;
    _cachedVisibleEpisodes = filtered;
  }

  void _scheduleAutoScrollToCurrentEpisode(
    List<Map<String, dynamic>> visibleEpisodes, {
    bool force = false,
  }) {
    if (!force && _initialAutoScrollDone) {
      return;
    }
    if (visibleEpisodes.isEmpty) {
      _initialAutoScrollDone = true;
      _pendingAutoScrollToCurrent = false;
      return;
    }

    int? targetIndex;

    // First priority: find the last (most recent) in-progress episode
    // This handles the case where current playing episode is the latest
    for (int i = visibleEpisodes.length - 1; i >= 0; i--) {
      final episode = visibleEpisodes[i];
      final isPlayed = (episode['played'] ?? false) == true;
      final isInProgress = !isPlayed && _readPositionMs(episode['lastPositionMs']) > 0;
      if (isInProgress) {
        targetIndex = i;
        break;
      }
    }

    // If no in-progress found, find the last played episode
    if (targetIndex == null) {
      for (int i = visibleEpisodes.length - 1; i >= 0; i--) {
        final episode = visibleEpisodes[i];
        final isPlayed = (episode['played'] ?? false) == true;
        if (isPlayed) {
          targetIndex = i;
          break;
        }
      }
    }

    _initialAutoScrollDone = true;
    _pendingAutoScrollToCurrent = false;
    if (targetIndex == null || targetIndex <= 0) {
      return;
    }

    WidgetsBinding.instance.addPostFrameCallback((_) {
      if (!mounted || !_itemScrollController.isAttached) return;
      _itemScrollController.jumpTo(index: targetIndex!, alignment: 0.02);
    });
  }

  List<Map<String, dynamic>> _queueEpisodesForSortState(
    List<dynamic> episodesSource,
    PodcastAppState podcastState,
    bool isOffline,
  ) {
    final episodeMaps = <Map<String, dynamic>>[];
    for (final entry in episodesSource) {
      if (entry is Map<String, dynamic>) {
        episodeMaps.add(Map<String, dynamic>.from(entry));
      } else if (entry is Map) {
        episodeMaps.add(Map<String, dynamic>.from(entry));
      }
    }

    final filtered = episodeMaps.where((episode) {
      if (isOffline && !podcastState.isEpisodeDownloaded(episode)) {
        return false;
      }
      return _matchesFilter(episode) && _matchesSearch(episode);
    }).toList();

    if (_sort == EpisodeSort.titleAsc) {
      filtered.sort(
        (a, b) => (a['title'] ?? '')
            .toString()
            .toLowerCase()
            .compareTo((b['title'] ?? '').toString().toLowerCase()),
      );
      return filtered;
    }

    final parsedDateCache = <Map<String, dynamic>, DateTime>{};
    DateTime cachedDate(Map<String, dynamic> episode) {
      return parsedDateCache.putIfAbsent(
        episode,
        () => _parseEpisodeDate(episode['pubDate']) ??
            DateTime.fromMillisecondsSinceEpoch(0),
      );
    }

    filtered.sort((a, b) {
      final dateA = cachedDate(a);
      final dateB = cachedDate(b);
      if (_sort == EpisodeSort.newest) {
        return dateB.compareTo(dateA);
      }
      return dateA.compareTo(dateB);
    });

    return filtered;
  }

  Future<void> _syncAudioQueueForCurrentPodcastIfActive(
    String feedUrl,
    Map<String, dynamic> podcast,
    List<dynamic> episodesSource,
    PodcastAppState podcastState,
    bool isOffline,
  ) async {
    final activeItem = _audioHandler.mediaItem.value;
    final activeFeedUrl = (activeItem?.extras?['feedUrl'] ?? '').toString();
    if (activeFeedUrl != feedUrl) return;

    final queueEpisodes = _queueEpisodesForSortState(
      episodesSource,
      podcastState,
      isOffline,
    );
    final mediaItems = queueEpisodes
        .map((episode) => podcastState._mediaItemFromEpisode(episode, podcast))
        .where((item) => item.id.isNotEmpty)
        .toList(growable: false);

    await _audioHandler.syncEpisodeQueuePreservingCurrent(mediaItems);
  }

  Future<void> _persistViewPrefsAndSyncQueue(
    String feedUrl,
    Map<String, dynamic> podcast,
    List<dynamic> episodesSource,
    PodcastAppState podcastState,
    bool isOffline,
  ) async {
    await podcastState.setEpisodeFilterForPodcast(
      feedUrl,
      _filterStorageValue(_filter),
    );
    await podcastState.setEpisodeSearchForPodcast(feedUrl, _searchQuery);
    await _syncAudioQueueForCurrentPodcastIfActive(
      feedUrl,
      podcast,
      episodesSource,
      podcastState,
      isOffline,
    );
  }

  List<Map<String, dynamic>> _audioRouteQueueEpisodes(
    List<Map<String, dynamic>> visibleEpisodes,
  ) {
    return visibleEpisodes
        .map((episode) => Map<String, dynamic>.from(episode))
        .toList(growable: false);
  }

  @override
  Widget build(BuildContext context) {
    final mediaQuery = MediaQuery.of(context);
    final bottomSystemInset = [
      mediaQuery.padding.bottom,
      mediaQuery.viewPadding.bottom,
      mediaQuery.systemGestureInsets.bottom,
    ].reduce((a, b) => a > b ? a : b);

    final feedUrl = ModalRoute.of(context)!.settings.arguments as String;
    final podcastState = Provider.of<PodcastAppState>(context);

    final podcast = podcastState.podcasts[feedUrl];
    if (podcast == null) {
      return Scaffold(
        appBar: AppBar(title: const Text('Episodes')),
        body: const Center(child: Text('Podcast not found. Please reopen or reload the feed.')),
      );
    }

    if (!_sortLoadedFromMetadata) {
      final persistedSort = podcastState.episodeSortForPodcast(feedUrl);
      _sort = _sortFromStorageValue(persistedSort);
      _sortLoadedFromMetadata = true;
    }

    if (_viewPrefsLoadedForFeed != feedUrl) {
      final persistedFilter = podcastState.episodeFilterForPodcast(feedUrl);
      final persistedSearch = podcastState.episodeSearchForPodcast(feedUrl);
      _filter = _filterFromStorageValue(persistedFilter);
      _searchQuery = persistedSearch;
      _isSearchOpen = persistedSearch.isNotEmpty;
      if (_searchController.text != persistedSearch) {
        _searchController.value = TextEditingValue(
          text: persistedSearch,
          selection: TextSelection.collapsed(offset: persistedSearch.length),
        );
      }
      _viewPrefsLoadedForFeed = feedUrl;
    }

    final isOffline = podcastState.isOffline;
    final episodesSource = (podcast['episodes'] as List<dynamic>?) ?? const [];
    _refreshVisibleEpisodesIfNeeded(
      feedUrl,
      episodesSource,
      podcastState,
      isOffline,
    );
    final visibleEpisodes = _cachedVisibleEpisodes;
    final downloadedCount = episodesSource.where((entry) {
      if (entry is Map<String, dynamic>) {
        return podcastState.isEpisodeDownloaded(entry);
      }
      if (entry is Map) {
        return podcastState.isEpisodeDownloaded(Map<String, dynamic>.from(entry));
      }
      return false;
    }).length;
    _scheduleAutoScrollToCurrentEpisode(
      visibleEpisodes,
      force: _pendingAutoScrollToCurrent,
    );
    final error = podcastState.error(feedUrl) ?? podcast['error'];

    return Scaffold(
      appBar: AppBar(
        title: _isSearchOpen
            ? TextField(
                controller: _searchController,
                autofocus: true,
                textInputAction: TextInputAction.search,
                decoration: const InputDecoration(
                  hintText: 'Search title or description',
                  border: InputBorder.none,
                ),
              )
            : Text(
                podcast['title'] ?? 'Episodes',
                overflow: TextOverflow.ellipsis,
              ),
        actions: [
          if (isOffline)
            Padding(
              padding: const EdgeInsets.symmetric(horizontal: 8),
              child: Container(
                padding: const EdgeInsets.symmetric(horizontal: 8, vertical: 4),
                decoration: BoxDecoration(
                  color: Colors.orange.withValues(alpha: 0.2),
                  borderRadius: BorderRadius.circular(999),
                ),
                child: const Row(
                  mainAxisSize: MainAxisSize.min,
                  children: [
                    Icon(Icons.cloud_off, size: 14, color: Colors.orange),
                    SizedBox(width: 4),
                    Text('Offline', style: TextStyle(fontSize: 12)),
                  ],
                ),
              ),
            ),
          IconButton(
            tooltip: _isSearchOpen ? 'Close search' : 'Search episodes',
            icon: Icon(_isSearchOpen ? Icons.close : Icons.search),
            onPressed: () async {
              setState(() {
                if (_isSearchOpen) {
                  _searchController.clear();
                  _searchQuery = '';
                }
                _isSearchOpen = !_isSearchOpen;
              });
              await _persistViewPrefsAndSyncQueue(
                feedUrl,
                podcast,
                episodesSource,
                podcastState,
                isOffline,
              );
            },
          ),
        ],
      ),
      body: Column(
        children: [
          Padding(
            padding: const EdgeInsets.fromLTRB(12, 8, 12, 4),
            child: Column(
              children: [
                if (isOffline)
                  Padding(
                    padding: const EdgeInsets.only(bottom: 8),
                    child: Row(
                      children: [
                        Icon(
                          Icons.download_done,
                          size: 16,
                          color: Theme.of(context).colorScheme.primary,
                        ),
                        const SizedBox(width: 6),
                        const Expanded(
                          child: Text(
                            'Offline mode: showing downloaded episodes only',
                          ),
                        ),
                      ],
                    ),
                  ),
                SingleChildScrollView(
                  scrollDirection: Axis.horizontal,
                  child: Row(
                    children: [
                      ChoiceChip(
                        label: const Text('All'),
                        selected: _filter == EpisodeFilter.all,
                        onSelected: (_) async {
                          setState(() => _filter = EpisodeFilter.all);
                          await _persistViewPrefsAndSyncQueue(
                            feedUrl,
                            podcast,
                            episodesSource,
                            podcastState,
                            isOffline,
                          );
                        },
                      ),
                      const SizedBox(width: 8),
                      ChoiceChip(
                        label: const Text('In Progress'),
                        selected: _filter == EpisodeFilter.inProgress,
                        onSelected: (_) async {
                          setState(() => _filter = EpisodeFilter.inProgress);
                          await _persistViewPrefsAndSyncQueue(
                            feedUrl,
                            podcast,
                            episodesSource,
                            podcastState,
                            isOffline,
                          );
                        },
                      ),
                      const SizedBox(width: 8),
                      ChoiceChip(
                        label: const Text('Played'),
                        selected: _filter == EpisodeFilter.played,
                        onSelected: (_) async {
                          setState(() => _filter = EpisodeFilter.played);
                          await _persistViewPrefsAndSyncQueue(
                            feedUrl,
                            podcast,
                            episodesSource,
                            podcastState,
                            isOffline,
                          );
                        },
                      ),
                      const SizedBox(width: 8),
                      ChoiceChip(
                        label: const Text('Unplayed'),
                        selected: _filter == EpisodeFilter.unplayed,
                        onSelected: (_) async {
                          setState(() => _filter = EpisodeFilter.unplayed);
                          await _persistViewPrefsAndSyncQueue(
                            feedUrl,
                            podcast,
                            episodesSource,
                            podcastState,
                            isOffline,
                          );
                        },
                      ),
                    ],
                  ),
                ),
                const SizedBox(height: 8),
                Row(
                  children: [
                    const Text('Sort:'),
                    const SizedBox(width: 8),
                    DropdownButton<EpisodeSort>(
                      value: _sort,
                      onChanged: (value) async {
                        if (value == null) return;
                        setState(() => _sort = value);
                        await podcastState.setEpisodeSortForPodcast(
                          feedUrl,
                          _sortStorageValue(value),
                        );
                        await _syncAudioQueueForCurrentPodcastIfActive(
                          feedUrl,
                          podcast,
                          episodesSource,
                          podcastState,
                          isOffline,
                        );
                      },
                      items: EpisodeSort.values
                          .map(
                            (sort) => DropdownMenuItem<EpisodeSort>(
                              value: sort,
                              child: Text(_sortLabel(sort)),
                            ),
                          )
                          .toList(),
                    ),
                    const Spacer(),
                    Text(
                      isOffline
                          ? '${visibleEpisodes.length}/$downloadedCount downloaded'
                          : '${visibleEpisodes.length}/${_cachedTotalCount}',
                    ),
                  ],
                ),
              ],
            ),
          ),
          if (podcastState.isLoading(feedUrl))
            Center(child: CircularProgressIndicator())
          else if (error != null)
            Center(child: Text("Error: $error"))
          else if (visibleEpisodes.isEmpty)
            Center(child: Text("No episodes found"))
          else
            Expanded(
              child: ScrollablePositionedList.separated(
                itemScrollController: _itemScrollController,
                padding: EdgeInsets.only(
                  bottom: EpisodesPage._overlayReservedHeight + bottomSystemInset,
                ),
                itemCount: visibleEpisodes.length,
                itemBuilder: (context, index) {
                  final episode = visibleEpisodes[index];
                  final episodeKey = _episodeStableKey(episode, index);
                  final isPlayed = (episode['played'] ?? false) == true;
                  final isDownloaded = podcastState.isEpisodeDownloaded(episode);
                  final isPlayableOffline = !isOffline || isDownloaded;
                  final lastPositionMs = _readPositionMs(episode['lastPositionMs']);
                  final isInProgress = !isPlayed && lastPositionMs > 0;
                    final localEpisodePath =
                      (episode['localImagePath'] ?? '').toString();
                    final localPodcastPath =
                      (podcast['localImagePath'] ?? '').toString();

                  final podcastTitle =
                      (episode['podcastTitle'] ?? podcast['title'] ?? '')
                          .toString();
                  final pubDateText = (episode['pubDate'] ?? '').toString();
                    final descriptionText = (episode['description'] ?? '').toString();
                    final isDescriptionExpanded =
                      _expandedEpisodeDescriptions.contains(episodeKey);

                  final offlineArtwork = Container(
                    width: 52,
                    height: 52,
                    color: Colors.grey.shade300,
                    alignment: Alignment.center,
                    child: const Icon(Icons.cloud_off, size: 18),
                  );

                  final networkArtwork = isOffline
                      ? offlineArtwork
                      : Image.network(
                          episode['imageUrl'] ?? 'https://via.placeholder.com/100',
                          width: 52,
                          height: 52,
                          fit: BoxFit.cover,
                          errorBuilder: (c, e, s) => offlineArtwork,
                        );

                  Widget artwork;
                  if (localEpisodePath.isNotEmpty) {
                    artwork = Image.file(
                      File(localEpisodePath),
                      width: 52,
                      height: 52,
                      fit: BoxFit.cover,
                      errorBuilder: (c, e, s) {
                        if (localPodcastPath.isNotEmpty) {
                          return Image.file(
                            File(localPodcastPath),
                            width: 52,
                            height: 52,
                            fit: BoxFit.cover,
                            errorBuilder: (c, e, s) => networkArtwork,
                          );
                        }
                        return networkArtwork;
                      },
                    );
                  } else if (localPodcastPath.isNotEmpty) {
                    artwork = Image.file(
                      File(localPodcastPath),
                      width: 52,
                      height: 52,
                      fit: BoxFit.cover,
                      errorBuilder: (c, e, s) => networkArtwork,
                    );
                  } else {
                    artwork = networkArtwork;
                  }

                  return InkWell(
                    onTap: () {
                      if (!isPlayableOffline) {
                        ScaffoldMessenger.of(context).showSnackBar(
                          const SnackBar(
                            content: Text(
                              "Can't play this episode offline. Download it first while online.",
                            ),
                          ),
                        );
                        return;
                      }
                      Navigator.pushNamed(
                        context,
                        '/audio',
                        arguments: {
                          'podcast': podcast,
                          'episode': episode,
                          'queueEpisodes': _audioRouteQueueEpisodes(visibleEpisodes),
                          'play': false,
                        },
                      );
                    },
                    child: Padding(
                      padding: const EdgeInsets.symmetric(
                        horizontal: 12,
                        vertical: 8,
                      ),
                      child: Column(
                        crossAxisAlignment: CrossAxisAlignment.start,
                        children: [
                          _buildHighlightedText(
                            context,
                            text: (episode['title'] ?? '').toString(),
                            maxLines: 2,
                            overflow: TextOverflow.ellipsis,
                            style: isPlayed
                                ? const TextStyle(
                                    decoration: TextDecoration.lineThrough,
                                    color: Colors.grey,
                                  )
                                : null,
                          ),
                          const SizedBox(height: 8),
                          Row(
                            crossAxisAlignment: CrossAxisAlignment.start,
                            children: [
                              ClipRRect(
                                borderRadius: BorderRadius.circular(6),
                                child: artwork,
                              ),
                              const SizedBox(width: 10),
                              Expanded(
                                child: Column(
                                  crossAxisAlignment: CrossAxisAlignment.start,
                                  children: [
                                    if (podcastTitle.isNotEmpty)
                                      Text(
                                        podcastTitle,
                                        maxLines: 1,
                                        overflow: TextOverflow.ellipsis,
                                        style: Theme.of(context)
                                            .textTheme
                                            .bodySmall,
                                      ),
                                    if (pubDateText.isNotEmpty)
                                      Text(
                                        pubDateText,
                                        maxLines: 1,
                                        overflow: TextOverflow.ellipsis,
                                        style: Theme.of(context)
                                            .textTheme
                                            .bodySmall,
                                      ),
                                    const SizedBox(height: 4),
                                    Wrap(
                                      spacing: 8,
                                      runSpacing: 4,
                                      children: [
                                        if (isPlayed)
                                          const Text(
                                            'Played',
                                            style: TextStyle(
                                              color: Colors.green,
                                              fontWeight: FontWeight.w600,
                                            ),
                                          ),
                                        if (isInProgress)
                                          Text(
                                            'In progress: ${_formatDuration(Duration(milliseconds: lastPositionMs))}',
                                            style: const TextStyle(
                                              color: Colors.orange,
                                              fontWeight: FontWeight.w600,
                                            ),
                                          ),
                                        if (!isPlayableOffline)
                                          const Text(
                                            'Not available offline',
                                            style: TextStyle(
                                              color: Colors.redAccent,
                                              fontWeight: FontWeight.w600,
                                            ),
                                          ),
                                      ],
                                    ),
                                  ],
                                ),
                              ),
                              Row(
                                mainAxisSize: MainAxisSize.min,
                                children: [
                                  Builder(
                                    builder: (context) {
                                      final audioUrl =
                                          (episode['audioUrl'] ?? '').toString();
                                      final isDownloading =
                                          podcastState.isAudioDownloading(audioUrl);
                                      final isDownloaded =
                                          podcastState.isEpisodeDownloaded(episode);

                                      if (isDownloading) {
                                        return const SizedBox(
                                          width: 24,
                                          height: 24,
                                          child: Padding(
                                            padding: EdgeInsets.all(3),
                                            child: CircularProgressIndicator(
                                              strokeWidth: 2,
                                            ),
                                          ),
                                        );
                                      }

                                      if (isDownloaded) {
                                        return const Padding(
                                          padding: EdgeInsets.symmetric(
                                            horizontal: 4,
                                          ),
                                          child: Icon(
                                            Icons.download_done,
                                            color: Colors.green,
                                            size: 20,
                                          ),
                                        );
                                      }

                                      return IconButton(
                                        constraints: const BoxConstraints(
                                          minWidth: 36,
                                          minHeight: 36,
                                        ),
                                        icon: const Icon(Icons.download),
                                        tooltip: 'Download for offline playback',
                                        onPressed: () {
                                          podcastState.downloadEpisodeAudio(
                                            feedUrl,
                                            episode,
                                          );
                                        },
                                      );
                                    },
                                  ),
                                  PopupMenuButton<String>(
                                    tooltip: 'Episode actions',
                                    onSelected: (action) {
                                      _handleEpisodeAction(
                                        context,
                                        podcastState,
                                        feedUrl,
                                        episode,
                                        action,
                                      );
                                    },
                                    itemBuilder: (context) => const [
                                      PopupMenuItem(
                                        value: 'edit_episode',
                                        child: Text('Edit Episode'),
                                      ),
                                      PopupMenuItem(
                                        value: 'mark_played',
                                        child: Text('Mark Played'),
                                      ),
                                      PopupMenuItem(
                                        value: 'mark_unplayed',
                                        child: Text('Mark Unplayed'),
                                      ),
                                      PopupMenuItem(
                                        value: 'reset_progress',
                                        child: Text('Reset Progress'),
                                      ),
                                    ],
                                  ),
                                  IconButton(
                                    constraints: const BoxConstraints(
                                      minWidth: 36,
                                      minHeight: 36,
                                    ),
                                    icon: Icon(
                                      isPlayableOffline
                                          ? Icons.play_circle_outline
                                          : Icons.cloud_off,
                                    ),
                                    onPressed: () {
                                      if (!isPlayableOffline) {
                                        ScaffoldMessenger.of(context).showSnackBar(
                                          const SnackBar(
                                            content: Text(
                                              "Can't play this episode offline. Download it first while online.",
                                            ),
                                          ),
                                        );
                                        return;
                                      }
                                      Navigator.pushNamed(
                                        context,
                                        '/audio',
                                        arguments: {
                                          'podcast': podcast,
                                          'episode': episode,
                                          'queueEpisodes': _audioRouteQueueEpisodes(visibleEpisodes),
                                          'play': true,
                                        },
                                      );
                                    },
                                  ),
                                ],
                              ),
                            ],
                          ),
                          const SizedBox(height: 8),
                          Builder(
                            builder: (context) {
                              final baseStyle =
                                  Theme.of(context).textTheme.bodyMedium;
                              final showToggle =
                                  descriptionText.trim().length > 180;

                              return Column(
                                crossAxisAlignment: CrossAxisAlignment.start,
                                children: [
                                  _buildHighlightedText(
                                    context,
                                    text: descriptionText,
                                    style: baseStyle,
                                    maxLines: isDescriptionExpanded ? null : 3,
                                    overflow: isDescriptionExpanded
                                        ? TextOverflow.visible
                                        : TextOverflow.ellipsis,
                                  ),
                                  if (showToggle)
                                    Align(
                                      alignment: Alignment.centerLeft,
                                      child: TextButton(
                                        style: TextButton.styleFrom(
                                          padding: const EdgeInsets.symmetric(
                                            horizontal: 0,
                                            vertical: 2,
                                          ),
                                          minimumSize: const Size(0, 0),
                                          tapTargetSize: MaterialTapTargetSize
                                              .shrinkWrap,
                                        ),
                                        onPressed: () {
                                          setState(() {
                                            if (isDescriptionExpanded) {
                                              _expandedEpisodeDescriptions
                                                  .remove(episodeKey);
                                            } else {
                                              _expandedEpisodeDescriptions
                                                  .add(episodeKey);
                                            }
                                          });
                                        },
                                        child: Text(
                                          isDescriptionExpanded
                                              ? 'Read less'
                                              : 'Read more',
                                        ),
                                      ),
                                    ),
                                ],
                              );
                            },
                          ),
                        ],
                      ),
                    ),
                  );
                },
                separatorBuilder: (context, index) => Divider(),
              ),
            ),
        ],
      ),
    );
  }
}

class AudioPage extends StatefulWidget {
  const AudioPage({super.key});

  @override
  State<AudioPage> createState() => _AudioPageState();
}

class _AudioPageState extends State<AudioPage> {
  bool _isInitialized = false;
  bool _routeInitialized = false;
  int currentIndex = 0;
  Map<String, dynamic>? currentPodcast;
  Map<String, dynamic>? currentEpisode;
  PodcastAppState? _podcastState;
  int _lastPersistedMs = -1;
  StreamSubscription<Duration>? _positionSub;
  StreamSubscription<PlaybackState>? _playbackSub;
  StreamSubscription<MediaItem?>? _mediaItemSub;

  int _readPositionMs(dynamic value) {
    if (value is int) return value;
    if (value is num) return value.toInt();
    if (value is String) return int.tryParse(value) ?? 0;
    return 0;
  }

  DateTime? _parseEpisodeDate(dynamic raw) {
    final value = (raw ?? '').toString().trim();
    if (value.isEmpty) return null;
    final direct = DateTime.tryParse(value);
    if (direct != null) return direct;
    final formats = [
      DateFormat("EEE, dd MMM yyyy HH:mm:ss 'GMT'", 'en_US'),
      DateFormat("EEE, dd MMM yyyy HH:mm:ss Z", 'en_US'),
      DateFormat('yyyy-MM-dd HH:mm:ss', 'en_US'),
    ];
    for (final format in formats) {
      try { return format.parse(value, true).toLocal(); } catch (_) {}
    }
    return null;
  }

  void _sortEpisodesList(List<Map<String, dynamic>> episodes, String sortPref) {
    if (sortPref == 'titleAsc') {
      episodes.sort((a, b) => (a['title'] ?? '').toString().toLowerCase()
          .compareTo((b['title'] ?? '').toString().toLowerCase()));
      return;
    }
    final cache = <Map<String, dynamic>, DateTime>{};
    DateTime cachedDate(Map<String, dynamic> ep) {
      return cache.putIfAbsent(ep,
          () => _parseEpisodeDate(ep['pubDate']) ?? DateTime.fromMillisecondsSinceEpoch(0));
    }
    if (sortPref == 'oldest') {
      episodes.sort((a, b) => cachedDate(a).compareTo(cachedDate(b)));
    } else {
      episodes.sort((a, b) => cachedDate(b).compareTo(cachedDate(a)));
    }
  }

  String _selectedAudioUrl() {
    // Only return audio URL if route is initialized
    if (!_routeInitialized) return '';
    return (currentEpisode?['audioUrl'] ?? '').toString();
  }

  bool _isSelectedEpisodeActive(MediaItem? mediaItem) {
    final selectedAudioUrl = _selectedAudioUrl();
    if (selectedAudioUrl.isEmpty) return true;
    return mediaItem?.id == selectedAudioUrl;
  }

  MediaItem? _selectedRouteMediaItem() {
    final podcast = currentPodcast;
    final episode = currentEpisode;
    if (podcast == null || episode == null) return null;
    final audioUrl = (episode['audioUrl'] ?? '').toString();
    if (audioUrl.isEmpty) return null;
    
    // Look up the full episode data from podcast episodes list to ensure
    // we have all fields including durationMs
    final episodes = podcast['episodes'] as List<dynamic>?;
    Map<String, dynamic> episodeToUse = episode;
    if (episodes != null && episodes.isNotEmpty) {
      final selectedGuid = episode['guid']?.toString();
      try {
        final fullEpisode = episodes.firstWhere(
          (ep) {
            if (ep is! Map) return false;
            final map = Map<String, dynamic>.from(ep);
            final guid = map['guid']?.toString();
            final url = map['audioUrl']?.toString();
            
            if (selectedGuid != null && selectedGuid.isNotEmpty && guid == selectedGuid) {
              return true;
            }
            if (audioUrl.isNotEmpty && url == audioUrl) {
              return true;
            }
            return false;
          },
        );
        if (fullEpisode is Map) {
          episodeToUse = Map<String, dynamic>.from(fullEpisode);
        }
      } catch (e) {
        // firstWhere throws if not found, use original episode
      }
    }
    
    return _buildMediaItem(episodeToUse, podcast);
  }

  MediaItem? _displayMediaItemFor(MediaItem? activeMediaItem) {
    // If route isn't initialized yet, just use active media item
    if (!_routeInitialized) {
      return activeMediaItem;
    }
    
    if (_isSelectedEpisodeActive(activeMediaItem)) {
      return activeMediaItem ?? _selectedRouteMediaItem();
    }
    return _selectedRouteMediaItem() ?? activeMediaItem;
  }

  Duration _uiPositionFor(
    MediaItem? mediaItem,
    Duration livePosition,
    PlaybackState? playbackState,
  ) {
    if (!_isSelectedEpisodeActive(mediaItem)) {
      final fallbackItem = _selectedRouteMediaItem();
      final savedMs = _readPositionMs(currentEpisode?['lastPositionMs']);
      if (savedMs <= 0) return Duration.zero;
      final duration = fallbackItem?.duration;
      if (duration != null && duration > Duration.zero) {
        final cappedMs = savedMs > duration.inMilliseconds
            ? duration.inMilliseconds
            : savedMs;
        return Duration(milliseconds: cappedMs);
      }
      return Duration(milliseconds: savedMs);
    }

    final playbackPosition = playbackState?.updatePosition ?? Duration.zero;
    final resolvedLive = livePosition > Duration.zero
        ? livePosition
        : playbackPosition;
    if (resolvedLive > Duration.zero) {
      return resolvedLive;
    }

    final savedMs = _readPositionMs(
      mediaItem?.extras?['lastPositionMs'] ?? currentEpisode?['lastPositionMs'],
    );
    if (savedMs <= 0) return Duration.zero;

    final duration = mediaItem?.duration;
    if (duration != null && duration > Duration.zero) {
      final cappedMs = savedMs > duration.inMilliseconds
          ? duration.inMilliseconds
          : savedMs;
      return Duration(milliseconds: cappedMs);
    }

    return Duration(milliseconds: savedMs);
  }

  Future<void> _persistCurrentPosition(Duration position, {bool force = false}) async {
    final activeItem = await _audioHandler.mediaItem.first;
    final audioUrl = activeItem?.id ?? '';
    if (audioUrl.isEmpty) return;
    if (!mounted) return;

    final ms = position.inMilliseconds < 0 ? 0 : position.inMilliseconds;
    if (!force && _lastPersistedMs >= 0 && (ms - _lastPersistedMs).abs() < 3000) {
      return;
    }

    final podcastState = Provider.of<PodcastAppState>(context, listen: false);
    await podcastState.savePlaybackProgressByAudioUrl(
      audioUrl,
      ms,
      durationMs: activeItem?.duration?.inMilliseconds,
      feedUrl: activeItem?.extras?['feedUrl']?.toString(),
    );
    _lastPersistedMs = ms;
  }

  Future<void> _handlePausePressed() async {
    final position = await AudioService.position.first;
    await _persistCurrentPosition(position, force: true);
    final activeItem = await _audioHandler.mediaItem.first;
    if (activeItem != null) {
      final podcastState = Provider.of<PodcastAppState>(context, listen: false);
      await podcastState.rememberLastPlayedEpisode(
        activeItem,
        position.inMilliseconds,
      );
    }
    await _audioHandler.pause();
  }

  Future<void> _handleStopPressed() async {
    final position = await AudioService.position.first;
    await _persistCurrentPosition(position, force: true);
    await _audioHandler.stop();
  }

  Future<void> _handleSkipPressed({required bool next}) async {
    final position = await AudioService.position.first;
    await _persistCurrentPosition(position, force: true);
    if (next) {
      await _audioHandler.skipToNextEpisode();
    } else {
      await _audioHandler.skipToPreviousEpisode();
    }
  }

  Future<void> _handlePlayPressed() async {
    if (currentPodcast == null) {
      await _audioHandler.play();
      return;
    }

    final episodes = currentPodcast!['episodes'] as List<dynamic>;
    if (currentIndex < 0 || currentIndex >= episodes.length) {
      await _audioHandler.play();
      return;
    }

    final selectedEpisode = Map<String, dynamic>.from(episodes[currentIndex] as Map);
    final selectedUrl = (selectedEpisode['audioUrl'] ?? '').toString();
    final activeItem = await _audioHandler.mediaItem.first;

    if (selectedUrl.isNotEmpty && activeItem?.id != selectedUrl) {
      await _playEpisodeAtIndex(currentIndex, currentPodcast!);
      return;
    }

    await _audioHandler.play();
  }

  MediaItem _buildMediaItem(
    Map<String, dynamic> episode,
    Map<String, dynamic> podcast,
  ) {
    final localImagePath = episode['localImagePath'];
    final networkUrl = episode['imageUrl'];
    final artUri = (localImagePath != null && File(localImagePath).existsSync())
        ? Uri.file(localImagePath)
        : Uri.parse(networkUrl ?? 'https://via.placeholder.com/150');

    Duration? mediaDuration;
    final rawDurationMs = episode['durationMs'];
    if (rawDurationMs is int) {
      mediaDuration = Duration(milliseconds: rawDurationMs);
    } else if (rawDurationMs is String) {
      final parsed = int.tryParse(rawDurationMs);
      if (parsed != null) {
        mediaDuration = Duration(milliseconds: parsed);
      }
    }

    return MediaItem(
      id: episode['audioUrl'] ?? '',
      album: (episode['podcastTitle'] ?? podcast['title'] ?? 'Podcast').toString(),
      title: episode['title'] ?? 'Untitled',
      artist: episode['author'] ?? podcast['author'] ?? podcast['title'] ?? 'Unknown',
      artUri: artUri,
      duration: mediaDuration,
      extras: {
        'lastPositionMs': episode['lastPositionMs'] ?? 0,
        'played': episode['played'] ?? false,
        'feedUrl': podcast['feedUrl'] ?? '',
        'podcastTitle': episode['podcastTitle'] ?? podcast['title'] ?? 'Podcast',
        'localAudioPath': episode['localAudioPath'] ?? '',
        'autoCachedAudio': episode['autoCachedAudio'] ?? false,
      },
    );
  }

  Future<void> _playEpisodeAtIndex(
    int index,
    Map<String, dynamic> podcast,
  ) async {
    if (index < 0 || index >= (podcast['episodes'] as List).length) return;
    final episode = podcast['episodes'][index];
    final podcastState = _podcastState;
    if (podcastState == null) return;

    // Start image download for this episode
    podcastState.downloadEpisodeImage(episode);

    final mediaItem = _buildMediaItem(episode, podcast);

    final savedPositionMs = () {
      final raw = episode['lastPositionMs'];
      if (raw is int) return raw;
      if (raw is String) return int.tryParse(raw) ?? 0;
      if (raw is num) return raw.toInt();
      return 0;
    }();

    await _audioHandler.playEpisode(
      mediaItem,
      initialPosition: savedPositionMs > 0
          ? Duration(milliseconds: savedPositionMs)
          : null,
    );
  }

  @override
  void initState() {
    super.initState();
  }

  @override
  void didChangeDependencies() {
    super.didChangeDependencies();
    _podcastState ??= Provider.of<PodcastAppState>(context, listen: false);
    if (_routeInitialized) return;
    _routeInitialized = true;
    _initializeFromRoute();
  }

  Future<void> _initializeFromRoute() async {
    final args = ModalRoute.of(context)?.settings.arguments as Map<String, dynamic>?;
    final shouldPlay = args?['play'] == true;
    if (args != null) {
      currentPodcast = args['podcast'] as Map<String, dynamic>?;
      currentEpisode = args['episode'] as Map<String, dynamic>?;
      final rawQueueEpisodes = args['queueEpisodes'] as List<dynamic>?;

      if (currentPodcast != null && rawQueueEpisodes != null && rawQueueEpisodes.isNotEmpty) {
        final queueEpisodes = rawQueueEpisodes
            .whereType<Map>()
            .map((ep) => Map<String, dynamic>.from(ep))
            .toList(growable: false);
        currentPodcast = {
          ...currentPodcast!,
          'episodes': queueEpisodes,
        };
      } else if (currentPodcast != null) {
        // No explicit queueEpisodes provided (e.g. opened from media overlay).
        // Sort the podcast episodes according to the stored sort preference
        // so auto-advance goes in the correct direction.
        final feedUrl = (currentPodcast!['feedUrl'] ?? '').toString();
        final podcastState = _podcastState;
        if (feedUrl.isNotEmpty && podcastState != null) {
          final sortPref = podcastState.episodeSortForPodcast(feedUrl);
          final rawEpisodes = (currentPodcast!['episodes'] as List<dynamic>? ?? const [])
              .whereType<Map>()
              .map((ep) => Map<String, dynamic>.from(ep))
              .toList();
          _sortEpisodesList(rawEpisodes, sortPref);
          currentPodcast = {
            ...currentPodcast!,
            'episodes': rawEpisodes,
          };
        }
      }

      if (currentPodcast != null && currentEpisode != null) {
        final episodes = currentPodcast!['episodes'] as List<dynamic>;
        final selectedGuid = currentEpisode!['guid']?.toString();
        final selectedAudioUrl = currentEpisode!['audioUrl']?.toString();

        currentIndex = episodes.indexWhere((ep) {
          if (ep is! Map) return false;
          final map = Map<String, dynamic>.from(ep);
          final guid = map['guid']?.toString();
          final audioUrl = map['audioUrl']?.toString();

          if (selectedGuid != null && selectedGuid.isNotEmpty && guid == selectedGuid) {
            return true;
          }
          if (selectedAudioUrl != null &&
              selectedAudioUrl.isNotEmpty &&
              audioUrl == selectedAudioUrl) {
            return true;
          }
          return false;
        });

        if (currentIndex < 0) currentIndex = 0;
        final mediaItems = episodes
            .whereType<Map>()
            .map((ep) => _buildMediaItem(Map<String, dynamic>.from(ep), currentPodcast!))
            .where((item) => item.id.isNotEmpty)
            .toList();

        await _audioHandler.setEpisodeQueue(
          mediaItems,
          initialIndex: currentIndex,
        );
        if (shouldPlay && mounted) {
          await _playEpisodeAtIndex(currentIndex, currentPodcast!);
        }
      }
    }

    _playbackSub = _audioHandler.playbackState.listen((state) async {
      // Only save when the player is in a stable paused/ready state.
      // Skipping loading/buffering/idle prevents saving position 0 when
      // the player transitions between episodes during auto-advance.
      if (!state.playing &&
          state.processingState == AudioProcessingState.ready) {
        await _persistCurrentPosition(state.updatePosition, force: true);
      }
    });

    _positionSub = AudioService.position.listen((position) {
      _persistCurrentPosition(position);
    });

    // Track auto-advance: when the handler moves to a new episode, update
    // currentEpisode so the UI (image, title) reflects the new track.
    _mediaItemSub = _audioHandler.mediaItem.listen((item) {
      if (item == null || !mounted) return;
      final currentUrl = currentEpisode?['audioUrl']?.toString() ?? '';
      if (item.id.isNotEmpty && item.id != currentUrl) {
        _updateCurrentEpisodeFromMediaItem(item);
      }
    });
  }

  void _updateCurrentEpisodeFromMediaItem(MediaItem item) {
    if (!mounted) return;
    // Find the matching episode in the current podcast episode list
    final episodes = currentPodcast?['episodes'] as List<dynamic>?;
    if (episodes != null) {
      final idx = episodes.indexWhere((ep) {
        if (ep is! Map) return false;
        return (Map<String, dynamic>.from(ep)['audioUrl']?.toString() ?? '') == item.id;
      });
      if (idx >= 0) {
        setState(() {
          currentIndex = idx;
          currentEpisode = Map<String, dynamic>.from(episodes[idx] as Map);
        });
        return;
      }
    }
    // Fallback: build a minimal episode map from the MediaItem fields
    setState(() {
      currentEpisode = {
        'audioUrl': item.id,
        'title': item.title,
        'imageUrl': item.artUri?.toString(),
        'podcastTitle': item.album,
        'author': item.artist,
        'feedUrl': item.extras?['feedUrl'] ?? '',
        'lastPositionMs': item.extras?['lastPositionMs'] ?? 0,
        'played': item.extras?['played'] ?? false,
      };
    });
  }

  @override
  void dispose() {
    _positionSub?.cancel();
    _playbackSub?.cancel();
    _mediaItemSub?.cancel();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) {
    final args = ModalRoute.of(context)?.settings.arguments as Map<String, dynamic>?;
    final podcast = args != null ? args['podcast'] as Map<String, dynamic>? : null;
    final episode = args != null ? args['episode'] as Map<String, dynamic>? : null;
    final isOffline = context.select<PodcastAppState, bool>((s) => s.isOffline);

    final localImagePath = currentEpisode?['localImagePath'] as String?;
    final networkUrl = currentEpisode?['imageUrl'] as String?;

    return Scaffold(
      appBar: AppBar(title: const Text('')),
      body: Center(
        child: Column(
          mainAxisAlignment: MainAxisAlignment.center,
          children: [
            // Show image (network first, local when ready)
            if (localImagePath != null && File(localImagePath).existsSync())
              Image.file(
                File(localImagePath),
                width: 300,
                height: 300,
                fit: BoxFit.cover,
              )
            else if (!isOffline && networkUrl != null)
              Image.network(
                networkUrl,
                width: 150,
                height: 150,
                fit: BoxFit.cover,
              )
            else
              Container(
                width: 150,
                height: 150,
                color: Colors.grey.shade300,
                alignment: Alignment.center,
                child: Icon(
                  isOffline ? Icons.cloud_off : Icons.image_not_supported,
                  size: 34,
                ),
              ),

            // Title
            StreamBuilder<MediaState>(
              stream: _mediaStateStream,
              builder: (context, snapshot) {
                final mediaItem = snapshot.data?.mediaItem;
                return Text(mediaItem?.title ?? episode?['title'] ?? '');
              },
            ),

            // Controls
            StreamBuilder<bool>(
              stream: _audioHandler.playbackState
                  .map((s) => s.playing)
                  .distinct(),
              builder: (context, snapshot) {
                final playing = snapshot.data ?? false;
                return Row(
                  mainAxisAlignment: MainAxisAlignment.center,
                  children: [
                    _button(Icons.skip_previous, () => _handleSkipPressed(next: false)),
                    _button(Icons.fast_rewind, _audioHandler.rewind),
                    if (playing)
                      _button(Icons.pause, _handlePausePressed)
                    else
                      _button(Icons.play_arrow, _handlePlayPressed),
                    _button(Icons.stop, _handleStopPressed),
                    _button(Icons.fast_forward, _audioHandler.fastForward),
                    _button(Icons.skip_next, () => _handleSkipPressed(next: true)),
                  ],
                );
              },
            ),

            // Seek bar
            StreamBuilder<MediaState>(
              stream: _mediaStateStream,
              builder: (context, snapshot) {
                final mediaState = snapshot.data;
                return SeekBar(
                  duration: mediaState?.mediaItem?.duration ?? Duration.zero,
                  position: mediaState?.position ?? Duration.zero,
                  onChangeEnd: (newPosition) {
                    _audioHandler.seek(newPosition);
                  },
                );
              },
            ),

            // State
            StreamBuilder<PlaybackState>(
              stream: _audioHandler.playbackState,
              builder: (context, snapshot) {
                final state = snapshot.data;
                final processingState =
                    state?.processingState ?? AudioProcessingState.idle;
                final isPlaying = state?.playing ?? false;

                String status;
                if (processingState == AudioProcessingState.loading ||
                    processingState == AudioProcessingState.buffering) {
                  status = 'loading';
                } else if (isPlaying) {
                  status = 'playing';
                } else {
                  status = 'paused';
                }

                return Text('$status');
              },
            ),
          ],
        ),
      ),
    );
  }

  Stream<MediaState> get _mediaStateStream =>
      Rx.combineLatest3<MediaItem?, Duration, PlaybackState, MediaState>(
        _audioHandler.mediaItem,
        AudioService.position,
        _audioHandler.playbackState,
        (activeMediaItem, position, playbackState) => MediaState(
          _displayMediaItemFor(activeMediaItem),
          _uiPositionFor(activeMediaItem, position, playbackState),
        ),
      );

  IconButton _button(IconData iconData, VoidCallback onPressed) =>
      IconButton(icon: Icon(iconData), iconSize: 44.0, onPressed: onPressed);
}

class SeekBar extends StatefulWidget {
  final Duration duration;
  final Duration position;
  final ValueChanged<Duration>? onChanged;
  final ValueChanged<Duration>? onChangeEnd;

  const SeekBar({
    Key? key,
    required this.duration,
    required this.position,
    this.onChanged,
    this.onChangeEnd,
  }) : super(key: key);

  @override
  State<SeekBar> createState() => _SeekBarState();
}

class _SeekBarState extends State<SeekBar> {
  double? _dragValue;

  String _formatDuration(Duration duration) {
    final hours = duration.inHours;
    final minutes = duration.inMinutes.remainder(60);
    final seconds = duration.inSeconds.remainder(60);
    return '${hours.toString().padLeft(2, '0')}:${minutes.toString().padLeft(2, '0')}:${seconds.toString().padLeft(2, '0')}';
  }

  @override
  Widget build(BuildContext context) {
    final hasDuration = widget.duration.inMilliseconds > 0;
    final maxMs = hasDuration ? widget.duration.inMilliseconds.toDouble() : 1.0;
    final positionMs = hasDuration
        ? widget.position.inMilliseconds.toDouble().clamp(0.0, maxMs)
        : 0.0;
    final sliderValue = (_dragValue ?? positionMs).clamp(0.0, maxMs);
    final displayedPosition = Duration(milliseconds: sliderValue.round());

    return Column(
      mainAxisSize: MainAxisSize.min,
      children: [
        Padding(
          padding: const EdgeInsets.symmetric(horizontal: 12),
          child: Row(
            mainAxisAlignment: MainAxisAlignment.spaceBetween,
            children: [
              Text(
                _formatDuration(displayedPosition),
                style: const TextStyle(fontSize: 12),
              ),
              Text(
                _formatDuration(widget.duration),
                style: const TextStyle(fontSize: 12),
              ),
            ],
          ),
        ),
        Slider(
          min: 0.0,
          max: maxMs,
          value: sliderValue,
          onChanged: hasDuration
              ? (value) {
                  setState(() => _dragValue = value);
                  if (widget.onChanged != null) {
                    widget.onChanged!(Duration(milliseconds: value.round()));
                  }
                }
              : null,
          onChangeEnd: hasDuration
              ? (value) {
                  if (widget.onChangeEnd != null) {
                    widget.onChangeEnd!(Duration(milliseconds: value.round()));
                  }
                  setState(() => _dragValue = null);
                }
              : null,
        ),
      ],
    );
  }
}


/*import 'dart:convert';

import 'package:english_words/english_words.dart';
import 'package:flutter/material.dart';
import 'package:provider/provider.dart';
import 'package:http/http.dart' as http;
import 'package:xml_map_converter/src/types.dart';
import 'package:xml_map_converter/xml_map_converter.dart';


void main() {
  runApp(MyApp());
}

class MyApp extends StatelessWidget {
  const MyApp({super.key});

  @override
  Widget build(BuildContext context) {
    return ChangeNotifierProvider(
      create: (context) => MyAppState(),
      child: MaterialApp(
        title: 'Namer App',
        theme: ThemeData(
          colorScheme: ColorScheme.fromSeed(seedColor: const Color.fromRGBO(0, 255, 0, 1.0)),
        ),
        home: MyHomePage(),
      ),
    );
  }
}

class MyAppState extends ChangeNotifier {
  var current = WordPair.random();
  void getNext() {
    current = WordPair.random();
    notifyListeners();
  }

  var favorites = <WordPair>[];

  void toggleFavorite() {
    if (favorites.contains(current)) {
      favorites.remove(current);
    } else {
      favorites.add(current);
    }
    notifyListeners();
  }
}

// ...

class MyHomePage extends StatefulWidget {
  @override
  State<MyHomePage> createState() => _MyHomePageState();
}

class _MyHomePageState extends State<MyHomePage> {

  var selectedIndex = 0;

  @override
  Widget build(BuildContext context) {
    Widget page;
    switch (selectedIndex) {
      case 0:
        page = GeneratorPage();
        break;
      case 1:
        page = FavoritesPage();
        break;
      default:
        throw UnimplementedError('no widget for $selectedIndex');
    }
    final isWide = MediaQuery.of(context).size.width >= 600;
    return Scaffold(
      body: Row(
        children: [
          SafeArea(
            child: NavigationRail(
              extended: isWide,
              destinations: [
                NavigationRailDestination(
                  icon: Icon(Icons.home),
                  label: Text('Home'),
                ),
                NavigationRailDestination(
                  icon: Icon(Icons.favorite),
                  label: Text('Favorites'),
                ),
              ],
              selectedIndex: selectedIndex,
              onDestinationSelected: (value) {
                setState(() {
                  selectedIndex = value;
                });
              },
            ),
          ),
          Expanded(
            child: Container(
              color: Theme.of(context).colorScheme.primaryContainer,
              child: page,
            ),
          ),
        ],
      ),
    );
  }
}

class GeneratorPage extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    var appState = context.watch<MyAppState>();
    var pair = appState.current;

    IconData icon;
    if (appState.favorites.contains(pair)) {
      icon = Icons.favorite;
    } else {
      icon = Icons.favorite_border;
    }

    return Center(
      child: Column(
        mainAxisAlignment: MainAxisAlignment.center,
        children: [
          BigCard(pair: pair),
          SizedBox(height: 10),
          Row(
            mainAxisSize: MainAxisSize.min,
            children: [
              ElevatedButton.icon(
                onPressed: () {
                  appState.toggleFavorite();
                },
                icon: Icon(icon),
                label: Text('Like'),
              ),
              SizedBox(width: 10),
              ElevatedButton(
                onPressed: () {
                  appState.getNext();
                },
                child: Text('Next'),
              ),
            ],
          ),
        ],
      ),
    );
  }
}

Future<DataMap?> fetchPodcast() async {
  final response = await http.get(
      Uri.parse('https://feeds.feedburner.com/TellEmSteveDave')
    );
  if (response.statusCode == 200) {
    final converter1 = Xml2Map(response.body);
    final data = await converter1.transform();
    return data;

  }
  else {
    return null;
  }
}

// ...

class FavoritesPage extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    return FutureBuilder<DataMap?>(
      future: fetchPodcast(),
      builder: (context, snapshot) {
        if (snapshot.connectionState == ConnectionState.waiting) {
          return Center(child: CircularProgressIndicator()); // loading state
        } else if (snapshot.hasError) {
          return Center(child: Text('Error: ${snapshot.error}'));
        } else if (!snapshot.hasData || snapshot.data == null) {
          return Center(child: Text('No podcast found.'));
        }

        final rss = snapshot.data!;
        final List<dynamic> episodes = rss['rss']!['channel']!['item'];
        final List<String> episodeTitles =
            episodes.map((e) => e['title'] as String).toList();

        return ListView(
          children: [
            Padding(
              padding: const EdgeInsets.all(20),
              child: Text('You have ${episodeTitles.length} episodes:'),
            ),
            for (var title in episodeTitles)
              ListTile(
                leading: Icon(Icons.favorite),
                title: Text(title),
              ),
          ],
        );
      },
    );
  }
}

// ...
class BigCard extends StatelessWidget {
  const BigCard({
    super.key,
    required this.pair,
  });

  final WordPair pair;

  @override
  Widget build(BuildContext context) {
    final theme = Theme.of(context); 
    final style = theme.textTheme.displayMedium!.copyWith(
      color: theme.colorScheme.onPrimary,
    );
    return Card(
      color: theme.colorScheme.primary,
      child: Padding(
        padding: const EdgeInsets.all(25.0),
        child: Text(
          pair.asLowerCase, 
          style: style,
          semanticsLabel: "${pair.first} ${pair.second}",
          ),
      ),
    );
  }
}
*/

