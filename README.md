# Ulticast Podcast App

A Flutter-based podcast player for Android with persistent playback, smart episode selection, and background audio support.

## Features

- **Subscribe to Podcasts**: Add RSS feeds and manage your podcast library
- **Episode Playback**: Stream or play downloaded episodes with full audio controls
- **Session Persistence**: Your last-played episode is saved and restored automatically when you reopen the app
- **Smart Episode Selection**: Play button intelligently picks in-progress episodes, then next unplayed, then the first episode
- **Background Audio**: Continue listening with the app in the background or on the lock screen
- **Episode Filtering & Sorting**: Filter by status (all/in-progress/played/unplayed) and sort by date or title
- **Download Caching**: Episodes are cached locally for offline playback
- **Dark Mode**: Toggle between light and dark themes
- **Interruption Handling**: Respects system interruptions (calls, other audio apps) and resumes intelligently

### TODO

- fix logo

## Building & Installation

### Requirements
- Flutter 3.9.0+
- Android SDK 21+ (for app deployment)
- Connected Android device or emulator

### Build Release APK
```bash
flutter build apk --release
```

### Install on Device
```bash
adb install build/app/outputs/flutter-apk/app-release.apk
```

### Build Debug APK
```bash
flutter build apk --debug
adb install build/app/outputs/flutter-apk/app-debug.apk
```

## Tech Stack

- **Framework**: Flutter 3.9.0
- **State Management**: Provider
- **Audio**: audio_service + just_audio
- **Storage**: SharedPreferences + file-based JSON
- **Networking**: http for RSS parsing

## Development

```bash
flutter pub get
flutter run
```

## License

MIT
