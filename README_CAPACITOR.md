# Capacitor iOS Setup

The `ui/` directory is configured with [Capacitor](https://capacitorjs.com/) to build an iOS app from the existing Vite/React web app.

## Prerequisites

- [Xcode](https://apps.apple.com/app/xcode/id497799835) (Mac App Store)
- [Apple Developer account](https://developer.apple.com/) ($99/year, required to publish or install on device beyond 7 days)

## Commands

All commands run from the `ui/` directory:

```bash
cd ui

# Build the web app and sync to the iOS project
npm run build && npx cap sync ios

# Open in Xcode
npx cap open ios
```

In Xcode, select a simulator or connected device and press the Play button to run.

## Development Workflow

1. Make changes to the web app in `ui/src/`
2. Rebuild and sync: `npm run build && npx cap sync ios`
3. Run again from Xcode

## Configuration

- **App ID:** `com.lemmascript.equality-game`
- **App Name:** Equality Game
- **Config file:** `ui/capacitor.config.ts`

To change the app name, bundle ID, or icons, edit `capacitor.config.ts` and the Xcode project settings.
