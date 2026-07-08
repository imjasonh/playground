# Xeneon Cursor

Touch-first **Cursor cloud agent manager** for the [Corsair XENEON EDGE](https://www.corsair.com/us/en/p/monitors/cc-9011306-ww/xeneon-edge-14-5-lcd-touchscreen-cc-9011306-ww) (14.5″ / 2560×720).

A small macOS WKWebView kiosk hosts an expressive web HUD. The app talks to the [Cloud Agents API](https://cursor.com/docs/cloud-agent/api/endpoints) with your API key (Keychain), and **Open in Cursor** uses the desktop deeplink:

```text
cursor://anysphere.cursor-deeplink/background-agent?bcId=<agent-id>
```

## Install / update (macOS)

Releases are published by CI on every push to `main` that touches this app (`xeneon-cursor-v*` tags).

```bash
curl -fsSL https://raw.githubusercontent.com/imjasonh/playground/main/xeneon-cursor/scripts/install.sh | bash
open ~/Applications/XeneonCursor.app
```

Or download `XeneonCursor-macos.zip` from the latest
[GitHub Release](https://github.com/imjasonh/playground/releases?q=xeneon-cursor).

The build is **ad-hoc signed** (no Apple Developer ID yet). If macOS blocks launch:

1. Right-click the app → **Open**, or
2. Re-run the install script (it clears quarantine).

### First launch

1. Paste a Cloud Agents API key from [cursor.com/dashboard/api](https://cursor.com/dashboard/api) (or choose **Use Mock Data**).
2. Re-open later via **⌘K** to change the key.
3. Put the window on the XENEON (the app prefers a display named like Xeneon/Corsair, or an ultrawide strip) and fullscreen it.

### Touch on macOS

Corsair does not ship macOS touch/iCUE support for the EDGE. Install a community HID helper so taps become clicks:

- [Xeneon Touch Support](https://github.com/MatthiasReinholz/macos-touch-support-for-xeneon-edge)
- or [TouchscreenDriver](https://github.com/ymlaine/TouchscreenDriver)

Grant **Accessibility** + **Input Monitoring**, then keep this HUD fullscreen on the EDGE.

## What the HUD does

- List cloud agents (poll every 15s)
- Launch a new agent (prompt, repo, model)
- Follow-up / cancel / archive
- **Open in Cursor** (desktop deeplink) or open web / PR
- **Next needing me** cycles IDLE / FINISHED / ERROR agents

## Develop without the .app

Browser + local proxy (mock data, no API key):

```bash
cd xeneon-cursor
npm test
npm run dev          # http://127.0.0.1:8787
```

Live API through the Node proxy:

```bash
cp .env.example .env  # set CURSOR_API_KEY
npm start
```

### macOS app (on a Mac)

```bash
cd xeneon-cursor
bash scripts/package-macos.sh
open dist/XeneonCursor.app
```

Dev run via SwiftPM (loads `ui/` from the repo tree):

```bash
cd xeneon-cursor/macos
swift run XeneonCursor
```

## CI

Workflow: [`.github/workflows/xeneon-cursor.yml`](../.github/workflows/xeneon-cursor.yml)

| Event | What happens |
|-------|----------------|
| PR / push touching `xeneon-cursor/` | `npm test` on Ubuntu |
| Same, on `macos-14` | Build `XeneonCursor.app`, zip, upload artifact |
| Push to `main` | Also create/update GitHub Release `xeneon-cursor-v<VERSION>` with the zip |

Bump [`VERSION`](./VERSION) when you want a new release tag version.

## Layout

```text
xeneon-cursor/
├── ui/                 # Web HUD (2560×720-first)
├── server/             # Node proxy for browser/dev
├── macos/              # Swift WKWebView shell
├── scripts/            # package-macos.sh, install.sh
└── tests/              # Node unit tests
```

This directory is **not** a GitHub Pages browser app (no root `index.html`); it is a native macOS product with its own workflow.
