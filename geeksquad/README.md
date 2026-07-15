# geeksquad — Geek Squad

Offline Mac triage for **network/config**, **performance** (CPU/memory/disk/load),
login agents, storage hotspots, and common functionality gaps (ports, crashes).
**Chat** shows live tool results you can expand/copy; **Toolbox** runs the same
checks manually. Proposes fixes — never applies them or kills processes.
Shipped via Developer ID + Sparkle CD (same path as [`hello-macos/`](../hello-macos/)).

Design: [`docs/geeksquad-design.md`](../docs/geeksquad-design.md)

Bundle ID: `io.github.imjasonh.geeksquad`

## Layout

```
geeksquad/
├── project.yml
├── GeekSquad.entitlements
├── Sources/
│   ├── Diagnostics/     # services + parsers (unit-tested)
│   ├── Triage/          # Foundation Models tools + chat model
│   ├── UI/              # Chat + Manual Toolbox
│   └── Assets.xcassets  # App icon
├── Tests/GeekSquadTests/
├── fastlane/
└── README.md
```

## Local development

Requires macOS + Xcode. Chat needs **macOS 26+** with **Apple Intelligence**
enabled; Toolbox works without it.

```bash
cd geeksquad
brew install xcodegen
bundle install
xcodegen generate
open GeekSquad.xcodeproj
# or:
bundle exec fastlane test
```

## What 0.1.0 includes

- **Chat (primary):** describe symptoms → on-device model runs diagnostic tools →
  proposes steps you apply yourself
- **Toolbox:** same diagnostics as buttons (works without Apple Intelligence)
- Sparkle **Check for Updates…**
- 🤓 app icon

## CI / releases

`.github/workflows/macos.yml` discovers this app (`platform: macOS`), tests on
PRs, and on `main` notarizes + publishes:

```text
https://imjasonh.github.io/playground/macos/geeksquad/appcast.xml
```
