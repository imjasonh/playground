# geeksquad — Geek Squad

Offline Mac network & config triage. Manual Toolbox for DNS, routing, proxy/VPN,
reachability, and related checks; proposes fixes without applying them. Shipped
via the same Developer ID + Sparkle CD as [`hello-macos/`](../hello-macos/).

Design: [`docs/geeksquad-design.md`](../docs/geeksquad-design.md)

Bundle ID: `io.github.imjasonh.geeksquad`

## Layout

```
geeksquad/
├── project.yml
├── GeekSquad.entitlements
├── Sources/
│   ├── Diagnostics/     # services + parsers (unit-tested)
│   └── UI/              # Manual Toolbox
├── Tests/GeekSquadTests/
├── fastlane/            # test + beta
├── Gemfile
└── README.md
```

## Local development

Requires macOS + Xcode.

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

- Manual Toolbox: interfaces, default route, path status, DNS config/lookup,
  reachability, HTTP probe, proxy config, VPN interfaces, hosts file, current Wi‑Fi
- Proposed fixes shown as text only (never auto-applied)
- Sparkle **Check for Updates…** (shared playground EdDSA key)

Guided on-device Foundation Models triage is Phase 2 (see design doc).

## CI / releases

`.github/workflows/macos.yml` discovers this app (`platform: macOS`), tests on
PRs, and on `main` notarizes + publishes:

```text
https://imjasonh.github.io/playground/macos/geeksquad/appcast.xml
```
