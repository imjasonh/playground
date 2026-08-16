# onramp — Onramp

Offline Mac **network** triage for when you can’t get online. Playbooks chain
path/DNS/proxy/VPN/hosts checks, probe connectivity, and rank likely causes —
no Apple Intelligence required. Chat (optional) uses on-device Foundation Models
with the same read-only tools. Once you’re browsing again, search engines beat
local tools for everything else.

Design: [`docs/onramp-design.md`](../docs/onramp-design.md)

Bundle ID: `io.github.imjasonh.onramp`

## Layout

```
onramp/
├── AGENTS.md            # agent rules (read-only tools)
├── project.yml
├── Onramp.entitlements
├── Sources/
│   ├── Diagnostics/     # services, parsers, connectivity playbooks
│   ├── Triage/          # Foundation Models tools + chat model
│   ├── UI/              # Playbooks + Toolbox + Chat
│   └── Assets.xcassets  # App icon
├── Tests/OnrampTests/
├── fastlane/
└── README.md
```

Agent rules (especially **tools must never take action**): [`AGENTS.md`](AGENTS.md).

## Local development

Requires macOS + Xcode. Chat needs **macOS 26+** with **Apple Intelligence**
enabled; **Playbooks** and **Toolbox** work without it.

```bash
cd onramp
brew install xcodegen
bundle install
xcodegen generate
open Onramp.xcodeproj
# or:
bundle exec fastlane test
```

## What 0.2.x includes

- **Install-while-online setup:** hard gate for unsupported OS; aggressive model download; first-run baseline playbook so you’re ready before trouble
- **Can’t get online golden path:** auto-runs on open; ranked cause; **Fix & recheck** buttons (Settings / captive / read-only probes) with confirm sheets; output feeds another diagnosis until online
- **Toolbox:** network checks up front; advanced once-online checks demoted
- **Chat:** on-device model required; network scenario chips
- Menu bar: Can’t get online when allowed
- Sparkle **Check for Updates…**

## CI / releases

`.github/workflows/macos.yml` discovers this app (`platform: macOS`), tests on
PRs, and on `main` notarizes + publishes:

```text
https://imjasonh.github.io/playground/macos/onramp/appcast.xml
```
