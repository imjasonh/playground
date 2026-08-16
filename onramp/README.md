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

## What 0.2.0 includes

- **Playbooks (primary):** Can’t get online (and VPN / DNS / captive / some-sites variants) — chained checks + ranked cause card
- **Toolbox:** network checks up front; advanced once-online checks demoted
- **Chat (optional):** describe symptoms → on-device model runs diagnostic tools → proposes steps
- Menu bar: one-click Can’t get online
- Sparkle **Check for Updates…**

## CI / releases

`.github/workflows/macos.yml` discovers this app (`platform: macOS`), tests on
PRs, and on `main` notarizes + publishes:

```text
https://imjasonh.github.io/playground/macos/onramp/appcast.xml
```
