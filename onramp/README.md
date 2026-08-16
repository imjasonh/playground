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

- **Foundation Models gate:** hard block on unsupported OS / ineligible Mac; fullscreen setup that pushes Apple Intelligence enable + model download (Chat needs it)
- **Playbooks (primary offline path):** Can’t get online (+ VPN / DNS / captive / some-sites) — works while the model downloads if you choose Playbooks-only
- **Toolbox:** network checks up front; advanced once-online checks demoted
- **Chat:** on-device model required; scenario chips for network triage
- Menu bar: one-click Can’t get online (after setup, or Playbooks-only)
- Sparkle **Check for Updates…**

## CI / releases

`.github/workflows/macos.yml` discovers this app (`platform: macOS`), tests on
PRs, and on `main` notarizes + publishes:

```text
https://imjasonh.github.io/playground/macos/onramp/appcast.xml
```
