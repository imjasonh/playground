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
├── examples/            # MDM sample profile + playbook plist/JSON
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
- **Can’t get online golden path:** auto-runs on open; ranked diagnosis; **Fix & recheck** buttons (Settings / captive / read-only probes) with confirm sheets; output feeds another diagnosis until online
- **Custom playbooks:** device admins can add playbooks via MDM (preference domain `io.github.imjasonh.onramp`) or a drop-in plist/JSON — same read-only probes, optional corp hosts
- **Toolbox:** network checks up front; advanced once-online checks demoted
- **Chat:** on-device model required; network scenario chips
- Menu bar: Can’t get online when allowed
- Sparkle **Check for Updates…**

## Custom playbooks (MDM)

Onramp ships five built-in playbooks. Admins can **add** more (and optionally hide built-ins) without shipping a custom build. Custom playbooks only override allowlisted probe targets (DNS name, HTTP URL, TCP host/port) and extra **display-only** next steps. They cannot run shell or change Settings.

### Preference domain

`io.github.imjasonh.onramp`

| Key | Type | Purpose |
|-----|------|---------|
| `Playbooks` | Array of dictionaries | Custom playbook definitions |
| `PlaybooksJSON` | String | Same list as JSON (for MDM tools that only ship strings) |
| `DisabledPlaybookIDs` | Array of strings | Hide built-in or custom ids (`cantGetOnline`, `vpnBroken`, `dnsWrong`, `captivePortal`, `someSitesFail`, …) |

Push this with an MDM **Custom Settings** / preference-domain payload (Jamf, Kandji, Mosyle, Apple Configurator). A sample profile is [`examples/onramp-playbooks.mobileconfig`](examples/onramp-playbooks.mobileconfig); the raw preference plist is [`examples/playbooks.plist`](examples/playbooks.plist).

Without MDM, drop the same plist or JSON at:

- `/Library/Application Support/Onramp/playbooks.plist` (or `.json`) — all users
- `~/Library/Application Support/Onramp/playbooks.plist` (or `.json`) — this user

Managed preferences win when the same `id` appears in more than one source. Built-in ids cannot be replaced (disable them instead). `cantGetOnline` stays available even if every built-in is listed in `DisabledPlaybookIDs`.

### Playbook dictionary

| Field | Required | Notes |
|-------|----------|-------|
| `id` | yes | `[A-Za-z0-9._-]`, max 64; must not collide with a built-in id |
| `title` | yes | Shown in the list |
| `subtitle` | no | One-line description |
| `symbol` | no | SF Symbol name (e.g. `building.columns`) |
| `focus` | no | Ranking lens: `online` (default), `vpn`, `dns`, `captive`, `sites` |
| `dnsHostname` | no | Replaces `example.com` for DNS lookup / trace |
| `httpURL` | no | `http`/`https` only; no `file:`, no userinfo |
| `reachHost` / `reachPort` | no | TCP probe target (default `1.1.1.1:443`) |
| `extraSteps` | no | Up to 8 strings shown when the playbook is **not** healthy; never executed |

Invalid entries are skipped. Restart Onramp (or switch away and back to Playbooks) after changing profiles.

## CI / releases

`.github/workflows/macos.yml` discovers this app (`platform: macOS`), tests on
PRs, and on `main` notarizes + publishes:

```text
https://imjasonh.github.io/playground/macos/onramp/appcast.xml
```
