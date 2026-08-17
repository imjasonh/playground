# Agent guide: onramp

Onramp is an offline Mac **network** triage app (SwiftUI + Foundation Models +
Sparkle). Golden path:

1. **Install while online** — finish Apple Intelligence / model download + baseline check.
2. **Later, offline** — open Playbooks → Can’t get online (auto-runs), follow
   click-to-run next steps; each probe’s output feeds another diagnosis pass.

Read [`README.md`](README.md) for layout/run instructions and
[`docs/onramp-design.md`](../docs/onramp-design.md) for product design.
Repo-wide rules live in the root [`AGENTS.md`](../AGENTS.md); this file adds
rules specific to this app.

## Hard rules

- **Autonomous tools stay read-only.** Anything the on-device model can call as a
  Foundation Models `Tool`, and anything Playbooks / Toolbox / menu bar run
  through `DiagnosticServices` **without** an explicit user click, must only
  observe and report — never mutate the Mac (no killing processes, rewriting
  proxies, toggling VPN, editing hosts, privileged flush, etc.).
- **Confirmed click-to-run is allowed for the golden path.** `SuggestedAction`
  buttons may, after showing what/why and getting a click: open Settings or a
  captive URL, or run an **allowlisted read-only** probe (`SuggestedAction.DiagnosticProbe`).
  Probe output is shown and then fed into another playbook pass. Do **not** add
  mutating shell commands to that allowlist without an explicit product decision.
- **Custom / MDM playbooks stay inside that allowlist.** Admin-defined playbooks
  (`PlaybookCatalog`, preference domain `io.github.imjasonh.onramp`) may only
  override probe hosts/URLs and add display-only `extraSteps`. Do not add a
  path that runs arbitrary commands from a profile.
- **Prefer network/offline value.** Improve Can’t get online (setup → diagnose →
  act → recheck) over once-online Activity Monitor clones.

## Where tools live

| Layer | Path | Role |
|-------|------|------|
| Playbooks + actions | `Sources/Diagnostics/Connectivity*.swift`, `PlaybookDefinition.swift`, `SuggestedAction.swift` | Gather, rank, click-to-run; MDM/local catalog |
| First-run | `Sources/UI/FirstRunReadyView.swift` | Online install / baseline |
| FM tool wrappers | `Sources/Triage/DiagnosticTools.swift` | What the chat agent can call |
| Shared implementations | `Sources/Diagnostics/DiagnosticServices.swift` | Chat + Toolbox + playbooks |
| Parsers / CLI helpers | `Sources/Diagnostics/` | Pure reads + formatting |

When adding a diagnostic, wire it through `DiagnosticServices` (and tests)
first, then expose it via playbooks / suggested actions / FM tools as needed.

## Verify before you're done

```bash
cd onramp
xcodegen generate
bundle exec fastlane test
```

CI runs macOS tests via `.github/workflows/macos.yml` when `onramp/` changes.
