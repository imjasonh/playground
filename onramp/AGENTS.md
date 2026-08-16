# Agent guide: onramp

Onramp is an offline Mac **network** triage app (SwiftUI + Foundation Models +
Sparkle). Product focus: **can’t get online** — playbooks + toolbox. Chat is
optional sugar when Apple Intelligence is available.

Read [`README.md`](README.md) for layout/run instructions and
[`docs/onramp-design.md`](../docs/onramp-design.md) for product design.
Repo-wide rules live in the root [`AGENTS.md`](../AGENTS.md); this file adds
rules specific to this app.

## Hard rules

- **Diagnostic tools must NEVER take action — only read and diagnose.**
  Anything exposed to the on-device model as a Foundation Models `Tool`, and
  anything the Playbooks / Manual Toolbox / menu bar runs through
  `DiagnosticServices`, must be **read-only**: observe system state, return a
  report, propose what the *human* can do. Do **not** add tools (or service
  methods behind tools) that mutate the Mac — for example killing processes,
  deleting/moving files, changing System Settings / network config, clearing
  caches, toggling VPN or proxies, writing plists/hosts, or running privileged
  remediation commands. Propose-only is enforced by the tool surface, not by
  hoping the model obeys “don’t do that” prompt text.
- **New checks stay read-only end-to-end.** Parsers, `ProcessRunner` CLI
  fallbacks, playbooks, and toolbox buttons share the same constraint: gather
  evidence, never remediate. If a future feature needs confirmed apply actions,
  that is an explicit product decision (see design non-goals) — not something
  to sneak into an existing tool.
- **Prefer network/offline value.** New work should improve “can’t get online”
  (playbooks, ranking, probes, copy). Don’t grow once-online Activity Monitor
  clones unless asked.

## Where tools live

| Layer | Path | Role |
|-------|------|------|
| Playbooks | `Sources/Diagnostics/Connectivity*.swift` | Chained gather + ranked triage |
| FM tool wrappers | `Sources/Triage/DiagnosticTools.swift` | What the chat agent can call |
| Shared implementations | `Sources/Diagnostics/DiagnosticServices.swift` | Chat + Toolbox + playbooks |
| Parsers / CLI helpers | `Sources/Diagnostics/` | Pure reads + formatting |

When adding a diagnostic, wire it through `DiagnosticServices` (and tests)
first, then expose it via playbooks / toolbox / FM tools as needed.

## Verify before you're done

```bash
cd onramp
xcodegen generate
bundle exec fastlane test
```

CI runs macOS tests via `.github/workflows/macos.yml` when `onramp/` changes.
