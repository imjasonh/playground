# Agent guide: lantern

Lantern is a menu-bar-first macOS **local network sentinel** (SwiftUI +
Sparkle + optional on-device Foundation Models). It replaces Onramp with a
continuous **Watch → Score → Explain** architecture.

## Hard rules

- **All collectors and AI tools stay strictly read-only.** Lantern must never
  mutate system network settings, kill processes, rewrite `/etc/hosts`, send
  ARP spoofing packets, or modify router UPnP rules.
- **Never hard-block on Apple Intelligence.** All collectors, per-network
  baselining, anomaly scoring, and deterministic explanations must work on
  macOS 14+ without Foundation Models.
- **Keep the AFM harness narrow and tiny.** Never re-introduce a 15-tool
  agentic chat loop. Single-shot `@Generable` tasks (`DeviceClassifier`,
  `FindingExplainer`) stay zero-tool and under ~1k tokens; `ScopedInvestigator`
  starts a fresh session per question with a single finding and at most 3 tiny
  read-only tools.
- **Keep parsers pure and unit-tested.** Every CLI/XML/JSON parser (`arp`,
  `route`, `lsof`, `nettop`, `scutil`, UPnP SOAP, Pi-hole/AdGuard) lives as a
  pure static function tested in `Tests/LanternTests/`.

## Verify before you're done

```bash
cd lantern
xcodegen generate
bundle exec fastlane test
```

CI runs macOS tests via `.github/workflows/test.yml` when `lantern/` changes.
