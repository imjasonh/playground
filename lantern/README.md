# lantern — Lantern

Menu-bar-first macOS **local network sentinel** (formerly Onramp). Continuously
watches your home LAN and this Mac for suspicious behavior and connectivity
drift — new unknown devices, gateway MAC changes, UPnP inbound port forwards,
exposed proxy/ADB/Telnet ports, Mac processes with residential-proxy-like IP
fan-out or wildcard listeners, DNS/proxy hijacks, and optional Pi-hole /
AdGuard Home DNS logs.

Built around a **Watch → Score → Explain** pipeline:
- **Deterministic Swift collectors & anomaly rules** do 100% of observation,
  per-network baselining, and alerting (works on macOS 14+ without Apple
  Intelligence).
- **Narrow on-device Foundation Models harness** (macOS 26+ with Apple
  Intelligence) runs tiny, single-shot `@Generable` jobs (<1k tokens each) for
  cached device classification and plain-English alert explanations, plus a
  scoped 3-tool **Investigate** drawer for individual findings.

Bundle ID: `io.github.imjasonh.lantern`

## Layout

```text
lantern/
├── AGENTS.md                 # agent rules (read-only collectors & tools)
├── project.yml               # XcodeGen spec (macOS 14+, weak-linked FoundationModels)
├── Lantern.entitlements
├── Sources/
│   ├── LanternApp.swift      # MenuBarExtra + on-demand Inspector Window
│   ├── SparkleUpdater.swift
│   ├── Models/               # NetworkIdentity, LANDevice, Finding, BaselineStore
│   ├── Collectors/           # ARP/mDNS, targeted port probe, UPnP IGD, lsof/nettop, connectivity, Pi-hole/AdGuard
│   ├── Engine/               # AnomalyDetector, NotificationManager, SentinelController
│   ├── Intelligence/         # Non-blocking AFM status, DeviceClassifier, FindingExplainer, ScopedInvestigator
│   └── UI/                   # MenuBarPopoverView, InspectorWindowView, FindingRowView, detail tabs
├── Tests/LanternTests/       # Parser, anomaly, baseline persistence, and AFM harness tests
├── fastlane/
└── README.md
```

## Local development

Requires macOS + Xcode. Core monitoring works on **macOS 14+**; optional
on-device AI explanations activate automatically on **macOS 26+** with Apple
Intelligence enabled.

```bash
cd lantern
brew install xcodegen
bundle install
xcodegen generate
open Lantern.xcodeproj
# or:
bundle exec fastlane test
```

## CI / releases

`.github/workflows/test.yml` discovers `lantern/` (`platform: macOS`) and runs
`fastlane test`. On `main`, `.github/workflows/macos.yml` notarizes and
publishes the Sparkle appcast:

```text
https://imjasonh.github.io/playground/macos/lantern/appcast.xml
```
