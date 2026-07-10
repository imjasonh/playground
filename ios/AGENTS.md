# Agent guide: ios (Playground)

This directory is the **one** iOS app in the repo. It is a TestFlight container
that hosts many **experiments** — the iOS analog of many browser apps under one
GitHub Pages site.

Read this before adding features. Root [`AGENTS.md`](../AGENTS.md) has repo-wide
rules; this file is the iOS-specific contract.

## Non-negotiables

| Rule | Detail |
|------|--------|
| **One app** | Only `ios/`. Never add another top-level iOS app directory. |
| **One Bundle ID** | `io.github.imjasonh.playground` — one App Store Connect record, one TestFlight app. |
| **Experiments, not apps** | New functionality = a folder under `Sources/Experiments/`, registered in `ExperimentCatalog`. |
| **No re-signing for experiments** | Adding/changing an experiment must **not** require a new App ID, a new provisioning profile, or re-running **iOS signing bootstrap**. |
| **Prefer in-app only** | Ship features as SwiftUI (or UIKit) **inside** the host app. |

Bootstrap (`ios-signing-bootstrap` / `fastlane signing_bootstrap`) is **one-time**
for this Bundle ID. After that, every merge to `main` that touches `ios/` builds,
tests, and uploads a new TestFlight build with the **same** match profile.

## Will my change need re-bootstrap?

| Change | Re-bootstrap? |
|--------|----------------|
| New experiment under `Sources/Experiments/` | **No** |
| Edit existing experiment / tests / README | **No** |
| Add Info.plist privacy string (`NSCameraUsageDescription`, …) | **No** |
| Add `UIBackgroundModes` entry (location, audio, …) | **No** |
| Bump `MARKETING_VERSION` / normal `project.yml` settings | **No** |
| App extension (Custom Keyboard, Widget, Watch, App Clip, Share, …) | **Yes** — Apple requires a **second** Bundle ID + profile |
| New App ID capability / entitlement (Push, HealthKit, NFC, App Groups, …) | **Usually yes** — App ID + profile must be updated |
| Second top-level iOS app | **Forbidden** — don’t |

If a feature seems to need an extension or entitlement, **first** ask whether an
in-app experiment can demonstrate the same idea (e.g. T9 is an in-app pad, not a
system Custom Keyboard). Only add extensions when the platform API literally
cannot run in-process.

## Adding an experiment (happy path)

1. Create `Sources/Experiments/<YourExperiment>/` (one directory per experiment).
2. Put UI + logic there. Keep testable logic in plain types (no SwiftUI / sensors
   in unit-tested cores when possible). Add accessibility identifiers for UI tests.
3. Add `*Experiment.swift` exposing `static let experiment: Experiment` with a
   stable unique `id`, title, summary, SF Symbol `icon`, and destination view.
4. Append that static to `ExperimentCatalog.all` in `Sources/Experiment.swift`.
5. Add unit tests under `Tests/PlaygroundTests/` (and a UI smoke test under
   `Tests/PlaygroundUITests/` if useful).

No `project.yml` target changes. No Matchfile / Fastfile changes. No Apple
Developer Portal clicks. Next push to `main` ships it in the same Playground
build.

### Optional Info.plist keys

Privacy usage descriptions and background modes live in `project.yml` →
`Playground` target `info.properties`. Examples already in use: motion, location,
`UIBackgroundModes: [location]`. These are **not** App ID capabilities and do
**not** require re-signing.

## What not to do

- Do **not** add a new XcodeGen `app-extension` / Watch / widget target “just to
  try the API” — that is what blocked TestFlight after the T9 keyboard extension
  (second Bundle ID, missing match profile).
- Do **not** register a new Bundle ID per experiment.
- Do **not** commit `*.xcodeproj`, `Playground-Info.plist`, `node_modules`,
  signing material (`*.p8`, `*.p12`, `*.mobileprovision`), or `DerivedData/`.
- Do **not** stack PRs; branch off `main`.

## Layout

```
ios/
├── AGENTS.md                 ← you are here
├── README.md                 ← human-oriented runbook
├── project.yml               # XcodeGen source of truth + CI discovery marker
├── fastlane/                 # test / beta / signing_bootstrap (single App ID)
├── Shared/                   # optional shared pure logic (e.g. Shared/T9)
├── Sources/
│   ├── PlaygroundApp.swift
│   ├── RootView.swift        # launcher
│   ├── Experiment.swift      # Experiment + ExperimentCatalog
│   └── Experiments/<Name>/   # one folder per experiment
└── Tests/
    ├── PlaygroundTests/
    └── PlaygroundUITests/
```

## Local / CI

```bash
cd ios
brew install xcodegen && bundle install
xcodegen generate
bundle exec fastlane test
```

CI: `.github/workflows/ios.yml` — on PRs, test only; on `main` with secrets,
`fastlane beta` → TestFlight. Discovery marker: `project.yml`.

Apple setup (once): [`docs/ios-testflight-setup.md`](../docs/ios-testflight-setup.md).
Design: [`docs/ios-testflight-design.md`](../docs/ios-testflight-design.md).
