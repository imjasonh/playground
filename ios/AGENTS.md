# Agent guide: ios (Playground)

This directory is the **one** iOS app in the repo. It is a TestFlight container
that hosts many **experiments** — the iOS analog of many browser apps under one
GitHub Pages site.

Read this before adding features. Root [`AGENTS.md`](../AGENTS.md) has repo-wide
rules; this file is the iOS-specific contract.

## Mental model

| Layer | Bundle ID | Re-bootstrap when adding? |
|-------|-----------|---------------------------|
| **Host app** (launcher + all experiments) | `io.github.imjasonh.playground` | **No** — bootstrap once for the app |
| **In-app experiment** (Ride Monitor, Follow the Hum, in-app T9 demo, …) | *same as host* | **No** |
| **Apple app extension** (Custom Keyboard, Widget, Watch, App Clip, …) | **separate** id (Apple rule) | **Yes, once** for that extension id |

So: Ride Monitor–style experiments stay on the host Bundle ID forever. A
**system Custom Keyboard** (and any other app extension) **does** need a second
Bundle ID — that is unavoidable on Apple’s platform. Do that rarely; when you
do, re-run **iOS signing bootstrap** once so match stores the new profile.

Today’s Apple extensions (each its own Bundle ID):

| Extension | Bundle ID |
|-----------|-----------|
| **T9 Multi-tap** (Custom Keyboard) | `io.github.imjasonh.playground.t9keyboard` |
| **Ride Monitor** Live Activity (WidgetKit) | `io.github.imjasonh.playground.ridemonitorwidget` |
| **Ride Monitor** Watch companion | `io.github.imjasonh.playground.watch` |

After adding or changing any of these targets, re-run **iOS signing bootstrap** once so match stores the new App Store profiles.

## Non-negotiables

- **One host app** at `ios/` — never another top-level iOS app directory.
- **One TestFlight / App Store Connect record** for the host Bundle ID.
- **Experiments** = folders under `Sources/Experiments/`, registered in
  `ExperimentCatalog` — they share the host Bundle ID.
- **Do not** invent a new Bundle ID per experiment.
- Prefer demonstrating platform ideas **in-app** when possible; use an
  extension only when the feature *is* an extension (e.g. you want a real
  system keyboard).

## Will my change need re-bootstrap?

| Change | Re-bootstrap? |
|--------|----------------|
| New experiment under `Sources/Experiments/` (like Ride Monitor) | **No** |
| Edit experiment / tests / docs | **No** |
| Info.plist privacy string or `UIBackgroundModes` | **No** |
| Normal `project.yml` settings / version bumps | **No** |
| On-device frameworks used from the host app (e.g. Foundation Models) | **No** |
| **First time** adding/changing an **app extension** target (keyboard, widget, Watch, …) | **Yes** — new Bundle ID + match profile |
| New App ID **capability / entitlement** on an existing id (Push, HealthKit, NFC, …) | **Often yes** — update App ID + refresh profile |
| Second top-level iOS app | **Forbidden** |

`signing_bootstrap` creates missing Bundle IDs via the App Store Connect API
(then `match`). It also enables **HealthKit** on the host and Ride Monitor
Watch App IDs when missing (needed for the Watch frontmost workout session).
After the keyboard (or any new extension) is bootstrapped once,
day-to-day experiment work does not touch signing.

### PR requirement when bootstrap is needed

If a change **does** require re-running **iOS signing bootstrap** (new extension
Bundle ID, or a new App ID capability/entitlement that needs a refreshed match
profile), the pull request **must say so clearly** — in the PR title or near
the top of the PR body — so a human runs
[`ios-signing-bootstrap.yml`](../.github/workflows/ios-signing-bootstrap.yml)
before expecting TestFlight to succeed. Do not bury it in a checklist footnote.
PRs that do **not** need bootstrap should not claim they do.


## Adding an experiment (happy path — no signing)

1. Create `Sources/Experiments/<YourExperiment>/` (one directory per experiment).
2. Put UI + logic there. Keep testable logic in plain types. Add accessibility
   identifiers for UI tests.
3. Add `*Experiment.swift` with `static let experiment: Experiment` (stable
   unique `id`, title, summary, SF Symbol `icon`, destination).
4. Append it to `ExperimentCatalog.all` in `Sources/Experiment.swift`.
5. Add tests under `Tests/PlaygroundTests/` (UI smoke test optional).

No new XcodeGen targets. No Matchfile changes. No Developer Portal clicks.
Next push to `main` ships in the same Playground TestFlight build.

### Optional Info.plist keys

Privacy strings and background modes go in `project.yml` → Playground
`info.properties`. Not App ID capabilities → no re-signing.

## Adding an app extension (rare — keyboard is the example)

Apple requires a distinct Bundle ID for each extension. Checklist:

1. Add the extension target in `project.yml` (embed in Playground).
2. Choose Bundle ID under the host prefix, e.g.
   `io.github.imjasonh.playground.<extension>`.
3. List it in `fastlane/Matchfile` and `SIGNING_IDENTIFIERS` / `ensure_bundle_ids!`
   in `fastlane/Fastfile`.
4. Run **iOS signing bootstrap** once (creates Bundle ID + App Store profile in
   match).
5. Document the extension in `README.md` / this file.

Do **not** do this for ordinary experiments.

## Layout

```
ios/
├── AGENTS.md
├── README.md
├── project.yml              # host app + any extension targets
├── fastlane/                # match lists host + extension ids
├── Shared/T9/               # shared by in-app T9 demo + keyboard extension
├── Shared/RideMonitor/      # live snapshot + ActivityAttributes + sparkline view
├── T9Keyboard/              # Custom Keyboard appex (own Bundle ID)
├── RideMonitorWidget/       # Live Activity widget extension (own Bundle ID)
├── RideMonitorWatch/        # watchOS companion app (own Bundle ID)
├── Sources/
│   ├── Experiment.swift
│   └── Experiments/<Name>/  # in-app experiments (host Bundle ID)
└── Tests/
```

## Local / CI

```bash
cd ios
brew install xcodegen && bundle install
xcodegen generate
bundle exec fastlane test
```

CI: `.github/workflows/ios.yml`. Setup:
[`docs/ios-testflight-setup.md`](../docs/ios-testflight-setup.md).
