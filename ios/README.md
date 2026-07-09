# ios — the Playground app

The **single** iOS app for this repo. Like the GitHub Pages site hosts many
browser apps, this one **TestFlight app ("Playground")** hosts many
**experiments** internally. There is exactly one iOS app, one bundle identifier
(`io.github.imjasonh.playground`), and one App Store Connect record; you add
functionality by adding *experiments inside this app*, never by creating another
iOS app.

On every push to `main`, CI builds this app, runs its tests, and (once the Apple
signing secrets are set) uploads a new build to **TestFlight**.

## How it's structured

```
ios/
├── project.yml                    # XcodeGen spec (source of truth + discovery marker)
├── Gemfile                        # pins fastlane
├── fastlane/                      # Fastfile (test / beta / signing_bootstrap), Appfile, Matchfile
├── Sources/
│   ├── PlaygroundApp.swift        # @main app shell
│   ├── RootView.swift             # the launcher: lists every experiment
│   ├── Experiment.swift           # Experiment model + ExperimentCatalog registry
│   └── Experiments/               # one folder per experiment
│       ├── TemperatureConverter/
│       └── Counter/
└── Tests/
    ├── PlaygroundTests/           # XCTest unit tests (logic + catalog)
    └── PlaygroundUITests/         # XCUITest launcher/experiment flows
```

## Adding an experiment

1. Create `Sources/Experiments/<YourExperiment>/` with a SwiftUI view (keep the
   testable logic in plain types, add accessibility identifiers to controls).
2. Register it in `ExperimentCatalog.all` in `Sources/Experiment.swift` with a
   stable, unique `id`.
3. Add tests under `Tests/PlaygroundTests/` (and a UI flow if useful).

That's it — no project or CI changes, and no new TestFlight app. The launcher
picks it up automatically and the next push to `main` ships it in the same
Playground build.

## Local development (macOS + Xcode)

```bash
brew install xcodegen
bundle install
xcodegen generate
open Playground.xcodeproj        # optional

# tests (what CI runs)
bundle exec fastlane test
# or:
xcodebuild test -project Playground.xcodeproj -scheme Playground \
  -destination 'platform=iOS Simulator,name=iPhone 16,OS=latest'
```

The generated `Playground.xcodeproj` is git-ignored; regenerate it with
XcodeGen.

## Shipping to TestFlight

CI runs `fastlane beta` automatically on push to `main` once the signing secrets
exist. See [`docs/ios-testflight-setup.md`](../docs/ios-testflight-setup.md) for
the click-by-click Apple/TestFlight setup and
[`docs/ios-testflight-design.md`](../docs/ios-testflight-design.md) for the
design.
