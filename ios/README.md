# ios — the Playground app

The **single** iOS app for this repo. Like the GitHub Pages site hosts many
browser apps, this one **TestFlight app ("Playground")** hosts many
**experiments** internally. There is exactly one iOS app, one App Store Connect
record (`io.github.imjasonh.playground`), and optionally embedded app
extensions (today: a Custom Keyboard). You add functionality by adding
*experiments inside this app*, never by creating another top-level iOS app.

On every push to `main`, CI builds this app, runs its tests, and (once the Apple
signing secrets are set) uploads a new build to **TestFlight**.

## How it's structured

```
ios/
├── project.yml                    # XcodeGen spec (source of truth + discovery marker)
├── Gemfile                        # pins fastlane
├── fastlane/                      # Fastfile (test / beta / signing_bootstrap), Appfile, Matchfile
├── Shared/T9/                     # multi-tap engine + pad UI (app + keyboard extension)
├── T9Keyboard/                    # Custom Keyboard extension (+ README / screenshots)
├── Sources/
│   ├── PlaygroundApp.swift        # @main app shell
│   ├── RootView.swift             # the launcher: lists every experiment
│   ├── Experiment.swift           # Experiment model + ExperimentCatalog registry
│   └── Experiments/               # one folder per experiment
│       ├── RideMonitor/
│       └── T9Keyboard/            # in-app demo + enable instructions
└── Tests/
    ├── PlaygroundTests/           # XCTest unit tests (logic + catalog)
    └── PlaygroundUITests/         # XCUITest launcher/experiment flows
```

## Experiments

| Id | Title | Notes |
|----|-------|-------|
| `ride-monitor` | Ride Monitor | Background motion + GPS ride recorder |
| `t9-keyboard` | T9 Keyboard | In-app multi-tap pad + system Custom Keyboard extension |
| `follow-the-hum` | Follow the Hum | Hide a nearby walkable spot; steer with a spatial AirPods hum |

### Follow the Hum

Outdoor sound-hunt: the app hides a walkable spot ~120–320 m away and plays a
soft stereo hum in your headphones. **AirPods Pro/Max head tracking** keeps the
hum fixed in the world as you turn your head (phone compass locks north once at
start, then the phone can go in a pocket). Turn until the hum sits in front of
you, then walk — it brightens and clears as you get closer. Arrive within ~22 m
to win. Needs a real device with location + compass; head tracking needs
compatible AirPods.

### T9 Keyboard

Old Nokia-style **multi-tap**: tap `2` once for `a`, twice for `b`, thrice for `c`,
four times for `2`. Wait ~1s (or tap another key) to commit. `*` cycles
`abc` → `Abc` → `ABC` → `123`; `#` inserts a space; long-press a key for its
digit. The same engine powers:

1. The **in-app demo** under the T9 Keyboard experiment (works in Simulator).
2. The **system keyboard** `T9 Multi-tap` (`io.github.imjasonh.playground.t9keyboard`).

Enable the system keyboard on a device: **Settings → General → Keyboard →
Keyboards → Add New Keyboard… → T9 Multi-tap**, then switch to it with the
globe key. (Third-party keyboards cannot be fully exercised in UI tests.)

The keyboard extension needs its **own App ID + App Store provisioning
profile**. Re-run the iOS signing bootstrap workflow (or `fastlane signing_bootstrap`)
after pulling this so match creates
`match AppStore io.github.imjasonh.playground.t9keyboard`.

## Adding an experiment

1. Create `Sources/Experiments/<YourExperiment>/` — **one directory per
   experiment**. Put the SwiftUI view and any logic there (keep testable logic
   in plain types; add accessibility identifiers to controls).
2. In that folder, add a `*Experiment.swift` that exposes a static
   `experiment: Experiment` (id, title, summary, icon, destination view).
3. Append that static to `ExperimentCatalog.all` in `Sources/Experiment.swift`.
4. Add tests under `Tests/PlaygroundTests/` (and a UI flow if useful).

That's it for in-app-only experiments — no project or CI changes, and no new
TestFlight app. The launcher picks it up automatically and the next push to
`main` ships it in the same Playground build.

If you add another **app extension** (keyboard, widget, …), also update
`project.yml`, register the extension App ID, and teach `fastlane` match / beta
about the extra bundle identifier (see the T9 keyboard as a template).

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
