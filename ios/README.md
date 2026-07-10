# ios — the Playground app

The **single** iOS app for this repo. Like the GitHub Pages site hosts many
browser apps, this one **TestFlight app ("Playground")** hosts many
**experiments** internally. There is exactly one iOS app, one Bundle ID
(`io.github.imjasonh.playground`), and one App Store Connect / TestFlight
record. You add functionality by adding *experiments inside this app*, never by
creating another top-level iOS app or another Bundle ID.

On every push to `main`, CI builds this app, runs its tests, and (once the Apple
signing secrets are set) uploads a new build to **TestFlight**.

## Signing policy (important)

- **One App ID, one match profile, bootstrap once.** Adding an experiment never
  requires re-running signing bootstrap or regenerating certificates.
- Prefer **in-app experiments** (SwiftUI under `Sources/Experiments/`). They
  ship in the next TestFlight build with zero Apple-portal work.
- **Avoid app extensions** (Custom Keyboard, Watch, widgets, App Clip, …)
  unless you deliberately accept Apple’s rule that each extension needs its
  **own** Bundle ID + provisioning profile. That is the only case that forces
  a match bootstrap again.

## How it's structured

```
ios/
├── project.yml                    # XcodeGen spec (source of truth + discovery marker)
├── Gemfile                        # pins fastlane
├── fastlane/                      # Fastfile (test / beta / signing_bootstrap), Appfile, Matchfile
├── Shared/T9/                     # multi-tap engine shared by the T9 experiment
├── Sources/
│   ├── PlaygroundApp.swift        # @main app shell
│   ├── RootView.swift             # the launcher: lists every experiment
│   ├── Experiment.swift           # Experiment model + ExperimentCatalog registry
│   └── Experiments/               # one folder per experiment
│       ├── RideMonitor/
│       ├── T9Keyboard/            # in-app multi-tap pad (not a system keyboard)
│       └── FollowTheHum/
└── Tests/
    ├── PlaygroundTests/           # XCTest unit tests (logic + catalog)
    └── PlaygroundUITests/         # XCUITest launcher/experiment flows
```

## Experiments

| Id | Title | Notes |
|----|-------|-------|
| `ride-monitor` | Ride Monitor | Background motion + GPS ride recorder |
| `t9-keyboard` | T9 Keyboard | In-app Nokia-style multi-tap pad (same Bundle ID) |
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

Old Nokia-style **multi-tap**, entirely in-app: tap `2` once for `a`, twice for
`b`, thrice for `c`, four times for `2`. Wait ~1s (or tap another key) to
commit. `*` cycles `abc` → `Abc` → `ABC` → `123`; `#` inserts a space;
long-press a key for its digit. Works in Simulator. There is **no** system
Custom Keyboard extension (that would need a second Bundle ID).

## Adding an experiment

1. Create `Sources/Experiments/<YourExperiment>/` — **one directory per
   experiment**. Put the SwiftUI view and any logic there (keep testable logic
   in plain types; add accessibility identifiers to controls).
2. In that folder, add a `*Experiment.swift` that exposes a static
   `experiment: Experiment` (id, title, summary, icon, destination view).
3. Append that static to `ExperimentCatalog.all` in `Sources/Experiment.swift`.
4. Add tests under `Tests/PlaygroundTests/` (and a UI flow if useful).

That's it — **no project signing changes, no new Bundle ID, no bootstrap**. The
launcher picks it up and the next push to `main` ships it in the same Playground
TestFlight build.

Optional Info.plist keys (privacy usage strings, `UIBackgroundModes`) are fine
and still do not require re-signing.

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
