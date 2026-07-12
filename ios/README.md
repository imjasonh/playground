# ios — the Playground app

> **Agents:** read [`AGENTS.md`](AGENTS.md) — in-app experiments share one Bundle
> ID (no re-bootstrap); Apple app extensions (e.g. Custom Keyboard) need a
> second Bundle ID once.

The **single** iOS **host** app for this repo. Like the GitHub Pages site hosts
many browser apps, this one TestFlight app ("Playground") hosts many
**experiments** internally under Bundle ID `io.github.imjasonh.playground`.

On every push to `main`, CI builds, tests, and (with signing secrets) uploads to
**TestFlight**.

## Signing policy

| What you’re adding | Bundle ID | Re-run signing bootstrap? |
|--------------------|-----------|---------------------------|
| In-app experiment (Ride Monitor–style) | Host only | **No** |
| Info.plist privacy / background modes | Host only | **No** |
| Custom Keyboard / other **app extension** | Host + **extension id** (Apple requires it) | **Yes, once** for that extension |

Bootstrap is **not** per experiment. It is once for the host app, and once more
when you add a new extension Bundle ID (today: T9 keyboard).

## How it's structured

```
ios/
├── AGENTS.md
├── project.yml
├── fastlane/
├── Shared/T9/                 # multi-tap engine (app + keyboard extension)
├── T9Keyboard/                # system Custom Keyboard appex
├── Sources/Experiments/       # in-app experiments
└── Tests/
```

## Experiments

| Id | Title | Notes |
|----|-------|-------|
| `ride-monitor` | Ride Monitor | In-app; background motion + GPS |
| `t9-keyboard` | T9 Keyboard | In-app demo **and** system keyboard extension |
| `follow-the-hum` | Follow the Hum | In-app; AirPods spatial hum hunt |
| `snore-log` | Snore Log | In-app; mic buffer + snore clip logging |

### T9 Keyboard

Old Nokia-style **multi-tap**. Same engine powers:

1. **In-app demo** (Simulator-friendly) under the T9 Keyboard experiment.
2. **System keyboard** `T9 Multi-tap` — Bundle ID
   `io.github.imjasonh.playground.t9keyboard` (required by Apple for a Custom
   Keyboard). Enable: Settings → General → Keyboard → Keyboards → Add New
   Keyboard… → T9 Multi-tap.

After cloning a tree that adds/changes that extension, run **iOS signing
bootstrap** once so match has its App Store profile. Later in-app experiments
do not need that.

### Follow the Hum

Outdoor sound-hunt with AirPods head tracking. Needs a real device; see
experiment UI for details.

### Snore Log

Overnight snore logger. Keeps a short rolling microphone buffer in memory and
writes a clip only when loudness rises above an adaptive ambient floor. Needs
microphone permission and the `audio` background mode (Info.plist only — no new
Bundle ID or signing bootstrap). Best on a real device near the bed.

## Adding an experiment

1. `Sources/Experiments/<YourExperiment>/`
2. `*Experiment.swift` → `static let experiment: Experiment`
3. Append to `ExperimentCatalog.all`
4. Tests under `Tests/PlaygroundTests/`

No new Bundle ID. No bootstrap. See [`AGENTS.md`](AGENTS.md).

## Local development

```bash
brew install xcodegen && bundle install
xcodegen generate
bundle exec fastlane test
```

## Shipping to TestFlight

[`docs/ios-testflight-setup.md`](../docs/ios-testflight-setup.md) ·
[`docs/ios-testflight-design.md`](../docs/ios-testflight-design.md)
