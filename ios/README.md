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
when you add a new extension Bundle ID (today: T9 keyboard, Ride Monitor
widget, Ride Monitor Watch).

## How it's structured

```
ios/
├── AGENTS.md
├── project.yml
├── fastlane/
├── Shared/T9/                 # multi-tap engine (app + keyboard extension)
├── Shared/RideMonitor/        # live snapshot + Live Activity attributes
├── T9Keyboard/                # system Custom Keyboard appex
├── RideMonitorWidget/         # Ride Monitor Live Activity (WidgetKit)
├── RideMonitorWatch/          # Ride Monitor watchOS companion
├── Sources/Experiments/       # in-app experiments
└── Tests/
```

## Experiments

| Id | Title | Notes |
|----|-------|-------|
| `ride-monitor` | Ride Monitor | In-app; background motion + GPS; Live Activity + Watch companion |
| `t9-keyboard` | T9 Keyboard | In-app demo **and** system keyboard extension |
| `follow-the-hum` | Follow the Hum | In-app; AirPods spatial hum hunt |
| `snore-log` | Snore Log | In-app; mic buffer + snore clip logging |
| `z-camera` | Z-Camera | In-app; depth-band live camera (near/far sliders) |
| `voxel-world` | Voxel World | In-app; ARKit rebuilds the room as Minecraft-style palette blocks |

### Ride Monitor

In-app jolt/crash detector with GPS track logging. Recording requires **Always**
location so Core Motion keeps sampling with the screen off; without it iOS
suspends the process and the ride grows a multi-minute sensing hole (the app
auto-ends a ride if sensing is silent for ~90s). While a ride is active it
also:

1. **Live Activity** (`io.github.imjasonh.playground.ridemonitorwidget`) —
   Lock Screen / Dynamic Island shows duration, distance, current speed, and a
   rough elevation sparkline colored by speed.
2. **Apple Watch companion** (`io.github.imjasonh.playground.watch`) — glanceable
   clock time, duration, distance, and current speed via WatchConnectivity
   (phone remains the recorder).

Both need a one-time **iOS signing bootstrap** after this tree lands (new Bundle
IDs). Live Activities require a real device (and Live Activities enabled in
Settings); the Watch app needs a paired Apple Watch.

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

### Z-Camera

Live depth-band camera. Two sliders set a near/far interval (each from `0` to
`∞`); pixels outside that slice go black. An optional depth-overlay checkbox
adds a smooth blue gradient (lighter near, darker far). Capture prefers the
highest practical depth resolution (up to about 720p) with bilinear depth
sampling and calibration-aware alignment when the device provides it. Depth is
measured from the camera, not fixed in the room. Needs camera permission
(`NSCameraUsageDescription` only — no new Bundle ID or signing bootstrap) and
a depth-capable device (TrueDepth, dual camera, or LiDAR). Simulator opens the
UI but cannot stream depth.

### Voxel World

ARKit world tracking rebuilds the space around you as Minecraft-style blocks.
Every few frames the LiDAR depth map (or, without LiDAR, ARKit's sparse
tracked feature points) is unprojected into world space and quantized onto a
world-aligned voxel grid. Each voxel keeps a capped running average of the
camera pixels that saw it, and at mesh time that color snaps to a fixed
Minecraft-style block palette — stylization, not fidelity, is the goal. The
world is kept live two ways: re-observing a voxel refines its color, and a
carve pass removes any voxel the camera can now see *through* (observed
surface well behind it, several consecutive misses required), so moved objects
and depth-noise floaters clean themselves up instead of leaving trails
(LiDAR only). A log-scale slider dials the block edge from 10 cm to 50 cm —
deliberately chunky, since the 256×192 depth map can't support crisp small
voxels — and changing it clears and rescans. Freeze stops scanning so you can
walk around what you built, Camera feed toggles the live passthrough, and
Reset clears everything. Rendering is chunked SceneKit geometry with hidden
interior faces culled and per-face shading baked into vertex colors. Needs
camera permission (the existing `NSCameraUsageDescription` — no new Bundle ID,
entitlement, or signing bootstrap) and works best on LiDAR devices
(iPhone/iPad Pro). Simulator opens the UI but ARKit tracking is unavailable
there.

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
