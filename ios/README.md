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
| `wigglecam` | Wigglecam | In-app; dual-wide wigglegrams saved as GIF to Photos |
| `local-lens` | Local Lens | In-app; live on-device Vision (classify / OCR / face landmarks / body & hand pose / barcodes) |
| `container-lab` | Container Lab | In-app; pulls an OCI image to disk and probes whether WebKit can host a wasm runtime |

### Ride Monitor

In-app jolt/crash detector with GPS track logging. Core Motion only runs while
the process is awake, so recording **requires Always location** plus background
location updates to keep the app alive with the screen off. Older builds could
start under When-In-Use, which suspended the process on lock and produced
multi-minute sensing holes; the app now refuses to start without Always, holds
a background activity session on iOS 17+, and auto-ends if sensing is silent
for ~90s. Each saved ride stores a `recordingDiagnostics` block (end reason,
motion-restart / location-error counts, slowest companion push) and emits
`OSLog` under subsystem `io.github.imjasonh.playground` / category
`RideMonitor` (per-minute heartbeats + stop reasons) for Console.app debugging.
Leaving the Ride Monitor experiment while a ride is active stops and saves it
so `@StateObject` teardown cannot silently drop the recording or leave Live
Activity / Watch workouts orphaned (Past rides opens in a sheet so browsing
history mid-ride does not trigger that stop). While a ride is active it also:

1. **Live Activity** (`io.github.imjasonh.playground.ridemonitorwidget`) —
   Lock Screen / Dynamic Island shows duration, distance, average and max
   speed, and a rough elevation sparkline colored by speed. When the ride
   stops, the Live Activity freezes on that summary for about **30 minutes**
   and then auto-dismisses (force-quit leftovers are still cleared immediately
   when the app is idle).
2. **Apple Watch companion** (`io.github.imjasonh.playground.watch`) — glanceable
   clock time, duration, distance, current speed, heart rate, energy, and (when
   a Bluetooth sensor is paired) cadence/power via WatchConnectivity (phone
   remains the GPS/jolt recorder). Opening Ride Monitor on iPhone (and the
   Watch companion) prompts for Health access up front. Starting a ride
   launches the Watch app into an `HKWorkoutSession` so it stays frontmost —
   HealthKit is required for that long-running Watch execution (any workout
   type works; we use cycling to match the app). watchOS returns to the clock
   face when that session is not active, and also after the Digital Crown
   dismisses the app even with a live session; while the phone ride is active
   the Watch keeps (or retries) an `HKWorkoutSession`, and the phone re-calls
   `startWatchApp` every ~45s to bring the UI forward again. The session
   collects heart rate, active/basal energy, Watch cycling distance, and
   cadence/speed/power when available, mirrors them to the phone for the saved
   ride, and finishes a cycling workout into Health on stop.

Both need a one-time **iOS signing bootstrap** after this tree lands (new Bundle
IDs, and again when HealthKit is first enabled on the host + Watch App IDs).
Live Activities require a real device (and Live Activities enabled in
Settings); the Watch app needs a paired Apple Watch.

When a ride ends, Ride Monitor asks the on-device Foundation Model (Apple
Intelligence / `FoundationModels`, iOS 26+) for a **few-word summary** and
stores it on the ride for the Past rides list. If the model is unavailable or
fails, the summary stays empty — there is no heuristic substitute.

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

### Wigglecam

Dual-wide **wigglegram** camera: streams rear **ultra-wide + wide** together
(`AVCaptureMultiCamSession`), requires a **landscape and relatively level** hold,
and freezes a synchronized pair on shutter. Capture uses the DualWide virtual
device with **shared center metering** and **locks AE/AWB/AF** at shutter (Apple
drives the two eyes in tandem on that virtual device; DualWide can’t take custom
ISO/WB gains). After FOV match (plus a content scale refine), both eyes are
**brightness-matched** in software — clip-aware midtone + per-channel balance,
then a residual shadow/mid/highlight luma curve — so blown skies and mild ISP
curve differences don’t dominate the wiggle. Live capture is full-bleed with a
floating thumb shutter on the landscape trailing edge; after capture you only
see the wigglegram with tiny Retake / Save buttons. **Tap Save** writes a looping
GIF to **Photos**; **long-press Save** writes left and right **JPEGs** instead
(`NSPhotoLibraryAddUsageDescription` — no new Bundle ID or signing
bootstrap). Strongest depth around **1–2.5 m**. Simulator opens the UI but cannot
capture pairs.

### Local Lens

Live camera that runs **Apple Vision entirely on-device** — no network, no
bundled Core ML file, no cloud API. Modes:

1. **Classify** — scene / object labels (`VNClassifyImageRequest`)
2. **Text** — live OCR (`VNRecognizeTextRequest`)
3. **Animals** — cats and dogs (`VNRecognizeAnimalsRequest`)
4. **Faces** — face contour, eyes, and pupils (`VNDetectFaceLandmarksRequest`;
   2D image landmarks — not TrueDepth gaze / ARKit `lookAtPoint`)
5. **People** — human body rectangles
6. **Body** — full-body joint skeleton (`VNDetectHumanBodyPoseRequest`)
7. **Hands** — 21-point hand skeletons (`VNDetectHumanHandPoseRequest`)
8. **Codes** — QR / barcodes (`VNDetectBarcodesRequest`)

Full-bleed live preview with compact floating controls (mode icons + flip
camera); landscape keeps a thin trailing rail so the bottom panel never eats
half the frame. Detections with bounding boxes draw green overlays plus a
label chip. Camera buffers stay sensor-native; preview and Vision share one
`CGImagePropertyOrientation` (rear portrait → `.right`) so OCR reads forward
in portrait and landscape through aspect-fill. Needs camera permission
(extends the existing `NSCameraUsageDescription` — no new Bundle ID or signing
bootstrap). Simulator opens the UI but has no camera; use a physical device to
see live labels. True gaze / attention tracking would need ARKit face tracking
on a TrueDepth front camera — not wired here yet.

### Container Lab

Name a container image, pull it to an on-device **OCI image layout**, and check
whether this device can host the wasm runtime that would eventually run it. See
[`docs/ios-containers-design.md`](../docs/ios-containers-design.md) for why the
runtime has to live in a `WKWebView` at all.

What works today:

- **Registry client in Swift** — reference parsing (`alpine`, `alpine:3.20`,
  `ghcr.io/owner/name@sha256:…`), anonymous Bearer token auth, manifest lists
  resolved to one platform (`linux/arm64` by default), and blob pulls where
  every blob is checked against its digest before it is kept.
- **Native decompression** — gzip layers are inflated on the phone, not in the
  guest, because container2wasm's in-browser gunzip is documented as slow. The
  rewritten manifest is self-checking: an uncompressed layer's digest *is* the
  `diff_id` the image config already published, so a mismatch aborts the pull.
- **Loopback origin** — an in-app HTTP server on `127.0.0.1` serves the layout
  and the runtime page with `Cross-Origin-Opener-Policy: same-origin` and
  `Cross-Origin-Embedder-Policy: require-corp`. This is the only way to get a
  cross-origin-isolated page in `WKWebView`: a custom `WKURLSchemeHandler`
  scheme is not a secure context, and the service-worker COOP/COEP shims that
  work in Safari are ignored here.
- **Isolation probe** — “Check webview isolation” loads that origin in a
  `WKWebView` and reports `crossOriginIsolated`, `SharedArrayBuffer`, and
  whether a shared `WebAssembly.Memory` can be constructed. Those are the
  prerequisites for wasm threads, and therefore for any CPU emulator. The same
  check runs in CI on the simulator (`ContainerLabIsolationProbeTests`).

What does not work yet: **running** the image. That needs a bundled
container2wasm/QEMU-wasm runtime, which has to be built with Docker +
Emscripten and is not yet in the repo — the Runtime section says so plainly
rather than pretending. `RuntimeAssets` looks for a bundled `ContainerRuntime/`
directory and the loopback server already serves it at `/runtime/…`, with the
image layout alongside at `/image/…`.

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
