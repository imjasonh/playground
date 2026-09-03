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
| New App ID capability (HealthKit, NFC, …) | Host, plus extensions when they need it | **Yes** for a profile refresh |
| Custom Keyboard / other **app extension** | Host + **extension id** (Apple requires it) | **Yes, once** for that extension |

Bootstrap is **not** per experiment. It is once for the host app, once more
when you add a new extension Bundle ID (today: T9 keyboard, Ride Monitor
widget, Ride Monitor Watch), and again when you add an App ID capability such
as NFC Tag Reading.

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
| `device-agent` | Device Agent | On-device model drives an in-app browser; App Intents/Shortcuts; voice; requires Apple Intelligence |
| `army-list` | Army List | Build/validate 11th Edition army lists (Votann catalog first); export `.army.json` + text |
| `t9-keyboard` | T9 Keyboard | In-app demo **and** system keyboard extension |
| `follow-the-hum` | Follow the Hum | In-app; AirPods spatial hum hunt |
| `snore-log` | Snore Log | In-app; mic buffer + snore clip logging |
| `z-camera` | Z-Camera | In-app; depth-band live camera (near/far sliders) |
| `voxel-world` | Voxel World | In-app; ARKit rebuilds the room as Minecraft-style palette blocks |
| `wigglecam` | Wigglecam | In-app; dual-wide wigglegrams saved as GIF to Photos |
| `local-lens` | Local Lens | In-app; live on-device Vision (classify / OCR / face landmarks / body & hand pose / barcodes) |
| `doom-face` | Doom Face | Front camera + TrueDepth; stamp your face onto doomguy's sheet and export a GIF |
| `nfc-tags` | NFC Tags | In-app Core NFC tag read/write (NDEF text/URL, blank NTAGs); needs NFC Tag Reading capability bootstrap |

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

Past rides can be exported as JSON Lines (`.jsonl`): open a ride for a single
export, or use **Export all** on the Past rides list to **Save ZIP…** (one
archive of per-ride `.jsonl` files), save/share one combined JSONL, or share
through the system share sheet.

### Army List

Build and validate Warhammer 40,000 **11th Edition** army lists. v1 ships a
Leagues of Votann construction catalog (points, Detachment Points, unique tags,
Leader join edges) bundled as JSON, a deterministic validator, SwiftUI
authoring UI, and share/export as plain text or `.army.json`.

Refresh catalog data from BSData’s Munitorum Field Manual scrape:

```bash
python3 ios/scripts/refresh-army-list-catalog.py
```

Unofficial fan experiment — confirm points with the official Munitorum Field
Manual for events. On-device chat / list ideation is planned after validation
coverage is solid.

### Device Agent

On-device assistant that drives an in-app browser. The model can open http(s)
pages, snapshot interactive elements, click/type by ref or visible text, and
extract question-relevant bullets from the page. Mic/speech permissions are
requested only for optional voice input.

- Chat + tool transcript, plus a live WKWebView pane when a page is open
- Browser tools: `browserOpen`, `browserRead`, `browserSnapshot`,
  `browserFind`, `browserClick`, `browserClickText`, `browserType`,
  `browserSelect`, `browserGet`, `browserScroll`, `browserBack` (plus
  `getCurrentDateTime`). Find, click-by-text, get, and scroll return tiny
  payloads so digs do not re-dump the page into the model context.
- After each snapshot, Foundation Models guided generation extracts
  question-relevant "From the page" bullets into chat. If extraction fails,
  the tool fails with a visible error (no heuristic substitute). Diagnostics
  land in the export ZIP.
- Voice input (mic + speech, just-in-time) to editable text, then the same
  agent loop
- Export conversation: share a `.jsonl.zip` of the transcript (including
  hidden tool args/results), browser replay, and AFM extraction diagnostics
- Chat shows `Invoking <tool>…` only; raw tool I/O stays in the dump
- Context budget: tracks estimated fill of the 4096-token on-device window,
  shows a Context meter in the status bar, returns slim tool payloads to the
  model (page text stays in the export / chat findings), and compacts into a
  fresh session with page carry-over before the hard limit. Findings are bound
  to the page URL, so a navigate + compact does not reuse the previous page's
  bullets. If the framework still throws a context-window error, the run
  compacts and retries once.
- Shortcuts / App Intents / Siri:
  - **Ask Device Agent** — queue a free-form prompt
  - **Browse URL with Device Agent** — open an http(s) URL, then run an optional
    prompt so the model drives the in-app browser
  - **Summarize URL with Device Agent** — open a URL and summarize the page
  - **Find on Page with Device Agent** — open a URL and search it for a query
- Deep link: `playground://device-agent?prompt=…&url=https://…&voice=1`
  (`url` is optional; when set, Device Agent opens it before running the prompt)
- With the browser open, the composer collapses to an Ask follow-up control so
  the keyboard stays out of the way

When Apple Intelligence / Foundation Models is available (iOS 26+ device), the
on-device model chooses browser tools. If Apple Intelligence is off, the UI
offers a button that opens Settings (Apple Intelligence & Siri when the deep
link works). If the model is still downloading, it shows progress plus
**Check again**. Unsupported hardware / older OS / Simulator get a plain
unavailable pane. There is no keyword-planner fallback.

If page extraction quality is weak for a domain, a next step is Apple's
Foundation Models adapter toolkit (LoRA). Adapters ship as small packages and
must be retrained when Apple updates the base system model. Not wired up in
this experiment yet.

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

### Doom Face

Front TrueDepth camera matches blend shapes to doomguy status-bar faces. Hold a
look, grin, or open mouth for about half a second and your cropped face lands
in that cell. Unmatched cells stay grey.

Square camera on top, sprite sheet below, Reset and Export GIF. The GIF uses
the idle look cycle (left, center, right, center) when those faces exist,
otherwise every captured cell in sheet order. Extends
`NSCameraUsageDescription`. No new Bundle ID. Needs a TrueDepth iPhone;
Simulator cannot track a face.

### NFC Tags

Read and write NDEF text or URL records with Core NFC (`NFCTagReaderSession`),
including blank NTAG / Type 2 tags (UID + family, empty NDEF instead of an
error). Write stores a Text or URI record on writable tags.

Polls ISO 14443, ISO 15693, and FeliCa so chip-level discovery matches apps
like NFC Tools. That needs the NFC Tag Reading App ID capability
(`com.apple.developer.nfc.readersession.formats` = `TAG`),
`NFCReaderUsageDescription`, plus Info.plist lists for
`iso7816.select-identifiers` and `felica.systemcodes`. Without those lists,
Core NFC fails immediately with "Missing required entitlement". The App ID
capability change needs `needs-ios-bootstrap`; the Info.plist lists do not.
Simulator opens the UI but cannot scan; use a physical iPhone. The screen
shows the CFBundleVersion build number so TestFlight installs are easy to
confirm.

Today the UI covers NDEF text/URL read/write and blank-tag identity. NTAG /
Ultralight writes use raw Type 2 page commands and EEPROM read-back, then a
second NFC session after you remove and re-present the tag. Success means the
chip bytes matched, not only a same-session Core NFC soft view. Broader NFC
Tools features (lock bits, more record types) can build on the same Tag Reader
session.

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

`Gemfile.lock` is committed so local and CI resolve the same fastlane gems.
Re-run `bundle update fastlane` only when you intentionally bump.

## Shipping to TestFlight

[`docs/ios-testflight-setup.md`](../docs/ios-testflight-setup.md) ·
[`docs/ios-testflight-design.md`](../docs/ios-testflight-design.md)
