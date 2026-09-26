# ios — the Playground app

> **Agents:** read [`AGENTS.md`](AGENTS.md) — in-app experiments share one Bundle
> ID (no re-bootstrap); Apple app extensions (e.g. Custom Keyboard) need a
> second Bundle ID once.

The **single** iOS **host** app for this repo. Like the GitHub Pages site hosts
many browser apps, this one TestFlight app ("Playground") hosts many
**experiments** internally under Bundle ID `io.github.imjasonh.playground`.

On every push to `main`, CI builds, tests, and (with signing secrets) uploads to
**TestFlight**.

The host app and its iOS extensions require iOS 27. The Ride Monitor companion
requires watchOS 10. Build the app with Xcode 27.

## Signing policy

| What you’re adding | Bundle ID | Re-run signing bootstrap? |
|--------------------|-----------|---------------------------|
| In-app experiment (Ride Monitor–style) | Host only | **No** |
| Info.plist privacy / background modes | Host only | **No** |
| New App ID capability (HealthKit, App Attest, …) | Host, plus extensions when they need it | **Yes** for a profile refresh |
| Custom Keyboard / other **app extension** | Host + **extension id** (Apple requires it) | **Yes, once** for that extension |

Bootstrap is **not** per experiment. It is once for the host app, once more
when you add a new extension Bundle ID (today: T9 keyboard, Ride Monitor
widget, Ride Monitor Watch), and again when you add an App ID capability such
as App Attest or Sign in with Apple.

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
| `army-list` | Army List | Build/validate 11th Edition lists (all factions in the bundled catalog); catalog code lists legal moves and applies picks; Laya answers labeled choices and leftover yes/no; Apple Intelligence writes a theme brief, a list name, and matchup copy |
| `t9-keyboard` | T9 Keyboard | In-app demo **and** system keyboard extension |
| `follow-the-hum` | Follow the Hum | In-app; AirPods spatial hum hunt |
| `voxel-world` | Voxel Eyes | In-app; ARKit rebuilds the room as Minecraft-style palette blocks |
| `wigglecam` | Wigglecam | In-app; dual-wide wigglegrams saved as GIF to Photos |
| `local-lens` | Local Lens | In-app; live on-device Vision (classify / OCR / face landmarks / body & hand pose / barcodes) |
| `live-translate` | Live Translate | In-app; live OCR plus on-device Foundation Models translation painted over the source text; copies the translation |
| `blather` | Blather | In-app; Apple Intelligence writes spoken episodes on a topic, draws a cover, and saves the audio on this device |
| `esp32-ble` | ESP32 BLE | In-app Core Bluetooth central for `esp32-ble/` firmware; no extra Bundle ID |
| `app-attest` | App Attest | Sign in with Apple, attest once, then `generateAssertion` on each whoami; needs App Attest and Sign in with Apple capability bootstrap |
| `laya` | Laya | Swift port of the `laya-coreml` runtime; downloads the ANE bundle from Hugging Face on demand and answers choice / score / yes-no questions in one Core ML pass |

### Ride Monitor

In-app jolt/crash detector with GPS track logging. Core Motion only runs while
the process is awake, so recording **requires Always location** plus background
location updates to keep the app alive with the screen off. Older builds could
start under When-In-Use, which suspended the process on lock and produced
multi-minute sensing holes; the app now refuses to start without Always, holds
a background activity session, and auto-ends if sensing is silent
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
Intelligence / `FoundationModels`) for a **few-word summary** and
stores it on the ride for the Past rides list. If the model is unavailable or
fails, the summary stays empty — there is no heuristic substitute.

Past rides can be exported as JSON Lines (`.jsonl`): open a ride for a single
export, or use **Export all** on the Past rides list to **Save ZIP…** (one
archive of per-ride `.jsonl` files), save/share one combined JSONL, or share
through the system share sheet.

### Army List

Build and validate Warhammer 40,000 **11th Edition** army lists for every
faction in the bundled construction catalog (30 factions, faction-prefixed
datasheet/detachment ids). The experiment ships points, Detachment Points,
unique tags, and Leader join edges as versioned JSON, plus a deterministic
validator, SwiftUI authoring UI, and share/export as plain text or `.army.json`.
The editor focuses on units (drag to reorder); name, battle size, and
detachments live on **Army settings**. **Build starter list** on the New list
screen fills a roster from 0. Opening that screen does not load Laya. If a
download is already on disk, the button loads the graph and then Laya picks
among legal catalog moves. Otherwise a ranked greedy fill runs. The
controller then assigns legal enhancements and spends leftover points.
The construction loop farms work to three workers. Catalog code lists legal
moves, applies picks, and answers when only one option remains. Laya answers
when two or more options remain: detachments, units, model counts, warlord,
attaches, enhancements, and points cuts. It also answers leftover yes/no
questions: keep adding, pack leftover, and assign an enhancement. After the
pass it scores the finished list against the theme. Apple Intelligence writes
a short theme brief and a list name when it is available. Token overlap on
datasheet names and keywords is catalog work. Laya only gets a yes/no when a
candidate misses those tokens. Construction still runs without Apple
Intelligence or Laya.

Refresh the **bundled** catalog (no remote fetch at runtime):

```bash
python3 ios/scripts/refresh-army-list-catalog.py
```

A weekly GitHub Action (`.github/workflows/army-list-catalog.yml`) runs that
refresh on `main`, opens a PR, regenerates stress fixtures, and auto-merges
when CI is green. Catalog versions bump as `11e-<N>`; id migrations keep saved
lists pointed at the same named datasheets when ids would otherwise drift.

Stress-test the validator by building ~50 lists in Swift (same
`ArmyListValidator` as the app) and writing XCTest fixtures. Requires macOS:

```bash
bash ios/scripts/stress-army-lists.sh --write-fixtures
```

**List chat** (toolbar bubble on a list) always offers Build, Fill, and Fix.
Those chips load Laya when a download is already on disk, then run the
construction controller over legal catalog moves. Otherwise they use the
greedy fallback. Opening List chat does not load the graph. Optional theme
text steers ranking. Catalog code drops off-token units when any unit hits
the brief; Laya only classifies the leftovers. When Apple Intelligence is
available, Build and Fill ask it for a theme brief and a list name first.
Theme and Weaknesses still use on-device Foundation Models for matchup
write-ups. Those tools only summarize the list or rename it. Chat still
compacts AFM context with TN3193 first and last entries, a rolling summary,
and a list snapshot, and retries once on overflow. Without Apple Intelligence,
the construction chips stay available.

Unofficial fan experiment. Confirm points with Games Workshop for events.

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

### Voxel Eyes

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
(LiDAR only). The block edge is fixed at 10 cm, the smallest size that stays
crisp on the 256×192 depth map. LiDAR samples are kept out to 5 m, which is
as far as Apple's scanner reports. The camera photo is not shown. Every pixel
is drawn as a chunky palette square the size of a 10 cm block at that pixel's
depth (5 m when the scanner has no reading), and the voxel mesh draws in
front. A camera button floats on the viewer and saves the current frame,
camera plus voxels, to Photos. Rendering is chunked SceneKit geometry
with hidden interior faces culled and per-face shading baked into vertex
colors. Needs
camera permission (`NSCameraUsageDescription`) and add-only photo library
permission (`NSPhotoLibraryAddUsageDescription`). No new Bundle ID,
entitlement, or signing bootstrap. Works best on LiDAR devices
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

### Live Translate

Point the camera at printed or on-screen text. On-device Vision reads the
lines (`VNRecognizeTextRequest`) and detects their language on each frame, so
Japanese, Chinese, and Korean text is recognized too, not only English. A
tracker follows each line from one OCR pass to the next. It estimates the
camera's pan and zoom from lines that read the same in both passes, then pairs
each reading with the line that has similar text near its moved box. A line
keeps its identity through a misread, a missed pass, a pan, or a zoom.

Each line's overlay follows the reading's position, but its size changes
slowly. Motion blur or glare can swell OCR's box for a pass or two, and a
partial reading can shrink it, so a size change counts only once it lasts
three passes. The zoom estimate resizes the overlay right away.

After two passes read a line, a fresh `LanguageModelSession` translates it
into the language you picked. The reply streams, so each line appears as soon
as the model finishes it. The app stores each translation by its source text
while the experiment is open. Any later frame that reads a stored line shows
that translation without another model call, even after the camera looks away
and back. Readings that differ only in case, accents, spacing, or punctuation
share a translation. So do readings a letter or two apart whose digits match.
Each translation is painted over its source box using a sampled backdrop.
When every line in view is translated, the joined text is copied to the
pasteboard. It copies again only when a new line shows up. To copy on demand,
tap the copy control.

Each model call starts a new session (no tools, eight lines max) so the live
loop does not fill the 4096-token window. A context-window overflow retries
once with fewer lines. A line the model skips waits before its next try, and
the wait doubles each time. Needs camera permission (extends the existing
`NSCameraUsageDescription` — no new Bundle ID or signing bootstrap) and Apple
Intelligence for translation. Simulator opens the UI but has no camera.

`LiveTranslateClipTests` plays
`Tests/PlaygroundTests/Fixtures/LiveTranslate/moving-sign.mp4` through Vision
and the tracking pipeline, with a fake model in place of Foundation Models. The
clip is five seconds of a Spanish sign that pans, shakes, catches a glare, and
zooms, with fine print and a room plate that OCR reads unreliably. Each line on
the sign has to get a translation within the first three seconds and keep it on
at least 9 of every 10 later frames that read it. The test also compares each
overlay with where the line really is, from `moving-sign.json` next to the
clip: an overlay has to cover the line, and its height can't jump more than
12% between passes. To change the clip, edit and run
`ios/scripts/make-live-translate-clip.py`, which needs Pillow, NumPy, and
ffmpeg. It writes the clip and the JSON.

### Blather

The screen is a show page: cover, episode list, and a mini player. **New
episode** asks for a topic. Blather asks the on-device Foundation Model for a
spoken explainer, writes that speech to an audio file, and opens the player.
Playback waits until about 40 seconds of listening time are ready, then
starts. At 1.5×, 1.75×, and 2× that is more audio, because the same file ends
sooner. The next passage is written while the current one is turned into a
file. When about 25 seconds of listening time remain, it writes another
passage and keeps going. Faster playback starts that later work earlier.

The new-episode screen and the player include a voice control. It lists the
English voices installed on the device. Blather starts on the most
conversational one: a Siri or premium voice when you have downloaded one,
otherwise a natural voice ahead of the compact system voice. A voice you pick
is used for the next passage. Audio already written keeps its voice. Download
more voices under Accessibility, Spoken Content.

The player shows the episode cover, a scrubber, and a row of back 10 seconds,
playback speed (1×, 1.5×, 1.75×, 2×), play, keep writing, and forward 10
seconds. Pause, then type a direction, to change what it says next. **Keep
writing** on a saved episode appends more speech at the end and does not
start, pause, or move playback. While that is running the button is a
spinner, and tapping it stops writing. Close the player and the audio keeps
going in the mini
player, which has the same speed control. The lock screen shows the cover,
play, pause, skip, and playback speed. Playback continues while the screen is
locked (`UIBackgroundModes` includes `audio`). If a passage is still being
written when the phone locks, Blather finishes it if iOS allows, and otherwise
continues that passage when you open the app again.

Each episode stays on this device under Application Support: a JSON manifest,
a `cover.jpg`, and one audio file per passage. The cover is drawn on device
from the topic. `ImageCreator` does not run on iOS 27, so the app paints the
art itself.

Needs Apple Intelligence, the same on-device model gate as Live Translate.
The Simulator opens the screens and still draws covers. Generation and speech
need a device that supports Apple Intelligence.

### ESP32 BLE

Scan for a nearby board flashed with [`esp32-ble/`](../esp32-ble/), connect,
write LED commands (`led on`, `stop`, or the blink-speed slider), and show the
status line the firmware notifies. After the first connect, a drop immediately
retries that same peripheral. **Disconnect** stops the retries. Needs
`NSBluetoothAlwaysUsageDescription` only; Core Bluetooth central mode is not
an App ID capability, so no signing bootstrap. The Simulator opens the UI but
cannot see a real ESP32.

### App Attest

**Sign in with Apple** supplies the user id (the stable `ASAuthorizationAppleIDCredential.user`
string) and immediately runs Apple App Attest against the
[`app-attest/`](../app-attest/) Worker. The Worker checks the attestation and
binds that Apple user id and `deviceId` to the hardware key. Sign-in, opening
the experiment, and **Whoami** each spend a new challenge and a
`generateAssertion` so a reused token is not enough. **Sign out** drops the
Apple user, registration, and App Attest key.

Needs the App Attest App ID capability
(`com.apple.developer.devicecheck.appattest-environment` = `production`), the
Sign in with Apple capability (`com.apple.developer.applesignin` = `Default`),
and a match profile refresh (`needs-ios-bootstrap`). Simulator cannot generate a
Secure Enclave key; the handshake then uses `POST /v1/unattested-token`, which
production keeps off (`ALLOW_UNATTESTED=0`). Sign in with Apple still works on
the Simulator. Use a physical iPhone for a real handshake. Set the Worker
`APP_ID` var to `<Team ID>.io.github.imjasonh.playground` before a device
attestation can verify.

### Laya

[laya-coreml](https://github.com/mizorewww/laya-coreml) is a typed-decision
model: given a text (the *state*) and a `choice`, `score`, or `noul` (yes/no)
question, it returns a probability per option in one forward pass. It never
generates tokens. The upstream runtime is Python; this experiment is a Swift
port of its ANE path, so the same bundle runs on the phone.

The download, tokenizer, and Core ML runtime live in `Shared/Laya` so Army
List can load the same bundle (`LayaModelStore.shared`). The Laya experiment
is the diagnostics UI on top of that store. Opening it loads a downloaded
bundle. Army List does not: New list and List chat stay idle until Build,
Fill, or Fix, and that request loads the graph.

The bundle is
[`aac6fef/laya-multilingual-coreml-ane`](https://huggingface.co/aac6fef/laya-multilingual-coreml-ane)
pinned to the 0.1.0 release revision. **Download model** fetches the same
files `hub.py` allows (`coreml_config.json`, `rl_agent_config.json`,
`encoder/config.json`, `tokenizer/*`, `model.mlpackage/*`,
`host_weights.safetensors`, about 680 MB) into Application Support with the
`Hub` module of [swift-transformers](https://github.com/huggingface/swift-transformers),
checks each manifest SHA-256 once, compiles the `.mlpackage` with
`MLModel.compileModel` and caches the `.mlmodelc`, then loads the graph with
`.cpuAndNeuralEngine`. **Delete download** removes all of it.

The ANE export is fixed at batch 1, 96 tokens, and 32 option slots, so it is
for short decisions. The form shows the token count of the current draft
against that limit; a state that does not fit is truncated from the end, the
way `build_sequence` truncates, while the question head is kept whole.

What runs where, matching `ane.py`:

- The tokenizer is swift-transformers `AutoTokenizer` over the bundled
  `tokenizer.json`. The prompt is `[CLS] <type> question: <instructions>
  [SEP] [MASK] opt0 [MASK] opt1 … [SEP] <state> [SEP]`, with the same head
  and option token caps as `common.py` and the same padding as `inputs.py`.
- The token embedding table, type vectors, and attention masks are built on
  the CPU from `host_weights.safetensors` (read with a small memory-mapped
  safetensors parser; F16 / BF16 / F32) and handed to the Core ML graph as
  five `Float16` inputs.
- The graph returns marker logits and a pooled vector. The two-layer action
  head (`act_head`) runs on the CPU with exact-erf GELU, then temperature
  scaling, softmax, and normalized-entropy confidence follow `result.py`.

The Simulator has no Neural Engine, so Core ML falls back to the CPU there;
the answers are the same, just slower. On a physical iPhone, Core ML places
the graph on the ANE. Nothing here needs a capability or signing bootstrap.
Hugging Face is reached only for the download.

#### Debugging a TestFlight build

The Simulator cannot exercise the Neural Engine, so the screen is built to be
debugged from a device without a debugger attached:

- **Errors** show the stage that failed (`download`, `read bundle`,
  `compile`, `load`, `predict`), the message, and the `NSError` domain, code,
  file path, and underlying-error chain. Package signature and graph output
  mismatches print the actual names and shapes Core ML reported. **Copy
  error** puts that on the pasteboard.
- **Load performance** lists download size and throughput, checksum time,
  compile time and `.mlmodelc` size, and load time split into `MLModel.load`,
  tokenizer, and host weights, plus the process resident memory before and
  after the load.
- **Compute units** switches between CPU + Neural Engine, all, CPU + GPU, and
  CPU only; changing it unloads so **Load model** rebuilds with the new
  setting. **Analyze compute plan** asks `MLComputePlan` where each ML Program
  operation prefers to run and lists the operators that fall off the Neural
  Engine.
- Each answer shows the time spent in prepare (tokenize), host tensors,
  float16 packing, `MLModel.prediction`, and the action head, with median and
  p95 over recent asks. **Run 10×** repeats the current question and reports
  the first (warm-up) run separately from steady-state order statistics.
- Everything above is also appended to a diagnostics log that survives
  relaunches and **Delete download** (`Application Support/Laya-diagnostics.log`).
  **Copy report** and **Share report** bundle device facts, phase, stage
  timings, model info, signature, compute plan, latency history, benchmark,
  and the log into one text.

#### Snake demo

**Demos › Snake** is a port of
[`laya-coreml-snake`](https://github.com/mizorewww/laya-coreml/blob/main/docs/SNAKE_DEMO.md):
the model plays Snake on a 24 × 16 board by answering three questions per move.
Code owns the rules and a Hamiltonian-cycle safety planner (`LayaSnake.swift`,
a port of `snake/game.py`); it computes which moves are legal, which keep the
tail ahead on the cycle without passing the food, and whether the food is
reachable through empty cells. Those facts become the upstream compact prompt:
a `choice` over `UP`/`DOWN`/`LEFT`/`RIGHT` with one description per direction,
a `noul` "Is a safe route available?", and a `noul` "Is food reachable through
empty cells?". Under the board, each direction shows its probability, and
the executed move is highlighted. When the shield replaces that pick, the
model's direction is marked `proposed`. Dead-end risk (`1 − P(safe route)`),
food reachability, and the planner's best move stay in **Estimates**, below
the controls.

The **Cycle safety shield** (on by default) replaces an unsafe top-1 pick with
the most probable safe move and counts the intervention; the probabilities on
screen are never altered. Off, the model's top-1 runs as is and the snake can
die. **Decisions per second** paces the loop; **Max speed** moves as soon as
each decision is ready. **Step** plays one move while paused; **Next round**
starts the next seeded board and keeps the best score. The first round of a
launch takes a random seed from 1 to 9999. **Next round** uses the previous
seed plus one. The seed is shown under the status and written to the
diagnostics log with every round summary, so a round that died or hit a model
error can be reproduced from the log. Food placement is a seeded SplitMix64
generator, so a seed replays identically on any device, but not the same
sequence as the Python demo, which uses `random.Random`.

The ANE bundle is batch 1, so a move costs three `MLModel.prediction` passes.
The performance rows show inference time for the three questions and the graph
share of it, whole-decision time, median and p95 inference over the round,
achieved decisions per second, and the engine. Snake predictions stay out of
the Laya screen's per-ask history; round summaries, deaths, and failures are
appended to the diagnostics log, and **Copy round summary** copies the last
move, estimates, and timings with the device facts.

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

Compiler warnings fail the build (`SWIFT_TREAT_WARNINGS_AS_ERRORS` in
`project.yml`). Fix the warning. If an Apple type is not Sendable, add an
explicit `@unchecked Sendable` conformance next to the hop and say why.

## Shipping to TestFlight

[`docs/ios-testflight-setup.md`](../docs/ios-testflight-setup.md) ·
[`docs/ios-testflight-design.md`](../docs/ios-testflight-design.md)
