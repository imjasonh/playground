# Heli acoustics

A browser experiment in convincing 3D audio: a helicopter flies over a city and
you hear it reflect off the buildings. Built in milestones so each step is
judgeable from a live preview.

## Current milestone: M3–M4 late reverb + order-2

Five city blocks around a north-south avenue. First-person WASD + mouse or
touch drag. A helicopter loops overhead. Audio:

- **Direct path:** Web Audio HRTF `PannerNode`, distance falloff, and a low-pass
  + gain duck when a building blocks line of sight (toggle with **O**).
- **Early reflections:** order-1 and order-2 image-source bounces off facades
  and the street. Each bounce is a delay / gain / low-pass / HRTF tap aimed from
  the image location (toggle with **R**). Cyan rays are order-1; purple rays are
  order-2. Toggle rays with **G**.
- **Late reverb:** a diffuse `ConvolverNode` whose send level and IR length
  track how enclosed the listener is (street canyon vs open plaza). Toggle with
  **V**.

Order-2 runs on the CPU with a capped pair budget. WebGPU is not used; the
solver stays under a millisecond on this five-block scene.

## Run locally

```bash
npm start          # static server on :3000 (or: npx serve .)
```

No build step. Three.js is vendored under `vendor/`. Open in a browser, put on
headphones, click to start.

## Test

```bash
npm test           # node --test: geometry, occlusion, reflections, enclosure, IR, meters, vendor
npm run test:audio # Chromium: HRTF + live L/R + reflections A/B + reverb A/B
```

`test:audio` (also `test:e2e` for CI) launches Playwright Chromium and checks:

1. OfflineAudioContext HRTF left/right ear dominance.
2. Live orbit L/R balance flip with bearing.
3. Reflections-on vs reflections-off: average ear energy rises, and the solver
   finds order-1 and order-2 taps.
4. Reverb-on vs reverb-off in the canyon: average ear energy rises with the
   enclosure-driven Convolver send.

## Milestone history

- **M0:** binaural direct sound (HRTF + head turn), measured L/R meters.
- **M1:** three.js city, FPS controls, distance falloff, line-of-sight occlusion.
- **M2:** order-1 image-source early reflections + debug rays.
- **M3:** late reverb driven by enclosure (`ConvolverNode`).
- **M4:** order-2 image-source + CPU performance caps (no WebGPU).

## Spike: off-the-shelf library versus raw Web Audio

Raw Web Audio. Resonance Audio is the closest turnkey option but models a
single shoebox room, which cannot represent a helicopter ducking behind one
specific building. Per-building geometry is the point of this experiment, so
`PannerNode` (HRTF) handles the direct path and image-source reflections are
built here. howler.js / Tone.js add nothing for geometry. Steam Audio / Wwise
have no clean browser drop-in.

## Head tracking

AirPods head-tracking data is not exposed to browser JavaScript. This build
uses mouse-look and touch drag. Listener pose stays behind one seam
(`setListenerPose`) so a later input source can feed orientation without
touching the audio graph.

## Controls

| Input | Action |
|-------|--------|
| Tap / click start | Start audio (and pointer lock on desktop) |
| Drag on screen | Look (touch and mouse; works without pointer lock) |
| Mouse + pointer lock | Look (desktop) |
| WASD | Move (keyboard) |
| Occlusion checkbox (or O) | Enable / disable LOS muffling |
| Reflections checkbox (or R) | Enable / disable early reflections |
| Late reverb checkbox (or V) | Enable / disable enclosure reverb |
| Debug rays checkbox (or G) | Show / hide path lines |

## Refresh vendored three.js

```bash
npm install
npm run vendor
```

## Coordinate frame

Matches the Web Audio API: right-handed, +x right, +y up, +z toward the viewer.
A listener at yaw 0 faces down -z.
