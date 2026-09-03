# Heli acoustics

A browser experiment in convincing 3D audio: a helicopter flies over a city and
you hear it reflect off the buildings. Built in milestones so each step is
judgeable from a live preview.

## Current milestone: M2 early reflections

Five city blocks around a north-south avenue. First-person WASD + mouse look. A
helicopter loops overhead. Audio:

- **Direct path:** Web Audio HRTF `PannerNode`, distance falloff, and a low-pass
  + gain duck when a building blocks line of sight (toggle with `O`).
- **Early reflections:** order-1 image-source bounces off facades and the
  street. Each bounce is a delay / gain / low-pass / HRTF tap aimed from the
  image location (toggle with `R`). Debug rays (`G`) draw the direct path
  (green clear / red occluded) and cyan bounce polylines.

## Run locally

```bash
npm start          # static server on :3000 (or: npx serve .)
```

No build step. Three.js is vendored under `vendor/`. Open in a browser, put on
headphones, click to start.

## Test

```bash
npm test           # node --test: geometry, occlusion, reflections, meters, vendor
npm run test:audio # Chromium: HRTF proof + live L/R flip + reflections energy A/B
```

`test:audio` (also `test:e2e` for CI) launches Playwright Chromium and checks:

1. OfflineAudioContext HRTF left/right ear dominance.
2. Live orbit L/R balance flip with bearing.
3. Reflections-on vs reflections-off: average ear energy rises when wet taps are
   enabled, and the image-source solver finds at least one tap during the orbit.

## Milestone history

- **M0:** binaural direct sound (HRTF + head turn), measured L/R meters.
- **M1:** three.js city, FPS controls, distance falloff, line-of-sight occlusion.
- **M2 (here):** order-1 image-source early reflections + debug rays.
- **M3 (next):** late reverb driven by enclosure.
- **M4:** order-2 + performance (WebGPU only if profiling demands it).
- **M5:** head-tracking options (mouse-look + WebXR), seam for native.

## Spike: off-the-shelf library versus raw Web Audio

Raw Web Audio. Resonance Audio is the closest turnkey option but models a
single shoebox room, which cannot represent a helicopter ducking behind one
specific building. Per-building geometry is the point of this experiment, so
`PannerNode` (HRTF) handles the direct path and image-source reflections are
built here. howler.js / Tone.js add nothing for geometry. Steam Audio / Wwise
have no clean browser drop-in.

## Head tracking, honestly

AirPods head-tracking data is not exposed to browser JavaScript. This build
uses mouse-look. WebXR pose is the realistic web path later. Listener pose
stays behind one seam so a future native iOS build could feed real head
tracking in without touching the audio graph.

## Controls

| Input | Action |
|-------|--------|
| Click | Start + pointer lock |
| Mouse | Look |
| WASD | Move |
| O | Toggle occlusion |
| R | Toggle reflections |
| G | Toggle debug rays |

## Refresh vendored three.js

```bash
npm install
npm run vendor
```

## Coordinate frame

Matches the Web Audio API: right-handed, +x right, +y up, +z toward the viewer.
A listener at yaw 0 faces down -z.
