# Heli acoustics

A browser experiment in convincing 3D audio: a helicopter flies over a city and
you hear it reflect off the buildings. The end goal is a first-person urban
scene where the sound in your ears tracks the aircraft and the streets around
you. This is being built in milestones so you can judge each step from a live
preview before the next one starts.

M0 (this milestone) is the smallest possible proof: one synthesized helicopter
orbiting the listener, rendered through the Web Audio HRTF panner, with
drag-to-turn-your-head. No city, no reflections. If the direct sound does not
already track around your ears in headphones, nothing later will save it.

## Run locally

```bash
npm start          # static server on :3000 (or: npx serve .)
```

No build step. The app is plain ES modules with no dependencies. Open it in a
browser, put on headphones, and click to start.

## Test

```bash
npm test           # node --test over the pure geometry math
```

The Web Audio graph needs a browser, so tests cover the pure geometry in
`src/geometry.js` (orbit position, listener basis vectors, bearing, elevation,
distance falloff). That is the layer most likely to hide a sign error.

## Milestones

Each milestone is one PR with a live preview URL.

- **M0 (here): binaural direct sound.** Orbiting helicopter, HRTF panner,
  turn-your-head. Proves the spatializer.
- **M1: urban scene and occlusion.** three.js city (5 blocks, central street),
  FPS controls, distance falloff, line-of-sight muffling behind buildings.
- **M2: early reflections.** Image-source reflections off facades and the
  street, each an audible delayed and filtered tap, with debug rays.
- **M3: late reverb.** A convolution or feedback-delay tail driven by how
  enclosed you are (open intersection versus tight alley).
- **M4: order-2 reflections and performance.** Only if profiling says the CPU
  is the bottleneck; this is where WebGPU would earn its place, with real
  frame-time numbers.
- **M5: head tracking.** Mouse-look baseline plus WebXR pose, with a documented
  listener-pose seam for a future native path.

## Spike: off-the-shelf library versus raw Web Audio

The question for M0 was whether to adopt a spatial-audio library or drive the
Web Audio graph directly. The decision is **raw Web Audio**, and here is why.

**Web Audio `PannerNode` with `panningModel: "HRTF"`** is built into every
browser and does real binaural rendering for a moving point source, plus
distance attenuation. It has no concept of geometry, so reflections and
occlusion are on us. That is fine: those are exactly the milestones where the
project's value lives.

**Google Resonance Audio** is the closest turnkey option. Its Web Audio SDK
adds ambisonic HRTF plus early reflections and late reverb generated from a
*shoebox room* with per-surface materials. The catch is the shoebox: it models
one rectangular room, so it cannot represent a helicopter ducking behind one
specific building, a street canyon open to the sky, or reflections off a facade
that is not a wall of the box. Our whole premise is per-building geometry, which
is the one thing the shoebox cannot do. The project is also effectively in
maintenance.

**howler.js and Tone.js** wrap `PannerNode` for convenience and add nothing for
geometry-based reflections.

**Steam Audio and Wwise Reflect** do real geometry-driven acoustics, but they
are native or heavy engine integrations with no clean browser drop-in, so they
are out for a web-only target.

Conclusion: use `PannerNode` (HRTF) for the direct path and build the
reflections ourselves with the image-source method starting at M2. Resonance is
still worth a look at M3 as a possible late-reverb tail generator, but not as
the core engine.

## Head tracking, honestly

AirPods head-tracking data is not exposed to browser JavaScript, so a web app
cannot turn the game with your head through AirPods. The paths that do work on
the web are mouse-look (the M0 baseline) and WebXR head pose inside a VR
headset. M5 wires the listener pose through one seam so a future native iOS
build could feed real head tracking in without touching the audio code.

## Coordinate frame

Matches the Web Audio API: right-handed, +x right, +y up, +z toward the viewer.
A listener at yaw 0 faces down -z. Positive yaw turns the head right (clockwise
seen from above). The top-down view draws +x to the right and -z up the screen.
