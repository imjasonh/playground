# Heli acoustics

A browser experiment in convincing 3D audio: a helicopter flies over a tall
street canyon. Occlusion, specular image-source paths, edge diffraction, and a
stochastic late field feed binaural Web Audio.

## What you hear

- **Direct path:** HRTF `PannerNode` with LOS occlusion muffling.
- **Early paths:** order-1–3 image-source specular taps plus geometric edge
  diffraction around building corners and roofs. Materials (concrete, glass,
  asphalt) apply frequency-dependent absorption to each bounce.
- **Late field:** stochastic bounce energy binned into a Convolver IR (rebuilds
  as you move). Toggle with **V**.

Occlusion and order-1/2 specular candidates run in a **WebGPU compute shader**.
Order-3, diffraction, material banding, and stochastic IR merge on the CPU.
**WebGPU is required** — the live app does not fall back to a CPU solver. The HUD
**solver** row shows `webgpu`, or the start screen reports an error if the GPU
is missing.

Debug rays: cyan order-1, purple order-2, pink order-3, amber diffraction.

## Run locally

```bash
npm start
```

Headphones. Tap or click to start.

## Test

```bash
npm test
npm run test:audio
```

## Milestone history

- **M0–M2:** HRTF, city, occlusion, order-1 reflections
- **M3:** enclosure late reverb
- **M4:** order-2 + WebGPU solver
- **Fidelity:** taller canyon, order-3, edge diffraction, materials, stochastic IR

## Controls

| Input | Action |
|-------|--------|
| Tap / click start | Start audio |
| Drag | Look |
| WASD | Move |
| O / R / V / G | Occlusion / reflections / reverb / rays |

## Coordinate frame

Web Audio right-handed: +x right, +y up, +z toward the viewer. Yaw 0 faces -z.
