# Heli acoustics

A browser experiment in convincing 3D audio: a helicopter flies over a large
street canyon (~600 m across, eleven blocks). Occlusion, specular image-source
paths, edge diffraction, and a stochastic late field feed binaural Web Audio.

The physics model (Allen & Berkley ISM, Maekawa diffraction, ISO 9613-1 air
absorption, Kang-style scattering) is documented in
[`docs/acoustics-model.md`](docs/acoustics-model.md).

## What you hear

- **Direct path:** HRTF `PannerNode` with soft Maekawa occlusion muffling and Doppler from heli radial velocity.
- **Early paths:** order-1–3 image-source specular taps (pressure β/R) plus Maekawa edge diffraction. Materials use β = √(1−α) and scattering s.
- **Late field:** stochastic bounce energy (scatter mix) binned into a Convolver IR. Toggle with **V**.

Occlusion and order-1/2 specular candidates run in a **WebGPU compute shader**.
Order-3, diffraction, material banding, soft occlusion, and stochastic IR merge
on the CPU. **WebGPU is required** — the live app does not fall back to a CPU
solver. The HUD **solver** row shows `webgpu`, or the start screen reports an
error if the GPU is missing.

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
| F / Flight menu | Cycle traverse / orbit / follow |

**Traverse** (default): straight overflights, pause, another line. **Orbit**:
ellipse above the rooftops. **Follow**: crawls until it has line of sight, then
tracks you as you move.

## Coordinate frame

Web Audio right-handed: +x right, +y up, +z toward the viewer. Yaw 0 faces -z.
