# Rhomcraft

A tiny Minecraft-like sandbox where every voxel is a **rhombic dodecahedron**
instead of a cube.

Rhombic dodecahedra tile 3D space. Their centers form a face-centered cubic
(FCC) lattice — integer coordinates `(x, y, z)` with even `x + y + z` — and each
cell has **12 face-neighbors** along `(±1,±1,0)` and permutations.

## Run

```bash
cd rhomcraft
npm start
```

Open the URL (default `http://localhost:3000`). Click the canvas for pointer
lock, then dig and build.

### Controls

| Input | Action |
|-------|--------|
| WASD / arrows | Move |
| Mouse | Look |
| Space | Jump |
| Shift | Sprint |
| LMB | Break |
| RMB | Place |
| 1–9 / scroll / Q·E | Hotbar |
| Esc | Release pointer |

Touch: left stick moves, drag on the right to look, Break / Place / Jump buttons.

## Test

```bash
npm test
```

Unit tests cover lattice helpers, face windings, world gen, raycast, meshing,
and basic game actions (no WebGL required).

## Layout

```
rhomcraft/
├── index.html          # entry + Three.js import map
├── styles.css
├── src/
│   ├── rhombic.js      # 14-vertex polyhedron + FCC helpers
│   ├── blocks.js       # palette
│   ├── noise.js        # terrain noise
│   ├── world.js        # sparse voxel map, gen, raycast
│   ├── mesher.js       # exposed-face mesh builder
│   ├── player.js       # FPS movement + soft collision
│   ├── game.js         # dig/place/hotbar state
│   └── app.js          # Three.js renderer + HUD
└── tests/
```

Rendering uses [Three.js](https://threejs.org/) from a CDN import map (no
bundle step). Geometry and world logic are plain ES modules so CI can test them
with Node’s built-in test runner.
