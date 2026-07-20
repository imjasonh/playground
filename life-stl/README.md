# life-stl

Generate a **3D-printable STL** of [Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life), with **time as the Z axis**: each generation is a layer of voxels stacked upward.

```bash
cargo run --release -- -x 24 -y 24 -z 48 --seed 42 -o life.stl

# Physical size + cell size:
cargo run --release -- \
  --width-mm 100 --height-mm 100 --depth-mm 600 \
  --cell 4 --seed 42 -o tower.stl

# Slimmer tree supports with a tinier snap tip:
cargo run --release -- --pattern soup --seed 7 \
  --support-style tree --support-radius 0.5 --support-tip-radius 0.3 \
  -o soup.stl
```

## Breakaway supports (default)

Default `--mode breakaway` adds **slim geometric supports**:

| Style | Behavior |
|-------|----------|
| `tree` (default) | Cluster nearby overhang tips onto bed trunks with diagonal branches |
| `pillar` | One vertical tapered pillar per overhang tip |

Tunable (mm):

| Flag | Default | Meaning |
|------|---------|---------|
| `--support-style` | `tree` | `tree` or `pillar` |
| `--support-radius` | `0.6` | Shaft / branch radius |
| `--support-tip-radius` | `0.35` | Contact tip (smaller = easier snap) |
| `--support-tip-height` | `1.2` | Tip taper length |
| `--support-trunk-radius` | `0.9` | Tree trunk radius |
| `--support-cluster` | `12` | XY cluster radius for shared trunks |
| `--support-tip-offset` | `0` | Shift tip toward +X/+Y from cell center |
| `--support-segments` | `8` | Cylinder tessellation |

Supports are meant to **snap off** after printing. The remaining Life|Base mesh is a **single standing piece** only when every Life voxel is face-connected to the bed (no “orphans”). Still-life gardens (`--pattern random`) usually need **zero** supports. Chaotic `--pattern soup` often has orphans → STL is written but the CLI exits non-zero if you passed an explicit seed.

`--mode raw` emits Life only (no supports).

## Cell size (FDM / Bambu A1 Mini)

| | |
|--|--|
| **Default `--cell`** | **4.0 mm** (~10× a 0.4 mm nozzle) |
| **Minimum `--cell`** | **2.0 mm** |

A1 Mini stock nozzle is **0.4 mm**. Build volume is **180³ mm** — a 600 mm-tall tower will not fit in one piece.

## Seed policy

| Situation | Behavior |
|-----------|----------|
| `--seed` omitted (`random` / `soup`) | Search until Life is one piece after support removal |
| `--seed` given or named pattern | Always write STL; **exit non-zero** if orphans remain |

## Inputs (dimensions)

| Flag | Default | Meaning |
|------|---------|---------|
| `-x/-y/-z` | `24/24/48` | Size in cells |
| `--width-mm` / `--height-mm` / `--depth-mm` | — | Size in mm (with `--cell`) |
| `--cell` | `4.0` | Voxel edge (mm) |
| `--pattern` | `random` | `random` (still-life garden), `soup`, `glider`, … |
| `--mode` | `breakaway` | `breakaway` or `raw` |

## Examples

See [`examples/`](examples/) and [`examples/REPORT.md`](examples/REPORT.md). Regenerate with `./generate-examples.sh`.

## Develop

```bash
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
./generate-examples.sh
```
