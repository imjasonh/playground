# life-stl

Generate a **3D-printable STL** of [Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life), with **time as the Z axis**: each generation is a layer of voxels stacked upward.

```bash
cargo run --release -- -x 24 -y 24 -z 48 --seed 42 -o life.stl

# Soup with Cura-style tree supports (shared trunks):
cargo run --release -- --pattern soup --seed 99 \
  --support-style tree --support-cluster 24 --support-trunk-radius 1.2 \
  -o soup-tree.stl

# Same soup with one pillar per tip (for contrast):
cargo run --release -- --pattern soup --seed 99 \
  --support-style pillar -o soup-pillars.stl
```

## Breakaway supports (default)

Default `--mode breakaway` adds **slim geometric supports** that **route around Life cells** instead of punching through them (same idea as Cura / Bambu tree supports: collision clearance, layer-wise descent with a max branch angle, shared trunks, and rest-on-model when a path is blocked).

| Style | Behavior |
|-------|----------|
| `tree` (default) | Cluster nearby tips onto a **shared trunk**; diagonal branches join the trunk top |
| `pillar` | One shaft per tip; prefer a vertical drop, lean only when the column is blocked |

Tunable (mm / degrees):

| Flag | Default | Meaning |
|------|---------|---------|
| `--support-style` | `tree` | `tree` or `pillar` |
| `--support-radius` | `0.6` | Branch / pillar shaft radius |
| `--support-tip-radius` | `0.35` | Contact tip (smaller = easier snap) |
| `--support-tip-height` | `1.2` | Tip taper length |
| `--support-trunk-radius` | `1.1` | Shared tree trunk radius |
| `--support-cluster` | `18` | XY cluster radius for merging onto one trunk |
| `--support-tip-offset` | `0` | Shift tip toward +X/+Y from cell center |
| `--support-segments` | `8` | Cylinder tessellation |
| `--support-clearance` | `1.0` | XY keep-out from Life footprints (`0` → radius+0.4) |
| `--support-branch-angle` | `40` | Max lean from vertical while dodging (5–60°) |

Supports are meant to **snap off** after printing. The remaining Life|Base mesh is a **single standing piece** only when every Life voxel is face-connected to the bed (no “orphans”). Still-life gardens (`--pattern random`) usually need **zero** supports. Chaotic `--pattern soup` often has orphans → STL is written but the CLI exits non-zero if you passed an explicit seed.

`--mode raw` emits Life only (no supports).

## Cell size (FDM / Bambu A1 Mini)

| | |
|--|--|
| **Default `--cell`** | **4.0 mm** (~10× a 0.4 mm nozzle) |
| **Minimum `--cell`** | **2.0 mm** |

A1 Mini stock nozzle is **0.4 mm**. Build volume is **180³ mm** — keep `--depth-mm` (or `-z`) within that if you want a one-piece print.

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
