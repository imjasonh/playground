# life-stl

Generate a **3D-printable STL** of [Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life), with **time as the Z axis**: each generation is a layer of voxels stacked upward.

```bash
cargo run --release -- -x 24 -y 24 -z 48 --seed 42 -o life.stl

# Or give physical size in mm + cell size (voxel edge length):
cargo run --release -- \
  --width-mm 100 --height-mm 100 --depth-mm 600 \
  --cell 2 --seed 42 -o tower.stl
```

## Printability (the hard part)

Stacking Life generations on Z looks straightforward, and for the usual **~45° Moore rule** it already works: every birth has live neighbors in the previous generation, so no voxel is truly “floating in air” relative to the 3×3 below.

The practical FDM problem is weaker. Births often sit on only an **edge or corner** of cubes below — empty cell directly underneath. Those bottom faces are the overhangs that droop or need supports. Prior art on CA→print pipelines (Reiss & Price, *Complex Processes and 3D Printing*, 2013) fights overhangs with cube overlap + mesh smoothing; printable “Conway towers” on Printables (Fernando Jerez, yury.dz, JoergLatte’s OpenSCAD generator) use the same Z=time stacking and are typically tuned for support-free printing.

`life-stl` keeps **exact** Life cells, then in default `--mode scaffold` inserts **vertical scaffold columns** under every solid that lacks face-on-face support from `(x,y,z-1)`. That drives the primary overhang metric to **zero**. Scaffold is extra plastic under births; Life geometry is unchanged.

| Mode | Behavior |
|------|----------|
| `scaffold` (default) | Exact Life + vertical support columns → overhang area = 0 |
| `raw` | Exact Life + base plate only → reports overhang area to expect in the slicer |

## Inputs

| Flag | Default | Meaning |
|------|---------|---------|
| `-x` / `--width` | `24` | Grid width (cells); ignored if `--width-mm` is set |
| `-y` / `--height` | `24` | Grid height (cells); ignored if `--height-mm` is set |
| `-z` / `--depth` | `48` | Generations above the base; ignored if `--depth-mm` is set |
| `--width-mm` | — | Physical X size (mm); rounded to a whole number of `--cell` voxels |
| `--height-mm` | — | Physical Y size (mm) |
| `--depth-mm` | — | Physical total Z size including base (mm) |
| `--cell` | `2.0` | Voxel edge length (mm) — pairs with either cell counts or `*-mm` |
| `-s` / `--seed` | random* | RNG seed for `--pattern random` (*printed if omitted) |
| `--density` | `0.35` | Initial fill probability for random patterns |
| `--pattern` | `random` | `random`, `glider`, `rpento`, `blinker`, `lwss` |
| `--base-layers` | `1` | Solid bed plate thickness (cells) |
| `--mode` | `scaffold` | `scaffold` or `raw` |
| `-o` / `--output` | `life.stl` | Output path |

Physical size ≈ `cells × cell` mm on each axis. Defaults: **48 × 48 × 98 mm**.  
Example tower: `--width-mm 100 --height-mm 100 --depth-mm 600 --cell 2` → **50×50×300** cells = **100×100×600 mm**.

## Unsupported-space estimate

After each run:

- **Unsupported overhang** — solids with an empty cell directly below. Area ≈ `count × cell²` mm². This is what `--mode scaffold` eliminates.
- **Moore-unsupported** — no solid in the 3×3 below. Always **0** for pure Life stacks (births require neighbors). Kept as a sanity check.

Slicer tip from printable Conway-tower authors: ~0.2–0.3 mm **horizontal expansion** can fuse adjacent cubes into fewer extrusion islands.

## Examples

Committed under [`examples/`](examples/) (regenerate with `./generate-examples.sh`):

| File | Description |
|------|-------------|
| `glider-scaffold.stl` | Glider, scaffold mode |
| `glider-raw.stl` | Same glider, raw (for comparison) |
| `random-42-scaffold.stl` | 24×24×48 random seed 42, scaffold |
| `random-42-raw.stl` | Same, raw |
| `rpento-scaffold.stl` | R-pentomino methuselah, scaffold |
| `tower-10x10x60-scaffold.stl` | **100×100×600 mm** tower (seed 42, cell=2mm, scaffold) |

Measured overhang areas: [`examples/REPORT.md`](examples/REPORT.md).

## Develop

```bash
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
cargo run --release -- --pattern glider -x 12 -y 12 -z 24 -o /tmp/glider.stl
./generate-examples.sh
```

## Layout

| Path | Role |
|------|------|
| `src/life.rs` | B3/S23 on a finite (non-wrapping) grid |
| `src/seed.rs` | Random + named patterns |
| `src/volume.rs` | Voxel grid (`Base` / `Life` / `Scaffold`) |
| `src/scaffold.rs` | Vertical support-column insertion |
| `src/metrics.rs` | Overhang / unsupported-area estimates |
| `src/mesh.rs` | Face-culled cubes → STL triangles |
