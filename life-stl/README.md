# life-stl

Generate a **3D-printable STL** of [Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life), with **time as the Z axis**: each generation is a layer of voxels stacked upward.

```bash
cargo run --release -- -x 24 -y 24 -z 48 --seed 42 -o life.stl

# Physical size in mm + cell size (voxel edge length):
cargo run --release -- \
  --width-mm 100 --height-mm 100 --depth-mm 600 \
  --cell 4 --seed 42 -o tower.stl
```

## Cell size (FDM / Bambu A1 Mini)

| | |
|--|--|
| **Default `--cell`** | **4.0 mm** (~10× a 0.4 mm nozzle) |
| **Minimum `--cell`** | **2.0 mm** (~5× a 0.4 mm nozzle) |

Assuming you meant a **0.4 mm** nozzle (A1 Mini stock) rather than 0.04 mm: **yes, 4 mm cells are comfortably printable** — each voxel is many line widths wide. At the 2 mm floor, prints are still plausible but fiddlier (thin towers, more stringing risk).

**Build volume caveat:** an A1 Mini is **180×180×180 mm**. A 100×100×600 mm tower will not fit in one piece; split the Z range, scale down, or use a taller machine.

## Scaffold: not breakaway

Scaffold voxels are **the same fused filament** as Life cells — they are **not** dissolvable or snappable supports. They exist so the nozzle has something to land on while printing overhanging births.

A model is **Life-self-supporting** when every Life voxel is **face-connected to the bed through Life|Base only** (scaffold ignored). Then fused scaffold is not load-bearing for the sculpture; if you could remove it, the object would still hold together.

| Situation | Behavior |
|-----------|----------|
| `--seed` omitted (`random` / `soup`) | Try seeds until Life is self-supporting (`--max-seed-attempts`, default 200) |
| `--seed` given (or named pattern like `glider`) | Always write the STL; **exit non-zero** if Life is not self-supporting, with an explanation |

Default `--pattern random` is a **still-life garden** (blocks, tubs, beehives, boats) keyed by seed — stable, so stacks are columns and pass the check. Use `--pattern soup` for classic chaotic Bernoulli Life (usually fails the removable-scaffold check).

## Print overhang vs orphans

- **Print overhang** — empty cell directly below a solid. `--mode scaffold` drives this to 0 for the printed mesh.
- **Life orphans** — Life voxels disconnected from the bed if scaffold is ignored. This is the “impossible object if scaffold is removed” test.

## Inputs

| Flag | Default | Meaning |
|------|---------|---------|
| `-x` / `--width` | `24` | Grid width (cells); ignored if `--width-mm` is set |
| `-y` / `--height` | `24` | Grid height (cells); ignored if `--height-mm` is set |
| `-z` / `--depth` | `48` | Generations above the base; ignored if `--depth-mm` is set |
| `--width-mm` | — | Physical X size (mm) |
| `--height-mm` | — | Physical Y size (mm) |
| `--depth-mm` | — | Physical total Z including base (mm) |
| `--cell` | `4.0` | Voxel edge length (mm); minimum `2.0` |
| `-s` / `--seed` | search | RNG seed; omit to search for a self-supporting seed |
| `--max-seed-attempts` | `200` | Seed search budget when `--seed` is omitted |
| `--density` | `0.25` | Still-life coverage (`random`) or soup fill (`soup`) |
| `--pattern` | `random` | `random` (still-life garden), `soup`, `glider`, `rpento`, `blinker`, `lwss` |
| `--base-layers` | `1` | Solid bed plate thickness (cells) |
| `--mode` | `scaffold` | `scaffold` or `raw` |
| `-o` / `--output` | `life.stl` | Output path |

Example tower: `--width-mm 100 --height-mm 100 --depth-mm 600 --cell 4` → **25×25×150** cells = **100×100×600 mm**.

## Examples

Under [`examples/`](examples/) (regenerate with `./generate-examples.sh`):

| File | Description |
|------|-------------|
| `glider-scaffold.stl` | Glider + scaffold (Life not self-supporting — CLI exits 1) |
| `random-42-scaffold.stl` | Still-life garden seed 42 |
| `tower-10x10x60-scaffold.stl` | **100×100×600 mm** garden tower, cell=4 mm |

See [`examples/REPORT.md`](examples/REPORT.md).

## Develop

```bash
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
./generate-examples.sh
```
