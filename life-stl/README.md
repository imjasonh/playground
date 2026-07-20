# life-stl

Generate a **3D-printable STL** of [Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life), with **time as the Z axis**: each generation is a layer of voxels stacked upward.

```bash
cargo run --release -- -x 24 -y 24 -z 48 --seed 42 -o life.stl

# Soup with Cura-style tree supports (shared trunks + physics sizing):
cargo run --release -- --pattern soup --seed 99 \
  --support-style tree --support-tip-radius 0.12 --support-tip-height 2 \
  -o soup-tree.stl

# Same soup with one pillar per tip (for contrast):
cargo run --release -- --pattern soup --seed 99 \
  --support-style pillar -o soup-pillars.stl
```

## Breakaway supports (default)

Default `--mode breakaway` adds **slim geometric supports** that **route around Life cells** instead of punching through them (Cura / Bambu ideas: collision clearance, layer-wise descent, shared trunks, rest-on-model).

| Style | Behavior |
|-------|----------|
| `tree` (default) | Cluster nearby tips onto **shared trunks**; physics splits overloaded trunks |
| `pillar` | One shaft per tip; prefer a vertical drop, lean only when blocked |

Contacts taper to a **needle tip** (`--support-tip-radius`, default `0.12` mm; `0` = true point) over `--support-tip-height` so they snap off cleanly.

### Structural model (simplified, not full FEA)

Supports are sized with a beam/column model:

- Load ≈ PLA density × Life voxel volume × g × `--support-safety-factor`
- Shafts checked for compression, Euler buckling, and bending from lean
- Overloaded tree clusters **split** into more trunks (`--support-max-tips-per-trunk`)
- Trunk/branch radii auto-thicken up to `--support-max-trunk-radius`
- Tips stay thin on purpose (easy breakaway); strength lives in branches/trunks

| Flag | Default | Meaning |
|------|---------|---------|
| `--support-style` | `tree` | `tree` or `pillar` |
| `--support-radius` | `0.6` | Nominal branch / pillar shaft (mm) |
| `--support-tip-radius` | `0.12` | Needle contact radius (`0` = point) |
| `--support-tip-height` | `2.0` | Tip taper length (mm) |
| `--support-trunk-radius` | `1.1` | Nominal shared trunk (mm) |
| `--support-cluster` | `14` | XY merge radius (mm) |
| `--support-clearance` | `1.0` | XY keep-out from Life |
| `--support-branch-angle` | `40` | Max lean while dodging (5–60°) |
| `--support-auto-size` | on | Physics sizing + trunk splits |
| `--no-support-auto-size` | — | Freeze radii; no splits from load |
| `--filament-density` | `1.24` | g/cm³ (PLA) |
| `--allow-stress-mpa` | `18` | Working stress (MPa) |
| `--youngs-modulus-mpa` | `3000` | For buckling (PLA≈3 GPa) |
| `--support-safety-factor` | `3` | Multiplier on dead weight |
| `--support-max-tips-per-trunk` | `6` | Split after this many tips |
| `--support-min-shaft-radius` | `0.55` | Auto-size floor (mm) |
| `--support-max-trunk-radius` | `2.4` | Auto-size cap (mm) |
| `--min-removal-score` | `70` | Min post-print cleanup score (0–100) |
| `--allow-rest-on-model` | off | Allow supports that land on Life roofs |
| `--max-inaccessible-tip-fraction` | `0.08` | Max tip contacts in enclosed pockets |
| `--max-tip-density` | `1.25` | Max tips per XY cell footprint |
| `--allow-hard-supports` | off | Skip the removability gate |

After generating supports, life-stl scores **how hard they are to remove** (rest-on-model landings, trunks trapped in cavities, tip contacts in pockets, tip density). With `--seed` omitted it **retries** until cleanup looks practical; with an explicit seed it still writes the STL but **exits non-zero** if supports would be miserable to remove.

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

Only STLs that pass the **support removability** gate (`cleanup OK`) are shipped — currently ten easy-to-clean soups:

`soup-easy-{60,98,262,299,415,552,51,178,920,944}.stl`

Hard-to-remove shapes (dense soups, glider cages, full-bed chaos) are omitted on purpose. Still-life gardens are not shipped (static through Z). Soups may still leave Life orphans after cleanup (multiple pieces).

## Develop

```bash
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
./generate-examples.sh
```
