# life-stl

Generate a **3D-printable STL** of [Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life), with **time as the Z axis**: each generation is a layer of voxels stacked upward.

```bash
# Self-supporting glider tower (default gusset mode; 180 mm tall at --cell 4):
cargo run --release -- --pattern glider -x 16 -y 16 -z 44 -o glider-tower.stl

# Chaotic soup, A1 Mini max size, self-supporting:
cargo run --release -- --pattern soup --density 0.16 -x 44 -y 44 -z 44 -o soup.stl

# Soup with Cura-style breakaway tree supports instead:
cargo run --release -- --pattern soup --seed 99 --mode breakaway \
  --support-style tree -o soup-tree.stl
```

## Gusset mode (default): self-supporting by construction

The key observation: **stacked Life is never more than one diagonal step from
material below**. B3/S23 guarantees that every *birth* has exactly three live
parents in its Moore neighborhood one generation earlier, and every *survivor*
sits directly on itself. That is precisely the FDM 45° rule.

`--mode gusset` therefore adds a small leaning strut (**causality brace**) from
each birth down to each of its parents instead of any external supports:

- **Nothing to remove** — no supports, no cleanup, removability is trivially perfect.
- **One piece** — every voxel traces its ancestry to generation 0 on the base plate.
- **Readable causality** — the braces show which cells caused each birth.
- **Gliders and spaceships print** — motion is just births, and births are braced.

| Flag | Default | Meaning |
|------|---------|---------|
| `--gusset-width` | `1.8` | Brace strut width (mm) |

## Breakaway supports (`--mode breakaway`)

Adds **slim geometric supports** that **route around Life cells** instead of punching through them (Cura / Bambu ideas: collision clearance, layer-wise descent, shared trunks, rest-on-model). Rest-on-model landings are **double-tapered** (needle contact at both ends) so a few of them are practical to snap off; `--max-rest-on-model` (default 2) caps how many are allowed.

| Style | Behavior |
|-------|----------|
| `tree` (breakaway default) | Cluster nearby tips onto **shared trunks**; physics splits overloaded trunks |
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
| `--allow-rest-on-model` | off | Allow unlimited supports that land on Life roofs |
| `--max-rest-on-model` | `2` | Max rest-on-model landings (double-tapered) before the gate fails |
| `--max-inaccessible-tip-fraction` | `0.08` | Max tip contacts in enclosed pockets |
| `--max-tip-density` | `1.25` | Max tips per XY cell footprint |
| `--allow-hard-supports` | off | Skip the removability gate |
| `--min-active-generations` | `8` | Reject still life / short oscillators before this generation |
| `--min-active-fraction` | `1.0` | Require activity for this fraction of `--depth` (default: the whole stack) |
| `--max-boring-period` | `2` | Periods ≤ this count as boring once settled |
| `--allow-boring` | off | Skip the interestingness gate |

After generating supports, life-stl scores **how hard they are to remove** (rest-on-model landings, trunks trapped in cavities, tip contacts in pockets, tip density). It also scores **evolution complexity**: by default a pattern must stay active for its **entire printed height** — anything that settles into a still life or short oscillator partway up extrudes a boring static tower above the interesting part (lower `--min-active-fraction` to relax this). With `--seed` omitted it **retries** until both cleanup and interestingness look good; with an explicit seed it still writes the STL but **exits non-zero** if either gate fails.

Breakaway supports are meant to **snap off** after printing. The remaining Life|Base mesh is a **single standing piece** only when every Life voxel is face-connected to the bed (no “orphans”). In gusset mode connectivity follows **causality** instead — births are braced to their parents, so the whole stack is always one piece. Still-life gardens (`--pattern random`) are exempt from the complexity gate (stability is the point) and usually need **zero** supports. Chaotic `--pattern soup` under breakaway often has orphans → STL is written but the CLI exits non-zero if you passed an explicit seed.

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
| `--seed` omitted (`random`) | Search until Life is one piece (+ supports removable in breakaway) |
| `--seed` omitted (`soup`), gusset | Search until evolution stays interesting (always one piece) |
| `--seed` omitted (`soup`), breakaway | Search until supports removable **and** interesting |
| `--seed` given or named pattern | Always write STL; **exit non-zero** if a gate fails (boring / hard supports / orphans) |

## Inputs (dimensions)

| Flag | Default | Meaning |
|------|---------|---------|
| `-x/-y/-z` | `24/24/48` | Size in cells |
| `--width-mm` / `--height-mm` / `--depth-mm` | — | Size in mm (with `--cell`) |
| `--cell` | `4.0` | Voxel edge (mm) |
| `--pattern` | `random` | `random` (still-life garden), `soup`, `reverse`, `glider`, … |
| `--mode` | `gusset` | `gusset` (self-supporting), `breakaway`, or `raw` |

## Reverse evolution (`--pattern reverse`)

Builds the stack **backward** from a still-life ash at the top, preferring
**zero-birth** predecessors (sparks that die in one step → no support tips for
that layer). In practice those histories are only ~1 generation deep, so the
complexity gate still fails; see [`docs/reverse-and-methuselahs.md`](docs/reverse-and-methuselahs.md).
Gusset mode makes this moot for printing — kept for experimentation.

## Examples

See [`examples/`](examples/) and [`examples/REPORT.md`](examples/REPORT.md). Regenerate with `./generate-examples.sh`.

Every shipped STL is self-supporting (gusset) and stays **active for its entire printed height** — no still life or short oscillator before the top layer:

| File | What it is |
|------|------------|
| `gusset-glider-tower.stl` | Glider climbing 44 generations — 64×64×180 mm |
| `gusset-soup-mid.stl` | Chaotic soup, never settles — 96×96×148 mm |
| `gusset-soup-a1max.stl` | Chaotic soup at A1 Mini max, never settles — 176×176×180 mm |

Patterns that settle partway up (R-pentomino at gen 19 of 44, low-density soups at gen 8 of 24) and redundant spaceships (LWSS decays into a glider) were culled — they fail the default full-height activity gate.

## Develop

```bash
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
./generate-examples.sh
```
