# vase-stl

Convert an arbitrary **STL** into a shape that can be printed in FDM **vase /
spiral mode**.

Vase mode can only extrude a single continuous perimeter per layer. This tool
approximates the input by its **radial envelope**: at each height and angle
around a vertical axis it keeps the farthest surface hit, then lofts those
contours into a watertight solid (or thin open-top wall).

```bash
cd vase-stl
cargo run --release -- input.stl -o vase.stl

# Scale a tiny model up to a printable height:
cargo run --release -- tiny.stl -o vase.stl --height 120

# Thin open-top wall instead of a solid:
cargo run --release -- input.stl -o vase-wall.stl --shell hollow --wall 0.8

# Sweep smoothing knobs vs the raw envelope; write the fidelity-first pick:
cargo run --release -- input.stl -o vase.stl --height 120 --optimize

# Force which input axis becomes print-up (default: longest AABB edge):
cargo run --release -- input.stl -o vase.stl --up z --layer-height 0.15 --samples 360
```

In the slicer: enable spiral vase / vase mode, 0 top layers, 0 infill, and
usually 0–3 bottom layers (or rely on the mesh bottom).

## CLI

| Flag | Default | Meaning |
|------|---------|---------|
| `-o, --output` | required | Output STL path |
| `--layer-height` | `0.15` | Slice / loft step (mm); finer = less terrace look |
| `--samples` | `360` | Angular samples around the axis |
| `--min-radius` | `0.4` | Floor under every radius (mm) |
| `--inflate` | `0` | Extra radius added everywhere (mm) |
| `--smooth-angular` | `0` | Circular blur half-width (samples) |
| `--smooth-vertical` | `0` | Legacy neighbor blend along Z (`0`–`1`) |
| `--smooth-vertical-mm` | `0` | Spatial σ along Z (mm); `0` = raw envelope |
| `--smooth-vertical-range-mm` | `0` | Bilateral range σ on radius (mm); `>0` = edge-preserving |
| `--up` | auto | Force `x` / `y` / `z` as print-up |
| `--shell` | `solid` | `solid`, `open-top`, or `hollow` |
| `--wall` | `0.8` | Wall thickness when `--shell hollow` (mm) |
| `--scale` | `1` | Uniform scale after orientation |
| `--height` | unset | Scale so oriented height becomes this (mm) |
| `--detail-gain` | `1` | Amplify silhouette relief (`>1` for more punch) |
| `--optimize` | off | Sweep knobs vs raw envelope; write best fidelity pick |
| `--chop-budget` | `0.12` | Soft terrace budget (mm) used in optimize scoring |

Defaults keep the **raw radial envelope** (minimal difference from the
scaled source that vase mode can represent). Optional bilateral smoothing
(`--smooth-vertical-mm 0.25 --smooth-vertical-range-mm 0.2`) removes only
tiny slice jitter; large Gaussian σ melts real creases.

## Library

```rust
use vase_stl::{convert, read_stl, write_stl, ConvertOptions, ShellMode};

let input = read_stl("in.stl".as_ref())?;
let mut opts = ConvertOptions::default();
opts.shell = ShellMode::Solid;
let out = convert(&input, &opts)?;
write_stl("out.stl".as_ref(), &out.mesh)?;
```

## Limits

- Deep concavities that are not star-convex from the print axis are filled in
  (by design — vase mode cannot print them anyway).
- Internal cavities and through-holes are ignored; only the outer radial
  silhouette is kept.
- Very sparse / non-manifold STLs may need a larger `--inflate` or more
  `--samples`.

## Tests

```bash
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
```
