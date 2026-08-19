# vase-stl

Convert an arbitrary **STL** into a shape that can be printed in FDM **vase /
spiral mode**.

## Algorithm

1. **Layer bands** — partition the (scaled) model into slabs one `--layer-height`
   thick. Inside each band, sample several Z planes and keep the **max** radius
   per angle (outer silhouette of that band).
2. **Couple bands** — pull consecutive bands together so the wall stays
   vase-printable and round ridges stay round:
   - curvature springs (`--couple-weight`) kill stair-steps without melting
     steady slopes;
   - gap drag (`--couple-gap-mm`) only moves pairs whose `|Δr|` exceeds the
     budget (≈ printable overhang).
3. **Smooth loft** — Catmull-Rom densify along Z before meshing so the STL
   isn’t a coarse frustum staircase.

`--optimize` sweeps couple weight / gap and picks the minimum of
hull-error + staircasing score.

```bash
cd vase-stl
cargo run --release -- input.stl -o vase.stl --height 120
cargo run --release -- input.stl -o vase.stl --height 120 --optimize
```

In the slicer: spiral vase / vase mode, 0 top layers, 0 infill, 0–3 bottoms.

## CLI

| Flag | Default | Meaning |
|------|---------|---------|
| `-o, --output` | required | Output STL path |
| `--layer-height` | `0.15` | Band thickness (mm) |
| `--samples` | `360` | Angular samples |
| `--band-subsamples` | `5` | Z samples per band (max radius) |
| `--couple-weight` | `0.25` | Curvature spring (`0`–`1`) |
| `--couple-gap-mm` | `0.30` | Max \|Δr\| between bands before drag |
| `--loft-subdivide` | `3` | Catmull-Rom densify factor |
| `--min-radius` | `0.4` | Floor under every radius (mm) |
| `--inflate` | `0` | Extra radius (mm) |
| `--smooth-angular` | `0` | Circular blur half-width |
| `--up` | auto | Force `x` / `y` / `z` as print-up |
| `--shell` | `solid` | `solid`, `open-top`, or `hollow` |
| `--wall` | `0.8` | Wall thickness when hollow |
| `--scale` / `--height` | — | Uniform scale / target height (mm) |
| `--detail-gain` | `1` | Amplify silhouette relief |
| `--optimize` | off | Sweep couple knobs; write best |

## Tests

```bash
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
```
