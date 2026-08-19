# vase-stl

Convert an arbitrary **STL** into a shape that can be printed in FDM **vase /
spiral mode**.

## Algorithm

1. **Layer bands** — partition the (scaled) model into slabs one `--layer-height`
   thick. Inside each band, sample several Z planes and keep the **max** radius
   per angle (outer silhouette of that band).
2. **Couple bands** — curvature springs (`--couple-weight`) kill stair-steps on
   round ridges; then an **exact Lipschitz projection** enforces
   `|Δr| ≤ min(--couple-gap-mm, --line-width)` at every angle so consecutive
   walls always overlap within one extrusion. Conversion **fails** if this
   bonding check does not pass.
3. **Smooth loft** — Catmull-Rom densify along Z before meshing so the STL
   isn’t a coarse frustum staircase. The mesh is placed on the bed (`z=0`).

Output may be **STL** or **3MF** (extension of `-o`). For `.3mf`, loft densify is
forced to `1` and the package is stamped so **Bambu Studio** opens it as geometry
(not a broken project). Prefer `.3mf` for import; keep `.stl` if you want denser
preview meshes.

```bash
cd vase-stl
cargo run --release -- input.stl -o vase.3mf --height 120 --line-width 0.42
cargo run --release -- input.stl -o vase.stl --height 120 --optimize
```

In Bambu / any slicer: **Spiral vase** (or vase mode), 1 wall, 0 infill, 0 top
layers. Use a line width ≥ the `--line-width` you converted with (default
`0.42` for a 0.4 mm nozzle).

## CLI

| Flag | Default | Meaning |
|------|---------|---------|
| `-o, --output` | required | Output `.stl` or `.3mf` |
| `--layer-height` | `0.15` | Band thickness (mm) |
| `--samples` | `360` | Angular samples |
| `--band-subsamples` | `5` | Z samples per band (max radius) |
| `--couple-weight` | `0.25` | Curvature spring (`0`–`1`) |
| `--couple-gap-mm` | `0.35` | Max \|Δr\| between bands (capped at line width) |
| `--line-width` | `0.42` | Extrusion width; hard bonding budget |
| `--loft-subdivide` | `3` | Catmull-Rom densify factor |
| `--min-radius` | `0.4` | Floor under every radius (mm) |
| `--inflate` | `0` | Extra radius (mm) |
| `--smooth-angular` | `0` | Circular blur half-width |
| `--up` | auto | Force `x` / `y` / `z` as print-up |
| `--shell` | `solid` | `solid`, `open-top`, or `hollow` |
| `--wall` | `0.8` | Wall thickness when hollow |
| `--scale` / `--height` | — | Uniform scale / target height (mm) |
| `--detail-gain` | `1` | Amplify silhouette relief |
| `--optimize` | off | Sweep couple knobs among bonding-safe trials |

## Tests

```bash
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
```
