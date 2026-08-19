# Examples

## `glider-tower-vase.stl`

```bash
cargo run --release -- ../life-stl/examples/gusset-glider-tower.stl \
  -o examples/glider-tower-vase.stl --layer-height 1.0 --samples 48 \
  --couple-weight 0 --loft-subdivide 1 --band-subsamples 1
```

## `secret-level-titus-vase.stl`

Bonding-safe conversion (worst consecutive `|Δr|` ≤ line width):

```bash
cargo run --release -- /path/to/Secret_level_titus.stl \
  -o examples/secret-level-titus-vase.3mf \
  --height 120 --layer-height 0.15 --samples 360 \
  --couple-weight 0.25 --couple-gap-mm 0.35 --line-width 0.42 \
  --band-subsamples 5 --loft-subdivide 3 --up z
```

In Bambu Studio: import the `.3mf`, enable **Spiral vase**, 0.42 mm line width,
0.15 mm layer height, 1 wall, 0 infill, 0 top layers.
