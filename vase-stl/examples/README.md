# Examples

## `glider-tower-vase.stl`

```bash
cargo run --release -- ../life-stl/examples/gusset-glider-tower.stl \
  -o examples/glider-tower-vase.stl --layer-height 1.0 --samples 48 \
  --couple-weight 0 --loft-subdivide 1 --band-subsamples 1
```

## `secret-level-titus-vase.stl`

Layer-band + curvature/gap coupling (tuned with `--optimize`):

```bash
cargo run --release -- /path/to/Secret_level_titus.stl \
  -o examples/secret-level-titus-vase.stl \
  --height 120 --layer-height 0.4 --samples 180 \
  --couple-weight 0.25 --couple-gap-mm 0.30 \
  --band-subsamples 5 --loft-subdivide 3 --up z
```

Print-ready:

```bash
cargo run --release -- titus.stl -o titus-vase.stl \
  --height 120 --layer-height 0.15 --samples 360 \
  --couple-weight 0.25 --couple-gap-mm 0.30 \
  --band-subsamples 5 --loft-subdivide 3
# or: ... --optimize
```
