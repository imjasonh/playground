# Examples

## `glider-tower-vase.stl`

Radial-envelope conversion of `../life-stl/examples/gusset-glider-tower.stl`:

```bash
cargo run --release -- ../life-stl/examples/gusset-glider-tower.stl \
  -o examples/glider-tower-vase.stl --layer-height 1.0 --samples 48
```

## `secret-level-titus-vase.stl`

Vase-mode silhouette of the Secret Level Titus figure, scaled to 120 mm tall
(coarser settings for a smaller checked-in file; bump `--samples` /
`--layer-height` for print-ready detail):

```bash
cargo run --release -- /path/to/Secret_level_titus.stl \
  -o examples/secret-level-titus-vase.stl \
  --height 120 --layer-height 0.5 --samples 96 \
  --smooth-angular 2 --smooth-vertical 0.35 --up z
```

Print in spiral / vase mode (0 infill, 0 top layers).
