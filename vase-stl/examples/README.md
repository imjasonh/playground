# Examples

## `glider-tower-vase.stl`

```bash
cargo run --release -- ../life-stl/examples/gusset-glider-tower.stl \
  -o examples/glider-tower-vase.stl --layer-height 1.0 --samples 48
```

## `secret-level-titus-vase.stl`

120 mm vase silhouette of Secret Level Titus. Uses vertical Gaussian
smoothing (`--smooth-vertical-mm`) so discrete slices don't terrace on a
smooth helmet hull:

```bash
cargo run --release -- /path/to/Secret_level_titus.stl \
  -o examples/secret-level-titus-vase.stl \
  --height 120 --layer-height 0.4 --samples 180 \
  --detail-gain 1.0 --smooth-vertical-mm 2.5 --smooth-angular 1 --up z
```

Print-ready artifact settings:

```bash
cargo run --release -- titus.stl -o titus-vase.stl \
  --height 120 --layer-height 0.2 --samples 360 \
  --detail-gain 1.0 --smooth-vertical-mm 2.5 --smooth-angular 1 --up z
```

Increase `--smooth-vertical-mm` (e.g. `3.5`) for an even creamier hull;
set it to `0` if you want every slice notch preserved.
