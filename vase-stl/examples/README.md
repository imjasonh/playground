# Examples

## `glider-tower-vase.stl`

Radial-envelope conversion of `../life-stl/examples/gusset-glider-tower.stl`:

```bash
cargo run --release -- ../life-stl/examples/gusset-glider-tower.stl \
  -o examples/glider-tower-vase.stl --layer-height 1.0 --samples 48
```

## `secret-level-titus-vase.stl`

Vase-mode silhouette of the Secret Level Titus figure, scaled to 120 mm.
Defaults keep smoothing off; `--detail-gain` exaggerates shallow relief so it
survives a single-perimeter spiral print:

```bash
cargo run --release -- /path/to/Secret_level_titus.stl \
  -o examples/secret-level-titus-vase.stl \
  --height 120 --layer-height 0.5 --samples 180 \
  --smooth-angular 0 --smooth-vertical 0 --detail-gain 2.5 --up z
```

Print-ready (finer) settings used for artifacts:

```bash
cargo run --release -- titus.stl -o titus-vase.stl \
  --height 120 --layer-height 0.15 --samples 720 \
  --detail-gain 2.5 --up z
```

Print in spiral / vase mode (0 infill, 0 top layers).
