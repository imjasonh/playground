# Examples

## `glider-tower-vase.stl`

```bash
cargo run --release -- ../life-stl/examples/gusset-glider-tower.stl \
  -o examples/glider-tower-vase.stl --layer-height 1.0 --samples 48
```

## `secret-level-titus-vase.stl`

120 mm vase silhouette of Secret Level Titus. Auto-research (`--optimize`)
picked the **raw radial envelope** (no vertical/angular blur) at fine loft
spacing — that is the closest vase-mode match to the scaled source:

```bash
cargo run --release -- /path/to/Secret_level_titus.stl \
  -o examples/secret-level-titus-vase.stl \
  --height 120 --layer-height 0.4 --samples 180 \
  --detail-gain 1.0 --smooth-vertical-mm 0 --up z
```

Print-ready (fidelity-optimal) settings:

```bash
cargo run --release -- titus.stl -o titus-vase.stl \
  --height 120 --layer-height 0.15 --samples 360 \
  --detail-gain 1.0 --smooth-vertical-mm 0 --up z
# or: ... --optimize
```

Optional light denoise if slice jitter shows up (≈0.007 mm mean |Δr|):

```bash
--smooth-vertical-mm 0.25 --smooth-vertical-range-mm 0.2
```

Avoid large plain Gaussians (`σz ≥ 1.5`) — they melt helmet creases.
