# Examples

`glider-tower-vase.stl` is the radial-envelope conversion of
`../life-stl/examples/gusset-glider-tower.stl`, regenerated with:

```bash
cargo run --release -- ../life-stl/examples/gusset-glider-tower.stl \
  -o examples/glider-tower-vase.stl --layer-height 1.0 --samples 48
```

Print it in spiral / vase mode (0 infill, 0 top layers).
