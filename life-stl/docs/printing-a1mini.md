# Printing on a Bambu A1 Mini (generic PLA)

Settings for printing gusset-mode models (e.g. `examples/gusset-acorn.stl`)
on a Bambu Lab A1 Mini with a 0.4 mm nozzle and generic PLA.

## Ready-made project file

[`examples/gusset-acorn-a1mini.3mf`](../examples/gusset-acorn-a1mini.3mf) is a
Bambu Studio project with everything below already applied — open it, slice,
print. If your Studio version refuses the embedded settings and loads geometry
only, apply the table below by hand to the standard presets.

## Presets

| Slot | Preset |
|------|--------|
| Printer | Bambu Lab A1 mini 0.4 nozzle |
| Process | 0.20mm Standard @BBL A1M |
| Filament | Generic PLA |
| Plate | Textured PEI (the stock plate) |

## Overrides and why

| Setting | Value | Why |
|---------|-------|-----|
| **Enable support** | **off** | The model is self-supporting: every overhanging cube is a Life *birth*, braced to its three parents at ≤45°. Slicer supports would fill the sculpture's interior and be miserable to dig out — worse than useless. |
| Wall loops | 3 | The 1.8 mm causality braces slice as almost pure perimeter; 3 loops make them solid instead of relying on gap fill. |
| Sparse infill | 15 % | The 4 mm cubes are small; 15 % grid is plenty and keeps the tall print light. |
| Bridge speed | 30 mm/s | Every birth cube's underside is a short (≤4 mm) bridge anchored on braces; slowing bridges keeps those undersides clean. |
| Brim | none | The base plate is a solid 4 mm-thick slab sized to the model footprint — more than enough bed adhesion on textured PEI. |

Everything else stays at profile defaults (220 °C nozzle, 60 °C textured
plate, 0.2 mm layers). Defaults already include what tall prints need most on
an A1 Mini: slow-down for overhangs and full part-cooling fan on bridges.

## Practical notes

- **Height**: the 44-generation examples are exactly 180 mm — the A1 Mini's
  ceiling. If your slicer flags the height, regenerate one generation shorter
  (`-z 43`).
- **Orientation**: as modeled — base slab down. Don't rotate; the entire
  geometry assumes +Z is up (bridged undersides, 45° braces).
- **No rafts**: a raft would ruin the flat base and isn't needed.
- **Filament**: any PLA is fine. Silk PLA looks striking on the braces but
  bridges slightly worse; drop bridge speed to ~20 mm/s.
- **Cleanup**: none. Nothing to remove — the braces are part of the sculpture
  (they show which cells caused each birth).

## Regenerating the .3mf

The project file is built by the `bambu-3mf` subcommand. The A1 Mini +
Generic PLA presets (and the override table above) are **embedded**, so no
network or profile checkout is needed:

```bash
cargo run --release -- bambu-3mf \
  --stl examples/gusset-acorn.stl \
  --name gusset-acorn \
  -o examples/gusset-acorn-a1mini.3mf
```

To target other printers/filaments, point `--profiles` at a Bambu Studio
`resources/profiles/BBL` checkout and pick presets by name; `--override
KEY=VALUE` (repeatable) replaces the default gusset-print overrides:

```bash
git clone --depth 1 --filter=blob:none --sparse https://github.com/bambulab/BambuStudio /tmp/bambu
git -C /tmp/bambu sparse-checkout set resources/profiles

cargo run --release -- bambu-3mf \
  --stl examples/gusset-pi.stl \
  --profiles /tmp/bambu/resources/profiles/BBL \
  --printer "Bambu Lab A1 mini 0.4 nozzle" \
  --process "0.16mm Optimal @BBL A1M" \
  --filament "Generic PLA @BBL A1M" \
  --override enable_support=0 --override wall_loops=3 \
  -o pi-fine.3mf
```

The exporter (`src/bambu.rs`) flattens the printer/process/filament
inheritance chains into the full settings dump Bambu Studio expects in a
project file, applies the overrides, and records them in
`different_settings_to_system` so Studio shows them as modifications of the
system presets. The embedded preset dump lives in
`src/bambu_profile_a1mini_pla.json` (regenerate it from a profile checkout if
Bambu ships materially new profiles).
