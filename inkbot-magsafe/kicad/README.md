# KiCad project: inkbot-magsafe

Thickness-first MagSafe e-ink tile. Portrait, 60 × 99 mm, fits a 6.1" Pro in
both width and height. No case: the 3.97-inch panel is the front face and
overlaps the MagSafe ring. The radio is a pre-certified Raytac MDBT50Q-512K
(nRF52833) module, so there is no antenna or matching network to lay out.

## Files

| File | Role |
|------|------|
| `inkbot-magsafe.kicad_pro` | Project |
| `inkbot-magsafe.kicad_sch` | Schematic (Qi + charger, module, panel) |
| `inkbot-magsafe.kicad_pcb` | Routed 60 × 99 mm board: battery cutout, ring high (30 mm keep-in), 0.8 mm 4-layer stackup, GND/VSYS planes + signal tracks |
| `generate_schematic.py` | Regenerates the schematic from symbol libraries |
| `generate_pcb.py` | Regenerates the board outline and stackup |
| `layout_route.py` | Places footprints from the netlist, assigns nets, pours planes, routes tracks, fills, and exports the fab set |
| `tools/kicad_sch_helpers.py` | [kenchangh/kicad-schematic](https://github.com/kenchangh/kicad-schematic) helper (pin-accurate placement) |
| `tools/extract_symbol.py` | Embeds KiCad library symbols into the schematic |

## Regenerate

```bash
cd inkbot-magsafe
python3 kicad/generate_schematic.py
python3 kicad/generate_pcb.py
kicad-cli sch export netlist -o /tmp/inkbot.net kicad/inkbot-magsafe.kicad_sch
python3 kicad/layout_route.py            # place + net + pour + route + export
```

`layout_route.py` starts from the outline board, imports the schematic netlist,
places the module and support parts on the back, assigns nets to every pad,
pours In2/B.Cu ground and In1 VSYS planes, routes the signal nets, fills, and
writes Gerbers, drill, centroid, and BOM under `kicad/fab/`. Open
`inkbot-magsafe.kicad_pro` in KiCad 7+ to run DRC and check impedance before a
production order.

## Choices baked into this project

- **3.97-inch 480×800 portrait panel** (module 56.2 × 96.6 mm) so the tile is
  60 × 99 mm and fits a 6.1" Pro without side or bottom overhang (minis dropped;
  4.26" dropped because it hangs off the bottom).
- **MagSafe ring 30 mm from the top edge** (Apple's keep-in limit) so the tile
  hangs below the rear-camera plateau. The panel overlaps the ring.
- **Raytac MDBT50Q-512K** pre-certified nRF52833 module (128 KB RAM for the
  48 KB framebuffer) — antenna, 32 MHz crystal, DC/DC, and RF match on-module,
  so the board carries no discrete radio parts. Antenna end faces a board edge
  away from the ring.
- `BQ51050B` Qi receiver with integrated LiPo charger (one IC instead of RX + charger).
- 0.8 mm 4-layer prototype PCB (0.4 mm volume target) with a battery cutout so
  the cell does not stack on the PCB.
- No enclosure: panel bonded to the front, coil and magnets on the back.
