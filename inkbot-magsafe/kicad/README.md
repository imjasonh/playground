# KiCad project: inkbot-magsafe

Thickness-first MagSafe e-ink tile. Portrait, 66 × 108 mm, fits inside a
standard/Pro iPhone's width. No case: the 4.26-inch panel is the front face and
overlaps the MagSafe ring.

## Files

| File | Role |
|------|------|
| `inkbot-magsafe.kicad_pro` | Project |
| `inkbot-magsafe.kicad_sch` | Schematic (Qi + charger, MCU, panel) |
| `inkbot-magsafe.kicad_pcb` | Portrait 66 × 108 mm outline, battery cutout, MagSafe ring high (30 mm keep-in), 0.4 mm stackup |
| `generate_schematic.py` | Regenerates the schematic from symbol libraries |
| `generate_pcb.py` | Regenerates the board outline and stackup |
| `tools/kicad_sch_helpers.py` | [kenchangh/kicad-schematic](https://github.com/kenchangh/kicad-schematic) helper (pin-accurate placement) |
| `tools/extract_symbol.py` | Embeds KiCad library symbols into the schematic |

## Regenerate

```bash
cd inkbot-magsafe
python3 kicad/generate_schematic.py
python3 kicad/generate_pcb.py
kicad-cli sch export netlist -o /tmp/inkbot.net kicad/inkbot-magsafe.kicad_sch
```

Open `inkbot-magsafe.kicad_pro` in KiCad 7+, then **Update PCB from Schematic** to pull footprints onto the outline. Route with the antenna outside the MagSafe ring and the Qi coil inside it.

## Size and thickness choices baked into this project

- **4.26-inch 480×800 portrait panel** (module 62.4 × 105.3 mm) so the tile is
  66 mm wide and fits inside a standard/Pro iPhone (minis dropped).
- **MagSafe ring 30 mm from the top edge** (Apple's keep-in limit) so the tile
  hangs below the rear-camera plateau. The panel overlaps the ring.
- Bare `nRF52833` QFN-40 (128 KB RAM) for the 48 KB framebuffer.
- `BQ51050B` Qi receiver with integrated LiPo charger (one IC instead of RX + charger).
- 0.4 mm 4-layer PCB with a battery cutout so the cell does not stack on the PCB.
- No enclosure: panel bonded to the front, coil and magnets on the back.
