# KiCad project: inkbot-magsafe

Thickness-first MagSafe e-ink tile. No case: the panel is the front face.

## Files

| File | Role |
|------|------|
| `inkbot-magsafe.kicad_pro` | Project |
| `inkbot-magsafe.kicad_sch` | Schematic (Qi + charger, MCU, panel) |
| `inkbot-magsafe.kicad_pcb` | Board outline, battery cutout, MagSafe keepouts, 0.4 mm stackup |
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

## Thickness choices baked into this project

- Bare `nRF52832` QFN-48 (not a module) so the radio package is under 1 mm.
- `BQ51050B` Qi receiver with integrated LiPo charger (one IC instead of RX + charger).
- 0.4 mm 4-layer PCB with a central battery cutout so the cell does not stack on the PCB.
- No enclosure: panel bonded to the front, coil and magnets on the back.
