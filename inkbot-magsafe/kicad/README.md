# KiCad project: inkbot-magsafe

EVT hardware for a 60 x 99 mm portrait e-paper tile. The 3.97-inch panel is
the front face and overlaps the magnetic ring. The radio is a pre-certified
Raytac MDBT50Q-1MV2 nRF52840 module.

## Files

| File | Role |
|------|------|
| `inkbot-magsafe.kicad_pro` | Project |
| `inkbot-magsafe.kicad_sch` | Schematic (Qi + charger, module, panel) |
| `inkbot-magsafe.kicad_pcb` | Routed 60 × 99 mm board: battery cutout, ring high (30 mm keep-in), 0.8 mm 4-layer stackup, solid GND plane + signal and power tracks |
| `generate_schematic.py` | Regenerates the schematic from symbol libraries |
| `generate_pcb.py` | Regenerates the board outline and stackup |
| `route_freerouting.py` | Places the board and routes it through Freerouting's Specctra DSN/SES flow |
| `layout_route.py` | Shared placement, footprint, board-rule, and fabrication helpers |
| `run_drc.py` | Runs KiCad's board DRC engine and fails on hard violations |
| `run_erc.py` | Checks electrical pin contracts, no-connects, BOM coverage, and board parity |
| `tools/kicad_sch_helpers.py` | [kenchangh/kicad-schematic](https://github.com/kenchangh/kicad-schematic) helper (pin-accurate placement) |
| `tools/extract_symbol.py` | Embeds KiCad library symbols into the schematic |

## Regenerate

```bash
cd inkbot-magsafe/kicad
export FREEROUTING_JAR=/path/to/freerouting-2.4.1.jar
export FREEROUTING_JAVA=/path/to/java-25/bin/java
python3 route_freerouting.py
python3 run_drc.py
python3 run_erc.py
```

`route_freerouting.py` starts from the generated outline, exports the
schematic netlist, places the parts on the back, assigns nets, reserves In1.Cu
for SYS distribution and In2.Cu for ground, and exports a Specctra DSN file.
Two low-speed charger-control tracks cross In1.Cu; F.Cu and B.Cu carry the
remaining signals. The unbroken ground plane supplies their return path.
The script imports the SES file, refills the planes, and
writes Gerbers, drill, and centroid files under `fab/`. Freerouting 2.4.1
requires Java 25. The script runs without the GUI and disables Freerouting's
post-route optimizer because version 2.4.1 can hang while rendering conduction
areas. KiCad DRC checks the unoptimized route.

The fabrication export also writes a mirrored bottom-assembly PDF, a
populated STEP model, a schematic PDF, and a SHA-256 manifest tied to the source
commit. The manifest records the EVT classification and every unresolved gate
from `../production-gates.json`. Setting `INKBOT_PRODUCTION_EXPORT=1` blocks
the export unless that file classifies the design as `PRODUCTION` and gives
evidence for every passed gate. Review those files with the Gerber job before
ordering.

Open `inkbot-magsafe.kicad_pro` in KiCad 7 or later to inspect the result and
run interactive DRC before an order. A clean route is not approval to
fabricate. Complete the electrical, RF, thermal, and mechanical gates in the
design document first.

## Choices baked into this project

- **3.97-inch 480 x 800 GDEY0397T81P panel** with the full SSD1677 external
  boost circuit.
- **Accessory ring center 30 mm from the top edge** as an EVT placement
  hypothesis. Confirm each phone and camera keep-out against Apple's
  model-specific drawing. The panel overlaps the ring.
- **Raytac MDBT50Q-1MV2** pre-certified nRF52840 module (1 MiB flash and
  256 KiB RAM). Its antenna end is flush with the left board edge over
  an all-layer copper keep-out.
- **BQ51013C** Qi 1.3 receiver and default-off **BQ25186** protected-cell
  charger with a separate SYS power path.
- **TPS7A0230P** 3.0 V MCU rail with nRF52840 VDD and VDDH tied together.
- **TPS7A2030P** 3.0 V panel rail with active discharge.
- 0.8 mm, four-layer JLC7628 PCB with a 34 x 23 mm rounded battery cutout,
  1 oz outer copper, 0.5 oz inner copper, 0.10 mm minimum trace and clearance,
  0.5/0.25 mm standard vias, and two 0.45/0.20 mm Qi fanout vias.
- A bonded front panel plus a structural spacer and insulating rear cover.
