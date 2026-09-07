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
| `inkbot-magsafe.kicad_pcb` | Routed 60 × 99 mm board: battery cutout, ring high (30 mm keep-in), 0.8 mm 4-layer stackup, solid GND plane + signal and power tracks |
| `generate_schematic.py` | Regenerates the schematic from symbol libraries |
| `generate_pcb.py` | Regenerates the board outline and stackup |
| `route_freerouting.py` | Places the board and routes it through Freerouting's Specctra DSN/SES flow |
| `layout_route.py` | Placement-and-feasibility grid router used to prototype the board |
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

`route_freerouting.py` starts from the generated outline, exports the committed
schematic's netlist, places the module and support parts on the back, assigns
nets, reserves In2.Cu as the solid GND plane, pre-routes the dense receiver
fanout, and exports a Specctra DSN file. Freerouting routes F.Cu, In1.Cu, and
B.Cu while leaving the ground plane intact. The script imports the SES file,
refills the ground pours, and writes Gerbers, drill, and centroid files under
`fab/`. Freerouting 2.4.1 requires Java 25. Headless Linux also requires
`xvfb-run`.

Open `inkbot-magsafe.kicad_pro` in KiCad 7 or later to inspect the result and
check impedance before a production order.

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
