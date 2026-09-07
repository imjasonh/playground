# inkbot-magsafe hardware

Board design notes and the KiCad project for the MagSafe e-ink tile.

## KiCad project

See [`../kicad/`](../kicad/): the EVT schematic, 0.8 mm board with a routed
battery cutout, and generators that rebuild the design from source.

### Validation: DRC + ERC

Regenerate and check the board:

```bash
cd inkbot-magsafe/kicad
python3 generate_schematic.py
export FREEROUTING_JAR=/path/to/freerouting-2.4.1.jar
export FREEROUTING_JAVA=/path/to/java-25/bin/java
python3 route_freerouting.py
python3 run_drc.py
python3 run_erc.py
```

`route_freerouting.py` uses KiCad's Specctra DSN and SES support to run a real
autorouter. Freerouting 2.4.1 requires Java 25. The script disables the GUI,
analytics, API server, and post-route optimizer. The optimizer can hang on
conduction areas and is unnecessary because KiCad DRC is the release check.

**`run_drc.py` runs KiCad's real DRC engine** (clearance, hole, keep-out,
courtyard, mask, edge, connectivity, silk) through `pcbnew.WriteDRCReport`, not
a geometry approximation. `kicad-cli pcb drc` would be the tidier entry point,
but it only exists on KiCad 8+; this environment has KiCad 7.0, which cannot be
upgraded here (the KiCad PPA, Flathub, the Snap Store, and downloads.kicad.org
are all outside the sandbox's egress allow-list). The pcbnew engine is the same
core checker, so on KiCad 8/9 the tidier form is equivalent:

```bash
kicad-cli pcb drc --format report --exit-code-violations \
  --output fab/drc-report.txt inkbot-magsafe.kicad_pcb
```

`run_erc.py` substitutes for `kicad-cli sch erc` (also 8+ only): it flags
floating nets, checks that every unconnected pin is an intentional no-connect,
confirms the critical power/interface nets exist, and checks board↔netlist
parity.

#### Release criteria

- `run_erc.py` must report no contract, no-connect, BOM, or board-parity
  errors.
- `run_drc.py` must report no hard violations and no unconnected pads.
- `production-gates.json` must classify a production export as `PRODUCTION`
  and link evidence for every passed gate.
- The committed schematic must match a fresh generator run. Regenerating the
  placed board from the same source must preserve footprints, nets, keep-outs,
  fixed fanouts, and design rules before routing.
- A human must review the Gerbers, drill file, assembly drawing, BOM, centroid,
  board STEP model, schematic PDF, polarity marks, and component orientation
  before ordering.

The routing flow uses In1.Cu for SYS distribution and keeps In2.Cu as solid
ground. Three low-speed charger-control tracks cross In1.Cu; Freerouting routes
the remaining signals and plane fanouts on F.Cu and B.Cu. The outer layers do
not use ground pours, so every ground pad needs an explicit via to the solid
plane. The board is an EVT artifact until coil resonance, FOD, thermals, RF
behavior, and mechanical construction pass the bench gates in the design
document.

## Text sources

- [`netlist.md`](netlist.md): components and net-by-net connections.
- [`pinmap.md`](pinmap.md): module GPIO assignments (nRF port + module pin).
- [`stackup.md`](stackup.md): PCB stack and laminated enclosure requirements.

BOM: [`../../docs/inkbot-magsafe-bom.csv`](../../docs/inkbot-magsafe-bom.csv).
Circuit rationale: [`../../docs/inkbot-magsafe-design.md`](../../docs/inkbot-magsafe-design.md).

## Board summary

- MCU: **Raytac MDBT50Q-1MV2** pre-certified nRF52840 module. Its 1 MiB flash
  holds the update and frame slots, and its 256 KiB RAM leaves margin around
  the 48 KiB framebuffer. The antenna, 32 MHz crystal, DC/DC, and RF match are
  on the module.
- Panel: **3.97-inch 480x800 portrait** mono, 24-pin 0.5 mm FPC, SSD1677;
  fills the front and overlaps the MagSafe ring.
- Power: **BQ51013C** Qi 1.3 receiver, **BQ25186** charger with a
  default-off protected-cell power path, **TPS7A0230P** MCU LDO, and
  **TPS7A2030P** panel LDO.
- No user connector: SWD test pads for factory and erase recovery; wireless
  charging and signed BLE DFU are required before release.
- 4-layer PCB, **60 x 99 mm portrait**, **0.8 mm prototype** (0.4 mm volume
  study only), rounded battery cutout, and a required insulating rear cover.
- Ring high (30 mm from top edge) so the tile clears the camera bump and fits
  a 6.1" Pro in both width and height (minis dropped; 4.26" dropped for height).
