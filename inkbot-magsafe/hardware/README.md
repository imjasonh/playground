# inkbot-magsafe hardware

Board design notes and the KiCad project for the MagSafe e-ink tile.

## KiCad project

See [`../kicad/`](../kicad/): schematic, routed 0.8 mm board (0.4 mm volume
target) with battery cutout, and generators that rebuild both from symbol
libraries.

### Validation: DRC + ERC

Regenerate and check the board:

```bash
cd inkbot-magsafe/kicad
python3 generate_schematic.py
kicad-cli sch export netlist -o /tmp/inkbot.net inkbot-magsafe.kicad_sch
python3 generate_pcb.py
python3 layout_route.py     # place, pour, route, stitch, export fab/
python3 run_drc.py          # KiCad's DRC engine -> fab/drc-report.txt
python3 run_erc.py          # netlist electrical rules + board parity
```

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

#### Current results

- **ERC: clean.** 0 errors, 13/13 critical nets present, board↔netlist parity
  holds. The only warnings are intentional no-connects (module unused GPIO,
  the panel FPC's unused pins 11–24, the MIC5504 NC pin). The **electrical
  design is validated**.
- **DRC: 49 error-severity violations**, down from 1067 on the first
  auto-route. The clearance-correct router (0.2 mm grid with a neighbour
  clearance check, honoring the module footprint's antenna keep-outs, board
  edge and cutout margins, via-halo spacing, and plane fanout) removed the
  ~900 grid-pitch shorts and the keep-out intrusions. What remains is
  concentrated in the **fine-pitch fanout** (0.5 mm-pitch QFN / module pins)
  and the **dense bottom cluster** (module + 44 mm-wide FPC courtyard + panel
  power + SWD pads on a 60×99 board), plus the **20 signal nets the grid router
  can't finish** (left as ratsnest).

The in-repo Python router is a placement-and-feasibility tool, not a
fab-ready autorouter. **Finish routing interactively in the pcbnew GUI** (or a
real autorouter) and re-run `run_drc.py` to zero before ordering boards; the
generators keep the schematic, planes, keep-outs, and fanout reproducible.

## Text sources

- [`netlist.md`](netlist.md): components and net-by-net connections.
- [`pinmap.md`](pinmap.md): module GPIO assignments (nRF port + module pin).
- [`stackup.md`](stackup.md): PCB and mechanical stack (thickness-first, no case).

BOM: [`../../docs/inkbot-magsafe-bom.csv`](../../docs/inkbot-magsafe-bom.csv).
Circuit rationale: [`../../docs/inkbot-magsafe-design.md`](../../docs/inkbot-magsafe-design.md).

## Board summary

- MCU: **Raytac MDBT50Q-512K** pre-certified nRF52833 module (128 KB RAM holds
  the 48 KB framebuffer; antenna, 32 MHz crystal, DC/DC, and RF match on-module).
- Panel: **3.97-inch 480x800 portrait** mono, 24-pin 0.5 mm FPC, SSD1677;
  fills the front and overlaps the MagSafe ring.
- Power: **BQ51050B** (Qi RX + LiPo charger), TPS22810 load switch, MIC5504-3.3
  panel LDO. System hangs on the cell (detach-to-charge).
- No connector: SWD test pads; wireless charge + BLE DFU otherwise.
- 4-layer PCB, **60 x 99 mm portrait**, **0.8 mm prototype** (0.4 mm volume
  target), battery cutout, **no case**.
- Ring high (30 mm from top edge) so the tile clears the camera bump and fits
  a 6.1" Pro in both width and height (minis dropped; 4.26" dropped for height).
