# inkbot-magsafe hardware

Board design notes and the KiCad project for the MagSafe e-ink tile.

## KiCad project

See [`../kicad/`](../kicad/): schematic, routed 0.8 mm board (0.4 mm volume
target) with battery cutout, and generators that rebuild both from symbol
libraries.

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
