# inkbot-magsafe hardware

Board design notes and the KiCad project for the MagSafe e-ink tile.

## KiCad project

See [`../kicad/`](../kicad/): schematic, 0.4 mm board outline with battery
cutout, and generators that rebuild both from symbol libraries.

## Text sources

- [`netlist.md`](netlist.md): components and net-by-net connections.
- [`pinmap.md`](pinmap.md): nRF52833 GPIO assignments.
- [`stackup.md`](stackup.md): PCB and mechanical stack (thickness-first, no case).

BOM: [`../../docs/inkbot-magsafe-bom.csv`](../../docs/inkbot-magsafe-bom.csv).
Circuit rationale: [`../../docs/inkbot-magsafe-design.md`](../../docs/inkbot-magsafe-design.md).

## Board summary

- MCU: bare **nRF52833-QDAA** QFN-40 (128 KB RAM holds the 48 KB framebuffer).
- Panel: **4.26-inch 480x800 portrait** mono, 24-pin 0.5 mm FPC, SSD1677;
  fills the front and overlaps the MagSafe ring.
- Power: **BQ51050B** (Qi RX + LiPo charger), TPS22810 load switch, MIC5504-3.3
  panel LDO. System hangs on the cell (detach-to-charge).
- No connector: SWD test pads; wireless charge + BLE DFU otherwise.
- 4-layer PCB, **66 x 108 mm portrait**, **0.4 mm**, battery cutout, **no case**.
- Ring high (30 mm from top edge) so the tile clears the camera bump and fits
  the phone width (standard/Pro; minis dropped).
