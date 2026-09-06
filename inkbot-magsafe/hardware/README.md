# inkbot-magsafe hardware

Board design notes for the MagSafe e-ink tile. These are the text sources an
engineer imports into an EDA tool; there is no committed EDA project yet.

- [`netlist.md`](netlist.md): components and net-by-net connections.
- [`pinmap.md`](pinmap.md): nRF52832 GPIO assignments.
- [`stackup.md`](stackup.md): PCB stack-up, mechanical stack, and fab notes.

The bill of materials is [`../../docs/inkbot-magsafe-bom.csv`](../../docs/inkbot-magsafe-bom.csv),
and the circuit rationale (power path, wireless charge, antenna, thickness) is
in [`../../docs/inkbot-magsafe-design.md`](../../docs/inkbot-magsafe-design.md).

Board summary:

- MCU: nRF52832 (Raytac MDBT42Q module for early boards), running from the LiPo
  through its internal DC/DC.
- Panel: 4.2-inch 400x300 mono, 24-pin 0.5 mm FPC, SSD1683-class controller.
- Power: BQ25100 power-path charger, BQ51013B 5 W Qi receiver, TPS22860 load
  switch gating a TPS7A02 3.3 V panel rail.
- No connector: SWD test pads for factory flash and recovery; wireless charge
  and BLE DFU otherwise.
- 4-layer PCB, ~91 x 77 mm, following the panel outline.
