# Netlist

Net-by-net connections for the tile. Reference designators match the KiCad
schematic in [`../kicad/`](../kicad/) and
[`../../docs/inkbot-magsafe-bom.csv`](../../docs/inkbot-magsafe-bom.csv).

## Power nets

- **QI_OUT**: Regulated 5 V from the BQ51013C receiver to the BQ25186
  charger input.
- **BAT**: Protected cell positive terminal and BQ25186 battery pin.
- **SYS**: BQ25186 power-path output to the MCU and panel LDO inputs. C38
  provides 47 uF of local storage while total nominal SYS capacitance remains
  below the charger's 100 uF limit.
- **MCU_3V0**: TPS7A0230P output to both nRF52833 VDD and VDDH pins, the
  charger I2C pull-ups, and the SWD voltage-reference pad.
- **PANEL_3V0**: TPS7A2030P output to panel `VDDIO` and `VCI`.
- **QI_RECT**: BQ51013C rectifier reservoir. It does not power system loads.
- **GND**: Common return, including both exposed IC pads and all five Raytac
  module ground pads.

## Charger and sensing

- U3 is a BQ25186 with a separate power path and programmable JEITA limits.
- Firmware configures 4.2 V regulation, a 100 mA input limit, 40 mA fast
  charge, and a 0-45 degrees Celsius charge window before it enables charging.
- R5 pulls `/CE` up to SYS, so charging defaults off. Q2 pulls `/CE` low
  only after `CHG_ENABLE` goes high; R6 holds the MOSFET off during reset.
- R7 and R8 pull the I2C lines to `MCU_3V0`. `CHG_INT_N` and `CHG_PG_N` use
  MCU internal pull-ups.
- The protected pack's 10 kOhm, 3435 K NTC connects from `BAT_NTC` to ground.
  `BAT_NTC` connects only to U3 `TS/MR`.
- R9, R10, and C20 form the `SYS_SENSE` divider and filter for P0.29/AIN5.
  In battery-only mode, `SYS` tracks the cell through the BQ25186 battery FET.

## Wireless power

- L2 is a TDK WR222230-26M8-G 27 uH receiver coil connected through J3 pins
  1 and 2.
- C1-C3 provide the 81 nF starting series-resonance value. C4-C5 provide
  950 pF parallel resonance. Freeze these values only after measuring the
  assembled coil's `Ls` and `Ls'`.
- C6-C11 implement the BQ51013C BOOT, CLAMP, and COMM networks.
- R1 + R2 set about 250 mA nominal operating current and 300 mA hardware
  overcurrent protection. R2, R3, and optional R4 are the FOD calibration set.
- RT2 is a 10 kOhm, 3435 K NTC bonded to the coil. Its insulated leads use J3
  pins 3 and 4 and connect to U2 `TS/CTRL`.
- `QI_PRESENT` connects U2's open-drain `CHG` output to P0.02. Firmware
  enables the nRF GPIO pull-up.
- `QI_EN1` and `QI_EN2` connect U2 EN1/EN2 to P0.03 and P1.08. Firmware drives
  both high after charge completion so the receiver sends EPT 0x01 and lets the
  transmitter sleep.

## Panel (SPI + control)

Panel: GDEY0397T81P, 3.97-inch 480 x 800 portrait monochrome e-paper,
SSD1677 COG, and a 24-pin 0.5 mm FPC.

- PANEL_SCLK (P0.11) → J1 / panel SCK
- PANEL_MOSI (P0.15) → SDI
- PANEL_CS (P0.17) → CS#
- PANEL_DC (P0.20) → D/C#
- PANEL_RST (P1.09) → RST#
- PANEL_BUSY (P0.30) ← BUSY
- PANEL_PWR_EN (P0.31) → U4 EN. The TPS7A20's internal 500 kOhm smart
  pull-down keeps the panel rail off while the MCU pin is high impedance.
- J1 pins 15 and 16 connect `VDDIO` and `VCI` to `PANEL_3V0`.
- J1 pin 18 is the internally regulated 1.8 V `VDD` node and has only its
  reservoir capacitor.
- J1 pin 8 (`BS1`) is grounded for four-wire SPI. Pins 1, 4, 6, 7, and 19
  remain open as the panel data sheet requires.
- L1, Q1, D1-D3, C28-C37, R11, and R12 implement the panel-specific external
  boost and reservoir circuit.

## Radio, timing, debug

- U1 is the Raytac MDBT50Q-512K module: 2.4 GHz antenna, 32 MHz HFXO, DC/DC, and
  RF match are inside it. The board has no discrete RF network.
- U5 regulates SYS to `MCU_3V0`. The rail powers module pins 28 (`VDD`) and 30
  (`VDDH`) together, which selects the nRF52833 normal-voltage circuit.
- LFXO Y1 connects to XL1/XL2 (P0.00/P0.01). It is the only external crystal.
- NFC1/NFC2 and USB remain unconnected.
- TP1-TP5 expose SWDIO, SWDCLK, reset, VDD reference, and ground.
- TP6-TP9 expose SYS, BAT, QI_OUT, and PANEL_3V0.

## Decoupling

- U5 uses C21 at its input; C22 provides the module's 10 uF rail decoupling.
- U2 uses two 10 uF RECT capacitors plus high-frequency bypass and 10 uF OUT
  capacitance.
- U3 uses 1 uF IN, 10 uF SYS, and 1 uF BAT capacitors.
- U4 uses a 1 uF input capacitor and a 100 uF panel-rail reservoir.
- C38 is a 47 uF, 10 V MLCC on SYS. C27 is a 100 uF, 6.3 V MLCC on
  PANEL_3V0. Validation must use effective capacitance at operating bias, not
  the zero-bias nominal values.
