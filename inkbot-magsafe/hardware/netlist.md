# Netlist

Net-by-net connections for the tile. Reference designators match the KiCad
schematic in [`../kicad/`](../kicad/) and
[`../../docs/inkbot-magsafe-bom.csv`](../../docs/inkbot-magsafe-bom.csv).

## Power nets

- **QI_OUT**: Regulated 5 V from the BQ51013C receiver to the BQ25185
  charger input.
- **BAT**: Protected cell positive terminal and BQ25185 battery pin.
- **SYS**: BQ25185 power-path output to the nRF52833 `VDDH` pin and panel
  LDO input. C38 provides 220 uF of local pulse storage.
- **VDD_NRF**: nRF52833 REG0 output and decoupling only. The SWD fixture can
  use this net as a high-impedance target-voltage reference. It must not power
  external circuitry.
- **PANEL_3V0**: TPS7A2030P output to panel `VDDIO` and `VCI`.
- **QI_RECT**: BQ51013C rectifier reservoir. It does not power system loads.
- **GND**: Common return, including both exposed IC pads and all five Raytac
  module ground pads.

## Charger and sensing

- U3 is a BQ25185 with a separate power path.
- R6 = 24 kOhm selects 4.2 V battery regulation and the 100 mA input limit.
- R7 = 7.5 kOhm selects 40 mA fast charge. R8 and C20 provide the optional
  low-current ISET compensation network.
- The protected pack's 10 kOhm, 3435 K NTC connects from `BAT_NTC` to ground.
  `BAT_NTC` connects only to U3 `TS/MR`.
- `CHG_STAT1` and `CHG_STAT2` connect U3's open-drain status outputs to
  P0.04 and P0.05. Firmware enables the nRF GPIO pull-ups.
- `CHG_EN_N` connects U3 `/CE` to P0.06 and has a 100 kOhm default-enable
  pull-down.
- Firmware measures `SYS` with the nRF52833 SAADC `VDDHDIV5` input. In
  battery-only mode, `SYS` tracks the cell through the BQ25185 battery FET.

## Wireless power

- L2 is a TDK WR222230-26M8-G 27 uH receiver coil connected through J3.
- C1-C3 provide the 81 nF starting series-resonance value. C4-C5 provide
  950 pF parallel resonance. Freeze these values only after measuring the
  assembled coil's `Ls` and `Ls'`.
- C6-C11 implement the BQ51013C BOOT, CLAMP, and COMM networks.
- R1 + R2 set about 250 mA nominal operating current and 300 mA hardware
  overcurrent protection. R2, R3, and optional R4 are the FOD calibration set.
- RT2 is a 10 kOhm, 3435 K NTC bonded to the coil and connected to U2
  `TS/CTRL`.
- `QI_PRESENT` connects U2's open-drain `CHG` output to P0.02. Firmware
  enables the nRF GPIO pull-up.

## Panel (SPI + control)

Panel: GDEM0397T81P, 3.97-inch 480 x 800 portrait monochrome e-paper,
SSD1677 COG, and a 24-pin 0.5 mm FPC.

- PANEL_SCLK (P0.11) → J1 / panel SCK
- PANEL_MOSI (P0.15) → SDI
- PANEL_CS (P0.17) → CS#
- PANEL_DC (P0.20) → D/C#
- PANEL_RST (P1.09) → RST#
- PANEL_BUSY (P0.30) ← BUSY
- PANEL_PWR_EN (P0.31) → U4 EN
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
- SYS powers module pin 30 (`VDDH`). Module pin 28 (`VDD`) is the regulated
  SoC rail and is not tied to the cell.
- Factory provisioning writes UICR `REGOUT0=3.0 V`. Firmware checks this
  setting before it configures GPIO.
- LFXO Y1 connects to XL1/XL2 (P0.00/P0.01). It is the only external crystal.
- NFC1/NFC2 and USB remain unconnected.
- TP1-TP5 expose SWDIO, SWDCLK, reset, VDD reference, and ground.
- TP6-TP9 expose SYS, BAT, QI_OUT, and PANEL_3V0.

## Decoupling

- U1 uses separate VDDH and VDD capacitors, C21 and C22.
- U2 uses two 10 uF RECT capacitors plus high-frequency bypass and 10 uF OUT
  capacitance.
- U3 uses 1 uF IN, 10 uF SYS, and 1 uF BAT capacitors.
- U4 uses 1 uF input and 4.7 uF output capacitors.
- C38 is a low-leakage 220 uF MLCC on SYS. Validation must use its effective
  capacitance at 4.5 V, not the zero-bias nominal value.
