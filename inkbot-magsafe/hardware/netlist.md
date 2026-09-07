# Netlist

Net-by-net connections for the tile. Reference designators match the KiCad
schematic in [`../kicad/`](../kicad/) and
[`../../docs/inkbot-magsafe-bom.csv`](../../docs/inkbot-magsafe-bom.csv).

## Power nets

- **VSYS**: LiPo positive and BQ51050B BAT. The system hangs on the cell
  (detach-to-charge: you never cut over mid-use).
  - BT1+ → U5 BAT → U1 VDD, U3 VIN, C10 bulk, sense dividers
- **VSW_PANEL**: load-switch output (U3 VOUT).
- **V3V3_PANEL**: MIC5504 output to the panel FPC.
- **QI_RECT**: BQ51050B RECT rail (support caps only).
- **GND**: common ground, coil shield reference, antenna return.

## Charger and sensing

- U5 (BQ51050B) integrates Qi receive and LiPo charge. ILIM / FOD / TERM set by
  R1–R3. TS/CTRL shares the NTC with the MCU.
- U5 ~CHG → CHG_STAT (P0.05), pulled up to VSYS
- VBAT divider → VBAT_SENSE (P0.03/AIN1)
- NTC → NTC_SENSE (P0.04/AIN2) and U5 TS/CTRL

## Wireless power

- L1 (MagSafe-profile coil) → U5 AC1/AC2
- Series/shunt resonance and COMM/CLAMP/BOOT caps per the BQ51050B reference
- Ferrite between L1 and the board

## Panel (SPI + control)

Panel: 3.97-inch 480×800 portrait mono e-ink, SSD1677 COG, 24-pin 0.5 mm FPC.

- PANEL_SCLK (P0.11) → J1 / panel SCK
- PANEL_MOSI (P0.15) → SDI
- PANEL_CS (P0.17) → CS#
- PANEL_DC (P0.20) → D/C#
- PANEL_RST (P1.09) → RST#
- PANEL_BUSY (P0.30) ← BUSY
- PANEL_PWR_EN (P0.31) → U3 EN/UVLO
- Panel charge-pump caps on the remaining FPC pins per the panel datasheet

## Radio, timing, debug

- U1 ANT → matching (C22 stub) → ANT2 2.4 GHz chip antenna
- LFXO Y1 → XL1/XL2; HFXO Y2 → XC1/XC2
- NFC1/NFC2 (P0.09/P0.10) unused — no NFC antenna; pairing and frames are BLE
- SWDIO, SWDCLK, NRST, VSYS, GND → TP1–TP5

## Decoupling

- U1: VDD/VDDH caps, one cap per DEC rail (DEC1/3/4/5/6, DECUSB), DCC inductor
  per Nordic nRF52833 reference; VBUS tied to GND (USB unused)
- U3/U4/U5: datasheet input/output caps
- C10: 220 uF across VSYS next to the panel connector for refresh inrush
