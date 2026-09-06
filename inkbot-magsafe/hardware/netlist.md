# Netlist

Net-by-net connections for the tile. Reference designators match
[`../../docs/inkbot-magsafe-bom.csv`](../../docs/inkbot-magsafe-bom.csv).
Component pin names follow each part's datasheet.

## Power nets

- **VBAT**: the LiPo positive terminal (BT1+).
  - BT1+ → U2 BAT
  - BT1+ → C_BULK reservoir (with VSYS, see below)
- **VSYS**: system rail out of the power-path charger.
  - U2 SYS → U1 VDD (nRF supply, internal DC/DC)
  - U2 SYS → U3 VIN (panel load switch input)
  - U2 SYS → C_BULK+ (220 uF bulk near the panel)
- **V3V3_PANEL**: gated 3.3 V panel rail.
  - U3 VOUT → U4 VIN
  - U4 VOUT → DS1 VDD/VDDIO and the FPC reservoir caps
- **VIN_QI**: rectified output of the Qi receiver.
  - U5 (BQ51013B) RECT/OUT → U2 IN (charger input)
- **GND**: common ground for all parts, the coil shield, and the antenna
  keep-out reference plane.

## Charger and sensing

- U2 (BQ25100) ISET → R_ISET → GND (set 50 to 90 mA)
- U2 CHG (open drain) → CHG_STAT (P0.05), pulled up to VSYS
- VBAT → R_div_top → VBAT_SENSE (P0.03/AIN1) → R_div_bot → GND
- NTC (RT1) → NTC_SENSE (P0.04/AIN2) with its bias resistor to VSYS; also feeds
  U2 TS for charge thermal cutoff

## Wireless power

- L_RX (MagSafe-profile coil) → U5 AC1/AC2
- U5 series/shunt resonant caps per BQ51013B reference
- Ferrite shield between L_RX and the ground plane

## Panel (SPI + control)

- PANEL_SCLK (P0.14) → DS1 SCK
- PANEL_MOSI (P0.13) → DS1 SDI
- PANEL_CS (P0.12) → DS1 CS#
- PANEL_DC (P0.11) → DS1 D/C#
- PANEL_RST (P0.08) → DS1 RST#
- PANEL_BUSY (P0.07) ← DS1 BUSY
- PANEL_PWR_EN (P0.06) → U3 ON
- DS1 charge-pump caps on the FPC pins (VGL, VGH, VSH, VSL, VCOM) per the panel
  datasheet

## Radio, timing, NFC, debug

- U1 antenna pin → matching network → ANT (module integrates this on MDBT42Q)
- LFXO (Y1 32.768 kHz) → XL1 (P0.00), XL2 (P0.01)
- NFC1 (P0.09), NFC2 (P0.10) → ANT1 (2-turn tap-to-pair antenna, optional)
- SWDIO, SWDCLK, GND, VSYS → TP1 test pads (factory flash and recovery)

## Decoupling

- U1: 100 nF + 1 uF at VDD, plus the DC/DC inductor and caps per the Nordic
  reference
- U2, U3, U4, U5: input/output caps per each datasheet
- C_BULK: 220 uF across VSYS/GND next to the panel connector to absorb refresh
  inrush from the high-ESR cell
