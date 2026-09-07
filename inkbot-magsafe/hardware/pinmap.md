# nRF52833 pin map

GPIO assignments for the tile. Pins are on the nRF52833 in the QFN-40 (QDAA)
package. Keep the 2.4 GHz antenna and its keep-out at the board edge farthest
from the magnet ring and the Qi coil, both of which detune the radio (see the
design doc).

| Signal | nRF pin | Direction | Net | Notes |
|--------|---------|-----------|-----|-------|
| Panel SCLK | P0.11 | out | PANEL_SCLK | SPI clock to the COG |
| Panel MOSI | P0.15 | out | PANEL_MOSI | SPI data to the COG |
| Panel CS | P0.17 | out | PANEL_CS | active low |
| Panel DC | P0.20 | out | PANEL_DC | command / data select |
| Panel RST | P1.09 | out | PANEL_RST | active low |
| Panel BUSY | P0.30 / AIN6 | in | PANEL_BUSY | high while refreshing |
| Panel power enable | P0.31 / AIN7 | out | PANEL_PWR_EN | drives the TPS22810 load switch |
| Battery sense | P0.03 / AIN1 | analog in | VBAT_SENSE | SAADC, through a divider |
| Thermistor sense | P0.04 / AIN2 | analog in | NTC_SENSE | SAADC, NTC divider |
| Charge status | P0.02 / AIN0 | in | CHG_STAT | BQ51050B ~CHG open-drain, pulled up |
| SWDIO | SWDIO | bidir | SWDIO | test pad |
| SWDCLK | SWDCLK | in | SWDCLK | test pad |
| Reset | P0.18 / ~RESET | in | NRST | test pad |
| 32.768 kHz | P0.00 / XL1 | xtal | LFXO | low-power BLE timing |
| 32.768 kHz | P0.01 / XL2 | xtal | LFXO | low-power BLE timing |
| 32 MHz | XC1 / XC2 | xtal | HFXO | radio reference |
| (unused) | P0.09 / NFC1 | — | — | left free; no NFC antenna |
| (unused) | P0.10 / NFC2 | — | — | left free; no NFC antenna |

Panel SPI pins mirror the roles the [`inkbot-esp32/`](../../inkbot-esp32/) driver
uses (SCLK, MOSI, CS, DC, RST, BUSY), so the panel command sequence ports across
with only the pin numbers changed. The QFN-40 package has fewer GPIO than the
old QFN-48; the analog-capable pins double as digital where needed.
