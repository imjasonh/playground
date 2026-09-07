# Module pin map

GPIO assignments for the tile. The MCU is a **Raytac MDBT50Q-512K** (nRF52833
module), so each signal lands on an nRF port that maps to a module pin number.
The antenna, 32 MHz crystal, and RF match are inside the module — orient the
module with its antenna end at the board edge farthest from the magnet ring and
Qi coil (both detune 2.4 GHz; see the design doc).

| Signal | nRF port | Module pin | Direction | Net | Notes |
|--------|----------|-----------|-----------|-----|-------|
| Panel SCLK | P0.11 | 27 | out | PANEL_SCLK | SPI clock to the COG |
| Panel MOSI | P0.15 | 39 | out | PANEL_MOSI | SPI data to the COG |
| Panel CS | P0.17 | 41 | out | PANEL_CS | active low |
| Panel DC | P0.20 | 44 | out | PANEL_DC | command / data select |
| Panel RST | P1.09 | 26 | out | PANEL_RST | active low |
| Panel BUSY | P0.30 | 14 | in | PANEL_BUSY | high while refreshing |
| Panel power enable | P0.31 | 12 | out | PANEL_PWR_EN | drives the TPS22810 load switch |
| Battery sense | P0.03 / AIN1 | 9 | analog in | VBAT_SENSE | SAADC, through a divider |
| Thermistor sense | P0.04 / AIN2 | 20 | analog in | NTC_SENSE | SAADC, NTC divider |
| Charge status | P0.02 / AIN0 | 11 | in | CHG_STAT | BQ51050B ~CHG open-drain, pulled up |
| SWDIO | SWDIO | 51 | bidir | SWDIO | test pad |
| SWDCLK | SWDCLK | 53 | in | SWDCLK | test pad |
| Reset | P0.18 / ~RESET | 40 | in | NRST | test pad |
| 32.768 kHz | P0.00 / XL1 | 17 | xtal | LFXO | external Y1, low-power BLE timing |
| 32.768 kHz | P0.01 / XL2 | 18 | xtal | LFXO | external Y1, low-power BLE timing |
| VDD / VDDH | VDD / VDDH | 28 / 30 | pwr | VSYS | runs off the cell |
| VBUS | VBUS | 32 | pwr | GND | USB unused, tied to GND |

The module integrates the **32 MHz HFXO**, so there is no board crystal for it;
only the 32.768 kHz LFXO (Y1) is external, on P0.00/P0.01. NFC pins P0.09/P0.10
(module pins 52/54) are left free — pairing and frames ride BLE, no NFC antenna.

Panel SPI pins mirror the roles the [`inkbot-esp32/`](../../inkbot-esp32/) driver
uses (SCLK, MOSI, CS, DC, RST, BUSY), so the panel command sequence ports across
with only the pin numbers changed.
