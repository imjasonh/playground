# nRF52832 pin map

GPIO assignments for the tile. Pins are P0.xx on the nRF52832 (QFN48 / MDBT42Q).
Keep the 2.4 GHz antenna and its keep-out at the board edge farthest from the
magnet ring and the Qi coil, both of which detune the radio (see the design
doc).

| Signal | nRF pin | Direction | Net | Notes |
|--------|---------|-----------|-----|-------|
| Panel SCLK | P0.14 | out | PANEL_SCLK | SPI clock to the COG |
| Panel MOSI | P0.13 | out | PANEL_MOSI | SPI data to the COG |
| Panel CS | P0.12 | out | PANEL_CS | active low |
| Panel DC | P0.11 | out | PANEL_DC | command / data select |
| Panel RST | P0.08 | out | PANEL_RST | active low |
| Panel BUSY | P0.07 | in | PANEL_BUSY | high while refreshing |
| Panel power enable | P0.06 | out | PANEL_PWR_EN | drives the TPS22860 load switch |
| Battery sense | P0.03 / AIN1 | analog in | VBAT_SENSE | SAADC, through a divider |
| Thermistor sense | P0.04 / AIN2 | analog in | NTC_SENSE | SAADC, NTC divider |
| Charge status | P0.05 | in | CHG_STAT | BQ25100 open-drain, pulled up |
| Heartbeat LED | P0.15 | out | LED | optional, DNP by default |
| SWDIO | SWDIO | bidir | SWDIO | test pad |
| SWDCLK | SWDCLK | in | SWDCLK | test pad |
| 32.768 kHz | P0.00 / XL1 | xtal | LFXO | low-power BLE timing |
| 32.768 kHz | P0.01 / XL2 | xtal | LFXO | low-power BLE timing |
| (unused) | P0.09 / NFC1 | — | — | left free; no NFC antenna |
| (unused) | P0.10 / NFC2 | — | — | left free; no NFC antenna |

Panel SPI pins mirror the roles the [`inkbot-esp32/`](../../inkbot-esp32/) driver
uses (SCLK, MOSI, CS, DC, RST, BUSY), so the panel command sequence ports across
with only the pin numbers changed.
