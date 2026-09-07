# Module pin map

GPIO assignments for the tile. The MCU is a **Raytac MDBT50Q-1MV2** (nRF52840
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
| Panel power enable | P0.31 | 12 | out | PANEL_PWR_EN | TPS7A20's 500 kOhm smart pull-down holds EN low during reset |
| Qi power present | P0.19 | 8 | in | QI_PRESENT | BQ51013C CHG open-drain; enable internal pull-up |
| Qi enable 1 | P0.03 / AIN1 | 9 | out | QI_EN1 | drive high with QI_EN2 to send charge-complete EPT |
| Qi enable 2 | P1.08 | 25 | out | QI_EN2 | drive high with QI_EN1 to send charge-complete EPT |
| Charger interrupt | P0.04 / AIN2 | 20 | in | CHG_INT_N | BQ25186 open-drain interrupt; enable internal pull-up |
| Charger power good | P0.05 / AIN3 | 21 | in | CHG_PG_N | BQ25186 open-drain power-good; enable internal pull-up |
| Charge enable | P0.06 | 22 | out | CHG_ENABLE | drives Q2; charging defaults off until configuration succeeds |
| Charger SDA | P0.07 | 23 | bidir | CHG_SDA | BQ25186 I2C, 10 kOhm pull-up to MCU_3V0 |
| Charger SCL | P0.08 | 24 | out | CHG_SCL | BQ25186 I2C, 10 kOhm pull-up to MCU_3V0 |
| Battery/SYS sense | P0.29 / AIN5 | 10 | analog in | SYS_SENSE | 1 MOhm/330 kOhm divider with 10 nF filter |
| Panel temperature excitation | P0.27 | 16 | out | PANEL_TEMP_EXCITE | drive high only while sampling |
| Panel temperature sense | P0.02 / AIN0 | 11 | analog in | PANEL_TEMP_SENSE | ratiometric 10 kOhm divider; use VDD/4 reference and 1/4 gain |
| SWDIO | SWDIO | 51 | bidir | SWDIO | test pad |
| SWDCLK | SWDCLK | 53 | in | SWDCLK | test pad |
| Reset | P0.18 / ~RESET | 40 | in | NRST | test pad |
| 32.768 kHz | P0.00 / XL1 | 17 | xtal | LFXO | external Y1, low-power BLE timing |
| 32.768 kHz | P0.01 / XL2 | 18 | xtal | LFXO | external Y1, low-power BLE timing |
| VDD | VDD | 28 | pwr in | MCU_3V0 | tied to VDDH for normal-voltage mode |
| VDDH | VDDH | 30 | pwr in | MCU_3V0 | tied to VDD and powered by TPS7A0230P |
| VBUS | VBUS | 32 | pwr | GND | USB-disabled reference connection |

The module integrates the **32 MHz HFXO**, so there is no board crystal for it;
only the 32.768 kHz LFXO (Y1) is external, on P0.00/P0.01. NFC pins P0.09/P0.10
(module pins 52/54) are left free — pairing and frames ride BLE, no NFC antenna.
The unused USB D+ and D- pins remain open; `VBUS` connects to ground.

Panel SPI pins mirror the roles the [`inkbot-esp32/`](../../inkbot-esp32/) driver
uses (SCLK, MOSI, CS, DC, RST, BUSY), so the panel command sequence ports across
with only the pin numbers changed.

The open-drain Qi and charger status pins use the nRF52840's internal pull-ups.
Do not pull them up to `SYS`, which can reach 4.5 V.
