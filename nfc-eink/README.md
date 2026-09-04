# NFC batteryless e-ink tag

A phone field powers this board. There is no battery. The MCU boots, pulls a
1-bit image out of the tag over I2C, paints a 4.2 in panel, and dies when you
take the phone away.

I sized this for the largest panel I trust on harvested NFC: Good Display
GDEY042T81 (400×300, 91 mm × 77 mm). Commercial batteryless NFC e-paper stops
around this diagonal. A 7.5 in 800×480 frame is 48 KB and a long refresh. The
field cannot cover that without a hold-up cap that takes too long to charge.

The board outline matches the panel. Route the antenna in the bezel on the
front. Put the electronics on the back.

## Recommended design

| Role | Part | Why |
| --- | --- | --- |
| NFC + harvest | NXP NT3H2211W0FTTJ | ISO 14443-A. Faster than ST25DV (ISO 15693). About 15 mW in a strong phone field. 2 KB EEPROM, so the image must stream through the 64-byte SRAM mailbox. |
| MCU | STM32G071CBT6 | 36 KB RAM holds the 15 000-byte frame plus stack. HSI, no crystal. |
| Boost | TPS61023DRLR | Starts at 0.5 V. 3.29 V from 453 k / 100 k on FB. |
| EPD switch | TPS22917DBVR | Panel stays off until the tank and image are ready. |
| Reset | TCM809SENB713 | 2.93 V, active-low. Holds PF2-NRST until the boost is up. Do not use the J suffix (4.00 V). That part never releases on a 3.3 V rail. |
| Panel | GDEY042T81 | SSD1683, 24-pin 0.5 mm FPC, on-glass booster. Typical refresh about 5.6 mA at 3.0 V for about 3 s. |

Open `nfc-eink.kicad_pro` in KiCad 7. Sheets: cover, NFC, power, MCU, e-paper.
`nfc-eink.pdf` is the same schematic plotted.

## How a session runs

1. Place the phone on the bezel coil. Keep it there until the panel finishes.
2. NT3H2211 VOUT charges C2 (470 µF) through D1 and R1 (22 Ω). C1 on VOUT is
   220 nF. NXP caps that pin at 220 nF. Do not add bulk there.
3. TPS61023 starts near 0.5 V and regulates 3.29 V.
4. TCM809 releases PF2-NRST (LQFP48 pin 10). The G071 has no dedicated NRST pin
   on this package.
5. Firmware enables harvest in the tag config if it is not already on, then
   drains the SRAM mailbox over I2C1 (PB6/PB7).
6. When the 15 000-byte frame is in RAM and `VSTORE_DIV` looks healthy, the MCU
   asserts `EPD_PWR_EN`, talks 4-wire SPI to the SSD1683, and waits on BUSY.
7. The MCU drops the EPD rail and waits in WFI. Remove the phone and the rails
   collapse. The image stays.

ISO 14443-A through the mailbox is about 40 kbit/s in practice, so the frame
takes about 3 s. Refresh is another 3 s. Budget 8 to 12 s of coupling.

## Power budget

Phone harvest is 15 to 20 mW when the coil is well coupled (NXP NTAG I2C plus
app note, ST AN4913 on ST25DV). That is the whole supply.

| Load | Draw | Notes |
| --- | --- | --- |
| STM32G071 at 16 MHz HSI | about 3 to 5 mA | Run slow. 64 MHz wastes harvest. |
| GDEY042T81 refresh | about 5.6 mA at 3.0 V, 3 s | Good Display typical. Peaks are higher when the glass DC-DC starts. |
| NTAG I2C + boost losses | 1 to 3 mA | Continuous while the field is present. |

C2 at 2 V stores about 1 mJ. That is a dip absorber, not the refresh energy.
The phone must stay on the coil. C3 (22 mF, DNP) is there if you want more
hold-up. It also adds several seconds of charge time.

R1 is 22 Ω so a 10 mA harvest current only drops 0.22 V into the tank. 470 Ω
would isolate VOUT from the empty cap, and it would also starve the boost once
the MCU and panel start drawing. 22 Ω is the compromise: short inrush, then
the field can keep feeding VSTORE.

## Alternate designs

These get close to the same goals. I would not schematic them first.

| Design | Display | Reliability | Transfer | Board size | Notes |
| --- | --- | --- | --- | --- | --- |
| **This schematic** | 4.2 in 400×300 | High if the phone stays put | Fastest ISO 14443-A mailbox | 91 × 77 mm | Recommended. |
| ST25DV64KC, same MCU and power | 4.2 in | Similar harvest, sometimes a bit more | Slower ISO 15693 | Same | 8 KB EEPROM is still too small for the frame. You still stream. |
| Good Display NFC-D4-042 (FM1280) | 4.2 in | High on supported phones | Module-defined | Module-sized | Buy it if you want a known-good radio. The IC is not on DigiKey. The app is theirs. Phone coverage is uneven. |
| Same board, GDEY0213B74 | 2.13 in 250×122 | Highest | Fast (about 4 KB) | Smaller than 4.2 in | Best if you care more about first-try success than pixels. |
| STM32G0B1 + 0.047 F + 5.83 in | 5.83 in 648×480 | Low | 39 KB, long hold | Larger than I want | 15 to 30 s on the coil. Brownouts are common. |
| 7.5 in 800×480 | 7.5 in | Poor | 48 KB | Panel-sized | I would not ship this batteryless. Use a coin cell or keep inkbot's USB path. |
| ams AS3956 Type 4 | 4.2 in | High | Type 4, you write the app | Same | Regulated harvest, nicer analog, more money, harder phone code. |
| Infineon NGC1081 | any | n/a | n/a | n/a | End of life. Skip it. |
| STM32U031 in place of G071 | 2.13 in only | High on small glass | Fine | Smaller | 12 KB RAM cannot hold a 4.2 in frame. |

If two rows look tied, pick this schematic or the 2.13 in variant. The FM1280
module is the "I do not want to tune an antenna" option.

## Schematic and BOM

| File | What it is |
| --- | --- |
| `nfc-eink.kicad_pro` | KiCad 7 project |
| `nfc-eink.kicad_sch` | Cover sheet with the four children |
| `nfc.kicad_sch` | Antenna, NT3H2211, 220 nF on VOUT |
| `pwr.kicad_sch` | Diode, tank, boost, EPD load switch, reset |
| `mcu.kicad_sch` | STM32G071, SWD, UART, I2C pull-ups |
| `epd.kicad_sch` | FH12-24S, SSD1683 host caps, 2N7002 booster FET |
| `nfc-eink.pdf` | Plotted schematic |
| `bom.csv` | Qty-1 USD and buy links, dated 2026-09-04 |

`tools/gen_schematic.py` rebuilds the `.kicad_sch` files. Run it only when you
change the generator. Then run ERC again.

### Validate

KiCad 7 has no `kicad-cli sch erc`. `tools/erc.py` exports a netlist and checks
that every required pin sits on the net we designed.

```bash
# Debian/Ubuntu
sudo apt-get install -y kicad
bash nfc-eink/tools/validate.sh
```

The checker allows no-connects on unused G071 GPIO and on EPD pins 1, 4, 6, 7,
and 19. Anything else unconnected fails the run.

## MCU map

| Net | G071 pin | Ball |
| --- | --- | --- |
| NRST | 10 | PF2-NRST |
| VSTORE_DIV | 11 | PA0 (ADC) |
| DBG_TX / DBG_RX | 13 / 14 | PA2 / PA3 |
| EPD_CS / SCK / BUSY / MOSI | 15 / 16 / 17 / 18 | PA4 / PA5 / PA6 / PA7 |
| EPD_PWR_EN | 19 | PB0 |
| EPD_DC | 28 | PA8 |
| SWDIO / SWCLK | 35 / 36 | PA13 / PA14 |
| EPD_RST | 37 | PA15 |
| NFC_FD | 44 | PB5 |
| I2C_SCL / I2C_SDA | 45 / 46 | PB6 / PB7 |
| VBAT, VREF+, VDD | 4, 5, 6 | tie to +3V3 |
| VSS | 7 | GND |

J2 is 1.27 mm, 3V3 / SWDIO / SWCLK / NRST / GND. Close JP1 only when an
ST-Link feeds J2 pin 1. Leave it open for NFC power.

## Antenna and layout

Target L is 2.76 µH with the chip's 50 pF:

`L = 1 / (4π² f² C)` at 13.56 MHz.

Use a 2-turn Class-1 loop in the 91 mm × 77 mm bezel. 0.5 mm trace, 0.5 mm
gap, no copper pour in the keepout, no ground under the turns. CT1 / CT2 are
NP0 pads. Leave them DNP until a VNA or a phone-range sweep says you need
15 pF or 27 pF.

Keep D1, R1, and C2 tight to U1. Keep L1, C5, and C6 tight to U2. The FPC
connector sits on the long edge of the panel.

## Firmware outline

This tree is hardware only. A first image path looks like this:

1. Program the tag once under field (or with JP1 closed) so energy harvest is
   enabled and the SRAM mailbox is in pass-through.
2. Poll FD or the session register. Read 64-byte chunks on I2C address 0x55.
   ACK each chunk so the phone can write the next.
3. Pack bits into a 400×300 SSD1683 buffer (15000 bytes).
4. Read PA0. If the divider says VSTORE is high enough, set PB0 and run the
   Good Display / SSD1683 full-update sequence.
5. Clear PB0. WFI.

The sender is a small Android or iOS app that writes the mailbox. NXP's
NTAG I2C plus demo is the usual starting point. You cannot dump the whole
frame into EEPROM. There is not enough of it.

## What is not in this tree

No PCB layout. No firmware. No phone app. The schematic, netlist check, BOM,
and the size/power argument are the deliverable.

Parts total about $35 to $40 in qty 1, and most of that is the panel.
