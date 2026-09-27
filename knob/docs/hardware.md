# Hardware

Waveshare ESP32-S3-Knob-Touch-LCD-1.8. Two MCUs, one USB-C connector.
Flipping the plug selects which MCU the host enumerates.

Pin numbers below are the net names on the Waveshare schematic. A
third-party sketch that drives the jack from the S3 uses GPIO39, GPIO40,
and GPIO41 with GPIO0 high. This firmware leaves GPIO0 low so the CH445P
selects the companion I2S trio, and it talks to that chip on GPIO38 and
GPIO48. The UART runs at 921600 8N1.

## ESP32-S3R8

16 MB flash, 8 MB octal PSRAM. USB Serial/JTAG on the native USB pins.

| Function | GPIO | Notes |
|----------|------|--------|
| I2C SDA | 11 | CST816 at `0x15`, DRV2605 at `0x5A`, 400 kHz. DRV2605 EN is tied to 3.3V. |
| I2C SCL | 12 | |
| Touch interrupt | 9 | Active low, pulled up. The driver also polls. |
| Touch reset | 10 | Active low |
| Encoder A | 8 | Falling edge while B is high is one step the other way |
| Encoder B | 7 | Falling edge while A is high is one clockwise step |
| LCD CS | 14 | ST77916, QSPI |
| LCD PCLK | 13 | |
| LCD D0, D1, D2, D3 | 15, 16, 17, 18 | |
| LCD reset | 21 | Active low |
| Backlight | 47 | LEDC PWM, 25 kHz |
| Battery ADC | 1 | Divider. Pin millivolts times 2 is the cell. |
| I2S switch | 0 | `I2S_SWITCH_IN`. Strap. Low selects the companion trio. High selects GPIO39, GPIO40, GPIO41. |
| S3 I2S BCK, WS, DOUT | 39, 40, 41 | Not driven. The switch stays on the companion. |
| Mic clock | 45 | PDM. Strap. Do not pull it at reset. |
| Mic data | 46 | PDM. Strap. |
| SD clock | 4 | SDMMC 4-bit |
| SD command | 3 | Strap |
| SD D0, D1, D2, D3 | 5, 6, 42, 2 | |
| Link TX | 38 | `ESP32S3_TX`. Toward the companion, 921600 8N1 |
| Link RX | 48 | `ESP32S3_RX`. From the companion |

Display MADCTL is `0xC0`. Touch coordinates are inverted to match that
rotation. The panel is 360 by 360.

## ESP32-U4WDH

4 MB flash. No PSRAM. Classic Bluetooth only. UART0 is the console the
USB-UART bridge exposes when the plug is flipped this way.

| Function | GPIO | Notes |
|----------|------|--------|
| Link TX | 23 | Toward the S3, 921600 8N1 |
| Link RX | 18 | From the S3 |
| Encoder A | 19 | Second encoder. Counted with the same decoder as the S3 knob. Steps go to the S3 over the UART and move the same launcher. |
| Encoder B | 22 | |
| I2S bit clock | 25 | `ESP32_I2S_DAC_BCK` |
| I2S data | 26 | `ESP32_I2S_DAC_DIN` |
| I2S word select | 27 | `ESP32_I2S_DAC_LRCK/WS` |
| DAC unmute | 32 | PCM5100A `XSMT`. High unmutes. |

The S3 does not bit-bang or clock this DAC. Tone requests and A2DP audio
are rendered here.

## Partitions

Both chips use two OTA slots and rollback. The S3 slot is 6 MB
(`0x600000`). The companion slot is 1.5 MB (`0x180000`). A BLE image
larger than the destination slot is rejected before any byte is written.
