# Firmware

Bare-metal C for the STM32G071CBT6 on the 4.2 in tag. Host tests of the
mailbox framing and PBM packer do not need an ARM toolchain.

## What it does

1. Boot from harvested 3.3 V after the TCM809 releases PF2-NRST.
2. Turn on NTAG SRAM pass-through (RF toward I2C) and wait for 64-byte
   chunks on I2C address `0x55`, block `0xF8`.
3. Reassemble `EINK` + length + CRC-16 + 15 000 image bytes.
4. If `VSTORE_DIV` on PA0 is high enough, enable `+3V3_EPD` and run the
   GDEY042T81 / SSD1683 full update from GxEPD2 / Good Display.
5. Drop the panel rail and WFI. The image stays. Removing the phone
   collapses the rest.

Keep the phone on the coil for the whole transfer plus refresh (about
8 to 12 s).

## Mailbox framing

Each RF write is 64 bytes. Chunk 0 is the header:

| Bytes | Field |
| --- | --- |
| 0-3 | `EINK` |
| 4-5 | payload length, little-endian, 15000 |
| 6-7 | CRC-16-CCITT of the image bytes (`0xFFFF` start, poly `0x1021`) |

Chunks 1..234 are the image. 15008 bytes of payload plus pad is 235
chunks. `host/pack_pbm` writes that file from a 400×300 P1 or P4 PBM
(`0` black on the glass).

The phone app writes one SRAM page, waits until the tag is ready for
the next (FD or `SRAM_RF_READY` clear), and repeats. NXP's NTAG I2C
plus demo is the usual starting point. EEPROM cannot hold the frame.

## Build

```bash
cd nfc-eink/firmware
make test
make mcu   # writes nfc-eink.elf when arm-none-eabi-gcc is installed
```

Flash with an ST-Link on J2. Close JP1 only while the debugger feeds
3.3 V. Leave JP1 open for NFC power.

I2C1 is PB6/PB7. SPI1 is PA5/PA7. The MCU runs the 16 MHz HSI. Do not
clock it faster on harvest.
