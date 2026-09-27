# knob

Rust firmware for the Waveshare ESP32-S3-Knob-Touch-LCD-1.8.

The board has two MCUs. The ESP32-S3R8 owns the 360×360 round panel, the
capacitive touch pad, the single-pulse encoder, the DRV2605 haptics, the
PDM microphone, the battery divider, the TF card, and a BLE GATT server.
The ESP32-U4WDH owns Classic Bluetooth audio (A2DP sink and AVRCP) and the
PCM5100A on the 3.5 mm jack. A UART at 921600 baud joins them.

Flipping the USB-C plug selects which chip the host talks to. A later iOS
app can also push a new image over BLE. An image for the companion is
received by the S3 and forwarded over the UART into the companion's
inactive OTA slot.

## Example apps

Each app is a Cargo feature. The default S3 image includes all ten.

| Feature | Id | What it uses |
|---------|----|----------------|
| `app-dial` | `dial` | Encoder |
| `app-clock` | `clock` | Clock, after Wi-Fi SNTP |
| `app-pomodoro` | `pomodoro` | Encoder and haptics |
| `app-spectrum` | `spectrum` | PDM microphone |
| `app-tone` | `tone` | Jack, via the companion |
| `app-sketch` | `sketch` | Touch |
| `app-haptics` | `haptics` | DRV2605 |
| `app-battery` | `battery` | Battery ADC |
| `app-card` | `card` | TF card directory |
| `app-remote` | `remote` | BLE HID and the companion transport keys |

```bash
make build                  # all ten apps on the S3, plus the companion
make build APPS=clock,tone  # only those two on the S3
```

The launcher lists only the apps compiled into that image. BLE `open`
returns `missing <id>` for an app that was left out.

## Build and flash

One-time host setup:

```bash
cargo install espup espflash ldproxy
# macOS: brew install cmake ninja dfu-util
# Debian/Ubuntu: sudo apt-get install cmake ninja-build
espup install --targets esp32,esp32s3
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Then, from this directory:

```bash
make test
make flash-s3       # plug flipped toward the ESP32-S3
make flash-esp32    # plug flipped toward the ESP32
make monitor
```

The first install on a blank chip, or a chip that still has a factory
partition table, needs the bootloader and this crate's table:

```bash
make flash-all-s3
make flash-all-esp32
```

`PORT=/dev/ttyACM0` overrides the serial port. S3 logs come out of the USB
Serial/JTAG device. Companion logs come out of UART0 on the same connector
after the flip.

## BLE update

The S3 advertises as **PlaygroundKnob**. The write sequence is in
[`docs/ble.md`](docs/ble.md). Target `0` is the S3 image. Target `1` is the
companion image, which the S3 relays. After `finish`, write the reboot
opcode. The new image marks its own slot valid on the next boot. If it
never does, rollback returns to the previous slot.

## Tests

Host tests do not need the Xtensa toolchain:

```bash
make test
```

That runs the full default catalog, then the same tests with only
`app-dial` compiled in. `knob.yml` also cross-builds both chips.
