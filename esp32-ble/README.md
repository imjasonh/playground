# esp32-ble

Rust firmware for a classic ESP32 that speaks Bluetooth Low Energy to the
Playground iOS **ESP32 BLE** experiment.

The board advertises as **PlaygroundBLE**, accepts text commands on one
characteristic, and notifies a status line on another. The onboard LED
(GPIO 2 on most DevKitC boards) turns on, off, or blinks.

This is USB-flash only. There is no Wi-Fi, NVS provisioning, or OTA path.

## GATT

| Role | UUID |
|------|------|
| Service | `4fafc201-1fb5-459e-8fcc-c5c9c331914b` |
| Command (write) | `beb5483e-36e1-4688-b7f5-ea07361b26a6` |
| Status (read + notify) | `1a3c0001-36e1-4688-b7f5-ea07361b26a6` |

Commands are UTF-8, case-insensitive:

| Write | Effect |
|-------|--------|
| `led on` or `on` | LED on, blink cancelled |
| `led off` or `off` | LED off, blink cancelled |
| `blink 1` / `blink 1s` / `blink every 1s` | Full on+off period of 1 second |
| `blink 0.5` or `blink 500ms` | Period of 500 ms |
| `stop` | Cancel blink, leave the LED as it is |

Status is one line, notified about twice a second:

```
led=on blink_ms=1000 uptime_s=12 heap=185432 last=blink 1
```

`led` is the physical pin level, so it toggles while blinking. `blink_ms` is
`0` when the LED is held steady.

## Build and flash

One-time host setup (same tools as [`inkbot-esp32`](../inkbot-esp32/)):

```bash
cargo install espup espflash ldproxy
# macOS: brew install cmake ninja dfu-util
# Debian/Ubuntu: sudo apt-get install cmake ninja-build
espup install --targets esp32
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Then:

```bash
cd esp32-ble
make test
make flash          # PORT=/dev/ttyUSB0 if autodetection misses the board
make monitor
```

`make flash` builds the release ELF with `cargo +esp` and writes the app
partition over USB. If this board previously ran `inkbot-esp32`, that image
uses OTA slots at different offsets, so the first install must be:

```bash
make flash-all
```

That erases flash and writes this crate's bootloader plus a factory partition
table. After reset, nRF Connect lists **PlaygroundBLE** and the two
characteristics. The LED on GPIO 2 blinks every 1 s until you send a command.
The iOS experiment scans for the service UUID. Restoring inkbot later is
`cd ../inkbot-esp32 && make bootstrap`.

If the LED does not light, your board may use a different pin or an
active-low LED. Edit `gpio2` and `LED_ACTIVE_HIGH` in `src/main.rs`.

## Tests

Host protocol tests do not need the Xtensa toolchain:

```bash
cd esp32-ble
make test
cargo fmt --check
cargo clippy --lib --locked -- -D warnings
```

CI: `.github/workflows/esp32-ble.yml` runs those host checks and a firmware
cross-build when this directory changes.

```
esp32-ble/
├── AGENTS.md
├── Makefile
├── src/lib.rs          # host-testable protocol
├── src/protocol.rs
└── src/main.rs         # GATT server + GPIO (feature firmware)
```
