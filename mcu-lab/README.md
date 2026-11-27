# xiao-esp32c3

Rust / ESP-IDF firmware for the Seeed Studio XIAO ESP32C3 (`riscv32imc-esp-espidf`)
that measures active phase durations (`sensor`, `compute`, `epd_refresh`, and
`radio`), toggles a GPIO logic-marker pin for hardware power profilers, and
broadcasts a 24-byte telemetry payload over connectionless BLE Manufacturer
Specific Data (`0xFFFF`) to the Playground iOS **XIAO ESP32C3** experiment.

The iOS experiment deduplicates advertisement bursts by sequence number,
displays a live phase-timing and energy-budget breakdown (including e-paper
partial vs. full refresh duration), and forwards OTLP/HTTP JSON metrics to a
configurable OpenTelemetry Collector endpoint.

## Wire format (BLE Manufacturer Specific Data `0xFF`)

Each wake cycle broadcasts a 31-byte legacy BLE advertising packet for 150 ms
at a 20-30 ms interval across channels 37, 38, and 39, then enters deep sleep.

| Byte offset | Size | Field | Description |
|-------------|------|-------|-------------|
| `0..2` | 2 | `company_id` | `0xFFFF` (little-endian) |
| `2` | 1 | `seq` | Monotonic wake sequence counter (`u8`, wraps at 255) |
| `3` | 1 | `flags` | Bit 0: deep-sleep wake, Bit 1: e-paper attached, Bit 2: partial e-paper refresh, Bit 3: brownout reset |
| `4..8` | 4 | `wake_count` | Cumulative wakes since cold power-on (`u32` LE, persisted in `.rtc.data`) |
| `8..12` | 4 | `sensor_us` | Sensor / ADC read + spike/EMA filter duration in microseconds (`u32` LE) |
| `12..16` | 4 | `compute_us` | Compute / 1-bit 200x200 e-paper framebuffer render duration in microseconds (`u32` LE) |
| `16..20` | 4 | `epd_refresh_us` | E-paper SPI transfer + BUSY refresh wait duration in microseconds (`u32` LE) |
| `20..24` | 4 | `radio_us` | BLE advertising burst duration from the previous wake in microseconds (`u32` LE) |
| `24..26` | 2 | `battery_mv` | Battery voltage in millivolts (`u16` LE) |

## Power profiling with a logic marker pin

Pin `GPIO2` (silkscreen `D0` on the XIAO ESP32C3) toggles `HIGH` at the start
of each measured phase (`sensor`, `compute`, `epd_refresh`, and `radio`) and
returns `LOW` when the phase finishes. Connect `D0` to a Nordic Power Profiler
Kit II (PPK2) digital logic input while powering the XIAO through its `BAT+`
and `BAT-` pads at 3.7 V to align code phases with current spikes.

## On-demand BLE GATT OTA updates from iPhone

`partitions.csv` divides the 4 MB flash into two 1.9375 MiB app slots (`ota_0`
at `0x20000` and `ota_1` at `0x210000`) with `CONFIG_BOOTLOADER_APP_ROLLBACK_ENABLE=y`.

The 150 ms BLE advertisement burst is connectable (`ConnMode::Und`) and exposes
the OTA GATT service (`4fafc301-1fb5-459e-8fcc-c5c9c331914b`):

| Role | UUID | Properties | Format |
|------|------|------------|--------|
| Service | `4fafc301-1fb5-459e-8fcc-c5c9c331914b` | — | — |
| Control | `beb5483e-36e1-4688-b7f5-ea07361bc301` | Write | `BEGIN <size> <sha256>`, `COMMIT`, `ABORT` |
| Data | `beb5483e-36e1-4688-b7f5-ea07361bc302` | Write / Write Without Response | Raw `.bin` chunks (up to 480 B) |
| Status | `1a3c0001-36e1-4688-b7f5-ea07361bc303` | Read + Notify | `IDLE`, `READY total=<n>`, `PROGRESS written=<w> total=<n>`, `OK sha256=<hex>`, `ERR <msg>` |

On normal wakes when the iPhone only listens passively, no connection occurs
and the XIAO drops back into deep sleep after 150 ms. When you stage a `.bin`
(or pull `:latest` from GHCR) and tap **Arm Update for Next Wake** in the iOS
app, the iPhone connects during the 150 ms burst, streams the image into the
inactive OTA partition, verifies the SHA-256 digest, and reboots into the new
slot. On the first wake cycle in the new slot, the firmware calls
`esp_ota_mark_app_valid_cancel_rollback()`.

## Build and flash

One-time host setup:

```bash
cargo install espup espflash ldproxy
# macOS: brew install cmake ninja dfu-util
# Debian/Ubuntu: sudo apt-get install cmake ninja-build
espup install --targets esp32,esp32c3,esp32s3
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Then:

```bash
cd mcu-lab
make test
make flash          # PORT=/dev/cu.usbmodem101 if autodetection misses the board
make monitor
```

### XIAO ESP32-S3 Sense (`recorder` + On-Device TFLite Micro)

See [`docs/xiao-esp32s3-sense.md`](docs/xiao-esp32s3-sense.md) for microSD
setup, download commands for the required pre-trained visual (`MobileNetV1`
ImageNet-1K) and audio (`YAMNet` INT8 AudioSet) `.tflite` models, supported
object/sound classes, and iOS streaming instructions.

## Tests

Host protocol and OTLP JSON tests run on standard stable Rust without the
ESP-IDF C toolchain:

```bash
cd xiao-esp32c3
make test
cargo fmt --check
cargo clippy --lib --locked -- -D warnings
```

```
xiao-esp32c3/
├── AGENTS.md
├── Makefile
├── src/lib.rs          # host-testable protocol and OTLP JSON formatter
├── src/protocol.rs
└── src/main.rs         # phase timer, RTC slow memory, GPIO probe, BLE broadcaster
```
