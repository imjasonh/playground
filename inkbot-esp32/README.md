# inkbot-esp32

Rust / ESP-IDF firmware for the **Waveshare e-Paper ESP32 Driver Board** +
**7.5″ 800×480 mono** panel. It joins Wi-Fi, polls
`{base_url}/image.png` every minute with `If-None-Match`, decodes the Worker's
packed 1-bit PNG, and full-refreshes the panel when the ETag changes.

No OTA, no SSH — just the frame loop. Companion Worker: [`../inkbot/`](../inkbot/).

## Hardware

| Piece | Notes |
|-------|-------|
| Waveshare e-Paper ESP32 Driver Board | SKU 15823 / Amazon B07M5CNP3B |
| Waveshare 7.5″ raw mono 800×480 | V2 / UC8179 (SKU 13187) |
| USB cable + 5 V supply | |

Fixed board wiring (no jumper wires):

| Signal | GPIO |
|--------|-----:|
| SCLK | 13 |
| MOSI | 14 |
| CS | 15 |
| DC | 27 |
| RST | 26 |
| BUSY | 25 |

Set the driver-board resistor switch to the **0.47 Ω** path for the 7.5″ panel
(usually labeled `B` on current boards).

## One-time host setup (macOS)

```bash
cargo install espup espflash ldproxy
brew install cmake ninja dfu-util
espup install --targets esp32
curl -LsSf https://astral.sh/uv/install.sh | sh   # Python 3.12 for ESP-IDF
```

## Configure, build, flash

```bash
cd inkbot-esp32
cp config.toml.example config.toml
$EDITOR config.toml          # wifi.ssid / wifi.pass / inkbot.base_url

make build                   # first run clones ESP-IDF (~minutes)
make flash PORT=/dev/cu.usbserial-XXXX
make monitor
# or: make run
```

`config.toml` is gitignored. Values are baked in at compile time via `build.rs`.

## Behaviour

1. Bring up the panel + Wi-Fi.
2. Show a short “inkbot ready” splash.
3. `GET /image.png` with `If-None-Match` from NVS.
4. On `200`: decode PNG (must be 800×480 B/W), full refresh, store new ETag.
5. On `304` / `404`: do nothing.
6. Sleep `poll_secs` (default 60) and repeat.

## Host tests

PNG decode / geometry logic is target-agnostic:

```bash
make test
# or: cargo test --lib
```

Cross-builds need the espup toolchain and are not run by the shared `test.yml`
job (see root `AGENTS.md`).

## Layout

```
inkbot-esp32/
├── src/
│   ├── lib.rs / panel.rs / png_frame.rs   # host-tested
│   ├── main.rs                            # Wi-Fi + HTTP poll loop
│   └── display.rs                         # Waveshare 7.5″ V2 via epd-waveshare
├── config.toml.example
├── sdkconfig.defaults
└── Makefile
```
