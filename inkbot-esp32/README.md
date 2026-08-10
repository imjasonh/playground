# inkbot-esp32

Rust / ESP-IDF firmware for the **Waveshare e-Paper ESP32 Driver Board** +
**7.5″ 800×480 mono** panel. It joins Wi-Fi, polls
`{base_url}/image.bin` every minute with `If-None-Match`, and full-refreshes
the panel when the ETag changes. The Worker serves a raw packed framebuffer
so the device never runs zlib inflate (classic ESP32 heap is too fragmented
after HTTPS).

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
2. `GET /image.bin` with `If-None-Match` from NVS (boot poll before splash).
3. On `200`: body must be exactly 48 000 bytes; full refresh; store new ETag.
4. On `304` / `404`: show “inkbot ready” on first boot if nothing changed.
5. Sleep `poll_secs` (default 60) and repeat.

## Host tests

PNG decode / geometry logic is target-agnostic:

```bash
make test
# or: cargo test --lib
```

CI: `.github/workflows/inkbot-esp32.yml` runs those host checks plus an Xtensa
`make build` whenever `inkbot-esp32/` changes (the shared `test.yml` Rust job
skips this crate — it needs espup).

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
