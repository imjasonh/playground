# inkbot-esp32

Rust / ESP-IDF firmware for the **Waveshare e-Paper ESP32 Driver Board** +
**7.5″ 800×480 mono** panel. It joins Wi-Fi, polls `{base_url}/` for the image
catalog every minute, shows new uploads immediately, and every
`rotate_secs` (default 30 min) picks a random frame from the library. Frames
are fetched as raw `/{name}.bin` packed buffers (no on-device zlib).

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

### Power

Wi-Fi association draws brief ~300 mA spikes. A laptop USB port usually handles
that; many wall chargers / thin cables sag and the board shows `WiFi: connect`
(or reboots with `reset_reason=BROWNOUT`). Use a solid **5 V / ≥1 A** supply and
a short data-capable cable. Firmware retries association several times and caps
TX power to ease weak supplies.

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
2. Boot: `GET /`, then paint `latest` (full refresh).
3. Every `poll_secs` (default 60): refresh catalog; if `latest` changed, show it.
4. Every `rotate_secs` (default 1800): show a random other image.
5. Empty catalog → “inkbot ready”.

## Host tests

PNG decode / geometry logic is target-agnostic:

```bash
make test
# or: cargo test --lib
```

CI: `.github/workflows/inkbot-esp32.yml` always runs on PRs (so it can be a
required check), then no-ops unless `inkbot-esp32/` changed; when it has work
it runs host checks plus an Xtensa `make build` (the shared `test.yml` Rust
job skips this crate — it needs espup).

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
