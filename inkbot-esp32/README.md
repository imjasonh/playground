# inkbot-esp32

Minimal Arduino/PlatformIO firmware for the **Waveshare e-Paper ESP32 Driver
Board** + **7.5″ 800×480 mono** panel. It joins Wi-Fi, polls
`{INKBOT_BASE_URL}/image.png` every minute with `If-None-Match`, and full-refreshes
the panel when the Worker publishes a new frame.

No OTA, no SSH, no provisioning tool — copy a config header and flash.

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

## Build & flash

Install [PlatformIO](https://platformio.org/) (CLI or VS Code extension), then:

```bash
cd inkbot-esp32
cp include/config.h.example include/config.h
$EDITOR include/config.h          # WIFI_* and INKBOT_BASE_URL

pio run -t upload                # build + flash
pio device monitor               # 115200 baud
```

`include/config.h` is gitignored so credentials stay local.

## Behaviour

1. Connect to Wi-Fi.
2. Show a short “inkbot ready” splash.
3. `GET /image.png` with `If-None-Match` from NVS.
4. On `200`: decode PNG (must be 800×480), write the 1-bit buffer, full refresh, store new ETag.
5. On `304`: do nothing.
6. Sleep in a `delay(60000)` loop and repeat.

TLS uses `WiFiClientSecure::setInsecure()` for the prototype so you don’t have
to bake a CA bundle; pin a cert before any untrusted network use.

## Pair with the Worker

See [`../inkbot/`](../inkbot/) for the Cloudflare Worker, Slack `@inkbot` bot,
and `UPLOAD_SECRET` upload path.
