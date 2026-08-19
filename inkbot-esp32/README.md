# inkbot-esp32

Rust / ESP-IDF firmware for the **Waveshare e-Paper ESP32 Driver Board** +
**7.5″ 800×480 mono** panel. This crate ships two binaries that share the
panel geometry:

| Binary | `make flash` | What it does |
|--------|--------------|--------------|
| `inkbot-esp32` | `APP=inkbot` (default) | Joins Wi-Fi, polls the inkbot Worker, shows frames |
| `maze-esp32` | `APP=maze` | Offline maze: empty grid, then a correct solve on partial refreshes |

The inkbot binary polls `{base_url}/` for the image catalog every minute, shows
new uploads immediately, and every `rotate_secs` (default 30 min) picks a random
frame from the library. Frames are fetched as raw `/{name}.bin` packed buffers
(no on-device zlib).

No OTA, no SSH. Companion Worker for the inkbot binary:
[`../inkbot/`](../inkbot/).

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

`make build` always compiles both ELFs under `inkbot-esp32/target/` (it ignores
an inherited `CARGO_TARGET_DIR`) and refuses to continue unless each ELF
contains its baked id (`FIRMWARE_ID` in `src/status.rs`, `MAZE_FIRMWARE_ID` in
`src/maze/mod.rs`). `make flash` uploads the binary selected by `APP`. After
the inkbot binary boots, `POST /device` / `@inkbot status` shows the same
`firmware=` string.

`config.toml` is gitignored. The inkbot binary bakes those values in at
compile time via `build.rs`. The maze binary does not read them.

## Maze firmware

The maze binary does not join Wi-Fi or call a backend. Flash it, power the
board, and the panel loops on its own:

1. Full-refresh an empty 40×24 perfect maze (start and end marked).
2. Partial-refresh the unique solution path (never a search or a dead end).
   Pacing is two independent knobs in `src/maze/mod.rs`: `CELLS_PER_TICK`
   (default 1) and `TICK_MS` (default 5000). Set them to `10` and `1000` to
   advance 10 cells every second.
3. Hold the completed maze for 8 seconds, then generate another.

Generation, solving, and pixel drawing are separate modules under
`src/maze/` so you can swap any one later. Host tests cover those stages
without the ESP toolchain.

To put the maze firmware on the panel:

```bash
cd inkbot-esp32
make flash APP=maze
make monitor
```

`make flash` picks the first `/dev/cu.usbmodem*` or `/dev/cu.usbserial-*`
device. If more than one USB serial device is present, pass `PORT=`.

To return to the inkbot frame loop, flash without `APP=maze`. A USB-only
supply is enough here: the maze binary never associates, so it avoids the
Wi-Fi TX current spikes described in Power.

## Behaviour

1. Bring up the panel + Wi-Fi.
2. Boot: `GET /latest.bin`, then paint `latest` (full refresh).
3. Every `poll_secs` (default 60): refresh catalog; if `latest` changed, show it.
4. Every `rotate_secs` (default 1800): show a random other image.
5. Empty catalog → blank white panel (no banner).
6. Every `dhcp_renew_secs` (default 6 h): re-run DHCP while staying associated.
   `ESP_ERR_HTTP_CONNECT` (or a dropped STA) triggers a full re-associate and
   one immediate catalog retry, so a desk frame can stay up without a power
   cycle if lwIP’s automatic lease renew stalls.

### Error status line

The panel is the on-device debug surface. On **error only**, a white
bar is painted over the bottom ~1–3 rows of 6×10 text (the rest of the image
is left alone). When the device is healthy the bar is not drawn — there is no
“no errors” / “ready” message, because that would steal image pixels.

The bar can include:

| Kind | What you get |
|------|----------------|
| Wi-Fi | `step=` (configure/start/connect/dhcp), `ssid=`, `try=n/n`, `2.4GHz` reminder, disconnect reason if known, ESP error chain, heap |
| Fetch | `catalog` / `frame <name>` / `boot /latest.bin`, URL path, HTTP status, bytes read so far, IP, attempt count, error chain, heap |
| Crash | `esp_reset_reason` name+code (`PANIC`, `BROWNOUT`, `TASK_WDT`, …), last operation (NVS + RTC), panic payload `@file:line` if a panic hook ran, heap at boot |

Heap fields are `heap=` free bytes, `min=` lifetime minimum, `big=` largest
contiguous 8-bit block — `big<48000` is why a framebuffer alloc failed.

A crash line stays on the first image after reboot for one poll period, then
the next refresh is a full frame. Wi-Fi failure retries forever and keeps the
bar up until association succeeds.

Brownout still usually means a weak 5 V supply (see Power above).

### Remote status (`POST /device`)

When `inkbot.upload_secret` matches the Worker's `UPLOAD_SECRET`, the firmware
POSTs JSON telemetry to `{base_url}/device` (`User-Agent` / `firmware` =
`inkbot-esp32/0.2`):

- once after boot (Wi-Fi is up; SNTP is started first so `unix_secs` can fill in)
- whenever the on-panel error text changes
- after a DHCP renew or STA reconnect (so a new `ip` / `rssi` lands quickly)
- when a FETCH/WIFI incident is still unposted (NVS-backed; USB reset does
  not drop it)
- otherwise every `status_secs` (default 15 min)

A CONNECT failure is snapshotted *before* reconnect. The overlay is cleared if
the retry works, but `last_incident` (kind, uptime, unix time, ip, rssi,
gateway, error text) is POSTed as soon as HTTPS succeeds. Reports also include
`gateway`, `dns`, `last_ok_uptime_secs` / `last_ok_op`, and DHCP/reconnect
counters.

Empty `upload_secret` disables posting. Fetch the last report (and recent
history) with:

```bash
curl -H "Authorization: Bearer $UPLOAD_SECRET" https://inkbot.<account>.workers.dev/device
```

or mention `@inkbot status` in Slack.

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
│   ├── lib.rs / panel.rs / png_frame.rs / status.rs  # host-tested
│   ├── maze/                                         # generate / solve / render (host-tested)
│   ├── main.rs                                       # inkbot: Wi-Fi + HTTP poll loop
│   ├── maze_main.rs / maze_display.rs                # maze: offline panel loop
│   └── display.rs                                    # inkbot: Waveshare 7.5″ V2 via epd-waveshare
├── config.toml.example
├── sdkconfig.defaults
└── Makefile
```
