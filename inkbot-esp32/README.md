# inkbot-esp32

Rust / ESP-IDF firmware for the **Waveshare e-Paper ESP32 Driver Board** +
**7.5″ 800×480 mono** panel. This crate ships two binaries that share the
panel geometry:

| Binary | `make flash` | What it does |
|--------|--------------|--------------|
| `inkbot-esp32` | `APP=inkbot` (default) | Joins Wi-Fi, polls the inkbot Worker, shows frames, and polls GHCR for the image named in NVS `ota/app` |
| `maze-esp32` | `APP=maze` | Offline maze: empty grid, then a correct solve on partial refreshes. No Wi-Fi; cannot pull OTA |

The inkbot binary polls `{base_url}/` for the image catalog every minute, shows
new uploads immediately, and every `rotate_secs` (default 30 min) picks a random
frame from the library. Frames are fetched as raw `/{name}.bin` packed buffers
(no on-device zlib).

Wi-Fi, Worker, Sigstore trust, and optional GCP credentials live in NVS
(not in the ELF). After a one-time USB bootstrap, later inkbot builds can
arrive as signed GHCR images. Companion Worker:
[`../inkbot/`](../inkbot/). OTA / NVS / GCP details:
[`docs/ota.md`](docs/ota.md).

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
cargo install espup ldproxy
cargo install espflash --locked --version 4.2.2
brew install cmake ninja dfu-util cosign
espup install --targets esp32
curl -LsSf https://astral.sh/uv/install.sh | sh   # Python 3.12 for ESP-IDF
```

CI uses the same `espflash` 4.2.2 pin. On Linux, pass `PORT=/dev/ttyUSB0` or
`PORT=/dev/ttyACM0` (the Makefile also probes those paths).

## Configure, build, flash

Secrets are **not** compiled in. Copy the example, edit it, then bootstrap:

```bash
cd inkbot-esp32
cp provisioning.toml.example provisioning.toml
$EDITOR provisioning.toml    # wifi, inkbot.base_url, trust; optional [gcp] / [ota]

make build                   # first run clones ESP-IDF (~minutes)
make bootstrap PORT=/dev/cu.usbserial-XXXX   # Linux: PORT=/dev/ttyUSB0
make monitor
```

`make bootstrap` erases flash and writes the bootloader, the two-slot OTA
partition table, the inkbot app, and the NVS image. Boards that still have
the old factory-only table need this USB erase once; they cannot OTA from
the pre-OTA firmware.

`make build` compiles each app **separately** (different Cargo features and
sdkconfig trees under `target/inkbot-esp32/` and `target/maze-esp32/`). A
single `cargo build --bin inkbot-esp32 --bin maze-esp32` would compile maze
with Wi-Fi too. Each ELF must contain its baked id (`FIRMWARE_ID` in
`src/status.rs`, `MAZE_FIRMWARE_ID` in `src/maze/mod.rs`) or the Makefile
refuses to continue. `make flash` uploads the binary selected by `APP` and
always passes `partitions.csv` so espflash 4.x does not rewrite a factory-only
table. After the inkbot binary boots, `POST /device` / `@inkbot status` shows
the same `firmware=` string (`inkbot-esp32/0.4`). `make build GCP=0` compiles
GCP out of the inkbot image.

`provisioning.toml` is gitignored. `inkbot.base_url` must be `https://`.
Re-run `make provision` after you change the file (that replaces the whole
NVS partition, including runtime keys and `ota/last_digest`). `make provision`
does not rebuild firmware; run `make build` once first so ESP-IDF is present.
`make provision-build` writes `target/nvs.bin` without flashing. Maze reads
NVS only for OTA pending-verify (it ignores Wi-Fi and Worker keys).

`FIRMWARE_ID` in `src/status.rs` (`inkbot-esp32/0.4`) is the on-wire and OTA
contract. It is independent of the crate `version` in `Cargo.toml`.

To flash without erasing (app slot only) after the first bootstrap:

```bash
make flash PORT=/dev/cu.usbserial-XXXX
```

## OTA and optional GCP

On a provisioned inkbot image, the main loop polls the GHCR package for
NVS `ota/app` (default `inkbot-esp32`, repo
`ghcr.io/imjasonh/playground/{app}:latest`) every 10 minutes by default,
verifies a Cosign Sigstore bundle against the identities in NVS, writes the
inactive slot, and reboots. The new image stays pending-verify until its
health check succeeds (Worker boot fetch for inkbot; first panel paint for
maze). A failed check marks the slot invalid so the bootloader rolls back,
and the device records that digest so it does not re-download the same image.

Pushes to `main` that touch this directory publish and sign **both** packages
(`.github/workflows/inkbot-esp32-publish.yml`). Each GHCR package must be
**public** — the device pulls anonymously.

If you uncomment `[gcp]` and flash a service-account PKCS#8 PEM into NVS,
the same loop tees serial logs to Cloud Logging and posts heap / RSSI gauges
to Cloud Monitoring. There is no Google client crate on the device; JWT
RS256 uses mbedTLS. `make build GCP=0` omits that code from the ELF; omitting
`[gcp]` on a GCP-enabled image still means serial-only logs.

Set `ota.poll_secs = 0` in `provisioning.toml` if you want USB-only updates.
Set `ota.app = "maze-esp32"` to have a running inkbot pull maze. Maze cannot
pull inkbot back; use `make flash`. For the full contract, see
[`docs/ota.md`](docs/ota.md).

## Maze firmware

The maze binary does not join Wi-Fi or call a backend. Flash it (USB or an
inkbot OTA with `ota.app = "maze-esp32"`), power the board, and the panel
loops on its own:

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

`make flash` picks the first `/dev/cu.usbmodem*`, `/dev/cu.usbserial-*`,
`/dev/ttyACM*`, or `/dev/ttyUSB*` device. If more than one USB serial device
is present, pass `PORT=`.

To return to the inkbot frame loop, flash without `APP=maze`. Maze never
associates, so it avoids the Wi-Fi TX current spikes described in Power, and
it cannot pull a later image from GHCR.

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
7. Every `ota.poll_secs` (default 600, after a 30 s boot grace): poll GHCR
   for a newer signed image. Frame fetches pause while the blob downloads.

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
`inkbot-esp32/0.4`):

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

PNG decode / geometry logic and OTA encoding helpers are target-agnostic:

```bash
make test
# cargo test --lib, then provision --dry-run on provisioning.toml.example
```

CI: `.github/workflows/inkbot-esp32.yml` always runs on PRs (so it can be a
required check), then no-ops unless `inkbot-esp32/` changed; when it has work
it runs host checks plus an Xtensa `make build` of both apps (the shared
`test.yml` Rust job skips this crate — it needs espup). Pushes to `main` also
run `inkbot-esp32-publish.yml` to push and sign both GHCR images.

## Layout

```
inkbot-esp32/
├── src/
│   ├── lib.rs / panel.rs / png_frame.rs / status.rs / ota_format.rs
│   ├── maze/                         # generate / solve / render (host-tested)
│   ├── main.rs                       # inkbot: Wi-Fi + HTTP + OTA + GCP
│   ├── maze_main.rs / maze_display.rs
│   ├── display.rs                    # Waveshare 7.5″ V2 via epd-waveshare
│   └── ota.rs / ota_slot.rs / sig.rs / gcp.rs / https.rs / device_config.rs
├── tools/provision/                  # NVS image from provisioning.toml
├── tools/publisher/                  # OCI push of the firmware .bin
├── certs/                            # short HTTPS CA bundle (inkbot)
├── trust/                            # Fulcio PEMs staged into NVS
├── partitions.csv                    # two 1.9375 MiB OTA slots
├── sdkconfig.defaults.in             # inkbot: Wi-Fi, CA bundle, 48 KB stack
├── sdkconfig.defaults.maze.in        # maze: no CA bundle, smaller stack
├── provisioning.toml.example
├── docs/ota.md
└── Makefile
```
