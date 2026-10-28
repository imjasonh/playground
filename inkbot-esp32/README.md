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
cargo install espflash --locked --version 4.5.0
brew install cmake ninja dfu-util cosign
espup install --targets esp32
curl -LsSf https://astral.sh/uv/install.sh | sh   # Python 3.12 for ESP-IDF
```

CI uses the same `espflash` 4.5.0 pin. On Linux, pass `PORT=/dev/ttyUSB0` or
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
the same `firmware=` string (`inkbot-esp32/0.6`). `make build GCP=0` compiles
GCP out of the inkbot image.

`provisioning.toml` is gitignored. `inkbot.base_url` must be `https://`.
Re-run `make provision` after you change the file (that replaces the whole
NVS partition, including runtime keys and `ota/last_digest`). `make provision`
does not rebuild firmware; run `make build` once first so ESP-IDF is present.
`make provision-build` writes `target/nvs.bin` without flashing. Maze reads
NVS only for OTA pending-verify (it ignores Wi-Fi and Worker keys).

`FIRMWARE_ID` in `src/status.rs` (`inkbot-esp32/0.6`) is the on-wire and OTA
contract. It is independent of the crate `version` in `Cargo.toml`.

To flash without erasing (app slot only) after the first bootstrap:

```bash
make flash PORT=/dev/cu.usbserial-XXXX
```

From Chrome or Edge you can do the same write without `espflash`: open
[`esp-flash/`](../esp-flash/) (Pages or `npm start` in that directory), load
`inkbot-esp32:latest` or `maze-esp32:latest`, and connect the board over USB.
If the e-ink panel still shows the old picture, tap **RESET** without holding
**BOOT**. E-ink keeps the last picture until the new firmware paints.

## OTA and optional GCP

On a provisioned inkbot image, the main loop polls the GHCR package for
NVS `ota/app` (default `inkbot-esp32`, repo
`ghcr.io/imjasonh/playground/{app}:latest`) every 10 minutes by default,
verifies the Cosign signature against the identities in NVS, writes the
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
`inkbot-esp32/0.6`):

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

## Grayscale video demo (experimental)

`grayscale-esp32` is a separate experimental firmware from `maze-esp32`.
It does not show the maze. It plays 36 boids
([Reynolds' separation, alignment, and cohesion](https://www.red3d.com/cwr/boids/))
drawn as acute triangles that point in each boid's direction of travel.
The flock is the scene the drive loop refreshes as fast as the panel
allows. It is USB-flash only: no Wi-Fi, no OTA pull, and not in the
`inkbot` / `maze` OTA app registry.

Each refresh can darken or lighten a pixel by only one step of a 30-step
swing, so the flock's speed and triangle size are tuned together: a
9-logical-pixel-long triangle moving 0.29 logical pixels per refresh
(about 13 panel pixels a second at 22 refreshes a second) keeps a point
on its central axis covered for one full swing before the shape
moves past. A boid crosses the 800-pixel width in about 63 seconds.
Faster motion without a longer triangle leaves a pale streak instead of
a solid shape.

They start as three separate flocks of twelve, spread left, center, and
right across the panel, each on its own heading within about 20 degrees
of itself. Separation is 10 logical pixels, about one arrow length, so
boids within a flock can fly close enough to read as one group. The three
starting flocks aren't kept apart: perception reaches most of the panel,
so alignment and cohesion pull them into one flock within the first
10-15 seconds. Each boid also gets a small random steering nudge every
refresh, independent of its neighbors, so alignment pulls headings
together without ever locking them onto the exact same direction.

Boids steer away from the panel edges with a force that grows with the
square of how far into the margin they've come, so they stay gentle in
open water and turn sharply only right at the wall. That keeps the flock
from lining up along an edge instead of turning back toward the middle.

Instead of one multi-second factory waveform per image, it loads a custom
waveform that drives a pixel for one controller frame per refresh, toward
black, toward white, or not at all. Gray levels come from how many net
steps a pixel has had, the way [InkBoy](https://github.com/kuslota/InkBoy)
builds grays. Pixels are planned in 2×2 blocks (400×240).

- [`src/grayscale/lut.rs`](src/grayscale/lut.rs) builds the waveform
  tables for registers `0x20`-`0x25`, in the format GxEPD2 uses for this
  panel's fast partial mode (`src/epd/GxEPD2_750_T7.cpp` in
  [ZinggJM/GxEPD2](https://github.com/ZinggJM/GxEPD2)). The drive voltages
  (power setting `0x01`) are unchanged from Waveshare's init.
- [`src/grayscale/drive.rs`](src/grayscale/drive.rs) plans each refresh.
  The old plane holds each pixel's direction, so most refreshes send only
  the new plane; a pixel that has to reverse waits for an occasional
  refresh that rewrites both planes.
- [`src/grayscale/boids.rs`](src/grayscale/boids.rs) steps the flock once
  per refresh and renders it into a logical-sized luma buffer;
  [`src/grayscale/scene.rs`](src/grayscale/scene.rs) owns that buffer so
  `grayscale_main.rs` hands it straight to the planner.
- `src/grayscale_main.rs` sends a refresh, plans the next one while the
  panel is busy, and every 60 seconds drives every pixel back to white and
  runs a factory full refresh. The flock keeps moving through that
  cleanup; only the panel restarts.

The planner never drives a pixel past white or black, so each pixel's net
drive is its estimated level and returns to zero before every full
refresh; `cargo test --lib` checks that by replaying planned planes
through a simulated controller. The model is only an estimate of the ink:
ghosting and drift between full refreshes are expected, and the full
refresh clears them.

Build and flash it like maze, but build it explicitly; it is not part of
plain `make build`:

```bash
cd inkbot-esp32
make build-grayscale
make flash APP=grayscale PORT=/dev/cu.usbserial-XXXX
make monitor PORT=/dev/cu.usbserial-XXXX
```

Every 50 refreshes the monitor prints a line like
`drive hz=<hz> ms/refresh=<ms> spi=<ms> plan=<ms> wait=<ms> ...`.
`spi` is the time spent sending planes, `plan` the time spent planning
while the panel drives, and `wait` how long the panel was still busy
after planning finished. A `wait` near zero means planning is the
bottleneck; a large `wait` means the waveform is.

Knobs, all constants:

| Constant | File | Effect |
|----------|------|--------|
| `SPI_MHZ` | `src/grayscale_display.rs` | 20 MHz sends a plane in about 19 ms. If the panel shows noise or ignores commands, lower it; `maze_display.rs` uses 4 MHz. |
| `FRAMES_PER_STEP` | `src/grayscale_main.rs` | Frames per drive step. More frames move ink further per refresh and lower the refresh rate. |
| `SWAP_DRIVE_POLARITY` | `src/grayscale_main.rs` | Set when the scene appears as a negative, or barely at all. |
| `FULL_REFRESH_INTERVAL` | `src/grayscale_main.rs` | Time between cleanup full refreshes. |
| `DriveConfig::swing` | `src/grayscale/drive.rs` | Steps from white to black. Fewer steps give fewer grays and faster swings per step. |
| `FlockConfig` fields | `src/grayscale/boids.rs` | Flock size, speeds, triangle size, and flocking weights. `max_speed` is matched to `triangle_length` so the ink can reach the triangle's gray before it moves on. `flock_count` splits `count` boids into that many separate starting flocks. `wander_strength` sets how much headings drift apart instead of locking together. |

To watch the estimated ink on the host, run `examples/boids_preview.rs`.
It writes one 800×480 gray frame per refresh to stdout. Play the frames
at 22 per second. That is the expected rate when a 19 ms plane transfer
is followed by a 20 ms drive frame. 660 frames is 30 seconds.

```bash
cargo run --quiet --example boids_preview -- 660 | \
  ffmpeg -y -f rawvideo -pix_fmt gray -s 800x480 -r 22 -i - boids.mp4
```

This firmware compiles for `xtensa-esp32-espidf` but has not run on a
panel.

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
│   ├── grayscale/                    # drive planner + waveform tables (host-tested; experimental)
│   ├── main.rs                       # inkbot: Wi-Fi + HTTP + OTA + GCP
│   ├── maze_main.rs / maze_display.rs
│   ├── grayscale_main.rs / grayscale_display.rs   # experimental; not OTA-registered
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
