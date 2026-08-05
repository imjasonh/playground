# E-ink display — plan

The Inland ESP-WROOM-32 dev board doesn't have a software-controllable LED
(see [`setup.md`](setup.md)), so the visible-output story for this
project is an e-ink display. This file captures the hardware choice,
the Rust graphics stack we'll use, and a shortlist of projects to
build on top.

## Hardware

- **Display**: Inland 2.13" e-ink (Micro Center SKU 632694).
  - 250×122 mono, SPI, ~Waveshare 2.13" rebrand
  - 8-pin male header: `VCC`, `GND`, `DIN`, `CLK`, `CS`, `DC`, `RST`, `BUSY`
  - Pre-soldered headers — no soldering required
- **Refresh characteristics** (SSD1680 driver, typical for this panel):
  - Full refresh ~2s, with the black/white flash that clears ghosting
  - Partial refresh ~300ms, no flash, but ghosting accumulates
  - Run a full every 5–10 partials
  - No grayscale, no animation. "Update once, look at it for a while."
- **Supporting hardware**: half-size solderless breadboard, Dupont jumper
  assortment (F-F at minimum). Both boards are 3V3, no level shifter needed.

Wiring sketch (pins on the ESP32 are conventional for SPI2/HSPI, adjust
as needed once the panel arrives):

```
e-ink   ESP32
-----   -----
VCC  -> 3V3
GND  -> GND
DIN  -> GPIO23 (MOSI)
CLK  -> GPIO18 (SCK)
CS   -> GPIO5
DC   -> GPIO17
RST  -> GPIO16
BUSY -> GPIO4
```

## Rust graphics stack

All `no_std`-friendly, all sit on top of the existing `esp-idf-svc` setup —
just add deps to `Cargo.toml` and draw onto the display via the
`embedded-graphics` `DrawTarget` that `epd-waveshare` implements.

- **`embedded-graphics`** — primitives, base `DrawTarget` trait
- **`epd-waveshare`** — Waveshare e-ink driver, includes the 2.13" panel
- **`u8g2-fonts`** — large font collection, far better than the
  embedded-graphics built-ins
- **`embedded-text`** — text wrapping / multi-line layout in a bounding box
- **`embedded-layout`** — vertical/horizontal stacking, alignment helpers
  (no Flexbox, but covers most positioning we'll need)
- **`tinybmp`** — render `include_bytes!`'d 1-bit BMPs as
  embedded-graphics images; the easy path for icons
- **`embedded-iconoir`** — optional, ready-made Iconoir icons

Default starting set: `embedded-graphics + u8g2-fonts + embedded-text +
tinybmp`. Pull in `embedded-layout` once positioning gets tedious.

### Heavier option: Slint

[Slint](https://slint.dev/) has an MCU backend with explicit e-ink support.
Write `.slint` markup, get live layout preview. Workable on the
ESP32-WROOM-32 but noticeable flash/RAM footprint. Reach for it only if
iterating on layout becomes a bottleneck with the embedded-graphics stack.

## Project shortlist

Ordered by cool : effort ratio.

1. **Wi-Fi info screen** — weather, next calendar event, GitHub PR count,
   refreshed every 5–10 minutes. **Best first project**: smallest
   end-to-end exercise of Wi-Fi + HTTP + JSON + e-ink rendering. Once it
   works, the rest are variations on the same skeleton.
2. **Build status badge** — last commit's CI state for one or more repos.
   Sits on the desk, nags when CI breaks.
3. **Pomodoro timer** — two physical buttons, big "WORK 17:32" / "BREAK
   04:00" text. E-ink wins because no backlight to distract.
4. **Now-playing card** — Spotify Web API. Refresh slowness fits since
   tracks last minutes.
5. **Door / desk status sign** — "available / heads-down / on a call",
   toggled from phone via tiny HTTP server on the ESP32. Battery + e-ink
   = days of runtime.
6. **Home Assistant / MQTT subscriber** — display whatever the home
   automation system publishes.
7. **Conference badge / desk name tag** — name + handle + QR code,
   updateable over Wi-Fi.
8. **Status dashboard for a personal service** — uptime, last-deploy
   time, error count from one of Jason's own services.

## Crate stack already in place

The current `Cargo.toml` has `esp-idf-svc` 0.51 with `binstart` + `native`
features, plus `log` and `anyhow`. That covers Wi-Fi, HTTP client, NTP,
NVS storage. For the e-ink work we just add the embedded-graphics family
of crates listed above and an SPI driver from `esp-idf-hal`.
