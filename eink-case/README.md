# eink-case — Waveshare 7.5″ e-Paper + ESP32 driver case

Parametric OpenSCAD enclosure for:

| Device | ASIN | Notes |
|--------|------|-------|
| [Waveshare 7.5″ e-Paper raw panel](https://www.waveshare.com/7.5inch-e-Paper.htm) | `B075R69T93` | 800×480, **170.2 × 111.2 × 1.2 mm**, 24-pin SPI FPC |
| [Waveshare e-Paper ESP32 Driver Board](https://www.waveshare.com/product/displays/e-paper-esp32-driver-board.htm) | `B07M5CNP3B` | **29.46 × 48.25 mm**, USB-C. **No mounting holes.** |

## Closed overall dimensions

Run `./tools/validate.sh case.scad` — echoes the live size (tracks parameters).

## Three printable parts (FDM-friendly)

A one-piece front shell needed a solid deck behind the glass. Printed
bezel-down, that deck is a huge mid-air bridge. The design is split so every
part has a flat bed face and **no floating spans**:

| STL | Bed face | Role |
|-----|----------|------|
| [`stl/bezel.stl`](stl/bezel.stl) | Outer face down | Window + panel pocket |
| [`stl/tray.stl`](stl/tray.stl) | Floor down (cavity up) | Panel backer, board cradle, screw bosses |
| [`stl/back.stl`](stl/back.stl) | Outer face down | Lid, snaps, PCB hold-downs |

See [`tools/fdm-design-rules.md`](tools/fdm-design-rules.md) and [`AGENTS.md`](AGENTS.md).

```bash
bash export-stl.sh
```

## Screws

| Joint | Hardware |
|-------|----------|
| **Bezel → tray** | **4× M2 × 8 mm self-tapping pan-head** |
| **Lid → tray** | **4× M2 × 8 mm self-tapping pan-head** (same corner bosses) |
| **ESP32 board** | **None** — tray cradle + lid posts (optional VHB) |

## Assembly

1. Drop the panel into the **bezel** pocket (FPC through the bottom notch).
2. Clamp **bezel** to **tray** with 4× M2 (panel sandwiched; tray floor backs the glass).
3. Fold the SPI ribbon into the tray; use the kit **FFC extension** if USB exits a side wall.
4. Seat the ESP32 board in the tray cradle.
5. Close the **lid** (snaps + 4× M2 from the back).

## Tooling

Vendored [mitsuhiko OpenSCAD skill](https://github.com/mitsuhiko/agent-stuff/tree/main/skills/openscad) + FDM rules:

```bash
./tools/validate.sh case.scad
bash render.sh                 # multi-angle PNGs
bash export-stl.sh
./tools/extract-params.sh case.scad
```

| Parameter | Default | Meaning |
|-----------|---------|---------|
| `usb_exit` | `back` | USB wall: `back` / `side` / `bottom` |
| `panel_clear` | `0.40` | Slip fit around the panel (mm) |
| `part` | `assembled` | `assembled` / `bezel` / `tray` / `back` |

## Printing

- PLA or PETG, 0.2 mm layers, ≥3 perimeters, 15–20% infill.
- **Bezel:** outer face on bed (pocket opens up). No supports.
- **Tray:** floor on bed, cavity up. No supports.
- **Lid:** outer face on bed, posts/snaps up. No supports.
- Tap M2 gently into pilots — don’t over-torque.
