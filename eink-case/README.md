# eink-case — Waveshare 7.5″ e-Paper + ESP32 driver case

Parametric OpenSCAD enclosure for:

| Device | ASIN | Notes |
|--------|------|-------|
| [Waveshare 7.5″ e-Paper raw panel](https://www.waveshare.com/7.5inch-e-Paper.htm) | `B075R69T93` | 800×480, **170.2 × 111.2 × 1.2 mm**, 24-pin SPI FPC |
| [Waveshare e-Paper ESP32 Driver Board](https://www.waveshare.com/product/displays/e-paper-esp32-driver-board.htm) | `B07M5CNP3B` | **29.46 × 48.25 mm**, USB-C. **No mounting holes.** |

## Closed overall dimensions

Run `./tools/validate.sh case.scad` — echoes the live size (tracks parameters).
With defaults the rim is wide enough for corner M2 bosses **outside** the glass
(~192 × 140 × 22 mm).

## How the display is held snugly

| Axis | Mechanism |
|------|-----------|
| **XY** | Bezel pocket ≈ panel + `panel_clear` (0.30 mm), plus short **crush ribs** (`panel_crush` 0.20 mm) on left/right/top that press-fit the outline. Shoulders beside the FPC stop the panel from sliding into the fold bay. |
| **Z** | Tray floor clamps the glass against the bezel window lip when the four M2 screws are tightened (panel back and bezel rim share the same mating plane). |

There is no slide-in U-groove spanning the active area — that would be an FDM bridge. The three-part sandwich is the retention.

## Ribbon cable (no external access)

The SPI FPC never exits the case. It folds in the bezel’s internal bay (under
the tray floor), then reaches the driver board through a **narrow chase against
the inner wall** — not a hole in the middle of the floor, and not an opening in
the outer shell. USB-C still has its own wall cutout (`usb_exit`).

## Three printable parts (FDM-friendly)

A one-piece front shell needed a solid deck behind the glass. Printed
bezel-down, that deck is a huge mid-air bridge. The design is split so every
part has a flat bed face and **no floating spans**:

| STL | Bed face | Role |
|-----|----------|------|
| [`stl/bezel.stl`](stl/bezel.stl) | Outer face down | Window + panel pocket + crush ribs |
| [`stl/tray.stl`](stl/tray.stl) | Floor down (cavity up) | Solid panel backer, wall-edge FPC chase, board cradle, bosses |
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

1. Press the panel into the **bezel** pocket (FPC toward the internal fold bay — no external notch).
2. Clamp **bezel** to **tray** with 4× M2 (tray floor backs and clamps the glass).
3. Fold the SPI ribbon through the wall-edge chase to the board; use the kit **FFC extension** if USB exits a side wall.
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
| `panel_clear` | `0.30` | Base XY clearance around the panel (mm) |
| `panel_crush` | `0.20` | Crush-rib intrusion for snug XY (mm) |
| `fpc_fold_bay` | `6.0` | Internal bay under the FPC edge (mm) |
| `elephant_chamfer` | `0.5` | Bed-face outer 45° chamfer (mm); `0` disables |
| `window_elephant_chamfer` | `0.3` | Bezel window bed-face chamfer (mm) |
| `part` | `assembled` | `assembled` / `bezel` / `tray` / `back` |

## Printing

- PLA or PETG, 0.2 mm layers, ≥3 perimeters, 15–20% infill.
- **Bezel:** outer face on bed (pocket opens up). No supports.
- **Tray:** floor on bed, cavity up. No supports.
- **Lid:** outer face on bed, posts/snaps up. No supports.
- Bed faces have parametric **elephant-foot chamfers** (`elephant_chamfer`,
  `window_elephant_chamfer`). Still enable slicer elephant-foot compensation.
- Tap M2 gently into pilots — don’t over-torque.
