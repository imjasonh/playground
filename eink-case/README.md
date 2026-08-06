# eink-case — Waveshare 7.5″ e-Paper + ESP32 driver case

Parametric OpenSCAD enclosure for:

| Device | ASIN | Notes |
|--------|------|-------|
| [Waveshare 7.5″ e-Paper raw panel](https://www.waveshare.com/7.5inch-e-Paper.htm) | `B075R69T93` | 800×480, **170.2 × 111.2 × 1.2 mm**, 24-pin SPI FPC |
| [Waveshare e-Paper ESP32 Driver Board](https://www.waveshare.com/product/displays/e-paper-esp32-driver-board.htm) | `B07M5CNP3B` | **29.46 × 48.25 mm**, USB-C (2024+; Micro-USB earlier). **No mounting holes.** |

## Closed overall dimensions

**175.8 × 120.4 × 22.2 mm** (W × H × D)

| Axis | Meaning |
|------|---------|
| W 175.8 mm | Along the panel’s long edge |
| H 120.4 mm | Along the panel’s short edge (FPC on this side) |
| D 22.2 mm | Front bezel → back lid |

These track the parameters and are echoed whenever you open/render `case.scad`.

## Two printable parts

| STL | Role |
|-----|------|
| [`stl/front.stl`](stl/front.stl) | Bezel, panel groove, bay floor, board cradle, screw bosses |
| [`stl/back.stl`](stl/back.stl) | Lid with snap tabs + PCB hold-down posts |

```bash
openscad -o stl/front.stl -D 'part="front"' case.scad
openscad -o stl/back.stl  -D 'part="back"'  case.scad
# or: bash export-stl.sh
```

## Screws

| Joint | Hardware | Notes |
|-------|----------|-------|
| **Back lid → front** | **4× M2 × 8 mm self-tapping pan-head** | Into 1.7 mm pilots in the corner bosses. 6 mm is short; 10 mm works if you don’t bottom out hard. |
| **ESP32 board** | **None** | The Waveshare PCB has no mounting holes. It drops into a three-sided cradle and the lid posts press on the PCB corners. Optional: a square of 3M VHB / foam tape under the board. |

Snaps alone can hold the lid for a dry fit; use the M2 screws for a finished assembly.

## How it fits

1. **Slide** the panel into the three-sided groove from the FPC edge until it seats on the top stop.
2. **Fold** the SPI ribbon under the panel into the cable trough (use the **FFC extension + adapter** that ships with the driver board when `usb_exit` is `back` or `side` — that layout needs ~30 mm of lateral routing).
3. **Seat** the ESP32 board in the cradle; USB exits the chosen wall.
4. **Close** the lid (snaps + 4× M2×8).

### Fit budget (defaults)

| Item | Allowance |
|------|-----------|
| Panel XY | outline + 0.40 mm clearance each side |
| Panel Z | 1.20 mm panel in a 2.00 mm groove |
| Board XY | 29.46 × 48.25 mm + 0.50 mm pocket slop |
| Board Z | 2.0 mm pad + 1.6 mm PCB + 8.0 mm component air |
| Cable | 22 mm-wide trough under the panel for FPC + extension |

## Usage

This project vendors the
[mitsuhiko/agent-stuff OpenSCAD skill](https://github.com/mitsuhiko/agent-stuff/tree/main/skills/openscad)
under `tools/`. See [`AGENTS.md`](AGENTS.md) for the agent workflow.

```bash
openscad case.scad                 # Customizer GUI
./tools/validate.sh case.scad      # syntax + dimension echoes
bash render.sh                     # multi-angle PNGs → previews/
bash export-stl.sh                 # refresh stl/front.stl + stl/back.stl
./tools/extract-params.sh case.scad
```

| Parameter | Default | Meaning |
|-----------|---------|---------|
| `usb_exit` | `back` | USB wall: `back` (left/−X), `side` (+X), or `bottom` (FPC edge) |
| `groove_clearance` | `0.40` | Slip fit around the panel (mm) |
| `part` | `assembled` | `assembled` / `front` / `back` |

## Printing

- PLA or PETG, 0.2 mm layers, ≥3 perimeters, 15–20% infill.
- Print **front** with the bezel on the bed (window facing down) for a clean AA edge; support the bay overhangs if your slicer needs it.
- Print **back** flat (outer face down).
- Tap the M2 screws gently into the pilots — don’t over-torque into plastic.
