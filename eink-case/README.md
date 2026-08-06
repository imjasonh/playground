# eink-case — Waveshare 7.5″ e-Paper + ESP32 driver case

Parametric OpenSCAD enclosure for:

| Device | ASIN | Notes |
|--------|------|-------|
| [Waveshare 7.5″ e-Paper raw panel](https://www.waveshare.com/7.5inch-e-Paper.htm) | `B075R69T93` | 800×480, 170.2×111.2×1.2 mm, 24-pin SPI FPC |
| [Waveshare e-Paper ESP32 Driver Board](https://www.waveshare.com/product/displays/e-paper-esp32-driver-board.htm) | `B07M5CNP3B` | 29.46×48.25 mm, USB-C (2024+; Micro-USB earlier) |

## How it fits

1. **Slide** the panel into a three-sided groove from the FPC edge until it seats on the top stop.
2. **Fold** the SPI ribbon 180° under the panel into the rear bay.
3. **Seat** the ESP32 board; USB exits `back` / `side` / `bottom` (Customizer).
4. **Close** the back lid (snap tabs + optional M2 screws).

## Usage

```bash
# Preview in the GUI Customizer
openscad case.scad

# Export printable parts
openscad -o front.stl -D 'part="front"' case.scad
openscad -o back.stl  -D 'part="back"'  case.scad

# PNG previews
bash render.sh
```

## Key parameters

| Parameter | Default | Meaning |
|-----------|---------|---------|
| `usb_exit` | `back` | Wall the USB-C cable leaves through (`back` / `side` / `bottom`) |
| `groove_clearance` | `0.35` | Slip fit around the panel outline (mm) |
| `groove_lip` | `1.1` | Front bezel thickness over the glass edge |
| `wall` | `2.2` | Outer wall thickness |
| `show_components` | `true` | Ghost panel + board in assembled preview |
| `explode` | `0` | Lid / board separation for assembly views |

Panel outline / active-area / board dimensions are Customizer knobs too — tweak if your panel revision differs.

## Printing

- PLA or PETG, 0.2 mm layers, ≥3 perimeters.
- Print `front` face-down (bezel on the bed) for a clean window edge; support the rear-bay overhangs if needed.
- Print `back` flat.
- Tap M2 into the bosses, or rely on the snap tabs alone for a friction fit.
