# eink-case — Waveshare 7.5″ e-Paper + ESP32 driver case

Parametric OpenSCAD enclosure for:

| Device | ASIN | Notes |
|--------|------|-------|
| [Waveshare 7.5″ e-Paper raw panel](https://www.waveshare.com/7.5inch-e-Paper.htm) | `B075R69T93` | 800×480, **170.2 × 111.2 × 1.2 mm**, 24-pin SPI FPC |
| [Waveshare e-Paper ESP32 Driver Board](https://www.waveshare.com/product/displays/e-paper-esp32-driver-board.htm) | `B07M5CNP3B` | **29.46 × 48.25 mm**, USB-C. **No mounting holes.** |

Design history and FDM lessons: [`LEARNINGS.md`](LEARNINGS.md).

## Principle: print the slot upward

The panel sits in a **U-groove** (front lip | slot | backer). The shell is
printed with the **closed end on the bed** and the **FPC end open at the top**,
so that groove is extruded in Z — every layer is the U profile. The backer is a
vertical wall in that orientation, not a bridge over the window.

No 3-piece screw sandwich. Two parts: shell + cap.

## Closed overall dimensions

Run `./tools/validate.sh case.scad` — echoes the live size (tracks parameters).

## Two printable parts

| STL | Bed face | Role |
|-----|----------|------|
| [`stl/shell.stl`](stl/shell.stl) | Closed end down (FPC mouth up) | Window, U-slot, backer, bay, board cradle |
| [`stl/cap.stl`](stl/cap.stl) | Outer face down | Closes FPC end; retention tongue; clips |

```bash
bash export-stl.sh   # binary STLs under stl/
```

## Fasteners (no screws)

| Joint | Hardware |
|-------|----------|
| **Cap → shell** | **4× internal cantilever clips** (flush side windows; flat cap face) |
| **ESP32 board** | **None** — bay cradle (optional VHB) |

No screw heads — the cap’s outer face is flat so the FPC end can sit flush.

## Assembly

1. Print shell closed-end down; print cap outer-face down.
2. Slide the panel into the shell from the FPC end (crush ribs snug the outline).
3. Fold the SPI ribbon through the internal backer pass into the bay; seat the board.
4. Press the **cap** on until the side clips click — the tongue blocks the panel
   from sliding out. Pinch the flush side windows to release.

The shell’s FPC mouth is open on purpose for end-loading (bay access + slot).
The **front lip stays solid** through the fold-bay strip, so the face never
shows electronics. The **cap** closes that mouth: perimeter rabbet, front/back
skirts, bay plug, and retention tongue — no see-through when assembled.

## How the display is held snugly

| Axis | Mechanism |
|------|-----------|
| **Through-thickness** | True U-slot: front lip + backer |
| **Width** | Slot ≈ panel + `panel_clear`, plus **crush ribs** |
| **Slide-out** | Closed-end stop + **cap retention tongue** |

## Ribbon cable (no external access)

FPC folds in the open-end bay, passes through an **internal backer opening** into
the electronics bay. Outer shell stays closed. USB-C uses `usb_exit`.

## Tooling

```bash
./tools/validate.sh case.scad
bash render.sh
bash export-stl.sh
./tools/extract-params.sh case.scad
```

| Parameter | Default | Meaning |
|-----------|---------|---------|
| `usb_exit` | `back` | USB wall: `back` / `side` |
| `panel_clear` | `0.30` | Slot clearance (mm) |
| `panel_crush` | `0.20` | Crush-rib intrusion (mm) |
| `fpc_fold_bay` | `8.0` | Internal bay at FPC end (mm) |
| `elephant_chamfer` | `0.5` | Bed-face outer chamfer (mm) |
| `clip_barb` | `0.9` | Side-clip engagement (mm); lower if too tight |
| `part` | `assembled` | `assembled` / `shell` / `cap` |

## Printing

- PLA or PETG, 0.2 mm layers, ≥3 perimeters, 15–20% infill.
- **Shell:** closed end on bed, FPC mouth up. No supports (U-slot layers).
- **Cap:** outer face on bed. No supports.
- Enable slicer elephant-foot compensation in addition to `elephant_chamfer`.
- PETG is nicer for the cap clips; PLA works if `clip_barb` isn’t aggressive.

## Dimensions confidence

Panel outline **170.2 × 111.2** is from Waveshare datasheets (typical drawing
tolerance **±0.2 mm**). Thickness is **1.18–1.20** by SKU. Measure your unit and
tweak `panel_w` / `panel_h` / `panel_clear` / `panel_crush` before a final print.
