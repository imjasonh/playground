# eink-case — Waveshare 7.5″ e-Paper + ESP32 driver case

Parametric OpenSCAD enclosure for:

| Device | ASIN | Notes |
|--------|------|-------|
| [Waveshare 7.5″ e-Paper raw panel](https://www.waveshare.com/7.5inch-e-Paper.htm) | `B075R69T93` | 800×480, **170.2 × 111.2 × 1.2 mm**, 24-pin SPI FPC |
| [Waveshare e-Paper ESP32 Driver Board](https://www.waveshare.com/product/displays/e-paper-esp32-driver-board.htm) | `B07M5CNP3B` | **29.46 × 48.25 mm**, USB-C. **No mounting holes.** |

Design history and FDM lessons: [`LEARNINGS.md`](LEARNINGS.md).

Direct-connect thin-back concept: [`OPTION_A.md`](OPTION_A.md) /
[`option-a.scad`](option-a.scad). It keeps the full rear surface thin and adds
only a centered board-sized backpack; it is separate from the current model
pending physical FPC-position feedback.

## Principle: print the slot upward

The panel sits in a **U-groove** (front lip | slot | backer). The shell is
printed with the **closed end on the bed** and the **FPC end open at the top**,
so that groove is extruded in Z — every layer is the U profile. The backer is a
vertical wall in that orientation, not a bridge over the window.

No screw sandwich and no flexing PLA clips. The enclosure uses a shell, cap,
and **two identical rigid locking keys**.

## Closed overall dimensions

Run `./tools/validate.sh case.scad` — echoes the live size (tracks parameters).

## Printable parts

| STL | Bed face | Role |
|-----|----------|------|
| [`stl/shell.stl`](stl/shell.stl) | Closed end down (FPC mouth up) | Window, removable bridge lattice, U-slot, backer, bay, board cradle |
| [`stl/cap.stl`](stl/cap.stl) | Outer face down | Closes FPC end; retains panel and board |
| [`stl/cap-key.stl`](stl/cap-key.stl) | Pull-tab face down | Rigid cap lock — **print two** |

```bash
bash export-stl.sh   # binary STLs under stl/
```

## Fasteners (no screws)

| Joint | Hardware |
|-------|----------|
| **Cap → shell** | **2× printed rigid side keys** — no bending and no metal hardware |
| **ESP32 board** | **None** — straight slide rails; cap traps the USB end |

The first PLA cantilever clips were too stiff/brittle in a real print. The
replacement keys carry cap pull-out load in shear and do not flex. Their pull
tabs sit on the case sides, so the cap end remains the flat standing surface
(apart from the necessary USB-C opening). A shallow self-locking taper reaches
`0.10 mm` nominal interference only at full insertion, preventing a loose key
from falling out without relying on a thin snap arm.

## Assembly

1. Print shell closed-end down; print cap outer-face down.
2. **Before inserting the display**, cut the six narrow necks along the
   window’s lower edge and pull the sacrificial lattice out through the front.
   Its top has a one-layer gap, so it should release rather than tear the
   lintel. Trim any recessed nubs.
3. Slide the panel into the shell from the open FPC end. The revised slot has
   `0.40 mm` nominal clearance and gentler `0.15 mm` crush ribs.
4. Fold the SPI ribbon through the internal backer pass. Connect it to the
   board while the ZIF latch is still accessible.
5. Hold the board with components facing away from the panel/backer. Put the
   **ZIF end in first**, align both PCB edges with the two straight grooves,
   then push directly inward until the rails stop it. There is no sideways
   move and the USB-C connector remains at the shell mouth.
6. Fit the cap over the USB-C connector and panel tongue. Insert one rigid key
   from each side until its pull tab meets the wall.

To reopen, pull the two side keys, then remove the cap. The cap releases both
the panel and the board.

## Removable support for the window lintel

In print orientation, the upper edge of the display window is otherwise a
**~162 mm bridge**. The shell STL now includes a sacrificial lattice by
default:

- 6 vertical columns reduce the longest unsupported segment to **~22 mm**.
- Two horizontal rows keep the 97 mm-tall columns from wobbling.
- `0.45 mm` bottom necks are meant to be cut/snapped.
- The lattice is recessed `0.25 mm` from the cosmetic face.
- A `0.20 mm` gap (one normal layer) below the lintel limits welding while
  still catching the first bridge layer.

Keep `bridge_support_gap` equal to your normal layer height. Set
`window_bridge_supports=false` only if you intend to paint equivalent slicer
support under the lintel.

The shell’s FPC mouth is open on purpose for end-loading (bay access + slot).
The **front lip stays solid** through the fold-bay strip, so the face never
shows electronics. The **cap** closes that mouth: perimeter rabbet, front/back
skirts, bay plug, and retention tongue — no see-through when assembled.

## How the display is held snugly

| Axis | Mechanism |
|------|-----------|
| **Through-thickness** | True U-slot: front lip + backer |
| **Width / length / thickness** | Panel + `0.40 mm` per side; sparse `0.15 mm` crush ribs |
| **Slide-out** | Closed-end stop + **cap retention tongue** |

## Ribbon cable (no external access)

FPC folds in the open-end bay and passes through an **internal backer opening**
into the electronics bay. USB-C exits through the removable cap at
approximately **10.6 × 5.0 mm** (`9.2 × 3.6 mm` connector plus `0.7 mm`
clearance on each edge).

## Tooling

```bash
./tools/validate.sh case.scad
bash render.sh
bash export-stl.sh
./tools/extract-params.sh case.scad
```

| Parameter | Default | Meaning |
|-----------|---------|---------|
| `usb_face` | `0.0` | USB face recess from cap (`0`=flush) (mm) |
| `panel_clear` | `0.40` | Clearance per panel side / face (mm) |
| `panel_crush` | `0.15` | Sparse crush-rib intrusion (mm) |
| `board_pocket_clear` | `0.75` | PCB edge clearance in each rail (mm) |
| `board_z_clear` | `0.30` | PCB thickness clearance (mm) |
| `fpc_fold_bay` | `8.0` | Internal bay at FPC end (mm) |
| `lock_key_clear` | `0.25` | Printed key / lock-slot clearance (mm) |
| `lock_wedge` | `0.10` | Full-seat key interference; reduce if too tight (mm) |
| `window_bridge_supports` | `true` | Include removable window lattice |
| `bridge_support_count` | `6` | Columns under the window lintel |
| `bridge_support_gap` | `0.20` | Gap below lintel; match normal layer height (mm) |
| `elephant_chamfer` | `0.3` | Bed-face outer chamfer (mm) |
| `part` | `assembled` | `assembled` / `shell` / `cap` / `key` |

## Bambu A1 Mini / PLA starting profile

- Revised shell width is **178.8 mm**, under the A1 Mini’s 180 mm axis. Rotate
  it about 20° on the plate if a wide brim would otherwise exceed the boundary.
- Select the **actual plate type** in Bambu Studio. Textured PEI applies a
  plate-specific Z adjustment; the wrong selection can make layer one too high.
- Wash PEI with warm water and plain dish soap, rinse, dry, and avoid touching
  the print area. Run bed leveling.
- For PLA on textured PEI, start at **60 °C** and try **65 °C** if corners
  still lift (Bambu recommends the 55–65 °C range).
- Use **8–10 mm brim** with `0–0.05 mm` brim-object gap. Painted brim ears on
  the four shell corners are often more useful than increasing brim everywhere.
- No part cooling for the first **3 layers**; keep the printer away from HVAC
  drafts. A room below about 20 °C makes lifting more likely.
- First layer starting point: **0.25 mm height, 0.50 mm line width, 20 mm/s**.
  Inspect it: adjacent lines should merge without ridges or nozzle scraping.
- For the lintel, start with **25–30 mm/s bridge speed** and full bridge fan.
  The built-in lattice handles span length; no full-window slicer support is
  needed.
- PLA, 0.2 mm normal layers, ≥3 perimeters, 15–20% infill.
- **Shell:** closed end on bed, FPC mouth up. No supports (U-slot layers).
- **Cap:** outer face on bed. No supports.
- **Keys:** print two, pull-tab face down. No supports.
- Keep slicer elephant-foot compensation enabled. The model-side bed chamfer
  was reduced from `0.5` to `0.3 mm` to preserve more first-layer contact.

These are starting values rather than universal filament settings. Bambu’s
official guidance also recommends plate cleaning, +5–10 °C bed temperature,
8–10 mm brims / brim ears, and no cooling for the first three layers:
[warping guide](https://wiki.bambulab.com/en/filament-acc/filament/print-quality/warping-falling-off-collapsing).

## Dimensions confidence

Panel outline **170.2 × 111.2** is from Waveshare datasheets (typical drawing
tolerance **±0.2 mm**). Thickness is **1.18–1.20** by SKU. The revised defaults
incorporate feedback from one full-size PLA print, but printer flow and XY-hole
compensation still vary. Measure your unit before changing the fit parameters.
