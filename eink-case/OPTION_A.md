# Option A — thin display body + direct-connect backpack

This is a separate concept model in [`option-a.scad`](option-a.scad). It does
not replace the current `case.scad` design while the physical board/FPC pose is
being reviewed.

## Shape

- Full display body: **178.8 × 125 × 5.4 mm**
- Connector-aligned rounded backpack: **57.15 × 38.36 mm**
- Backpack projection beyond the thin back: **13.6 mm**
- Maximum assembled depth at the backpack: **19 mm**
- The rest of the display remains only **5.4 mm** deep

The full thin backer remains because the raw e-paper glass is fragile. Only
the electronics volume becomes a local bump.

## Direct-connection assumption

The model assumes:

The corrected layout follows Waveshare’s Rev 3 component-side photo:

1. Board outline is **48.25 mm X × 29.46 mm Y**.
2. The 24-pin ZIF sits on the **lower long edge**, with its center about
   **35.8 mm from the board’s left edge**.
3. USB-C sits on the adjacent **right short edge**, approximately 90° from
   the display connector.
4. Aligning the offset ZIF to the panel’s centered FPC puts the board at
   **X=53.6…101.85 mm** and shifts the backpack left of display center.
5. USB-C exits the backpack’s right wall. A larger exterior access well leaves
   its face only **0.5 mm recessed**, even though the rounded cover is thicker.
6. The board is folded flat behind the panel, components facing outward.

Waveshare documents direct panel-to-board connection, but also warns that the
FPC must not be repeatedly bent, bent vertically, or bent toward the panel
front. The connector offsets above are photo-derived because Waveshare only
publishes the overall PCB dimensions. Before finalizing fit, compare
`board_fpc_center_x`, `board_usb_center_y`, the FPC slot, and USB well against
the user’s exact USB-C board revision while directly connected.

## Printable parts

| File | Quantity | Print face |
|------|---------:|------------|
| `stl/option-a-shell.stl` | 1 | Closed panel end down |
| `stl/option-a-cap.stl` | 1 | Outer end face down |
| `stl/option-a-pod-cover.stl` | 1 | Rounded rear face down |
| `stl/option-a-key.stl` | 2 | Pull-tab face down |

The shell includes the same removable six-column window-lintel lattice as the
current case. The board backpack cover is a separate rounded shell that prints
rear-face down and friction-fits over a shallow collar. The collar’s sparse
`pod_crush` ribs and `pod_fit_clear` tune that fit.

## Assembly concept

1. Remove the shell’s sacrificial window lattice.
2. Slide in the display and expose its FPC through the centered rear slot.
3. Connect the driver board directly and fold it flat, components outward.
4. Place it on the four standoff pads inside the rounded collar.
5. Press on the backpack cover; USB-C exits its right-side access well.
6. Fit the thin panel-end cap and insert two rigid keys.

The pod-cover retention and exact FPC strain relief are provisional until the
real direct-connected pose is measured.

## Generate

```bash
bash render-option-a.sh
bash export-option-a.sh
```
