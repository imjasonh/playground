# Option A — thin display body + direct-connect backpack

This is a separate concept model in [`option-a.scad`](option-a.scad). It does
not replace the current `case.scad` design while the physical board/FPC pose is
being reviewed.

## Shape

- Full display body: **178.8 × 125 × 5.4 mm**
- Centered rounded backpack: **38.36 × 57.15 mm**
- Backpack projection beyond the thin back: **13.6 mm**
- Maximum assembled depth at the backpack: **19 mm**
- The rest of the display remains only **5.4 mm** deep

The full thin backer remains because the raw e-paper glass is fragile. Only
the electronics volume becomes a local bump.

## Direct-connection assumption

The model assumes:

1. The panel’s 24-pin FPC passes directly through the centered backer opening.
2. The driver board is flipped flat against the rear, components facing out.
3. Its ZIF connector is at the backpack’s lower end.
4. Its USB-C connector exits the backpack’s upper wall.

Waveshare documents direct panel-to-board connection, but also warns that the
FPC must not be repeatedly bent, bent vertically, or bent toward the panel
front. Before finalizing fit, compare `board_y0`, the FPC slot, and USB opening
against a photo/measurement of the real board connected and folded into place.

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
5. Press on the backpack cover; USB-C exits its upper wall.
6. Fit the thin panel-end cap and insert two rigid keys.

The pod-cover retention and exact FPC strain relief are provisional until the
real direct-connected pose is measured.

## Generate

```bash
bash render-option-a.sh
bash export-option-a.sh
```
