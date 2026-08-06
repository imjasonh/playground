# FDM design rules for eink-case

Distilled from:

- [m-esm/3d-print-modeling `references/fdm-design-rules.md`](https://github.com/m-esm/3d-print-modeling/blob/main/references/fdm-design-rules.md)
- [m-esm/3d-print-modeling `references/design-rules-checklist.md`](https://github.com/m-esm/3d-print-modeling/blob/main/references/design-rules-checklist.md)
- [chriscantey/skill-3d-printing Design workflow](https://github.com/chriscantey/skill-3d-printing)

Use with the OpenSCAD skill tools in this folder. Cite rules by id in review notes.

## Declared print orientations (R1.3)

| Part | STL | Bed face | Why |
|------|-----|----------|-----|
| Bezel | `stl/bezel.stl` | **Outer face down** | Crisp window on the bed; panel pocket opens up |
| Tray | `stl/tray.stl` | **Floor down (cavity up)** | Solid panel backer on the bed — not a mid-air deck |
| Back lid | `stl/back.stl` | **Outer face down** | Large flat on bed; snaps + posts point up |

## Hard rules we enforce here

- **R1.1** Walls ≥ 0.8 mm (we use ≥ 2.0 mm).
- **R1.2** No flat ceilings over open cavities. No solid floor spanning the active-area window. Panel is backed by a **perimeter ledge** only; board mounts on the **lid**, not on a mid-air deck over the glass.
- **R1.3** Orientation is chosen at design time; STLs are exported already flipped for the bed.
- **R1.4** Holes undersize — screw clearance and USB cutouts include slop parameters.
- **R1.7** Lid snaps / self-tap bosses are light-duty; PETG optional for snaps.
- **Elephant foot** — each part’s bed-face outer perimeter gets a parametric
  45° chamfer (`elephant_chamfer`, default 0.5 mm). The bezel window also gets
  `window_elephant_chamfer` so the lip doesn’t flare inward. Set either to `0`
  to disable. Still tune slicer first-layer compensation.

## Anti-patterns that bit this case

1. **Solid bay floor behind the AA** — when printing bezel-down, that floor is a ~160×100 mm mid-air bridge over the window. Failed R1.2. Fixed with a perimeter ledge + open center.
2. **Board cradle on the front shell** — pad overlapped the AA in XY, recreating a floating deck. Fixed by moving the cradle to the lid (prints as upward walls on a flat bed face).
3. **Label recess deeper than remaining lid thickness** — punched a through-hole. Removed.
4. **Exporting the lid in assembly orientation** — posts pointed at the bed. Fixed with `back_lid_print()`.

## Checklist before exporting STLs

1. `./tools/validate.sh case.scad` — manifold / echoes OK
2. `bash render.sh` — inspect every PNG
3. Mentally raycast from bed-up in the declared orientation: any region above the bed that isn't grown from a wall is a bridge — redesign it out
4. `bash export-stl.sh`
5. In the slicer: confirm support volume is ~0 on both parts (tree support only if something slipped through)
