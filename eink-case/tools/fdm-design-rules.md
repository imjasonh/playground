# FDM design rules for eink-case

Distilled from:

- [m-esm/3d-print-modeling `references/fdm-design-rules.md`](https://github.com/m-esm/3d-print-modeling/blob/main/references/fdm-design-rules.md)
- [m-esm/3d-print-modeling `references/design-rules-checklist.md`](https://github.com/m-esm/3d-print-modeling/blob/main/references/design-rules-checklist.md)
- [chriscantey/skill-3d-printing Design workflow](https://github.com/chriscantey/skill-3d-printing)

Project-specific history: [`../LEARNINGS.md`](../LEARNINGS.md).

Use with the OpenSCAD skill tools in this folder. Cite rules by id in review notes.

## Declared print orientations (R1.3)

| Part | STL | Bed face | Why |
|------|-----|----------|-----|
| Shell | `stl/shell.stl` | **Closed end down** (FPC mouth up) | U-slot is extruded in print Z — every layer is the U profile; backer is a vertical wall, not a bridge |
| Cap | `stl/cap.stl` | **Outer face down** | Flat plate; retention tongue + rigid lock tongues point up |
| Cap key (print 2) | `stl/cap-key.stl` | **Pull-tab face down** | Wide tab gives a stable base; rigid key grows upward |

## Hard rules we enforce here

- **R1.1** Walls ≥ 0.8 mm (we use ≥ 2.0 mm).
- **R1.2** No flat ceilings over open cavities. Do **not** print a solid deck behind the AA as a ceiling. The panel backer must be a wall in the print orientation (U-slot principle).
- **R1.3** Orientation is chosen at design time; STLs are exported already flipped for the bed.
- **R1.4** USB, rigid-key slots, panel slot, and PCB rails have explicit slop.
- **R1.7** No functional PLA flexures. Cap locks use removable rigid keys in
  shear; `lock_key_clear` controls fit.
- **Elephant foot** — bed-face outer chamfer (`elephant_chamfer`) + optional window lip chamfer. Set `0` to disable. Still tune slicer compensation.
- **Binary STLs** — `--export-format=binstl`; `*.stl binary` in `.gitattributes`.
- **A1 Mini envelope** — default shell X must remain ≤180 mm. Wide brims may
  require rotating the 178.8 mm shell on the plate.

## Anti-patterns (see LEARNINGS.md)

1. Solid bay floor behind the AA printed bezel-down → huge bridge.
2. 3-piece screw sandwich just to make the deck printable.
3. External / mid-floor ribbon holes mistaken for cable exits.
4. Screw bosses through the glass footprint.
5. ASCII STLs exploding PR diffs.

## Checklist before exporting STLs

1. `./tools/validate.sh case.scad` — manifold / echoes OK
2. `bash render.sh` — inspect every PNG
3. Mentally raycast from bed-up: shell layers should look like a U (lip | slot | backer | bay). Any mid-air ceiling is a redesign.
4. `bash export-stl.sh`
5. Slicer: support volume ~0 on shell, cap, and keys
