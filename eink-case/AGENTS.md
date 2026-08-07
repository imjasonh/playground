# Agent guide: eink-case

Parametric OpenSCAD case for a Waveshare 7.5″ e-Paper raw panel + ESP32
driver board.

**Read [`LEARNINGS.md`](LEARNINGS.md) before changing geometry.**

## Skills in this project

1. **OpenSCAD skill** (vendored under `tools/` from
   [mitsuhiko/agent-stuff](https://github.com/mitsuhiko/agent-stuff/tree/main/skills/openscad))
   — validate, multi-preview, extract-params, export-stl. Upstream text:
   `tools/UPSTREAM_SKILL.md`.
2. **FDM printability rules** — `tools/fdm-design-rules.md`.

**Never skip visual validation. Never export STLs that put a flat deck behind
the AA as a print ceiling (R1.2).**

## Design principle

The panel groove is a **U-channel extruded in print Z** (slide direction).
Shell prints **closed-end down / FPC mouth up**. The backer is a vertical wall
in that orientation — not a bridge. Cap closes the open end and retains the
panel.

## Workflow after every geometry edit

```bash
./tools/validate.sh case.scad
bash render.sh                 # previews/{assembled,shell,cap}/
# READ every PNG with the image tool — confirm U-slot layers, no bridges
bash export-stl.sh             # stl/{shell,cap}.stl (binary)
```

## Two printable parts

| Part | STL | Bed face | Role |
|------|-----|----------|------|
| `shell` | `stl/shell.stl` | Closed end down | Window, U-slot, backer, bay, cradle |
| `cap` | `stl/cap.stl` | Outer face down | Retains panel; closes FPC end |

## Fasteners

| Joint | Hardware |
|-------|----------|
| Cap → shell | 4× internal cantilever clips (no screws; flat cap face) |
| Board | None — bay cradle (optional VHB) |

## Fit notes

- Closed overall echoed by `validate.sh`.
- Panel slides into the U-slot; crush ribs snug XY; cap tongue blocks slide-out.
- Ribbon stays inside: fold bay + backer pass into bay — **no external hole**.
- Board cradle rails/beads are fused to the backer; USB-end rail omitted.
- USB tip defaults flush with the outer wall (`usb_face=0`); opening is
  `usb_w/h + 2*usb_cut_clear` (≈10.6×5.0 mm for stock USB-C).
- Datasheet outline is nominal (±0.2 mm typical) — measure before final print.
- `elephant_chamfer` / `window_elephant_chamfer` (set `0` to disable).
