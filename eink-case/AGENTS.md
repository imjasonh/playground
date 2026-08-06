# Agent guide: eink-case

Parametric OpenSCAD case for a Waveshare 7.5″ e-Paper raw panel + ESP32
driver board.

## Skills in this project

1. **OpenSCAD skill** (vendored under `tools/` from
   [mitsuhiko/agent-stuff](https://github.com/mitsuhiko/agent-stuff/tree/main/skills/openscad))
   — validate, multi-preview, extract-params, export-stl. Upstream text:
   `tools/UPSTREAM_SKILL.md`.
2. **FDM printability rules** — `tools/fdm-design-rules.md` (distilled from
   [m-esm/3d-print-modeling](https://github.com/m-esm/3d-print-modeling) and
   [chriscantey/skill-3d-printing](https://github.com/chriscantey/skill-3d-printing)).

**Never skip visual validation. Never export STLs that violate R1.2 (flat
ceilings / AA-spanning decks).**

## Workflow after every geometry edit

```bash
./tools/validate.sh case.scad
bash render.sh                 # previews/{assembled,bezel,tray,back}/
# READ every PNG with the image tool — check for bridges & floating spans
bash export-stl.sh             # stl/{bezel,tray,back}.stl
```

Mentally raycast bed→up in each part’s declared print orientation
(`tools/fdm-design-rules.md`). Any mid-air region that isn’t grown from a wall
is a redesign, not “add support”.

## Three printable parts

| Part | STL | Bed face | Role |
|------|-----|----------|------|
| `bezel` | `stl/bezel.stl` | Outer face down | Window frame + panel pocket |
| `tray` | `stl/tray.stl` | Floor down (cavity up) | Panel backer, board cradle, bosses |
| `back` | `stl/back.stl` | Outer face down | Lid + snaps + PCB hold-downs |

Why not a one-piece “front”? A solid bay floor behind the active area becomes a
~160×100 mm bridge when printed bezel-down (fails R1.2). Splitting face vs tray
puts that floor **on the bed**.

## Fasteners

| Joint | Hardware |
|-------|----------|
| Bezel → tray | 4× M2×8 mm self-tapping into corner pilots |
| Lid → tray | 4× M2×8 mm self-tapping (same bosses, from back) |
| Board | None — cradle in tray + lid posts |

## Fit notes

- Closed overall echoed by `validate.sh` (defaults ~176×120×~24 mm).
- Side/back USB layouts need the kit FFC extension (~30 mm lateral jog).
- Customizer knobs use `// [range] desc` comments for `extract-params.sh`.
