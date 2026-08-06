# Agent guide: eink-case

Parametric OpenSCAD case for a Waveshare 7.5″ e-Paper raw panel + ESP32
driver board. Follow the
[mitsuhiko/agent-stuff OpenSCAD skill](https://github.com/mitsuhiko/agent-stuff/tree/main/skills/openscad)
workflow (tools vendored under `tools/`; upstream text in
`tools/UPSTREAM_SKILL.md`).

## Never skip visual validation

After writing or editing `case.scad`:

1. `./tools/validate.sh case.scad`
2. `./tools/multi-preview.sh case.scad ./previews/ -D 'part="assembled"' -D 'show_components=true'`
3. **Read every generated PNG** (`previews/case_*.png`) with the image read tool
4. Also preview printable parts alone:
   - `./tools/multi-preview.sh case.scad ./previews/front/ -D 'part="front"'`
   - `./tools/multi-preview.sh case.scad ./previews/back/ -D 'part="back"'`
5. Fix geometry issues and re-validate before exporting STLs

Syntax OK is not enough — catch inverted normals, bad booleans, missing
features, and wrong proportions by looking at the images.

## Tools (`tools/`)

| Script | Purpose |
|--------|---------|
| `validate.sh` | Parse/eval; print echoes (closed size, fasteners) |
| `preview.sh` | Single PNG (`--camera=…`, `--size=WxH`, `-D`) |
| `multi-preview.sh` | front / back / left / right / top / iso PNGs |
| `export-stl.sh` | Binary STL |
| `extract-params.sh` | Customizer parameters (`--json` supported) |
| `render-with-params.sh` | STL/PNG from a JSON param file |

Convenience wrappers at the project root:

```bash
bash render.sh                 # multi-preview assembled + front + back
bash export-stl.sh             # stl/front.stl + stl/back.stl
```

## Parameter comments

Keep Customizer knobs at file scope with skill-style trailing comments so
`extract-params.sh` can read them:

```openscad
wall = 2.4;              // [1.5:0.1:4] Outer wall thickness (mm)
usb_exit = "back";       // [back, side, bottom] USB-C wall
show_components = true;  // Ghost panel + board in assembled preview
```

## Printable parts

Exactly **two** STLs:

| Part | Export |
|------|--------|
| `front` | `./tools/export-stl.sh case.scad stl/front.stl -D 'part="front"'` |
| `back` | `./tools/export-stl.sh case.scad stl/back.stl -D 'part="back"'` |

Do not commit `previews/` (generated). Do commit refreshed `stl/*.stl` when
geometry changes.

## Fit / fasteners (defaults)

- Closed overall: **175.8 × 120.4 × 22.2 mm** (W × H × D) — confirm via
  `validate.sh` echoes after param changes
- Lid: 4× M2×8 mm self-tapping into 1.7 mm pilots
- Board: no screws (PCB has no holes); cradle + lid posts
- Side/back USB layouts expect the kit FFC extension for the lateral jog
