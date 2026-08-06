# OpenSCAD skill tools

Vendored from
[mitsuhiko/agent-stuff `skills/openscad`](https://github.com/mitsuhiko/agent-stuff/tree/main/skills/openscad)
(see `UPSTREAM_SKILL.md`).

Local delta: `common.sh` wraps OpenSCAD with `xvfb-run` when `DISPLAY` is
unset so headless CI / cloud agents can preview and export.

| Script | Purpose |
|--------|---------|
| `validate.sh` | Syntax check + echo output |
| `preview.sh` | Single-angle PNG |
| `multi-preview.sh` | front / back / left / right / top / iso |
| `export-stl.sh` | STL export |
| `extract-params.sh` | Customizer parameter table / JSON |
| `render-with-params.sh` | STL/PNG from a JSON param file |

Use via [`../AGENTS.md`](../AGENTS.md) / [`../render.sh`](../render.sh) /
[`../export-stl.sh`](../export-stl.sh).
