# Frequency-2 spherical pentakis snub dodecahedron

OpenSCAD + STL for a 560-triangle geodesic built from the snub dodecahedron:

1. Start with a **snub dodecahedron** (80 triangles + 12 pentagons).
2. **Kis** each pentagon (split into 5 triangles) and raise the new apex to the circumsphere → **pentakis snub dodecahedron** (140 triangles).
3. Split **each** triangle into 4 (edge midpoints) and project onto the sphere → **560 triangles**.

## Files

| File | Role |
|------|------|
| `geodesic.stl` | Triangle mesh (ASCII STL) — viewable in GitHub’s 3D viewer |
| `geodesic.scad` | Same mesh as an OpenSCAD `polyhedron` |
| `generate.py` | Regenerates the `.scad` and `.stl` from the construction above |

## Regenerate

```bash
python3 generate.py
```

Requires `numpy`. Output circumradius defaults to 50.

## Open in OpenSCAD

```bash
openscad geodesic.scad
```
