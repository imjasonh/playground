# Life QR — Game of Life sculpture with a scannable QR roof

`life_qr.scad` turns a text string into a 3D-printable Game of Life solid
whose **top layer is a QR code**. Z is time: the roof is generation 0, and
each step down the stack is one B3/S23 generation forward, so the history is
a valid Life run at any target height. All parameters work with the OpenSCAD
Customizer (Window > Customizer), MakerWorld Parametric Model Maker, or `-D`
overrides on the command line.

## Requirements

- [OpenSCAD](https://openscad.org/) (any recent release; tested with 2021.01+)

## Usage

```bash
# Default: QR for "HELLO", 8 generations down to the build plate
openscad -o life-qr.stl life_qr.scad

# Custom payload and height
openscad -o life-qr.stl \
  -D 'qr_text="https://example.com"' \
  -D 'generations=24' \
  -D 'error_correction="M"' \
  life_qr.scad

# Compact print: smaller cells
openscad -o life-qr.stl \
  -D 'qr_text="HI"' \
  -D 'generations=12' \
  -D 'cell_size=2.5' \
  -D 'layer_height=2.5' \
  life_qr.scad
```

Open `life_qr.scad` in OpenSCAD and use the Customizer to edit `qr_text` and
`generations` live.

## Why time runs downward

Exact *reverse* Life search into an arbitrary QR (seed on the bed → QR on the
roof with time pointing up) is a hard SAT problem: many QR roofs are Gardens
of Eden without margin, and even with margin the chain is typically only one
generation deep (see [`../life-scad/reverse_life.py`](../life-scad/reverse_life.py)).

This file takes the approach that **works for any text and any height in pure
OpenSCAD**:

1. Encode `qr_text` as a QR (generation 0) and put it on the **roof**.
2. Evolve it forward with Conway's rules.
3. Stack each next generation **below** the previous one.

So time points toward the build plate. The roof stays a scannable QR; the
body is the code dissolving into Life. Consecutive layers still satisfy
`below = step(above)`.

Because parents sit *above* their children in this stacking, the 45°
birth-parent ramps from `life-scad` are not enough — keep `strict_supports`
on (the default) so pillars carry every overhang to the bed.

## Parameters

| Parameter | Meaning |
|---|---|
| `qr_text` | Payload encoded into the roof QR (not named `text`, so it does not shadow OpenSCAD's `text()`). |
| `error_correction` | QR ECC level: `L` / `M` / `Q` / `H`. |
| `mask_pattern` | QR mask 0–7. |
| `encoding` | `UTF-8` or `Shift_JIS`. |
| `quiet_zone` | White modules around the QR (4 is the QR minimum for scanning). |
| `life_margin` | Extra dead cells beyond the quiet zone so the pattern can evolve. |
| `generations` | Life steps from the QR roof down to the build plate (model has `generations + 1` layers). |
| `overall_width` / `overall_depth` / `overall_height` | Total model size in mm; `0` = derive from `cell_size` / `layer_height`. |
| `cell_size`, `layer_height` | Per-module footprint and per-generation height. |
| `cell_overlap` | Tiny inflation so edge/corner touches stay manifold. |
| `strict_supports` | Pillars under unsupported cells (default on — needed for downward time). |
| `diagonal_ramps` | Optional ramps to neighbors below; not a substitute for pillars here. |
| `rainbow_preview` | Color layers in the preview (blue = roof/QR). Ignored in STL export. Off by default for faster MakerWorld renders. |

## How it works

1. **QR** — The MIT-licensed [scadqr](https://github.com/xypwn/scadqr) library
   (vendored in `life_qr.scad` for single-file Customizer / MakerWorld use)
   encodes `qr_text` into modules. A small helper turns that into a 0/1 grid,
   padded by `quiet_zone + life_margin`.
2. **Life** — `next_generation` / `evolve` apply B3/S23 with a dead border
   (same rules as `life-scad`).
3. **Stack** — Generation `g` of the QR history is placed at
   `z = (generations - g) · layer_height`, so the QR is on top.
4. **Supports** — A top-down pillar pass fills empty cells under occupied ones
   down to the bed. There is no built-in roof or base plate — use your
   slicer’s brim/raft/skirt if you need bed adhesion.

## Printing tips

- Prefer `cell_size` ≥ 2.5 mm so QR modules survive FDM.
- The roof is open voxels (black QR modules only). White modules are air; for
  a scannable print, add a contrasting solid under-layer in the slicer or
  paint the top after printing if needed.
- Leave `quiet_zone` at 4 unless you know your scanner is forgiving.
- Disable slicer supports when `strict_supports` is on — the pillars are
  already in the mesh.
- Long payloads grow the QR version (module count). A version-1 QR is 21×21;
  with quiet zone 4 and margin 2 the footprint is 33×33 modules.

## Offline exact reverse (time up)

To search for a seed on the bed that evolves *up* into a QR (true reverse
Life), use the MaxSAT tool in [`../life-scad`](../life-scad) — it works for
shallow depths (often a single generation) and is not parametric inside
OpenSCAD:

```bash
pip install -r ../life-scad/requirements.txt
python3 ../life-scad/reverse_life.py --qr 'HI' --generations 1 --margin 2 --openscad-args
```

## Tests

```bash
pip install segno
python3 life_qr_test.py
```

## MakerWorld

Upload `life_qr.scad` as a parametric model. The script is self-contained
(Customizer parameters, then the vendored QR library, then Life evaluation,
then `life_qr();` as the last line).

If you previously saw **Current top level object is empty**, that was from
evaluating QR helpers before they were defined in the file — MakerWorld's
evaluator resolves names in source order. The current file order fixes that.

Keep `generations` and payload length moderate so server-side renders finish
(defaults are tuned for that). Turn `rainbow_preview` on only for local
preview if you want layer colors.
