# life-stl design notes

Context for future maintainers: the geometry model, why gusset mode exists,
what the gates protect, and approaches that were evaluated and rejected.

## Geometry model

- Life runs on a finite board (dead edges, no wrap-around) — `life.rs`.
- Generation `g` becomes a layer of cube voxels at `z = base_layers + g`
  (`build_life_volume` in `lib.rs`); a solid base plate anchors the bottom.
- The base plate **shrink-wraps** to the bounding box of the model's XY
  projection plus `base_margin` cells (a rectangle: connected, and under the
  center of mass → table-stable). `full_base` restores the whole board;
  breakaway mode forces it because supports may land on the bed anywhere.
- Meshing emits face-culled cubes (`mesh.rs`); support/brace geometry is
  appended as extra closed shells. Overlapping shells are fine — slicers
  union them.

## The core theorem: birth ≡ overhang, and every birth is 45°-supported

A voxel at `(x, y, z)` has empty space directly below iff the cell was **born**
at generation `z` (a survivor has itself below; S23). B3 says a birth has
**exactly three live neighbors** in its Moore neighborhood one generation
earlier — three voxels diagonally below it. Two consequences:

1. **Strict-vertical overhangs are exactly the births.** Any support strategy
   pays one contact per birth; chaotic (interesting) patterns are precisely
   the ones with many births. External supports and interestingness are
   fundamentally in tension.
2. **The stack is always Moore-supported.** No Life voxel is ever more than
   one diagonal step from material below — the FDM 45° rule. The stack never
   *needed* external supports; it needed the diagonal contacts to be real
   solid connections instead of zero-area cube edges.

Gusset mode (`gusset.rs`) is consequence 2 made printable: a small leaning
strut (≈35° max from vertical) from each birth down into each of its parents.
Every voxel then traces ancestry to generation 0 on the base plate, so the
print is one connected piece with nothing to remove. Orphan analysis in gusset
mode uses this causal connectivity (`count_orphan_life_causal`); breakaway and
raw modes use face-only connectivity (`metrics::count_orphan_life`) because
without braces, diagonal contact is not a physical joint.

## Support modes

| Mode | Strategy | Cleanup | Works for |
|------|----------|---------|-----------|
| `gusset` (default) | Causality braces to birth parents | none | everything, including gliders/spaceships |
| `breakaway` | Cura-style trees / pillars, needle tips, physics-sized trunks | snap-off; gated by removability score | mildly chaotic patterns |
| `raw` | nothing | none | overhang-free stacks (still-life gardens) |

Breakaway is kept because it produces a clean Life-only sculpture after
cleanup (no visible braces). Its removability gate (`removal.rs`) scores
rest-on-model landings (double-tapered, capped by `max_rest_on_model`),
trunks trapped in cavities, tip contacts in enclosed pockets, and tip density.

## The complexity gate

`complexity.rs` simulates until the first repeated grid. If the attractor
period ≤ `max_boring_period` and quiescence starts before
`max(min_active_generations, depth × min_active_fraction)`, the run is
rejected — with the default fraction of 1.0, a print-worthy pattern must stay
active for its **entire** height. A pattern that settles partway up extrudes a
static tower above the interesting part. Still-life gardens
(`Pattern::Random`) are exempt: stability is their point.

Both gates behave the same at the CLI: seed search retries until they pass;
an explicit seed still writes the STL but exits non-zero.

## Evaluated and rejected

- **External supports for movers (gliders, spaceships).** Every layer of
  motion is births; tree routing lands branches on the model or cages the
  shape. Made obsolete by gusset mode rather than by weakening the gate.
- **Backward search from still-life ash** (enumerate predecessors of a target
  end-state, pruning unsupportable transitions). Zero-birth predecessors of
  still lifes exist (spark cells that die in one step) but chain only ~1
  generation deep before requiring births; long predecessor chains need
  SAT-style search, and gusset mode removed the motivation.
- **Classic methuselahs at print scale.** R-pentomino (~1103 gens) and acorn
  (~5206 gens) outlive any printable Z, which is exactly what makes truncated
  acorn a good gusset print: it never settles inside the stack. R-pentomino on
  small bounded boards settles around gen 19 and fails the full-height gate.
- **Weakening the complexity gate to ship more examples.** Print review
  consistently rejected anything that goes quiescent partway up; the gate
  default (`min_active_fraction = 1.0`) encodes that judgment.

## Print notes (FDM, 0.4 mm nozzle)

- Default `--cell 4.0` mm (min 2.0). Bambu A1 Mini build volume is 180³ mm →
  44 generations plus one base layer at 4 mm.
- Gusset prints have flat cube undersides bridging one cell (4 mm) anchored on
  braces — enable bridging/cooling, disable slicer supports (the braces are
  the supports).
- Gusset width default 1.8 mm ≈ 4–5 perimeters; braces are decorative-strength,
  fine for a static sculpture.
- Concrete A1 Mini + generic PLA settings: `docs/printing-a1mini.md`.
  `tools/make_bambu_3mf.py` packages an STL plus those settings as a Bambu
  Studio project .3mf (flattens official profiles, applies overrides).
