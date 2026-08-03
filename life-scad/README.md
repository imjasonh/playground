# Conway's Game of Life in OpenSCAD — Z axis is time

`game_of_life.scad` turns a Game of Life run into a single 3D solid. The seed
grid is the bottom layer, and every generation is computed in pure OpenSCAD
functions and stacked one layer up, so the finished model is the space-time
history of the automaton. All parameters work with the OpenSCAD Customizer
(Window > Customizer) or `-D` overrides on the command line.

## Requirements

- [OpenSCAD](https://openscad.org/) (any recent release; tested with 2021.01)

## Usage

Open `game_of_life.scad` in OpenSCAD, or render from the command line:

```bash
# Default: a glider and a block on a 10x10 grid, 24 generations
openscad -o gol.stl game_of_life.scad

# Fixed overall dimensions (cells are sized to fit), with a base plate
openscad -o gol.stl \
  -D 'overall_width=50' -D 'overall_depth=50' -D 'overall_height=100' \
  -D 'base_thickness=2' \
  game_of_life.scad

# Random 16x16 soup, reproducible via random_pattern_number
openscad -o gol.stl -D 'random_seed=true' -D 'generations=30' game_of_life.scad

# A named specimen: the r-pentomino methuselah with room to grow
openscad -o gol.stl -D 'preset="r-pentomino"' -D 'preset_margin=8' \
  -D 'generations=40' game_of_life.scad
```

## Parameters

| Parameter | Meaning |
|---|---|
| `preset` | Named starting specimen, shown as a dropdown in the Customizer and on MakerWorld. Spaceships: `glider`, `lwss`. Methuselahs: `r-pentomino`, `b-heptomino`, `pi-heptomino`, `acorn`, `diehard`. Oscillators: `toad`, `beacon`, `pulsar` (period 3), `pentadecathlon` (period 15). `glider-and-block` is the default demo; `custom` uses `seed_pattern` below. |
| `preset_margin` | Empty cells added on every side of a named preset so it has room to evolve. Methuselahs benefit from a large margin (8–15); oscillators need only a few cells. |
| `seed_pattern` | Generation 0 as a single string, used when `preset` is `custom`: rows separated by `/`, live cells `1` `#` `O` `o` `X` `x`, dead cells anything else (`.` by convention). Short rows are padded with dead cells. Example glider: `".#./..#/###"` |
| `random_seed`, `random_rows`, `random_cols`, `random_density`, `random_pattern_number` | Replace `seed` with a reproducible random grid. |
| `generations` | Number of steps simulated above the seed layer. Cells beyond the grid border are dead. |
| `overall_width` / `overall_depth` / `overall_height` | Total model size in mm. Set to `0` to derive size from `cell_size` / `layer_height` instead. |
| `cell_size`, `layer_height` | Per-cell footprint and per-generation height, used when the overall dimensions are `0`. Keep `layer_height` ≥ `cell_size` (see ramps below); the model warns in the console if it isn't. |
| `cell_overlap` | Tiny inflation (default 0.02 mm, invisible) keeping the mesh manifold where cubes touch only along an edge or corner. |
| `base_thickness` | Optional solid plate under the seed layer to tie disconnected towers together for printing. |
| `diagonal_ramps` | On by default. Fills the gap between an overhanging cell and each of its supporting neighbors in the layer below with a solid sloped ramp, so no cell relies on bridging. By the Life rules every cell without material directly beneath it has at least one supporter in the 3×3 below (a survivor sits on itself, a birth on its 3 parents). Every ramp underside slopes at `atan(layer_height / cell_size)` — exactly 45° with the default cubic cells, steeper with taller layers — verified by measuring all downward-facing triangles of exported STLs. |
| `strict_supports` | Alternative to ramps: vertical pillars beneath any cell with no material directly underneath, cascading to the base. More material; useful if you want cube-shaped cells (`layer_height` = `cell_size`) without shallow diagonal ramps. Pillars show up gray in the preview. |
| `rainbow_preview` | Colors layers by generation in the preview (blue = seed, yellow = last). Ignored in STL export. |

## How it works

The simulation lives in three functions: `live_neighbors` counts the eight
neighbors (cells beyond the border are dead), `next_generation` applies the
standard B3/S23 rules, and `evolve` tail-recursively accumulates the list of grids.
The geometry pass then places one cube per live cell at
`(col * cell_x, row * cell_y, generation * cell_z)`, adds a `hull()` ramp
between every overhanging cell and each of its supporters in the layer below,
and clips everything to the overall bounding box.

The generation history produced by the SCAD functions has been verified
cell-for-cell against an independent Python implementation of the rules.

## MakerWorld

The file is compatible with MakerWorld's parametric (OpenSCAD) model support:
it is a single self-contained file with no external includes, and every
parameter uses plain Customizer types (numbers, booleans, and one string).
The seed is deliberately a string rather than a 2D array because neither the
OpenSCAD Customizer nor MakerWorld can present nested arrays as an editable
control. Keep `generations` and the grid size moderate so renders stay within
MakerWorld's server-side time limit.
