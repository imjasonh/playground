/*
 * Conway's Game of Life as a 3D solid — Z axis is time.
 *
 * The seed grid (generation 0) sits on the build plate. Each Game of Life
 * generation is computed in pure OpenSCAD functions and stacked as the next
 * layer up, so the finished solid is the space-time history of the automaton.
 *
 * All parameters below work with the OpenSCAD Customizer
 * (Window > Customizer).
 */

/* [Seed — generation 0 (the bottom layer)] */

// Named starting specimen. Spaceships: glider, lwss. Methuselahs (grow chaotically for many generations; give them a large margin): r-pentomino, b-heptomino, pi-heptomino, acorn, diehard. Oscillators: toad (period 2), beacon (period 2), pulsar (period 3), pentadecathlon (period 15). Choose custom to use the seed_pattern field below.
preset = "glider-and-block"; // [glider-and-block, glider, lwss, r-pentomino, b-heptomino, pi-heptomino, acorn, diehard, toad, beacon, pulsar, pentadecathlon, custom]
// Empty cells added around a named preset so the pattern has room to evolve
preset_margin = 5; // [0:30]
// Custom initial grid, used when preset is "custom": rows separated by "/", live cells are 1 # O o X or x, dead cells anything else (use .). Row 0 is at y=0, column 0 at x=0. Short rows are padded with dead cells. To put a letter/QR on the *roof*, generate this string with reverse_life.py so the seed evolves into that target.
seed_pattern = "........../..1......./...1....../.111....../........../.......11./.......11./........../........../..........";

// Ignore the seed above and start from a random grid instead
random_seed = false;
// Random grid size (rows x columns)
random_rows = 16; // [4:64]
random_cols = 16; // [4:64]
// Fraction of cells alive in the random seed
random_density = 0.35; // [0.05:0.05:0.9]
// Change this number to get a different (but repeatable) random pattern
random_pattern_number = 42;

/* [Simulation] */

// Number of generations to simulate above the seed layer
generations = 24; // [1:200]

/* [Dimensions] */

// Overall model width along X in mm (0 = derive from cell_size)
overall_width = 0;
// Overall model depth along Y in mm (0 = derive from cell_size)
overall_depth = 0;
// Overall model height along Z in mm (0 = derive from layer_height)
overall_height = 0;
// Cell footprint in mm, used when overall width/depth are 0
cell_size = 3;
// Height of one generation in mm, used when overall height is 0. Keep it at least as large as cell_size: ramp undersides slope at atan(layer_height / cell_size), so equal values give exactly 45 degrees.
layer_height = 3;
// Tiny inflation of every cube, in mm, so the mesh stays manifold where cubes touch only along an edge or corner. Keep it small; it is invisible at the default 0.02.
cell_overlap = 0.02;
// Optional solid base plate under the seed layer, in mm (0 = none)
base_thickness = 0;

/* [Supports] */

// Fill the space between an overhanging cell and each of its supporting neighbors in the layer below with a solid sloped ramp. The underside of a ramp is an exact 45-degree slope when cell size equals layer height. Only added where a cell has nothing directly beneath it; by the Life rules every such cell has at least one supporter in the 3x3 below.
diagonal_ramps = true;
// Instead of ramps, add vertical pillars beneath any cell with no material directly underneath, cascading to the base. Stronger and more material than ramps; useful when layer_height is much larger than cell_size and ramp slopes would get too steep.
strict_supports = false;

/* [Preview] */

// Color layers by generation in the preview (ignored in STL export)
rainbow_preview = true;

/* [Hidden] */

function random_row(r) =
    [for (v = rands(0, 1, random_cols, random_pattern_number + r * 7919))
        v < random_density ? 1 : 0];

// --- Seed string parsing ----------------------------------------------------

function split_rows(s, i = 0, cur = "", out = []) =
    i >= len(s)
        ? concat(out, [cur])
        : s[i] == "/"
            ? split_rows(s, i + 1, "", concat(out, [cur]))
            : split_rows(s, i + 1, str(cur, s[i]), out);

function is_alive(ch) =
    ch == "1" || ch == "#" || ch == "O" || ch == "o" || ch == "X" || ch == "x";

preset_library = [
    ["glider-and-block", ".#....../..#...../###...../......../......##/......##"],
    ["glider",           ".#./..#/###"],
    ["lwss",             "#..#./....#/#...#/.####"],
    ["r-pentomino",      ".##/##./.#."],
    ["b-heptomino",      "#.##/###./.#.."],
    ["pi-heptomino",     "###/#.#/#.#"],
    ["acorn",            ".#...../...#.../##..###"],
    ["diehard",          "......#./##....../.#...###"],
    ["toad",             ".###/###."],
    ["beacon",           "##../##../..##/..##"],
    ["pulsar",           "..###...###../............./#....#.#....#/#....#.#....#/#....#.#....#/..###...###../............./..###...###../#....#.#....#/#....#.#....#/#....#.#....#/............./..###...###.."],
    ["pentadecathlon",   "..#....#../##.####.##/..#....#.."],
];

preset_idx = search([preset], preset_library)[0];

// The assert is part of the expression so an unknown name fails immediately
// at evaluation time with a clear message.
active_pattern =
    preset == "custom" ? seed_pattern
    : assert(preset_idx != [], str("Unknown preset \"", preset, "\""))
      preset_library[preset_idx][1];
margin = preset == "custom" ? 0 : preset_margin;

seed_rows = [for (row = split_rows(active_pattern)) if (len(row) > 0) row];
seed_cols = max([for (row = seed_rows) len(row)]);

grid0 = random_seed
    ? [for (r = [0 : random_rows - 1]) random_row(r)]
    : [for (r = [0 : len(seed_rows) + 2 * margin - 1])
          [for (c = [0 : seed_cols + 2 * margin - 1])
              let (pr = r - margin, pc = c - margin)
              pr >= 0 && pr < len(seed_rows)
              && pc >= 0 && pc < len(seed_rows[pr])
              && is_alive(seed_rows[pr][pc]) ? 1 : 0]];

rows = len(grid0);
cols = len(grid0[0]);

assert(rows >= 1 && cols >= 1, "Seed grid must not be empty");

// --- Game of Life rules ---------------------------------------------------

// Cells beyond the border are dead.
function cell(g, r, c) =
    (r < 0 || r >= rows || c < 0 || c >= cols) ? 0 : g[r][c];

function live_neighbors(g, r, c) =
    cell(g, r - 1, c - 1) + cell(g, r - 1, c) + cell(g, r - 1, c + 1) +
    cell(g, r,     c - 1) +                     cell(g, r,     c + 1) +
    cell(g, r + 1, c - 1) + cell(g, r + 1, c) + cell(g, r + 1, c + 1);

function next_generation(g) =
    [for (r = [0 : rows - 1])
        [for (c = [0 : cols - 1])
            let (n = live_neighbors(g, r, c))
            g[r][c] == 1
                ? (n == 2 || n == 3 ? 1 : 0)  // survival
                : (n == 3 ? 1 : 0)]];         // birth

// List of grids: [generation 0, generation 1, ..., generation n]
function evolve(g, n, acc = []) =
    n < 0 ? acc : evolve(next_generation(g), n - 1, concat(acc, [g]));

history = evolve(grid0, generations);

// --- Strict supports ----------------------------------------------------------
// Cell values in the final stack: 0 = empty, 1 = live cell, 2 = added support.
// Life with a dead border never needs supports at 45 degrees (survivors sit on
// themselves, births sit on their 3 parents), so pillars are only generated in
// strict mode: a support cell goes directly beneath every occupied cell that
// has nothing directly underneath.

function augment_below(below, above) =
    [for (r = [0 : rows - 1])
        [for (c = [0 : cols - 1])
            below[r][c] != 0 ? below[r][c]
            : above[r][c] != 0 ? 2 : 0]];

// Sweep top-down so new support cells cascade all the way to the base layer.
function support_pass(stack, g) =
    g <= 0 ? stack
    : support_pass(
        [for (i = [0 : len(stack) - 1])
            i == g - 1 ? augment_below(stack[g - 1], stack[g]) : stack[i]],
        g - 1);

final_stack = strict_supports ? support_pass(history, len(history) - 1) : history;

support_count = len([for (g = [0 : len(final_stack) - 1],
                          r = [0 : rows - 1], c = [0 : cols - 1])
                        if (final_stack[g][r][c] == 2) 1]);

// --- 45-degree ramps ----------------------------------------------------------
// For every occupied cell with nothing directly beneath it, list each occupied
// neighbor in the 3x3 of the layer below; a solid ramp (hull of the two cubes)
// is rendered per pair. With strict_supports on, pillars make every cell
// directly supported, so this list is empty.

ramp_pairs = diagonal_ramps
    ? [for (g = [1 : len(final_stack) - 1],
            r = [0 : rows - 1], c = [0 : cols - 1])
          if (final_stack[g][r][c] != 0 && final_stack[g - 1][r][c] == 0)
              for (dr = [-1 : 1], dc = [-1 : 1])
                  let (rr = r + dr, cc = c + dc)
                  if (!(dr == 0 && dc == 0)
                      && rr >= 0 && rr < rows && cc >= 0 && cc < cols
                      && final_stack[g - 1][rr][cc] != 0)
                      [g, r, c, rr, cc]]
    : [];

// --- Geometry ---------------------------------------------------------------

cell_x = overall_width  > 0 ? overall_width  / cols : cell_size;
cell_y = overall_depth  > 0 ? overall_depth  / rows : cell_size;
cell_z = overall_height > 0 ? overall_height / (generations + 1) : layer_height;

total_x = cell_x * cols;
total_y = cell_y * rows;
total_z = cell_z * (generations + 1);

echo(str("Seed: ", random_seed ? "random" : preset,
         ", grid: ", cols, " x ", rows, ", generations: ", generations + 1));
echo(str("Model size: ", total_x, " x ", total_y, " x ", total_z, " mm"));
echo(str("Support pillars: ", support_count, ", 45-degree ramps: ", len(ramp_pairs)));

// Ramp undersides slope at atan(cell_z / cell_xy), so the layer height must be
// at least the cell footprint for every overhang to stay at 45 degrees or
// steeper (verified empirically on exported meshes).
min_cell_z = max(cell_x, cell_y);
if (len(ramp_pairs) > 0 && cell_z < min_cell_z - 0.001)
    echo(str("WARNING: layer height ", cell_z, " mm is less than the cell",
             " footprint ", min_cell_z, " mm, so ramp undersides will be",
             " shallower than 45 degrees (", atan(cell_z / min_cell_z),
             " degrees). Increase layer_height/overall_height or enable",
             " strict_supports."));

function layer_color(g) =
    let (t = generations == 0 ? 0 : g / generations)
    [0.2 + 0.8 * t, 0.4, 1.0 - 0.8 * t];

module life_cell(g, r, c) {
    ov = cell_overlap;
    translate([c * cell_x - ov, r * cell_y - ov, g * cell_z - ov])
        cube([cell_x + 2 * ov, cell_y + 2 * ov, cell_z + 2 * ov]);
}

module ramp(g, r, c, rr, cc) {
    hull() {
        life_cell(g, r, c);
        life_cell(g - 1, rr, cc);
    }
}

module life_cells() {
    for (g = [0 : len(final_stack) - 1], r = [0 : rows - 1], c = [0 : cols - 1])
        if (final_stack[g][r][c] != 0) {
            if (final_stack[g][r][c] == 2)
                color("Gray") life_cell(g, r, c);
            else if (rainbow_preview)
                color(layer_color(g)) life_cell(g, r, c);
            else
                life_cell(g, r, c);
        }
    for (p = ramp_pairs) {
        if (rainbow_preview)
            color(layer_color(p[0] - 0.5)) ramp(p[0], p[1], p[2], p[3], p[4]);
        else
            ramp(p[0], p[1], p[2], p[3], p[4]);
    }
}

module game_of_life() {
    // Clip the overlap so the outer faces stay flat and the footprint honest.
    intersection() {
        life_cells();
        cube([total_x, total_y, total_z]);
    }
    if (base_thickness > 0)
        translate([0, 0, -base_thickness])
            cube([total_x, total_y, base_thickness]);
}

game_of_life();
