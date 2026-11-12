// Queens and Two Not Touch puzzles. No DOM, so Node can test it.
//
// Both games put stars on an n×n grid split into n regions. Every row,
// column, and region holds the same number of stars (one in Queens, two in
// Two Not Touch), and no two stars touch, not even at a corner.
//
// Cells are numbered in row-major order. Units are numbered with rows
// first (0 to n-1), then columns (n to 2n-1), then regions (2n to 3n-1).

export const UNKNOWN = 0;
export const STAR = 1;
export const EMPTY = 2;

// Each level sets the board size and the hardest rule (by rank in RULES)
// that a puzzle needs. A puzzle at rank r is solvable with the rules up to
// r and not with the rules below r. Two Not Touch starts at rank 1, because
// the rank 0 rules can't place a star on an empty board: every region has
// more open cells than stars. Two Not Touch skips 8×8, where the 16 stars
// fill all 16 of the 2×2 blocks that tile the board and only two star
// layouts fit.
export const GAMES = {
  queens: {
    name: 'Queens',
    stars: 1,
    levels: {
      easy: {size: 7, rank: 0},
      medium: {size: 8, rank: 1},
      hard: {size: 9, rank: 2},
      expert: {size: 10, rank: 3},
    },
  },
  twonottouch: {
    name: 'Two Not Touch',
    stars: 2,
    levels: {
      easy: {size: 9, rank: 1},
      medium: {size: 10, rank: 1},
      hard: {size: 10, rank: 2},
      expert: {size: 10, rank: 3},
    },
  },
};

export const LEVELS = ['easy', 'medium', 'hard', 'expert'];

// Rules, easiest first. A rule's find function returns steps: cells to fill
// with stars (place), cells to rule out (clear), the cells that justify the
// step (reason), and the units it is about.
//
//   neighbors  a star rules out the eight cells around it
//   full       a unit that has all its stars rules out its other cells
//   forced     a unit with as many open cells as missing stars fills them
//   touch      a star in a cell would leave some unit too little room
//   group      n regions that fit in n rows (or columns) fill those lines,
//              and n lines that fit in n regions fill those regions
//   forcing    a star in a cell, followed by the simple rules, leads to a
//              contradiction
const RULES = [
  {name: 'neighbors', rank: 0, find: findNeighbors},
  {name: 'full', rank: 0, find: findFull},
  {name: 'forced', rank: 0, find: findForced},
  {name: 'touch', rank: 1, find: findTouch},
  {name: 'group', rank: 2, find: findGroup},
  {name: 'forcing', rank: 3, find: findForcing},
];

// Rules whose steps follow from the stars already on the board. Hints
// apply them silently, since the board shows them as dots.
const IMPLIED_RULES = new Set(['neighbors', 'full']);

// Region reshaping gives up on a layout after this many moves and starts
// again from a new solution.
const CLIMB_MOVES = 1500;

// Filling rows with stars gives up after this many search nodes and starts
// again; most fills take a few dozen.
const FILL_NODES = 20000;

export function makeRandom(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function shuffle(items, random) {
  for (let i = items.length - 1; i > 0; i -= 1) {
    const j = Math.floor(random() * (i + 1));
    [items[i], items[j]] = [items[j], items[i]];
  }
  return items;
}

// Bit counts for masks over up to 10 units, the largest board.
const POPCOUNT = new Uint8Array(1 << 10);
for (let mask = 1; mask < POPCOUNT.length; mask += 1) {
  POPCOUNT[mask] = POPCOUNT[mask >> 1] + (mask & 1);
}

function popcount(mask) {
  return POPCOUNT[mask];
}

const subsetCache = new Map();

// Every nonempty proper subset of n items as a bitmask, smallest first, so
// hints name the fewest units.
function subsetsBySize(n) {
  let subsets = subsetCache.get(n);
  if (!subsets) {
    subsets = [];
    for (let mask = 1; mask < (1 << n) - 1; mask += 1) {
      subsets.push(mask);
    }
    subsets.sort((a, b) => popcount(a) - popcount(b) || a - b);
    subsetCache.set(n, subsets);
  }
  return subsets;
}

export function makeShape(size, stars, regions) {
  const cells = size * size;
  const units = [];
  for (let u = 0; u < 3 * size; u += 1) {
    units.push([]);
  }
  const unitsOf = [];
  const neighbors = [];
  for (let cell = 0; cell < cells; cell += 1) {
    const row = Math.floor(cell / size);
    const col = cell % size;
    const cellUnits = [row, size + col, 2 * size + regions[cell]];
    for (const u of cellUnits) {
      units[u].push(cell);
    }
    unitsOf.push(cellUnits);
    const around = [];
    for (let dr = -1; dr <= 1; dr += 1) {
      for (let dc = -1; dc <= 1; dc += 1) {
        const r = row + dr;
        const c = col + dc;
        if ((dr !== 0 || dc !== 0) && r >= 0 && r < size && c >= 0 &&
            c < size) {
          around.push(r * size + c);
        }
      }
    }
    neighbors.push(around);
  }
  return {size, stars, regions: Array.from(regions), units, unitsOf, neighbors};
}

export function touches(size, a, b) {
  return a !== b &&
      Math.abs(Math.floor(a / size) - Math.floor(b / size)) <= 1 &&
      Math.abs((a % size) - (b % size)) <= 1;
}

// Reports whether need stars fit among cells with none touching. Exact for
// need up to 2, which covers both games.
function canFit(size, cells, need) {
  if (need <= 0) {
    return need === 0;
  }
  if (need === 1) {
    return cells.length > 0;
  }
  if (need === 2) {
    for (let i = 0; i < cells.length; i += 1) {
      for (let j = i + 1; j < cells.length; j += 1) {
        if (!touches(size, cells[i], cells[j])) {
          return true;
        }
      }
    }
    return false;
  }
  return cells.length >= need;
}

// Counts the stars and the open cells in each unit.
function countUnits(shape, state) {
  const stars = new Int8Array(shape.units.length);
  const open = new Int8Array(shape.units.length);
  for (let cell = 0; cell < state.length; cell += 1) {
    const counts = state[cell] === STAR ? stars :
        state[cell] === UNKNOWN ? open : null;
    if (counts) {
      for (const u of shape.unitsOf[cell]) {
        counts[u] += 1;
      }
    }
  }
  return {stars, open};
}

function openCells(shape, state, u) {
  return shape.units[u].filter((cell) => state[cell] === UNKNOWN);
}

export function isBroken(shape, state) {
  const {size} = shape;
  for (let cell = 0; cell < state.length; cell += 1) {
    if (state[cell] === STAR &&
        shape.neighbors[cell].some((other) => state[other] === STAR)) {
      return true;
    }
  }
  const {stars, open} = countUnits(shape, state);
  for (let u = 0; u < shape.units.length; u += 1) {
    const need = shape.stars - stars[u];
    if (need < 0 || open[u] < need) {
      return true;
    }
    if (need >= 2 && !canFit(size, openCells(shape, state, u), need)) {
      return true;
    }
  }
  return false;
}

export function isSolved(shape, state) {
  return state.every((value) => value !== UNKNOWN) && !isBroken(shape, state);
}

function findNeighbors(shape, state, all) {
  const steps = [];
  for (let cell = 0; cell < state.length; cell += 1) {
    if (state[cell] !== STAR) {
      continue;
    }
    const clear = shape.neighbors[cell].filter((n) => state[n] === UNKNOWN);
    if (clear.length > 0) {
      steps.push({rule: 'neighbors', place: [], clear, reason: [cell],
        units: []});
      if (!all) {
        break;
      }
    }
  }
  return steps;
}

function findFull(shape, state, all) {
  const steps = [];
  const {stars, open} = countUnits(shape, state);
  for (let u = 0; u < shape.units.length; u += 1) {
    if (stars[u] === shape.stars && open[u] > 0) {
      const clear = openCells(shape, state, u);
      const reason = shape.units[u].filter((cell) => state[cell] === STAR);
      steps.push({rule: 'full', place: [], clear, reason, units: [u]});
      if (!all) {
        break;
      }
    }
  }
  return steps;
}

function findForced(shape, state, all) {
  const steps = [];
  const {stars, open} = countUnits(shape, state);
  for (let u = 0; u < shape.units.length; u += 1) {
    if (open[u] > 0 && open[u] === shape.stars - stars[u]) {
      const place = openCells(shape, state, u);
      steps.push({rule: 'forced', place, clear: [], reason: place,
        units: [u]});
      if (!all) {
        break;
      }
    }
  }
  return steps;
}

function findTouch(shape, state, all) {
  const {size, stars} = shape;
  const steps = [];
  const counts = countUnits(shape, state).stars;
  const removed = new Int32Array(state.length);
  const checked = new Int32Array(shape.units.length);
  let stamp = 0;
  for (let cell = 0; cell < state.length; cell += 1) {
    if (state[cell] !== UNKNOWN) {
      continue;
    }
    stamp += 1;
    // The cells a star here would rule out, including the cell itself,
    // which the star fills.
    const lost = [cell];
    removed[cell] = stamp;
    const remove = (other) => {
      if (state[other] === UNKNOWN && removed[other] !== stamp) {
        removed[other] = stamp;
        lost.push(other);
      }
    };
    shape.neighbors[cell].forEach(remove);
    for (const u of shape.unitsOf[cell]) {
      if (counts[u] + 1 === stars) {
        shape.units[u].forEach(remove);
      }
    }
    let starved = -1;
    for (const other of lost) {
      for (const u of shape.unitsOf[other]) {
        if (checked[u] === stamp) {
          continue;
        }
        checked[u] = stamp;
        const need = stars - counts[u] -
            (shape.unitsOf[cell].includes(u) ? 1 : 0);
        const keep = (c) => state[c] === UNKNOWN && removed[c] !== stamp;
        const fits = need < 2 ?
            need === 0 || (need === 1 && shape.units[u].some(keep)) :
            canFit(size, shape.units[u].filter(keep), need);
        if (!fits) {
          starved = u;
          break;
        }
      }
      if (starved >= 0) {
        break;
      }
    }
    if (starved >= 0) {
      const reason = openCells(shape, state, starved)
          .filter((c) => c !== cell);
      steps.push({rule: 'touch', place: [], clear: [cell], reason,
        units: [starved]});
      if (!all) {
        break;
      }
    }
  }
  return steps;
}

function findGroup(shape, state, all) {
  const {size, regions} = shape;
  // In each pairing, a set of "from" units whose cells that can still hold
  // stars fit inside the same number of "into" units fills those into
  // units. reach[i] is the into units that from unit i reaches; open[j] is
  // the from units with an open cell in into unit j.
  const rowOf = (cell) => Math.floor(cell / size);
  const colOf = (cell) => cell % size;
  const regionOf = (cell) => regions[cell];
  const pairings = [
    {from: regionOf, fromBase: 2 * size, into: rowOf, intoBase: 0},
    {from: regionOf, fromBase: 2 * size, into: colOf, intoBase: size},
    {from: rowOf, fromBase: 0, into: regionOf, intoBase: 2 * size},
    {from: colOf, fromBase: size, into: regionOf, intoBase: 2 * size},
  ];
  const full = 1 << size;
  for (const pairing of pairings) {
    const reach = new Int32Array(size);
    const open = new Int32Array(size);
    for (let cell = 0; cell < state.length; cell += 1) {
      if (state[cell] === EMPTY) {
        continue;
      }
      const from = pairing.from(cell);
      const into = pairing.into(cell);
      reach[from] |= 1 << into;
      if (state[cell] === UNKNOWN) {
        open[into] |= 1 << from;
      }
    }
    // union[mask] is the into units that the from units in mask reach.
    const union = new Int32Array(full);
    for (let mask = 1; mask < full; mask += 1) {
      const low = 31 - Math.clz32(mask & -mask);
      union[mask] = union[mask & (mask - 1)] | reach[low];
    }
    pairing.union = union;
    pairing.open = open;
  }
  const steps = [];
  for (const subset of subsetsBySize(size)) {
    const count = popcount(subset);
    for (const {from, fromBase, into, intoBase, union, open} of pairings) {
      const lines = union[subset];
      if (popcount(lines) !== count) {
        continue;
      }
      let outside = 0;
      for (let j = 0; j < size; j += 1) {
        if (lines & (1 << j)) {
          outside |= open[j] & ~subset;
        }
      }
      if (outside === 0) {
        continue;
      }
      const clear = [];
      const reason = [];
      for (let cell = 0; cell < state.length; cell += 1) {
        if (state[cell] === EMPTY) {
          continue;
        }
        if ((subset >> from(cell)) & 1) {
          reason.push(cell);
        } else if (state[cell] === UNKNOWN && (lines >> into(cell)) & 1) {
          clear.push(cell);
        }
      }
      const units = [];
      for (let i = 0; i < size; i += 1) {
        if (subset & (1 << i)) {
          units.push(fromBase + i);
        }
      }
      for (let i = 0; i < size; i += 1) {
        if (lines & (1 << i)) {
          units.push(intoBase + i);
        }
      }
      steps.push({rule: 'group', place: [], clear, reason, units,
        count});
      if (!all) {
        return steps;
      }
    }
  }
  return steps;
}

function findForcing(shape, state, all) {
  const steps = [];
  for (let cell = 0; cell < state.length; cell += 1) {
    if (state[cell] !== UNKNOWN) {
      continue;
    }
    const trial = Uint8Array.from(state);
    trial[cell] = STAR;
    if (propagate(shape, trial, 0).broken) {
      steps.push({rule: 'forcing', place: [], clear: [cell], reason: [cell],
        units: []});
      if (!all) {
        break;
      }
    }
  }
  return steps;
}

// Applies step to state. Returns false if the step contradicts a cell
// that is already known.
export function applyStep(state, step) {
  let ok = true;
  for (const cell of step.place) {
    if (state[cell] === EMPTY) {
      ok = false;
    }
    state[cell] = STAR;
  }
  for (const cell of step.clear) {
    if (state[cell] === STAR) {
      ok = false;
    }
    state[cell] = EMPTY;
  }
  return ok;
}

// Applies every rule up to maxRank until none finds anything, easiest rule
// first. Mutates state. Reports whether the state broke and the highest
// rank it used (-1 if none).
export function propagate(shape, state, maxRank) {
  let hardest = -1;
  for (;;) {
    if (isBroken(shape, state)) {
      return {broken: true, hardest};
    }
    let progress = false;
    for (const rule of RULES) {
      if (rule.rank > maxRank) {
        break;
      }
      const steps = rule.find(shape, state, true);
      if (steps.length === 0) {
        continue;
      }
      for (const step of steps) {
        if (!applyStep(state, step)) {
          return {broken: true, hardest};
        }
      }
      hardest = Math.max(hardest, rule.rank);
      progress = true;
      break;
    }
    if (!progress) {
      return {broken: false, hardest};
    }
  }
}

function knownCount(state) {
  let count = 0;
  for (const value of state) {
    if (value !== UNKNOWN) {
      count += 1;
    }
  }
  return count;
}

// Fills the stars implied by the stars already in state: the cells around
// each star, and the rest of every unit that has all its stars.
export function implied(shape, state) {
  const result = Uint8Array.from(state);
  for (;;) {
    const steps = [
      ...findNeighbors(shape, result, true),
      ...findFull(shape, result, true),
    ];
    if (steps.length === 0) {
      return result;
    }
    steps.forEach((step) => applyStep(result, step));
  }
}

// Returns the easiest step from state that the board doesn't already show,
// or null if no rule finds one. Steps the stars imply are applied first.
export function nextStep(shape, state) {
  const known = implied(shape, state);
  for (const rule of RULES) {
    if (IMPLIED_RULES.has(rule.name)) {
      continue;
    }
    const [step] = rule.find(shape, known, false);
    if (step) {
      return step;
    }
  }
  return null;
}

// Picks k stars in each row and column with none touching, row by row.
// Returns a Uint8Array with 1 at each star, or null if the search ran out
// of nodes.
function fillStars(size, stars, random) {
  const choices = [];
  for (let a = 0; a < size; a += 1) {
    if (stars === 1) {
      choices.push([a]);
    } else {
      for (let b = a + 2; b < size; b += 1) {
        choices.push([a, b]);
      }
    }
  }
  const colCount = new Int8Array(size);
  const rows = [];
  let nodes = 0;
  const place = (row) => {
    if (row === size) {
      return true;
    }
    const left = size - row;
    for (let c = 0; c < size; c += 1) {
      // A column still missing d stars needs 2d - 1 rows, since its stars
      // can't sit in adjacent rows.
      const missing = stars - colCount[c];
      if (missing > 0 && 2 * missing - 1 > left) {
        return false;
      }
    }
    const previous = row > 0 ? rows[row - 1] : [];
    for (const choice of shuffle([...choices], random)) {
      nodes += 1;
      if (nodes > FILL_NODES) {
        return false;
      }
      const fits = choice.every((c) => colCount[c] < stars &&
          previous.every((p) => Math.abs(p - c) > 1));
      if (!fits) {
        continue;
      }
      choice.forEach((c) => {
        colCount[c] += 1;
      });
      rows.push(choice);
      if (place(row + 1)) {
        return true;
      }
      rows.pop();
      choice.forEach((c) => {
        colCount[c] -= 1;
      });
    }
    return false;
  };
  if (!place(0)) {
    return null;
  }
  const solution = new Uint8Array(size * size);
  rows.forEach((cols, row) => {
    for (const c of cols) {
      solution[row * size + c] = 1;
    }
  });
  return solution;
}

function sideNeighbors(size, cell) {
  const row = Math.floor(cell / size);
  const col = cell % size;
  const result = [];
  if (row > 0) {
    result.push(cell - size);
  }
  if (row < size - 1) {
    result.push(cell + size);
  }
  if (col > 0) {
    result.push(cell - 1);
  }
  if (col < size - 1) {
    result.push(cell + 1);
  }
  return result;
}

// Grows one region from each seed cell, a random edge cell at a time.
function growFrom(size, seeds, random) {
  const regions = new Int8Array(size * size).fill(-1);
  seeds.forEach((cell, i) => {
    regions[cell] = i;
  });
  let left = size * size - seeds.length;
  while (left > 0) {
    const frontier = [];
    for (let cell = 0; cell < regions.length; cell += 1) {
      if (regions[cell] < 0 &&
          sideNeighbors(size, cell).some((n) => regions[n] >= 0)) {
        frontier.push(cell);
      }
    }
    const cell = frontier[Math.floor(random() * frontier.length)];
    const owners = sideNeighbors(size, cell).filter((n) => regions[n] >= 0);
    regions[cell] = regions[owners[Math.floor(random() * owners.length)]];
    left -= 1;
  }
  return regions;
}

// Pairs up regions that share an edge so that every region is in exactly
// one pair. Returns the pair index of each region, or null if there is no
// such pairing.
function pairRegions(count, adjacent, random) {
  const partner = new Int8Array(count).fill(-1);
  const match = () => {
    let best = -1;
    let bestOptions = null;
    for (let r = 0; r < count; r += 1) {
      if (partner[r] >= 0) {
        continue;
      }
      const options = [...adjacent[r]].filter((o) => partner[o] < 0);
      if (bestOptions === null || options.length < bestOptions.length) {
        best = r;
        bestOptions = options;
      }
    }
    if (best < 0) {
      return true;
    }
    for (const other of shuffle(bestOptions, random)) {
      partner[best] = other;
      partner[other] = best;
      if (match()) {
        return true;
      }
      partner[best] = -1;
      partner[other] = -1;
    }
    return false;
  };
  if (!match()) {
    return null;
  }
  const pairOf = new Int8Array(count).fill(-1);
  let next = 0;
  for (let r = 0; r < count; r += 1) {
    if (pairOf[r] < 0) {
      pairOf[r] = next;
      pairOf[partner[r]] = next;
      next += 1;
    }
  }
  return pairOf;
}

// Grows n regions with k stars each around solution, or returns null.
function growRegions(size, stars, solution, random) {
  const seeds = [];
  for (let cell = 0; cell < solution.length; cell += 1) {
    if (solution[cell]) {
      seeds.push(cell);
    }
  }
  shuffle(seeds, random);
  const grown = growFrom(size, seeds, random);
  if (stars === 1) {
    return grown;
  }
  const adjacent = seeds.map(() => new Set());
  for (let cell = 0; cell < grown.length; cell += 1) {
    for (const n of sideNeighbors(size, cell)) {
      if (grown[n] !== grown[cell]) {
        adjacent[grown[cell]].add(grown[n]);
      }
    }
  }
  const pairOf = pairRegions(seeds.length, adjacent, random);
  if (!pairOf) {
    return null;
  }
  return grown.map((r) => pairOf[r]);
}

// Reports whether region stays in one piece without cell.
function connectedWithout(size, regions, region, cell) {
  const members = [];
  for (let c = 0; c < regions.length; c += 1) {
    if (regions[c] === region && c !== cell) {
      members.push(c);
    }
  }
  const seen = new Set([members[0]]);
  const queue = [members[0]];
  while (queue.length > 0) {
    const current = queue.pop();
    for (const n of sideNeighbors(size, current)) {
      if (n !== cell && regions[n] === region && !seen.has(n)) {
        seen.add(n);
        queue.push(n);
      }
    }
  }
  return seen.size === members.length;
}

// How far the rules get from an empty board: cells known with the rules
// below rank, and with the rules up to rank.
function evaluate(size, stars, regions, rank) {
  const shape = makeShape(size, stars, regions);
  const state = new Uint8Array(size * size);
  let low = 0;
  if (rank > 0) {
    propagate(shape, state, rank - 1);
    low = knownCount(state);
  }
  propagate(shape, state, rank);
  return {low, high: knownCount(state)};
}

// Moves edge cells between regions until the rules up to rank solve the
// board and the rules below rank don't. Keeps a move unless it makes the
// board less solvable at rank, or more solvable below it. Returns whether
// it got there; regions holds the result.
function climb(size, stars, solution, regions, rank, random) {
  const cells = size * size;
  const score = ({low, high}) => high * (cells + 1) - low;
  const done = ({low, high}) => high === cells && (rank === 0 || low < cells);
  let current = evaluate(size, stars, regions, rank);
  for (let move = 0; move < CLIMB_MOVES && !done(current); move += 1) {
    const cell = Math.floor(random() * cells);
    if (solution[cell]) {
      continue;
    }
    const from = regions[cell];
    const targets = sideNeighbors(size, cell)
        .map((n) => regions[n])
        .filter((r) => r !== from);
    if (targets.length === 0 ||
        !connectedWithout(size, regions, from, cell)) {
      continue;
    }
    regions[cell] = targets[Math.floor(random() * targets.length)];
    const next = evaluate(size, stars, regions, rank);
    if (score(next) >= score(current)) {
      current = next;
    } else {
      regions[cell] = from;
    }
  }
  return done(current);
}

// Builds the puzzle for game, level, and seed. The same arguments always
// build the same puzzle. The rules of the level solve it, so it has exactly
// one solution.
export function generatePuzzle(game, level, seed) {
  const {stars, levels} = GAMES[game];
  const {size, rank} = levels[level];
  const random = makeRandom(seed);
  for (;;) {
    const solution = fillStars(size, stars, random);
    if (!solution) {
      continue;
    }
    const regions = growRegions(size, stars, solution, random);
    if (!regions) {
      continue;
    }
    if (climb(size, stars, solution, regions, rank, random)) {
      return {
        game,
        level,
        seed,
        size,
        stars,
        regions: Array.from(regions),
        solution: Array.from(solution),
      };
    }
  }
}

// Counts solutions by search, up to limit. Slow; for tests.
export function countSolutions(shape, limit = 2) {
  const {size, stars, regions} = shape;
  const colCount = new Int8Array(size);
  const regionCount = new Int8Array(size);
  const placed = [];
  let found = 0;
  const choices = [];
  for (let a = 0; a < size; a += 1) {
    if (stars === 1) {
      choices.push([a]);
    } else {
      for (let b = a + 2; b < size; b += 1) {
        choices.push([a, b]);
      }
    }
  }
  const search = (row) => {
    if (row === size) {
      found += 1;
      return;
    }
    const previous = row > 0 ? placed[row - 1] : [];
    for (const choice of choices) {
      const cells = choice.map((c) => row * size + c);
      const ok = choice.every((c) => colCount[c] < stars &&
          previous.every((p) => Math.abs(p - c) > 1)) &&
          cells.every((cell) => regionCount[regions[cell]] +
              cells.filter((o) => regions[o] === regions[cell]).length <=
              stars);
      if (!ok) {
        continue;
      }
      choice.forEach((c) => {
        colCount[c] += 1;
      });
      cells.forEach((cell) => {
        regionCount[regions[cell]] += 1;
      });
      placed.push(choice);
      search(row + 1);
      placed.pop();
      choice.forEach((c) => {
        colCount[c] -= 1;
      });
      cells.forEach((cell) => {
        regionCount[regions[cell]] -= 1;
      });
      if (found >= limit) {
        return;
      }
    }
  };
  search(0);
  return found;
}

export function parseGame(value) {
  return Object.hasOwn(GAMES, value) ? value : null;
}

export function parseLevel(value) {
  return LEVELS.includes(value) ? value : null;
}

export function formatSeed(seed) {
  return (seed >>> 0).toString(16).padStart(8, '0');
}

export function parseSeed(value) {
  if (typeof value !== 'string' || !/^[0-9a-f]{1,8}$/i.test(value)) {
    return null;
  }
  return Number.parseInt(value, 16) >>> 0;
}
