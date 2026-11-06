// 16x16 sudoku over the hex digits 0-9 and A-F, in 4x4 boxes. No DOM, so
// Node can test it.
//
// A grid is a Uint8Array of 256 cells in row-major order. 0 is an empty
// cell and 1-16 stand for SYMBOLS[0] through SYMBOLS[15], so the digit 0
// is stored as 1.

export const SIZE = 16;
export const BOX = 4;
export const CELLS = SIZE * SIZE;
export const SYMBOLS = "0123456789ABCDEF";

// Each level allows the techniques of the levels before it, plus its own:
//
//   easy    hidden singles: a symbol with one possible cell in a row,
//           column, or box
//   medium  naked singles: a cell with one possible symbol
//   hard    locked candidates, naked pairs, and hidden pairs
//
// None of them needs guessing.
export const LEVELS = ["easy", "medium", "hard"];

// Easy boards keep more clues than hidden singles strictly need, so more
// than one move is usually open at a time.
export const EASY_CLUES = 120;

const ALL = 0xffff;
const UNIT_COUNT = 3 * SIZE;
const PEER_COUNT = 3 * (SIZE - 1) - 2 * (BOX - 1);
const SEGMENT_COUNT = 2 * SIZE * BOX;

// Solver state is one Int32Array: cell values, then each cell's candidate
// bitmask (0 once the cell is filled), then a bitmask per unit of the
// symbols placed in it, then the count of empty cells. Units 0-15 are rows,
// 16-31 are columns, and 32-47 are boxes.
const CAND = CELLS;
const PLACED = 2 * CELLS;
const EMPTY = PLACED + UNIT_COUNT;
const STATE_LENGTH = EMPTY + 1;

const STUCK = 0;
const PROGRESS = 1;
const CONTRADICTION = -1;

// Now and then a medium or hard board comes out solvable at the level
// below. Dig again with a fresh order, up to this many times, rather than
// label it wrong.
const DIG_ATTEMPTS = 10;

// About 1 in 600 random fills of the diagonal boxes sends the search down
// a branch it takes far too long to back out of. Give up after this many
// nodes and fill again; a typical fill takes about 120.
const FILL_NODES = 1000;

const ROW_OF = new Uint8Array(CELLS);
const COL_OF = new Uint8Array(CELLS);
const BOX_OF = new Uint8Array(CELLS);
const UNIT_CELLS = new Uint8Array(UNIT_COUNT * SIZE);
const PEERS = new Uint8Array(CELLS * PEER_COUNT);
const POPCOUNT = new Uint8Array(ALL + 1);

// A segment is where a line crosses a box: four cells. Segments 0-63 are
// row segments (row * 4 + stack), and 64-127 are column segments
// (64 + column * 4 + band).
const ROW_SEGMENT_OF = new Uint8Array(CELLS);
const COL_SEGMENT_OF = new Uint8Array(CELLS);
const SEGMENT_CELLS = new Uint8Array(SEGMENT_COUNT * BOX);
const SEGMENT_LINE = new Uint8Array(SEGMENT_COUNT);
const SEGMENT_BOX = new Uint8Array(SEGMENT_COUNT);

// Locked candidates work on groups of four segments that split one unit.
// In the first 32 groups the unit is a box, split into rows or columns; a
// symbol confined to one segment leaves the rest of that segment's line.
// In the last 32 the unit is a line, split by box; a symbol confined to
// one segment leaves the rest of that segment's box.
const BOX_GROUPS = 2 * SIZE;
const LINE_GROUPS = 2 * SIZE;
const LOCKED_GROUPS = new Uint8Array((BOX_GROUPS + LINE_GROUPS) * BOX);

function buildTables() {
  const unitFill = new Uint8Array(UNIT_COUNT);
  const segmentFill = new Uint8Array(SEGMENT_COUNT);
  for (let i = 0; i < CELLS; i += 1) {
    const row = Math.floor(i / SIZE);
    const col = i % SIZE;
    const band = Math.floor(row / BOX);
    const stack = Math.floor(col / BOX);
    ROW_OF[i] = row;
    COL_OF[i] = SIZE + col;
    BOX_OF[i] = 2 * SIZE + band * BOX + stack;
    for (const unit of [ROW_OF[i], COL_OF[i], BOX_OF[i]]) {
      UNIT_CELLS[unit * SIZE + unitFill[unit]] = i;
      unitFill[unit] += 1;
    }
    ROW_SEGMENT_OF[i] = row * BOX + stack;
    COL_SEGMENT_OF[i] = SIZE * BOX + col * BOX + band;
    for (const segment of [ROW_SEGMENT_OF[i], COL_SEGMENT_OF[i]]) {
      SEGMENT_CELLS[segment * BOX + segmentFill[segment]] = i;
      segmentFill[segment] += 1;
      SEGMENT_BOX[segment] = BOX_OF[i];
    }
    SEGMENT_LINE[ROW_SEGMENT_OF[i]] = ROW_OF[i];
    SEGMENT_LINE[COL_SEGMENT_OF[i]] = COL_OF[i];
  }

  for (let i = 0; i < CELLS; i += 1) {
    let fill = 0;
    for (let j = 0; j < CELLS; j += 1) {
      const peer =
        ROW_OF[i] === ROW_OF[j] ||
        COL_OF[i] === COL_OF[j] ||
        BOX_OF[i] === BOX_OF[j];
      if (peer && i !== j) {
        PEERS[i * PEER_COUNT + fill] = j;
        fill += 1;
      }
    }
  }

  let group = 0;
  for (let box = 0; box < SIZE; box += 1) {
    const band = Math.floor(box / BOX);
    const stack = box % BOX;
    for (let k = 0; k < BOX; k += 1) {
      LOCKED_GROUPS[group * BOX + k] = (band * BOX + k) * BOX + stack;
      LOCKED_GROUPS[(group + 1) * BOX + k] =
        SIZE * BOX + (stack * BOX + k) * BOX + band;
    }
    group += 2;
  }
  for (let line = 0; line < LINE_GROUPS; line += 1) {
    for (let k = 0; k < BOX; k += 1) {
      LOCKED_GROUPS[group * BOX + k] = line * BOX + k;
    }
    group += 1;
  }

  for (let mask = 1; mask <= ALL; mask += 1) {
    POPCOUNT[mask] = POPCOUNT[mask >> 1] + (mask & 1);
  }
}

buildTables();

const segmentMasks = new Int32Array(SEGMENT_COUNT);
const positions = new Int32Array(SIZE);

// One state per search depth, reused across solves.
const frames = [];

// Bookkeeping for the current solve(). Module state keeps the recursion
// cheap, so solve() isn't reentrant.
const run = {
  nodes: 0,
  nodeLimit: 0,
  limit: 1,
  found: 0,
  solution: null,
  random: null,
};

// Returns a seeded generator (mulberry32) of floats in [0, 1).
export function createRandom(seed) {
  let state = seed >>> 0;
  return function next() {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// Shuffles items in place (Fisher-Yates) and returns them.
export function shuffle(items, random) {
  for (let i = items.length - 1; i > 0; i -= 1) {
    const j = Math.floor(random() * (i + 1));
    const held = items[i];
    items[i] = items[j];
    items[j] = held;
  }
  return items;
}

function frame(depth) {
  if (depth === frames.length) {
    frames.push(new Int32Array(STATE_LENGTH));
  }
  return frames[depth];
}

function indexOfBit(bit) {
  return 31 - Math.clz32(bit);
}

function assign(s, i, bit) {
  s[i] = indexOfBit(bit) + 1;
  s[CAND + i] = 0;
  s[PLACED + ROW_OF[i]] |= bit;
  s[PLACED + COL_OF[i]] |= bit;
  s[PLACED + BOX_OF[i]] |= bit;
  s[EMPTY] -= 1;
  const base = i * PEER_COUNT;
  for (let k = 0; k < PEER_COUNT; k += 1) {
    s[CAND + PEERS[base + k]] &= ~bit;
  }
}

// Loads grid into s. Returns false when two clues clash.
function load(grid, s) {
  s.fill(0);
  s.fill(ALL, CAND, CAND + CELLS);
  s[EMPTY] = CELLS;
  for (let i = 0; i < CELLS; i += 1) {
    const value = grid[i];
    if (value !== 0) {
      const bit = 1 << (value - 1);
      if ((s[CAND + i] & bit) === 0) {
        return false;
      }
      assign(s, i, bit);
    }
  }
  return true;
}

function hiddenSingles(s) {
  let result = STUCK;
  for (let unit = 0; unit < UNIT_COUNT; unit += 1) {
    const base = unit * SIZE;
    let once = 0;
    let twice = 0;
    for (let k = 0; k < SIZE; k += 1) {
      const i = UNIT_CELLS[base + k];
      const cand = s[CAND + i];
      if (s[i] === 0 && cand === 0) {
        return CONTRADICTION;
      }
      twice |= once & cand;
      once |= cand;
    }
    if ((once | s[PLACED + unit]) !== ALL) {
      return CONTRADICTION;
    }
    let hidden = once & ~twice;
    while (hidden !== 0) {
      const bit = hidden & -hidden;
      hidden ^= bit;
      // Two hidden singles in one cell leave the second symbol with no
      // place. The next pass reports that as a contradiction.
      for (let k = 0; k < SIZE; k += 1) {
        const i = UNIT_CELLS[base + k];
        if ((s[CAND + i] & bit) !== 0) {
          assign(s, i, bit);
          result = PROGRESS;
          break;
        }
      }
    }
  }
  return result;
}

function nakedSingles(s) {
  let result = STUCK;
  for (let i = 0; i < CELLS; i += 1) {
    const cand = s[CAND + i];
    if (s[i] === 0) {
      if (cand === 0) {
        return CONTRADICTION;
      }
      if ((cand & (cand - 1)) === 0) {
        assign(s, i, cand);
        result = PROGRESS;
      }
    }
  }
  return result;
}

function inSegment(i, segment) {
  if (segment < SIZE * BOX) {
    return ROW_SEGMENT_OF[i] === segment;
  }
  return COL_SEGMENT_OF[i] === segment;
}

// Eliminations from earlier groups only shrink candidates, so a symbol
// found confined to a segment stays confined and the masks need no refresh.
function lockedCandidates(s) {
  for (let segment = 0; segment < SEGMENT_COUNT; segment += 1) {
    let mask = 0;
    for (let k = 0; k < BOX; k += 1) {
      mask |= s[CAND + SEGMENT_CELLS[segment * BOX + k]];
    }
    segmentMasks[segment] = mask;
  }
  let progress = false;
  for (let group = 0; group < BOX_GROUPS + LINE_GROUPS; group += 1) {
    const base = group * BOX;
    for (let k = 0; k < BOX; k += 1) {
      const segment = LOCKED_GROUPS[base + k];
      let elsewhere = 0;
      for (let j = 0; j < BOX; j += 1) {
        if (j !== k) {
          elsewhere |= segmentMasks[LOCKED_GROUPS[base + j]];
        }
      }
      const confined = segmentMasks[segment] & ~elsewhere;
      if (confined !== 0) {
        const unit =
          group < BOX_GROUPS ? SEGMENT_LINE[segment] : SEGMENT_BOX[segment];
        for (let j = 0; j < SIZE; j += 1) {
          const i = UNIT_CELLS[unit * SIZE + j];
          if ((s[CAND + i] & confined) !== 0 && !inSegment(i, segment)) {
            s[CAND + i] &= ~confined;
            progress = true;
          }
        }
      }
    }
  }
  return progress;
}

// Two cells in a unit with the same two candidates take those two symbols,
// so no other cell in the unit can.
function nakedPairs(s) {
  let progress = false;
  for (let unit = 0; unit < UNIT_COUNT; unit += 1) {
    const base = unit * SIZE;
    for (let a = 0; a < SIZE; a += 1) {
      const pair = s[CAND + UNIT_CELLS[base + a]];
      if (POPCOUNT[pair] === 2) {
        for (let b = a + 1; b < SIZE; b += 1) {
          if (s[CAND + UNIT_CELLS[base + b]] === pair) {
            for (let k = 0; k < SIZE; k += 1) {
              const i = UNIT_CELLS[base + k];
              if (k !== a && k !== b && (s[CAND + i] & pair) !== 0) {
                s[CAND + i] &= ~pair;
                progress = true;
              }
            }
          }
        }
      }
    }
  }
  return progress;
}

// Two symbols that fit only the same two cells of a unit fill those cells,
// so those cells can't hold anything else.
function hiddenPairs(s) {
  let progress = false;
  for (let unit = 0; unit < UNIT_COUNT; unit += 1) {
    const base = unit * SIZE;
    positions.fill(0);
    for (let k = 0; k < SIZE; k += 1) {
      let cand = s[CAND + UNIT_CELLS[base + k]];
      while (cand !== 0) {
        const bit = cand & -cand;
        cand ^= bit;
        positions[indexOfBit(bit)] |= 1 << k;
      }
    }
    for (let x = 0; x < SIZE; x += 1) {
      if (POPCOUNT[positions[x]] === 2) {
        for (let y = x + 1; y < SIZE; y += 1) {
          if (positions[y] === positions[x]) {
            const pair = (1 << x) | (1 << y);
            let spots = positions[x];
            while (spots !== 0) {
              const spot = spots & -spots;
              spots ^= spot;
              const i = UNIT_CELLS[base + indexOfBit(spot)];
              if ((s[CAND + i] & ~pair) !== 0) {
                s[CAND + i] &= pair;
                progress = true;
              }
            }
          }
        }
      }
    }
  }
  return progress;
}

// Applies the simplest technique, up to tier (an index into LEVELS), that
// makes progress.
function step(s, tier) {
  const hidden = hiddenSingles(s);
  if (hidden !== STUCK || tier < 1) {
    return hidden;
  }
  const naked = nakedSingles(s);
  if (naked !== STUCK || tier < 2) {
    return naked;
  }
  if (lockedCandidates(s) || nakedPairs(s) || hiddenPairs(s)) {
    return PROGRESS;
  }
  return STUCK;
}

// Applies techniques up to tier until they stop making progress. Returns
// -1 on a contradiction, otherwise the number of empty cells left.
function deduce(s, tier) {
  let result = PROGRESS;
  while (result === PROGRESS && s[EMPTY] > 0) {
    result = step(s, tier);
  }
  if (result === CONTRADICTION) {
    return -1;
  }
  return s[EMPTY];
}

// Returns the empty cell with the fewest candidates. Naked singles have
// already filled every cell with one candidate, so two is the floor.
function pickCell(s) {
  let best = -1;
  let bestCount = SIZE + 1;
  for (let i = 0; i < CELLS; i += 1) {
    if (s[i] === 0) {
      const count = POPCOUNT[s[CAND + i]];
      if (count < bestCount) {
        best = i;
        bestCount = count;
        if (count === 2) {
          return best;
        }
      }
    }
  }
  return best;
}

function search(depth) {
  run.nodes += 1;
  if (run.nodes > run.nodeLimit) {
    return;
  }
  const s = frames[depth];
  const empty = deduce(s, 1);
  if (empty < 0) {
    return;
  }
  if (empty === 0) {
    run.found += 1;
    if (run.solution === null) {
      run.solution = Uint8Array.from(s.subarray(0, CELLS));
    }
    return;
  }
  const cell = pickCell(s);
  const options = [];
  let rest = s[CAND + cell];
  while (rest !== 0) {
    const bit = rest & -rest;
    rest ^= bit;
    options.push(bit);
  }
  if (run.random !== null) {
    shuffle(options, run.random);
  }
  const next = frame(depth + 1);
  for (const bit of options) {
    next.set(s);
    assign(next, cell, bit);
    search(depth + 1);
    if (run.found >= run.limit || run.nodes > run.nodeLimit) {
      return;
    }
  }
}

// Searches for solutions of grid, guessing where singles run out, and stops
// after `limit` of them.
//
// Options:
//   limit      solutions to look for before stopping (default 1)
//   nodeLimit  search nodes to visit before giving up (default unlimited)
//   random     a createRandom() generator; tries candidates in random order
//
// Returns { count, solution, aborted, nodes }. count stops at limit.
// solution is the first solution found, or null. aborted is true when the
// node limit ran out before count reached limit, so count is a lower bound.
export function solve(grid, options = {}) {
  const { limit = 1, nodeLimit = Infinity, random = null } = options;
  run.nodes = 0;
  run.nodeLimit = nodeLimit;
  run.limit = limit;
  run.found = 0;
  run.solution = null;
  run.random = random;
  if (load(grid, frame(0))) {
    search(0);
  }
  const { found, solution, nodes } = run;
  run.solution = null;
  run.random = null;
  return {
    count: found,
    solution,
    aborted: found < limit && nodes > nodeLimit,
    nodes,
  };
}

function solvesAtTier(grid, tier) {
  const s = frame(0);
  return load(grid, s) && deduce(s, tier) === 0;
}

function levelTier(level) {
  const tier = LEVELS.indexOf(level);
  if (tier < 0) {
    throw new Error(`unknown level ${level}`);
  }
  return tier;
}

// Reports whether the techniques of level, one of LEVELS, fill grid
// without guessing.
export function solvesAt(grid, level) {
  return solvesAtTier(grid, levelTier(level));
}

// Applies the techniques of level to grid until they stop making progress.
// Returns { grid, candidates }: grid with every cell they filled, and each
// empty cell's remaining candidates as a bitmask, where bit k stands for
// SYMBOLS[k]. Returns null when the clues contradict each other.
export function applyTechniques(grid, level) {
  const tier = levelTier(level);
  const s = frame(0);
  if (!load(grid, s) || deduce(s, tier) < 0) {
    return null;
  }
  return {
    grid: Uint8Array.from(s.subarray(0, CELLS)),
    candidates: Uint16Array.from(s.subarray(CAND, CAND + CELLS)),
  };
}

// Returns a random complete grid. The four boxes on the main diagonal share
// no row, column, or box, so they take independent shuffles of the symbols.
// A randomized search fills in the rest.
export function generateSolution(random) {
  const symbols = Array.from({ length: SIZE }, (_, k) => k + 1);
  for (let attempt = 0; attempt < 100; attempt += 1) {
    const grid = new Uint8Array(CELLS);
    for (let box = 0; box < BOX; box += 1) {
      shuffle(symbols, random);
      for (let k = 0; k < SIZE; k += 1) {
        const row = box * BOX + Math.floor(k / BOX);
        const col = box * BOX + (k % BOX);
        grid[row * SIZE + col] = symbols[k];
      }
    }
    const { solution } = solve(grid, { random, nodeLimit: FILL_NODES });
    if (solution !== null) {
      return solution;
    }
  }
  throw new Error("could not fill a 16x16 grid");
}

// Clears clues from solution in pairs that mirror through the center, so
// the clue pattern has 180-degree rotational symmetry. A pair stays
// cleared only if the techniques up to tier still solve the puzzle. Easy
// boards stop at EASY_CLUES.
function dig(solution, tier, random) {
  const puzzle = solution.slice();
  const floor = tier === 0 ? EASY_CLUES : 0;
  const order = shuffle(
    Array.from({ length: CELLS / 2 }, (_, k) => k),
    random,
  );
  let clues = CELLS;
  for (const a of order) {
    if (clues <= floor) {
      break;
    }
    const b = CELLS - 1 - a;
    puzzle[a] = 0;
    puzzle[b] = 0;
    if (solvesAtTier(puzzle, tier)) {
      clues -= 2;
    } else {
      puzzle[a] = solution[a];
      puzzle[b] = solution[b];
    }
  }
  return puzzle;
}

export function countClues(grid) {
  let clues = 0;
  for (const value of grid) {
    if (value !== 0) {
      clues += 1;
    }
  }
  return clues;
}

// Builds the board for seed (a 32-bit unsigned integer) at level, one of
// LEVELS. The same seed and level always build the same board, and boards
// with the same seed share a solution.
//
// The puzzle has one solution, and the techniques of its level reach it.
// Medium and hard boards also stall at the level below, so they need their
// own level's techniques.
//
// Returns { seed, level, puzzle, solution, clues }.
export function generatePuzzle(seed, level) {
  const tier = levelTier(level);
  const random = createRandom(seed);
  const solution = generateSolution(random);
  let puzzle = dig(solution, tier, random);
  for (let attempt = 1; attempt < DIG_ATTEMPTS; attempt += 1) {
    if (tier === 0 || !solvesAtTier(puzzle, tier - 1)) {
      break;
    }
    puzzle = dig(solution, tier, random);
  }
  return { seed, level, puzzle, solution, clues: countClues(puzzle) };
}

// Formats grid as 16 lines of 16 symbols, with "." for an empty cell.
export function formatGrid(grid) {
  const lines = [];
  for (let row = 0; row < SIZE; row += 1) {
    let line = "";
    for (let col = 0; col < SIZE; col += 1) {
      const value = grid[row * SIZE + col];
      line += value === 0 ? "." : SYMBOLS[value - 1];
    }
    lines.push(line);
  }
  return lines.join("\n");
}

// Formats a seed as eight uppercase hex digits.
export function formatSeed(seed) {
  return (seed >>> 0).toString(16).toUpperCase().padStart(8, "0");
}

// Parses one to eight hex digits into a seed. Returns null for anything
// else, including a missing value.
export function parseSeed(text) {
  if (typeof text !== "string" || !/^[0-9a-f]{1,8}$/i.test(text)) {
    return null;
  }
  return Number.parseInt(text, 16);
}

// Returns text as a level name, or null when it isn't one.
export function parseLevel(text) {
  const level = typeof text === "string" ? text.toLowerCase() : "";
  return LEVELS.includes(level) ? level : null;
}
