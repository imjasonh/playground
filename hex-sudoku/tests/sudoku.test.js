import test from "node:test";
import assert from "node:assert/strict";

import {
  BOX,
  CELLS,
  EASY_CLUES,
  LEVELS,
  SIZE,
  SYMBOLS,
  applyTechniques,
  countClues,
  createRandom,
  formatGrid,
  formatSeed,
  generatePuzzle,
  generateSolution,
  parseLevel,
  parseSeed,
  shuffle,
  solve,
  solvesAt,
} from "../src/sudoku.js";

const SEEDS = [1, 2, 0x4f2a9c01, 0xdeadbeef, 0xffffffff];

// Checks every row, column, and box without going through the solver.
function isCompleteSudoku(grid) {
  for (let n = 0; n < SIZE; n += 1) {
    const row = new Set();
    const col = new Set();
    const box = new Set();
    for (let k = 0; k < SIZE; k += 1) {
      row.add(grid[n * SIZE + k]);
      col.add(grid[k * SIZE + n]);
      const r = Math.floor(n / BOX) * BOX + Math.floor(k / BOX);
      const c = (n % BOX) * BOX + (k % BOX);
      box.add(grid[r * SIZE + c]);
    }
    for (const group of [row, col, box]) {
      if (group.size !== SIZE || group.has(0)) {
        return false;
      }
    }
  }
  return true;
}

// A valid grid built from a formula: each row shifts the one before it.
function patternGrid() {
  const grid = new Uint8Array(CELLS);
  for (let r = 0; r < SIZE; r += 1) {
    for (let c = 0; c < SIZE; c += 1) {
      grid[r * SIZE + c] =
        ((BOX * (r % BOX) + Math.floor(r / BOX) + c) % SIZE) + 1;
    }
  }
  return grid;
}

function isMirrored(puzzle) {
  for (let i = 0; i < CELLS; i += 1) {
    if ((puzzle[i] === 0) !== (puzzle[CELLS - 1 - i] === 0)) {
      return false;
    }
  }
  return true;
}

const ROWS = [];
const COLS = [];
const BOXES = [];
for (let n = 0; n < SIZE; n += 1) {
  const row = [];
  const col = [];
  const box = [];
  for (let k = 0; k < SIZE; k += 1) {
    row.push(n * SIZE + k);
    col.push(k * SIZE + n);
    const r = Math.floor(n / BOX) * BOX + Math.floor(k / BOX);
    box.push(r * SIZE + (n % BOX) * BOX + (k % BOX));
  }
  ROWS.push(row);
  COLS.push(col);
  BOXES.push(box);
}
const LINES = [...ROWS, ...COLS];
const UNITS = [...LINES, ...BOXES];

// Random subsets of a solution's clues. Most have many solutions and stall
// every level, which leaves the techniques plenty to work on.
function sparsePuzzles() {
  const puzzles = [];
  for (let seed = 1; seed <= 40; seed += 1) {
    const random = createRandom(seed);
    const solution = generateSolution(random);
    const puzzle = solution.slice();
    const order = shuffle(
      Array.from({ length: CELLS }, (_, k) => k),
      random,
    );
    for (const i of order.slice(70 + (seed % 6) * 10)) {
      puzzle[i] = 0;
    }
    puzzles.push({ solution, puzzle });
  }
  return puzzles;
}

// Names a move of level's techniques that is still open after
// applyTechniques, or returns null. Written out longhand so it shares no
// code with the solver.
function openMove({ grid, candidates }, level) {
  const options = Array.from({ length: CELLS }, (_, i) => {
    const symbols = [];
    for (let k = 0; k < SIZE && grid[i] === 0; k += 1) {
      if ((candidates[i] & (1 << k)) !== 0) {
        symbols.push(k);
      }
    }
    return symbols;
  });
  const spotsOf = (unit, k) => unit.filter((i) => options[i].includes(k));

  for (const unit of UNITS) {
    for (let k = 0; k < SIZE; k += 1) {
      if (spotsOf(unit, k).length === 1) {
        return `hidden single ${SYMBOLS[k]}`;
      }
    }
  }
  if (level === "easy") {
    return null;
  }
  if (options.some((symbols) => symbols.length === 1)) {
    return "naked single";
  }
  if (level === "medium") {
    return null;
  }

  for (const box of BOXES) {
    for (const line of LINES) {
      const shared = box.filter((i) => line.includes(i));
      for (let k = 0; k < SIZE && shared.length > 0; k += 1) {
        const inShared = spotsOf(shared, k).length > 0;
        const restOfBox = box.some(
          (i) => !shared.includes(i) && options[i].includes(k),
        );
        const restOfLine = line.some(
          (i) => !shared.includes(i) && options[i].includes(k),
        );
        if (inShared && restOfBox !== restOfLine) {
          return `locked candidate ${SYMBOLS[k]}`;
        }
      }
    }
  }
  for (const unit of UNITS) {
    for (const a of unit) {
      for (const b of unit) {
        const pair = options[a];
        const same = a < b && pair.length === 2 && pair.join() === options[b].join();
        const others = unit.filter((i) => i !== a && i !== b);
        if (same && others.some((i) => pair.some((k) => options[i].includes(k)))) {
          return "naked pair";
        }
      }
    }
    for (let x = 0; x < SIZE; x += 1) {
      for (let y = x + 1; y < SIZE; y += 1) {
        const spots = spotsOf(unit, x);
        const same = spots.length === 2 && spots.join() === spotsOf(unit, y).join();
        if (same && spots.some((i) => options[i].length > 2)) {
          return "hidden pair";
        }
      }
    }
  }
  return null;
}

test("createRandom repeats for a seed and differs across seeds", () => {
  const take = (random) => Array.from({ length: 8 }, () => random());
  const first = take(createRandom(42));
  assert.deepEqual(take(createRandom(42)), first);
  assert.notDeepEqual(take(createRandom(43)), first);
  for (const value of first) {
    assert.ok(value >= 0 && value < 1);
  }
});

test("shuffle reorders items without losing any", () => {
  const sorted = Array.from({ length: 40 }, (_, k) => k);
  const items = shuffle(sorted.slice(), createRandom(7));
  assert.notDeepEqual(items, sorted);
  assert.deepEqual(
    items.slice().sort((a, b) => a - b),
    sorted,
  );
});

test("patternGrid is a valid sudoku, so the checker accepts real grids", () => {
  assert.equal(isCompleteSudoku(patternGrid()), true);
  const broken = patternGrid();
  broken[0] = broken[1];
  assert.equal(isCompleteSudoku(broken), false);
});

test("generateSolution fills a valid grid", () => {
  for (const seed of SEEDS) {
    assert.equal(isCompleteSudoku(generateSolution(createRandom(seed))), true);
  }
});

test("solve fills the empty cells of a grid", () => {
  const full = patternGrid();
  const puzzle = full.slice();
  for (let i = 0; i < CELLS; i += 3) {
    puzzle[i] = 0;
  }
  const { count, solution, aborted } = solve(puzzle);
  assert.equal(count, 1);
  assert.equal(aborted, false);
  assert.equal(isCompleteSudoku(solution), true);
  for (let i = 0; i < CELLS; i += 1) {
    if (puzzle[i] !== 0) {
      assert.equal(solution[i], puzzle[i]);
    }
  }
});

test("solve stops at the limit when a grid has many solutions", () => {
  const { count, aborted } = solve(new Uint8Array(CELLS), { limit: 2 });
  assert.equal(count, 2);
  assert.equal(aborted, false);
});

test("solve finds no solution when two clues clash", () => {
  const puzzle = new Uint8Array(CELLS);
  puzzle[0] = 5;
  puzzle[SIZE - 1] = 5;
  assert.deepEqual(solve(puzzle, { limit: 2 }), {
    count: 0,
    solution: null,
    aborted: false,
    nodes: 0,
  });
});

test("solve reports a search cut short by the node limit", () => {
  const result = solve(new Uint8Array(CELLS), { limit: 2, nodeLimit: 1 });
  assert.equal(result.count, 0);
  assert.equal(result.aborted, true);
});

test("solvesAt needs only hidden singles for one missing cell", () => {
  const puzzle = patternGrid();
  puzzle[100] = 0;
  for (const level of LEVELS) {
    assert.equal(solvesAt(puzzle, level), true);
  }
  assert.equal(solvesAt(new Uint8Array(CELLS), "hard"), false);
  assert.throws(() => solvesAt(puzzle, "expert"), /unknown level/);
});

test("techniques never rule out a symbol that a solution uses", () => {
  // A sound technique keeps the known solution's symbol in every cell it
  // doesn't fill, even when the clues allow other solutions too.
  let stalled = 0;
  for (const { solution, puzzle } of sparsePuzzles()) {
    for (const level of LEVELS) {
      const result = applyTechniques(puzzle, level);
      assert.notEqual(result, null);
      for (let i = 0; i < CELLS; i += 1) {
        if (result.grid[i] === 0) {
          const bit = 1 << (solution[i] - 1);
          assert.notEqual(result.candidates[i] & bit, 0, `${level} cell ${i}`);
        } else {
          assert.equal(result.grid[i], solution[i], `${level} cell ${i}`);
        }
      }
      if (countClues(result.grid) < CELLS) {
        stalled += 1;
      }
    }
  }
  assert.ok(stalled > 20, `only ${stalled} runs stalled`);
});

test("techniques run until none of their moves is left", () => {
  let hardMovesAfterMedium = 0;
  for (const { puzzle } of sparsePuzzles()) {
    for (const level of LEVELS) {
      const result = applyTechniques(puzzle, level);
      assert.equal(openMove(result, level), null, level);
    }
    if (openMove(applyTechniques(puzzle, "medium"), "hard") !== null) {
      hardMovesAfterMedium += 1;
    }
  }
  // Medium leaves hard moves on the table, so the check above has teeth.
  assert.ok(hardMovesAfterMedium > 5, `only ${hardMovesAfterMedium}`);
});

test("applyTechniques returns null when clues clash", () => {
  const puzzle = new Uint8Array(CELLS);
  puzzle[0] = 3;
  puzzle[SIZE] = 3;
  assert.equal(applyTechniques(puzzle, "easy"), null);
});

test("generatePuzzle repeats for a seed and level", () => {
  const a = generatePuzzle(0x1234abcd, "hard");
  const b = generatePuzzle(0x1234abcd, "hard");
  assert.deepEqual(a, b);
  assert.notDeepEqual(generatePuzzle(0x1234abce, "hard").solution, a.solution);
});

test("boards with one seed share a solution across levels", () => {
  const [easy, medium, hard] = LEVELS.map((level) =>
    generatePuzzle(0xc0ffee, level),
  );
  assert.deepEqual(medium.solution, easy.solution);
  assert.deepEqual(hard.solution, easy.solution);
  assert.notDeepEqual(medium.puzzle, easy.puzzle);
  assert.notDeepEqual(hard.puzzle, medium.puzzle);
});

test("every board has one solution and a mirrored clue pattern", () => {
  for (const level of LEVELS) {
    for (const seed of SEEDS) {
      const board = generatePuzzle(seed, level);
      const label = `${level} ${formatSeed(seed)}`;
      assert.equal(board.seed, seed);
      assert.equal(board.level, level);
      assert.equal(isCompleteSudoku(board.solution), true, label);
      assert.equal(board.clues, countClues(board.puzzle), label);
      for (let i = 0; i < CELLS; i += 1) {
        assert.ok(
          board.puzzle[i] === 0 || board.puzzle[i] === board.solution[i],
          label,
        );
      }
      assert.equal(isMirrored(board.puzzle), true, label);
      const check = solve(board.puzzle, { limit: 2 });
      assert.equal(check.count, 1, label);
      assert.deepEqual(check.solution, board.solution, label);
    }
  }
});

test("easy boards have 120 clues and hidden singles solve them", () => {
  for (const seed of SEEDS) {
    const board = generatePuzzle(seed, "easy");
    assert.equal(board.clues, EASY_CLUES);
    assert.equal(solvesAt(board.puzzle, "easy"), true);
  }
});

test("medium boards need naked singles", () => {
  for (const seed of SEEDS) {
    const { puzzle, clues } = generatePuzzle(seed, "medium");
    assert.ok(clues < EASY_CLUES);
    assert.equal(solvesAt(puzzle, "medium"), true);
    assert.equal(solvesAt(puzzle, "easy"), false);
  }
});

test("hard boards need locked candidates or pairs", () => {
  for (const seed of SEEDS) {
    const { puzzle } = generatePuzzle(seed, "hard");
    assert.equal(solvesAt(puzzle, "hard"), true);
    assert.equal(solvesAt(puzzle, "medium"), false);
  }
});

test("generatePuzzle rejects an unknown level", () => {
  assert.throws(() => generatePuzzle(1, "expert"), /unknown level/);
});

test("formatGrid writes 16 lines of symbols with dots for empty cells", () => {
  const grid = patternGrid();
  grid[1] = 0;
  const lines = formatGrid(grid).split("\n");
  assert.equal(lines.length, SIZE);
  assert.equal(lines[0], "0.23456789ABCDEF");
  assert.equal(lines[1], "456789ABCDEF0123");
  for (const line of lines) {
    assert.match(line, /^[0-9A-F.]{16}$/);
  }
  assert.equal(SYMBOLS.length, SIZE);
});

test("formatSeed pads to eight uppercase hex digits", () => {
  assert.equal(formatSeed(0), "00000000");
  assert.equal(formatSeed(0xabc), "00000ABC");
  assert.equal(formatSeed(0xffffffff), "FFFFFFFF");
});

test("parseSeed reads one to eight hex digits", () => {
  assert.equal(parseSeed("4f2a9c01"), 0x4f2a9c01);
  assert.equal(parseSeed("ABC"), 0xabc);
  assert.equal(parseSeed(formatSeed(0xffffffff)), 0xffffffff);
  for (const bad of [null, "", "123456789", "xyz", "-1", " 12", "1.5"]) {
    assert.equal(parseSeed(bad), null, String(bad));
  }
});

test("parseLevel accepts level names in any case", () => {
  assert.equal(parseLevel("easy"), "easy");
  assert.equal(parseLevel("Hard"), "hard");
  for (const bad of [null, "", "expert", "medium "]) {
    assert.equal(parseLevel(bad), null, String(bad));
  }
});
