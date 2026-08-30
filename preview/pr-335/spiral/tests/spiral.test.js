import test from "node:test";
import assert from "node:assert/strict";

import {
  buildSuffixSet,
  isValidOutwardSuffix,
  wordBreak,
} from "../src/trie.js";
import {
  generatePuzzle,
  generatePuzzleWithRetry,
  validatePuzzle,
} from "../src/generate.js";
import { WORD_SET } from "../src/words.js";
import { spiralLayout } from "../src/spiral.js";
import {
  createPlayState,
  setLetter,
  checkGuesses,
  cellStatus,
  spanIndices,
  selectClue,
  cluesCovering,
  isSolved,
  revealAll,
} from "../src/puzzle.js";

const SUFFIX_SET = buildSuffixSet([...WORD_SET]);

test("wordBreak segments a known reverse string", () => {
  const words = wordBreak("SPEEDRELATE", WORD_SET, 3, 8);
  assert.ok(words);
  assert.deepEqual(words, ["SPEED", "RELATE"]);
});

test("isValidOutwardSuffix accepts a complete trailing word sequence", () => {
  assert.equal(
    isValidOutwardSuffix("SPEED", WORD_SET, SUFFIX_SET, 3, 8),
    true,
  );
});

test("isValidOutwardSuffix accepts a word-suffix head plus complete words", () => {
  // TESPEED = suffix "TE" of many words + SPEED
  assert.equal(
    isValidOutwardSuffix("TESPEED", WORD_SET, SUFFIX_SET, 3, 8),
    true,
  );
});

test("generatePuzzle builds a valid interlocking spiral", () => {
  const puzzle = generatePuzzle({ size: 36, seed: 42, maxNodes: 200000 });
  assert.ok(puzzle, "expected a puzzle");
  assert.equal(puzzle.letters.length, 36);
  assert.equal(validatePuzzle(puzzle), true);
  assert.ok(puzzle.inward.length >= 4);
  assert.ok(puzzle.outward.length >= 4);

  const inwardJoined = puzzle.inward.map((s) => s.word).join("");
  assert.equal(inwardJoined, puzzle.letters);

  const outwardJoined = puzzle.outward.map((s) => s.word).join("");
  assert.equal(
    outwardJoined,
    puzzle.letters.split("").reverse().join(""),
  );
});

test("generatePuzzleWithRetry succeeds for size 100", () => {
  const puzzle = generatePuzzleWithRetry({
    size: 100,
    seed: 7,
    attempts: 16,
    maxNodes: 100 * 16000,
  });
  assert.ok(puzzle);
  assert.equal(validatePuzzle(puzzle), true);
  assert.equal(puzzle.size, 100);
});

test("spiralLayout returns equal-arc cells that stay chunky near the center", () => {
  const layout = spiralLayout(100);
  assert.equal(layout.cells.length, 100);
  assert.ok(layout.cells[0].path.includes("Z"));
  assert.ok(layout.trackWidth > 0.04, "track should be wide enough to write in");

  // Outer and inner cells should have similar bounding-box area (arc-length division).
  function area(cell) {
    const nums = [...cell.path.matchAll(/([0-9.]+)\s+([0-9.]+)/g)].map((m) => [
      Number(m[1]),
      Number(m[2]),
    ]);
    let minX = Infinity;
    let maxX = -Infinity;
    let minY = Infinity;
    let maxY = -Infinity;
    for (const [x, y] of nums) {
      minX = Math.min(minX, x);
      maxX = Math.max(maxX, x);
      minY = Math.min(minY, y);
      maxY = Math.max(maxY, y);
    }
    return (maxX - minX) * (maxY - minY);
  }

  const outer = area(layout.cells[2]);
  const inner = area(layout.cells[90]);
  assert.ok(
    inner / outer > 0.35,
    `inner cell should not collapse (inner/outer=${(inner / outer).toFixed(2)})`,
  );

  const last = layout.cells[layout.cells.length - 1];
  const dist = Math.hypot(last.cx - 0.5, last.cy - 0.5);
  assert.ok(dist < 0.28, "last cell near the middle");
});

test("play state tracks guesses, check, and reveal", () => {
  const puzzle = generatePuzzle({ size: 24, seed: 1, maxNodes: 100000 });
  assert.ok(puzzle);
  let state = createPlayState(puzzle);

  state = setLetter(state, 0, puzzle.letters[0]);
  assert.equal(cellStatus(state, 0), "filled");

  state = setLetter(state, 1, "Z");
  state = checkGuesses(state);
  assert.equal(cellStatus(state, 0), "correct");
  assert.equal(cellStatus(state, 1), "wrong");

  state = revealAll(state);
  assert.equal(isSolved(state), true);
  assert.equal(cellStatus(state, 1), "revealed");
});

test("spanIndices walks outward ranges backward", () => {
  assert.deepEqual(spanIndices({ start: 5, end: 1 }), [4, 3, 2, 1, 0]);
  assert.deepEqual(spanIndices({ start: 1, end: 4 }), [0, 1, 2, 3]);
});

test("selectClue jumps to the first empty cell in the span", () => {
  const puzzle = generatePuzzle({ size: 24, seed: 1, maxNodes: 100000 });
  assert.ok(puzzle);
  let state = createPlayState(puzzle);
  const span = puzzle.inward[0];
  const indices = spanIndices(span);
  state = setLetter(state, indices[0], "A");
  state = setLetter(state, indices[1], "B");
  state = selectClue(state, "inward", 0);
  assert.equal(state.selected, indices[2]);
  assert.equal(state.activeDir, "inward");
});

test("cluesCovering finds inward and outward spans for a cell", () => {
  const puzzle = generatePuzzle({ size: 24, seed: 1, maxNodes: 100000 });
  assert.ok(puzzle);
  const inwardHits = cluesCovering(puzzle, "inward", 0);
  const outwardHits = cluesCovering(puzzle, "outward", 0);
  assert.ok(inwardHits.length >= 1);
  assert.ok(outwardHits.length >= 1);
});
