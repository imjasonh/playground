import test from "node:test";
import assert from "node:assert/strict";

import {
  buildSuffixSet,
  isValidOutwardSuffix,
  wordBreak,
} from "../src/trie.js";
import {
  generatePuzzleWithRetry,
  validatePuzzle,
  partitionsInterlock,
  seamsFromLengths,
} from "../src/generate.js";
import { WORD_SET, ENTRIES } from "../src/words.js";
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
  const words = wordBreak("ACEALE", WORD_SET, 3, 8);
  assert.ok(words);
  assert.deepEqual(words, ["ACE", "ALE"]);
});

test("isValidOutwardSuffix accepts a complete trailing word sequence", () => {
  assert.equal(
    isValidOutwardSuffix("STOIC", WORD_SET, SUFFIX_SET, 3, 8),
    true,
  );
});

test("isValidOutwardSuffix accepts a word-suffix head plus complete words", () => {
  // ICSTOIC = suffix "IC" of STOIC + STOIC
  assert.equal(
    isValidOutwardSuffix("ICSTOIC", WORD_SET, SUFFIX_SET, 3, 8),
    true,
  );
});

test("generatePuzzle builds a valid interlocking spiral", () => {
  const puzzle = generatePuzzleWithRetry({
    size: 36,
    seed: 42,
    attempts: 120,
    maxNodes: 200000,
  });
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

  const clues = [...puzzle.inward, ...puzzle.outward].map((s) => s.clue);
  assert.equal(new Set(clues).size, clues.length, "clues must be unique");

  const inSeams = seamsFromLengths(
    puzzle.inward.map((s) => Math.abs(s.start - s.end) + 1),
    "inward",
    puzzle.size,
  );
  const outSeams = seamsFromLengths(
    puzzle.outward.map((s) => Math.abs(s.start - s.end) + 1),
    "outward",
    puzzle.size,
  );
  for (const seam of inSeams) {
    assert.equal(outSeams.has(seam), false, `shared seam after cell ${seam}`);
  }
});

test("generatePuzzleWithRetry succeeds for size 64", () => {
  const puzzle = generatePuzzleWithRetry({
    size: 64,
    seed: 11,
    attempts: 200,
    maxNodes: 64 * 10000,
  });
  assert.ok(puzzle);
  assert.equal(validatePuzzle(puzzle), true);
  assert.equal(puzzle.size, 64);
  const clues = [...puzzle.inward, ...puzzle.outward].map((s) => s.clue);
  assert.equal(new Set(clues).size, clues.length);
  assert.equal(
    partitionsInterlock(puzzle.inward, puzzle.outward, puzzle.size),
    true,
  );
});

test("partitionsInterlock rejects shared seams and identical spans", () => {
  const size = 10;
  const aligned = {
    inward: [
      { start: 1, end: 5, word: "ABCDE", clue: "a", display: "ABCDE" },
      { start: 6, end: 10, word: "FGHIJ", clue: "b", display: "FGHIJ" },
    ],
    outward: [
      { start: 10, end: 6, word: "JIHGF", clue: "c", display: "JIHGF" },
      { start: 5, end: 1, word: "EDCBA", clue: "d", display: "EDCBA" },
    ],
  };
  assert.equal(partitionsInterlock(aligned.inward, aligned.outward, size), false);

  const staggered = {
    inward: [
      { start: 1, end: 4, word: "ABCD", clue: "a", display: "ABCD" },
      { start: 5, end: 10, word: "EFGHIJ", clue: "b", display: "EFGHIJ" },
    ],
    outward: [
      { start: 10, end: 8, word: "JIH", clue: "c", display: "JIH" },
      { start: 7, end: 3, word: "GFEDC", clue: "d", display: "GFEDC" },
      { start: 2, end: 1, word: "BA", clue: "e", display: "BA" },
    ],
  };
  // outward last word length 2 is only for this unit illustration; interlock
  // cares about seams: in={4}, out={7,2} — disjoint, ranges differ.
  assert.equal(
    partitionsInterlock(staggered.inward, staggered.outward, size),
    true,
  );
});

test("lexicon clues are unique and omit the magazine originals", () => {
  assert.equal(ENTRIES.length, new Set(ENTRIES.map((e) => e.clue)).size);
  assert.equal(ENTRIES.length, new Set(ENTRIES.map((e) => e.word)).size);
  const banned = [
    "Recessed, as eyes",
    "Irish singer",
    "Rubber City",
    "Schwarzenegger",
    "Megan Thee Stallion",
    "Spot for a massage",
    "Church recess",
  ];
  for (const entry of ENTRIES) {
    for (const phrase of banned) {
      assert.equal(
        entry.clue.includes(phrase),
        false,
        `${entry.word} still uses banned clue text`,
      );
    }
  }
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
  const puzzle = generatePuzzleWithRetry({
    size: 24,
    seed: 1,
    attempts: 64,
    maxNodes: 100000,
  });
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
  const puzzle = generatePuzzleWithRetry({
    size: 24,
    seed: 1,
    attempts: 64,
    maxNodes: 100000,
  });
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
  const puzzle = generatePuzzleWithRetry({
    size: 24,
    seed: 1,
    attempts: 64,
    maxNodes: 100000,
  });
  assert.ok(puzzle);
  const inwardHits = cluesCovering(puzzle, "inward", 0);
  const outwardHits = cluesCovering(puzzle, "outward", 0);
  assert.ok(inwardHits.length >= 1);
  assert.ok(outwardHits.length >= 1);
});
