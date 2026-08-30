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

test("spiralLayout returns size points starting near the top", () => {
  const points = spiralLayout(48);
  assert.equal(points.length, 48);
  assert.ok(Math.abs(points[0].x - 0.5) < 0.02);
  assert.ok(points[0].y < 0.2);
  const last = points[points.length - 1];
  const dist = Math.hypot(last.x - 0.5, last.y - 0.5);
  assert.ok(dist < 0.2, "center cell near middle");
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
