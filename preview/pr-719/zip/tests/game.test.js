import assert from 'node:assert/strict';
import {describe, test} from 'node:test';

import {
  boardOf,
  canExtend,
  findHint,
  isSolved,
  moveTo,
  nextNumber,
} from '../src/game.js';
import {LEVEL_NAMES, generatePuzzle} from '../src/zip.js';

// 3×3, numbered 1 . 2 / . . . / 4 . 3, with a wall between the middle cell
// and the one above it. Its solution is 0 1 2 5 8 7 4 3 6.
const small = {
  size: 3,
  clues: [1, 0, 2, 0, 0, 0, 4, 0, 3],
  walls: [[1, 4]],
  solution: [0, 1, 2, 5, 8, 7, 4, 3, 6],
};

describe('drawing', () => {
  const board = boardOf(small);

  test('a path starts on 1', () => {
    assert.ok(canExtend(board, [], 0));
    assert.ok(!canExtend(board, [], 1));
  });

  test('numbers come in order', () => {
    assert.equal(nextNumber(board, [0, 1]), 2);
    assert.ok(!canExtend(board, [0, 3], 6));
    assert.ok(canExtend(board, [0, 1], 2));
  });

  test('walls, visited cells, and distant cells block a step', () => {
    assert.ok(!canExtend(board, [0, 1], 4));
    assert.ok(!canExtend(board, [0, 3, 4], 3));
    assert.ok(!canExtend(board, [0], 2));
    assert.ok(canExtend(board, [0, 3], 4));
  });

  test('the path stops at the last number', () => {
    assert.ok(!canExtend(board, [0, 1, 2, 5, 8, 7, 6], 3));
  });

  test('moving onto the path cuts it back', () => {
    assert.deepEqual(moveTo(board, [0, 1, 2, 5], 1), [0, 1]);
  });

  test('a drag in line fills the cells between', () => {
    assert.deepEqual(moveTo(board, [0], 2), [0, 1, 2]);
    assert.deepEqual(moveTo(board, [0, 3], 5), [0, 3, 4, 5]);
    assert.equal(moveTo(board, [0, 1], 7), null);
    assert.equal(moveTo(board, [0], 4), null);
  });

  test('the solution solves it', () => {
    assert.ok(isSolved(board, small.solution));
    assert.ok(!isSolved(board, small.solution.slice(0, -1)));
  });
});

describe('hints', () => {
  test('an empty board starts at 1', () => {
    const hint = findHint(small, []);
    assert.equal(hint.rule, 'start');
    assert.deepEqual(hint.cells, [0, 1, 2, 5]);
  });

  test('the next cells stop at a number', () => {
    const hint = findHint(small, [0]);
    assert.equal(hint.rule, 'next');
    assert.deepEqual(hint.cells, [1, 2]);
    assert.equal(hint.text, 'Head this way to reach 2.');
  });

  test('a hint that stops short names the next number', () => {
    const hint = findHint(small, [0, 1, 2]);
    assert.deepEqual(hint.cells, [5, 8]);
    assert.equal(hint.text, 'Head this way to reach 3.');
    const puzzle = generatePuzzle('hard', 3);
    const far = findHint(puzzle, puzzle.solution.slice(0, 1));
    assert.match(far.text, /^Head this way (toward|to reach) \d+\.$/);
  });

  test('a wrong turn backs up to the last right cell', () => {
    const hint = findHint(small, [0, 3, 4]);
    assert.equal(hint.rule, 'back');
    assert.equal(hint.from, 0);
    assert.deepEqual(hint.wrong, [3, 4]);
  });

  test('a solved board has no hint', () => {
    assert.equal(findHint(small, small.solution), null);
  });

  for (const level of LEVEL_NAMES) {
    test(`following hints solves ${level}`, () => {
      const puzzle = generatePuzzle(level, 99);
      const board = boardOf(puzzle);
      let path = [];
      for (let i = 0; i < board.cells && !isSolved(board, path); i += 1) {
        const hint = findHint(puzzle, path);
        assert.notEqual(hint.rule, 'back');
        for (const cell of hint.cells) {
          assert.ok(canExtend(board, path, cell));
          path = [...path, cell];
        }
      }
      assert.ok(isSolved(board, path));
    });
  }
});
