import assert from 'node:assert/strict';
import {describe, test} from 'node:test';

import {
  LEVELS,
  LEVEL_NAMES,
  findSolutions,
  formatSeed,
  generatePuzzle,
  gridNeighbors,
  makeRandom,
  parseLevel,
  parseSeed,
  randomPath,
  wallKey,
} from '../src/zip.js';

function assertFullPath(size, path) {
  assert.equal(path.length, size * size);
  assert.equal(new Set(path).size, size * size);
  for (let i = 1; i < path.length; i += 1) {
    assert.ok(gridNeighbors(size, path[i - 1]).includes(path[i]),
        `step ${i} jumps from ${path[i - 1]} to ${path[i]}`);
  }
}

describe('randomPath', () => {
  test('visits every cell once with edge steps', () => {
    for (const size of [2, 5, 8]) {
      assertFullPath(size, randomPath(size, makeRandom(size)));
    }
  });

  test('is not the starting zigzag', () => {
    const path = randomPath(6, makeRandom(1));
    assert.notDeepEqual(path.slice(0, 6), [0, 1, 2, 3, 4, 5]);
  });
});

describe('findSolutions', () => {
  test('finds the only path on a small board', () => {
    // 1 . / 2 .: the path must go 1, right, down, left.
    assert.deepEqual(findSolutions(2, [1, 0, 2, 0], []), [[0, 1, 3, 2]]);
  });

  test('a wall can leave no solution', () => {
    assert.deepEqual(findSolutions(2, [1, 0, 2, 0], [[1, 3]]), []);
  });

  test('numbers must come in order', () => {
    // 1 . / 3 2: going down first would reach 3 before 2.
    assert.deepEqual(findSolutions(2, [1, 0, 3, 2], []), [[0, 1, 3, 2]]);
  });

  test('stops at the limit', () => {
    const clues = new Array(9).fill(0);
    clues[0] = 1;
    clues[8] = 2;
    assert.equal(findSolutions(3, clues, [], 2).length, 2);
  });
});

for (const level of LEVEL_NAMES) {
  const {size, walls: wallBudget} = LEVELS[level];

  describe(level, () => {
    for (const seed of [1, 0xdeadbeef, 424242]) {
      const puzzle = generatePuzzle(level, seed);

      test(`seed ${formatSeed(seed)} is a valid board`, () => {
        assert.equal(puzzle.size, size);
        assertFullPath(size, puzzle.solution);
        const numbers = puzzle.clues.filter((n) => n !== 0);
        const last = Math.max(...numbers);
        assert.deepEqual([...numbers].sort((a, b) => a - b),
            Array.from({length: last}, (_, i) => i + 1));
        assert.equal(puzzle.clues[puzzle.solution[0]], 1);
        assert.equal(puzzle.clues[puzzle.solution.at(-1)], last);
        const inOrder = puzzle.solution
            .map((cell) => puzzle.clues[cell])
            .filter((n) => n !== 0);
        assert.deepEqual(inOrder, [...inOrder].sort((a, b) => a - b));
      });

      test(`seed ${formatSeed(seed)} has walls only off the path`, () => {
        assert.ok(puzzle.walls.length <= wallBudget);
        const steps = new Set();
        for (let i = 1; i < puzzle.solution.length; i += 1) {
          steps.add(wallKey(puzzle.solution[i - 1], puzzle.solution[i]));
        }
        for (const [a, b] of puzzle.walls) {
          assert.ok(a < b);
          assert.ok(gridNeighbors(size, a).includes(b));
          assert.ok(!steps.has(wallKey(a, b)));
        }
      });

      test(`seed ${formatSeed(seed)} has exactly one solution`, () => {
        assert.deepEqual(
            findSolutions(size, puzzle.clues, puzzle.walls, 2),
            [puzzle.solution]);
      });
    }

    test('the same seed builds the same puzzle', () => {
      assert.deepEqual(generatePuzzle(level, 7), generatePuzzle(level, 7));
    });
  });
}

describe('parsing', () => {
  test('seeds round-trip through hex', () => {
    for (const seed of [0, 1, 0xdeadbeef, 0xffffffff]) {
      assert.equal(parseSeed(formatSeed(seed)), seed);
    }
    assert.equal(parseSeed('xyz'), null);
    assert.equal(parseSeed(null), null);
  });

  test('levels', () => {
    assert.equal(parseLevel('hard'), 'hard');
    assert.equal(parseLevel('constructor'), null);
  });
});
