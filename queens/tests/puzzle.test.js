import assert from 'node:assert/strict';
import {describe, test} from 'node:test';

import {
  EMPTY,
  GAMES,
  LEVELS,
  STAR,
  UNKNOWN,
  countSolutions,
  formatSeed,
  generatePuzzle,
  isBroken,
  isSolved,
  makeShape,
  nextStep,
  parseGame,
  parseLevel,
  parseSeed,
  propagate,
  touches,
} from '../src/puzzle.js';

const SEEDS = [1, 0xdeadbeef];

function regionIsConnected(size, regions, region) {
  const members = [];
  regions.forEach((r, cell) => {
    if (r === region) {
      members.push(cell);
    }
  });
  const seen = new Set([members[0]]);
  const queue = [members[0]];
  while (queue.length > 0) {
    const cell = queue.pop();
    const row = Math.floor(cell / size);
    const col = cell % size;
    const next = [];
    if (row > 0) {
      next.push(cell - size);
    }
    if (row < size - 1) {
      next.push(cell + size);
    }
    if (col > 0) {
      next.push(cell - 1);
    }
    if (col < size - 1) {
      next.push(cell + 1);
    }
    for (const n of next) {
      if (regions[n] === region && !seen.has(n)) {
        seen.add(n);
        queue.push(n);
      }
    }
  }
  return seen.size === members.length;
}

for (const game of Object.keys(GAMES)) {
  for (const level of LEVELS) {
    const {stars, levels} = GAMES[game];
    const {size, rank} = levels[level];

    describe(`${game} ${level}`, () => {
      for (const seed of SEEDS) {
        const puzzle = generatePuzzle(game, level, seed);
        const shape = makeShape(puzzle.size, puzzle.stars, puzzle.regions);

        test(`seed ${formatSeed(seed)} has ${size} connected regions`, () => {
          assert.equal(puzzle.size, size);
          assert.equal(puzzle.stars, stars);
          assert.equal(puzzle.regions.length, size * size);
          assert.equal(new Set(puzzle.regions).size, size);
          for (let region = 0; region < size; region += 1) {
            assert.ok(regionIsConnected(size, puzzle.regions, region),
                `region ${region} is in more than one piece`);
          }
        });

        test(`seed ${formatSeed(seed)} has a valid solution`, () => {
          const state = Uint8Array.from(puzzle.solution,
              (star) => (star ? STAR : EMPTY));
          assert.ok(isSolved(shape, state));
        });

        test(`seed ${formatSeed(seed)} has exactly one solution`, () => {
          assert.equal(countSolutions(shape, 2), 1);
        });

        test(`seed ${formatSeed(seed)} needs rank ${rank} rules`, () => {
          const state = new Uint8Array(size * size);
          if (rank > 0) {
            propagate(shape, state, rank - 1);
            assert.ok(state.includes(UNKNOWN),
                'the rules of the level below solve it');
          }
          const {broken} = propagate(shape, state, rank);
          assert.equal(broken, false);
          assert.deepEqual(Array.from(state, (v) => (v === STAR ? 1 : 0)),
              puzzle.solution);
        });
      }

      test('the board has more 2×2 blocks than stars', () => {
        // Each block that tiles the board holds at most one star. With as
        // many stars as blocks, every block holds one, and only a couple of
        // layouts fit, so the regions barely matter.
        assert.ok(stars * size < Math.ceil(size / 2) ** 2);
      });

      test('the same seed builds the same puzzle', () => {
        assert.deepEqual(generatePuzzle(game, level, 42),
            generatePuzzle(game, level, 42));
      });
    });
  }
}

describe('rules', () => {
  // Five rows, with a two-cell region in the corner of row 0.
  //   A A B B B
  //   B B B B B
  //   C C C C C
  //   D D D D D
  //   E E E E E
  const regions = [
    0, 0, 1, 1, 1,
    1, 1, 1, 1, 1,
    2, 2, 2, 2, 2,
    3, 3, 3, 3, 3,
    4, 4, 4, 4, 4,
  ];
  const shape = makeShape(5, 1, regions);

  test('touch rules out a cell that would starve a region', () => {
    const step = nextStep(shape, new Uint8Array(25));
    assert.equal(step.rule, 'touch');
    assert.deepEqual(step.clear, [2]);
    assert.deepEqual(step.units, [10]);
    assert.deepEqual(step.reason, [0, 1]);
  });

  test('forced fills the last open cell of a unit', () => {
    const state = new Uint8Array(25);
    state[0] = EMPTY;
    const step = nextStep(shape, state);
    assert.equal(step.rule, 'forced');
    assert.deepEqual(step.place, [1]);
  });

  test('steps skip the cells a star already rules out', () => {
    const state = new Uint8Array(25);
    state[1] = STAR;
    const ruledOut = new Set([...shape.neighbors[1], ...shape.units[0],
      ...shape.units[6], ...shape.units[10]]);
    const step = nextStep(shape, state);
    assert.ok(step);
    for (const cell of [...step.place, ...step.clear]) {
      assert.ok(!ruledOut.has(cell), `step repeats cell ${cell}`);
    }
  });

  test('isBroken catches touching stars and starved units', () => {
    const touching = new Uint8Array(25);
    touching[0] = STAR;
    touching[6] = STAR;
    assert.ok(isBroken(shape, touching));
    const starved = new Uint8Array(25);
    starved[0] = EMPTY;
    starved[1] = EMPTY;
    assert.ok(isBroken(shape, starved));
    assert.ok(!isBroken(shape, new Uint8Array(25)));
  });

  test('touches includes corners only', () => {
    assert.ok(touches(5, 0, 6));
    assert.ok(touches(5, 0, 1));
    assert.ok(!touches(5, 0, 2));
    assert.ok(!touches(5, 4, 5));
    assert.ok(!touches(5, 0, 0));
  });
});

describe('parsing', () => {
  test('seeds round-trip through hex', () => {
    for (const seed of [0, 1, 0xdeadbeef, 0xffffffff]) {
      assert.equal(parseSeed(formatSeed(seed)), seed);
    }
    assert.equal(formatSeed(255), '000000ff');
    assert.equal(parseSeed('zz'), null);
    assert.equal(parseSeed('123456789'), null);
    assert.equal(parseSeed(null), null);
  });

  test('games and levels', () => {
    assert.equal(parseGame('queens'), 'queens');
    assert.equal(parseGame('twonottouch'), 'twonottouch');
    assert.equal(parseGame('toString'), null);
    assert.equal(parseLevel('expert'), 'expert');
    assert.equal(parseLevel('impossible'), null);
  });
});
