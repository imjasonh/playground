import assert from 'node:assert/strict';
import {describe, test} from 'node:test';

import {
  conflicts,
  cycleMark,
  describeStep,
  dots,
  findHint,
  isWon,
  shapeOf,
} from '../src/game.js';
import {
  EMPTY,
  GAMES,
  LEVELS,
  STAR,
  UNKNOWN,
  generatePuzzle,
} from '../src/puzzle.js';

function solvedMarks(puzzle) {
  return Uint8Array.from(puzzle.solution, (star) => (star ? STAR : EMPTY));
}

describe('marks', () => {
  test('a tap cycles blank, ×, star', () => {
    assert.equal(cycleMark(UNKNOWN), EMPTY);
    assert.equal(cycleMark(EMPTY), STAR);
    assert.equal(cycleMark(STAR), UNKNOWN);
  });

  const puzzle = generatePuzzle('queens', 'easy', 7);
  const shape = shapeOf(puzzle);
  const size = puzzle.size;

  test('touching stars and crowded units conflict', () => {
    const marks = new Uint8Array(size * size);
    marks[0] = STAR;
    marks[size + 1] = STAR;
    assert.deepEqual([...conflicts(shape, marks)].sort(), [0, size + 1]);
    const row = new Uint8Array(size * size);
    row[0] = STAR;
    row[3] = STAR;
    assert.deepEqual([...conflicts(shape, row)].sort(), [0, 3]);
    assert.equal(conflicts(shape, solvedMarks(puzzle)).size, 0);
  });

  test('the solution wins and a missing star does not', () => {
    const marks = solvedMarks(puzzle);
    assert.ok(isWon(shape, marks));
    marks[marks.indexOf(STAR)] = UNKNOWN;
    assert.ok(!isWon(shape, marks));
  });

  test('dots fill the cells a star rules out', () => {
    const marks = new Uint8Array(size * size);
    const star = puzzle.solution.indexOf(1);
    marks[star] = STAR;
    const ruledOut = dots(shape, marks);
    for (const cell of shape.neighbors[star]) {
      assert.ok(ruledOut.has(cell));
    }
    const row = Math.floor(star / size);
    for (let col = 0; col < size; col += 1) {
      const cell = row * size + col;
      assert.equal(ruledOut.has(cell), cell !== star);
    }
    assert.ok(!ruledOut.has(star));
  });
});

describe('hints', () => {
  for (const game of Object.keys(GAMES)) {
    for (const level of LEVELS) {
      test(`following hints solves ${game} ${level}`, () => {
        const puzzle = generatePuzzle(game, level, 99);
        const shape = shapeOf(puzzle);
        const marks = new Uint8Array(puzzle.size * puzzle.size);
        const rules = new Set();
        for (let i = 0; i < marks.length && !isWon(shape, marks); i += 1) {
          const hint = findHint(puzzle, marks);
          assert.ok(hint, 'no hint before the puzzle is solved');
          assert.notEqual(hint.rule, 'reveal');
          assert.notEqual(hint.rule, 'mistake');
          assert.doesNotMatch(hint.text, /undefined|NaN/);
          assert.ok(hint.cells.length > 0);
          rules.add(hint.rule);
          hint.place.forEach((cell) => {
            marks[cell] = STAR;
          });
          hint.clear.forEach((cell) => {
            marks[cell] = EMPTY;
          });
        }
        assert.ok(isWon(shape, marks));
        assert.equal(findHint(puzzle, solvedMarks(puzzle)), null);
      });
    }
  }

  const puzzle = generatePuzzle('queens', 'medium', 5);

  test('a wrong star comes first', () => {
    const marks = new Uint8Array(puzzle.size * puzzle.size);
    const wrong = puzzle.solution.indexOf(0);
    marks[wrong] = STAR;
    const hint = findHint(puzzle, marks);
    assert.equal(hint.rule, 'mistake');
    assert.deepEqual(hint.cells, [wrong]);
    assert.equal(hint.text, "This queen isn't part of the solution.");
  });

  test('a × on a star is a mistake', () => {
    const marks = new Uint8Array(puzzle.size * puzzle.size);
    const star = puzzle.solution.indexOf(1);
    marks[star] = EMPTY;
    const hint = findHint(puzzle, marks);
    assert.equal(hint.rule, 'mistake');
    assert.deepEqual(hint.place, [star]);
    assert.equal(hint.text, 'This cell is marked ×, but it holds a queen.');
  });
});

describe('describeStep', () => {
  // Rows 0-2 of a 5×5 Queens board with region 0 in row 0 and region 1 in
  // rows 1 and 2.
  const queens = {
    size: 5,
    stars: 1,
    regions: [
      0, 0, 2, 2, 2,
      1, 1, 2, 2, 2,
      1, 1, 3, 3, 3,
      4, 4, 4, 4, 4,
      4, 4, 4, 4, 4,
    ],
  };
  const stars = {...queens, stars: 2};

  test('forced', () => {
    assert.equal(
        describeStep(queens, {rule: 'forced', place: [1], units: [10]}),
        'The purple region has one open cell left, so its queen goes there.');
    assert.equal(
        describeStep(stars, {rule: 'forced', place: [0, 2], units: [0]}),
        'Row 1 has 2 open cells left and needs 2 stars, so each one holds ' +
        'a star.');
  });

  test('touch', () => {
    assert.equal(
        describeStep(queens, {rule: 'touch', units: [6]}),
        'A queen here would leave column 2 without room for its queen. ' +
        'Mark it ×.');
    assert.equal(
        describeStep(stars, {rule: 'touch', units: [11]}),
        'A star here would leave the orange region without room for its ' +
        'stars. Mark it ×.');
  });

  test('group', () => {
    assert.equal(
        describeStep(queens, {rule: 'group', count: 1, units: [10, 0]}),
        'The purple region can only hold its queen in row 1. That uses up ' +
        "row 1's queen, so mark the rest of row 1 ×.");
    assert.equal(
        describeStep(queens,
            {rule: 'group', count: 2, units: [1, 2, 11, 13]}),
        'Rows 2 and 3 can only hold their queens in the orange and green ' +
        'regions. That uses up all the queens in those regions, so mark ' +
        'their other cells ×.');
    assert.equal(
        describeStep(stars,
            {rule: 'group', count: 3, units: [10, 11, 12, 0, 1, 2]}),
        'The purple, orange, and blue regions can only hold their stars in ' +
        'rows 1, 2, and 3. That uses up all the stars in those rows, so ' +
        'mark their other cells ×.');
  });

  test('forcing', () => {
    assert.equal(
        describeStep(queens, {rule: 'forcing'}),
        'If this cell held a queen, the basic rules would soon leave a ' +
        'row, column, or region without room for its queen. Mark it ×.');
  });
});
