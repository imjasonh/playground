import assert from 'node:assert/strict';
import {describe, test} from 'node:test';

import {
  KINDS,
  MODES,
  dealCard,
  isMode,
  makeCard,
  randomInt,
  sameProblem,
  spokenProblem,
} from '../src/problems.js';

// A deterministic generator (mulberry32), so failures reproduce.
function seeded(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

describe('randomInt', () => {
  test('covers both ends', () => {
    assert.equal(randomInt(() => 0, 3, 7), 3);
    assert.equal(randomInt(() => 0.999999, 3, 7), 7);
  });
});

describe('addition', () => {
  test('every card sums to at most 100 with addends of at least 1', () => {
    const rng = seeded(1);
    for (let i = 0; i < 5000; i++) {
      const card = makeCard('addition', rng);
      const [a, b] = card.operands;
      assert.ok(a >= 1 && b >= 1, `${a} + ${b}`);
      assert.equal(card.answer, a + b);
      assert.ok(card.answer <= 100, `${a} + ${b}`);
    }
  });

  test('offers the answer and one different, in-range wrong answer', () => {
    const rng = seeded(2);
    for (let i = 0; i < 5000; i++) {
      const card = makeCard('addition', rng);
      assert.equal(card.choices.length, 2);
      assert.equal(card.choices.filter((n) => n === card.answer).length, 1);
      for (const choice of card.choices) {
        assert.ok(choice >= 0 && choice <= 100, `${choice}`);
      }
    }
  });

  test('puts the answer on each side about half the time', () => {
    const rng = seeded(3);
    let left = 0;
    const n = 4000;
    for (let i = 0; i < n; i++) {
      const card = makeCard('addition', rng);
      if (card.choices[0] === card.answer) {
        left++;
      }
    }
    assert.ok(left > n * 0.45 && left < n * 0.55, `${left} of ${n}`);
  });

  test('honors a smaller max', () => {
    const rng = seeded(4);
    for (let i = 0; i < 1000; i++) {
      const card = makeCard('addition', rng, null, {max: 10});
      assert.ok(card.answer <= 10);
      assert.ok(card.choices.every((n) => n <= 10));
    }
  });

  test('wrong answers include carry and digit-swap mistakes', () => {
    const wrong = KINDS.addition.distractors({answer: 47}, {max: 100});
    assert.deepEqual(new Set(wrong), new Set([46, 48, 45, 49, 37, 57, 74]));
  });

  test('wrong answers stay in range at the edges', () => {
    assert.deepEqual(
        new Set(KINDS.addition.distractors({answer: 2}, {max: 100})),
        new Set([1, 3, 0, 4, 12]));
    assert.deepEqual(
        new Set(KINDS.addition.distractors({answer: 100}, {max: 100})),
        new Set([99, 98, 90]));
  });

  test('does not repeat the previous problem', () => {
    // Always picks the smallest sum, so 1 + 1 every time.
    const previous = makeCard('addition', () => 0);
    let calls = 0;
    const rng = () => (calls++ < 3 ? 0 : 0.5);
    const next = makeCard('addition', rng, previous);
    assert.ok(!sameProblem(next, previous));
  });
});

describe('subtraction', () => {
  test('stays within 100 and leaves at least 1', () => {
    const rng = seeded(5);
    for (let i = 0; i < 5000; i++) {
      const card = makeCard('subtraction', rng);
      const [a, b] = card.operands;
      assert.ok(a <= 100 && b >= 1, `${a} − ${b}`);
      assert.equal(card.answer, a - b);
      assert.ok(card.answer >= 1, `${a} − ${b}`);
      assert.equal(card.choices.filter((n) => n === card.answer).length, 1);
      assert.ok(card.choices.every((n) => n >= 0 && n <= 100));
    }
  });

  test('wrong answers include borrow mistakes and adding instead', () => {
    const wrong = KINDS.subtraction.distractors(
        {operands: [52, 17], answer: 35}, {max: 100});
    assert.deepEqual(
        new Set(wrong), new Set([34, 36, 33, 37, 25, 45, 53, 69]));
  });

  test('wrong answers stay in range', () => {
    const wrong = KINDS.subtraction.distractors(
        {operands: [95, 94], answer: 1}, {max: 100});
    assert.deepEqual(new Set(wrong), new Set([0, 2, 3, 11]));
  });
});

describe('multiplication', () => {
  test('uses factors from 1 to 5', () => {
    const rng = seeded(6);
    const seen = new Set();
    for (let i = 0; i < 2000; i++) {
      const card = makeCard('multiplication', rng);
      const [a, b] = card.operands;
      assert.ok(a >= 1 && a <= 5 && b >= 1 && b <= 5, `${a} × ${b}`);
      assert.equal(card.answer, a * b);
      assert.equal(card.choices.filter((n) => n === card.answer).length, 1);
      assert.ok(card.choices.every((n) => n >= 0));
      seen.add(`${a}×${b}`);
    }
    assert.equal(seen.size, 25);
  });

  test('wrong answers include a group off and adding instead', () => {
    const wrong = KINDS.multiplication.distractors(
        {operands: [3, 4], answer: 12});
    assert.deepEqual(new Set(wrong), new Set([15, 9, 16, 8, 7, 13, 11]));
  });

  test('1 × 1 still has a wrong answer', () => {
    const wrong = KINDS.multiplication.distractors(
        {operands: [1, 1], answer: 1});
    assert.deepEqual(new Set(wrong), new Set([0, 2]));
  });
});

describe('division', () => {
  test('divides evenly with divisor and quotient from 1 to 5', () => {
    const rng = seeded(7);
    for (let i = 0; i < 2000; i++) {
      const card = makeCard('division', rng);
      const [dividend, divisor] = card.operands;
      assert.ok(divisor >= 1 && divisor <= 5, `${dividend} ÷ ${divisor}`);
      assert.ok(card.answer >= 1 && card.answer <= 5);
      assert.equal(card.answer * divisor, dividend);
      assert.equal(card.choices.filter((n) => n === card.answer).length, 1);
      assert.ok(card.choices.every((n) => n >= 0));
    }
  });

  test('wrong answers include the divisor and subtracting instead', () => {
    const wrong = KINDS.division.distractors(
        {operands: [15, 3], answer: 5});
    assert.deepEqual(new Set(wrong), new Set([4, 6, 3, 12]));
  });

  test('wrong answers never repeat the answer', () => {
    const wrong = KINDS.division.distractors({operands: [4, 2], answer: 2});
    assert.deepEqual(new Set(wrong), new Set([1, 3]));
  });
});

describe('modes', () => {
  test('every mode names known kinds', () => {
    for (const kinds of Object.values(MODES)) {
      assert.ok(kinds.length > 0);
      assert.ok(kinds.every((kind) => Object.hasOwn(KINDS, kind)));
    }
  });

  test('multiply-divide deals both kinds', () => {
    const rng = seeded(8);
    let division = 0;
    const n = 2000;
    for (let i = 0; i < n; i++) {
      const card = dealCard('multiply-divide', rng);
      assert.ok(['multiplication', 'division'].includes(card.kind));
      if (card.kind === 'division') {
        division++;
      }
    }
    assert.ok(division > n * 0.4 && division < n * 0.6, `${division} of ${n}`);
  });

  test('each single-kind mode deals only its kind', () => {
    const rng = seeded(9);
    for (let i = 0; i < 200; i++) {
      assert.equal(dealCard('addition', rng).kind, 'addition');
      assert.equal(dealCard('subtraction', rng).kind, 'subtraction');
    }
  });

  test('isMode accepts only mode keys', () => {
    assert.ok(isMode('subtraction'));
    assert.ok(!isMode('calculus'));
    assert.ok(!isMode('constructor'));
    assert.ok(!isMode(null));
  });

  test('dealCard rejects an unknown mode', () => {
    assert.throws(() => dealCard('calculus', Math.random), /unknown mode/);
  });
});

test('makeCard rejects an unknown kind', () => {
  assert.throws(() => makeCard('calculus', Math.random), /unknown/);
  assert.throws(() => makeCard('toString', Math.random), /unknown/);
});

test('spokenProblem', () => {
  const problem = {operands: [23, 45], operator: '+', spoken: 'plus'};
  assert.equal(spokenProblem(problem), '23 plus 45');
});
