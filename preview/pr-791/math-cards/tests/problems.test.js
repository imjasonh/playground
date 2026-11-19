import assert from 'node:assert/strict';
import {describe, test} from 'node:test';

import {
  KINDS,
  makeCard,
  problemText,
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

test('makeCard rejects an unknown kind', () => {
  assert.throws(() => makeCard('calculus', Math.random), /unknown/);
});

test('problem text', () => {
  const problem = {operands: [23, 45], operator: '+', spoken: 'plus'};
  assert.equal(problemText(problem), '23 + 45');
  assert.equal(spokenProblem(problem), '23 plus 45');
});
