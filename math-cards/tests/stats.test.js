import assert from 'node:assert/strict';
import {describe, test} from 'node:test';

import {
  CELEBRATE_EVERY,
  Progress,
  filledDots,
  recordAnswer,
} from '../src/stats.js';

const ZERO = Object.freeze({answered: 0, correct: 0, streak: 0, best: 0});

function memoryStorage(initial = {}) {
  const values = new Map(Object.entries(initial));
  return {
    getItem: (key) => values.get(key) ?? null,
    setItem: (key, value) => values.set(key, String(value)),
    values,
  };
}

function blockedStorage() {
  return {
    getItem() {
      throw new Error('blocked');
    },
    setItem() {
      throw new Error('full');
    },
  };
}

describe('recordAnswer', () => {
  test('counts answers and grows the streak', () => {
    let stats = ZERO;
    for (let i = 0; i < 3; i++) {
      ({stats} = recordAnswer(stats, true));
    }
    assert.deepEqual(stats, {answered: 3, correct: 3, streak: 3, best: 3});
  });

  test('a wrong answer ends the streak and keeps the best', () => {
    let stats = {answered: 5, correct: 5, streak: 5, best: 5};
    ({stats} = recordAnswer(stats, false));
    assert.deepEqual(stats, {answered: 6, correct: 5, streak: 0, best: 5});
    ({stats} = recordAnswer(stats, true));
    assert.equal(stats.streak, 1);
    assert.equal(stats.best, 5);
  });

  test('celebrates every ten in a row', () => {
    let stats = ZERO;
    const celebrations = [];
    for (let i = 1; i <= 25; i++) {
      const result = recordAnswer(stats, true);
      stats = result.stats;
      if (result.celebrate) {
        celebrations.push(stats.streak);
      }
    }
    assert.equal(CELEBRATE_EVERY, 10);
    assert.deepEqual(celebrations, [10, 20]);
  });

  test('does not celebrate a wrong answer', () => {
    const {celebrate} = recordAnswer(
        {answered: 9, correct: 9, streak: 9, best: 9}, false);
    assert.equal(celebrate, false);
  });
});

describe('Progress', () => {
  test('starts in addition with no stats', () => {
    const progress = new Progress(memoryStorage());
    assert.equal(progress.mode, 'addition');
    assert.deepEqual(progress.stats, ZERO);
  });

  test('saves the mode and each mode\'s stats', () => {
    const storage = memoryStorage();
    const progress = new Progress(storage);
    progress.record(true);
    progress.selectMode('subtraction');
    progress.record(true);
    progress.record(false);

    assert.deepEqual([...storage.values.keys()].sort(), [
      'math-cards:mode',
      'math-cards:v1:addition',
      'math-cards:v1:subtraction',
    ]);
    const reopened = new Progress(storage);
    assert.equal(reopened.mode, 'subtraction');
    assert.deepEqual(
        reopened.stats, {answered: 2, correct: 1, streak: 0, best: 1});
    reopened.selectMode('addition');
    assert.deepEqual(
        reopened.stats, {answered: 1, correct: 1, streak: 1, best: 1});
    reopened.selectMode('multiply-divide');
    assert.deepEqual(reopened.stats, ZERO);
  });

  test('reports a celebration every ten in a row', () => {
    const progress = new Progress(memoryStorage());
    const celebrations = [];
    for (let i = 1; i <= 20; i++) {
      if (progress.record(true)) {
        celebrations.push(i);
      }
    }
    assert.deepEqual(celebrations, [10, 20]);
  });

  test('addition falls back to the stats saved before modes', () => {
    const old = {answered: 40, correct: 35, streak: 6, best: 12};
    const storage = memoryStorage({'math-cards:v1': JSON.stringify(old)});
    const progress = new Progress(storage);
    assert.deepEqual(progress.stats, old);
    progress.record(true);
    assert.equal(
        storage.values.get('math-cards:v1:addition'),
        JSON.stringify({answered: 41, correct: 36, streak: 7, best: 12}));
    progress.selectMode('subtraction');
    assert.deepEqual(progress.stats, ZERO);
  });

  test('an unknown saved mode reads as addition', () => {
    const progress =
        new Progress(memoryStorage({'math-cards:mode': 'constructor'}));
    assert.equal(progress.mode, 'addition');
  });

  test('rejects an unknown mode', () => {
    const progress = new Progress(memoryStorage());
    assert.throws(() => progress.selectMode('calculus'), /unknown mode/);
    assert.equal(progress.mode, 'addition');
  });

  test('corrupt JSON reads as zero', () => {
    const storage = memoryStorage({'math-cards:v1:addition': '{nope'});
    assert.deepEqual(new Progress(storage).stats, ZERO);
  });

  test('bad fields read as zero, one at a time', () => {
    const storage = memoryStorage({
      'math-cards:v1:addition': JSON.stringify(
          {answered: 8, correct: -1, streak: 'lots', best: 2.5}),
    });
    assert.deepEqual(
        new Progress(storage).stats,
        {answered: 8, correct: 0, streak: 0, best: 0});
  });

  for (const [name, storage] of [
    ['missing', null],
    ['blocked', blockedStorage()],
  ]) {
    test(`${name} storage keeps each mode apart in memory`, () => {
      const progress = new Progress(storage);
      progress.record(true);
      progress.selectMode('subtraction');
      assert.deepEqual(progress.stats, ZERO);
      progress.selectMode('addition');
      assert.deepEqual(
          progress.stats, {answered: 1, correct: 1, streak: 1, best: 1});
    });
  }
});

test('filledDots', () => {
  assert.equal(filledDots(0), 0);
  assert.equal(filledDots(3), 3);
  assert.equal(filledDots(10), 10);
  assert.equal(filledDots(11), 1);
  assert.equal(filledDots(20), 10);
});
