import assert from 'node:assert/strict';
import {describe, test} from 'node:test';

import {
  CELEBRATE_EVERY,
  STORAGE_KEY,
  emptyStats,
  filledDots,
  loadStats,
  recordAnswer,
  saveStats,
} from '../src/stats.js';

function memoryStorage(initial = {}) {
  const values = new Map(Object.entries(initial));
  return {
    getItem: (key) => values.get(key) ?? null,
    setItem: (key, value) => values.set(key, String(value)),
    values,
  };
}

describe('recordAnswer', () => {
  test('counts answers and grows the streak', () => {
    let stats = emptyStats();
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
    let stats = emptyStats();
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

describe('storage', () => {
  test('round-trips', () => {
    const storage = memoryStorage();
    const stats = {answered: 12, correct: 10, streak: 4, best: 7};
    assert.equal(saveStats(storage, stats), true);
    assert.deepEqual(loadStats(storage), stats);
  });

  test('missing storage reads as zero', () => {
    assert.deepEqual(loadStats(null), emptyStats());
    assert.deepEqual(loadStats(memoryStorage()), emptyStats());
    assert.equal(saveStats(null, emptyStats()), false);
  });

  test('corrupt JSON reads as zero', () => {
    const storage = memoryStorage({[STORAGE_KEY]: '{nope'});
    assert.deepEqual(loadStats(storage), emptyStats());
  });

  test('bad fields read as zero, one at a time', () => {
    const storage = memoryStorage({
      [STORAGE_KEY]: JSON.stringify(
          {answered: 8, correct: -1, streak: 'lots', best: 2.5}),
    });
    assert.deepEqual(
        loadStats(storage), {answered: 8, correct: 0, streak: 0, best: 0});
  });

  test('a storage that throws reports failure', () => {
    const storage = {
      getItem() {
        throw new Error('blocked');
      },
      setItem() {
        throw new Error('full');
      },
    };
    assert.deepEqual(loadStats(storage), emptyStats());
    assert.equal(saveStats(storage, emptyStats()), false);
  });
});

test('filledDots', () => {
  assert.equal(filledDots(0), 0);
  assert.equal(filledDots(3), 3);
  assert.equal(filledDots(10), 10);
  assert.equal(filledDots(11), 1);
  assert.equal(filledDots(20), 10);
});
