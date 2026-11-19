import assert from 'node:assert/strict';
import {describe, test} from 'node:test';

import {
  CELEBRATE_EVERY,
  LEGACY_KEY,
  emptyStats,
  filledDots,
  loadStats,
  recordAnswer,
  saveStats,
  statsKey,
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
    assert.equal(saveStats(storage, 'subtraction', stats), true);
    assert.deepEqual(loadStats(storage, 'subtraction'), stats);
  });

  test('keeps each mode apart', () => {
    const storage = memoryStorage();
    const plus = {answered: 3, correct: 3, streak: 3, best: 3};
    const times = {answered: 9, correct: 4, streak: 0, best: 2};
    saveStats(storage, 'addition', plus);
    saveStats(storage, 'multiply-divide', times);
    assert.deepEqual(loadStats(storage, 'addition'), plus);
    assert.deepEqual(loadStats(storage, 'multiply-divide'), times);
    assert.deepEqual(loadStats(storage, 'subtraction'), emptyStats());
    assert.ok(storage.values.has(statsKey('multiply-divide')));
  });

  test('addition falls back to the stats saved before modes', () => {
    const old = {answered: 40, correct: 35, streak: 6, best: 12};
    const storage = memoryStorage({[LEGACY_KEY]: JSON.stringify(old)});
    assert.deepEqual(loadStats(storage, 'addition'), old);
    assert.deepEqual(loadStats(storage, 'subtraction'), emptyStats());

    const next = {...old, answered: 41, correct: 36, streak: 7};
    saveStats(storage, 'addition', next);
    assert.deepEqual(loadStats(storage, 'addition'), next);
  });

  test('missing storage reads as zero', () => {
    assert.deepEqual(loadStats(null, 'addition'), emptyStats());
    assert.deepEqual(loadStats(memoryStorage(), 'addition'), emptyStats());
    assert.equal(saveStats(null, 'addition', emptyStats()), false);
  });

  test('corrupt JSON reads as zero', () => {
    const storage = memoryStorage({[statsKey('addition')]: '{nope'});
    assert.deepEqual(loadStats(storage, 'addition'), emptyStats());
  });

  test('bad fields read as zero, one at a time', () => {
    const storage = memoryStorage({
      [statsKey('addition')]: JSON.stringify(
          {answered: 8, correct: -1, streak: 'lots', best: 2.5}),
    });
    assert.deepEqual(
        loadStats(storage, 'addition'),
        {answered: 8, correct: 0, streak: 0, best: 0});
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
    assert.deepEqual(loadStats(storage, 'addition'), emptyStats());
    assert.equal(saveStats(storage, 'addition', emptyStats()), false);
  });
});

test('filledDots', () => {
  assert.equal(filledDots(0), 0);
  assert.equal(filledDots(3), 3);
  assert.equal(filledDots(10), 10);
  assert.equal(filledDots(11), 1);
  assert.equal(filledDots(20), 10);
});
