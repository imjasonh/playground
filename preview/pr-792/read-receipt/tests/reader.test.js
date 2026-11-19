import assert from 'node:assert/strict';
import {test} from 'node:test';

import {
  Reader,
  formatDuration,
  isAdvanceKey,
  withinSpeedLimit,
  wordsPerMinute,
} from '../src/reader.js';

/**
 * @param {string} key
 * @param {!Object=} overrides
 * @return {!Object} A keydown event's fields.
 */
function key(key, overrides = {}) {
  return {
    key,
    repeat: false,
    altKey: false,
    ctrlKey: false,
    metaKey: false,
    shiftKey: false,
    ...overrides,
  };
}

test('isAdvanceKey accepts fresh Right Arrow and Space presses', () => {
  assert.equal(isAdvanceKey(key('ArrowRight')), true);
  assert.equal(isAdvanceKey(key(' ')), true);
});

test('isAdvanceKey ignores held keys', () => {
  assert.equal(isAdvanceKey(key('ArrowRight', {repeat: true})), false);
  assert.equal(isAdvanceKey(key(' ', {repeat: true})), false);
});

test('isAdvanceKey ignores other keys and modified presses', () => {
  for (const name of ['ArrowLeft', 'ArrowDown', 'Enter', 'a', 'Spacebar']) {
    assert.equal(isAdvanceKey(key(name)), false, name);
  }
  for (const modifier of ['altKey', 'ctrlKey', 'metaKey', 'shiftKey']) {
    assert.equal(isAdvanceKey(key(' ', {[modifier]: true})), false, modifier);
  }
});

test('Reader steps through every word once', () => {
  const reader = new Reader(3);
  assert.equal(reader.index, 0);
  assert.equal(reader.done, false);
  assert.equal(reader.advance(), true);
  assert.equal(reader.advance(), true);
  assert.equal(reader.done, false);
  assert.equal(reader.advance(), true);
  assert.equal(reader.done, true);
  assert.equal(reader.index, 3);
  assert.equal(reader.advance(), false);
  assert.equal(reader.index, 3);
});

test('Reader times from the first step to the last', () => {
  let now = 1000;
  const reader = new Reader(2, () => now);
  now = 60_000;
  assert.equal(reader.seconds, 0);
  reader.advance();
  now += 4_400;
  assert.equal(reader.seconds, 4);
  assert.equal(reader.finishedAt, null);
  reader.advance();
  now += 100_000;
  assert.equal(reader.seconds, 4);
  assert.equal(reader.finishedAt, 64_400);
});

test('Reader allows a short burst, then 400 words a minute', () => {
  let now = 0;
  const reader = new Reader(100, () => now);
  for (let i = 0; i < 5; i++) assert.equal(reader.advance(), true, `${i}`);
  assert.equal(reader.advance(), false);
  now += 149;
  assert.equal(reader.advance(), false);
  now += 1;
  assert.equal(reader.advance(), true);
  assert.equal(reader.advance(), false);
  assert.equal(reader.index, 6);
});

test('Reader saves up only a short burst during a pause', () => {
  let now = 0;
  const reader = new Reader(100, () => now);
  reader.advance();
  now += 60_000;
  for (let i = 0; i < 5; i++) assert.equal(reader.advance(), true, `${i}`);
  assert.equal(reader.advance(), false);
});

test('Reader at its fastest stays within the speed limit', () => {
  let now = 0;
  const reader = new Reader(400, () => now);
  while (!reader.done) {
    if (!reader.advance()) now += 1;
  }
  assert.equal(reader.seconds, 59);
  assert.equal(withinSpeedLimit(400, reader.seconds), true);
});

test('withinSpeedLimit allows the burst plus 400 words a minute', () => {
  // 0 seconds is anything under half a second.
  assert.equal(withinSpeedLimit(8, 0), true);
  assert.equal(withinSpeedLimit(9, 0), false);
  assert.equal(withinSpeedLimit(405, 60), true);
  assert.equal(withinSpeedLimit(409, 60), false);
  assert.equal(withinSpeedLimit(192, 47), true);
  assert.equal(withinSpeedLimit(192, 10), false);
});

test('wordsPerMinute rounds and skips a zero time', () => {
  assert.equal(wordsPerMinute(192, 47), 245);
  assert.equal(wordsPerMinute(3, 0), null);
});

test('formatDuration drops leading zero units', () => {
  assert.equal(formatDuration(0), '0s');
  assert.equal(formatDuration(42), '42s');
  assert.equal(formatDuration(252), '4m 12s');
  assert.equal(formatDuration(3605), '1h 0m 5s');
});
