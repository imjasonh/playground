import { test } from 'node:test';
import assert from 'node:assert/strict';
import { BUILDINGS } from '../src/city.js';
import { enclosureAt } from '../src/enclosure.js';

test('avenue center is more enclosed than far open ground', () => {
  const canyon = enclosureAt([0, 1.7, 0], BUILDINGS);
  const open = enclosureAt([0, 1.7, -200], BUILDINGS);
  assert.ok(canyon.amount > open.amount + 0.15);
  assert.ok(canyon.nearestWall < open.nearestWall);
  assert.ok(canyon.rt60Sec > open.rt60Sec);
});

test('enclosure amount stays in [0, 1]', () => {
  for (const p of [
    [0, 1.7, 0],
    [15, 1.7, 40],
    [-90, 1.7, 0],
    [0, 1.7, 150],
  ]) {
    const e = enclosureAt(p, BUILDINGS);
    assert.ok(e.amount >= 0 && e.amount <= 1);
    assert.ok(e.rt60Sec > 0);
  }
});
