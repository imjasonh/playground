import { test } from 'node:test';
import assert from 'node:assert/strict';
import { rayAabb, isOccluded } from '../src/occlusion.js';
import { BUILDINGS } from '../src/city.js';

test('ray hits a known AABB', () => {
  const box = { min: [1, -1, -1], max: [2, 1, 1] };
  const t = rayAabb([0, 0, 0], [1, 0, 0], box);
  assert.equal(t, 1);
});

test('ray misses when aimed past the box', () => {
  const box = { min: [1, -1, -1], max: [2, 1, 1] };
  assert.equal(rayAabb([0, 0, 0], [0, 1, 0], box), null);
});

test('heli behind the NW block is occluded from the street origin', () => {
  const nw = BUILDINGS.find((b) => b.id === 'nw');
  assert.ok(nw);
  const listener = [0, 1.7, (nw.min[2] + nw.max[2]) / 2];
  const source = [nw.min[0] - 40, 60, listener[2]];
  assert.equal(isOccluded(listener, source, BUILDINGS), true);
});

test('heli over the open avenue is not occluded', () => {
  const listener = [0, 1.7, 0];
  const source = [0, 80, -90];
  assert.equal(isOccluded(listener, source, BUILDINGS), false);
});
