import { test } from 'node:test';
import assert from 'node:assert/strict';
import { BUILDINGS, buildingFaces, SPEED_OF_SOUND } from '../src/city.js';
import {
  facadeReflection,
  groundReflection,
  computeReflections,
  excessDelaySec,
} from '../src/reflections.js';

test('ground reflection delays by the mirrored path', () => {
  const listener = [0, 2, 0];
  const source = [0, 10, -20];
  const r = groundReflection(listener, source);
  assert.ok(r);
  assert.equal(r.kind, 'ground');
  // Image at y=-10; path from (0,2,0) to (0,-10,-20)
  const expected = Math.hypot(0, -12, -20);
  assert.ok(Math.abs(r.pathLength - expected) < 1e-9);
  assert.ok(Math.abs(r.delaySec - expected / SPEED_OF_SOUND) < 1e-9);
  assert.ok(r.hit[1] === 0);
});

test('facade reflection against a west wall places the image correctly', () => {
  const face = buildingFaces(BUILDINGS).find((f) => f.id === 'nw-e');
  // East face of NW block is at x=-20. Source in the street east of it.
  const source = [0, 30, 50];
  const listener = [10, 1.7, 50];
  const r = facadeReflection(listener, source, face, BUILDINGS);
  assert.ok(r, 'expected a valid reflection');
  assert.ok(Math.abs(r.image[0] - (-40)) < 1e-6); // mirror of x=0 across x=-20
  assert.ok(Math.abs(r.hit[0] - (-20)) < 1e-6);
  assert.ok(r.delaySec > 0);
  assert.ok(r.gain > 0);
});

test('computeReflections returns ground plus facade hits, strongest first', () => {
  const listener = [0, 1.7, 0];
  const source = [5, 35, -40];
  const list = computeReflections(listener, source, BUILDINGS, { limit: 8 });
  assert.ok(list.length >= 1);
  assert.ok(list.some((r) => r.kind === 'ground'));
  for (let i = 1; i < list.length; i++) {
    assert.ok(list[i - 1].gain >= list[i].gain);
  }
  const top = list[0];
  assert.ok(excessDelaySec(top, listener, source) >= -1e-9);
});

test('reflection from the wrong side of a face is rejected', () => {
  const face = buildingFaces(BUILDINGS).find((f) => f.id === 'nw-e');
  // Source is west of the east face (inside/behind the building).
  const source = [-50, 30, 50];
  const listener = [0, 1.7, 50];
  assert.equal(facadeReflection(listener, source, face, BUILDINGS), null);
});
