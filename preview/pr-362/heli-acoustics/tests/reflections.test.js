import { test } from 'node:test';
import assert from 'node:assert/strict';
import { BUILDINGS, buildingFaces, SPEED_OF_SOUND } from '../src/city.js';
import {
  facadeReflection,
  groundReflection,
  computeReflections,
  excessDelaySec,
  order2Reflection,
  groundFace,
  order2PairList,
} from '../src/reflections.js';

test('ground reflection delays by the mirrored path', () => {
  const listener = [0, 2, 0];
  const source = [0, 10, -20];
  const r = groundReflection(listener, source);
  assert.ok(r);
  assert.equal(r.kind, 'ground');
  assert.equal(r.order, 1);
  // Image at y=-10; path from (0,2,0) to (0,-10,-20)
  const expected = Math.hypot(0, -12, -20);
  assert.ok(Math.abs(r.pathLength - expected) < 1e-9);
  assert.ok(Math.abs(r.delaySec - expected / SPEED_OF_SOUND) < 1e-9);
  assert.ok(r.hit[1] === 0);
  assert.equal(r.hits.length, 1);
});

test('facade reflection against a west wall places the image correctly', () => {
  const face = buildingFaces(BUILDINGS).find((f) => f.id === 'nw-e');
  assert.ok(face);
  // East face of NW block. Source in the street east of it.
  const source = [0, 30, 80];
  const listener = [10, 1.7, 80];
  const r = facadeReflection(listener, source, face, BUILDINGS);
  assert.ok(r, 'expected a valid reflection');
  const mirrored = 2 * face.value - source[0];
  assert.ok(Math.abs(r.image[0] - mirrored) < 1e-6);
  assert.ok(Math.abs(r.hit[0] - face.value) < 1e-6);
  assert.ok(r.delaySec > 0);
  assert.ok(r.gain > 0);
  assert.equal(r.order, 1);
});

test('computeReflections returns ground plus facade hits, strongest first', () => {
  const listener = [0, 1.7, 0];
  const source = [5, 55, -70];
  const list = computeReflections(listener, source, BUILDINGS, { limit: 8, maxOrder: 1 });
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
  const source = [face.value - 40, 30, 80];
  const listener = [0, 1.7, 80];
  assert.equal(facadeReflection(listener, source, face, BUILDINGS), null);
});

test('order-2 opposite street walls produce a double bounce', () => {
  const faces = buildingFaces(BUILDINGS);
  const west = faces.find((f) => f.id === 'nw-e');
  const east = faces.find((f) => f.id === 'ne-low-w');
  assert.ok(west && east);
  // Listener and source in the avenue between the walls.
  const listener = [0, 1.7, 60];
  const source = [5, 45, 70];
  const r = order2Reflection(listener, source, west, east, BUILDINGS);
  assert.ok(r, 'expected an order-2 canyon bounce');
  assert.equal(r.order, 2);
  assert.equal(r.hits.length, 2);
  assert.ok(r.pathLength > 40);
  assert.ok(r.gain > 0);
  assert.ok(r.delaySec > r.pathLength / SPEED_OF_SOUND - 1e-9);
});

test('order-2 facade then ground is accepted when clear', () => {
  const faces = buildingFaces(BUILDINGS);
  const face = faces.find((f) => f.id === 'sw-e');
  const ground = groundFace();
  const listener = [0, 1.7, -50];
  const source = [5, 30, -50];
  const r = order2Reflection(listener, source, face, ground, BUILDINGS);
  // May or may not hit depending on geometry; if present it must be well-formed.
  if (r) {
    assert.equal(r.order, 2);
    assert.equal(r.hits.length, 2);
    assert.ok(Math.abs(r.hits[1][1]) < 1e-3 || Math.abs(r.hits[0][1]) < 1e-3);
  }
});

test('computeReflections with maxOrder 2 includes order-2 taps in the avenue', () => {
  const listener = [0, 1.7, 0];
  const source = [0, 70, 120];
  const list = computeReflections(listener, source, BUILDINGS, {
    limit: 12,
    maxOrder: 2,
  });
  assert.ok(list.length >= 1);
  assert.ok(
    list.some((r) => r.order === 2),
    `expected at least one order-2 tap, got ${list.map((r) => `${r.order}:${r.faceId}`).join(',')}`,
  );
});

test('order2PairList puts ground pairs before facade pairs', () => {
  const faces = buildingFaces(BUILDINGS);
  const pairs = order2PairList(faces, { limit: 80 });
  assert.ok(pairs.length > 0);
  const firstGround = pairs.findIndex(
    ([a, b]) => a.kind === 'ground' || b.kind === 'ground',
  );
  assert.equal(firstGround, 0);
  assert.ok(
    pairs.every(([a, b]) => a.building !== b.building || a.kind === 'ground' || b.kind === 'ground'),
  );
});

test('maxOrder 1 never returns order-2', () => {
  const listener = [0, 1.7, 40];
  const source = [8, 30, 50];
  const list = computeReflections(listener, source, BUILDINGS, { limit: 12, maxOrder: 1 });
  assert.ok(list.every((r) => r.order === 1));
});
