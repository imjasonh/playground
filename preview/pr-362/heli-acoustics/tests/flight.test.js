import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  helicopterPath,
  helicopterVelocity,
  cityBounds,
  BUILDINGS,
} from '../src/city.js';

test('city spans hundreds of meters with many blocks', () => {
  const b = cityBounds(BUILDINGS);
  assert.ok(BUILDINGS.length >= 9);
  assert.ok(b.spanX >= 500);
  assert.ok(b.spanZ >= 500);
  assert.ok(b.yMax >= 200);
});

test('traverse mode flies straight then pauses before the next leg', () => {
  const p0 = helicopterPath(0.5, { mode: 'traverse' });
  const p1 = helicopterPath(1.5, { mode: 'traverse' });
  // First leg is a straight overflight (constant velocity, no street constraint).
  const d0 = [p1[0] - p0[0], p1[1] - p0[1], p1[2] - p0[2]];
  assert.ok(Math.hypot(d0[0], d0[1], d0[2]) > 5, 'moves along the lane');
  const p2 = helicopterPath(2.5, { mode: 'traverse' });
  const d1 = [p2[0] - p1[0], p2[1] - p1[1], p2[2] - p1[2]];
  // Same direction (collinear step) while cruising.
  const cross = Math.hypot(
    d0[1] * d1[2] - d0[2] * d1[1],
    d0[2] * d1[0] - d0[0] * d1[2],
    d0[0] * d1[1] - d0[1] * d1[0],
  );
  assert.ok(cross < 1e-6, 'cruise stays on a straight line');

  let sawPause = false;
  for (let t = 0; t < 120; t += 0.25) {
    const v = helicopterVelocity(t, { mode: 'traverse' });
    const speed = Math.hypot(v[0], v[1], v[2]);
    if (speed < 0.05) {
      const a = helicopterPath(t, { mode: 'traverse' });
      const b = helicopterPath(t + 0.5, { mode: 'traverse' });
      assert.ok(Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]) < 0.05);
      sawPause = true;
      break;
    }
  }
  assert.ok(sawPause, 'expected a pause between traverse legs');
});

test('traverse overflights clear every rooftop', () => {
  const { yMax } = cityBounds(BUILDINGS);
  for (let t = 0; t < 200; t += 0.5) {
    const p = helicopterPath(t, { mode: 'traverse' });
    assert.ok(p[1] > yMax, `heli y=${p[1]} must clear yMax=${yMax} at t=${t}`);
  }
});

test('orbit mode still circles the canyon', () => {
  const a = helicopterPath(0, { mode: 'orbit' });
  const b = helicopterPath(7, { mode: 'orbit' });
  assert.ok(Math.hypot(a[0] - b[0], a[2] - b[2]) > 40);
});
