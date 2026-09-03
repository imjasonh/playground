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
  // First leg is west→east at constant z≈-90.
  assert.ok(Math.abs(p0[2] - p1[2]) < 1e-6, 'leg holds constant latitude');
  assert.ok(p1[0] > p0[0], 'moves east along the lane');

  // Find a pause: velocity near zero while position holds.
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

test('orbit mode still circles the canyon', () => {
  const a = helicopterPath(0, { mode: 'orbit' });
  const b = helicopterPath(7, { mode: 'orbit' });
  assert.ok(Math.hypot(a[0] - b[0], a[2] - b[2]) > 40);
});
