import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  helicopterPath,
  helicopterVelocity,
  cityBounds,
  BUILDINGS,
} from '../src/city.js';
import { FollowFlight, findClearOffset } from '../src/follow.js';
import { isOccluded } from '../src/occlusion.js';

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
  const d0 = [p1[0] - p0[0], p1[1] - p0[1], p1[2] - p0[2]];
  assert.ok(Math.hypot(d0[0], d0[1], d0[2]) > 5, 'moves along the lane');
  const p2 = helicopterPath(2.5, { mode: 'traverse' });
  const d1 = [p2[0] - p1[0], p2[1] - p1[1], p2[2] - p1[2]];
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

test('traverse and orbit overflights clear every rooftop', () => {
  const { yMax } = cityBounds(BUILDINGS);
  for (let t = 0; t < 200; t += 0.5) {
    const tr = helicopterPath(t, { mode: 'traverse' });
    assert.ok(tr[1] > yMax, `traverse y=${tr[1]} must clear yMax=${yMax}`);
    const orb = helicopterPath(t, { mode: 'orbit' });
    assert.ok(orb[1] > yMax, `orbit y=${orb[1]} must clear yMax=${yMax}`);
  }
});

test('orbit mode circles above the district', () => {
  const a = helicopterPath(0, { mode: 'orbit' });
  const b = helicopterPath(8, { mode: 'orbit' });
  assert.ok(Math.hypot(a[0] - b[0], a[2] - b[2]) > 40);
});

test('findClearOffset returns a visible perch above the avenue', () => {
  const listener = [0, 1.7, 0];
  const height = cityBounds().yMax + 30;
  const p = findClearOffset(listener, height, BUILDINGS, 0);
  assert.ok(p, 'expected a clear offset');
  assert.equal(isOccluded(listener, p, BUILDINGS), false);
  assert.ok(p[1] > cityBounds().yMax);
});

test('follow searches until LOS then tracks listener motion', () => {
  const follow = new FollowFlight(BUILDINGS);
  const listener = [0, 1.7, 0];
  follow.reset(listener);
  assert.equal(follow.phase, 'search');

  let sawTrack = false;
  let t = 0;
  for (let i = 0; i < 800; i++) {
    const sample = follow.update(0.05, listener);
    t += 0.05;
    if (sample.phase === 'track' && sample.canSee) {
      sawTrack = true;
      break;
    }
  }
  assert.ok(sawTrack, `never acquired LOS after ${t.toFixed(1)}s`);

  const before = follow.pos.slice();
  const moved = [80, 1.7, 40];
  for (let i = 0; i < 400; i++) follow.update(0.05, moved);
  const after = follow.pos;
  assert.ok(
    Math.hypot(after[0] - before[0], after[2] - before[2]) > 15,
    'heli should relocate when the listener moves',
  );
  const distToMoved = Math.hypot(after[0] - moved[0], after[2] - moved[2]);
  const distToOrigin = Math.hypot(after[0] - listener[0], after[2] - listener[2]);
  assert.ok(
    distToMoved < distToOrigin,
    `should close on new listener (toMoved=${distToMoved.toFixed(0)} toOrigin=${distToOrigin.toFixed(0)})`,
  );
});
