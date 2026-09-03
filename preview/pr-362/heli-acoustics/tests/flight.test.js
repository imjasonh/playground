import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  helicopterPath,
  helicopterVelocity,
  cityBounds,
  BUILDINGS,
} from '../src/city.js';
import { FollowFlight, findClearOffset, avoidBuildings, buildingAt, FOLLOW_CRUISE_Y } from '../src/follow.js';
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

test('findClearOffset returns a visible perch at follow altitude', () => {
  const listener = [0, 1.7, 0];
  const height = 42;
  const p = findClearOffset(listener, height, BUILDINGS, 0);
  assert.ok(p, 'expected a clear offset');
  assert.equal(isOccluded(listener, p, BUILDINGS), false);
  assert.ok(Math.abs(p[1] - height) < 1e-6);
});

test('follow searches until LOS then tracks listener motion', () => {
  const follow = new FollowFlight(BUILDINGS);
  const listener = [0, 1.7, 0];
  follow.reset(listener);
  assert.equal(follow.phase, 'search');

  let sawTrack = false;
  let t = 0;
  for (let i = 0; i < 2500; i++) {
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
  for (let i = 0; i < 1500; i++) follow.update(0.05, moved);
  const after = follow.pos;
  assert.ok(
    Math.hypot(after[0] - before[0], after[2] - before[2]) > 15,
    'heli should relocate when the listener moves',
  );
  assert.ok(
    Math.hypot(after[0] - moved[0], after[2] - moved[2]) < 160,
    `should end near the new listener (dist=${Math.hypot(after[0] - moved[0], after[2] - moved[2]).toFixed(0)})`,
  );
});

test('follow cruises lower than orbit/traverse skyline', () => {
  const { yMax } = cityBounds(BUILDINGS);
  const follow = new FollowFlight(BUILDINGS);
  follow.reset([0, 1.7, 0]);
  assert.ok(follow.pos[1] < yMax * 0.4, `follow y=${follow.pos[1]} should be low canyon`);
  const orb = helicopterPath(0, { mode: 'orbit' });
  const tr = helicopterPath(0, { mode: 'traverse' });
  assert.ok(orb[1] > yMax);
  assert.ok(tr[1] > yMax);
  assert.ok(follow.pos[1] < orb[1] - 50);
});

test('follow turns and climbs smoothly (no snap headings)', () => {
  const follow = new FollowFlight(BUILDINGS);
  follow.reset([0, 1.7, 0]);
  // Force a hard goal behind a tall block so avoidance must climb or turn.
  const nw = BUILDINGS.find((b) => b.id === 'nw');
  follow.pos = [nw.min[0] - 40, 42, (nw.min[2] + nw.max[2]) / 2];
  follow.vel = [12, 0, 0];
  follow.yaw = Math.PI / 2; // facing +x into the block
  const goal = [nw.max[0] + 40, 42, follow.pos[2]];
  const adjusted = avoidBuildings(follow.pos, follow.vel, goal, BUILDINGS, 42);
  assert.ok(
    adjusted[1] > 42 + 5 ||
      Math.hypot(adjusted[0] - goal[0], adjusted[2] - goal[2]) > 5 ||
      adjusted[0] !== goal[0],
    `expected climb or detour, got ${adjusted}`,
  );

  let maxYawRate = 0;
  let prevYaw = follow.yaw;
  for (let i = 0; i < 120; i++) {
    const s = follow.update(0.05, [0, 1.7, 0]);
    let d = s.yaw - prevYaw;
    while (d > Math.PI) d -= Math.PI * 2;
    while (d < -Math.PI) d += Math.PI * 2;
    maxYawRate = Math.max(maxYawRate, Math.abs(d) / 0.05);
    prevYaw = s.yaw;
    assert.ok(!buildingAt(s.position[0], s.position[2], s.position[1], BUILDINGS));
  }
  assert.ok(maxYawRate <= 0.9 + 1e-6, `yaw rate ${maxYawRate} exceeds heli limit`);
});
