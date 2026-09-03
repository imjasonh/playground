import { test } from 'node:test';
import assert from 'node:assert/strict';
import { BUILDINGS, helicopterPath } from '../src/city.js';
import { GpuAcoustics, computeAcousticsCpu } from '../src/acousticsGpu.js';

test('GpuAcoustics.init rejects when WebGPU is missing', async () => {
  const gpu = new GpuAcoustics({ buildings: BUILDINGS, limit: 4 });
  await assert.rejects(() => gpu.init(), /WebGPU is required/);
});

test('reference acoustics returns occlusion, reflections, enclosure', () => {
  const listener = [0, 1.7, 0];
  const source = helicopterPath(0);
  const r = computeAcousticsCpu(listener, source, BUILDINGS, 12);
  assert.equal(r.backend, 'reference');
  assert.ok(r.occlusion === 0 || r.occlusion === 1);
  assert.ok(Array.isArray(r.reflections));
  assert.ok(r.enclosure.amount >= 0 && r.enclosure.amount <= 1);
});

test('taller canyon produces occlusion on more of the orbit', () => {
  const listener = [0, 1.7, 0];
  let blocked = 0;
  for (let t = 0; t < 18; t += 0.5) {
    const r = computeAcousticsCpu(listener, helicopterPath(t), BUILDINGS, 12);
    if (r.occlusion > 0) blocked++;
  }
  // With mid-canyon flight and tall towers, expect occlusion on a sizable share.
  assert.ok(blocked >= 8, `expected frequent occlusion, got ${blocked}/36`);
});

test('orbit finds both order-1 and order-2 reflections', () => {
  const listener = [0, 1.7, 0];
  let saw1 = false;
  let saw2 = false;
  for (let t = 0; t < 18; t += 0.5) {
    const r = computeAcousticsCpu(listener, helicopterPath(t), BUILDINGS, 12);
    if (r.reflections.some((x) => x.order === 1)) saw1 = true;
    if (r.reflections.some((x) => x.order === 2)) saw2 = true;
  }
  assert.ok(saw1);
  assert.ok(saw2);
});
