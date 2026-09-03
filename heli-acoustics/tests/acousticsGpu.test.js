import { test } from 'node:test';
import assert from 'node:assert/strict';
import { BUILDINGS } from '../src/city.js';
import { GpuAcoustics } from '../src/acousticsGpu.js';

test('GpuAcoustics.init rejects when WebGPU is missing', async () => {
  const gpu = new GpuAcoustics({ buildings: BUILDINGS, limit: 4 });
  await assert.rejects(() => gpu.init(), /WebGPU is required/);
});
