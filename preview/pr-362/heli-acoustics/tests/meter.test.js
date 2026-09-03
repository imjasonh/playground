import { test } from 'node:test';
import assert from 'node:assert/strict';
import { channelRms, stereoBalance } from '../src/meter.js';

function fakeBuffer(channels) {
  return {
    getChannelData(i) {
      return channels[i];
    },
  };
}

test('channelRms is zero for silence', () => {
  assert.equal(channelRms(fakeBuffer([new Float32Array(8)]), 0), 0);
});

test('channelRms matches known RMS', () => {
  // values 1, -1, 1, -1 → mean square 1 → rms 1
  assert.equal(channelRms(fakeBuffer([new Float32Array([1, -1, 1, -1])]), 0), 1);
});

test('stereoBalance is negative when left is louder', () => {
  assert.ok(stereoBalance(0.4, 0.1) < 0);
  assert.ok(stereoBalance(0.1, 0.4) > 0);
  assert.equal(stereoBalance(0, 0), 0);
  assert.equal(stereoBalance(0.5, 0.5), 0);
});
