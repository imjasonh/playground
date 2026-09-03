import { test } from 'node:test';
import assert from 'node:assert/strict';
import { buildImpulseResponse, irParamsForEnclosure } from '../src/impulseResponse.js';

class FakeCtx {
  constructor(sampleRate = 48000) {
    this.sampleRate = sampleRate;
  }
  createBuffer(channels, length, rate) {
    const chans = Array.from({ length: channels }, () => new Float32Array(length));
    return {
      numberOfChannels: channels,
      length,
      sampleRate: rate,
      getChannelData: (i) => chans[i],
    };
  }
}

test('IR params lengthen as enclosure rises', () => {
  const open = irParamsForEnclosure(0);
  const deep = irParamsForEnclosure(1);
  assert.ok(deep.durationSec > open.durationSec);
  assert.ok(deep.decay < open.decay);
});

test('buildImpulseResponse fills stereo noise that decays', () => {
  const ctx = new FakeCtx();
  const buf = buildImpulseResponse(ctx, { durationSec: 0.5, decay: 4, damping: 2 });
  assert.equal(buf.numberOfChannels, 2);
  assert.ok(buf.length > 1000);
  const L = buf.getChannelData(0);
  const early = rms(L, 0, 200);
  const late = rms(L, L.length - 400, L.length);
  assert.ok(early > late * 2);
});

function rms(arr, from, to) {
  let s = 0;
  const n = to - from;
  for (let i = from; i < to; i++) s += arr[i] * arr[i];
  return Math.sqrt(s / n);
}
