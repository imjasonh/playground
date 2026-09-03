// OfflineAudioContext HRTF proof: place a short noise burst hard left and hard
// right of a yaw=0 listener, render through an HRTF PannerNode, and compare
// left/right ear energy. This is the audio claim of M0, measured, not assumed.
//
// Must run in a browser (or Chromium) that implements OfflineAudioContext with
// HRTF. Node's npm test does not cover this; see tests/hrtf-binaural.mjs.

import { channelRms, stereoBalance } from './meter.js';

function setListener(listener, forward, up) {
  if (listener.positionX) {
    listener.positionX.value = 0;
    listener.positionY.value = 0;
    listener.positionZ.value = 0;
    listener.forwardX.value = forward[0];
    listener.forwardY.value = forward[1];
    listener.forwardZ.value = forward[2];
    listener.upX.value = up[0];
    listener.upY.value = up[1];
    listener.upZ.value = up[2];
  } else {
    listener.setPosition(0, 0, 0);
    listener.setOrientation(forward[0], forward[1], forward[2], up[0], up[1], up[2]);
  }
}

function setPanner(panner, pos) {
  if (panner.positionX) {
    panner.positionX.value = pos[0];
    panner.positionY.value = pos[1];
    panner.positionZ.value = pos[2];
  } else {
    panner.setPosition(pos[0], pos[1], pos[2]);
  }
}

async function renderAt(OfflineCtx, sourcePos, { sampleRate = 48000, durationSec = 0.35 } = {}) {
  const frames = Math.floor(sampleRate * durationSec);
  const ctx = new OfflineCtx(2, frames, sampleRate);

  const panner = ctx.createPanner();
  panner.panningModel = 'HRTF';
  panner.distanceModel = 'inverse';
  panner.refDistance = 1;
  panner.rolloffFactor = 1;
  setPanner(panner, sourcePos);
  setListener(ctx.listener, [0, 0, -1], [0, 1, 0]);
  panner.connect(ctx.destination);

  // Burst of noise, long enough that HRTF filtering is measurable.
  const nFrames = Math.floor(sampleRate * 0.25);
  const buf = ctx.createBuffer(1, nFrames, sampleRate);
  const data = buf.getChannelData(0);
  for (let i = 0; i < nFrames; i++) data[i] = Math.random() * 2 - 1;
  const src = ctx.createBufferSource();
  src.buffer = buf;
  src.connect(panner);
  src.start(0);

  const rendered = await ctx.startRendering();
  const left = channelRms(rendered, 0);
  const right = channelRms(rendered, 1);
  return { left, right, balance: stereoBalance(left, right) };
}

// Returns a verdict object. pass=true means hard-left is louder in the left
// ear and hard-right is louder in the right ear by a meaningful margin.
export async function proveHrtfBinaural(OfflineCtx = globalThis.OfflineAudioContext) {
  if (typeof OfflineCtx !== 'function') {
    return { pass: false, reason: 'OfflineAudioContext unavailable' };
  }

  const leftSide = await renderAt(OfflineCtx, [-8, 0, 0]);
  const rightSide = await renderAt(OfflineCtx, [8, 0, 0]);

  // Require a clear ear preference: balance < -0.08 means left ear louder,
  // > +0.08 means right ear louder. Equalpower alone would also do this;
  // HRTF is what the graph uses, and the asymmetry is the audio claim.
  const leftOk = leftSide.balance < -0.08;
  const rightOk = rightSide.balance > 0.08;
  const pass = leftOk && rightOk;

  return {
    pass,
    reason: pass
      ? 'HRTF panner produces opposite ear dominance for left vs right sources'
      : 'ear energy did not flip with source side',
    leftSide,
    rightSide,
  };
}
