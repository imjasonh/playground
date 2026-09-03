// Procedural stereo impulse response for late reverb. Noise with exponential
// decay and progressive high-frequency damping. Duration/decay track the
// enclosure estimate so a street canyon rings longer than an open plaza.

/**
 * @param {BaseAudioContext} ctx
 * @param {{ durationSec?: number, decay?: number, damping?: number }} [opts]
 * @returns {AudioBuffer}
 */
export function buildImpulseResponse(
  ctx,
  { durationSec = 1.8, decay = 3.2, damping = 2.5 } = {},
) {
  const n = Math.max(1, Math.floor(ctx.sampleRate * durationSec));
  const buf = ctx.createBuffer(2, n, ctx.sampleRate);
  for (let ch = 0; ch < 2; ch++) {
    const data = buf.getChannelData(ch);
    // Slightly different seed per channel so the field is not mono.
    let state = (ch + 1) * 1103515245 + 12345;
    for (let i = 0; i < n; i++) {
      state = (state * 1664525 + 1013904223) >>> 0;
      const noise = state / 0xffffffff * 2 - 1;
      const t = i / ctx.sampleRate;
      const env = Math.exp(-decay * t) * Math.exp(-damping * t * 0.35);
      data[i] = noise * env;
    }
  }
  return buf;
}

/**
 * Map enclosure amount to Convolver IR parameters. Higher enclosure → longer,
 * louder, darker tail.
 * @param {number} amount enclosure in [0,1]
 */
export function irParamsForEnclosure(amount) {
  const a = Math.max(0, Math.min(1, amount));
  return {
    durationSec: 0.9 + a * 1.4,
    decay: 5.5 - a * 3.2,
    damping: 4.5 - a * 2.2,
  };
}
