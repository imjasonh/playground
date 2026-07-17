export const MIN_BPM = 40;
export const MAX_BPM = 280;
export const DEFAULT_BPM = 120;
/** Engine macro/sequencer subdivision ticks per quarter note (at 4/4). */
export const TICKS_PER_STEP = 6;
export const STEPS_PER_BEAT = 4; // 16th notes when step = 1/4 beat

/**
 * @typedef {object} TransportState
 * @property {number} bpm
 * @property {boolean} playing
 * @property {boolean} recording
 * @property {number} step           current step index
 * @property {number} tickInStep     0 .. TICKS_PER_STEP-1
 * @property {number} sampleInTick   samples elapsed in current tick
 * @property {number} patternLength
 */

/**
 * @param {{ bpm?: number, patternLength?: number }} [opts]
 * @returns {TransportState}
 */
export function createTransport({
  bpm = DEFAULT_BPM,
  patternLength = 16,
} = {}) {
  return {
    bpm: clampBpm(bpm),
    playing: false,
    recording: false,
    step: 0,
    tickInStep: 0,
    sampleInTick: 0,
    patternLength: Math.max(4, patternLength | 0),
  };
}

/**
 * Seconds per sequencer step (16th note at STEPS_PER_BEAT=4).
 * @param {number} bpm
 */
export function secondsPerStep(bpm) {
  const beatsPerSecond = clampBpm(bpm) / 60;
  return 1 / (beatsPerSecond * STEPS_PER_BEAT);
}

/**
 * Seconds per macro/engine tick.
 * @param {number} bpm
 */
export function secondsPerTick(bpm) {
  return secondsPerStep(bpm) / TICKS_PER_STEP;
}

/**
 * Samples per engine tick at a given sample rate.
 * @param {number} bpm
 * @param {number} sampleRate
 */
export function samplesPerTick(bpm, sampleRate) {
  return secondsPerTick(bpm) * sampleRate;
}

/**
 * @param {TransportState} transport
 * @param {number} bpm
 */
export function setBpm(transport, bpm) {
  transport.bpm = clampBpm(bpm);
}

/**
 * @param {TransportState} transport
 * @param {boolean} playing
 */
export function setPlaying(transport, playing) {
  transport.playing = Boolean(playing);
  if (!playing) {
    transport.recording = false;
    transport.step = 0;
    transport.tickInStep = 0;
    transport.sampleInTick = 0;
  }
}

/**
 * @param {TransportState} transport
 * @param {boolean} recording
 */
export function setRecording(transport, recording) {
  transport.recording = Boolean(recording);
  if (recording) transport.playing = true;
}

/**
 * Advance transport by `sampleCount` samples.
 * Returns events that occurred: step boundaries and tick boundaries.
 *
 * @param {TransportState} transport
 * @param {number} sampleCount
 * @param {number} sampleRate
 * @returns {{ ticks: number, steps: number[], crossedStep: boolean }}
 */
export function advanceTransport(transport, sampleCount, sampleRate) {
  /** @type {number[]} */
  const steps = [];
  let ticks = 0;
  if (!transport.playing || sampleCount <= 0) {
    return { ticks: 0, steps, crossedStep: false };
  }

  const spt = samplesPerTick(transport.bpm, sampleRate);
  let remaining = sampleCount;
  let crossedStep = false;

  while (remaining > 0) {
    const room = spt - transport.sampleInTick;
    if (remaining < room) {
      transport.sampleInTick += remaining;
      remaining = 0;
      break;
    }
    remaining -= room;
    transport.sampleInTick = 0;
    ticks += 1;
    transport.tickInStep += 1;
    if (transport.tickInStep >= TICKS_PER_STEP) {
      transport.tickInStep = 0;
      transport.step = (transport.step + 1) % transport.patternLength;
      steps.push(transport.step);
      crossedStep = true;
    }
  }

  return { ticks, steps, crossedStep };
}

/**
 * Quantize a fractional step position to nearest step index.
 * @param {number} stepFloat
 * @param {number} patternLength
 */
export function quantizeStep(stepFloat, patternLength) {
  const len = Math.max(1, patternLength | 0);
  return ((Math.round(stepFloat) % len) + len) % len;
}

/**
 * Current fractional step position (for UI playhead).
 * @param {TransportState} transport
 * @param {number} sampleRate
 */
export function playheadStep(transport, sampleRate) {
  const spt = samplesPerTick(transport.bpm, sampleRate);
  const fracTick =
    spt > 0 ? transport.sampleInTick / spt : 0;
  return (
    transport.step +
    (transport.tickInStep + fracTick) / TICKS_PER_STEP
  );
}

function clampBpm(bpm) {
  const n = Number(bpm);
  if (!Number.isFinite(n)) return DEFAULT_BPM;
  return Math.min(MAX_BPM, Math.max(MIN_BPM, n));
}
