import { CHANNELS } from "../apu/constants.js";
import { TICKS_PER_STEP } from "./transport.js";

/**
 * @typedef {"pulse1"|"pulse2"|"triangle"|"noise"} ChannelId
 *
 * @typedef {object} StepNote
 * @property {number} [midi]        0–127; omit when `cut` is true
 * @property {number} [velocity]    0–15 volume override
 * @property {number} [length]      steps to hold (default 1)
 * @property {number} [gate]        ticks held in the final step (1–TICKS_PER_STEP)
 * @property {number} [slideTo]     glide toward this MIDI over the hold
 * @property {boolean} [cut]        force note-off on this step
 *
 * @typedef {object} Pattern
 * @property {string} [name]
 * @property {number} length
 * @property {Record<ChannelId, (StepNote|null)[]>} tracks
 */

export const DEFAULT_PATTERN_LENGTH = 16;
export const MIN_PATTERN_LENGTH = 4;
export const MAX_PATTERN_LENGTH = 64;

/**
 * @param {number} [length=DEFAULT_PATTERN_LENGTH]
 * @param {string} [name]
 * @returns {Pattern}
 */
export function createEmptyPattern(
  length = DEFAULT_PATTERN_LENGTH,
  name = "Pattern",
) {
  const len = clampLength(length);
  /** @type {Pattern} */
  const pattern = { name, length: len, tracks: {} };
  for (const ch of CHANNELS) {
    pattern.tracks[ch] = Array.from({ length: len }, () => null);
  }
  return pattern;
}

/**
 * @param {Pattern} pattern
 * @param {ChannelId} channel
 * @param {number} step
 * @param {StepNote|null} note
 * @returns {Pattern}
 */
export function setStep(pattern, channel, step, note) {
  assertChannel(channel);
  const next = clonePattern(pattern);
  const i = mod(step, next.length);
  next.tracks[channel][i] = note ? normalizeNote(note) : null;
  return next;
}

/**
 * @param {Pattern} pattern
 * @param {ChannelId} channel
 * @param {number} step
 * @returns {StepNote|null}
 */
export function getStep(pattern, channel, step) {
  assertChannel(channel);
  return pattern.tracks[channel][mod(step, pattern.length)] ?? null;
}

/**
 * @param {Pattern} pattern
 * @param {ChannelId} channel
 * @param {number} step
 */
export function clearStep(pattern, channel, step) {
  return setStep(pattern, channel, step, null);
}

/**
 * Place a note-cut (force release) on a step.
 * @param {Pattern} pattern
 * @param {ChannelId} channel
 * @param {number} step
 */
export function setCut(pattern, channel, step) {
  return setStep(pattern, channel, step, { cut: true });
}

/**
 * @param {Pattern} pattern
 * @param {number} length
 */
export function resizePattern(pattern, length) {
  const len = clampLength(length);
  /** @type {Pattern} */
  const next = { name: pattern.name, length: len, tracks: {} };
  for (const ch of CHANNELS) {
    const src = pattern.tracks[ch] || [];
    next.tracks[ch] = Array.from({ length: len }, (_, i) =>
      i < src.length ? (src[i] ? normalizeNote(src[i]) : null) : null,
    );
  }
  return next;
}

/**
 * @param {Pattern} pattern
 * @param {ChannelId} channel
 * @param {number} step
 * @param {number} midi
 * @param {{ velocity?: number, length?: number, gate?: number, slideTo?: number }} [opts]
 */
export function overdubNote(pattern, channel, step, midi, opts = {}) {
  /** @type {StepNote} */
  const note = { midi };
  if (opts.velocity != null) note.velocity = opts.velocity;
  if (opts.length != null) note.length = opts.length;
  if (opts.gate != null) note.gate = opts.gate;
  if (opts.slideTo != null) note.slideTo = opts.slideTo;
  return setStep(pattern, channel, step, note);
}

/**
 * @param {Pattern} pattern
 * @returns {Pattern}
 */
export function clonePattern(pattern) {
  /** @type {Pattern} */
  const next = {
    name: pattern?.name || "Pattern",
    length: pattern?.length || DEFAULT_PATTERN_LENGTH,
    tracks: {},
  };
  for (const ch of CHANNELS) {
    next.tracks[ch] = Array.from({ length: next.length }, (_, i) => {
      const cell = pattern.tracks[ch]?.[i];
      return cell ? normalizeNote(cell) : null;
    });
  }
  return next;
}

/**
 * @param {Pattern} pattern
 * @returns {object}
 */
export function patternToJSON(pattern) {
  const tracks = {};
  for (const ch of CHANNELS) {
    tracks[ch] = pattern.tracks[ch].map((n) => (n ? noteToJSON(n) : null));
  }
  return {
    name: pattern.name || "Pattern",
    length: pattern.length,
    tracks,
  };
}

/**
 * @param {unknown} raw
 * @returns {Pattern}
 */
export function patternFromJSON(raw) {
  const o = raw && typeof raw === "object" ? raw : {};
  const length = clampLength(o.length ?? DEFAULT_PATTERN_LENGTH);
  const base = createEmptyPattern(
    length,
    typeof o.name === "string" ? o.name : "Pattern",
  );
  const tracks = o.tracks && typeof o.tracks === "object" ? o.tracks : {};
  for (const ch of CHANNELS) {
    const row = Array.isArray(tracks[ch]) ? tracks[ch] : [];
    for (let i = 0; i < length; i += 1) {
      const cell = row[i];
      base.tracks[ch][i] = cell ? normalizeNote(cell) : null;
    }
  }
  return base;
}

/**
 * @param {Pattern} pattern
 */
export function countNotes(pattern) {
  let n = 0;
  for (const ch of CHANNELS) {
    for (const cell of pattern.tracks[ch]) {
      if (cell) n += 1;
    }
  }
  return n;
}

/**
 * Total hold ticks for a note (length steps with gate on the last).
 * @param {StepNote} note
 */
export function noteHoldTicks(note) {
  if (note.cut) return 0;
  const length = Math.max(1, note.length ?? 1);
  const gate = clampInt(note.gate ?? TICKS_PER_STEP, 1, TICKS_PER_STEP);
  return (length - 1) * TICKS_PER_STEP + gate;
}

/**
 * @param {unknown} note
 * @returns {StepNote}
 */
export function normalizeNote(note) {
  if (note?.cut) {
    return { cut: true };
  }
  const midi = clampInt(note?.midi ?? 60, 0, 127);
  /** @type {StepNote} */
  const out = { midi };
  if (note?.velocity != null) out.velocity = clampInt(note.velocity, 0, 15);
  if (note?.length != null) {
    out.length = Math.max(1, clampInt(note.length, 1, 64));
  }
  if (note?.gate != null) {
    out.gate = clampInt(note.gate, 1, TICKS_PER_STEP);
  }
  if (note?.slideTo != null) {
    out.slideTo = clampInt(note.slideTo, 0, 127);
  }
  return out;
}

/**
 * @param {StepNote} note
 */
function noteToJSON(note) {
  if (note.cut) return { cut: true };
  /** @type {Record<string, number|boolean>} */
  const out = { midi: note.midi };
  if (note.velocity != null) out.velocity = note.velocity;
  if (note.length != null && note.length !== 1) out.length = note.length;
  if (note.gate != null && note.gate !== TICKS_PER_STEP) out.gate = note.gate;
  if (note.slideTo != null) out.slideTo = note.slideTo;
  return out;
}

function assertChannel(channel) {
  if (!CHANNELS.includes(channel)) {
    throw new Error(`Unknown channel: ${channel}`);
  }
}

function clampLength(length) {
  const n = Number(length) | 0;
  if (n < MIN_PATTERN_LENGTH) return MIN_PATTERN_LENGTH;
  if (n > MAX_PATTERN_LENGTH) return MAX_PATTERN_LENGTH;
  return Math.max(MIN_PATTERN_LENGTH, Math.round(n / 4) * 4);
}

function clampInt(value, min, max) {
  return Math.min(max, Math.max(min, Number(value) | 0));
}

function mod(n, m) {
  return ((n % m) + m) % m;
}
