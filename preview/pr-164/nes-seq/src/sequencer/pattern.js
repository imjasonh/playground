import { CHANNELS } from "../apu/constants.js";

/**
 * @typedef {"pulse1"|"pulse2"|"triangle"|"noise"} ChannelId
 *
 * @typedef {object} StepNote
 * @property {number} midi          0–127
 * @property {number} [velocity]    0–15 volume override; omit = instrument default
 * @property {number} [length]      steps to hold (default 1)
 *
 * @typedef {object} Pattern
 * @property {number} length        step count
 * @property {Record<ChannelId, (StepNote|null)[]>} tracks
 */

export const DEFAULT_PATTERN_LENGTH = 16;
export const MIN_PATTERN_LENGTH = 4;
export const MAX_PATTERN_LENGTH = 64;

/**
 * @param {number} [length=DEFAULT_PATTERN_LENGTH]
 * @returns {Pattern}
 */
export function createEmptyPattern(length = DEFAULT_PATTERN_LENGTH) {
  const len = clampLength(length);
  /** @type {Pattern} */
  const pattern = { length: len, tracks: {} };
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
 * Clear a step (note off / empty).
 * @param {Pattern} pattern
 * @param {ChannelId} channel
 * @param {number} step
 */
export function clearStep(pattern, channel, step) {
  return setStep(pattern, channel, step, null);
}

/**
 * Resize pattern, preserving existing steps (truncate or pad with nulls).
 * @param {Pattern} pattern
 * @param {number} length
 */
export function resizePattern(pattern, length) {
  const len = clampLength(length);
  /** @type {Pattern} */
  const next = { length: len, tracks: {} };
  for (const ch of CHANNELS) {
    const src = pattern.tracks[ch] || [];
    next.tracks[ch] = Array.from({ length: len }, (_, i) =>
      i < src.length ? (src[i] ? normalizeNote(src[i]) : null) : null,
    );
  }
  return next;
}

/**
 * Overdub: write a note onto a step, replacing whatever was there.
 * @param {Pattern} pattern
 * @param {ChannelId} channel
 * @param {number} step
 * @param {number} midi
 * @param {{ velocity?: number, length?: number }} [opts]
 */
export function overdubNote(pattern, channel, step, midi, opts = {}) {
  /** @type {import("./pattern.js").StepNote} */
  const note = { midi };
  if (opts.velocity != null) note.velocity = opts.velocity;
  if (opts.length != null) note.length = opts.length;
  return setStep(pattern, channel, step, note);
}

/**
 * @param {Pattern} pattern
 * @returns {Pattern}
 */
export function clonePattern(pattern) {
  /** @type {Pattern} */
  const next = { length: pattern.length, tracks: {} };
  for (const ch of CHANNELS) {
    next.tracks[ch] = (pattern.tracks[ch] || []).map((n) =>
      n ? normalizeNote(n) : null,
    );
  }
  // Ensure all channels exist even if source was partial.
  for (const ch of CHANNELS) {
    if (!next.tracks[ch] || next.tracks[ch].length !== next.length) {
      next.tracks[ch] = Array.from({ length: next.length }, (_, i) =>
        next.tracks[ch]?.[i] ? normalizeNote(next.tracks[ch][i]) : null,
      );
    }
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
    tracks[ch] = pattern.tracks[ch].map((n) =>
      n
        ? {
            midi: n.midi,
            ...(n.velocity != null ? { velocity: n.velocity } : {}),
            ...(n.length != null && n.length !== 1 ? { length: n.length } : {}),
          }
        : null,
    );
  }
  return { length: pattern.length, tracks };
}

/**
 * @param {unknown} raw
 * @returns {Pattern}
 */
export function patternFromJSON(raw) {
  const o = raw && typeof raw === "object" ? raw : {};
  const length = clampLength(o.length ?? DEFAULT_PATTERN_LENGTH);
  const base = createEmptyPattern(length);
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
 * Count non-empty steps across all channels.
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
 * @param {unknown} note
 * @returns {StepNote}
 */
export function normalizeNote(note) {
  const midi = clampInt(note?.midi ?? 60, 0, 127);
  /** @type {StepNote} */
  const out = { midi };
  if (note?.velocity != null) out.velocity = clampInt(note.velocity, 0, 15);
  if (note?.length != null) out.length = Math.max(1, clampInt(note.length, 1, 64));
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
  // Snap to multiples of 4 for tracker friendliness.
  return Math.max(MIN_PATTERN_LENGTH, Math.round(n / 4) * 4);
}

function clampInt(value, min, max) {
  return Math.min(max, Math.max(min, Number(value) | 0));
}

function mod(n, m) {
  return ((n % m) + m) % m;
}
