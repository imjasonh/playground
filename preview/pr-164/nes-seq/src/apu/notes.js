import { CPU_CLOCK_NTSC, NOISE_PERIODS_NTSC } from "./constants.js";

/** Lowest MIDI note that maps cleanly onto the NES pulse/triangle range. */
export const MIN_MELODIC_MIDI = 24; // C1
/** Highest MIDI note before the pulse period collapses / mutes. */
export const MAX_MELODIC_MIDI = 108; // C8

/**
 * Convert a MIDI note number to Hz (A4 = 440).
 * @param {number} midi
 * @returns {number}
 */
export function midiToHz(midi) {
  return 440 * 2 ** ((midi - 69) / 12);
}

/**
 * Pulse/triangle timer period for a MIDI note.
 * period = round(CPU / (16 * freq)) - 1, clamped to the hardware 11-bit range.
 * Values below 8 are muted by the pulse sweep unit on real hardware.
 *
 * @param {number} midi
 * @param {number} [cpuClock=CPU_CLOCK_NTSC]
 * @returns {number} 11-bit timer period (0–0x7FF)
 */
export function midiToTimerPeriod(midi, cpuClock = CPU_CLOCK_NTSC) {
  const freq = midiToHz(midi);
  if (!(freq > 0) || !Number.isFinite(freq)) return 0;
  const period = Math.round(cpuClock / (16 * freq) - 1);
  return clampInt(period, 0, 0x7ff);
}

/**
 * Best-effort reverse: timer period → nearest MIDI note.
 * @param {number} period
 * @param {number} [cpuClock=CPU_CLOCK_NTSC]
 * @returns {number}
 */
export function timerPeriodToMidi(period, cpuClock = CPU_CLOCK_NTSC) {
  const p = period + 1;
  if (p <= 0) return MIN_MELODIC_MIDI;
  const freq = cpuClock / (16 * p);
  const midi = Math.round(69 + 12 * Math.log2(freq / 440));
  return clampInt(midi, 0, 127);
}

/**
 * Map a MIDI note (or drum-style pitch) onto a noise period index 0–15.
 * Higher MIDI → shorter period (brighter noise), matching tracker conventions.
 *
 * @param {number} midi
 * @returns {number}
 */
export function midiToNoisePeriodIndex(midi) {
  // Spread MIDI 36–84 across the 16 noise periods.
  const t = (midi - 36) / (84 - 36);
  const idx = Math.round((1 - clamp(t, 0, 1)) * 15);
  return clampInt(idx, 0, 15);
}

/**
 * @param {number} index
 * @returns {number}
 */
export function noisePeriodCycles(index) {
  return NOISE_PERIODS_NTSC[clampInt(index, 0, 15)];
}

/**
 * Build a lookup table of pulse/triangle periods for MIDI 0–127.
 * @returns {Int16Array}
 */
export function buildPeriodTable() {
  const table = new Int16Array(128);
  for (let midi = 0; midi < 128; midi += 1) {
    table[midi] = midiToTimerPeriod(midi);
  }
  return table;
}

/**
 * True when a pulse period would be muted by the sweep unit (period < 8).
 * @param {number} period
 */
export function isPulsePeriodMuted(period) {
  return period < 8;
}

/**
 * Format a MIDI note as a tracker-style name (e.g. "C-4", "F#5").
 * @param {number|null|undefined} midi
 * @returns {string}
 */
export function formatNoteName(midi) {
  if (midi == null || !Number.isFinite(midi)) return "---";
  const names = [
    "C-",
    "C#",
    "D-",
    "D#",
    "E-",
    "F-",
    "F#",
    "G-",
    "G#",
    "A-",
    "A#",
    "B-",
  ];
  const m = clampInt(Math.round(midi), 0, 127);
  const name = names[m % 12];
  const octave = Math.floor(m / 12) - 1;
  return `${name}${octave}`;
}

function clamp(value, min, max) {
  return Math.min(max, Math.max(min, value));
}

function clampInt(value, min, max) {
  return Math.min(max, Math.max(min, value | 0));
}
