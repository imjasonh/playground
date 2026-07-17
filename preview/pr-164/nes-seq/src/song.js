import { CHANNELS } from "./apu/constants.js";
import {
  createDefaultInstruments,
  instrumentFromJSON,
  instrumentToJSON,
} from "./instruments/macros.js";
import {
  clonePattern,
  createEmptyPattern,
  patternFromJSON,
  patternToJSON,
} from "./sequencer/pattern.js";
import { DEFAULT_BPM, secondsPerStep } from "./sequencer/transport.js";

export const SONG_VERSION = 2;
export const MAX_PATTERNS = 16;
export const MAX_ORDER_LENGTH = 32;

/**
 * @typedef {import("./instruments/macros.js").ChannelId} ChannelId
 * @typedef {import("./instruments/macros.js").Instrument} Instrument
 * @typedef {import("./sequencer/pattern.js").Pattern} Pattern
 *
 * @typedef {object} Song
 * @property {number} version
 * @property {string} title
 * @property {number} bpm
 * @property {Pattern[]} patterns
 * @property {number[]} order          pattern indices to play
 * @property {number} editPattern      which pattern is being edited
 * @property {Record<ChannelId, Instrument>} instruments
 */

/**
 * @param {{ title?: string, bpm?: number, length?: number }} [opts]
 * @returns {Song}
 */
export function createSong({
  title = "Untitled",
  bpm = DEFAULT_BPM,
  length = 16,
} = {}) {
  const defaults = createDefaultInstruments();
  /** @type {Record<ChannelId, Instrument>} */
  const instruments = {
    pulse1: defaults.find((i) => i.id === "pulse-lead"),
    pulse2: defaults.find((i) => i.id === "pulse-square"),
    triangle: defaults.find((i) => i.id === "tri-bass"),
    noise: defaults.find((i) => i.id === "noise-hat"),
  };
  for (const ch of CHANNELS) {
    instruments[ch] = { ...instruments[ch], channel: ch };
  }
  const pattern = createEmptyPattern(length, "A");
  return {
    version: SONG_VERSION,
    title,
    bpm,
    patterns: [pattern],
    order: [0],
    editPattern: 0,
    instruments,
  };
}

/** @param {Song} song @returns {Pattern} */
export function getEditPattern(song) {
  const idx = clampPatternIndex(song.editPattern, song.patterns.length);
  return song.patterns[idx];
}

/**
 * Replace the currently edited pattern.
 * @param {Song} song
 * @param {Pattern} pattern
 * @returns {Song}
 */
export function setEditPatternData(song, pattern) {
  const next = cloneSong(song);
  const idx = clampPatternIndex(next.editPattern, next.patterns.length);
  next.patterns[idx] = pattern;
  return next;
}

/**
 * @param {Song} song
 * @param {number} index
 */
export function selectEditPattern(song, index) {
  const next = cloneSong(song);
  next.editPattern = clampPatternIndex(index, next.patterns.length);
  return next;
}

/**
 * @param {Song} song
 * @param {string} [name]
 */
export function addPattern(song, name) {
  if (song.patterns.length >= MAX_PATTERNS) return song;
  const next = cloneSong(song);
  const len = getEditPattern(song).length;
  const label =
    name || String.fromCharCode(65 + Math.min(25, next.patterns.length));
  next.patterns.push(createEmptyPattern(len, label));
  next.editPattern = next.patterns.length - 1;
  return next;
}

/**
 * @param {Song} song
 */
export function duplicateEditPattern(song) {
  if (song.patterns.length >= MAX_PATTERNS) return song;
  const next = cloneSong(song);
  const src = getEditPattern(song);
  const copy = clonePattern(src);
  copy.name = `${src.name || "Pattern"}*`;
  next.patterns.push(copy);
  next.editPattern = next.patterns.length - 1;
  return next;
}

/**
 * @param {Song} song
 * @param {number} index
 */
export function deletePattern(song, index) {
  if (song.patterns.length <= 1) return song;
  const next = cloneSong(song);
  const idx = clampPatternIndex(index, next.patterns.length);
  next.patterns.splice(idx, 1);
  next.order = next.order
    .map((p) => {
      if (p === idx) return -1;
      return p > idx ? p - 1 : p;
    })
    .filter((p) => p >= 0);
  if (next.order.length === 0) next.order = [0];
  next.editPattern = Math.min(next.editPattern, next.patterns.length - 1);
  return next;
}

/**
 * @param {Song} song
 * @param {number[]} order
 */
export function setOrder(song, order) {
  const next = cloneSong(song);
  next.order = normalizeOrder(order, next.patterns.length);
  return next;
}

/**
 * Append a pattern index to the order list.
 * @param {Song} song
 * @param {number} patternIndex
 */
export function appendOrder(song, patternIndex) {
  if (song.order.length >= MAX_ORDER_LENGTH) return song;
  const next = cloneSong(song);
  next.order.push(clampPatternIndex(patternIndex, next.patterns.length));
  return next;
}

/**
 * @param {Song} song
 * @param {number} orderIndex
 */
export function removeOrderEntry(song, orderIndex) {
  if (song.order.length <= 1) return song;
  const next = cloneSong(song);
  if (orderIndex < 0 || orderIndex >= next.order.length) return song;
  next.order.splice(orderIndex, 1);
  return next;
}

/**
 * Total steps across one full play of the order list.
 * @param {Song} song
 */
export function orderStepCount(song) {
  let n = 0;
  for (const idx of song.order) {
    const p = song.patterns[idx];
    if (p) n += p.length;
  }
  return Math.max(1, n);
}

/**
 * Duration in seconds of one full order loop.
 * @param {Song} song
 */
export function orderDurationSeconds(song) {
  return secondsPerStep(song.bpm) * orderStepCount(song);
}

/**
 * @returns {Song}
 */
export function createDemoSong() {
  const song = createSong({ title: "Boot Loop", bpm: 140, length: 16 });
  const a = song.patterns[0];
  a.name = "A";

  const bass = [36, null, 36, null, 43, null, 41, null, 36, null, 36, null, 34, null, 36, null];
  const lead = [60, null, 63, null, 67, 63, null, 60, 58, null, 60, null, 63, null, 67, null];
  const harm = [null, null, 55, null, null, 58, null, null, 55, null, null, 53, null, null, 55, null];
  const hats = [72, null, 72, null, 72, null, 72, 60, 72, null, 72, null, 72, null, 72, 60];

  for (let i = 0; i < 16; i += 1) {
    if (bass[i] != null) a.tracks.triangle[i] = { midi: bass[i], length: 2 };
    if (lead[i] != null) a.tracks.pulse1[i] = { midi: lead[i], length: 1 };
    if (harm[i] != null) a.tracks.pulse2[i] = { midi: harm[i], length: 2 };
    if (hats[i] != null) {
      a.tracks.noise[i] = {
        midi: hats[i],
        velocity: hats[i] < 70 ? 12 : 8,
        length: 1,
      };
    }
  }

  // Pattern B — fill / variation with a slide and cut
  const b = createEmptyPattern(16, "B");
  const leadB = [67, null, 70, null, 72, 70, null, 67, 65, null, 67, null, 70, null, 72, null];
  const bassB = [36, null, null, null, 41, null, null, null, 36, null, 34, null, 36, null, 31, null];
  for (let i = 0; i < 16; i += 1) {
    if (bassB[i] != null) b.tracks.triangle[i] = { midi: bassB[i], length: 3, gate: 4 };
    if (leadB[i] != null) {
      b.tracks.pulse1[i] =
        i === 0
          ? { midi: leadB[i], length: 2, gate: 6, slideTo: 72 }
          : { midi: leadB[i], length: 1 };
    }
    if (i % 2 === 0) {
      b.tracks.noise[i] = { midi: 80, velocity: 7, length: 1, gate: 2 };
    }
    if (i === 15) b.tracks.pulse1[i] = { cut: true };
  }
  song.patterns.push(b);
  song.order = [0, 0, 1, 0];

  const defaults = createDefaultInstruments();
  song.instruments.pulse1 = {
    ...defaults.find((i) => i.id === "pulse-arp"),
    channel: "pulse1",
  };
  song.instruments.pulse2 = {
    ...defaults.find((i) => i.id === "pulse-vib"),
    channel: "pulse2",
  };
  return song;
}

/**
 * @param {Song} song
 */
export function songToJSON(song) {
  /** @type {Record<string, unknown>} */
  const instruments = {};
  for (const ch of CHANNELS) {
    instruments[ch] = instrumentToJSON(song.instruments[ch]);
  }
  return {
    version: SONG_VERSION,
    title: song.title,
    bpm: song.bpm,
    patterns: song.patterns.map(patternToJSON),
    order: [...song.order],
    editPattern: song.editPattern,
    instruments,
    // Legacy single-pattern field for older readers.
    pattern: patternToJSON(getEditPattern(song)),
  };
}

/**
 * @param {unknown} raw
 * @returns {Song}
 */
export function songFromJSON(raw) {
  const o = raw && typeof raw === "object" ? /** @type {any} */ (raw) : {};
  const base = createSong({
    title: typeof o.title === "string" ? o.title : "Untitled",
    bpm: Number(o.bpm) || DEFAULT_BPM,
  });

  if (Array.isArray(o.patterns) && o.patterns.length > 0) {
    base.patterns = o.patterns
      .slice(0, MAX_PATTERNS)
      .map((p, i) => patternFromJSON({ name: String.fromCharCode(65 + i), ...p }));
  } else if (o.pattern) {
    // v1 migration
    base.patterns = [patternFromJSON(o.pattern)];
  }

  base.order = normalizeOrder(
    Array.isArray(o.order) ? o.order : [0],
    base.patterns.length,
  );
  base.editPattern = clampPatternIndex(
    o.editPattern ?? 0,
    base.patterns.length,
  );

  if (o.instruments && typeof o.instruments === "object") {
    for (const ch of CHANNELS) {
      if (o.instruments[ch]) {
        base.instruments[ch] = {
          ...instrumentFromJSON(o.instruments[ch]),
          channel: ch,
        };
      }
    }
  }
  base.version = SONG_VERSION;
  return base;
}

/** @param {Song} song */
export function serializeSong(song) {
  return JSON.stringify(songToJSON(song));
}

/** @param {string} text */
export function deserializeSong(text) {
  return songFromJSON(JSON.parse(text));
}

/** @param {Song} song */
export function cloneSong(song) {
  return songFromJSON(songToJSON(song));
}

function normalizeOrder(order, patternCount) {
  const cleaned = (Array.isArray(order) ? order : [0])
    .map((n) => clampPatternIndex(n, patternCount))
    .slice(0, MAX_ORDER_LENGTH);
  return cleaned.length ? cleaned : [0];
}

function clampPatternIndex(index, count) {
  const n = Number(index) | 0;
  if (count <= 0) return 0;
  return Math.min(count - 1, Math.max(0, n));
}
