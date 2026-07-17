import { CHANNELS } from "./apu/constants.js";
import {
  createDefaultInstruments,
  instrumentFromJSON,
  instrumentToJSON,
} from "./instruments/macros.js";
import {
  createEmptyPattern,
  patternFromJSON,
  patternToJSON,
} from "./sequencer/pattern.js";
import { DEFAULT_BPM } from "./sequencer/transport.js";

export const SONG_VERSION = 1;

/**
 * @typedef {import("./instruments/macros.js").ChannelId} ChannelId
 * @typedef {import("./instruments/macros.js").Instrument} Instrument
 * @typedef {import("./sequencer/pattern.js").Pattern} Pattern
 *
 * @typedef {object} Song
 * @property {number} version
 * @property {string} title
 * @property {number} bpm
 * @property {Pattern} pattern
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
  // Ensure channel field matches assignment.
  for (const ch of CHANNELS) {
    instruments[ch] = { ...instruments[ch], channel: ch };
  }
  return {
    version: SONG_VERSION,
    title,
    bpm,
    pattern: createEmptyPattern(length),
    instruments,
  };
}

/**
 * Seed a demo groove so first-open isn't silent.
 * @returns {Song}
 */
export function createDemoSong() {
  const song = createSong({ title: "Boot Loop", bpm: 140, length: 16 });
  const { pattern } = song;
  // Bass line on triangle
  const bass = [36, null, 36, null, 43, null, 41, null, 36, null, 36, null, 34, null, 36, null];
  // Pulse lead
  const lead = [60, null, 63, null, 67, 63, null, 60, 58, null, 60, null, 63, null, 67, null];
  // Pulse 2 harmony
  const harm = [null, null, 55, null, null, 58, null, null, 55, null, null, 53, null, null, 55, null];
  // Noise hats
  const hats = [72, null, 72, null, 72, null, 72, 60, 72, null, 72, null, 72, null, 72, 60];

  for (let i = 0; i < 16; i += 1) {
    if (bass[i] != null) pattern.tracks.triangle[i] = { midi: bass[i], length: 2 };
    if (lead[i] != null) pattern.tracks.pulse1[i] = { midi: lead[i], length: 1 };
    if (harm[i] != null) pattern.tracks.pulse2[i] = { midi: harm[i], length: 2 };
    if (hats[i] != null) {
      pattern.tracks.noise[i] = {
        midi: hats[i],
        velocity: hats[i] < 70 ? 12 : 8,
        length: 1,
      };
    }
  }
  song.instruments.pulse1 = {
    ...song.instruments.pulse1,
    ...createDefaultInstruments().find((i) => i.id === "pulse-arp"),
    channel: "pulse1",
  };
  return song;
}

/**
 * @param {Song} song
 * @returns {object}
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
    pattern: patternToJSON(song.pattern),
    instruments,
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
  if (o.pattern) base.pattern = patternFromJSON(o.pattern);
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
  return base;
}

/**
 * @param {Song} song
 * @returns {string}
 */
export function serializeSong(song) {
  return JSON.stringify(songToJSON(song));
}

/**
 * @param {string} text
 * @returns {Song}
 */
export function deserializeSong(text) {
  return songFromJSON(JSON.parse(text));
}
