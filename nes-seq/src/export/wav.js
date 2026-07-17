import { NesApu } from "../apu/nesApu.js";
import { NesPlayer } from "../sequencer/player.js";
import { createTransport, setPlaying } from "../sequencer/transport.js";
import { orderDurationSeconds } from "../song.js";

/**
 * @typedef {import("../song.js").Song} Song
 */

/**
 * Render a song (full order list) to a mono Float32Array.
 *
 * @param {Song} song
 * @param {{
 *   sampleRate?: number,
 *   loops?: number,
 *   tailSeconds?: number,
 * }} [opts]
 * @returns {Float32Array}
 */
export function renderSongToSamples(
  song,
  { sampleRate = 44100, loops = 1, tailSeconds = 0.05 } = {},
) {
  const apu = new NesApu();
  const first = song.patterns[song.order[0] ?? 0] ?? song.patterns[0];
  const transport = createTransport({
    bpm: song.bpm,
    patternLength: first.length,
  });
  const player = new NesPlayer(apu, {
    patterns: song.patterns,
    order: song.order,
    transport,
    instruments: song.instruments,
    sampleRate,
  });

  const loopSeconds = orderDurationSeconds(song) * Math.max(1, loops);
  const totalSeconds = loopSeconds + Math.max(0, tailSeconds);
  const totalSamples = Math.max(1, Math.ceil(totalSeconds * sampleRate));
  const out = new Float32Array(totalSamples);

  setPlaying(transport, true);
  player.onStart();
  player.render(out, totalSamples);
  return out;
}

/**
 * @param {Float32Array} samples
 * @param {number} [sampleRate=44100]
 * @returns {ArrayBuffer}
 */
export function encodeWav(samples, sampleRate = 44100) {
  const numSamples = samples.length;
  const bytesPerSample = 2;
  const blockAlign = bytesPerSample;
  const dataSize = numSamples * bytesPerSample;
  const buffer = new ArrayBuffer(44 + dataSize);
  const view = new DataView(buffer);

  writeString(view, 0, "RIFF");
  view.setUint32(4, 36 + dataSize, true);
  writeString(view, 8, "WAVE");
  writeString(view, 12, "fmt ");
  view.setUint32(16, 16, true);
  view.setUint16(20, 1, true);
  view.setUint16(22, 1, true);
  view.setUint32(24, sampleRate, true);
  view.setUint32(28, sampleRate * blockAlign, true);
  view.setUint16(32, blockAlign, true);
  view.setUint16(34, 16, true);
  writeString(view, 36, "data");
  view.setUint32(40, dataSize, true);

  let offset = 44;
  for (let i = 0; i < numSamples; i += 1) {
    const s = Math.max(-1, Math.min(1, samples[i]));
    view.setInt16(offset, (s * 0x7fff) | 0, true);
    offset += 2;
  }
  return buffer;
}

/**
 * @param {Song} song
 * @param {{ sampleRate?: number, loops?: number }} [opts]
 * @returns {Blob}
 */
export function songToWavBlob(song, opts = {}) {
  const rate = opts.sampleRate ?? 44100;
  const samples = renderSongToSamples(song, opts);
  const wav = encodeWav(samples, rate);
  return new Blob([wav], { type: "audio/wav" });
}

/**
 * @param {DataView} view
 * @param {number} offset
 * @param {string} string
 */
function writeString(view, offset, string) {
  for (let i = 0; i < string.length; i += 1) {
    view.setUint8(offset + i, string.charCodeAt(i));
  }
}
