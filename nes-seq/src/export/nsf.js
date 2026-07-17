import { NesApu } from "../apu/nesApu.js";
import { NesPlayer } from "../sequencer/player.js";
import {
  createTransport,
  secondsPerStep,
  setPlaying,
} from "../sequencer/transport.js";

/** NTSC NSF PLAY period in microseconds (~60.098 Hz using $411F). */
export const NSF_NTSC_PLAY_US = 16_639;
export const NSF_LOAD_ADDRESS = 0x8000;
export const NSF_PLAY_HZ = 1_000_000 / NSF_NTSC_PLAY_US;

const APU_ADDR_MIN = 0x4000;
const APU_ADDR_MAX = 0x4017;

/**
 * @typedef {import("../song.js").Song} Song
 * @typedef {{ addr: number, value: number }} RegWrite
 * @typedef {RegWrite[]} FrameWrites
 */

/**
 * Compile a song into per-PLAY-frame APU register write lists (delta-encoded).
 *
 * @param {Song} song
 * @param {{ loops?: number }} [opts]
 * @returns {{ frames: FrameWrites[], playHz: number, durationSec: number }}
 */
export function compileSongFrames(song, { loops = 1 } = {}) {
  const playHz = NSF_PLAY_HZ;
  const sampleRate = 48000;
  const totalSeconds =
    secondsPerStep(song.bpm) * song.pattern.length * Math.max(1, loops);
  const totalSamples = Math.max(1, Math.ceil(totalSeconds * sampleRate));

  /** @type {RegWrite[]} */
  let frameBucket = [];
  /** @type {FrameWrites[]} */
  const frames = [];
  const samplesPerFrame = sampleRate / playHz;
  let sampleCursor = 0;
  let nextFrameAt = samplesPerFrame;

  /** @type {Map<number, number>} */
  const emitted = new Map();

  const apu = new NesApu();
  const rawWrite = apu.writeRegister.bind(apu);
  apu.writeRegister = (address, value) => {
    const addr = address & 0xffff;
    const v = value & 0xff;
    rawWrite(addr, v);
    if (addr < APU_ADDR_MIN || addr > APU_ADDR_MAX) return;
    frameBucket.push({ addr, value: v });
  };

  const transport = createTransport({
    bpm: song.bpm,
    patternLength: song.pattern.length,
  });
  const player = new NesPlayer(apu, {
    pattern: song.pattern,
    transport,
    instruments: song.instruments,
    sampleRate,
  });

  setPlaying(transport, true);
  player.onStart();

  const scratch = new Float32Array(128);
  while (sampleCursor < totalSamples) {
    const n = Math.min(scratch.length, totalSamples - sampleCursor);
    player.render(scratch, n);
    sampleCursor += n;
    while (sampleCursor + 1e-9 >= nextFrameAt) {
      frames.push(deltaWrites(frameBucket, emitted));
      frameBucket = [];
      nextFrameAt += samplesPerFrame;
    }
  }
  if (frameBucket.length) {
    frames.push(deltaWrites(frameBucket, emitted));
  }
  if (frames.length === 0) frames.push([]);

  return { frames, playHz, durationSec: totalSeconds };
}

/**
 * @param {RegWrite[]} writes
 * @param {Map<number, number>} emitted
 * @returns {FrameWrites}
 */
function deltaWrites(writes, emitted) {
  /** @type {Map<number, number>} */
  const desired = new Map();
  for (const w of writes) desired.set(w.addr, w.value);
  /** @type {FrameWrites} */
  const out = [];
  for (const [addr, value] of desired) {
    if (emitted.get(addr) === value) continue;
    emitted.set(addr, value);
    out.push({ addr, value });
  }
  out.sort((a, b) => a.addr - b.addr);
  return out;
}

/**
 * @param {Song} song
 * @param {{ loops?: number, title?: string, artist?: string, copyright?: string }} [opts]
 * @returns {Uint8Array}
 */
export function songToNsf(song, opts = {}) {
  const { frames } = compileSongFrames(song, { loops: opts.loops ?? 1 });
  const program = assemblePlayerProgram(frames);
  return packNsf(program, {
    title: opts.title ?? song.title ?? "Untitled",
    artist: opts.artist ?? "2A03",
    copyright: opts.copyright ?? "nes-seq",
  });
}

/**
 * @param {Song} song
 * @param {object} [opts]
 * @returns {Blob}
 */
export function songToNsfBlob(song, opts = {}) {
  const bytes = songToNsf(song, opts);
  // Copy into a fresh ArrayBuffer-backed view for Blob typing.
  const copy = bytes.slice();
  return new Blob([copy], { type: "application/octet-stream" });
}

/**
 * @param {Uint8Array} bytes
 */
export function parseNsfHeader(bytes) {
  if (bytes.length < 128) throw new Error("NSF too short");
  if (
    bytes[0] !== 0x4e ||
    bytes[1] !== 0x45 ||
    bytes[2] !== 0x53 ||
    bytes[3] !== 0x4d ||
    bytes[4] !== 0x1a
  ) {
    throw new Error("Not an NSF file");
  }
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  return {
    version: bytes[5],
    songs: bytes[6],
    startingSong: bytes[7],
    loadAddress: view.getUint16(0x08, true),
    initAddress: view.getUint16(0x0a, true),
    playAddress: view.getUint16(0x0c, true),
    title: readNsfString(bytes, 0x0e, 32),
    artist: readNsfString(bytes, 0x2e, 32),
    copyright: readNsfString(bytes, 0x4e, 32),
    ntscPlayUs: view.getUint16(0x6e, true),
    bankswitch: [...bytes.subarray(0x70, 0x78)],
    palPlayUs: view.getUint16(0x78, true),
    tvSystem: bytes[0x7a],
    expansion: bytes[0x7b],
    data: bytes.subarray(128),
  };
}

/**
 * Assemble 6502 player + frame data at NSF_LOAD_ADDRESS.
 * @param {FrameWrites[]} frames
 */
export function assemblePlayerProgram(frames) {
  const load = NSF_LOAD_ADDRESS;
  const frameCount = frames.length;
  if (frameCount > 0xffff) {
    throw new Error(`Song too long for NSF player (${frameCount} frames)`);
  }
  for (const frame of frames) {
    if (frame.length > 255) {
      throw new Error("Too many APU writes in one NSF frame");
    }
  }

  const initCode = Uint8Array.from([
    0xa9, 0x0f, // LDA #$0F
    0x8d, 0x15, 0x40, // STA $4015
    0xa9, 0x40, // LDA #$40
    0x8d, 0x17, 0x40, // STA $4017
    0xa9, 0x00, // LDA #0
    0x85, 0x10, // STA $10
    0x85, 0x11, // STA $11
    0x60, // RTS
  ]);

  const initLen = initCode.length;
  const playAddress = load + initLen;
  // PLAY length is independent of the absolute frame_ptrs address.
  const playLen = assemblePlayRoutine({
    framePtrsAddr: 0,
    frameCount,
    playAddress,
  }).length;
  const framePtrsAddr = load + initLen + playLen + 2;
  const playCode = assemblePlayRoutine({
    framePtrsAddr,
    frameCount,
    playAddress,
  });
  if (playCode.length !== playLen) {
    throw new Error("PLAY routine length mismatch");
  }

  const listsOff = initLen + playLen + 2 + frameCount * 2;
  /** @type {number[]} */
  const lists = [];
  const ptrs = new Uint8Array(frameCount * 2);
  for (let i = 0; i < frames.length; i += 1) {
    const listCpu = load + listsOff + lists.length;
    ptrs[i * 2] = listCpu & 0xff;
    ptrs[i * 2 + 1] = (listCpu >> 8) & 0xff;
    const frame = frames[i];
    lists.push(frame.length);
    for (const w of frame) {
      lists.push((w.addr - 0x4000) & 0xff, w.value & 0xff);
    }
  }

  const prg = concatBytes([
    initCode,
    playCode,
    Uint8Array.from([frameCount & 0xff, (frameCount >> 8) & 0xff]),
    ptrs,
    Uint8Array.from(lists),
  ]);

  if (load + prg.length > 0x10000) {
    throw new Error("NSF program exceeds 6502 address space");
  }

  return {
    prg,
    loadAddress: load,
    initAddress: load,
    playAddress,
  };
}

/**
 * @param {{ framePtrsAddr: number, frameCount: number, playAddress: number }} opts
 */
function assemblePlayRoutine({ framePtrsAddr, frameCount, playAddress }) {
  /** @type {number[]} */
  const b = [];
  const here = () => playAddress + b.length;
  const emit = (...bytes) => {
    b.push(...bytes);
  };

  emit(0xa5, 0x10, 0x85, 0x00, 0xa5, 0x11, 0x85, 0x01);
  emit(0x06, 0x00, 0x26, 0x01, 0x18);
  emit(0xa5, 0x00, 0x69, framePtrsAddr & 0xff, 0x85, 0x00);
  emit(0xa5, 0x01, 0x69, (framePtrsAddr >> 8) & 0xff, 0x85, 0x01);
  emit(0xa0, 0x00, 0xb1, 0x00, 0x85, 0x02, 0xc8, 0xb1, 0x00, 0x85, 0x03);
  emit(0xa0, 0x00, 0xb1, 0x02);
  const beqAt = b.length;
  emit(0xf0, 0x00);
  emit(0xaa, 0xc8);
  const loopAddr = here();
  emit(0xb1, 0x02, 0xc8);
  const staSmc = b.length;
  emit(0x8d, 0x00, 0x00);
  emit(0xb1, 0x02, 0xc8);
  const sta4000 = b.length;
  emit(0x8d, 0x00, 0x40);
  emit(0xca);
  const bneLoopAt = b.length;
  emit(0xd0, 0x00);
  const advanceAddr = here();
  emit(0xe6, 0x10, 0xd0, 0x02, 0xe6, 0x11);
  emit(0xa5, 0x10, 0xc9, frameCount & 0xff);
  const bneDone1 = b.length;
  emit(0xd0, 0x00);
  emit(0xa5, 0x11, 0xc9, (frameCount >> 8) & 0xff);
  const bneDone2 = b.length;
  emit(0xd0, 0x00);
  emit(0xa9, 0x00, 0x85, 0x10, 0x85, 0x11);
  const doneAddr = here();
  emit(0x60);

  const smcLowCpu = playAddress + sta4000 + 1;
  b[staSmc + 1] = smcLowCpu & 0xff;
  b[staSmc + 2] = (smcLowCpu >> 8) & 0xff;
  b[beqAt + 1] = rel8(advanceAddr, playAddress + beqAt);
  b[bneLoopAt + 1] = rel8(loopAddr, playAddress + bneLoopAt);
  b[bneDone1 + 1] = rel8(doneAddr, playAddress + bneDone1);
  b[bneDone2 + 1] = rel8(doneAddr, playAddress + bneDone2);

  return Uint8Array.from(b);
}

/** @param {number} target @param {number} branchInstrAddr */
function rel8(target, branchInstrAddr) {
  const offset = target - (branchInstrAddr + 2);
  if (offset < -128 || offset > 127) {
    throw new Error(`Branch out of range: ${offset}`);
  }
  return offset & 0xff;
}

/**
 * @param {{ prg: Uint8Array, loadAddress: number, initAddress: number, playAddress: number }} program
 * @param {{ title: string, artist: string, copyright: string }} meta
 */
function packNsf(program, meta) {
  const header = new Uint8Array(128);
  header[0] = 0x4e;
  header[1] = 0x45;
  header[2] = 0x53;
  header[3] = 0x4d;
  header[4] = 0x1a;
  header[5] = 0x01;
  header[6] = 0x01;
  header[7] = 0x01;
  const view = new DataView(header.buffer);
  view.setUint16(0x08, program.loadAddress, true);
  view.setUint16(0x0a, program.initAddress, true);
  view.setUint16(0x0c, program.playAddress, true);
  writeNsfString(header, 0x0e, meta.title, 32);
  writeNsfString(header, 0x2e, meta.artist, 32);
  writeNsfString(header, 0x4e, meta.copyright, 32);
  view.setUint16(0x6e, NSF_NTSC_PLAY_US, true);
  view.setUint16(0x78, 19_997, true);
  header[0x7a] = 0;
  header[0x7b] = 0;
  return concatBytes([header, program.prg]);
}

/** @param {Uint8Array[]} parts */
function concatBytes(parts) {
  let n = 0;
  for (const p of parts) n += p.length;
  const out = new Uint8Array(n);
  let o = 0;
  for (const p of parts) {
    out.set(p, o);
    o += p.length;
  }
  return out;
}

/**
 * @param {Uint8Array} bytes
 * @param {number} offset
 * @param {string} text
 * @param {number} length
 */
function writeNsfString(bytes, offset, text, length) {
  const ascii = String(text || "")
    .replace(/[^\x20-\x7e]/g, "?")
    .slice(0, length - 1);
  for (let i = 0; i < length; i += 1) {
    bytes[offset + i] = i < ascii.length ? ascii.charCodeAt(i) : 0;
  }
}

/**
 * @param {Uint8Array} bytes
 * @param {number} offset
 * @param {number} length
 */
function readNsfString(bytes, offset, length) {
  let end = offset;
  const limit = offset + length;
  while (end < limit && bytes[end] !== 0) end += 1;
  return String.fromCharCode(...bytes.subarray(offset, end));
}
