import {
  assemblePlayerProgram,
  compileSongFrames,
  parseNsfHeader,
} from "./nsf.js";

/**
 * @typedef {import("../song.js").Song} Song
 */

/**
 * Wrap an NSF into a Mapper-0 iNES ROM that JSNES can run.
 * NMI calls the NSF PLAY routine each frame after RESET runs INIT.
 *
 * @param {Uint8Array} nsfBytes
 * @returns {Uint8Array}
 */
export function nsfToInesRom(nsfBytes) {
  const header = parseNsfHeader(nsfBytes);
  if (header.bankswitch.some((b) => b !== 0)) {
    throw new Error("Bankswitched NSF cannot be wrapped into a simple iNES ROM");
  }
  if (header.loadAddress !== 0x8000) {
    throw new Error(
      `Unsupported NSF load address $${header.loadAddress.toString(16)}`,
    );
  }
  return buildMusicRom({
    prgPayload: header.data,
    initAddress: header.initAddress,
    playAddress: header.playAddress,
  });
}

/**
 * Build a playable .nes ROM directly from a song (same program as NSF export).
 *
 * @param {Song} song
 * @param {{ loops?: number }} [opts]
 * @returns {Uint8Array}
 */
export function songToNesRom(song, { loops = 1 } = {}) {
  const { frames } = compileSongFrames(song, { loops });
  const program = assemblePlayerProgram(frames);
  return buildMusicRom({
    prgPayload: program.prg,
    initAddress: program.initAddress,
    playAddress: program.playAddress,
  });
}

/**
 * @param {{
 *   prgPayload: Uint8Array,
 *   initAddress: number,
 *   playAddress: number,
 * }} opts
 */
function buildMusicRom({ prgPayload, initAddress, playAddress }) {
  const prg = new Uint8Array(32 * 1024);
  if (prgPayload.length > prg.length - 256) {
    throw new Error("Music program too large for 32KB iNES PRG");
  }
  prg.set(prgPayload, 0); // CPU $8000

  const stubAddr = 0xff00;
  const { code, nmiAddress } = assembleRomStub({
    initAddress,
    playAddress,
    stubAddr,
  });
  prg.set(code, stubAddr - 0x8000);

  const view = new DataView(prg.buffer);
  view.setUint16(0xfffa - 0x8000, nmiAddress, true);
  view.setUint16(0xfffc - 0x8000, stubAddr, true);
  view.setUint16(0xfffe - 0x8000, nmiAddress, true);

  const chr = new Uint8Array(8 * 1024);
  const ines = new Uint8Array(16 + prg.length + chr.length);
  ines[0] = 0x4e;
  ines[1] = 0x45;
  ines[2] = 0x53;
  ines[3] = 0x1a;
  ines[4] = 2; // 32KB PRG
  ines[5] = 1; // 8KB CHR
  ines.set(prg, 16);
  ines.set(chr, 16 + prg.length);
  return ines;
}

/**
 * @param {{ initAddress: number, playAddress: number, stubAddr: number }} opts
 */
function assembleRomStub({ initAddress, playAddress, stubAddr }) {
  /** @type {number[]} */
  const b = [];
  const emit = (...xs) => b.push(...xs);

  // RESET
  emit(0x78, 0xd8); // SEI CLD
  emit(0xa2, 0xff, 0x9a); // LDX #$FF / TXS
  emit(0xa9, 0x00);
  emit(0x8d, 0x00, 0x20); // STA $2000
  emit(0x8d, 0x01, 0x20); // STA $2001
  // Wait for two VBlanks
  emit(0x2c, 0x02, 0x20, 0x10, 0xfb);
  emit(0x2c, 0x02, 0x20, 0x10, 0xfb);
  emit(0x20, initAddress & 0xff, (initAddress >> 8) & 0xff);
  emit(0xa9, 0x80, 0x8d, 0x00, 0x20); // enable NMI
  const forever = stubAddr + b.length;
  emit(0x4c, forever & 0xff, (forever >> 8) & 0xff);

  const nmiAddress = stubAddr + b.length;
  emit(0x48, 0x8a, 0x48, 0x98, 0x48);
  emit(0x20, playAddress & 0xff, (playAddress >> 8) & 0xff);
  emit(0x68, 0xa8, 0x68, 0xaa, 0x68, 0x40);

  return { code: Uint8Array.from(b), nmiAddress };
}
