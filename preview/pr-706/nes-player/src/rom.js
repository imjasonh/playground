const MIRRORING = ["horizontal", "vertical"];

/**
 * Reads the iNES header so the page can reject a file that isn't a ROM
 * before handing it to the emulator.
 * @param {Uint8Array} bytes
 */
export function readHeader(bytes) {
  if (
    bytes.length < 16 ||
    bytes[0] !== 0x4e ||
    bytes[1] !== 0x45 ||
    bytes[2] !== 0x53 ||
    bytes[3] !== 0x1a
  ) {
    throw new Error("Not an iNES ROM: the file doesn't start with NES␚");
  }
  const flags6 = bytes[6];
  const flags7 = bytes[7];
  const nes2 = (flags7 & 0x0c) === 0x08;
  // Old dumpers wrote junk into bytes 7 to 15; DiskDude! is the usual case.
  const junk = !nes2 && bytes.slice(12, 16).some((b) => b !== 0);
  const mapper = (flags6 >> 4) | (junk ? 0 : flags7 & 0xf0);
  const prgBanks = bytes[4];
  const chrBanks = bytes[5];
  const trainer = (flags6 & 0x04) !== 0;
  const needed = 16 + (trainer ? 512 : 0) + prgBanks * 16384 + chrBanks * 8192;
  if (prgBanks === 0) {
    throw new Error("Not a playable ROM: the header lists no PRG banks");
  }
  if (bytes.length < needed) {
    throw new Error(
      `ROM is truncated: the header needs ${needed} bytes, the file has ${bytes.length}`,
    );
  }
  return {
    mapper,
    prgKiB: prgBanks * 16,
    chrKiB: chrBanks * 8,
    mirroring: flags6 & 0x08 ? "four-screen" : MIRRORING[flags6 & 1],
    battery: (flags6 & 0x02) !== 0,
  };
}

export function describeHeader(h) {
  const chr = h.chrKiB ? `${h.chrKiB} KiB CHR` : "CHR RAM";
  return `Mapper ${h.mapper}, ${h.prgKiB} KiB PRG, ${chr}`;
}
