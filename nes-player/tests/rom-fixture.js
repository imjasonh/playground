/**
 * Builds an iNES ROM whose code spins in place: every PRG byte is a NOP and
 * the reset vector points at $8000.
 */
export function makeRom({
  prgBanks = 1,
  chrBanks = 1,
  mapper = 0,
  vertical = false,
} = {}) {
  const prg = prgBanks * 16384;
  const rom = new Uint8Array(16 + prg + chrBanks * 8192);
  rom.set([0x4e, 0x45, 0x53, 0x1a, prgBanks, chrBanks]);
  rom[6] = ((mapper & 0x0f) << 4) | (vertical ? 1 : 0);
  rom[7] = mapper & 0xf0;
  rom.fill(0xea, 16, 16 + prg);
  for (const vector of [prg - 6, prg - 4, prg - 2]) {
    rom[16 + vector] = 0x00;
    rom[16 + vector + 1] = 0x80;
  }
  return rom;
}
