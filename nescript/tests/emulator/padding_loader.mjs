// Models the iNES loader that rounds PRG and CHR up to a power of
// two, and rebuilds the ROM image such a loader hands to the mapper.
//
// jsnes, Mesen, and Nestopia trust the bank counts in the header, so
// they happily run an image whose PRG is, say, 5 x 16 KB. FCEUX does
// not. `src/ines.cpp` computes `uppow2(prg_banks << 14)`, allocates
// that many bytes, fills them with $FF, and *then* reads the file in:
//
//     rom_size_bytes = uppow2(not_round_size);
//     ROM = FCEU_malloc(rom_size_bytes);
//     memset(ROM, 0xFF, rom_size_bytes);
//     SetupCartPRGMapping(0, ROM, rom_size_bytes, 0);
//     FCEU_fread(ROM, 1, (round) ? rom_size_bytes : not_round_size, fp);
//     if (vrom_size_bytes) FCEU_fread(VROM, 1, vrom_size_bytes, fp);
//
// `round` is false only for the four mappers in `not_power2[]`
// (53, 198, 228, 547), so every mapper NEScript emits gets rounded.
// Two things go wrong for a ROM that is not already a power of two:
// MMC1, UxROM, and MMC3 wire the top of the address space to the
// *last* PRG bank, which is now $FF filler rather than the fixed
// bank, so $FFFA-$FFFF reads back as $FFFF; and the greedy PRG read
// swallows the CHR data, leaving CHR ROM blank.
//
// `paddingLoaderImage` returns the equivalent .nes file — padded
// data plus a header that declares the padded bank counts — so the
// harness can run a ROM through jsnes exactly the way FCEUX would
// see it. For a ROM that already declares power-of-two sizes the
// result is byte-identical to the input, which is the property the
// harness asserts.

const PRG_BANK_SIZE = 16384;
const CHR_BANK_SIZE = 8192;
const HEADER_SIZE = 16;

function uppow2(n) {
  let p = 1;
  while (p < n) p <<= 1;
  return p;
}

export function paddingLoaderImage(romBytes) {
  if (romBytes.length < HEADER_SIZE) {
    throw new Error(`ROM is ${romBytes.length} bytes, too small for an iNES header`);
  }
  const prgDeclared = romBytes[4] * PRG_BANK_SIZE;
  const chrDeclared = romBytes[5] * CHR_BANK_SIZE;
  const prgAlloc = uppow2(prgDeclared);
  const chrAlloc = chrDeclared === 0 ? 0 : uppow2(chrDeclared);

  const prg = Buffer.alloc(prgAlloc, 0xff);
  const chr = Buffer.alloc(chrAlloc, 0xff);

  let cursor = HEADER_SIZE;
  const prgRead = Math.max(0, Math.min(prgAlloc, romBytes.length - cursor));
  romBytes.copy(prg, 0, cursor, cursor + prgRead);
  cursor += prgRead;
  const chrRead = Math.max(0, Math.min(chrAlloc, romBytes.length - cursor));
  romBytes.copy(chr, 0, cursor, cursor + chrRead);

  const out = Buffer.alloc(HEADER_SIZE + prgAlloc + chrAlloc);
  romBytes.copy(out, 0, 0, HEADER_SIZE);
  out[4] = prgAlloc / PRG_BANK_SIZE;
  out[5] = chrAlloc / CHR_BANK_SIZE;
  prg.copy(out, HEADER_SIZE);
  chr.copy(out, HEADER_SIZE + prgAlloc);
  return out;
}

// Human-readable account of what the loader had to change, for the
// failure message. Returns null when the image was already safe.
export function paddingLoaderReport(romBytes) {
  const prgBanks = romBytes[4];
  const chrBanks = romBytes[5];
  const prgPadded = uppow2(prgBanks * PRG_BANK_SIZE) / PRG_BANK_SIZE;
  const chrPadded = chrBanks === 0 ? 0 : uppow2(chrBanks * CHR_BANK_SIZE) / CHR_BANK_SIZE;
  const notes = [];
  if (prgPadded !== prgBanks) {
    notes.push(
      `PRG ${prgBanks} x 16 KB is padded to ${prgPadded} banks, so the bank the ` +
        `mapper wires to $E000-$FFFF becomes $FF filler and the CHR data is read ` +
        `into PRG space`,
    );
  }
  if (chrPadded !== chrBanks) {
    notes.push(`CHR ${chrBanks} x 8 KB is padded to ${chrPadded} banks`);
  }
  return notes.length > 0 ? notes.join("; ") : null;
}
