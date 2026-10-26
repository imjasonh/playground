#[cfg(test)]
mod tests;

use crate::parser::ast::{HeaderFormat, Mapper, Mirroring};

/// iNES header magic bytes
const INES_MAGIC: [u8; 4] = [0x4E, 0x45, 0x53, 0x1A]; // "NES\x1A"

/// PRG ROM bank size (16 KB)
const PRG_BANK_SIZE: usize = 16384;

/// CHR ROM bank size (8 KB)
const CHR_BANK_SIZE: usize = 8192;

/// Build a complete iNES ROM file.
///
/// Supports both single-bank (NROM) and multi-bank (MMC1, `UxROM`,
/// MMC3) layouts. When you call [`RomBuilder::set_prg`] the builder
/// treats the bytes as a single 16 KB bank and pads out. When you
/// call [`RomBuilder::set_prg_banks`] the builder writes each bank
/// back-to-back in the order you provided. The iNES header's PRG
/// bank count always reflects the actual number of 16 KB slots.
///
/// By default the builder emits an iNES 1.0 header. Call
/// [`RomBuilder::enable_nes2`] to opt into the NES 2.0 header format,
/// which is backwards-compatible (byte 7 bits 2-3 are set to `10`)
/// and populates bytes 8-15 per the NES 2.0 spec. The header remains
/// 16 bytes either way.
pub struct RomBuilder {
    /// One Vec per 16 KB PRG bank, in physical order. An empty
    /// outer Vec means no PRG has been set yet; a single inner Vec
    /// means a classic NROM layout.
    prg_banks: Vec<Vec<u8>>,
    chr_data: Vec<u8>,
    mapper: u8,
    mirroring: Mirroring,
    header_format: HeaderFormat,
    /// True when the program declared a `save { var ... }` block.
    /// Sets byte 6 bit 1 of the iNES header so emulators and
    /// cartridge boards persist `$6000-$7FFF` SRAM across power
    /// cycles. Default false; the linker calls `set_battery(true)`
    /// from `analysis.has_battery_saves`.
    has_battery: bool,
}

impl RomBuilder {
    pub fn new(mirroring: Mirroring) -> Self {
        Self {
            prg_banks: Vec::new(),
            chr_data: Vec::new(),
            mapper: 0, // NROM
            mirroring,
            header_format: HeaderFormat::Ines1,
            has_battery: false,
        }
    }

    /// Mark the ROM as carrying battery-backed SRAM. Flips iNES
    /// header byte 6 bit 1; emulators that respect the flag (FCEUX,
    /// Mesen, Nestopia, real flash carts) will load/save the
    /// `$6000-$7FFF` window from/to a `.sav` file alongside the ROM.
    pub fn set_battery(&mut self, has_battery: bool) {
        self.has_battery = has_battery;
    }

    #[allow(dead_code)]
    pub fn set_mapper(&mut self, mapper: u8) {
        self.mapper = mapper;
    }

    /// Opt into the NES 2.0 header format. Bytes 7 bits 2-3 are
    /// set to `10` to mark the header as NES 2.0, and bytes 8-15
    /// are populated with the extended metadata. The header is
    /// still exactly 16 bytes.
    pub fn enable_nes2(&mut self) {
        self.header_format = HeaderFormat::Nes2;
    }

    /// Set the PRG ROM data as a single bank. Will be padded to fill
    /// 16 KB or 32 KB. Equivalent to calling `set_prg_banks` with a
    /// one- or two-element Vec depending on whether the data crosses
    /// the 16 KB boundary.
    pub fn set_prg(&mut self, data: Vec<u8>) {
        // Preserve the legacy single-bank behaviour: if the data is
        // <= 16 KB we emit exactly one 16 KB bank; if it's larger
        // (but still <= 32 KB) we split into two consecutive banks
        // so the iNES header byte 4 reflects 2, matching the old
        // `set_prg` contract used by all current NROM tests.
        if data.len() <= PRG_BANK_SIZE {
            self.prg_banks = vec![data];
        } else {
            let mut first = data;
            let second = first.split_off(PRG_BANK_SIZE);
            self.prg_banks = vec![first, second];
        }
    }

    /// Set the PRG ROM data as a list of 16 KB banks. Each bank will
    /// be padded with $FF to fill its 16 KB slot. The banks are
    /// written in the order provided — for mapper-specific layouts
    /// the caller (usually the Linker) is responsible for placing
    /// the fixed bank last.
    ///
    /// # Panics
    /// Panics if any single bank exceeds 16 KB, which would indicate
    /// a compiler bug (the allocator is expected to overflow-check
    /// before calling the rom builder).
    pub fn set_prg_banks(&mut self, banks: Vec<Vec<u8>>) {
        for (i, bank) in banks.iter().enumerate() {
            assert!(
                bank.len() <= PRG_BANK_SIZE,
                "PRG bank {i} exceeds 16 KB ({} bytes)",
                bank.len()
            );
        }
        self.prg_banks = banks;
    }

    /// Set the CHR ROM data. Will be padded to fill 8 KB.
    pub fn set_chr(&mut self, data: Vec<u8>) {
        self.chr_data = data;
    }

    /// Build the complete .nes file.
    pub fn build(self) -> Vec<u8> {
        // Determine PRG size. If no banks were set, fall back to a
        // single empty bank so the ROM has a valid 16 KB PRG slot.
        let prg_banks_vec: Vec<Vec<u8>> = if self.prg_banks.is_empty() {
            vec![Vec::new()]
        } else {
            self.prg_banks
        };
        let prg_banks = prg_banks_vec.len();
        let prg_size = prg_banks * PRG_BANK_SIZE;

        // CHR: 1 bank (8 KB), or 0 if using CHR RAM
        let chr_banks = usize::from(!self.chr_data.is_empty());
        let chr_size = chr_banks * CHR_BANK_SIZE;

        let mut rom = Vec::with_capacity(16 + prg_size + chr_size);

        // iNES header (16 bytes — NES 2.0 is the same size, it just
        // reinterprets bytes 7-15).
        rom.extend_from_slice(&INES_MAGIC);
        rom.push(prg_banks as u8); // PRG ROM banks (16 KB units) — low 8 bits
        rom.push(chr_banks as u8); // CHR ROM banks (8 KB units) — low 8 bits

        // Flags 6: mirroring (bit 0), battery-backed SRAM (bit 1),
        // mapper low nibble (bits 4-7). Bits 2-3 (trainer, four-screen
        // mirroring) stay zero — neither is a NEScript feature today.
        let mut flags6 = match self.mirroring {
            Mirroring::Horizontal => 0,
            Mirroring::Vertical => 1,
        };
        if self.has_battery {
            flags6 |= 0x02;
        }
        flags6 |= (self.mapper & 0x0F) << 4;
        rom.push(flags6);

        // Flags 7: mapper high nibble plus header-format marker.
        // NES 2.0 sets bits 2-3 to `10`; iNES 1.0 leaves them at `00`.
        let mut flags7 = self.mapper & 0xF0;
        if self.header_format == HeaderFormat::Nes2 {
            flags7 |= 0b0000_1000;
        }
        rom.push(flags7);

        // Bytes 8-15. For iNES 1.0 these are zero-padded. For NES 2.0
        // they carry the extended metadata described in the spec:
        //
        //   byte 8  — mapper high nibble (bits 8-11) + submapper (0)
        //   byte 9  — PRG ROM size MSB (0) | CHR ROM size MSB (0)
        //   byte 10 — PRG RAM / EEPROM size (0)
        //   byte 11 — CHR RAM size (0 — we use CHR ROM)
        //   byte 12 — CPU/PPU timing (0 = NTSC)
        //   byte 13 — mapper-specific (0)
        //   byte 14 — miscellaneous ROMs (0)
        //   byte 15 — default expansion device (0)
        //
        // Since we never exceed 4 MB of PRG or 2 MB of CHR, don't use
        // submappers, and don't have CHR RAM or miscellaneous ROMs,
        // most of these stay zero. Only the mapper high nibble in
        // byte 8 can be non-zero for mappers numbered >= 256.
        match self.header_format {
            HeaderFormat::Ines1 => rom.extend_from_slice(&[0u8; 8]),
            HeaderFormat::Nes2 => {
                // byte 8 low nibble would hold mapper bits 8-11;
                // since `self.mapper` is a u8 it's always zero here.
                // High nibble would hold the submapper, which we
                // never use.
                rom.push(0); // byte 8
                rom.push(0); // byte 9: PRG/CHR size MSBs
                rom.push(0); // byte 10: PRG RAM / EEPROM
                rom.push(0); // byte 11: CHR RAM
                rom.push(0); // byte 12: NTSC timing
                rom.push(0); // byte 13: mapper-specific
                rom.push(0); // byte 14: miscellaneous ROMs
                rom.push(0); // byte 15: default expansion device
            }
        }

        // PRG ROM data: each bank padded to 16 KB, concatenated.
        for mut bank in prg_banks_vec {
            bank.resize(PRG_BANK_SIZE, 0xFF);
            rom.extend_from_slice(&bank);
        }

        // CHR ROM data (padded to fill)
        if chr_banks > 0 {
            let mut chr = self.chr_data;
            chr.resize(chr_size, 0x00);
            rom.extend_from_slice(&chr);
        }

        rom
    }
}

/// Validate that a byte slice looks like a valid iNES ROM. Accepts
/// both iNES 1.0 and NES 2.0 headers — the former treats bytes 8-15
/// as zero-padded, the latter as extended metadata. The returned
/// [`RomInfo`] reports which format was detected in `header_format`
/// so callers can distinguish the two.
pub fn validate_ines(data: &[u8]) -> Result<RomInfo, &'static str> {
    if data.len() < 16 {
        return Err("file too small for iNES header");
    }
    if data[0..4] != INES_MAGIC {
        return Err("invalid iNES magic bytes");
    }

    let prg_banks = data[4] as usize;
    let chr_banks = data[5] as usize;
    let expected_size = 16 + prg_banks * PRG_BANK_SIZE + chr_banks * CHR_BANK_SIZE;

    if data.len() < expected_size {
        return Err("file too small for declared ROM banks");
    }

    let mirroring = if data[6] & 1 == 0 {
        Mirroring::Horizontal
    } else {
        Mirroring::Vertical
    };

    // Header format is encoded in byte 7 bits 2-3. `10` (binary)
    // means NES 2.0; anything else is iNES 1.0.
    let header_format = if data[7] & 0x0C == 0x08 {
        HeaderFormat::Nes2
    } else {
        HeaderFormat::Ines1
    };

    // iNES 1.0: mapper number is the low nibble of byte 6 plus the
    // high nibble of byte 7. NES 2.0 extends this with bits 8-11 in
    // byte 8's low nibble — we decode that too, even though we
    // never emit mappers >= 256 ourselves.
    let mut mapper = (data[6] >> 4) | (data[7] & 0xF0);
    if header_format == HeaderFormat::Nes2 {
        // Mapper field is 12 bits in NES 2.0; the high nibble in
        // byte 8 would push the mapper number past a u8. We still
        // only return the low 8 bits here since NEScript never
        // emits mappers beyond NROM/MMC1/UxROM/MMC3.
        let mapper_high = data[8] & 0x0F;
        if mapper_high != 0 {
            // Can't fit in a u8 — callers that care about high
            // mapper bits should read the header directly.
            mapper = mapper.wrapping_add(mapper_high << 4);
        }
    }

    Ok(RomInfo {
        prg_banks,
        chr_banks,
        mapper,
        mirroring,
        header_format,
    })
}

#[derive(Debug)]
pub struct RomInfo {
    pub prg_banks: usize,
    pub chr_banks: usize,
    pub mapper: u8,
    pub mirroring: Mirroring,
    pub header_format: HeaderFormat,
}

/// Map a `Mapper` enum variant to its iNES mapper number.
pub fn mapper_number(mapper: Mapper) -> u8 {
    match mapper {
        Mapper::NROM => 0,
        Mapper::MMC1 => 1,
        Mapper::UxROM => 2,
        Mapper::CNROM => 3,
        Mapper::MMC3 => 4,
        Mapper::AxROM => 7,
        Mapper::GNROM => 66,
    }
}
