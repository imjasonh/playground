use super::*;
use crate::parser::ast::{HeaderFormat, Mirroring};

#[test]
fn build_minimal_rom() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_prg(vec![0xEA; 100]); // 100 bytes of NOP
    let rom = builder.build();

    // Should have 16-byte header + 16 KB PRG
    assert_eq!(rom.len(), 16 + 16384);

    // Magic bytes
    assert_eq!(&rom[0..4], b"NES\x1a");

    // 1 PRG bank
    assert_eq!(rom[4], 1);

    // 0 CHR banks (CHR RAM)
    assert_eq!(rom[5], 0);
}

#[test]
fn build_rom_with_chr() {
    let mut builder = RomBuilder::new(Mirroring::Vertical);
    builder.set_prg(vec![0xEA; 100]);
    builder.set_chr(vec![0x00; 16]); // 1 tile
    let rom = builder.build();

    // 16-byte header + 16 KB PRG + 8 KB CHR
    assert_eq!(rom.len(), 16 + 16384 + 8192);
    assert_eq!(rom[5], 1); // 1 CHR bank
}

#[test]
fn horizontal_mirroring() {
    let builder = RomBuilder::new(Mirroring::Horizontal);
    let rom = builder.build();
    assert_eq!(rom[6] & 1, 0);
}

#[test]
fn vertical_mirroring() {
    let builder = RomBuilder::new(Mirroring::Vertical);
    let rom = builder.build();
    assert_eq!(rom[6] & 1, 1);
}

#[test]
fn prg_data_is_padded() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_prg(vec![0xAA; 10]);
    let rom = builder.build();

    // First 10 bytes of PRG should be $AA
    assert_eq!(&rom[16..26], &[0xAA; 10]);
    // Rest should be $FF (fill byte)
    assert_eq!(rom[26], 0xFF);
}

#[test]
fn validate_valid_rom() {
    let builder = RomBuilder::new(Mirroring::Horizontal);
    let rom = builder.build();
    let info = validate_ines(&rom).unwrap();
    assert_eq!(info.prg_banks, 1);
    assert_eq!(info.chr_banks, 0);
    assert_eq!(info.mapper, 0);
    assert_eq!(info.mirroring, Mirroring::Horizontal);
}

#[test]
fn validate_bad_magic() {
    let rom = vec![0x00; 100];
    assert!(validate_ines(&rom).is_err());
}

#[test]
fn validate_too_small() {
    let rom = vec![0x4E, 0x45, 0x53];
    assert!(validate_ines(&rom).is_err());
}

#[test]
fn large_prg_uses_two_banks() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_prg(vec![0xEA; 20000]); // > 16 KB
    let rom = builder.build();
    assert_eq!(rom[4], 2); // 2 PRG banks
    assert_eq!(rom.len(), 16 + 32768);
}

#[test]
fn mapper_number_encoded() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_mapper(1); // MMC1
    let rom = builder.build();
    let info = validate_ines(&rom).unwrap();
    assert_eq!(info.mapper, 1);
}

#[test]
fn chr_data_is_padded() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_chr(vec![0xBB; 16]); // 1 tile = 16 bytes
    let rom = builder.build();

    let chr_start = 16 + 16384; // after header + PRG
    assert_eq!(&rom[chr_start..chr_start + 16], &[0xBB; 16]);
    assert_eq!(rom[chr_start + 16], 0x00); // padded with zeros
}

#[test]
fn mapper_mmc1_encoded() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_mapper(crate::rom::mapper_number(crate::parser::ast::Mapper::MMC1));
    let rom = builder.build();
    let info = validate_ines(&rom).unwrap();
    assert_eq!(info.mapper, 1);
}

#[test]
fn mapper_uxrom_encoded() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_mapper(crate::rom::mapper_number(crate::parser::ast::Mapper::UxROM));
    let rom = builder.build();
    let info = validate_ines(&rom).unwrap();
    assert_eq!(info.mapper, 2);
}

#[test]
fn mapper_mmc3_encoded() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_mapper(crate::rom::mapper_number(crate::parser::ast::Mapper::MMC3));
    let rom = builder.build();
    let info = validate_ines(&rom).unwrap();
    assert_eq!(info.mapper, 4);
}

// ─── Multi-bank PRG layout ─────────────────────────────────────────

#[test]
fn set_prg_banks_with_two_banks_pads_and_concatenates() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_prg_banks(vec![vec![0xAA, 0xAA, 0xAA], vec![0xBB, 0xBB]]);
    let rom = builder.build();
    // Header reports 2 banks.
    assert_eq!(rom[4], 2);
    // Total file size: 16 header + 2 * 16 KB
    assert_eq!(rom.len(), 16 + 2 * 16384);
    // First bank: 0xAA at the start, $FF padding, then second bank.
    assert_eq!(&rom[16..19], &[0xAA, 0xAA, 0xAA]);
    assert_eq!(rom[19], 0xFF); // padding continues in bank 0
                               // Second bank starts at 16 + 16384.
    let bank1 = 16 + 16384;
    assert_eq!(&rom[bank1..bank1 + 2], &[0xBB, 0xBB]);
    assert_eq!(rom[bank1 + 2], 0xFF); // padding in bank 1
}

#[test]
fn set_prg_banks_with_four_banks_produces_64kb_prg() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_prg_banks(vec![vec![0x00], vec![0x01], vec![0x02], vec![0x03]]);
    let rom = builder.build();
    assert_eq!(rom[4], 4, "header should report 4 PRG banks");
    assert_eq!(rom.len(), 16 + 4 * 16384);
    // Each bank's first byte should be the bank index.
    for i in 0..4 {
        let offset = 16 + i * 16384;
        assert_eq!(rom[offset], i as u8, "bank {i} should start with byte {i}");
    }
}

#[test]
#[should_panic(expected = "exceeds 16 KB")]
fn set_prg_banks_panics_when_bank_too_large() {
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    // 16 KB + 1 byte overflows a single 16 KB bank slot.
    builder.set_prg_banks(vec![vec![0x00; 16385]]);
}

#[test]
fn set_prg_banks_preserves_content_exactly() {
    // Verify byte-for-byte fidelity: if the caller provides bytes
    // A, B, C in a bank, they must land at bank_start, bank_start+1,
    // bank_start+2 with no rearrangement.
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.set_prg_banks(vec![(0u8..=9).collect(), (100u8..=109).collect()]);
    let rom = builder.build();
    assert_eq!(&rom[16..26], &(0u8..=9).collect::<Vec<_>>()[..]);
    let bank1 = 16 + 16384;
    assert_eq!(
        &rom[bank1..bank1 + 10],
        &(100u8..=109).collect::<Vec<_>>()[..]
    );
}

#[test]
fn validate_detects_multi_bank_prg() {
    // A ROM built with 3 banks should validate with prg_banks=3.
    let mut builder = RomBuilder::new(Mirroring::Vertical);
    builder.set_mapper(1); // MMC1
    builder.set_prg_banks(vec![vec![0x11; 10], vec![0x22; 10], vec![0x33; 10]]);
    let rom = builder.build();
    let info = validate_ines(&rom).unwrap();
    assert_eq!(info.prg_banks, 3);
    assert_eq!(info.mapper, 1);
    assert_eq!(info.mirroring, Mirroring::Vertical);
}

#[test]
fn empty_prg_banks_fallback_to_single_bank() {
    // If a caller doesn't call set_prg or set_prg_banks, the builder
    // still produces a valid single-bank ROM so tests that only
    // exercise the CHR path keep working.
    let builder = RomBuilder::new(Mirroring::Horizontal);
    let rom = builder.build();
    assert_eq!(rom[4], 1, "default should be 1 PRG bank");
    assert_eq!(rom.len(), 16 + 16384);
}

// ─── NES 2.0 header support ────────────────────────────────────────

#[test]
fn ines1_default_has_clear_nes2_marker() {
    // Default header format is iNES 1.0 — byte 7 bits 2-3 must be 00.
    let builder = RomBuilder::new(Mirroring::Horizontal);
    let rom = builder.build();
    assert_eq!(
        rom[7] & 0x0C,
        0x00,
        "iNES 1.0 default must not set byte 7 bits 2-3"
    );
    // Bytes 8-15 must all be zero padding in iNES 1.0.
    assert_eq!(&rom[8..16], &[0u8; 8]);
    assert_eq!(rom.len(), 16 + 16384);
}

#[test]
fn nes2_header_sets_byte7_bits_2_3() {
    // Opting into NES 2.0 must set byte 7 bits 2-3 to `10` (binary).
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.enable_nes2();
    let rom = builder.build();
    assert_eq!(
        rom[7] & 0x0C,
        0x08,
        "NES 2.0 header must set byte 7 bits 2-3 to 10"
    );
    // Header is still 16 bytes — NES 2.0 is not a longer header,
    // it just reinterprets the existing bytes.
    assert_eq!(rom.len(), 16 + 16384);
}

#[test]
fn nes2_header_populates_bytes_8_through_15() {
    // Bytes 8-15 should all be zero for our tiny ROMs — we don't
    // use submappers, oversized PRG/CHR, CHR RAM, or non-NTSC
    // timing — but they must still be present (not omitted).
    let mut builder = RomBuilder::new(Mirroring::Horizontal);
    builder.enable_nes2();
    let rom = builder.build();
    assert_eq!(&rom[8..16], &[0u8; 8]);
}

#[test]
fn nes2_preserves_mapper_and_mirroring() {
    // Opting into NES 2.0 should not disturb the mapper or
    // mirroring fields in bytes 6-7.
    let mut builder = RomBuilder::new(Mirroring::Vertical);
    builder.set_mapper(crate::rom::mapper_number(crate::parser::ast::Mapper::MMC3));
    builder.enable_nes2();
    let rom = builder.build();
    // Vertical mirroring keeps bit 0 of byte 6 set.
    assert_eq!(rom[6] & 1, 1);
    // Mapper 4 splits 0x40 across byte 6 high nibble and byte 7
    // high nibble: 4 = 0b0100 → nibble 0 goes to byte 7.
    let info = validate_ines(&rom).unwrap();
    assert_eq!(info.mapper, 4);
    assert_eq!(info.header_format, HeaderFormat::Nes2);
    assert_eq!(info.mirroring, Mirroring::Vertical);
}

#[test]
fn validate_accepts_both_header_formats() {
    // iNES 1.0 ROM validates and is marked as `Ines1`.
    let ines1 = RomBuilder::new(Mirroring::Horizontal).build();
    let info1 = validate_ines(&ines1).unwrap();
    assert_eq!(info1.header_format, HeaderFormat::Ines1);

    // NES 2.0 ROM validates and is marked as `Nes2`.
    let mut b = RomBuilder::new(Mirroring::Horizontal);
    b.enable_nes2();
    let nes2 = b.build();
    let info2 = validate_ines(&nes2).unwrap();
    assert_eq!(info2.header_format, HeaderFormat::Nes2);
}

#[test]
fn nes2_mapper_high_nibble_in_byte_8_is_zero_for_small_mappers() {
    // NEScript only supports u8 mapper numbers, so byte 8's low
    // nibble (mapper bits 8-11) is always zero. Verify that
    // explicitly so a future change that accidentally shifts bits
    // into byte 8 is caught.
    for mapper in [
        crate::parser::ast::Mapper::NROM,
        crate::parser::ast::Mapper::MMC1,
        crate::parser::ast::Mapper::UxROM,
        crate::parser::ast::Mapper::MMC3,
        crate::parser::ast::Mapper::AxROM,
        crate::parser::ast::Mapper::CNROM,
        crate::parser::ast::Mapper::GNROM,
    ] {
        let mut builder = RomBuilder::new(Mirroring::Horizontal);
        builder.set_mapper(crate::rom::mapper_number(mapper));
        builder.enable_nes2();
        let rom = builder.build();
        assert_eq!(rom[8], 0, "byte 8 should be zero for {mapper:?}");
    }
}
