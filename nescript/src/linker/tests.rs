use super::*;
use crate::asm::{AddressingMode as AM, Instruction, Opcode::*};
use crate::parser::ast::{Channel, Mapper, Mirroring};
use crate::rom;

#[test]
fn link_produces_valid_ines() {
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__main_loop".into())),
        Instruction::implied(NOP),
        Instruction::new(JMP, AM::Label("__main_loop".into())),
    ];
    let rom_data = linker.link(&user_code);
    let info = rom::validate_ines(&rom_data).unwrap();
    assert_eq!(info.prg_banks, 1);
    assert_eq!(info.chr_banks, 1);
    assert_eq!(info.mapper, 0);
}

#[test]
fn link_has_correct_vector_table() {
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![Instruction::implied(NOP)];
    let rom_data = linker.link(&user_code);

    // Vector table is at the last 6 bytes of PRG ROM
    // PRG starts at offset 16 in the .nes file
    let prg_end = 16 + 16384;
    let vector_start = prg_end - 6;

    // NMI vector (2 bytes, little-endian)
    let nmi = u16::from_le_bytes([rom_data[vector_start], rom_data[vector_start + 1]]);
    // RESET vector
    let reset = u16::from_le_bytes([rom_data[vector_start + 2], rom_data[vector_start + 3]]);
    // IRQ vector
    let irq = u16::from_le_bytes([rom_data[vector_start + 4], rom_data[vector_start + 5]]);

    // All vectors should be in the $C000-$FFFF range
    assert!(nmi >= 0xC000, "NMI vector {nmi:#06X} should be >= $C000");
    assert!(
        reset >= 0xC000,
        "RESET vector {reset:#06X} should be >= $C000"
    );
    assert!(irq >= 0xC000, "IRQ vector {irq:#06X} should be >= $C000");

    // RESET should point to the start of code ($C000)
    assert_eq!(reset, 0xC000, "RESET should point to $C000");
}

#[test]
fn link_includes_chr_data() {
    // When user code signals that it uses the default smiley tile
    // (fallback for an unresolved `draw` target), the linker should
    // copy the built-in 16-byte smiley CHR blob into tile 0.
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__default_sprite_used".into())),
        Instruction::implied(NOP),
    ];
    let rom_data = linker.link(&user_code);

    // CHR starts after PRG
    let chr_start = 16 + 16384;
    // First 16 bytes should be the smiley sprite
    assert_ne!(
        &rom_data[chr_start..chr_start + 16],
        &[0u8; 16],
        "CHR data should contain sprite tile"
    );
}

#[test]
fn link_omits_default_smiley_without_marker() {
    // Without the `__default_sprite_used` marker the linker should
    // leave tile 0 as the all-zero blank tile — programs that draw
    // only user-declared sprites or never draw at all reclaim the
    // 16 CHR bytes.
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![Instruction::implied(NOP)];
    let rom_data = linker.link(&user_code);
    let chr_start = 16 + 16384;
    assert_eq!(
        &rom_data[chr_start..chr_start + 16],
        &[0u8; 16],
        "tile 0 should be zero when no program draws fall back to the smiley"
    );
}

#[test]
fn link_rom_size_correct() {
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![Instruction::implied(NOP)];
    let rom_data = linker.link(&user_code);

    // 16 header + 16384 PRG + 8192 CHR
    assert_eq!(rom_data.len(), 16 + 16384 + 8192);
}

#[test]
fn sprite_cycle_marker_implies_oam_dma() {
    // `cycle_sprites` rotates the OAM DMA start offset each frame;
    // without the DMA itself the cycling is a no-op. The linker's
    // `has_oam` gate therefore ORs `__sprite_cycle_used` with
    // `__oam_used` so a program that only cycles still gets the
    // DMA plumbing. The NMI of such a program writes the DMA
    // trigger at `$4014`.
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__sprite_cycle_used".into())),
        Instruction::implied(NOP),
    ];
    let rom = linker.link(&user_code);
    // The OAM DMA write is `STA $4014` — `8D 14 40` in bytes.
    let prg = &rom[16..16 + 16_384];
    assert!(
        prg.windows(3).any(|w| w == [0x8D, 0x14, 0x40]),
        "cycle_sprites should force the OAM DMA even without a draw"
    );
}

#[test]
fn link_with_sprites_places_chr_data() {
    let linker = Linker::new(Mirroring::Horizontal);
    // Seed the `__default_sprite_used` marker so the linker still
    // emits the smiley tile alongside the user sprite — this test
    // asserts the legacy "smiley at tile 0, user sprite at tile 1"
    // layout that programs doing both fallback and named draws
    // depend on.
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__default_sprite_used".into())),
        Instruction::implied(NOP),
    ];

    let sprite_bytes: Vec<u8> = (0x20..0x30).collect(); // 16 bytes, one tile
    let sprites = vec![SpriteData {
        name: "Player".into(),
        tile_index: 1,
        chr_bytes: sprite_bytes.clone(),
    }];

    let rom_data = linker.link_with_assets(&user_code, &sprites);

    // CHR starts right after the 16-byte iNES header and 16 KB PRG bank.
    let chr_start = 16 + 16384;

    // Tile 0 should still contain the built-in smiley (first 16 bytes, not
    // all zero).
    let tile0 = &rom_data[chr_start..chr_start + 16];
    assert_ne!(
        tile0, &[0u8; 16],
        "default smiley should occupy tile index 0",
    );

    // Tile 1 (CHR offset 16) should contain the sprite's CHR bytes exactly.
    let tile1 = &rom_data[chr_start + 16..chr_start + 32];
    assert_eq!(tile1, sprite_bytes.as_slice());

    // Tile 2 and beyond should be untouched (all zeros).
    let tile2 = &rom_data[chr_start + 32..chr_start + 48];
    assert_eq!(tile2, &[0u8; 16]);
}

#[test]
fn link_with_sprites_spanning_multiple_tiles() {
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![Instruction::implied(NOP)];

    // 32 bytes = 2 tiles. The linker should place them consecutively
    // starting at the requested tile index.
    let sprite_bytes: Vec<u8> = (0..32).collect();
    let sprites = vec![SpriteData {
        name: "Big".into(),
        tile_index: 4,
        chr_bytes: sprite_bytes.clone(),
    }];

    let rom_data = linker.link_with_assets(&user_code, &sprites);
    let chr_start = 16 + 16384;

    // Tile 4 starts at CHR offset 64.
    let placed = &rom_data[chr_start + 64..chr_start + 64 + 32];
    assert_eq!(placed, sprite_bytes.as_slice());
}

#[test]
fn link_with_background_chr_places_blob_after_sprites() {
    // A `BackgroundData` carrying its own CHR data should drop
    // the bytes into CHR ROM at `chr_base_tile * 16`. The
    // linker must NOT touch any earlier tiles (the smiley at
    // tile 0 plus any sprites). We seed a sprite at tile 1 and
    // a background at tile 5, then verify the linker placed
    // both blobs at their expected offsets.
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![Instruction::implied(NOP)];
    let sprite_bytes: Vec<u8> = vec![0xAA; 16]; // tile 1
    let bg_chr: Vec<u8> = (0u8..32u8).collect(); // tiles 5, 6
    let sprites = vec![SpriteData {
        name: "Player".into(),
        tile_index: 1,
        chr_bytes: sprite_bytes.clone(),
    }];
    let backgrounds = vec![crate::assets::BackgroundData {
        name: "Stage".into(),
        tiles: [5u8; 960],
        attrs: [0u8; 64],
        chr_bytes: bg_chr.clone(),
        chr_base_tile: 5,
    }];
    let rom = linker.link_banked_with_ppu(&user_code, &sprites, &[], &[], &[], &backgrounds, &[]);
    let chr_start = 16 + 16384;
    // Sprite bytes still at tile 1.
    assert_eq!(
        &rom[chr_start + 16..chr_start + 32],
        sprite_bytes.as_slice(),
        "sprite tile bytes should survive the background CHR splice"
    );
    // Background CHR at tile 5 (offset 80).
    assert_eq!(
        &rom[chr_start + 80..chr_start + 80 + 32],
        bg_chr.as_slice(),
        "background CHR bytes should land at chr_base_tile * 16"
    );
    // Tiles 2/3/4 should still be all zeros — the linker mustn't
    // shadow the gap between the sprite tile and the background.
    for tile in 2..5usize {
        let off = chr_start + tile * 16;
        assert_eq!(
            &rom[off..off + 16],
            &[0u8; 16],
            "tile {tile} should remain zero between sprite and background"
        );
    }
}

#[test]
fn link_splices_audio_tick_when_user_marker_present() {
    // When user code contains the `__audio_used` marker label (the
    // IR codegen emits this whenever it sees a `play`/`start_music`/
    // `stop_music` op), the linker must splice a `JSR __audio_tick`
    // into the NMI handler prologue AND link in the audio driver
    // body so the JSR target exists.
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![
        // Pretend user code with the marker the codegen would emit.
        Instruction::new(NOP, AM::Label("__audio_used".into())),
        Instruction::implied(NOP),
    ];
    let rom_data = linker.link(&user_code);

    // The ROM should be valid even with the splice — the driver
    // body has to fit in bank 0 without overflowing.
    let info = rom::validate_ines(&rom_data).unwrap();
    assert_eq!(info.prg_banks, 1);
}

#[test]
fn link_omits_audio_tick_when_no_marker() {
    // User code without the marker should not pay any ROM cost
    // for the audio driver. We can't easily inspect bytes, but we
    // can at least verify the ROM builds and has a normal shape.
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![Instruction::implied(NOP)];
    let rom_data = linker.link(&user_code);
    let info = rom::validate_ines(&rom_data).unwrap();
    assert_eq!(info.prg_banks, 1);
}

#[test]
fn link_with_audio_data_places_sfx_blobs_in_prg() {
    // When user code has the `__audio_used` marker AND we pass in
    // sfx data, the linker must:
    //   1. Splice in the audio tick (driver body)
    //   2. Splice in the period table
    //   3. Splice in the envelope blob under its label
    //   4. Resolve SymbolLo/SymbolHi references from user code to
    //      the blob's address (second pass of the assembler)
    let linker = Linker::new(Mirroring::Horizontal);
    // User code: `LDA #<__sfx_test`, `STA $0C`, `LDA #>__sfx_test`,
    // `STA $0D` — simulates what IR codegen's gen_play_sfx emits.
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__audio_used".into())),
        Instruction::new(LDA, AM::SymbolLo("__sfx_test".into())),
        Instruction::new(STA, AM::ZeroPage(0x0C)),
        Instruction::new(LDA, AM::SymbolHi("__sfx_test".into())),
        Instruction::new(STA, AM::ZeroPage(0x0D)),
    ];
    let sfx = vec![SfxData {
        name: "test".into(),
        period_lo: 0x50,
        period_hi: 0x08,
        envelope: vec![0xBF, 0xB8, 0xB4, 0xB0, 0x00],
        pitch_envelope: Vec::new(),
        channel: Channel::Pulse1,
    }];
    let rom = linker.link_with_all_assets(&user_code, &[], &sfx, &[]);
    let info = rom::validate_ines(&rom).unwrap();
    assert_eq!(info.prg_banks, 1);
    // The envelope bytes must appear somewhere in PRG. Find them.
    let prg = &rom[16..16 + 16384];
    let needle = [0xBF, 0xB8, 0xB4, 0xB0, 0x00];
    let found = prg.windows(needle.len()).any(|w| w == needle);
    assert!(found, "sfx envelope bytes should be spliced into PRG ROM");
}

#[test]
fn link_with_audio_data_places_music_stream_in_prg() {
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__audio_used".into())),
        Instruction::new(LDA, AM::SymbolLo("__music_test".into())),
        Instruction::new(STA, AM::ZeroPage(0x0E)),
        Instruction::new(LDA, AM::SymbolHi("__music_test".into())),
        Instruction::new(STA, AM::ZeroPage(0x0F)),
    ];
    let music = vec![MusicData {
        name: "test".into(),
        header: 0xA9,
        stream: vec![37, 8, 41, 8, 44, 8, 0xFF, 0xFF],
    }];
    let rom = linker.link_with_all_assets(&user_code, &[], &[], &music);
    let prg = &rom[16..16 + 16384];
    let needle = [37, 8, 41, 8, 44, 8, 0xFF, 0xFF];
    let found = prg.windows(needle.len()).any(|w| w == needle);
    assert!(found, "music note stream should be spliced into PRG ROM");
}

#[test]
fn link_with_audio_resolves_sfx_pointer_references() {
    // The SymbolLo/SymbolHi references in user code must get
    // fixed up to the *actual* PRG address of the envelope blob.
    // We can verify this by reading back the user code bytes and
    // checking that the LDA immediates point somewhere in the
    // valid PRG range ($C000-$FFFF).
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__audio_used".into())),
        Instruction::new(LDA, AM::SymbolLo("__sfx_test".into())),
        Instruction::new(LDA, AM::SymbolHi("__sfx_test".into())),
    ];
    let sfx = vec![SfxData {
        name: "test".into(),
        period_lo: 0x50,
        period_hi: 0x08,
        envelope: vec![0xDE, 0xAD, 0xBE, 0xEF, 0x00],
        pitch_envelope: Vec::new(),
        channel: Channel::Pulse1,
    }];
    let rom = linker.link_with_all_assets(&user_code, &[], &sfx, &[]);
    // The user code starts at RESET ($C000) after init+palette_load.
    // Rather than compute the exact offset, verify the envelope
    // bytes appear at a byte that matches what the LDA immediate
    // pair would produce. We find the immediate pair by searching
    // for `A9 xx A9 yy` and checking `$xxyy` points at the needle.
    let prg = &rom[16..16 + 16384];
    let needle = [0xDE, 0xAD, 0xBE, 0xEF, 0x00];
    // Find where the envelope lives in ROM.
    let env_offset = prg
        .windows(needle.len())
        .position(|w| w == needle)
        .expect("envelope should be in PRG");
    let env_addr = 0xC000u16 + env_offset as u16;
    // Find any LDA-immediate pair that matches the envelope address.
    let lo = (env_addr & 0xFF) as u8;
    let hi = (env_addr >> 8) as u8;
    let pattern = [0xA9u8, lo, 0xA9, hi];
    let matched = prg.windows(pattern.len()).any(|w| w == pattern);
    assert!(
        matched,
        "should find `LDA #<env_addr; LDA #>env_addr` in PRG ($A9 ${lo:02X} $A9 ${hi:02X})"
    );
}

#[test]
fn link_without_audio_marker_does_not_emit_period_table() {
    // Programs that never use audio must not pay the cost of the
    // period table, driver body, or any blobs. We verify this
    // indirectly: the `__period_table` label should NOT appear at
    // a distinct ROM address from the main body.
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![Instruction::implied(NOP)];
    let rom = linker.link_with_all_assets(
        &user_code,
        &[],
        &[SfxData {
            name: "unused".into(),
            period_lo: 0,
            period_hi: 0,
            envelope: vec![0xAA, 0xBB, 0x00],
            pitch_envelope: Vec::new(),
            channel: Channel::Pulse1,
        }],
        &[],
    );
    // The envelope bytes `AA BB 00` must NOT appear in PRG — the
    // linker should have elided the whole audio section because
    // the marker is absent.
    let prg = &rom[16..16 + 16384];
    let needle = [0xAAu8, 0xBB, 0x00];
    let found = prg.windows(needle.len()).any(|w| w == needle);
    assert!(
        !found,
        "unused sfx data should not be spliced when __audio_used is absent"
    );
}

// ─── Banked linking ────────────────────────────────────────────────

#[test]
fn link_banked_mmc1_produces_multi_bank_rom() {
    // MMC1 with two switchable banks should produce a 3-bank ROM
    // (2 switchable + 1 fixed). The iNES header must report 3 PRG
    // banks, mapper number 1, and the file size must match.
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::MMC1);
    let user_code = vec![Instruction::implied(NOP)];
    let banks = vec![PrgBank::empty("Level1"), PrgBank::empty("Level2")];
    let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
    let info = rom::validate_ines(&rom).unwrap();
    assert_eq!(info.prg_banks, 3);
    assert_eq!(info.mapper, 1);
    assert_eq!(rom.len(), 16 + 3 * 16384 + 8192);
}

#[test]
fn link_banked_uxrom_produces_multi_bank_rom() {
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::UxROM);
    let user_code = vec![Instruction::implied(NOP)];
    // Four switchable banks = 5 PRG banks total.
    let banks = vec![
        PrgBank::empty("BankA"),
        PrgBank::empty("BankB"),
        PrgBank::empty("BankC"),
        PrgBank::empty("BankD"),
    ];
    let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
    let info = rom::validate_ines(&rom).unwrap();
    assert_eq!(info.prg_banks, 5);
    assert_eq!(info.mapper, 2);
}

#[test]
fn link_banked_mmc3_produces_multi_bank_rom() {
    let linker = Linker::with_mapper(Mirroring::Vertical, Mapper::MMC3);
    let user_code = vec![Instruction::implied(NOP)];
    let banks = vec![
        PrgBank::empty("Stage1"),
        PrgBank::empty("Stage2"),
        PrgBank::empty("Stage3"),
    ];
    let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
    let info = rom::validate_ines(&rom).unwrap();
    assert_eq!(info.prg_banks, 4);
    assert_eq!(info.mapper, 4);
    // Vertical mirroring must propagate through the builder.
    assert_eq!(info.mirroring, Mirroring::Vertical);
}

#[test]
#[should_panic(expected = "NROM does not support switchable PRG banks")]
fn link_banked_nrom_rejects_switchable_banks() {
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::NROM);
    let _ = linker.link_banked(
        &[Instruction::implied(NOP)],
        &[],
        &[],
        &[],
        &[PrgBank::empty("Nope")],
    );
}

#[test]
fn link_banked_fixed_bank_lives_at_end_of_prg() {
    // The linker must place the fixed bank *last* so it maps to
    // $C000-$FFFF at reset. The vector table at $FFFA..$FFFF must
    // land in the final bank. We verify by reading the reset vector
    // and checking it points into the fixed bank's address window.
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::MMC1);
    let user_code = vec![Instruction::implied(NOP)];
    let banks = vec![PrgBank::empty("A"), PrgBank::empty("B")];
    let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
    // Three PRG banks = 48 KB; the fixed bank is the last 16 KB
    // slot in the file, and its $FFFA..$FFFF area holds the
    // vector table.
    let fixed_bank_offset = 16 + 2 * 16384;
    // Vectors live at the last 6 bytes of the fixed bank.
    let vec_offset = fixed_bank_offset + 16384 - 6;
    let reset = u16::from_le_bytes([rom[vec_offset + 2], rom[vec_offset + 3]]);
    assert!(
        reset >= 0xC000,
        "RESET vector {reset:#06X} should point into fixed bank ($C000-$FFFF)"
    );
}

#[test]
fn link_banked_switchable_banks_are_padded_with_ff() {
    // Empty switchable banks should end up as 16 KB of $FF — the
    // same pad value the ROM builder uses for unset code. This is
    // important so banks are always a known shape regardless of
    // payload.
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::MMC1);
    let user_code = vec![Instruction::implied(NOP)];
    let banks = vec![PrgBank::empty("Empty")];
    let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
    // Bank 0 is at offset 16; check a few bytes are $FF.
    assert_eq!(rom[16], 0xFF);
    assert_eq!(rom[16 + 100], 0xFF);
    // Last byte of bank 0 (just before bank 1 begins).
    assert_eq!(rom[16 + 16384 - 1], 0xFF);
}

#[test]
fn link_banked_assembles_switchable_bank_instructions() {
    // When a caller populates a switchable bank's instruction
    // stream, the linker must assemble those instructions at the
    // bank's $8000 base and splice the resulting bytes into the
    // bank's slot. We use a label + a couple of NOPs so the byte
    // pattern is unambiguous: NOP NOP NOP would be three $EA bytes
    // at the very start of the bank.
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::UxROM);
    let user_code = vec![Instruction::implied(NOP)];
    let bank_code = vec![
        Instruction::new(NOP, AM::Label("__bank_payload".into())),
        Instruction::implied(NOP),
        Instruction::implied(NOP),
        Instruction::implied(NOP),
    ];
    let banks = vec![PrgBank::with_instructions(
        "DataBank",
        bank_code,
        Vec::new(),
    )];
    let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
    // Bank 0 starts at offset 16. Verify the three NOP bytes land
    // at the very start (the label pseudo-op emits zero bytes).
    assert_eq!(&rom[16..19], &[0xEA, 0xEA, 0xEA]);
}

#[test]
fn link_banked_fixed_bank_contains_bank_select_subroutine() {
    // The linker must emit `__bank_select` (as labelled 6502 code)
    // somewhere in the fixed bank whenever the mapper isn't NROM.
    // We verify by assembling a minimal program and searching for
    // the opcode signature of the MMC1 bank-select tail — 5 STAs
    // to $E000 ($8D $00 $E0).
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::MMC1);
    let user_code = vec![Instruction::implied(NOP)];
    let banks = vec![PrgBank::empty("Foo")];
    let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
    // Fixed bank starts at offset 16 + 16384.
    let fixed = &rom[16 + 16384..16 + 2 * 16384];
    // Find five consecutive STA $E000 (opcode $8D operand $00 $E0)
    // instructions with LSR A ($4A) between pairs. This is the
    // signature pattern generated by `gen_bank_select(MMC1)`.
    let sta_e000 = [0x8D, 0x00, 0xE0];
    let lsr_then_sta_e000 = [0x4A, 0x8D, 0x00, 0xE0];
    let has_tail = fixed
        .windows(lsr_then_sta_e000.len())
        .any(|w| w == lsr_then_sta_e000);
    let sta_e000_count = fixed
        .windows(sta_e000.len())
        .filter(|w| w == &sta_e000)
        .count();
    assert!(
        has_tail,
        "MMC1 fixed bank should contain LSR A ; STA $E000 pattern"
    );
    assert!(
        sta_e000_count >= 5,
        "MMC1 fixed bank should contain >= 5 STA $E000 writes (bank-select + init), got {sta_e000_count}"
    );
}

#[test]
fn link_banked_fixed_bank_contains_trampolines_for_declared_banks() {
    // When a bank requests a trampoline, the linker must emit a
    // matching `__tramp_<name>` stub in the fixed bank that JSRs
    // the entry label inside the switchable bank. We check by
    // constructing a bank with both an entry-label-defining
    // instruction stream and a matching trampoline request, then
    // verifying the linker doesn't panic on unresolved fixups (the
    // banked-bank label seeding is what makes the JSR inside the
    // trampoline resolve correctly).
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::MMC1);
    let user_code = vec![Instruction::implied(NOP)];
    // The switchable bank holds the entry label and a tiny RTS so
    // there's something for the trampoline to JSR into.
    let bank_code = vec![
        Instruction::new(NOP, AM::Label("__ir_fn_helper".into())),
        Instruction::implied(RTS),
    ];
    let banks = vec![PrgBank::with_instructions(
        "Level1",
        bank_code,
        vec![BankTrampoline {
            tramp_label: "__tramp_helper".into(),
            entry_label: "__ir_fn_helper".into(),
        }],
    )];
    // Should not panic — trampoline and entry label both present.
    let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
    let info = rom::validate_ines(&rom).unwrap();
    assert_eq!(info.prg_banks, 2);
}

#[test]
fn link_banked_reset_vector_points_into_fixed_bank_window() {
    // The reset vector must land somewhere in $C000-$FFFF — that's
    // the CPU address where the fixed bank maps in at boot on every
    // supported mapper (NROM, MMC1, UxROM, MMC3).
    for mapper in [Mapper::NROM, Mapper::MMC1, Mapper::UxROM, Mapper::MMC3] {
        let linker = Linker::with_mapper(Mirroring::Horizontal, mapper);
        let user_code = vec![Instruction::implied(NOP)];
        let banks: Vec<PrgBank> = if mapper == Mapper::NROM {
            Vec::new()
        } else {
            vec![PrgBank::empty("X")]
        };
        let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
        // Last 6 bytes of PRG = vectors.
        let prg_end = 16 + rom::validate_ines(&rom).unwrap().prg_banks * 16384;
        let reset_bytes = [rom[prg_end - 4], rom[prg_end - 3]];
        let reset = u16::from_le_bytes(reset_bytes);
        assert!(
            (0xC000..=0xFFFF).contains(&reset),
            "{mapper:?} reset vector {reset:#06X} must live in fixed-bank window"
        );
    }
}

#[test]
fn link_banked_rom_size_matches_bank_count() {
    // For each banked mapper, verify total ROM file size =
    // 16 header + N * 16 KB PRG + 8 KB CHR.
    for (mapper, switchable) in [
        (Mapper::MMC1, 0usize),
        (Mapper::MMC1, 1),
        (Mapper::MMC1, 3),
        (Mapper::UxROM, 0),
        (Mapper::UxROM, 7),
        (Mapper::MMC3, 0),
        (Mapper::MMC3, 15),
    ] {
        let linker = Linker::with_mapper(Mirroring::Horizontal, mapper);
        let user_code = vec![Instruction::implied(NOP)];
        let banks: Vec<PrgBank> = (0..switchable)
            .map(|i| PrgBank::empty(format!("B{i}")))
            .collect();
        let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
        let expected_prg_banks = switchable + 1;
        let expected_len = 16 + expected_prg_banks * 16384 + 8192;
        assert_eq!(
            rom.len(),
            expected_len,
            "{mapper:?} with {switchable} switchable banks: expected {expected_len} bytes, got {}",
            rom.len(),
        );
    }
}

#[test]
fn link_with_mapper_nrom_produces_single_bank_rom() {
    // Regression: calling link_banked with NROM and no switchable
    // banks should produce the same 1-bank layout as the legacy
    // `link_with_all_assets` — no extra cost for the new API.
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::NROM);
    let user_code = vec![Instruction::implied(NOP)];
    let rom = linker.link_banked(&user_code, &[], &[], &[], &[]);
    let info = rom::validate_ines(&rom).unwrap();
    assert_eq!(info.prg_banks, 1);
    assert_eq!(info.mapper, 0);
    assert_eq!(rom.len(), 16 + 16384 + 8192);
}

#[test]
fn link_banked_chr_rom_survives_with_switchable_banks() {
    // The default smiley + any sprites should still appear in CHR
    // ROM even when switchable PRG banks are present. Seed the
    // `__default_sprite_used` marker so the smiley gate fires.
    let linker = Linker::with_mapper(Mirroring::Horizontal, Mapper::MMC1);
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__default_sprite_used".into())),
        Instruction::implied(NOP),
    ];
    let banks = vec![PrgBank::empty("X")];
    let rom = linker.link_banked(&user_code, &[], &[], &[], &banks);
    // CHR starts after 2 PRG banks.
    let chr_start = 16 + 2 * 16384;
    // First 16 bytes = smiley tile, non-zero.
    assert_ne!(&rom[chr_start..chr_start + 16], &[0u8; 16]);
}

#[test]
fn default_palette_blob_present_when_no_user_palette() {
    // With no user palette but some visual output (the IR codegen
    // drops an `__oam_used` marker whenever it lowers a `draw`),
    // the linker emits the shared reset-time loop loader and
    // splices a 32-byte `__default_palette` data block into PRG.
    // The end-to-end ROM should contain the default palette bytes
    // verbatim at some offset in the fixed bank.
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__oam_used".into())),
        Instruction::new(NOP, AM::Label("__ir_main_loop".into())),
    ];
    let rom = linker.link(&user_code);

    // The first four bytes of DEFAULT_PALETTE are {0x0F, 0x00, 0x10,
    // 0x20}; they should appear verbatim in the PRG portion of the
    // iNES file (bytes 16..16+16_384). We look for that 4-byte
    // sequence rather than matching the full 32 bytes so this stays
    // robust against minor palette tweaks.
    let prg = &rom[16..16 + 16_384];
    let found = prg.windows(4).any(|w| w == [0x0F, 0x00, 0x10, 0x20]);
    assert!(found, "default palette bytes should appear in PRG");
}

#[test]
fn default_palette_suppressed_when_no_visual_output() {
    // An audio- or compute-only program (no palette declared, no
    // sprites, no backgrounds, no `draw`) shouldn't pay for the
    // built-in default palette: no `__default_palette` label in
    // the symbol table, and the 32 bytes of palette data must not
    // appear anywhere in PRG.
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![Instruction::new(NOP, AM::Label("__ir_main_loop".into()))];
    let result = linker.link_banked_with_ppu_detailed(&user_code, &[], &[], &[], &[], &[], &[]);
    assert!(
        !result.labels.contains_key("__default_palette"),
        "default palette label must not be defined without visual output"
    );
    let prg = &result.rom[16..16 + 16_384];
    assert!(
        !prg.windows(4).any(|w| w == [0x0F, 0x00, 0x10, 0x20]),
        "default palette bytes must not appear in PRG when suppressed"
    );
}

#[test]
fn no_default_palette_blob_when_user_palette_present() {
    // A program that declares its own palette should suppress the
    // built-in fallback entirely — the `__default_palette` label
    // never gets emitted, and the assembler's label table doesn't
    // contain it.
    use crate::assets::PaletteData;
    let linker = Linker::new(Mirroring::Horizontal);
    let user_code = vec![Instruction::new(NOP, AM::Label("__ir_main_loop".into()))];
    let user_pal = PaletteData {
        name: "Menu".into(),
        colors: [0x0F; 32],
    };
    let result =
        linker.link_banked_with_ppu_detailed(&user_code, &[], &[], &[], &[user_pal], &[], &[]);
    assert!(
        !result.labels.contains_key("__default_palette"),
        "default palette must be suppressed when user palette is present"
    );
}

#[test]
fn link_banked_with_ppu_detailed_exposes_label_table() {
    // The detailed variant carries the assembler's symbol table so
    // the CLI can emit a `.mlb` file. Round-trip a minimal program
    // through the linker and verify the classic runtime labels
    // (`__reset`, `__nmi`, `__ir_main_loop`) show up with CPU
    // addresses in the $C000-$FFFF fixed-bank window.
    let lnk = Linker::new(Mirroring::Horizontal);
    let user_code = vec![
        Instruction::new(NOP, AM::Label("__ir_main_loop".into())),
        Instruction::new(JMP, AM::Label("__ir_main_loop".into())),
    ];
    let result = lnk.link_banked_with_ppu_detailed(&user_code, &[], &[], &[], &[], &[], &[]);
    assert!(
        result.labels.contains_key("__reset"),
        "LinkedRom should surface the reset label"
    );
    assert!(
        result.labels.contains_key("__nmi"),
        "LinkedRom should surface the nmi label"
    );
    assert!(
        result.labels.contains_key("__ir_main_loop"),
        "LinkedRom should surface user-code labels"
    );
    let main_addr = result.labels["__ir_main_loop"];
    assert!(
        (0xC000..=0xFFFF).contains(&main_addr),
        "fixed-bank label should sit inside the $C000-$FFFF window, got {main_addr:#06X}"
    );
    // NROM has no switchable banks, so the fixed bank starts right
    // after the 16-byte iNES header.
    assert_eq!(result.fixed_bank_file_offset, 16);
}
