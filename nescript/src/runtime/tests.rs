use super::*;
use crate::asm;
use crate::asm::{AddressingMode as AM, Opcode::*};

#[test]
fn init_disables_irq() {
    let init = gen_init(true);
    assert_eq!(init[0].opcode, SEI);
}

#[test]
fn init_sets_stack_pointer() {
    let init = gen_init(true);
    // LDX #$FF, TXS
    let has_ldx = init
        .iter()
        .any(|i| i.opcode == LDX && i.mode == AM::Immediate(0xFF));
    let has_txs = init.iter().any(|i| i.opcode == TXS);
    assert!(has_ldx, "should load $FF into X");
    assert!(has_txs, "should transfer X to stack pointer");
}

#[test]
fn init_disables_ppu() {
    let init = gen_init(true);
    // Should write 0 to $2000 and $2001
    let writes_ppu_ctrl = init
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x2000));
    let writes_ppu_mask = init
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x2001));
    assert!(writes_ppu_ctrl, "should disable PPU control");
    assert!(writes_ppu_mask, "should disable PPU mask");
}

#[test]
fn init_enables_nmi_at_end() {
    let init = gen_init(true);
    // Last STA $2000 should enable NMI (bit 7 set = 0x80)
    let nmi_writes: Vec<_> = init
        .iter()
        .enumerate()
        .filter(|(_, i)| i.opcode == STA && i.mode == AM::Absolute(0x2000))
        .collect();
    assert!(
        nmi_writes.len() >= 2,
        "should write to PPU_CTRL at least twice"
    );
    // The last write should be preceded by LDA #$80
    let last_write_idx = nmi_writes.last().unwrap().0;
    assert!(last_write_idx > 0);
    assert_eq!(init[last_write_idx - 1].opcode, LDA);
    assert_eq!(init[last_write_idx - 1].mode, AM::Immediate(0x80));
}

#[test]
fn init_assembles_without_error() {
    let init = gen_init(true);
    let result = asm::assemble(&init, 0x8000);
    // Should produce non-empty output
    assert!(!result.bytes.is_empty(), "init should produce bytes");
    // Should be under 200 bytes (the plan estimates ~80)
    assert!(
        result.bytes.len() < 200,
        "init is {} bytes, expected < 200",
        result.bytes.len()
    );
}

#[test]
fn nmi_saves_and_restores_registers() {
    let nmi = gen_nmi(NmiOptions::default());
    // First three instructions should push A, X, Y
    assert_eq!(nmi[0].opcode, PHA);
    assert_eq!(nmi[1].opcode, TXA);
    assert_eq!(nmi[2].opcode, PHA);
    assert_eq!(nmi[3].opcode, TYA);
    assert_eq!(nmi[4].opcode, PHA);

    // Last instructions should restore and RTI
    let len = nmi.len();
    assert_eq!(nmi[len - 1].opcode, RTI);
    assert_eq!(nmi[len - 2].opcode, PLA);
}

#[test]
fn nmi_triggers_oam_dma_when_requested() {
    let nmi = gen_nmi(NmiOptions {
        has_oam: true,
        ..NmiOptions::default()
    });
    let has_dma = nmi
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4014));
    assert!(has_dma, "NMI should trigger OAM DMA when has_oam is set");
}

#[test]
fn nmi_skips_oam_dma_by_default() {
    // With `has_oam = false` (the default) the NMI must not write
    // the OAM DMA trigger at $4014, saving ~520 cycles per frame
    // for programs that don't `draw`.
    let nmi = gen_nmi(NmiOptions::default());
    let has_dma = nmi
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4014));
    assert!(!has_dma, "NMI should skip OAM DMA when has_oam is unset");
}

#[test]
fn nmi_reads_controller_when_p1_requested() {
    let nmi = gen_nmi(NmiOptions {
        has_p1_input: true,
        ..NmiOptions::default()
    });
    // Should write strobe to $4016
    let has_strobe = nmi
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4016));
    assert!(has_strobe, "NMI should strobe controller when P1 requested");
    let reads_joy1 = nmi
        .iter()
        .any(|i| i.opcode == LDA && i.mode == AM::Absolute(0x4016));
    assert!(reads_joy1, "NMI should read JOY1 when P1 requested");
}

#[test]
fn nmi_skips_strobe_when_no_input() {
    // With both `has_p1_input` and `has_p2_input` unset, the NMI
    // should emit neither the strobe write to $4016 nor any reads
    // from the two controller ports — programs that never touch
    // `button.*` pay zero cycles for input sampling.
    let nmi = gen_nmi(NmiOptions::default());
    let has_strobe = nmi
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4016));
    assert!(
        !has_strobe,
        "NMI must not strobe controllers when no input is requested"
    );
    let reads_joy1 = nmi
        .iter()
        .any(|i| i.opcode == LDA && i.mode == AM::Absolute(0x4016));
    let reads_joy2 = nmi
        .iter()
        .any(|i| i.opcode == LDA && i.mode == AM::Absolute(0x4017));
    assert!(!reads_joy1, "NMI must not read JOY1 without P1 input");
    assert!(!reads_joy2, "NMI must not read JOY2 without P2 input");
}

#[test]
fn nmi_sets_frame_flag() {
    let nmi = gen_nmi(NmiOptions::default());
    let has_flag = nmi
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::ZeroPage(ZP_FRAME_FLAG));
    assert!(has_flag, "NMI should set frame-ready flag");
}

#[test]
fn nmi_assembles_without_error() {
    let nmi = gen_nmi(NmiOptions::default());
    let result = asm::assemble(&nmi, 0xF000);
    assert!(!result.bytes.is_empty());
    assert!(
        result.bytes.len() < 150,
        "NMI handler is {} bytes, expected < 150",
        result.bytes.len()
    );
}

#[test]
fn nmi_debug_mode_bumps_overrun_counter() {
    // With `debug_mode = true`, the NMI handler must include an
    // `INC $07FF` (the frame-overrun counter at
    // `DEBUG_FRAME_OVERRUN_ADDR`) guarded by a BEQ that skips the
    // bump when the frame flag was clear. Without `debug_mode`,
    // neither the `INC` nor the guard label appear so release
    // builds keep the top byte of RAM free for user allocation.
    let nmi = gen_nmi(NmiOptions {
        debug_mode: true,
        ..NmiOptions::default()
    });
    let has_inc = nmi.iter().any(|i| {
        i.opcode == INC && matches!(i.mode, AM::Absolute(a) if a == DEBUG_FRAME_OVERRUN_ADDR)
    });
    assert!(
        has_inc,
        "debug-mode NMI should INC the overrun counter at $07FF"
    );

    let release_nmi = gen_nmi(NmiOptions::default());
    let has_inc_release = release_nmi.iter().any(|i| {
        i.opcode == INC && matches!(i.mode, AM::Absolute(a) if a == DEBUG_FRAME_OVERRUN_ADDR)
    });
    assert!(
        !has_inc_release,
        "release NMI must not touch the debug overrun slot"
    );
}

#[test]
fn nmi_debug_mode_samples_sprite_overflow() {
    // Debug NMI should read $2002 and INC the sprite overflow
    // counter at DEBUG_SPRITE_OVERFLOW_COUNT_ADDR when bit 5 is
    // set. Release NMI must not touch either.
    let nmi = gen_nmi(NmiOptions {
        debug_mode: true,
        ..NmiOptions::default()
    });
    let has_status_read = nmi
        .iter()
        .any(|i| i.opcode == LDA && i.mode == AM::Absolute(0x2002));
    assert!(
        has_status_read,
        "debug-mode NMI should read $2002 to sample sprite overflow"
    );
    let has_inc = nmi.iter().any(|i| {
        i.opcode == INC
            && matches!(i.mode, AM::Absolute(a) if a == DEBUG_SPRITE_OVERFLOW_COUNT_ADDR)
    });
    assert!(
        has_inc,
        "debug-mode NMI should INC the sprite overflow counter at $07FD"
    );
    let has_sticky = nmi.iter().any(|i| {
        i.opcode == STA && matches!(i.mode, AM::Absolute(a) if a == DEBUG_SPRITE_OVERFLOW_FLAG_ADDR)
    });
    assert!(
        has_sticky,
        "debug-mode NMI should set the sprite overflow sticky bit at $07FC"
    );

    let release_nmi = gen_nmi(NmiOptions::default());
    let has_inc_release = release_nmi.iter().any(|i| {
        i.opcode == INC
            && matches!(i.mode, AM::Absolute(a) if a == DEBUG_SPRITE_OVERFLOW_COUNT_ADDR)
    });
    assert!(
        !has_inc_release,
        "release NMI must not touch the sprite overflow counter slot"
    );
}

#[test]
fn nmi_sprite_cycle_variant_reads_rotating_offset() {
    // With `has_sprite_cycle = true`, the NMI handler should
    // read SPRITE_CYCLE_ADDR and write it to OAM_ADDR ($2003)
    // before the DMA, instead of the default fixed 0. The
    // default variant must stay byte-identical to legacy NMI.
    // Sprite cycling is always paired with `has_oam = true`
    // (cycling is pointless without the DMA).
    let cycling = gen_nmi(NmiOptions {
        has_sprite_cycle: true,
        has_oam: true,
        ..NmiOptions::default()
    });
    let reads_cycle = cycling
        .iter()
        .any(|i| i.opcode == LDA && i.mode == AM::Absolute(SPRITE_CYCLE_ADDR));
    assert!(
        reads_cycle,
        "sprite-cycling NMI should read SPRITE_CYCLE_ADDR"
    );

    let default = gen_nmi(NmiOptions::default());
    let reads_cycle_default = default
        .iter()
        .any(|i| i.opcode == LDA && i.mode == AM::Absolute(SPRITE_CYCLE_ADDR));
    assert!(
        !reads_cycle_default,
        "default NMI must not touch SPRITE_CYCLE_ADDR"
    );
}

#[test]
fn irq_handler_is_just_rti() {
    let irq = gen_irq();
    assert_eq!(irq.len(), 1);
    assert_eq!(irq[0].opcode, RTI);
}

#[test]
fn multiply_routine_assembles() {
    let mul = gen_multiply();
    // Should have a reasonable number of instructions
    assert!(
        mul.len() > 5,
        "multiply routine too short: {} instructions",
        mul.len()
    );
    let result = asm::assemble(&mul, 0x8000);
    assert!(
        !result.bytes.is_empty(),
        "multiply routine should produce bytes"
    );
    // Should be under 100 bytes (compact 6502 routine)
    assert!(
        result.bytes.len() < 100,
        "multiply routine is {} bytes, expected < 100",
        result.bytes.len()
    );
    // Should contain the __multiply label
    assert!(
        result.labels.contains_key("__multiply"),
        "should define __multiply label"
    );
    // Should end with RTS
    assert_eq!(
        mul.last().unwrap().opcode,
        RTS,
        "multiply routine should end with RTS"
    );
}

// ── Audio driver tests ──

#[test]
fn audio_tick_defines_required_labels() {
    let tick = gen_audio_tick(false, false, false);
    // The IR codegen JSRs into `__audio_tick`; that's the entry.
    let has_entry = tick
        .iter()
        .any(|i| matches!(&i.mode, AM::Label(n) if n == "__audio_tick"));
    assert!(has_entry, "audio tick must define __audio_tick entry label");
    // The tick references `__period_table` via SymbolLo/SymbolHi —
    // the period table itself is linked in separately.
    let refs_period = tick.iter().any(|i| {
        matches!(&i.mode, AM::SymbolLo(n) if n == "__period_table")
            || matches!(&i.mode, AM::SymbolHi(n) if n == "__period_table")
    });
    assert!(
        refs_period,
        "audio tick must reference the __period_table label"
    );
}

#[test]
fn audio_tick_ends_with_rts() {
    let tick = gen_audio_tick(false, false, false);
    assert_eq!(
        tick.last().unwrap().opcode,
        RTS,
        "audio tick must return to caller"
    );
}

#[test]
fn audio_tick_reads_sfx_envelope_via_indirect_y() {
    // The sfx branch walks the envelope via (ZP_SFX_PTR_LO),Y with
    // Y=0 — each NMI reads one byte through the pointer and writes
    // it to $4000. Verify the indirect-indexed load is present.
    let tick = gen_audio_tick(false, false, false);
    let has_load = tick
        .iter()
        .any(|i| i.opcode == LDA && i.mode == AM::IndirectY(ZP_SFX_PTR_LO));
    assert!(
        has_load,
        "audio tick must read envelope via (ZP_SFX_PTR_LO),Y"
    );
}

#[test]
fn audio_tick_writes_pulse1_envelope_register() {
    // After reading the envelope byte the tick writes it to $4000.
    let tick = gen_audio_tick(false, false, false);
    let has_store = tick
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4000));
    assert!(has_store, "audio tick must write pulse-1 envelope to $4000");
}

#[test]
fn audio_tick_noise_block_writes_400c_when_enabled() {
    // With `has_noise = true` the tick gains a block that loads an
    // envelope byte and writes it to the APU noise volume register
    // at $400C. Verify both the marker label and the STA $400C are
    // present.
    let tick = gen_audio_tick(true, false, false);
    let has_label = tick
        .iter()
        .any(|i| matches!(&i.mode, AM::Label(n) if n == "__audio_noise_tick"));
    assert!(has_label, "noise tick should define __audio_noise_tick");
    let has_400c = tick
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x400C));
    assert!(has_400c, "noise tick should write to $400C");
}

#[test]
fn audio_tick_noise_block_absent_when_disabled() {
    // The pulse-only path must not emit any noise label, so
    // programs that never declare a noise sfx get byte-identical
    // code to the pre-feature version.
    let tick = gen_audio_tick(false, false, false);
    let has_label = tick
        .iter()
        .any(|i| matches!(&i.mode, AM::Label(n) if n == "__audio_noise_tick"));
    assert!(
        !has_label,
        "noise tick label must not appear when flag is off"
    );
    let has_400c = tick
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x400C));
    assert!(
        !has_400c,
        "noise $400C write must not appear when flag is off"
    );
}

#[test]
fn audio_tick_triangle_block_writes_4008_when_enabled() {
    let tick = gen_audio_tick(false, true, false);
    let has_label = tick
        .iter()
        .any(|i| matches!(&i.mode, AM::Label(n) if n == "__audio_triangle_tick"));
    assert!(
        has_label,
        "triangle tick should define __audio_triangle_tick"
    );
    let has_4008 = tick
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4008));
    assert!(has_4008, "triangle tick should write to $4008");
}

#[test]
fn audio_tick_triangle_block_absent_when_disabled() {
    let tick = gen_audio_tick(false, false, false);
    let has_label = tick
        .iter()
        .any(|i| matches!(&i.mode, AM::Label(n) if n == "__audio_triangle_tick"));
    assert!(!has_label);
    let has_4008 = tick
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4008));
    assert!(!has_4008);
}

#[test]
fn audio_tick_sfx_pitch_block_writes_4002_when_enabled() {
    // With `has_sfx_pitch = true` the tick gains a per-frame pitch
    // update path that writes to `$4002` (pulse-1 period low) on
    // every NMI. The path also needs to read the pitch envelope
    // pointer from main RAM, so we check both the absolute-RAM
    // load and the period write.
    let tick = gen_audio_tick(false, false, true);
    let writes_4002 = tick
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4002));
    assert!(
        writes_4002,
        "sfx pitch tick path should write to $4002 (pulse-1 period low)"
    );
    let reads_pitch_ptr = tick
        .iter()
        .any(|i| i.opcode == LDA && i.mode == AM::Absolute(AUDIO_SFX_PITCH_PTR_LO));
    assert!(
        reads_pitch_ptr,
        "sfx pitch tick path should LDA from AUDIO_SFX_PITCH_PTR_LO"
    );
}

#[test]
fn audio_tick_sfx_pitch_block_absent_when_disabled() {
    // Programs without varying-pitch sfx must not pay any bytes
    // for the pitch update path, otherwise existing audio_demo /
    // friendly_assets goldens would byte-shift.
    let tick = gen_audio_tick(false, false, false);
    let writes_4002 = tick
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4002));
    assert!(
        !writes_4002,
        "sfx pitch tick path must not appear when flag is off"
    );
    let reads_pitch_ptr = tick
        .iter()
        .any(|i| i.opcode == LDA && i.mode == AM::Absolute(AUDIO_SFX_PITCH_PTR_LO));
    assert!(
        !reads_pitch_ptr,
        "AUDIO_SFX_PITCH_PTR_LO must not be touched when flag is off"
    );
}

#[test]
fn audio_tick_both_channels_assemble() {
    // With both new channels enabled, the tick + period table must
    // still fit its internal branches (±127 bytes) and assemble
    // successfully.
    let mut combined = gen_audio_tick(true, true, false);
    combined.extend(gen_period_table());
    let result = asm::assemble(&combined, 0xC000);
    assert!(!result.bytes.is_empty());
    assert!(result.labels.contains_key("__audio_noise_tick"));
    assert!(result.labels.contains_key("__audio_triangle_tick"));
}

#[test]
fn audio_tick_mutes_pulse2_on_non_looping_end_of_track() {
    // When a non-looping track hits the (0xFF, 0xFF) sentinel, the
    // tick writes $30 to $4004 and clears ZP_MUSIC_STATE. We verify
    // the mute path exists by checking both writes exist somewhere
    // in the tick body.
    let tick = gen_audio_tick(false, false, false);
    let has_mute = tick
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0x4004));
    assert!(has_mute, "audio tick must mute pulse-2 on end-of-track");
    let has_state_clear = tick
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::ZeroPage(ZP_MUSIC_STATE));
    assert!(
        has_state_clear,
        "audio tick must clear ZP_MUSIC_STATE on stop"
    );
}

#[test]
fn audio_tick_assembles_without_error() {
    // Splice the period table into the same assembly pass so the
    // tick's SymbolLo/SymbolHi references resolve. The tick also
    // uses label-relative branches internally which need to fit
    // within ±127 bytes — if the body grows past that the branches
    // will panic at assemble time.
    let mut combined = gen_audio_tick(false, false, false);
    combined.extend(gen_period_table());
    let result = asm::assemble(&combined, 0xC000);
    assert!(
        !result.bytes.is_empty(),
        "audio tick + period table should assemble"
    );
    assert!(
        result.labels.contains_key("__audio_tick"),
        "audio tick entry label should be exported"
    );
    assert!(
        result.labels.contains_key("__period_table"),
        "period table label should be exported"
    );
}

#[test]
fn period_table_has_60_entries_of_2_bytes() {
    // The table covers C1..B5 inclusive = 60 semitones, 2 bytes
    // each for period_lo and period_hi. Total = 120 data bytes
    // plus the leading label pseudo-instruction.
    let table = gen_period_table();
    // Count the raw bytes in the single `Bytes` block.
    let total: usize = table
        .iter()
        .filter_map(|i| match &i.mode {
            AM::Bytes(v) => Some(v.len()),
            _ => None,
        })
        .sum();
    assert_eq!(total, 120, "period table should be 60 entries × 2 bytes");
}

#[test]
fn period_table_high_bytes_include_length_counter_bit() {
    // Every period_hi byte must have bit 3 set ($08) so the length
    // counter holds the note indefinitely. Without that bit, pulse
    // 2 would silence after a few frames.
    let table = gen_period_table();
    let bytes: Vec<u8> = table
        .iter()
        .filter_map(|i| match &i.mode {
            AM::Bytes(v) => Some(v.clone()),
            _ => None,
        })
        .flatten()
        .collect();
    for (i, chunk) in bytes.chunks(2).enumerate() {
        let hi = chunk[1];
        assert!(
            hi & 0x08 != 0,
            "period table entry {i} high byte ${hi:02X} missing length-counter bit"
        );
    }
}

#[test]
fn period_table_a4_matches_440hz() {
    // Entry for A4 should produce ~253 period. Sanity check the
    // rounding: CPU/(16*440)-1 ≈ 253.12.
    let table = gen_period_table();
    let bytes: Vec<u8> = table
        .iter()
        .filter_map(|i| match &i.mode {
            AM::Bytes(v) => Some(v.clone()),
            _ => None,
        })
        .flatten()
        .collect();
    // A4 is semitone 69 in MIDI. C1 is MIDI 24 (entry 0 in the
    // table). A4 = entry 69 - 24 = 45. Each entry is 2 bytes.
    let lo = bytes[45 * 2];
    let hi = bytes[45 * 2 + 1] & 0x07; // strip length-counter bit
    let period = u16::from_le_bytes([lo, hi]);
    // Expect period ≈ 253 (±1 for rounding).
    assert!(
        (252..=254).contains(&period),
        "A4 period {period} should be ~253"
    );
}

#[test]
fn gen_data_block_emits_label_and_bytes() {
    let block = gen_data_block("__sfx_test", vec![0xDE, 0xAD, 0xBE, 0xEF]);
    assert_eq!(block.len(), 2);
    assert!(matches!(&block[0].mode, AM::Label(n) if n == "__sfx_test"));
    match &block[1].mode {
        AM::Bytes(v) => assert_eq!(v, &[0xDE, 0xAD, 0xBE, 0xEF]),
        other => panic!("expected Bytes, got {other:?}"),
    }
}

#[test]
fn data_block_assembles_verbatim() {
    // A labelled data block must emit exactly the payload bytes
    // (no opcode prefix) and register the label at the payload's
    // address. Verifies the `NOP+Bytes` pseudo doesn't accidentally
    // get wrapped with an instruction byte.
    let block = gen_data_block("__test", vec![0x11, 0x22, 0x33]);
    let result = asm::assemble(&block, 0x8000);
    assert_eq!(result.bytes, vec![0x11, 0x22, 0x33]);
    assert_eq!(result.labels.get("__test").copied(), Some(0x8000));
}

#[test]
fn divide_routine_assembles() {
    let div = gen_divide();
    // Should have a reasonable number of instructions
    assert!(
        div.len() > 5,
        "divide routine too short: {} instructions",
        div.len()
    );
    let result = asm::assemble(&div, 0x8000);
    assert!(
        !result.bytes.is_empty(),
        "divide routine should produce bytes"
    );
    // Should be under 100 bytes (compact 6502 routine)
    assert!(
        result.bytes.len() < 100,
        "divide routine is {} bytes, expected < 100",
        result.bytes.len()
    );
    // Should contain the __divide label
    assert!(
        result.labels.contains_key("__divide"),
        "should define __divide label"
    );
    // Should end with RTS
    assert_eq!(
        div.last().unwrap().opcode,
        RTS,
        "divide routine should end with RTS"
    );
}

/// `$03` is `ZP_CURRENT_STATE` in the codegen — the byte the main
/// dispatch loop reads every frame to pick the right `on_frame`
/// handler. If the divide routine writes to `$03` at any point it
/// zeroes the current-state value and kicks the state machine back
/// to state 0 on the very next frame (see the PR that introduced
/// the platformer HUD for the full repro). This test pins the
/// routine to a `$03`-free implementation so any future refactor
/// that reintroduces a ZP-3 write fails loudly instead of shipping
/// a silent miscompile.
#[test]
fn divide_routine_does_not_touch_zp_03() {
    for inst in gen_divide() {
        let touches_03 = matches!(&inst.mode, AM::ZeroPage(0x03));
        assert!(
            !touches_03,
            "gen_divide emitted an instruction touching $03 \
             (collides with ZP_CURRENT_STATE): {:?} {:?}",
            inst.opcode, inst.mode,
        );
    }
}

/// Same argument as `divide_routine_does_not_touch_zp_03`, applied
/// to the multiplicand. The old `gen_multiply` accumulated the
/// result in ZP `$03` even for `u8 * u8 → u8` (the high byte was
/// simply discarded at the callsite), which silently corrupted
/// `ZP_CURRENT_STATE` across every `*` operator in a multi-state
/// program. Holding the running product in the accumulator instead
/// keeps `$03` pristine.
#[test]
fn multiply_routine_does_not_touch_zp_03() {
    for inst in gen_multiply() {
        let touches_03 = matches!(&inst.mode, AM::ZeroPage(0x03));
        assert!(
            !touches_03,
            "gen_multiply emitted an instruction touching $03 \
             (collides with ZP_CURRENT_STATE): {:?} {:?}",
            inst.opcode, inst.mode,
        );
    }
}

// ─── Bank switching ────────────────────────────────────────────────

#[test]
fn mapper_init_nrom_is_empty() {
    // NROM has no banks and nothing to configure at reset — the
    // generator must return an empty Vec so the linker doesn't
    // pay any ROM cost for unused mapper config.
    let init = gen_mapper_init(Mapper::NROM, Mirroring::Horizontal, 1);
    assert!(
        init.is_empty(),
        "NROM mapper init should be empty, got {} instructions",
        init.len()
    );
}

#[test]
fn mapper_init_mmc1_pulses_reset_and_writes_control() {
    // MMC1 init must: (1) pulse bit 7 of any $8000-range write to
    // reset the shift register, then (2) serialize a 5-bit control
    // value into the same $8000 register window. We verify:
    //   * there's at least one STA to $8000 preceded by LDA #$80
    //   * there are exactly 6 writes to $8000 total (1 reset + 5 bits)
    let init = gen_mapper_init(Mapper::MMC1, Mirroring::Horizontal, 4);
    let writes_8000: Vec<_> = init
        .iter()
        .enumerate()
        .filter(|(_, i)| i.opcode == STA && i.mode == AM::Absolute(0x8000))
        .collect();
    assert_eq!(
        writes_8000.len(),
        6,
        "MMC1 init should write to $8000 six times (1 reset + 5 control bits), got {}",
        writes_8000.len()
    );
    // The reset write comes first and must be preceded by LDA #$80.
    let first_idx = writes_8000[0].0;
    assert!(first_idx > 0);
    assert_eq!(init[first_idx - 1].opcode, LDA);
    assert_eq!(init[first_idx - 1].mode, AM::Immediate(0x80));
}

/// Find the first LDA immediate operand appearing after the MMC1
/// reset-pulse (`LDA #$80`) inside an MMC1 init sequence. Used by
/// [`mapper_init_mmc1_horizontal_vs_vertical_control_bits`] to
/// inspect the first serialized control-register bit.
fn mmc1_first_control_bit(init: &[Instruction]) -> Option<u8> {
    let mut saw_reset = false;
    for inst in init {
        if !saw_reset {
            if inst.opcode == LDA && inst.mode == AM::Immediate(0x80) {
                saw_reset = true;
            }
            continue;
        }
        if inst.opcode == LDA {
            if let AM::Immediate(v) = inst.mode {
                return Some(v);
            }
        }
    }
    None
}

#[test]
fn mapper_init_mmc1_horizontal_vs_vertical_control_bits() {
    // The control register's bits 0-1 encode mirroring. Our layout
    // uses $0F for horizontal (0b01111) and $0E for vertical
    // (0b01110). The first bit sent (LDA #0 or #1) differs between
    // the two — horizontal bit 0 = 1, vertical bit 0 = 0.
    let h = gen_mapper_init(Mapper::MMC1, Mirroring::Horizontal, 2);
    let v = gen_mapper_init(Mapper::MMC1, Mirroring::Vertical, 2);
    assert_eq!(
        mmc1_first_control_bit(&h),
        Some(1),
        "horizontal mirror bit 0"
    );
    assert_eq!(mmc1_first_control_bit(&v), Some(0), "vertical mirror bit 0");
}

#[test]
fn mapper_init_uxrom_emits_label_and_seeds_zp_bank_current() {
    // UxROM powers up with bank 0 at $8000 and the last bank fixed
    // at $C000, so apart from a marker label there's no mapper-
    // specific init to do — *but* the runtime now seeds
    // ZP_BANK_CURRENT with the fixed bank index so the
    // banked-call trampoline knows which bank to restore on the
    // way out. The seed is a 2-instruction LDA #imm / STA $10
    // pair appended after the marker label.
    let init = gen_mapper_init(Mapper::UxROM, Mirroring::Horizontal, 3);
    assert!(
        matches!(&init[0].mode, AM::Label(n) if n == "__uxrom_init"),
        "UxROM init should still start with the marker label",
    );
    assert_eq!(
        init.len(),
        3,
        "UxROM init should be marker + LDA #fixed + STA ZP_BANK_CURRENT"
    );
    assert_eq!(init[1].opcode, LDA);
    assert!(
        matches!(init[1].mode, AM::Immediate(2)),
        "fixed bank index for 3 banks is 2"
    );
    assert_eq!(init[2].opcode, STA);
    assert!(matches!(init[2].mode, AM::ZeroPage(addr) if addr == ZP_BANK_CURRENT));
}

#[test]
fn mapper_init_mmc3_configures_prg_and_mirroring() {
    // MMC3 init writes:
    //   $8000 = 6 (select PRG-0 register)
    //   $8001 = 0 (bank 0 at $8000)
    //   $8000 = 7 (select PRG-1 register)
    //   $8001 = 1 (bank 1 at $A000)
    //   $A000 = mirroring bit
    //   $E000 = 0 (disable IRQ)
    let init = gen_mapper_init(Mapper::MMC3, Mirroring::Vertical, 4);
    let count_writes = |addr: u16| -> usize {
        init.iter()
            .filter(|i| i.opcode == STA && i.mode == AM::Absolute(addr))
            .count()
    };
    assert_eq!(count_writes(0x8000), 2, "MMC3 should write $8000 twice");
    assert_eq!(count_writes(0x8001), 2, "MMC3 should write $8001 twice");
    assert_eq!(
        count_writes(0xA000),
        1,
        "MMC3 should write $A000 for mirroring"
    );
    assert_eq!(
        count_writes(0xE000),
        1,
        "MMC3 should clear $E000 to disable IRQ"
    );
}

#[test]
fn mapper_init_assembles_for_every_banked_mapper() {
    // Sanity check: every mapper's init sequence should pass the
    // assembler without unresolved labels. We splice in a dummy
    // reset label to prevent branch-range issues.
    for m in [Mapper::MMC1, Mapper::UxROM, Mapper::MMC3] {
        let init = gen_mapper_init(m, Mirroring::Horizontal, 2);
        let result = asm::assemble(&init, 0xC000);
        // Either empty (UxROM is basically zero-cost) or a short
        // init stub — all fit comfortably in < 100 bytes.
        assert!(
            result.bytes.len() < 100,
            "mapper {m:?} init is {} bytes, expected < 100",
            result.bytes.len()
        );
    }
}

#[test]
fn bank_select_nrom_is_a_plain_rts() {
    // The NROM bank-select stub exists so user code can
    // unconditionally call `__bank_select` regardless of mapper.
    // Its body must RTS immediately — no register writes.
    let sel = gen_bank_select(Mapper::NROM);
    assert!(matches!(&sel[0].mode, AM::Label(n) if n == "__bank_select"));
    assert_eq!(sel.last().unwrap().opcode, RTS);
    // Must not write to any mapper register.
    let writes_mapper = sel.iter().any(|i| {
        i.opcode == STA
            && matches!(
                &i.mode,
                AM::Absolute(a) if (0x8000..=0xFFFF).contains(a)
            )
    });
    assert!(!writes_mapper, "NROM bank-select must not write to $8000+");
}

#[test]
fn bank_select_mmc1_serializes_five_bits_to_e000() {
    // MMC1 bank-select serializes the 5 LSBs of A into the $E000
    // register. We check: exactly 5 STA $E000 instructions, and
    // they're interleaved with LSR A shifts between them (4 LSRs
    // total — one between each pair of writes).
    let sel = gen_bank_select(Mapper::MMC1);
    let writes_e000 = sel
        .iter()
        .filter(|i| i.opcode == STA && i.mode == AM::Absolute(0xE000))
        .count();
    assert_eq!(writes_e000, 5, "MMC1 should write $E000 five times");
    let lsrs = sel
        .iter()
        .filter(|i| i.opcode == LSR && i.mode == AM::Accumulator)
        .count();
    assert_eq!(lsrs, 4, "MMC1 should shift A four times between bit writes");
    assert_eq!(sel.last().unwrap().opcode, RTS);
}

#[test]
fn bank_select_uxrom_uses_bus_conflict_table() {
    // UxROM bank-select has to write to a ROM address whose byte
    // already equals the bank being selected. The routine does
    // `TAX; STA __bank_select_table, X` so the store goes to
    // `table + bank_num`, whose ROM byte is `bank_num` — making
    // the bus write match the ROM byte regardless of which bank
    // is being requested. We assert both pieces here so a
    // regression back to the broken `STA $FFF0` form fails
    // loudly.
    let sel = gen_bank_select(Mapper::UxROM);
    let has_tax = sel.iter().any(|i| i.opcode == TAX && i.mode == AM::Implied);
    assert!(has_tax, "UxROM bank-select must TAX before the store");
    let has_indexed_store = sel.iter().any(|i| {
        i.opcode == STA && matches!(&i.mode, AM::LabelAbsoluteX(n) if n == "__bank_select_table")
    });
    assert!(
        has_indexed_store,
        "UxROM bank-select must `STA __bank_select_table,X`"
    );
    let writes_fff0 = sel
        .iter()
        .any(|i| i.opcode == STA && i.mode == AM::Absolute(0xFFF0));
    assert!(
        !writes_fff0,
        "UxROM bank-select must not fall back to the bus-conflict-unsafe STA $FFF0 form"
    );
    assert_eq!(sel.last().unwrap().opcode, RTS);
}

#[test]
fn bank_select_mmc3_writes_8000_and_8001() {
    // MMC3 bank-select writes 6 to $8000, then writes A to $8001.
    // We check both writes happen exactly once.
    let sel = gen_bank_select(Mapper::MMC3);
    let writes_8000 = sel
        .iter()
        .filter(|i| i.opcode == STA && i.mode == AM::Absolute(0x8000))
        .count();
    let writes_8001 = sel
        .iter()
        .filter(|i| i.opcode == STA && i.mode == AM::Absolute(0x8001))
        .count();
    assert_eq!(writes_8000, 1, "MMC3 should write $8000 once");
    assert_eq!(writes_8001, 1, "MMC3 should write $8001 once");
    assert_eq!(sel.last().unwrap().opcode, RTS);
}

#[test]
fn bank_select_stashes_bank_number_in_zp() {
    // Every bank-select routine (including NROM) saves A into
    // ZP_BANK_CURRENT so trampolines can restore the previous
    // bank later.
    for m in [Mapper::NROM, Mapper::MMC1, Mapper::UxROM, Mapper::MMC3] {
        let sel = gen_bank_select(m);
        let has_stash = sel
            .iter()
            .any(|i| i.opcode == STA && i.mode == AM::ZeroPage(ZP_BANK_CURRENT));
        assert!(
            has_stash,
            "mapper {m:?} bank-select must stash A into ZP_BANK_CURRENT"
        );
    }
}

#[test]
fn bank_select_assembles_for_every_mapper() {
    for m in [Mapper::NROM, Mapper::MMC1, Mapper::UxROM, Mapper::MMC3] {
        let mut sel = gen_bank_select(m);
        // UxROM `gen_bank_select` references `__bank_select_table`
        // via `AM::LabelAbsoluteX`; give the assembler something
        // to resolve against in this standalone unit test. Real
        // linking appends the table in the linker pass, so the
        // label always resolves there.
        if m == Mapper::UxROM {
            sel.extend(super::gen_uxrom_bank_table());
        }
        let result = asm::assemble(&sel, 0xC000);
        assert!(
            !result.bytes.is_empty(),
            "mapper {m:?} bank-select produced no bytes"
        );
        assert!(
            result.labels.contains_key("__bank_select"),
            "mapper {m:?} bank-select must export __bank_select"
        );
    }
}

#[test]
fn trampoline_switches_target_then_restores_caller() {
    // A trampoline must save the caller's bank from
    // ZP_BANK_CURRENT, switch to the target, call the entry, then
    // restore the saved value. We check the immediate loaded
    // (target bank), the PHA/PLA pair around the body, and the
    // JSR sequence.
    let t = gen_bank_trampoline("__tramp_helper", "__ir_fn_helper", 0);
    // First instruction is the trampoline label.
    assert!(matches!(&t[0].mode, AM::Label(n) if n == "__tramp_helper"));
    // The only LDA immediate is the target bank itself — the
    // restore path uses PLA, not a hardcoded LDA, so the caller's
    // bank can be anything.
    let imms: Vec<u8> = t
        .iter()
        .filter_map(|i| {
            if i.opcode == LDA {
                if let AM::Immediate(v) = i.mode {
                    return Some(v);
                }
            }
            None
        })
        .collect();
    assert_eq!(
        imms,
        vec![0],
        "trampoline must load only the target bank as an immediate"
    );
    // The trampoline must read ZP_BANK_CURRENT into A then PHA
    // (save), and later PLA (restore).
    let reads_current = t.iter().any(|i| {
        i.opcode == LDA && matches!(i.mode, AM::ZeroPage(addr) if addr == ZP_BANK_CURRENT)
    });
    assert!(
        reads_current,
        "trampoline must LDA ZP_BANK_CURRENT to capture the caller's bank"
    );
    let pushes = t.iter().filter(|i| i.opcode == PHA).count();
    let pops = t.iter().filter(|i| i.opcode == PLA).count();
    assert_eq!(
        (pushes, pops),
        (1, 1),
        "trampoline must have exactly one PHA / PLA pair"
    );
    // And two JSRs to __bank_select, plus one JSR to the entry —
    // dispatch order is still target-first, restore-last.
    let jsrs: Vec<&str> = t
        .iter()
        .filter_map(|i| {
            if i.opcode == JSR {
                if let AM::Label(n) = &i.mode {
                    return Some(n.as_str());
                }
            }
            None
        })
        .collect();
    assert_eq!(
        jsrs,
        vec!["__bank_select", "__ir_fn_helper", "__bank_select"],
        "trampoline JSRs must dispatch target → entry → restore"
    );
    // Final instruction returns to caller.
    assert_eq!(t.last().unwrap().opcode, RTS);
}

#[test]
fn trampoline_label_uses_caller_supplied_name() {
    // The codegen picks the trampoline label (typically
    // `__tramp_<fn_name>`) so it can JSR it from the call site
    // without knowing bank indices. `gen_bank_trampoline` should
    // emit that exact label as its leading pseudo-op so the
    // assembler resolves the JSR.
    let t = gen_bank_trampoline("__tramp_big_helper", "__ir_fn_big_helper", 1);
    assert!(matches!(&t[0].mode, AM::Label(n) if n == "__tramp_big_helper"));
}

#[test]
fn mapper_init_seeds_zp_bank_current_with_fixed_bank_index() {
    // The trampoline reads ZP_BANK_CURRENT to decide which bank
    // to switch back to after a cross-bank call. For fixed-bank
    // callers that have never explicitly switched banks, the
    // value must point at the fixed bank — otherwise the very
    // first cross-bank call from the fixed bank would restore
    // bank 0 (the RAM-clear default) at $8000, breaking the
    // pre-banked-banked semantics that other examples rely on.
    //
    // For UxROM with 6 banks, the fixed bank is index 5.
    let init = gen_mapper_init(Mapper::UxROM, Mirroring::Horizontal, 6);
    let mut found_seed = false;
    let mut last_imm: Option<u8> = None;
    for inst in &init {
        if inst.opcode == LDA {
            if let AM::Immediate(v) = inst.mode {
                last_imm = Some(v);
            }
        }
        if inst.opcode == STA {
            if let AM::ZeroPage(addr) = inst.mode {
                if addr == ZP_BANK_CURRENT && last_imm == Some(5) {
                    found_seed = true;
                    break;
                }
            }
        }
    }
    assert!(
        found_seed,
        "gen_mapper_init must seed ZP_BANK_CURRENT with the fixed bank index (5 here)"
    );
}

#[test]
fn nrom_mapper_init_does_not_seed_zp_bank_current() {
    // NROM has no banks at all, so seeding ZP_BANK_CURRENT would
    // both waste a couple of bytes and cause the existing NROM
    // example ROMs (every flat-mapper sample) to byte-shift.
    // Verify the init stays empty for NROM.
    let init = gen_mapper_init(Mapper::NROM, Mirroring::Horizontal, 1);
    assert!(
        init.is_empty(),
        "NROM mapper init must remain empty: {init:?}"
    );
}

#[test]
fn uxrom_bank_table_is_256_bytes_of_sequential_values() {
    // The bus-conflict table must contain bytes 0..=255 in order
    // so that `STA __bank_select_table,X` where X = desired bank
    // number produces a matching ROM byte.
    let table = gen_uxrom_bank_table();
    assert_eq!(table.len(), 2);
    assert!(matches!(&table[0].mode, AM::Label(n) if n == "__bank_select_table"));
    match &table[1].mode {
        AM::Bytes(v) => {
            assert_eq!(v.len(), 256);
            for (i, &b) in v.iter().enumerate() {
                assert_eq!(b as usize, i, "table byte at {i} should equal {i}");
            }
        }
        other => panic!("expected Bytes, got {other:?}"),
    }
}
