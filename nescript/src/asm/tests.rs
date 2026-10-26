use super::*;
use opcodes::{AddressingMode as AM, Opcode::*};

#[allow(clippy::needless_pass_by_value)]
fn encode_ok(opcode: Opcode, mode: AM) -> Vec<u8> {
    assemble_instruction(opcode, &mode).expect("encoding should succeed")
}

#[allow(clippy::needless_pass_by_value)]
fn encode_fails(opcode: Opcode, mode: AM) {
    assert!(
        assemble_instruction(opcode, &mode).is_none(),
        "encoding should fail"
    );
}

// ── LDA ──

#[test]
fn lda_immediate() {
    assert_eq!(encode_ok(LDA, AM::Immediate(0xFF)), vec![0xA9, 0xFF]);
}

#[test]
fn lda_zero_page() {
    assert_eq!(encode_ok(LDA, AM::ZeroPage(0x10)), vec![0xA5, 0x10]);
}

#[test]
fn lda_zero_page_x() {
    assert_eq!(encode_ok(LDA, AM::ZeroPageX(0x10)), vec![0xB5, 0x10]);
}

#[test]
fn lda_absolute() {
    assert_eq!(encode_ok(LDA, AM::Absolute(0x8000)), vec![0xAD, 0x00, 0x80]);
}

#[test]
fn lda_absolute_x() {
    assert_eq!(
        encode_ok(LDA, AM::AbsoluteX(0x8000)),
        vec![0xBD, 0x00, 0x80]
    );
}

#[test]
fn lda_absolute_y() {
    assert_eq!(
        encode_ok(LDA, AM::AbsoluteY(0x8000)),
        vec![0xB9, 0x00, 0x80]
    );
}

#[test]
fn lda_indirect_x() {
    assert_eq!(encode_ok(LDA, AM::IndirectX(0x10)), vec![0xA1, 0x10]);
}

#[test]
fn lda_indirect_y() {
    assert_eq!(encode_ok(LDA, AM::IndirectY(0x10)), vec![0xB1, 0x10]);
}

// ── LDX ──

#[test]
fn ldx_immediate() {
    assert_eq!(encode_ok(LDX, AM::Immediate(0x42)), vec![0xA2, 0x42]);
}

#[test]
fn ldx_zero_page() {
    assert_eq!(encode_ok(LDX, AM::ZeroPage(0x10)), vec![0xA6, 0x10]);
}

#[test]
fn ldx_zero_page_y() {
    assert_eq!(encode_ok(LDX, AM::ZeroPageY(0x10)), vec![0xB6, 0x10]);
}

#[test]
fn ldx_absolute() {
    assert_eq!(encode_ok(LDX, AM::Absolute(0x4000)), vec![0xAE, 0x00, 0x40]);
}

// ── LDY ──

#[test]
fn ldy_immediate() {
    assert_eq!(encode_ok(LDY, AM::Immediate(0x00)), vec![0xA0, 0x00]);
}

#[test]
fn ldy_zero_page_x() {
    assert_eq!(encode_ok(LDY, AM::ZeroPageX(0x10)), vec![0xB4, 0x10]);
}

// ── STA ──

#[test]
fn sta_zero_page() {
    assert_eq!(encode_ok(STA, AM::ZeroPage(0x10)), vec![0x85, 0x10]);
}

#[test]
fn sta_absolute() {
    assert_eq!(encode_ok(STA, AM::Absolute(0x2000)), vec![0x8D, 0x00, 0x20]);
}

#[test]
fn sta_indirect_y() {
    assert_eq!(encode_ok(STA, AM::IndirectY(0x10)), vec![0x91, 0x10]);
}

// ── STX, STY ──

#[test]
fn stx_zero_page() {
    assert_eq!(encode_ok(STX, AM::ZeroPage(0x10)), vec![0x86, 0x10]);
}

#[test]
fn sty_zero_page() {
    assert_eq!(encode_ok(STY, AM::ZeroPage(0x10)), vec![0x84, 0x10]);
}

// ── ADC ──

#[test]
fn adc_immediate() {
    assert_eq!(encode_ok(ADC, AM::Immediate(0x02)), vec![0x69, 0x02]);
}

#[test]
fn adc_zero_page() {
    assert_eq!(encode_ok(ADC, AM::ZeroPage(0x10)), vec![0x65, 0x10]);
}

// ── SBC ──

#[test]
fn sbc_immediate() {
    assert_eq!(encode_ok(SBC, AM::Immediate(0x01)), vec![0xE9, 0x01]);
}

// ── AND, ORA, EOR ──

#[test]
fn and_immediate() {
    assert_eq!(encode_ok(AND, AM::Immediate(0x0F)), vec![0x29, 0x0F]);
}

#[test]
fn ora_immediate() {
    assert_eq!(encode_ok(ORA, AM::Immediate(0xF0)), vec![0x09, 0xF0]);
}

#[test]
fn eor_immediate() {
    assert_eq!(encode_ok(EOR, AM::Immediate(0xFF)), vec![0x49, 0xFF]);
}

// ── Shifts ──

#[test]
fn asl_accumulator() {
    assert_eq!(encode_ok(ASL, AM::Accumulator), vec![0x0A]);
}

#[test]
fn lsr_accumulator() {
    assert_eq!(encode_ok(LSR, AM::Accumulator), vec![0x4A]);
}

#[test]
fn rol_accumulator() {
    assert_eq!(encode_ok(ROL, AM::Accumulator), vec![0x2A]);
}

#[test]
fn ror_accumulator() {
    assert_eq!(encode_ok(ROR, AM::Accumulator), vec![0x6A]);
}

#[test]
fn asl_zero_page() {
    assert_eq!(encode_ok(ASL, AM::ZeroPage(0x10)), vec![0x06, 0x10]);
}

// ── INC, DEC ──

#[test]
fn inc_zero_page() {
    assert_eq!(encode_ok(INC, AM::ZeroPage(0x10)), vec![0xE6, 0x10]);
}

#[test]
fn dec_zero_page() {
    assert_eq!(encode_ok(DEC, AM::ZeroPage(0x10)), vec![0xC6, 0x10]);
}

// ── Implied ──

#[test]
fn implied_instructions() {
    assert_eq!(encode_ok(INX, AM::Implied), vec![0xE8]);
    assert_eq!(encode_ok(INY, AM::Implied), vec![0xC8]);
    assert_eq!(encode_ok(DEX, AM::Implied), vec![0xCA]);
    assert_eq!(encode_ok(DEY, AM::Implied), vec![0x88]);
    assert_eq!(encode_ok(CLC, AM::Implied), vec![0x18]);
    assert_eq!(encode_ok(SEC, AM::Implied), vec![0x38]);
    assert_eq!(encode_ok(CLI, AM::Implied), vec![0x58]);
    assert_eq!(encode_ok(SEI, AM::Implied), vec![0x78]);
    assert_eq!(encode_ok(CLV, AM::Implied), vec![0xB8]);
    assert_eq!(encode_ok(CLD, AM::Implied), vec![0xD8]);
    assert_eq!(encode_ok(SED, AM::Implied), vec![0xF8]);
    assert_eq!(encode_ok(NOP, AM::Implied), vec![0xEA]);
    assert_eq!(encode_ok(BRK, AM::Implied), vec![0x00]);
    assert_eq!(encode_ok(RTS, AM::Implied), vec![0x60]);
    assert_eq!(encode_ok(RTI, AM::Implied), vec![0x40]);
}

// ── Stack ──

#[test]
fn stack_instructions() {
    assert_eq!(encode_ok(PHA, AM::Implied), vec![0x48]);
    assert_eq!(encode_ok(PLA, AM::Implied), vec![0x68]);
    assert_eq!(encode_ok(PHP, AM::Implied), vec![0x08]);
    assert_eq!(encode_ok(PLP, AM::Implied), vec![0x28]);
}

// ── Transfer ──

#[test]
fn transfer_instructions() {
    assert_eq!(encode_ok(TAX, AM::Implied), vec![0xAA]);
    assert_eq!(encode_ok(TAY, AM::Implied), vec![0xA8]);
    assert_eq!(encode_ok(TXA, AM::Implied), vec![0x8A]);
    assert_eq!(encode_ok(TYA, AM::Implied), vec![0x98]);
    assert_eq!(encode_ok(TSX, AM::Implied), vec![0xBA]);
    assert_eq!(encode_ok(TXS, AM::Implied), vec![0x9A]);
}

// ── CMP, CPX, CPY ──

#[test]
fn cmp_immediate() {
    assert_eq!(encode_ok(CMP, AM::Immediate(0x10)), vec![0xC9, 0x10]);
}

#[test]
fn cpx_immediate() {
    assert_eq!(encode_ok(CPX, AM::Immediate(0x10)), vec![0xE0, 0x10]);
}

#[test]
fn cpy_immediate() {
    assert_eq!(encode_ok(CPY, AM::Immediate(0x10)), vec![0xC0, 0x10]);
}

// ── BIT ──

#[test]
fn bit_zero_page() {
    assert_eq!(encode_ok(BIT, AM::ZeroPage(0x10)), vec![0x24, 0x10]);
}

// ── JMP, JSR ──

#[test]
fn jmp_absolute() {
    assert_eq!(encode_ok(JMP, AM::Absolute(0x8000)), vec![0x4C, 0x00, 0x80]);
}

#[test]
fn jmp_indirect() {
    assert_eq!(encode_ok(JMP, AM::Indirect(0xFFFC)), vec![0x6C, 0xFC, 0xFF]);
}

#[test]
fn jsr_absolute() {
    assert_eq!(encode_ok(JSR, AM::Absolute(0x8000)), vec![0x20, 0x00, 0x80]);
}

// ── Branches ──

#[test]
fn branch_instructions() {
    assert_eq!(encode_ok(BEQ, AM::Relative(5)), vec![0xF0, 0x05]);
    assert_eq!(encode_ok(BNE, AM::Relative(-3)), vec![0xD0, 0xFD]);
    assert_eq!(encode_ok(BCC, AM::Relative(0)), vec![0x90, 0x00]);
    assert_eq!(encode_ok(BCS, AM::Relative(10)), vec![0xB0, 0x0A]);
    assert_eq!(encode_ok(BMI, AM::Relative(1)), vec![0x30, 0x01]);
    assert_eq!(encode_ok(BPL, AM::Relative(2)), vec![0x10, 0x02]);
    assert_eq!(encode_ok(BVC, AM::Relative(3)), vec![0x50, 0x03]);
    assert_eq!(encode_ok(BVS, AM::Relative(4)), vec![0x70, 0x04]);
}

// ── Invalid combinations ──

#[test]
fn invalid_sta_immediate() {
    encode_fails(STA, AM::Immediate(0));
}

#[test]
fn invalid_jmp_immediate() {
    encode_fails(JMP, AM::Immediate(0));
}

#[test]
fn invalid_lda_implied() {
    encode_fails(LDA, AM::Implied);
}

#[test]
fn invalid_jsr_zero_page() {
    encode_fails(JSR, AM::ZeroPage(0));
}

// ── Instruction size ──

#[test]
fn instruction_sizes() {
    assert_eq!(Instruction::implied(NOP).size(), 1);
    assert_eq!(Instruction::new(LDA, AM::Immediate(0)).size(), 2);
    assert_eq!(Instruction::new(LDA, AM::Absolute(0)).size(), 3);
    assert_eq!(Instruction::new(ASL, AM::Accumulator).size(), 1);
    assert_eq!(Instruction::new(BEQ, AM::Relative(0)).size(), 2);
}

// ── Assembler with labels ──

#[test]
fn assemble_with_labels() {
    let instructions = vec![
        // label: "loop"
        Instruction::new(NOP, AM::Label("loop".into())),
        // NOP
        Instruction::implied(NOP),
        // BNE loop
        Instruction::new(BNE, AM::LabelRelative("loop".into())),
    ];
    let result = assemble(&instructions, 0x8000);
    // NOP at $8000, BNE $8000 at $8001
    // BNE opcode = 0xD0, offset = 0x8000 - (0x8001 + 2) = -3 = 0xFD
    assert_eq!(result.bytes, vec![0xEA, 0xD0, 0xFD]);
    assert_eq!(result.labels["loop"], 0x8000);
}

// ── Endianness ──

#[test]
fn little_endian_addresses() {
    // 6502 is little-endian
    let bytes = encode_ok(LDA, AM::Absolute(0x1234));
    assert_eq!(bytes, vec![0xAD, 0x34, 0x12]); // low byte first
}

// ── Full sequence test ──

#[test]
fn assemble_add_immediate() {
    // LDA $10 / CLC / ADC #2 / STA $10
    let instructions = vec![
        Instruction::new(LDA, AM::ZeroPage(0x10)),
        Instruction::implied(CLC),
        Instruction::new(ADC, AM::Immediate(2)),
        Instruction::new(STA, AM::ZeroPage(0x10)),
    ];
    let result = assemble(&instructions, 0x8000);
    assert_eq!(result.bytes, vec![0xA5, 0x10, 0x18, 0x69, 0x02, 0x85, 0x10]);
}

// ── Code review regression tests ──

#[test]
#[should_panic(expected = "branch offset")]
fn branch_out_of_range_panics() {
    // Regression: branch offsets > 127 bytes used to silently wrap
    let mut instructions = vec![Instruction::new(NOP, AM::Label("start".into()))];
    // Insert 200 NOPs to push the branch target out of range
    for _ in 0..200 {
        instructions.push(Instruction::implied(NOP));
    }
    instructions.push(Instruction::new(BEQ, AM::LabelRelative("start".into())));
    let _ = assemble(&instructions, 0x8000);
}

#[test]
#[should_panic(expected = "unresolved label")]
fn unresolved_label_panics() {
    // Regression: unresolved labels used to silently produce offset 0
    let instructions = vec![Instruction::new(
        BEQ,
        AM::LabelRelative("nonexistent".into()),
    )];
    let _ = assemble(&instructions, 0x8000);
}
