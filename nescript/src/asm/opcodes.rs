use crate::lexer::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Opcode {
    LDA,
    LDX,
    LDY,
    STA,
    STX,
    STY,
    ADC,
    SBC,
    AND,
    ORA,
    EOR,
    ASL,
    LSR,
    ROL,
    ROR,
    INC,
    DEC,
    INX,
    INY,
    DEX,
    DEY,
    CMP,
    CPX,
    CPY,
    BIT,
    JMP,
    JSR,
    RTS,
    RTI,
    BEQ,
    BNE,
    BCC,
    BCS,
    BMI,
    BPL,
    BVC,
    BVS,
    CLC,
    SEC,
    CLI,
    SEI,
    CLV,
    CLD,
    SED,
    PHA,
    PLA,
    PHP,
    PLP,
    TAX,
    TAY,
    TXA,
    TYA,
    TSX,
    TXS,
    NOP,
    BRK,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AddressingMode {
    Implied,
    Accumulator,
    Immediate(u8),
    ZeroPage(u8),
    ZeroPageX(u8),
    ZeroPageY(u8),
    Absolute(u16),
    AbsoluteX(u16),
    AbsoluteY(u16),
    Indirect(u16),
    IndirectX(u8),
    IndirectY(u8),
    Relative(i8),

    // Pre-resolution symbolic forms
    Label(String),
    LabelRelative(String),
    /// Absolute-X indexed form targeting a named label — resolves
    /// to the 16-bit address of `label` at fix-up time, with the
    /// instruction encoded as `absolute,X`. Used by `UxROM`'s
    /// `__bank_select` to write into the bus-conflict table
    /// (`STA __bank_select_table,X`) where the target address has
    /// to be resolved by the linker.
    LabelAbsoluteX(String),
    SymbolLo(String),
    SymbolHi(String),

    /// Raw data payload — emitted verbatim by the assembler as a
    /// `NOP` pseudo-instruction. Used to splice data tables (audio
    /// envelopes, note streams, period tables) between code
    /// sections so they live inside the same PRG bank and get their
    /// labels resolved by the normal two-pass assembler.
    Bytes(Vec<u8>),
}

impl AddressingMode {
    /// Number of bytes for the operand (not including the opcode byte).
    pub fn operand_size(&self) -> usize {
        match self {
            Self::Implied | Self::Accumulator => 0,
            Self::Immediate(_)
            | Self::ZeroPage(_)
            | Self::ZeroPageX(_)
            | Self::ZeroPageY(_)
            | Self::IndirectX(_)
            | Self::IndirectY(_)
            | Self::Relative(_) => 1,
            Self::Absolute(_) | Self::AbsoluteX(_) | Self::AbsoluteY(_) | Self::Indirect(_) => 2,
            Self::Label(_)
            | Self::LabelRelative(_)
            | Self::LabelAbsoluteX(_)
            | Self::SymbolLo(_)
            | Self::SymbolHi(_) => 0,
            // `Bytes` is the full emitted payload — the assembler
            // skips the usual opcode byte for `NOP+Bytes` and writes
            // the raw vector, so the whole thing is operand.
            Self::Bytes(v) => v.len(),
        }
    }

    /// Get the operand bytes for resolved addressing modes.
    pub fn operand_bytes(&self) -> Vec<u8> {
        match self {
            Self::Implied | Self::Accumulator => vec![],
            Self::Immediate(v)
            | Self::ZeroPage(v)
            | Self::ZeroPageX(v)
            | Self::ZeroPageY(v)
            | Self::IndirectX(v)
            | Self::IndirectY(v) => vec![*v],
            Self::Relative(v) => vec![(*v).cast_unsigned()],
            Self::Absolute(v) | Self::AbsoluteX(v) | Self::AbsoluteY(v) | Self::Indirect(v) => {
                v.to_le_bytes().to_vec()
            }
            Self::Label(_)
            | Self::LabelRelative(_)
            | Self::LabelAbsoluteX(_)
            | Self::SymbolLo(_)
            | Self::SymbolHi(_) => {
                vec![]
            }
            Self::Bytes(v) => v.clone(),
        }
    }

    pub fn as_absolute_address(&self) -> Option<u16> {
        match self {
            Self::Absolute(a) | Self::AbsoluteX(a) | Self::AbsoluteY(a) | Self::Indirect(a) => {
                Some(*a)
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Instruction {
    pub opcode: Opcode,
    pub mode: AddressingMode,
    pub source: Option<Span>,
}

impl Instruction {
    pub fn new(opcode: Opcode, mode: AddressingMode) -> Self {
        Self {
            opcode,
            mode,
            source: None,
        }
    }

    pub fn implied(opcode: Opcode) -> Self {
        Self::new(opcode, AddressingMode::Implied)
    }

    /// Total size in bytes (opcode + operand).
    ///
    /// The `NOP`+`Label` pair is a label-definition pseudo — zero
    /// bytes. `NOP`+`Bytes(v)` is a raw-data pseudo — exactly `v.len()`
    /// bytes (no opcode). All other instructions are 1 byte opcode
    /// plus operand.
    pub fn size(&self) -> usize {
        match &self.mode {
            AddressingMode::Label(_) if self.opcode == Opcode::NOP => 0,
            AddressingMode::Bytes(v) if self.opcode == Opcode::NOP => v.len(),
            _ => 1 + self.mode.operand_size(),
        }
    }
}

/// Encode an opcode + addressing mode into the corresponding byte.
/// Returns None if the combination is invalid.
pub fn encode(opcode: Opcode, mode: &AddressingMode) -> Option<u8> {
    // 6502 opcode encoding table
    // This covers all legal opcode/addressing mode combinations
    use AddressingMode as AM;
    use Opcode::*;

    let result = match (opcode, mode) {
        // LDA
        (LDA, AM::Immediate(_)) => 0xA9,
        (LDA, AM::ZeroPage(_)) => 0xA5,
        (LDA, AM::ZeroPageX(_)) => 0xB5,
        (LDA, AM::Absolute(_)) => 0xAD,
        (LDA, AM::AbsoluteX(_)) => 0xBD,
        (LDA, AM::AbsoluteY(_)) => 0xB9,
        (LDA, AM::IndirectX(_)) => 0xA1,
        (LDA, AM::IndirectY(_)) => 0xB1,

        // LDX
        (LDX, AM::Immediate(_)) => 0xA2,
        (LDX, AM::ZeroPage(_)) => 0xA6,
        (LDX, AM::ZeroPageY(_)) => 0xB6,
        (LDX, AM::Absolute(_)) => 0xAE,
        (LDX, AM::AbsoluteY(_)) => 0xBE,

        // LDY
        (LDY, AM::Immediate(_)) => 0xA0,
        (LDY, AM::ZeroPage(_)) => 0xA4,
        (LDY, AM::ZeroPageX(_)) => 0xB4,
        (LDY, AM::Absolute(_)) => 0xAC,
        (LDY, AM::AbsoluteX(_)) => 0xBC,

        // STA
        (STA, AM::ZeroPage(_)) => 0x85,
        (STA, AM::ZeroPageX(_)) => 0x95,
        (STA, AM::Absolute(_)) => 0x8D,
        (STA, AM::AbsoluteX(_)) => 0x9D,
        (STA, AM::AbsoluteY(_)) => 0x99,
        (STA, AM::IndirectX(_)) => 0x81,
        (STA, AM::IndirectY(_)) => 0x91,

        // STX
        (STX, AM::ZeroPage(_)) => 0x86,
        (STX, AM::ZeroPageY(_)) => 0x96,
        (STX, AM::Absolute(_)) => 0x8E,

        // STY
        (STY, AM::ZeroPage(_)) => 0x84,
        (STY, AM::ZeroPageX(_)) => 0x94,
        (STY, AM::Absolute(_)) => 0x8C,

        // ADC
        (ADC, AM::Immediate(_)) => 0x69,
        (ADC, AM::ZeroPage(_)) => 0x65,
        (ADC, AM::ZeroPageX(_)) => 0x75,
        (ADC, AM::Absolute(_)) => 0x6D,
        (ADC, AM::AbsoluteX(_)) => 0x7D,
        (ADC, AM::AbsoluteY(_)) => 0x79,
        (ADC, AM::IndirectX(_)) => 0x61,
        (ADC, AM::IndirectY(_)) => 0x71,

        // SBC
        (SBC, AM::Immediate(_)) => 0xE9,
        (SBC, AM::ZeroPage(_)) => 0xE5,
        (SBC, AM::ZeroPageX(_)) => 0xF5,
        (SBC, AM::Absolute(_)) => 0xED,
        (SBC, AM::AbsoluteX(_)) => 0xFD,
        (SBC, AM::AbsoluteY(_)) => 0xF9,
        (SBC, AM::IndirectX(_)) => 0xE1,
        (SBC, AM::IndirectY(_)) => 0xF1,

        // AND
        (AND, AM::Immediate(_)) => 0x29,
        (AND, AM::ZeroPage(_)) => 0x25,
        (AND, AM::ZeroPageX(_)) => 0x35,
        (AND, AM::Absolute(_)) => 0x2D,
        (AND, AM::AbsoluteX(_)) => 0x3D,
        (AND, AM::AbsoluteY(_)) => 0x39,
        (AND, AM::IndirectX(_)) => 0x21,
        (AND, AM::IndirectY(_)) => 0x31,

        // ORA
        (ORA, AM::Immediate(_)) => 0x09,
        (ORA, AM::ZeroPage(_)) => 0x05,
        (ORA, AM::ZeroPageX(_)) => 0x15,
        (ORA, AM::Absolute(_)) => 0x0D,
        (ORA, AM::AbsoluteX(_)) => 0x1D,
        (ORA, AM::AbsoluteY(_)) => 0x19,
        (ORA, AM::IndirectX(_)) => 0x01,
        (ORA, AM::IndirectY(_)) => 0x11,

        // EOR
        (EOR, AM::Immediate(_)) => 0x49,
        (EOR, AM::ZeroPage(_)) => 0x45,
        (EOR, AM::ZeroPageX(_)) => 0x55,
        (EOR, AM::Absolute(_)) => 0x4D,
        (EOR, AM::AbsoluteX(_)) => 0x5D,
        (EOR, AM::AbsoluteY(_)) => 0x59,
        (EOR, AM::IndirectX(_)) => 0x41,
        (EOR, AM::IndirectY(_)) => 0x51,

        // ASL
        (ASL, AM::Accumulator) => 0x0A,
        (ASL, AM::ZeroPage(_)) => 0x06,
        (ASL, AM::ZeroPageX(_)) => 0x16,
        (ASL, AM::Absolute(_)) => 0x0E,
        (ASL, AM::AbsoluteX(_)) => 0x1E,

        // LSR
        (LSR, AM::Accumulator) => 0x4A,
        (LSR, AM::ZeroPage(_)) => 0x46,
        (LSR, AM::ZeroPageX(_)) => 0x56,
        (LSR, AM::Absolute(_)) => 0x4E,
        (LSR, AM::AbsoluteX(_)) => 0x5E,

        // ROL
        (ROL, AM::Accumulator) => 0x2A,
        (ROL, AM::ZeroPage(_)) => 0x26,
        (ROL, AM::ZeroPageX(_)) => 0x36,
        (ROL, AM::Absolute(_)) => 0x2E,
        (ROL, AM::AbsoluteX(_)) => 0x3E,

        // ROR
        (ROR, AM::Accumulator) => 0x6A,
        (ROR, AM::ZeroPage(_)) => 0x66,
        (ROR, AM::ZeroPageX(_)) => 0x76,
        (ROR, AM::Absolute(_)) => 0x6E,
        (ROR, AM::AbsoluteX(_)) => 0x7E,

        // INC
        (INC, AM::ZeroPage(_)) => 0xE6,
        (INC, AM::ZeroPageX(_)) => 0xF6,
        (INC, AM::Absolute(_)) => 0xEE,
        (INC, AM::AbsoluteX(_)) => 0xFE,

        // DEC
        (DEC, AM::ZeroPage(_)) => 0xC6,
        (DEC, AM::ZeroPageX(_)) => 0xD6,
        (DEC, AM::Absolute(_)) => 0xCE,
        (DEC, AM::AbsoluteX(_)) => 0xDE,

        // INX, INY, DEX, DEY
        (INX, AM::Implied) => 0xE8,
        (INY, AM::Implied) => 0xC8,
        (DEX, AM::Implied) => 0xCA,
        (DEY, AM::Implied) => 0x88,

        // CMP
        (CMP, AM::Immediate(_)) => 0xC9,
        (CMP, AM::ZeroPage(_)) => 0xC5,
        (CMP, AM::ZeroPageX(_)) => 0xD5,
        (CMP, AM::Absolute(_)) => 0xCD,
        (CMP, AM::AbsoluteX(_)) => 0xDD,
        (CMP, AM::AbsoluteY(_)) => 0xD9,
        (CMP, AM::IndirectX(_)) => 0xC1,
        (CMP, AM::IndirectY(_)) => 0xD1,

        // CPX
        (CPX, AM::Immediate(_)) => 0xE0,
        (CPX, AM::ZeroPage(_)) => 0xE4,
        (CPX, AM::Absolute(_)) => 0xEC,

        // CPY
        (CPY, AM::Immediate(_)) => 0xC0,
        (CPY, AM::ZeroPage(_)) => 0xC4,
        (CPY, AM::Absolute(_)) => 0xCC,

        // BIT
        (BIT, AM::ZeroPage(_)) => 0x24,
        (BIT, AM::Absolute(_)) => 0x2C,

        // JMP
        (JMP, AM::Absolute(_)) => 0x4C,
        (JMP, AM::Indirect(_)) => 0x6C,

        // JSR
        (JSR, AM::Absolute(_)) => 0x20,

        // RTS, RTI
        (RTS, AM::Implied) => 0x60,
        (RTI, AM::Implied) => 0x40,

        // Branches (all use relative addressing)
        (BEQ, AM::Relative(_)) => 0xF0,
        (BNE, AM::Relative(_)) => 0xD0,
        (BCC, AM::Relative(_)) => 0x90,
        (BCS, AM::Relative(_)) => 0xB0,
        (BMI, AM::Relative(_)) => 0x30,
        (BPL, AM::Relative(_)) => 0x10,
        (BVC, AM::Relative(_)) => 0x50,
        (BVS, AM::Relative(_)) => 0x70,

        // Flag instructions (all implied)
        (CLC, AM::Implied) => 0x18,
        (SEC, AM::Implied) => 0x38,
        (CLI, AM::Implied) => 0x58,
        (SEI, AM::Implied) => 0x78,
        (CLV, AM::Implied) => 0xB8,
        (CLD, AM::Implied) => 0xD8,
        (SED, AM::Implied) => 0xF8,

        // Stack
        (PHA, AM::Implied) => 0x48,
        (PLA, AM::Implied) => 0x68,
        (PHP, AM::Implied) => 0x08,
        (PLP, AM::Implied) => 0x28,

        // Transfer
        (TAX, AM::Implied) => 0xAA,
        (TAY, AM::Implied) => 0xA8,
        (TXA, AM::Implied) => 0x8A,
        (TYA, AM::Implied) => 0x98,
        (TSX, AM::Implied) => 0xBA,
        (TXS, AM::Implied) => 0x9A,

        // NOP, BRK
        (NOP, AM::Implied) => 0xEA,
        (BRK, AM::Implied) => 0x00,

        _ => return None,
    };
    Some(result)
}
