//! Minimal 6502 assembly parser used by `asm { ... }` inline blocks.
//!
//! Supports the addressing modes we actually emit in codegen:
//!   - Implied / Accumulator: `CLC`, `LSR A`
//!   - Immediate: `LDA #$10`, `LDA #42`, `LDA #%00001111`
//!   - Zero page (+ X/Y): `STA $02`, `LDA $10,X`, `LDX $20,Y`
//!   - Absolute (+ X/Y): `STA $2000`, `LDA $0200,X`, `LDA $0100,Y`
//!   - Indirect: `JMP ($FFFC)`
//!   - Indirect (X/Y): `LDA ($10,X)`, `STA ($10),Y`
//!   - Labels: `foo:` on a line by itself, `JMP foo`, `BNE loop`
//!
//! This is not a full 6502 assembler — it only accepts the subset
//! needed by hand-written inline blocks. Unknown mnemonics, unsupported
//! addressing modes, or syntax errors return a `String` message.

use super::{AddressingMode, Instruction, Opcode};

/// Parse a block of inline assembly text into a list of `Instruction`s.
///
/// Each line is either:
///   - blank / a `; comment`
///   - a label `name:`
///   - a mnemonic with an optional operand
///
/// On error, returns the first problem with a line number.
pub fn parse_inline(body: &str) -> Result<Vec<Instruction>, String> {
    let mut out = Vec::new();
    for (lineno, raw) in body.lines().enumerate() {
        let line = strip_comment(raw).trim();
        if line.is_empty() {
            continue;
        }
        // Label: `name:`
        if let Some(name) = line.strip_suffix(':') {
            let name = name.trim();
            if name.is_empty() || !is_valid_ident(name) {
                return Err(format!("line {}: invalid label `{line}`", lineno + 1));
            }
            out.push(Instruction::new(
                Opcode::NOP,
                AddressingMode::Label(name.to_string()),
            ));
            continue;
        }
        let (mnemonic, rest) = split_mnemonic(line);
        let opcode = parse_opcode(mnemonic)
            .ok_or_else(|| format!("line {}: unknown mnemonic `{mnemonic}`", lineno + 1))?;
        let mode =
            parse_operand(opcode, rest.trim()).map_err(|e| format!("line {}: {e}", lineno + 1))?;
        out.push(Instruction::new(opcode, mode));
    }
    Ok(out)
}

fn strip_comment(line: &str) -> &str {
    match line.find(';') {
        Some(i) => &line[..i],
        None => line,
    }
}

fn split_mnemonic(line: &str) -> (&str, &str) {
    match line.find(|c: char| c.is_whitespace()) {
        Some(i) => (&line[..i], &line[i..]),
        None => (line, ""),
    }
}

fn is_valid_ident(s: &str) -> bool {
    s.chars()
        .next()
        .is_some_and(|c| c == '_' || c.is_ascii_alphabetic())
        && s.chars().all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn parse_opcode(mnemonic: &str) -> Option<Opcode> {
    let m = mnemonic.to_ascii_uppercase();
    Some(match m.as_str() {
        "LDA" => Opcode::LDA,
        "LDX" => Opcode::LDX,
        "LDY" => Opcode::LDY,
        "STA" => Opcode::STA,
        "STX" => Opcode::STX,
        "STY" => Opcode::STY,
        "ADC" => Opcode::ADC,
        "SBC" => Opcode::SBC,
        "AND" => Opcode::AND,
        "ORA" => Opcode::ORA,
        "EOR" => Opcode::EOR,
        "ASL" => Opcode::ASL,
        "LSR" => Opcode::LSR,
        "ROL" => Opcode::ROL,
        "ROR" => Opcode::ROR,
        "INC" => Opcode::INC,
        "DEC" => Opcode::DEC,
        "INX" => Opcode::INX,
        "INY" => Opcode::INY,
        "DEX" => Opcode::DEX,
        "DEY" => Opcode::DEY,
        "CMP" => Opcode::CMP,
        "CPX" => Opcode::CPX,
        "CPY" => Opcode::CPY,
        "BIT" => Opcode::BIT,
        "JMP" => Opcode::JMP,
        "JSR" => Opcode::JSR,
        "RTS" => Opcode::RTS,
        "RTI" => Opcode::RTI,
        "BEQ" => Opcode::BEQ,
        "BNE" => Opcode::BNE,
        "BCC" => Opcode::BCC,
        "BCS" => Opcode::BCS,
        "BMI" => Opcode::BMI,
        "BPL" => Opcode::BPL,
        "BVC" => Opcode::BVC,
        "BVS" => Opcode::BVS,
        "CLC" => Opcode::CLC,
        "SEC" => Opcode::SEC,
        "CLI" => Opcode::CLI,
        "SEI" => Opcode::SEI,
        "CLV" => Opcode::CLV,
        "CLD" => Opcode::CLD,
        "SED" => Opcode::SED,
        "PHA" => Opcode::PHA,
        "PLA" => Opcode::PLA,
        "PHP" => Opcode::PHP,
        "PLP" => Opcode::PLP,
        "TAX" => Opcode::TAX,
        "TAY" => Opcode::TAY,
        "TXA" => Opcode::TXA,
        "TYA" => Opcode::TYA,
        "TSX" => Opcode::TSX,
        "TXS" => Opcode::TXS,
        "NOP" => Opcode::NOP,
        "BRK" => Opcode::BRK,
        _ => return None,
    })
}

fn parse_operand(opcode: Opcode, operand: &str) -> Result<AddressingMode, String> {
    // No operand → implied (or accumulator for some shifts)
    if operand.is_empty() {
        return Ok(AddressingMode::Implied);
    }
    // Explicit accumulator (e.g. `LSR A`)
    if operand.eq_ignore_ascii_case("A") {
        return Ok(AddressingMode::Accumulator);
    }
    // Immediate: `#...`
    if let Some(rest) = operand.strip_prefix('#') {
        let v = parse_u8(rest.trim())?;
        return Ok(AddressingMode::Immediate(v));
    }
    // Indirect: `(addr)`, `(addr,X)`, `(addr),Y`
    if operand.starts_with('(') {
        // `(addr),Y` — outer ,Y after the closing paren
        if let Some(inner) = operand
            .strip_suffix(",Y")
            .or_else(|| operand.strip_suffix(",y"))
        {
            let inside = inner
                .strip_prefix('(')
                .and_then(|s| s.strip_suffix(')'))
                .ok_or_else(|| format!("malformed indirect operand `{operand}`"))?;
            let addr = parse_u8(inside.trim())?;
            return Ok(AddressingMode::IndirectY(addr));
        }
        // `(addr,X)` or `(addr)` — both end with `)`
        if let Some(rest) = operand.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
            if let Some(inside) = rest.strip_suffix(",X").or_else(|| rest.strip_suffix(",x")) {
                let addr = parse_u8(inside.trim())?;
                return Ok(AddressingMode::IndirectX(addr));
            }
            let addr = parse_u16(rest.trim())?;
            return Ok(AddressingMode::Indirect(addr));
        }
        return Err(format!("malformed indirect operand `{operand}`"));
    }
    // `addr,X` / `addr,Y`
    if let Some((base, reg)) = split_index(operand) {
        let is_zp = looks_like_zero_page(base);
        let (abs_mode, zp_mode) = match reg {
            'X' | 'x' => (
                AddressingMode::AbsoluteX as fn(u16) -> AddressingMode,
                AddressingMode::ZeroPageX as fn(u8) -> AddressingMode,
            ),
            'Y' | 'y' => (
                AddressingMode::AbsoluteY as fn(u16) -> AddressingMode,
                AddressingMode::ZeroPageY as fn(u8) -> AddressingMode,
            ),
            _ => return Err(format!("unknown index register `{reg}`")),
        };
        if is_zp {
            let v = parse_u8(base)?;
            return Ok(zp_mode(v));
        }
        let v = parse_u16(base)?;
        return Ok(abs_mode(v));
    }
    // Branch instructions take a label by name.
    if is_branch(opcode) && is_valid_ident(operand) {
        return Ok(AddressingMode::LabelRelative(operand.to_string()));
    }
    // Plain label: JMP foo, JSR foo
    if matches!(opcode, Opcode::JMP | Opcode::JSR) && is_valid_ident(operand) {
        return Ok(AddressingMode::Label(operand.to_string()));
    }
    // Plain address: ZeroPage if it fits, else Absolute
    if looks_like_zero_page(operand) {
        let v = parse_u8(operand)?;
        return Ok(AddressingMode::ZeroPage(v));
    }
    let v = parse_u16(operand)?;
    Ok(AddressingMode::Absolute(v))
}

fn split_index(operand: &str) -> Option<(&str, char)> {
    let bytes = operand.as_bytes();
    if bytes.len() >= 2 && bytes[bytes.len() - 2] == b',' {
        let reg = bytes[bytes.len() - 1] as char;
        if matches!(reg, 'X' | 'x' | 'Y' | 'y') {
            return Some((operand[..operand.len() - 2].trim_end(), reg));
        }
    }
    None
}

/// True if the operand is a numeric literal that fits in 8 bits.
fn looks_like_zero_page(operand: &str) -> bool {
    parse_u16(operand).is_ok_and(|v| v <= 0xFF) && parse_u8(operand).is_ok()
}

fn parse_u8(s: &str) -> Result<u8, String> {
    let v = parse_u16(s)?;
    u8::try_from(v).map_err(|_| format!("value {v} out of u8 range"))
}

fn parse_u16(s: &str) -> Result<u16, String> {
    let s = s.trim();
    let (negative, s) = if let Some(rest) = s.strip_prefix('-') {
        (true, rest)
    } else {
        (false, s)
    };
    let v: u16 = if let Some(hex) = s.strip_prefix('$') {
        u16::from_str_radix(hex, 16).map_err(|e| format!("bad hex `{s}`: {e}"))?
    } else if let Some(bin) = s.strip_prefix('%') {
        u16::from_str_radix(bin, 2).map_err(|e| format!("bad binary `{s}`: {e}"))?
    } else {
        s.parse().map_err(|e| format!("bad number `{s}`: {e}"))?
    };
    Ok(if negative { v.wrapping_neg() } else { v })
}

fn is_branch(opcode: Opcode) -> bool {
    matches!(
        opcode,
        Opcode::BEQ
            | Opcode::BNE
            | Opcode::BCC
            | Opcode::BCS
            | Opcode::BMI
            | Opcode::BPL
            | Opcode::BVC
            | Opcode::BVS
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_lda_immediate_hex() {
        let insts = parse_inline("LDA #$10").unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0].opcode, Opcode::LDA);
        assert_eq!(insts[0].mode, AddressingMode::Immediate(0x10));
    }

    #[test]
    fn parse_lda_immediate_decimal() {
        let insts = parse_inline("LDA #42").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::Immediate(42));
    }

    #[test]
    fn parse_sta_zero_page() {
        let insts = parse_inline("STA $10").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::ZeroPage(0x10));
    }

    #[test]
    fn parse_sta_absolute() {
        let insts = parse_inline("STA $2007").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::Absolute(0x2007));
    }

    #[test]
    fn parse_lda_absolute_x() {
        let insts = parse_inline("LDA $2000,X").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::AbsoluteX(0x2000));
    }

    #[test]
    fn parse_lda_zero_page_x() {
        let insts = parse_inline("LDA $10,X").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::ZeroPageX(0x10));
    }

    #[test]
    fn parse_lda_indirect_y() {
        let insts = parse_inline("LDA ($10),Y").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::IndirectY(0x10));
    }

    #[test]
    fn parse_jmp_indirect() {
        let insts = parse_inline("JMP ($FFFC)").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::Indirect(0xFFFC));
    }

    #[test]
    fn parse_implied() {
        let insts = parse_inline("CLC").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::Implied);
    }

    #[test]
    fn parse_accumulator() {
        let insts = parse_inline("LSR A").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::Accumulator);
    }

    #[test]
    fn parse_label_and_branch() {
        let insts = parse_inline(
            r"
            LDA #0
        loop:
            INC $10
            BNE loop
            RTS
        ",
        )
        .unwrap();
        // LDA, label, INC, BNE, RTS
        assert_eq!(insts.len(), 5);
        assert_eq!(insts[1].mode, AddressingMode::Label("loop".into()));
        assert_eq!(insts[3].mode, AddressingMode::LabelRelative("loop".into()));
    }

    #[test]
    fn parse_jmp_label() {
        let insts = parse_inline("JMP main").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::Label("main".into()));
    }

    #[test]
    fn parse_comments_and_blanks() {
        let insts = parse_inline(
            r"
            ; this is a comment
            LDA #$00  ; inline comment
        ",
        )
        .unwrap();
        assert_eq!(insts.len(), 1);
    }

    #[test]
    fn parse_unknown_mnemonic_errors() {
        let err = parse_inline("WTF $10").unwrap_err();
        assert!(err.contains("unknown mnemonic"));
    }

    #[test]
    fn parse_binary_immediate() {
        let insts = parse_inline("LDA #%00001111").unwrap();
        assert_eq!(insts[0].mode, AddressingMode::Immediate(0x0F));
    }
}
