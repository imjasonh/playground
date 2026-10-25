//! Peephole optimizations over the 6502 instruction stream.
//!
//! Runs after codegen but before assembly, so we can rewrite
//! `Instruction`s directly. Kept conservative to avoid breaking the
//! IR codegen's zero-page slot assumptions.

use crate::asm::{AddressingMode, Instruction, Opcode};

/// Run all peephole passes until fixed point.
pub fn optimize(instructions: &mut Vec<Instruction>) {
    loop {
        let before_len = instructions.len();
        let before = snapshot(instructions);
        copy_propagate_temps(instructions);
        remove_dead_loads(instructions);
        remove_sta_then_lda(instructions);
        remove_lda_then_sta_same(instructions);
        remove_dead_temp_stores(instructions);
        remove_redundant_loads(instructions);
        fold_branch_over_jmp(instructions);
        remove_jmp_to_next_label(instructions);
        fold_inc_dec(instructions);
        // Stop when no pass removed an instruction *and* the stream
        // is unchanged. Copy propagation doesn't shrink the stream —
        // it rewrites operands — so we need the content check too.
        if instructions.len() == before_len && !changed(&before, instructions) {
            break;
        }
    }
}

/// Fold `LDA addr; CLC; ADC #1; STA addr` into `INC addr`, and
/// `LDA addr; SEC; SBC #1; STA addr` into `DEC addr`. Both are
/// shorter (2 bytes vs 7) and faster (5 cycles vs 10) than the
/// ADC/SBC variants.
///
/// Safety: INC/DEC leave the carry flag alone, whereas the ADC
/// version clears it via CLC first and then consumes+produces a
/// new carry. The pattern we fold explicitly uses `CLC; ADC #1`
/// (so the incoming carry is discarded) and the STA commits the
/// result without reading flags, so anyone downstream relying on
/// the Z/N flags still gets the right flags from the INC/DEC —
/// both ops update N and Z from the new value just like ADC/SBC
/// would. Any downstream code reading the carry flag from the
/// original ADC/SBC would be depending on +1/-1 wrap arithmetic,
/// which the folded form can't preserve; we conservatively
/// require the pattern to be followed by an instruction that
/// isn't a carry-reading branch.
fn fold_inc_dec(instructions: &mut Vec<Instruction>) {
    let mut out = Vec::with_capacity(instructions.len());
    let mut idx = 0;
    while idx < instructions.len() {
        if idx + 3 < instructions.len() {
            let lda = &instructions[idx];
            let carry_op = &instructions[idx + 1];
            let adc_or_sbc = &instructions[idx + 2];
            let sta = &instructions[idx + 3];
            // Must start with `LDA <addr>`.
            let lda_addr = match (lda.opcode, &lda.mode) {
                (Opcode::LDA, AddressingMode::ZeroPage(addr)) => {
                    Some(AddressingMode::ZeroPage(*addr))
                }
                (Opcode::LDA, AddressingMode::Absolute(addr)) => {
                    Some(AddressingMode::Absolute(*addr))
                }
                _ => None,
            };
            // STA of the same address.
            let sta_matches = sta.opcode == Opcode::STA && Some(sta.mode.clone()) == lda_addr;
            let is_clc_adc_1 = carry_op.opcode == Opcode::CLC
                && adc_or_sbc.opcode == Opcode::ADC
                && adc_or_sbc.mode == AddressingMode::Immediate(1);
            let is_sec_sbc_1 = carry_op.opcode == Opcode::SEC
                && adc_or_sbc.opcode == Opcode::SBC
                && adc_or_sbc.mode == AddressingMode::Immediate(1);
            // Only fold if the next instruction after the STA
            // doesn't rely on the ADC's carry output. A BCC/BCS
            // right after the pattern would break; anything else
            // (including "no next instruction") is safe.
            let next_is_carry_branch = instructions
                .get(idx + 4)
                .is_some_and(|n| matches!(n.opcode, Opcode::BCC | Opcode::BCS));
            if let Some(addr) = lda_addr {
                if sta_matches && !next_is_carry_branch {
                    if is_clc_adc_1 {
                        out.push(Instruction::new(Opcode::INC, addr));
                        idx += 4;
                        continue;
                    }
                    if is_sec_sbc_1 {
                        out.push(Instruction::new(Opcode::DEC, addr));
                        idx += 4;
                        continue;
                    }
                }
            }
        }
        out.push(instructions[idx].clone());
        idx += 1;
    }
    *instructions = out;
}

/// Fold `Bxx label1; JMP label2; label1:` into `Byy label2`, where
/// `Byy` is the inversion of `Bxx`. This is emitted by the IR codegen
/// for every `if` statement without an else clause — the `BNE taken;
/// JMP fallthrough; taken: … fallthrough:` pattern collapses to
/// `BEQ fallthrough; …`. Saves 2 instructions per if.
///
/// The fold is only safe when the JMP target is close enough to fit
/// in a branch's signed 8-bit offset (-128..+127 bytes). We use a
/// conservative estimate: scan forward up to 60 instructions (~120
/// bytes) looking for the target label. If it's not found in that
/// window, leave the JMP alone.
fn fold_branch_over_jmp(instructions: &mut Vec<Instruction>) {
    const MAX_LOOKAHEAD: usize = 60;
    let mut out = Vec::with_capacity(instructions.len());
    let mut i = 0;
    while i < instructions.len() {
        if i + 2 < instructions.len() {
            let br = &instructions[i];
            let jmp = &instructions[i + 1];
            let lbl = &instructions[i + 2];
            let inverted = invert_branch(br.opcode);
            let is_branch = inverted.is_some();
            let is_jmp = jmp.opcode == Opcode::JMP;
            let is_label =
                lbl.opcode == Opcode::NOP && matches!(lbl.mode, AddressingMode::Label(_));
            if is_branch && is_jmp && is_label {
                if let (AddressingMode::LabelRelative(br_tgt), AddressingMode::Label(lbl_name)) =
                    (&br.mode, &lbl.mode)
                {
                    if br_tgt == lbl_name {
                        let jmp_tgt = match &jmp.mode {
                            AddressingMode::Label(n) => n.clone(),
                            _ => {
                                out.push(instructions[i].clone());
                                i += 1;
                                continue;
                            }
                        };
                        // Confirm the target is reachable within a
                        // short branch. Scan forward looking for the
                        // label definition.
                        let mut found = false;
                        for (offset, ahead) in instructions
                            .iter()
                            .enumerate()
                            .skip(i + 1)
                            .take(MAX_LOOKAHEAD)
                        {
                            if ahead.opcode == Opcode::NOP {
                                if let AddressingMode::Label(name) = &ahead.mode {
                                    if name == &jmp_tgt {
                                        found = true;
                                        break;
                                    }
                                }
                            }
                            // Stop scan if we walk off the end.
                            let _ = offset;
                        }
                        if !found {
                            out.push(instructions[i].clone());
                            i += 1;
                            continue;
                        }
                        out.push(Instruction::new(
                            inverted.unwrap(),
                            AddressingMode::LabelRelative(jmp_tgt),
                        ));
                        // Preserve the label definition.
                        out.push(lbl.clone());
                        i += 3;
                        continue;
                    }
                }
            }
        }
        out.push(instructions[i].clone());
        i += 1;
    }
    *instructions = out;
}

/// Remove `JMP label` when the very next instruction is the label
/// definition itself. This is a dead jump left behind by IR codegen
/// patterns like `if-else` and `while` that unconditionally jump to
/// a label that's already directly following.
fn remove_jmp_to_next_label(instructions: &mut Vec<Instruction>) {
    let mut out = Vec::with_capacity(instructions.len());
    let mut i = 0;
    while i < instructions.len() {
        if i + 1 < instructions.len() {
            let jmp = &instructions[i];
            let next = &instructions[i + 1];
            if jmp.opcode == Opcode::JMP {
                if let (AddressingMode::Label(tgt), AddressingMode::Label(name)) =
                    (&jmp.mode, &next.mode)
                {
                    if next.opcode == Opcode::NOP && tgt == name {
                        // Drop the JMP — fall through to the label.
                        i += 1;
                        continue;
                    }
                }
            }
        }
        out.push(instructions[i].clone());
        i += 1;
    }
    *instructions = out;
}

/// Return the logical inverse of a branch opcode, or None if the
/// opcode isn't a conditional branch.
fn invert_branch(op: Opcode) -> Option<Opcode> {
    Some(match op {
        Opcode::BEQ => Opcode::BNE,
        Opcode::BNE => Opcode::BEQ,
        Opcode::BCC => Opcode::BCS,
        Opcode::BCS => Opcode::BCC,
        Opcode::BMI => Opcode::BPL,
        Opcode::BPL => Opcode::BMI,
        Opcode::BVC => Opcode::BVS,
        Opcode::BVS => Opcode::BVC,
        _ => return None,
    })
}

/// Remove `LDA …` instructions whose value is never read — the next
/// instruction overwrites A without using the current value.
///
/// The heuristic looks forward, stepping over instructions that
/// don't touch A (memory `INC`/`DEC`/`STX`/`STY`, labels). If the
/// first instruction that *does* touch A overwrites it without
/// reading it (`LDA`, `PLA`, `TXA`, `TYA`), the preceding `LDA` is
/// dead. Shifts and arithmetic ops read A, so they end the scan
/// without marking dead.
///
/// One unconditional `JMP` is followed: we look up its target label
/// and resume scanning from the first instruction after it. This
/// catches `LDA #imm; DEC zp; JMP loop_cond; loop_cond: LDA loop_var`
/// patterns that the IR codegen leaves behind for `i -= 1`-style
/// loops, where the `LDA #1` was the constant operand of a `Sub`
/// the optimizer already strength-reduced into the `DEC`. Conditional
/// branches and `JSR` still end the scan — JSR could land on a
/// runtime helper that reads A, and a branch's not-taken path is
/// unconstrained.
fn remove_dead_loads(instructions: &mut Vec<Instruction>) {
    let mut keep = vec![true; instructions.len()];
    for i in 0..instructions.len() {
        let inst = &instructions[i];
        if inst.opcode != Opcode::LDA {
            continue;
        }
        let mut j = i + 1;
        let mut dead = false;
        let mut followed_jmp = false;
        while j < instructions.len() {
            let next = &instructions[j];
            // Labels are passive markers.
            if next.opcode == Opcode::NOP && matches!(next.mode, AddressingMode::Label(_)) {
                j += 1;
                continue;
            }
            // Step past every op that neither reads nor writes A,
            // so a redundant LDA before the op gets dropped by its
            // successor's overwrite. Stepping past LDX/LDY is the
            // most impactful win — it kills one LDA per `draw`
            // statement, because the IR codegen emits
            // `LDA #imm / LDY oam_cursor / LDA #imm / STA $0200,Y`
            // and copy propagation leaves the two `LDA #imm`s
            // looking identical around the LDY. INX/INY/DEX/DEY
            // and the flag ops (CLC/SEC/CLI/SEI/CLD/SED/CLV) are
            // cheap additions — they don't touch A either, so the
            // same scan picks them up. INC/DEC in memory mode
            // (matched explicitly below) likewise leave A alone.
            let skippable = matches!(
                next.opcode,
                Opcode::INC
                    | Opcode::DEC
                    | Opcode::STX
                    | Opcode::STY
                    | Opcode::LDX
                    | Opcode::LDY
                    | Opcode::INX
                    | Opcode::INY
                    | Opcode::DEX
                    | Opcode::DEY
                    | Opcode::CLC
                    | Opcode::SEC
                    | Opcode::CLI
                    | Opcode::SEI
                    | Opcode::CLD
                    | Opcode::SED
                    | Opcode::CLV
            ) && !matches!(next.mode, AddressingMode::Accumulator);
            if skippable {
                j += 1;
                continue;
            }
            // Cross one unconditional `JMP <label>` by looking the
            // target up and resuming scan there. Refuse a second
            // JMP — the analysis is meant to catch a single
            // straight-line `loop_body → loop_cond` jump, not an
            // arbitrary chain.
            if !followed_jmp && next.opcode == Opcode::JMP {
                if let AddressingMode::Label(target) = &next.mode {
                    if let Some(target_idx) = instructions.iter().position(|ins| {
                        ins.opcode == Opcode::NOP
                            && matches!(&ins.mode, AddressingMode::Label(name) if name == target)
                    }) {
                        followed_jmp = true;
                        j = target_idx + 1;
                        continue;
                    }
                }
                break;
            }
            // Instructions that overwrite A without reading it.
            if matches!(
                next.opcode,
                Opcode::LDA | Opcode::PLA | Opcode::TXA | Opcode::TYA
            ) {
                dead = true;
            }
            // Any other instruction — might read A (STA, ADC,
            // SBC, AND, JSR …) or transfer control (Bxx, RTS) —
            // stop scanning.
            break;
        }
        if dead {
            keep[i] = false;
        }
    }
    let mut out = Vec::with_capacity(instructions.len());
    for (i, inst) in instructions.iter().enumerate() {
        if keep[i] {
            out.push(inst.clone());
        }
    }
    *instructions = out;
}

fn snapshot(instructions: &[Instruction]) -> Vec<(Opcode, AddressingMode)> {
    instructions
        .iter()
        .map(|i| (i.opcode, i.mode.clone()))
        .collect()
}

fn changed(before: &[(Opcode, AddressingMode)], after: &[Instruction]) -> bool {
    if before.len() != after.len() {
        return true;
    }
    before
        .iter()
        .zip(after.iter())
        .any(|((op, mode), inst)| *op != inst.opcode || *mode != inst.mode)
}

/// Copy propagation for IR temp slots.
///
/// After the IR codegen, each temp produced by an IR op is spilled
/// to a zero-page slot via `STA slot`. Any subsequent op that needs
/// the temp emits `LDA slot`. Copy propagation notes the *source*
/// of each temp store (e.g. "slot 128 was set from [slot 16]") and
/// rewrites subsequent loads of that slot to load from the source
/// directly. If the source is later written, the equivalence is
/// invalidated before we see the consuming load. Immediate values
/// are tracked the same way.
///
/// The rewrite doesn't remove anything — it just swaps the operand.
/// The other peephole passes then pick up the now-dead `STA slot`
/// and drop it.
fn copy_propagate_temps(instructions: &mut [Instruction]) {
    use std::collections::HashMap;

    // slot -> source of the most recent STA into that slot.
    let mut temp_source: HashMap<u8, Source> = HashMap::new();
    // Track what A currently holds so we can decide whether an STA
    // actually copies a known source into the slot.
    let mut a: Option<Source> = None;

    for inst in instructions.iter_mut() {
        if instruction_crosses_block(inst) {
            temp_source.clear();
            a = None;
            continue;
        }
        match (inst.opcode, inst.mode.clone()) {
            (Opcode::LDA, AddressingMode::Immediate(v)) => {
                a = Some(Source::Imm(v));
            }
            (Opcode::LDA, AddressingMode::ZeroPage(addr)) => {
                // If addr is a temp whose source is tracked, rewrite
                // the load to use the source directly.
                if is_temp_slot_addr(addr) {
                    if let Some(src) = temp_source.get(&addr).copied() {
                        inst.mode = source_to_mode(src);
                        a = Some(src);
                        continue;
                    }
                }
                a = Some(Source::Zp(addr));
            }
            (Opcode::LDA, AddressingMode::Absolute(addr)) => {
                a = Some(Source::Abs(addr));
            }
            // Arithmetic / logical ops that read a temp slot: rewrite
            // the operand to the temp's tracked source. Clobbers A.
            (
                Opcode::ADC | Opcode::SBC | Opcode::AND | Opcode::ORA | Opcode::EOR | Opcode::CMP,
                AddressingMode::ZeroPage(addr),
            ) if is_temp_slot_addr(addr) => {
                if let Some(src) = temp_source.get(&addr).copied() {
                    inst.mode = source_to_mode(src);
                }
                a = None;
            }
            (Opcode::STA, AddressingMode::ZeroPage(addr)) => {
                // If we're storing to a temp slot and we know the
                // source of the value in A, record the equivalence.
                if is_temp_slot_addr(addr) {
                    if let Some(src) = a {
                        temp_source.insert(addr, src);
                    } else {
                        temp_source.remove(&addr);
                    }
                } else {
                    // Storing to a non-temp ZP addr invalidates any
                    // temp that was tracking [addr] as its source.
                    temp_source.retain(|_, src| !matches!(*src, Source::Zp(a) if a == addr));
                }
            }
            (Opcode::STA, AddressingMode::Absolute(addr)) => {
                // Invalidate any temp tracking this absolute source.
                temp_source.retain(|_, src| !matches!(*src, Source::Abs(a) if a == addr));
            }
            // Any op that reads a non-ZP location or clobbers A: just
            // invalidate A; temps are unaffected.
            _ => {
                if modifies_a(inst.opcode) {
                    a = None;
                }
            }
        }
    }
}

fn source_to_mode(src: Source) -> AddressingMode {
    match src {
        Source::Imm(v) => AddressingMode::Immediate(v),
        Source::Zp(addr) => AddressingMode::ZeroPage(addr),
        Source::Abs(addr) => AddressingMode::Absolute(addr),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Source {
    Imm(u8),
    Zp(u8),
    Abs(u16),
}

fn is_temp_slot_addr(addr: u8) -> bool {
    addr >= 0x80
}

fn modifies_a(op: Opcode) -> bool {
    matches!(
        op,
        Opcode::LDA
            | Opcode::ADC
            | Opcode::SBC
            | Opcode::AND
            | Opcode::ORA
            | Opcode::EOR
            | Opcode::ASL
            | Opcode::LSR
            | Opcode::ROL
            | Opcode::ROR
            | Opcode::PLA
            | Opcode::TXA
            | Opcode::TYA
    )
}

/// Track what `A` holds through a linear run of instructions and
/// eliminate `LDA` that would reload a value A already has.
///
/// We track an equivalence class for A: at any point, A equals a
/// single `AValue` (immediate, ZP cell, or absolute cell). After a
/// `STA addr`, that address is added to the equivalence — a later
/// `LDA` from the same class is redundant.
///
/// Any instruction that may clobber A resets the tracker, as does
/// a control-flow instruction or label.
fn remove_redundant_loads(instructions: &mut Vec<Instruction>) {
    let mut keep = vec![true; instructions.len()];
    // Current equivalence class for A. All members hold the same
    // value as A right now.
    let mut eq: Vec<AValue> = Vec::new();

    for (i, inst) in instructions.iter().enumerate() {
        if instruction_crosses_block(inst) {
            eq.clear();
            continue;
        }
        match (inst.opcode, &inst.mode) {
            (Opcode::LDA, AddressingMode::Immediate(v)) => {
                if eq.contains(&AValue::Imm(*v)) {
                    keep[i] = false;
                    continue;
                }
                eq.clear();
                eq.push(AValue::Imm(*v));
            }
            (Opcode::LDA, AddressingMode::ZeroPage(addr)) => {
                if eq.contains(&AValue::Zp(*addr)) {
                    keep[i] = false;
                    continue;
                }
                eq.clear();
                eq.push(AValue::Zp(*addr));
            }
            (Opcode::LDA, AddressingMode::Absolute(addr)) => {
                if eq.contains(&AValue::Abs(*addr)) {
                    keep[i] = false;
                    continue;
                }
                eq.clear();
                eq.push(AValue::Abs(*addr));
            }
            // Indexed, indirect, and accumulator-mode LDAs clobber A
            // but the value they load isn't trackable here (the
            // effective address depends on a register or memory we
            // don't track), so we can't add it to `eq`. We MUST still
            // clear the tracker — otherwise a subsequent `LDA #v`
            // might look redundant against a stale entry from before
            // the indexed load, and get dropped. That's a miscompile,
            // not an optimization.
            (
                Opcode::LDA,
                AddressingMode::AbsoluteX(_)
                | AddressingMode::AbsoluteY(_)
                | AddressingMode::ZeroPageX(_)
                | AddressingMode::IndirectX(_)
                | AddressingMode::IndirectY(_),
            ) => {
                eq.clear();
            }
            (Opcode::STA, AddressingMode::ZeroPage(addr)) => {
                // A unchanged; address now holds A's value. Add the
                // address to the equivalence class.
                if eq.is_empty() {
                    // No prior knowledge — start fresh with this
                    // address.
                }
                eq.push(AValue::Zp(*addr));
            }
            (Opcode::STA, AddressingMode::Absolute(addr)) => {
                eq.push(AValue::Abs(*addr));
            }
            (Opcode::STA, _) => {
                // Other addressing modes: A unchanged.
            }
            // Ops that clobber A — clear tracker.
            (
                Opcode::ADC
                | Opcode::SBC
                | Opcode::AND
                | Opcode::ORA
                | Opcode::EOR
                | Opcode::ASL
                | Opcode::LSR
                | Opcode::ROL
                | Opcode::ROR
                | Opcode::LDX
                | Opcode::LDY
                | Opcode::PLA
                | Opcode::TXA
                | Opcode::TYA,
                _,
            ) => {
                eq.clear();
            }
            // Ops that write to an address we might be tracking:
            // invalidate any equivalence pointing at that cell,
            // because the stored value is no longer correct.
            (
                Opcode::STX | Opcode::STY | Opcode::INC | Opcode::DEC,
                AddressingMode::ZeroPage(addr),
            ) => {
                eq.retain(|v| !matches!(v, AValue::Zp(a) if *a == *addr));
            }
            (
                Opcode::STX | Opcode::STY | Opcode::INC | Opcode::DEC,
                AddressingMode::Absolute(addr),
            ) => {
                eq.retain(|v| !matches!(v, AValue::Abs(a) if *a == *addr));
            }
            _ => {}
        }
    }
    let mut out = Vec::with_capacity(instructions.len());
    for (i, inst) in instructions.iter().enumerate() {
        if keep[i] {
            out.push(inst.clone());
        }
    }
    *instructions = out;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AValue {
    Imm(u8),
    Zp(u8),
    Abs(u16),
}

/// Remove `STA temp_slot` instructions whose written value is never
/// read before the slot is overwritten or we cross a control-flow
/// boundary (label, branch, jump, call, return).
///
/// This targets the IR codegen's pattern where each op spills its
/// result to an IR temp slot even if the next op consumes it by
/// reading directly from that slot — but nothing further does. The
/// final store-to-user-variable covers the actual need; the intermediate
/// store-to-temp is dead.
fn remove_dead_temp_stores(instructions: &mut Vec<Instruction>) {
    // Walk forward. For each `STA slot` where slot is a temp, look
    // ahead through the rest of the current function (bounded by the
    // next `__ir_fn_` label or EOF). If no subsequent instruction
    // reads the slot before the function ends or the slot is
    // overwritten, the STA is dead.
    //
    // IR temp slots are assigned uniquely per IR op within a function
    // (the IR codegen resets `next_temp_slot` to 0 at each function
    // entry and never reuses slot numbers within a function), so it's
    // safe to scan past labels and branches within the same function.
    // Cross-function JSR can't read our temps because the callee also
    // starts its own temp numbering from $80 — if it stomps on our
    // slots, we can't have relied on them surviving the call anyway.
    let mut keep = vec![true; instructions.len()];
    for i in 0..instructions.len() {
        let inst = &instructions[i];
        if inst.opcode != Opcode::STA {
            continue;
        }
        let slot = match inst.mode {
            AddressingMode::ZeroPage(addr) if addr >= 0x80 => addr,
            _ => continue,
        };
        let mut dead = true;
        for next in instructions.iter().skip(i + 1) {
            if is_function_boundary(next) {
                break;
            }
            if reads_zero_page(next, slot) {
                dead = false;
                break;
            }
            if writes_zero_page(next, slot) {
                // Overwritten with no read in between — our STA is
                // dead. Stop scanning either way.
                break;
            }
        }
        if dead {
            keep[i] = false;
        }
    }
    let mut out = Vec::with_capacity(instructions.len());
    for (i, inst) in instructions.iter().enumerate() {
        if keep[i] {
            out.push(inst.clone());
        }
    }
    *instructions = out;
}

/// True if `inst` marks the start of a new function. IR codegen emits
/// function bodies with a `NOP Label("__ir_fn_…")` pseudo-instruction.
/// A JSR to a function also transfers control away, but since each
/// function starts its own temp slot allocation at $80 we don't rely
/// on slot contents surviving calls.
fn is_function_boundary(inst: &Instruction) -> bool {
    if inst.opcode == Opcode::NOP {
        if let AddressingMode::Label(name) = &inst.mode {
            return name.starts_with("__ir_fn_")
                || name.starts_with("__fn_")
                || name == "__reset"
                || name == "__nmi"
                || name == "__irq";
        }
    }
    matches!(inst.opcode, Opcode::RTS | Opcode::RTI)
}

/// True if the given instruction is a control-flow boundary — we can't
/// safely reason about liveness across it.
fn instruction_crosses_block(inst: &Instruction) -> bool {
    // Branches / jumps / calls / returns all count as boundaries
    // because they might transfer to code that reads the slot.
    if matches!(
        inst.opcode,
        Opcode::JMP
            | Opcode::JSR
            | Opcode::RTS
            | Opcode::RTI
            | Opcode::BEQ
            | Opcode::BNE
            | Opcode::BCC
            | Opcode::BCS
            | Opcode::BMI
            | Opcode::BPL
            | Opcode::BVC
            | Opcode::BVS
            | Opcode::BRK
    ) {
        return true;
    }
    // A label definition (NOP with `Label` operand) is also a boundary —
    // it's a potential jump target, and we can't see where jumps come
    // from without a full control-flow graph.
    matches!(inst.mode, AddressingMode::Label(_))
}

/// True if `inst` reads from the given zero-page address.
fn reads_zero_page(inst: &Instruction, addr: u8) -> bool {
    let targets_same = matches!(
        inst.mode,
        AddressingMode::ZeroPage(a) if a == addr
    );
    if !targets_same {
        return false;
    }
    // Reading instructions: LDA/LDX/LDY, arithmetic ops, comparisons,
    // BIT — anything that consumes the byte at the address.
    matches!(
        inst.opcode,
        Opcode::LDA
            | Opcode::LDX
            | Opcode::LDY
            | Opcode::ADC
            | Opcode::SBC
            | Opcode::AND
            | Opcode::ORA
            | Opcode::EOR
            | Opcode::CMP
            | Opcode::CPX
            | Opcode::CPY
            | Opcode::BIT
            | Opcode::ASL
            | Opcode::LSR
            | Opcode::ROL
            | Opcode::ROR
            | Opcode::INC
            | Opcode::DEC
    )
}

/// True if `inst` writes to the given zero-page address (overwriting
/// whatever was there). We treat read-modify-write ops as reads, not
/// writes — they preserve the "was read" bit for the original STA.
fn writes_zero_page(inst: &Instruction, addr: u8) -> bool {
    if !matches!(inst.mode, AddressingMode::ZeroPage(a) if a == addr) {
        return false;
    }
    matches!(inst.opcode, Opcode::STA | Opcode::STX | Opcode::STY)
}

/// Remove `LDA addr` immediately followed by `STA addr` (same addr).
/// The store is a no-op because the byte is already there.
fn remove_lda_then_sta_same(instructions: &mut Vec<Instruction>) {
    let mut out = Vec::with_capacity(instructions.len());
    let mut i = 0;
    while i < instructions.len() {
        if i + 1 < instructions.len() {
            let a = &instructions[i];
            let b = &instructions[i + 1];
            if a.opcode == Opcode::LDA && b.opcode == Opcode::STA && a.mode == b.mode {
                // Keep the LDA (in case the value in A is used later)
                // but drop the pointless STA.
                out.push(a.clone());
                i += 2;
                continue;
            }
        }
        out.push(instructions[i].clone());
        i += 1;
    }
    *instructions = out;
}

/// Remove `STA slot` immediately followed by `LDA slot` when both
/// refer to an IR temp slot. The LDA is redundant because A already
/// holds the value we just stored.
///
/// This targets the IR codegen's store-every-temp pattern: ops that
/// produce a value into `A` then immediately store it, and the next
/// op loads it back.
fn remove_sta_then_lda(instructions: &mut Vec<Instruction>) {
    let mut out = Vec::with_capacity(instructions.len());
    let mut i = 0;
    while i < instructions.len() {
        if i + 1 < instructions.len() {
            let a = &instructions[i];
            let b = &instructions[i + 1];
            if a.opcode == Opcode::STA
                && b.opcode == Opcode::LDA
                && a.mode == b.mode
                && is_temp_slot(&a.mode)
            {
                // Keep the STA (subsequent code may read the slot),
                // drop the LDA.
                out.push(a.clone());
                i += 2;
                continue;
            }
        }
        out.push(instructions[i].clone());
        i += 1;
    }
    *instructions = out;
}

/// True if the addressing mode targets an IR temp slot ($80-$FF).
/// We restrict peephole store/load elimination to temp slots so we
/// don't accidentally merge accesses to user variables in ZP (where
/// an intervening call or IRQ could have clobbered A).
fn is_temp_slot(mode: &AddressingMode) -> bool {
    matches!(mode, AddressingMode::ZeroPage(addr) if *addr >= 0x80)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::asm::AddressingMode as AM;
    use crate::asm::Opcode::*;

    #[test]
    fn removes_sta_then_lda_temp() {
        // `STA $80; LDA $80; CLC; RTS` — the STA is dead (the slot
        // is never read by anything reachable), and even if we did
        // keep the STA the LDA would be eliminated by A-tracking
        // since A already holds the value we just stored. Both get
        // stripped, leaving just CLC + RTS.
        let mut insts = vec![
            Instruction::new(STA, AM::ZeroPage(0x80)),
            Instruction::new(LDA, AM::ZeroPage(0x80)),
            Instruction::new(CLC, AM::Implied),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        assert_eq!(insts.len(), 2);
        assert_eq!(insts[0].opcode, CLC);
        assert_eq!(insts[1].opcode, RTS);
    }

    #[test]
    fn keeps_sta_when_temp_is_read_later() {
        // STA $80; LDA #5; ORA $80 — the ORA reads slot $80, so
        // the STA is live.
        let mut insts = vec![
            Instruction::new(STA, AM::ZeroPage(0x80)),
            Instruction::new(LDA, AM::Immediate(5)),
            Instruction::new(ORA, AM::ZeroPage(0x80)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        // STA must remain because the ORA reads it.
        assert!(
            insts
                .iter()
                .any(|i| i.opcode == STA && i.mode == AM::ZeroPage(0x80)),
            "STA to $80 should be preserved: {insts:?}"
        );
    }

    #[test]
    fn eliminates_sta_then_lda_via_a_tracking() {
        // Even for user variables, `STA $10; LDA $10` is redundant in
        // straight-line code: A still holds the value we just stored.
        // The A-value tracker handles this. (If a JSR or branch
        // intervenes, the tracker clears and the LDA is preserved.)
        let mut insts = vec![
            Instruction::new(STA, AM::ZeroPage(0x10)),
            Instruction::new(LDA, AM::ZeroPage(0x10)),
        ];
        optimize(&mut insts);
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0].opcode, STA);
    }

    #[test]
    fn preserves_lda_across_jsr() {
        // JSR clobbers A (callee can do anything), so the second LDA
        // must survive.
        let mut insts = vec![
            Instruction::new(STA, AM::ZeroPage(0x10)),
            Instruction::new(JSR, AM::Label("foo".into())),
            Instruction::new(LDA, AM::ZeroPage(0x10)),
        ];
        optimize(&mut insts);
        // STA, JSR, LDA — all preserved
        assert_eq!(insts.len(), 3);
    }

    #[test]
    fn eliminates_duplicate_immediate_loads_across_stores() {
        // LDA #5; STA $10; LDA #5 — the second LDA should be
        // eliminated because A still holds 5 after STA.
        let mut insts = vec![
            Instruction::new(LDA, AM::Immediate(5)),
            Instruction::new(STA, AM::ZeroPage(0x10)),
            Instruction::new(LDA, AM::Immediate(5)),
            Instruction::new(STA, AM::ZeroPage(0x11)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        // Expect: LDA #5, STA $10, STA $11, RTS
        let lda_count = insts.iter().filter(|i| i.opcode == LDA).count();
        assert_eq!(
            lda_count, 1,
            "expected one LDA (the second is redundant): {insts:?}"
        );
    }

    #[test]
    fn removes_lda_then_sta_same_address() {
        let mut insts = vec![
            Instruction::new(LDA, AM::ZeroPage(0x10)),
            Instruction::new(STA, AM::ZeroPage(0x10)),
            Instruction::new(CLC, AM::Implied),
        ];
        optimize(&mut insts);
        // LDA kept (value in A may be used), pointless STA removed
        assert_eq!(insts.len(), 2);
        assert_eq!(insts[0].opcode, LDA);
        assert_eq!(insts[1].opcode, CLC);
    }

    #[test]
    fn preserves_sta_when_slot_is_read() {
        let mut insts = vec![
            Instruction::new(STA, AM::ZeroPage(0x80)),
            Instruction::new(LDA, AM::ZeroPage(0x81)),
            Instruction::new(CMP, AM::ZeroPage(0x80)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        // STA $80 is live because CMP reads it.
        assert!(
            insts
                .iter()
                .any(|i| i.opcode == STA && i.mode == AM::ZeroPage(0x80)),
            "STA should be preserved when slot is later read: {insts:?}"
        );
    }

    #[test]
    fn copy_propagation_rewrites_temp_load_to_source() {
        // LDA $10; STA $80; LDA $80 should become LDA $10; (stores
        // trimmed by dead-store). End result: just a single LDA.
        let mut insts = vec![
            Instruction::new(LDA, AM::ZeroPage(0x10)),
            Instruction::new(STA, AM::ZeroPage(0x80)),
            Instruction::new(LDA, AM::ZeroPage(0x80)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        // After copy prop + dead store elim + A-tracking, the sequence
        // collapses to a single LDA + RTS.
        assert!(
            insts
                .iter()
                .any(|i| i.opcode == LDA && i.mode == AM::ZeroPage(0x10)),
            "should preserve original LDA: {insts:?}"
        );
    }

    #[test]
    fn copy_propagation_rewrites_arithmetic_operand() {
        // LDA #1; STA $80; LDA $10; CLC; ADC $80 — the ADC should be
        // rewritten to `ADC #1` because $80 is a temp tracked to Imm(1).
        let mut insts = vec![
            Instruction::new(LDA, AM::Immediate(1)),
            Instruction::new(STA, AM::ZeroPage(0x80)),
            Instruction::new(LDA, AM::ZeroPage(0x10)),
            Instruction::new(CLC, AM::Implied),
            Instruction::new(ADC, AM::ZeroPage(0x80)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        assert!(
            insts
                .iter()
                .any(|i| i.opcode == ADC && i.mode == AM::Immediate(1)),
            "ADC should be rewritten to immediate: {insts:?}"
        );
    }

    #[test]
    fn dead_load_elimination_drops_overwritten_lda() {
        // LDA $10; LDA #0 — the first LDA is dead because A is
        // overwritten before being used.
        let mut insts = vec![
            Instruction::new(LDA, AM::ZeroPage(0x10)),
            Instruction::new(LDA, AM::Immediate(0)),
            Instruction::new(STA, AM::ZeroPage(0x10)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        // First LDA dropped; result is LDA #0, STA $10, RTS
        let lda_count = insts.iter().filter(|i| i.opcode == LDA).count();
        assert_eq!(lda_count, 1, "expected one LDA, got: {insts:?}");
    }

    #[test]
    fn folds_branch_over_jmp_to_nearby_label() {
        // BNE taken; JMP fallthrough; taken:
        // becomes: BEQ fallthrough; taken:
        // (and taken: is harmless even without a corresponding JSR).
        let mut insts = vec![
            Instruction::new(LDA, AM::Immediate(0)),
            Instruction::new(BNE, AM::LabelRelative("taken".into())),
            Instruction::new(JMP, AM::Label("fallthrough".into())),
            Instruction::new(NOP, AM::Label("taken".into())),
            Instruction::new(NOP, AM::Implied),
            Instruction::new(NOP, AM::Label("fallthrough".into())),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        // The BNE should have been rewritten to BEQ fallthrough.
        let has_beq_fallthrough = insts
            .iter()
            .any(|i| i.opcode == BEQ && i.mode == AM::LabelRelative("fallthrough".into()));
        assert!(
            has_beq_fallthrough,
            "expected BEQ fallthrough after folding: {insts:?}"
        );
        // The JMP fallthrough should be gone.
        let has_jmp = insts
            .iter()
            .any(|i| i.opcode == JMP && i.mode == AM::Label("fallthrough".into()));
        assert!(!has_jmp, "JMP should be folded away: {insts:?}");
    }

    #[test]
    fn skips_branch_fold_for_distant_labels() {
        // Same pattern but the target label is too far away (beyond
        // the lookahead window). The fold should be skipped.
        let mut insts = vec![
            Instruction::new(LDA, AM::Immediate(0)),
            Instruction::new(BNE, AM::LabelRelative("taken".into())),
            Instruction::new(JMP, AM::Label("far_label".into())),
            Instruction::new(NOP, AM::Label("taken".into())),
        ];
        // Pad with 100 NOPs.
        for _ in 0..100 {
            insts.push(Instruction::new(NOP, AM::Implied));
        }
        insts.push(Instruction::new(NOP, AM::Label("far_label".into())));
        insts.push(Instruction::new(RTS, AM::Implied));
        optimize(&mut insts);
        // The BNE should NOT have been rewritten — far_label is too
        // far to reach with a short branch.
        let has_beq_far = insts
            .iter()
            .any(|i| i.opcode == BEQ && i.mode == AM::LabelRelative("far_label".into()));
        assert!(
            !has_beq_far,
            "BNE should not be folded when target is far: {insts:?}"
        );
    }

    #[test]
    fn removes_jmp_to_immediately_following_label() {
        let mut insts = vec![
            Instruction::new(JMP, AM::Label("next".into())),
            Instruction::new(NOP, AM::Label("next".into())),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        let has_jmp = insts.iter().any(|i| i.opcode == JMP);
        assert!(!has_jmp, "JMP to next label should be removed: {insts:?}");
    }

    #[test]
    fn idempotent_on_optimized_code() {
        let mut insts = vec![
            Instruction::new(LDA, AM::Immediate(5)),
            Instruction::new(CLC, AM::Implied),
            Instruction::new(RTS, AM::Implied),
        ];
        let before = insts.len();
        optimize(&mut insts);
        assert_eq!(insts.len(), before);
    }

    #[test]
    fn dead_load_elim_steps_past_ldx_ldy() {
        // `LDA #16 / LDY oam_cursor / LDA #16 / STA $0200,Y` is the
        // IR codegen's DrawSprite shape after copy propagation
        // rewrites the y-position slot read into a fresh immediate.
        // The first `LDA #16` is dead — the second one overwrites
        // A and the intervening `LDY zp` doesn't touch A. Before
        // the LDX/LDY step-past extension this pattern leaked
        // through because `remove_dead_loads` bailed on any
        // unexpected opcode; after the fix the first LDA is dropped,
        // saving 2 bytes per draw.
        let mut insts = vec![
            Instruction::new(LDA, AM::Immediate(16)),
            Instruction::new(LDY, AM::ZeroPage(0x09)),
            Instruction::new(LDA, AM::Immediate(16)),
            Instruction::new(STA, AM::AbsoluteY(0x0200)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        let lda_count = insts.iter().filter(|i| i.opcode == LDA).count();
        assert_eq!(
            lda_count, 1,
            "expected one LDA after peephole; the `LDA #16` before \
             `LDY $09` should be dropped as dead (next LDA \
             overwrites): {insts:?}"
        );
    }

    #[test]
    fn dead_load_elim_preserves_lda_when_used_by_shift() {
        // Counter case: an LDA whose value IS used (by ASL/LSR in
        // accumulator mode) must survive the step-past extension.
        // The ASL reads A, so the LDA isn't dead even though LDY
        // sits between them.
        let mut insts = vec![
            Instruction::new(LDA, AM::ZeroPage(0x10)),
            Instruction::new(LDY, AM::ZeroPage(0x09)),
            Instruction::new(ASL, AM::Accumulator),
            Instruction::new(STA, AM::ZeroPage(0x11)),
            Instruction::new(RTS, AM::Implied),
        ];
        let before_lda = insts.iter().filter(|i| i.opcode == LDA).count();
        optimize(&mut insts);
        let after_lda = insts.iter().filter(|i| i.opcode == LDA).count();
        assert_eq!(
            before_lda, after_lda,
            "LDA feeding an ASL must survive even with LDY in between: {insts:?}"
        );
    }

    #[test]
    fn indexed_load_invalidates_redundant_load_tracker() {
        // Regression test for a miscompile that affected every
        // `draw Sprite at: (arr[i], arr[j])` pattern in the IR
        // codegen. The original `remove_redundant_loads` only
        // tracked `LDA Immediate/ZeroPage/Absolute`; indexed-mode
        // loads like `LDA AbsoluteX(...)` fell through the match
        // and left the A-equivalence tracker unchanged. A later
        // `LDA #imm` that happened to match a stale entry from
        // BEFORE the indexed load was then silently dropped as
        // "already in A" — even though A really held the element
        // the AbsoluteX just loaded.
        //
        // The buggy pattern: load 0 into A to index array1, load
        // arr1[0], STASH it in a temp (so remove_dead_loads keeps
        // the AbsoluteX), load 0 again to index array2, read
        // arr2[0]. With the buggy pass, the second `LDA #0` was
        // dropped as redundant because the tracker still said
        // A = Imm(0) from before the AbsoluteX. Then TAX would
        // push the arr1[0] value into X and the second array
        // load would use an out-of-bounds index.
        let stash = 0x90; // a temp slot addr >= 0x80
        let mut insts = vec![
            Instruction::new(LDA, AM::Immediate(0)),
            Instruction::new(TAX, AM::Implied),
            Instruction::new(LDA, AM::AbsoluteX(0x0300)),
            Instruction::new(STA, AM::ZeroPage(stash)),
            Instruction::new(LDA, AM::Immediate(0)),
            Instruction::new(TAX, AM::Implied),
            Instruction::new(LDA, AM::AbsoluteX(0x0308)),
            Instruction::new(STA, AM::Absolute(0x0200)),
            Instruction::new(LDA, AM::ZeroPage(stash)),
            Instruction::new(STA, AM::Absolute(0x0203)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        // The exact shape after optimization isn't the point —
        // what matters is that there are still two `TAX`
        // instructions each preceded by a fresh `LDA #0` so
        // both AbsoluteX loads target index 0. If the optimizer
        // dropped the second `LDA #0`, the second `TAX` would
        // copy whatever arr1[0] was into X and the second
        // AbsoluteX load would read arr2[arr1[0]] — wildly out
        // of bounds.
        let mut saw_lda_zero_before_tax = 0;
        let mut saw_other_lda_before_tax = false;
        let mut last_lda: Option<AM> = None;
        for inst in &insts {
            match inst.opcode {
                LDA => {
                    last_lda = Some(inst.mode.clone());
                }
                TAX => {
                    match &last_lda {
                        Some(AM::Immediate(0)) => saw_lda_zero_before_tax += 1,
                        _ => saw_other_lda_before_tax = true,
                    }
                    last_lda = None;
                }
                _ => {}
            }
        }
        assert!(
            !saw_other_lda_before_tax,
            "a TAX is preceded by a non-Imm(0) LDA — optimizer kept a stale index: {insts:?}"
        );
        assert_eq!(
            saw_lda_zero_before_tax, 2,
            "both TAXes must be preceded by a fresh LDA #0: {insts:?}"
        );
    }

    #[test]
    fn folds_lda_clc_adc_sta_into_inc() {
        // `LDA $10; CLC; ADC #1; STA $10` is a 4-instruction
        // sequence (7 bytes, 10 cycles) that can be a single
        // `INC $10` (2 bytes, 5 cycles). The peephole fold catches
        // this for both zero-page and absolute addressing.
        let mut insts = vec![
            Instruction::new(LDA, AM::ZeroPage(0x10)),
            Instruction::new(CLC, AM::Implied),
            Instruction::new(ADC, AM::Immediate(1)),
            Instruction::new(STA, AM::ZeroPage(0x10)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        let has_inc = insts
            .iter()
            .any(|i| i.opcode == INC && i.mode == AM::ZeroPage(0x10));
        assert!(has_inc, "should fold to INC $10: {insts:?}");
        // None of the original 4 instructions should survive.
        assert!(!insts.iter().any(|i| i.opcode == CLC));
        assert!(!insts.iter().any(|i| i.opcode == ADC));
    }

    #[test]
    fn folds_lda_sec_sbc_sta_into_dec() {
        let mut insts = vec![
            Instruction::new(LDA, AM::Absolute(0x0300)),
            Instruction::new(SEC, AM::Implied),
            Instruction::new(SBC, AM::Immediate(1)),
            Instruction::new(STA, AM::Absolute(0x0300)),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        let has_dec = insts
            .iter()
            .any(|i| i.opcode == DEC && i.mode == AM::Absolute(0x0300));
        assert!(has_dec, "should fold to DEC $0300: {insts:?}");
        assert!(!insts.iter().any(|i| i.opcode == SEC));
        assert!(!insts.iter().any(|i| i.opcode == SBC));
    }

    #[test]
    fn inc_fold_preserves_when_followed_by_carry_branch() {
        // If the next instruction after the STA is a carry-dependent
        // branch (BCC/BCS), the ADC/SBC → INC/DEC fold would change
        // observable semantics — INC doesn't touch carry. Preserve
        // the original sequence in that case.
        let mut insts = vec![
            Instruction::new(LDA, AM::ZeroPage(0x10)),
            Instruction::new(CLC, AM::Implied),
            Instruction::new(ADC, AM::Immediate(1)),
            Instruction::new(STA, AM::ZeroPage(0x10)),
            Instruction::new(BCC, AM::LabelRelative("skip".into())),
            Instruction::new(NOP, AM::Label("skip".into())),
            Instruction::new(RTS, AM::Implied),
        ];
        optimize(&mut insts);
        // The ADC must still be present because the carry it
        // produces is consumed by the BCC.
        assert!(
            insts.iter().any(|i| i.opcode == ADC),
            "ADC must survive when followed by a carry-dependent branch: {insts:?}"
        );
    }
}
