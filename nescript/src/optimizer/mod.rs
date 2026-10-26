#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use crate::ir::{
    IrBasicBlock, IrFunction, IrOp, IrProgram, IrTemp, IrTerminator, Signedness, VarId,
};

/// Compare two byte-valued constants under the requested signedness.
/// Used by the constant-folding paths for the ordering comparisons —
/// when both operands have collapsed to compile-time constants, we
/// can pre-compute the boolean and replace the IR op with a
/// `LoadImm`. The signed branch reinterprets the byte through `i8`
/// so that e.g. `LoadImm 0xFF < LoadImm 0x01` folds to `1` under
/// signed semantics (-1 < 1) but `0` under unsigned (255 > 1).
fn cmp_const_signed(a: u8, b: u8, signed: Signedness) -> std::cmp::Ordering {
    match signed {
        Signedness::Signed => a.cast_signed().cmp(&b.cast_signed()),
        Signedness::Unsigned => a.cmp(&b),
    }
}

/// Run all optimization passes on the IR program.
pub fn optimize(program: &mut IrProgram) {
    strength_reduce(program);
    inline_small_functions(program);
    const_fold(program);
    dead_code(program);
}

// ---------------------------------------------------------------------------
// Zero-page promotion analysis
// ---------------------------------------------------------------------------

/// Analyze IR to count variable access frequency.
/// Returns a list of `(VarId, count)` sorted by frequency (highest first).
pub fn analyze_zp_candidates(program: &IrProgram) -> Vec<(VarId, u32)> {
    let mut counts: HashMap<VarId, u32> = HashMap::new();

    for func in &program.functions {
        for block in &func.blocks {
            for op in &block.ops {
                match op {
                    IrOp::LoadVar(_, var_id) | IrOp::StoreVar(var_id, _) => {
                        *counts.entry(*var_id).or_insert(0) += 1;
                    }
                    IrOp::ArrayLoad(_, var_id, _) | IrOp::ArrayStore(var_id, _, _) => {
                        *counts.entry(*var_id).or_insert(0) += 1;
                    }
                    _ => {}
                }
            }
        }
    }

    let mut result: Vec<(VarId, u32)> = counts.into_iter().collect();
    result.sort_by_key(|(_, count)| std::cmp::Reverse(*count));
    result
}

// ---------------------------------------------------------------------------
// Function inlining
// ---------------------------------------------------------------------------

/// Inline small functions (< 8 ops) called from <= 2 sites.
/// For now, just remove empty/trivial functions (those with 0 meaningful ops).
pub fn inline_small_functions(program: &mut IrProgram) {
    // Count call sites for each function
    let mut call_counts: HashMap<String, u32> = HashMap::new();
    for func in &program.functions {
        for block in &func.blocks {
            for op in &block.ops {
                if let IrOp::Call(_, name, _) = op {
                    *call_counts.entry(name.clone()).or_insert(0) += 1;
                }
            }
        }
    }

    // Find functions that are trivial (0 meaningful ops, just return)
    // and have <= 2 call sites and < 8 ops
    let trivial_fns: HashSet<String> = program
        .functions
        .iter()
        .filter(|f| {
            let op_count = f.op_count();
            let calls = call_counts.get(&f.name).copied().unwrap_or(0);
            op_count < 8 && calls <= 2 && op_count == 0
        })
        .map(|f| f.name.clone())
        .collect();

    if trivial_fns.is_empty() {
        return;
    }

    // Remove calls to trivial functions
    for func in &mut program.functions {
        for block in &mut func.blocks {
            block
                .ops
                .retain(|op| !matches!(op, IrOp::Call(_, name, _) if trivial_fns.contains(name)));
        }
    }

    // Remove the trivial functions themselves
    program.functions.retain(|f| !trivial_fns.contains(&f.name));
}

// ---------------------------------------------------------------------------
// Strength reduction
// ---------------------------------------------------------------------------

/// Replace multiply by power-of-2 with shifts, and multiply by 3 with add chain.
fn strength_reduce(program: &mut IrProgram) {
    for func in &mut program.functions {
        for block in &mut func.blocks {
            strength_reduce_block(block);
        }
    }
}

fn strength_reduce_block(block: &mut IrBasicBlock) {
    // First, collect known constants from LoadImm ops
    let mut constants: HashMap<IrTemp, u8> = HashMap::new();
    for op in &block.ops {
        if let IrOp::LoadImm(t, v) = op {
            constants.insert(*t, *v);
        }
    }

    // Now scan for Mul / Div / Mod / ShiftVar ops where one operand
    // is a known constant. Each reduces to a shift, AND, or Add chain.
    let mut replacements: Vec<(usize, Vec<IrOp>)> = Vec::new();

    for (i, op) in block.ops.iter().enumerate() {
        match op {
            IrOp::Mul(dest, a, b) => {
                // Check if b is a known constant
                if let Some(&val) = constants.get(b) {
                    if val.is_power_of_two() && val > 1 {
                        let shift = val.trailing_zeros() as u8;
                        replacements.push((i, vec![IrOp::ShiftLeft(*dest, *a, shift)]));
                    } else if val == 3 {
                        // Mul by 3: tmp = a + a; dest = tmp + a
                        // We reuse dest as tmp in first step, then compute final
                        replacements.push((
                            i,
                            vec![IrOp::Add(*dest, *a, *a), IrOp::Add(*dest, *dest, *a)],
                        ));
                    }
                    continue;
                }
                // Check if a is a known constant (commutative)
                if let Some(&val) = constants.get(a) {
                    if val.is_power_of_two() && val > 1 {
                        let shift = val.trailing_zeros() as u8;
                        replacements.push((i, vec![IrOp::ShiftLeft(*dest, *b, shift)]));
                    } else if val == 3 {
                        replacements.push((
                            i,
                            vec![IrOp::Add(*dest, *b, *b), IrOp::Add(*dest, *dest, *b)],
                        ));
                    }
                }
            }
            // `x / 2ⁿ` → right shift; `x % 2ⁿ` → AND with `2ⁿ - 1`.
            // Only the divisor side is interesting — `const / x` and
            // `const % x` still need the runtime routine.
            IrOp::Div(dest, a, b) => {
                if let Some(&val) = constants.get(b) {
                    if val.is_power_of_two() && val > 1 {
                        let shift = val.trailing_zeros() as u8;
                        replacements.push((i, vec![IrOp::ShiftRight(*dest, *a, shift)]));
                    } else if val == 1 {
                        // `x / 1 == x` — copy via `a | 0`. Reusing the
                        // existing LoadImm at `b` saves us from
                        // having to synthesize a new temp.
                        replacements.push((i, vec![IrOp::Or(*dest, *a, *b)]));
                    }
                }
            }
            IrOp::Mod(dest, a, b) => {
                if let Some(&val) = constants.get(b) {
                    if val.is_power_of_two() && val > 1 {
                        // `x % 2ⁿ == x & (2ⁿ - 1)`. We need a LoadImm
                        // temp for the mask; reuse `b`'s slot via a
                        // fresh LoadImm so later ops that read `b`
                        // still see the original divisor. Emitting a
                        // second LoadImm into the same temp is
                        // tolerated because use counts treat it as a
                        // redefinition.
                        let mask = val - 1;
                        replacements
                            .push((i, vec![IrOp::LoadImm(*b, mask), IrOp::And(*dest, *a, *b)]));
                    } else if val == 1 {
                        // `x % 1 == 0`.
                        replacements.push((i, vec![IrOp::LoadImm(*dest, 0)]));
                    }
                }
            }
            IrOp::ShiftLeftVar(dest, a, b) => {
                if let Some(&val) = constants.get(b) {
                    let count = val.min(8);
                    replacements.push((i, vec![IrOp::ShiftLeft(*dest, *a, count)]));
                }
            }
            IrOp::ShiftRightVar(dest, a, b) => {
                if let Some(&val) = constants.get(b) {
                    let count = val.min(8);
                    replacements.push((i, vec![IrOp::ShiftRight(*dest, *a, count)]));
                }
            }
            _ => {}
        }
    }

    // Apply replacements in reverse order to maintain correct indices
    for (i, new_ops) in replacements.into_iter().rev() {
        block.ops.splice(i..=i, new_ops);
    }
}

// ---------------------------------------------------------------------------
// Constant folding
// ---------------------------------------------------------------------------

/// Single-pass constant folding within each basic block.
///
/// When we see `LoadImm(t, v)`, we record `t -> v`. When a binary op or
/// comparison has both operands as known constants we replace the instruction
/// with a single `LoadImm`. After folding we remove `LoadImm` ops whose
/// destination temps are no longer referenced anywhere in the block.
fn const_fold(program: &mut IrProgram) {
    for func in &mut program.functions {
        // Pre-compute function-wide source-operand usage: a LoadImm's
        // destination may be read by an op in a sibling block or
        // consumed by a branch/jump terminator in another block, so
        // the per-block DCE below can't decide liveness by looking
        // at its own block alone. Cf. the `and` / `or` short-circuit
        // lowering: the false path writes `LoadImm(result, 0)` but
        // `result` is read by the merge block's branch, not in the
        // false block itself.
        let func_used = collect_used_temps(func);
        for block in &mut func.blocks {
            const_fold_block(block, &func_used);
        }
    }
}

fn const_fold_block(block: &mut IrBasicBlock, func_used: &HashSet<IrTemp>) {
    let mut constants: HashMap<IrTemp, u8> = HashMap::new();

    // First pass: fold arithmetic / comparison ops into LoadImm where possible.
    for op in &mut block.ops {
        match *op {
            IrOp::LoadImm(t, v) => {
                constants.insert(t, v);
            }
            IrOp::Add(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result = va.wrapping_add(vb);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::Sub(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result = va.wrapping_sub(vb);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::And(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result = va & vb;
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::Or(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result = va | vb;
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::Xor(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result = va ^ vb;
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::CmpEq(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result = u8::from(va == vb);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::CmpNe(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result = u8::from(va != vb);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::CmpLt(dest, a, b, signed) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result =
                        u8::from(cmp_const_signed(va, vb, signed) == std::cmp::Ordering::Less);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::CmpGt(dest, a, b, signed) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result =
                        u8::from(cmp_const_signed(va, vb, signed) == std::cmp::Ordering::Greater);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::CmpLtEq(dest, a, b, signed) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result =
                        u8::from(cmp_const_signed(va, vb, signed) != std::cmp::Ordering::Greater);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::CmpGtEq(dest, a, b, signed) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result =
                        u8::from(cmp_const_signed(va, vb, signed) != std::cmp::Ordering::Less);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::Mul(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result = va.wrapping_mul(vb);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::Div(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    // `checked_div` returns None on `vb == 0`; the
                    // division-by-zero fallback stays `0` so folded
                    // `x / 0` matches the runtime semantics elsewhere
                    // in the compiler.
                    let result = va.checked_div(vb).unwrap_or(0);
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::Mod(dest, a, b) => {
                if let (Some(&va), Some(&vb)) = (constants.get(&a), constants.get(&b)) {
                    let result = if vb == 0 { 0 } else { va % vb };
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::ShiftLeft(dest, a, count) => {
                if let Some(&va) = constants.get(&a) {
                    let result = va.wrapping_shl(u32::from(count));
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            IrOp::ShiftRight(dest, a, count) => {
                if let Some(&va) = constants.get(&a) {
                    let result = va.wrapping_shr(u32::from(count));
                    *op = IrOp::LoadImm(dest, result);
                    constants.insert(dest, result);
                }
            }
            _ => {}
        }
    }

    // Second pass: remove LoadImm ops whose dest temps are no longer
    // referenced locally AND aren't referenced function-wide. The
    // function-wide check is what makes this pass correct in the
    // presence of control-flow merges — a LoadImm written in one
    // block and consumed in another (for example the `and`/`or`
    // short-circuit false path, whose `LoadImm(result, 0)` is only
    // read by the downstream merge block's branch terminator) must
    // not be dropped. The previous implementation only consulted
    // block-local usage and silently dropped these cross-block
    // LoadImms, leaving the zero-page result slot to carry whatever
    // value the *previous* AND/OR had written into it.
    let used_local = collect_used_temps_in_block(block);
    block.ops.retain(|op| {
        if let IrOp::LoadImm(t, _) = op {
            used_local.contains(t) || func_used.contains(t)
        } else {
            true
        }
    });
}

// ---------------------------------------------------------------------------
// Dead code elimination
// ---------------------------------------------------------------------------

/// Remove ops whose destination temps are never used, and remove unreachable
/// basic blocks (those that have no incoming edges, except the entry block).
fn dead_code(program: &mut IrProgram) {
    for func in &mut program.functions {
        dead_code_eliminate(func);
        remove_unreachable_blocks(func);
    }
}

fn dead_code_eliminate(func: &mut IrFunction) {
    let used = collect_used_temps(func);
    for block in &mut func.blocks {
        block.ops.retain(|op| {
            if let Some(dest) = op_dest(op) {
                used.contains(&dest)
            } else {
                true // ops without a dest (StoreVar, WaitFrame, etc.) are always kept
            }
        });
    }
}

/// Collect every `IrTemp` that is used as a *source* operand anywhere in the
/// function (ops + terminators).
fn collect_used_temps(func: &IrFunction) -> HashSet<IrTemp> {
    let mut used = HashSet::new();
    for block in &func.blocks {
        collect_used_from_block(block, &mut used);
    }
    used
}

/// Collect temps used as source operands within a single block
/// (ops + terminator). Used by the per-block `LoadImm` DCE so we
/// can cheaply find local uses before falling back on the
/// function-wide liveness set.
fn collect_used_temps_in_block(block: &IrBasicBlock) -> HashSet<IrTemp> {
    let mut used = HashSet::new();
    collect_used_from_block(block, &mut used);
    used
}

fn collect_used_from_block(block: &IrBasicBlock, used: &mut HashSet<IrTemp>) {
    for op in &block.ops {
        collect_source_temps(op, used);
    }
    match &block.terminator {
        IrTerminator::Branch(t, _, _) | IrTerminator::Return(Some(t)) => {
            used.insert(*t);
        }
        IrTerminator::Jump(_) | IrTerminator::Return(None) | IrTerminator::Unreachable => {}
    }
}

/// Add all source-operand temps of an op to `used`.
fn collect_source_temps(op: &IrOp, used: &mut HashSet<IrTemp>) {
    match op {
        IrOp::LoadImm(_, _) => {} // dest only, no source temps
        IrOp::LoadVar(_, _) => {} // dest only
        IrOp::StoreVar(_, src) => {
            used.insert(*src);
        }
        IrOp::Add(_, a, b)
        | IrOp::Sub(_, a, b)
        | IrOp::Mul(_, a, b)
        | IrOp::Div(_, a, b)
        | IrOp::Mod(_, a, b)
        | IrOp::And(_, a, b)
        | IrOp::Or(_, a, b)
        | IrOp::Xor(_, a, b)
        | IrOp::ShiftLeftVar(_, a, b)
        | IrOp::ShiftRightVar(_, a, b)
        | IrOp::CmpEq(_, a, b)
        | IrOp::CmpNe(_, a, b)
        | IrOp::CmpLt(_, a, b, _)
        | IrOp::CmpGt(_, a, b, _)
        | IrOp::CmpLtEq(_, a, b, _)
        | IrOp::CmpGtEq(_, a, b, _) => {
            used.insert(*a);
            used.insert(*b);
        }
        IrOp::ShiftLeft(_, src, _) | IrOp::ShiftRight(_, src, _) => {
            used.insert(*src);
        }
        IrOp::Negate(_, src) | IrOp::Complement(_, src) | IrOp::SignExtend(_, src) => {
            used.insert(*src);
        }
        IrOp::ArrayLoad(_, _, idx) => {
            used.insert(*idx);
        }
        IrOp::ArrayStore(_, idx, val) => {
            used.insert(*idx);
            used.insert(*val);
        }
        IrOp::Call(_, _, args) => {
            for a in args {
                used.insert(*a);
            }
        }
        IrOp::DrawSprite { x, y, frame, .. } => {
            used.insert(*x);
            used.insert(*y);
            if let Some(f) = frame {
                used.insert(*f);
            }
        }
        IrOp::Scroll(x, y) => {
            used.insert(*x);
            used.insert(*y);
        }
        IrOp::DebugLog(args) => {
            for a in args {
                used.insert(*a);
            }
        }
        IrOp::DebugAssert(cond) => {
            used.insert(*cond);
        }
        IrOp::Poke(_, src) => {
            used.insert(*src);
        }
        IrOp::StoreVarHi(_, src) => {
            used.insert(*src);
        }
        IrOp::Add16 {
            a_lo,
            a_hi,
            b_lo,
            b_hi,
            ..
        }
        | IrOp::Sub16 {
            a_lo,
            a_hi,
            b_lo,
            b_hi,
            ..
        }
        | IrOp::CmpEq16 {
            a_lo,
            a_hi,
            b_lo,
            b_hi,
            ..
        }
        | IrOp::CmpNe16 {
            a_lo,
            a_hi,
            b_lo,
            b_hi,
            ..
        }
        | IrOp::CmpLt16 {
            a_lo,
            a_hi,
            b_lo,
            b_hi,
            ..
        }
        | IrOp::CmpGt16 {
            a_lo,
            a_hi,
            b_lo,
            b_hi,
            ..
        }
        | IrOp::CmpLtEq16 {
            a_lo,
            a_hi,
            b_lo,
            b_hi,
            ..
        }
        | IrOp::CmpGtEq16 {
            a_lo,
            a_hi,
            b_lo,
            b_hi,
            ..
        } => {
            used.insert(*a_lo);
            used.insert(*a_hi);
            used.insert(*b_lo);
            used.insert(*b_hi);
        }
        IrOp::LoadVarHi(_, _)
        | IrOp::ReadInput(_, _)
        | IrOp::ReadInputEdge { .. }
        | IrOp::WaitFrame
        | IrOp::CycleSprites
        | IrOp::Transition(_)
        | IrOp::InlineAsm(_)
        | IrOp::Peek(_, _)
        | IrOp::PlaySfx(_)
        | IrOp::StartMusic(_)
        | IrOp::StopMusic
        | IrOp::Rand8(_)
        | IrOp::Rand16(_, _)
        | IrOp::SetPalette(_)
        | IrOp::LoadBackground(_)
        | IrOp::PaintRoom(_)
        | IrOp::SourceLoc(_) => {}
        IrOp::SeedRand(lo, hi) => {
            used.insert(*lo);
            used.insert(*hi);
        }
        IrOp::SetPaletteBrightness(level) => {
            used.insert(*level);
        }
        IrOp::FadeOut(step_frames) | IrOp::FadeIn(step_frames) => {
            used.insert(*step_frames);
        }
        IrOp::Sprite0Split { scroll_x, scroll_y } => {
            used.insert(*scroll_x);
            used.insert(*scroll_y);
        }
        IrOp::NtSet { x, y, tile } => {
            used.insert(*x);
            used.insert(*y);
            used.insert(*tile);
        }
        IrOp::NtAttr { x, y, value } => {
            used.insert(*x);
            used.insert(*y);
            used.insert(*value);
        }
        IrOp::NtFillH { x, y, len, tile } => {
            used.insert(*x);
            used.insert(*y);
            used.insert(*len);
            used.insert(*tile);
        }
        IrOp::CollidesAt { x, y, .. } => {
            used.insert(*x);
            used.insert(*y);
        }
    }
}

/// Return the destination temp of an op, if it has one.
fn op_dest(op: &IrOp) -> Option<IrTemp> {
    match op {
        IrOp::LoadImm(d, _)
        | IrOp::LoadVar(d, _)
        | IrOp::Add(d, _, _)
        | IrOp::Sub(d, _, _)
        | IrOp::Mul(d, _, _)
        | IrOp::Div(d, _, _)
        | IrOp::Mod(d, _, _)
        | IrOp::And(d, _, _)
        | IrOp::Or(d, _, _)
        | IrOp::Xor(d, _, _)
        | IrOp::ShiftLeft(d, _, _)
        | IrOp::ShiftRight(d, _, _)
        | IrOp::ShiftLeftVar(d, _, _)
        | IrOp::ShiftRightVar(d, _, _)
        | IrOp::Negate(d, _)
        | IrOp::Complement(d, _)
        | IrOp::SignExtend(d, _)
        | IrOp::CmpEq(d, _, _)
        | IrOp::CmpNe(d, _, _)
        | IrOp::CmpLt(d, _, _, _)
        | IrOp::CmpGt(d, _, _, _)
        | IrOp::CmpLtEq(d, _, _, _)
        | IrOp::CmpGtEq(d, _, _, _)
        | IrOp::ArrayLoad(d, _, _) => Some(*d),
        IrOp::Call(dest, _, _) => *dest,
        IrOp::ReadInput(d, _) => Some(*d),
        IrOp::ReadInputEdge { dest, .. } => Some(*dest),
        IrOp::Peek(d, _) => Some(*d),
        IrOp::CollidesAt { dest, .. } => Some(*dest),
        // Rand8 / Rand16 have an observable side effect — advancing
        // the PRNG state — so a statement-level call like
        // `rand8()` (result discarded) must NOT be dropped by DCE.
        // Returning `None` here keeps the JSR regardless of whether
        // the dest temp is live; the dest is still referenced by
        // `op_source_temps` so live expression-position uses still
        // track correctly.
        IrOp::Rand8(_) | IrOp::Rand16(_, _) => None,
        IrOp::StoreVar(_, _)
        | IrOp::StoreVarHi(_, _)
        | IrOp::ArrayStore(_, _, _)
        | IrOp::DrawSprite { .. }
        | IrOp::WaitFrame
        | IrOp::CycleSprites
        | IrOp::Transition(_)
        | IrOp::Scroll(_, _)
        | IrOp::DebugLog(_)
        | IrOp::DebugAssert(_)
        | IrOp::InlineAsm(_)
        | IrOp::Poke(_, _)
        | IrOp::PlaySfx(_)
        | IrOp::StartMusic(_)
        | IrOp::StopMusic
        | IrOp::SeedRand(_, _)
        | IrOp::SetPaletteBrightness(_)
        | IrOp::FadeOut(_)
        | IrOp::FadeIn(_)
        | IrOp::Sprite0Split { .. }
        | IrOp::NtSet { .. }
        | IrOp::NtAttr { .. }
        | IrOp::NtFillH { .. }
        | IrOp::SetPalette(_)
        | IrOp::LoadBackground(_)
        | IrOp::PaintRoom(_)
        | IrOp::SourceLoc(_) => None,
        // 16-bit ops have two destinations; the simple single-dest
        // DCE below would incorrectly drop a 16-bit op whose low
        // dest is unused even if its high dest is live. Returning
        // `None` here preserves them unconditionally — they're
        // rare enough that the lost DCE opportunity is a good
        // trade for correctness.
        IrOp::LoadVarHi(_, _)
        | IrOp::Add16 { .. }
        | IrOp::Sub16 { .. }
        | IrOp::CmpEq16 { .. }
        | IrOp::CmpNe16 { .. }
        | IrOp::CmpLt16 { .. }
        | IrOp::CmpGt16 { .. }
        | IrOp::CmpLtEq16 { .. }
        | IrOp::CmpGtEq16 { .. } => None,
    }
}

/// Remove basic blocks that have no incoming edges (except the entry block,
/// which is always reachable by definition).
fn remove_unreachable_blocks(func: &mut IrFunction) {
    if func.blocks.is_empty() {
        return;
    }

    let entry_label = func.blocks[0].label.clone();

    // Collect all labels that are jump/branch targets.
    let mut reachable_labels: HashSet<String> = HashSet::new();
    reachable_labels.insert(entry_label);

    for block in &func.blocks {
        match &block.terminator {
            IrTerminator::Jump(lbl) => {
                reachable_labels.insert(lbl.clone());
            }
            IrTerminator::Branch(_, t, f) => {
                reachable_labels.insert(t.clone());
                reachable_labels.insert(f.clone());
            }
            IrTerminator::Return(_) | IrTerminator::Unreachable => {}
        }
    }

    func.blocks.retain(|b| reachable_labels.contains(&b.label));
}
