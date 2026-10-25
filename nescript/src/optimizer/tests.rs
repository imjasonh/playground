use super::*;
use crate::ir::{IrBasicBlock, IrFunction, IrOp, IrProgram, IrTemp, IrTerminator, VarId};
use crate::lexer::Span;

/// Helper: build a minimal `IrProgram` wrapping a single function with one block.
fn make_program(ops: Vec<IrOp>, terminator: IrTerminator) -> IrProgram {
    IrProgram {
        functions: vec![IrFunction {
            name: "test_fn".to_string(),
            blocks: vec![IrBasicBlock {
                label: "entry".to_string(),
                ops,
                terminator,
            }],
            locals: vec![],
            param_count: 0,
            has_return: false,
            bank: None,
            source_span: Span::new(0, 0, 0),
        }],
        globals: vec![],
        rom_data: vec![],
        states: vec![],
        start_state: String::new(),
        var_map: std::collections::HashMap::new(),
    }
}

// ---------------------------------------------------------------------------
// Constant folding tests
// ---------------------------------------------------------------------------

#[test]
fn fold_add_constants() {
    // LoadImm(t0, 3), LoadImm(t1, 5), Add(t2, t0, t1)
    // should become LoadImm(t2, 8) with unused t0/t1 removed.
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let t2 = IrTemp(2);

    let ops = vec![
        IrOp::LoadImm(t0, 3),
        IrOp::LoadImm(t1, 5),
        IrOp::Add(t2, t0, t1),
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t2)));
    optimize(&mut prog);

    let block = &prog.functions[0].blocks[0];
    // After folding + dead-code removal we should have exactly one LoadImm(t2, 8).
    assert_eq!(block.ops.len(), 1, "expected 1 op, got {:?}", block.ops);
    assert!(
        matches!(block.ops[0], IrOp::LoadImm(t, 8) if t == t2),
        "expected LoadImm(t2, 8), got {:?}",
        block.ops[0]
    );
}

#[test]
fn fold_sub_constants() {
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let t2 = IrTemp(2);

    let ops = vec![
        IrOp::LoadImm(t0, 10),
        IrOp::LoadImm(t1, 3),
        IrOp::Sub(t2, t0, t1),
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t2)));
    optimize(&mut prog);

    let block = &prog.functions[0].blocks[0];
    assert_eq!(block.ops.len(), 1, "expected 1 op, got {:?}", block.ops);
    assert!(
        matches!(block.ops[0], IrOp::LoadImm(t, 7) if t == t2),
        "expected LoadImm(t2, 7), got {:?}",
        block.ops[0]
    );
}

#[test]
fn fold_comparison() {
    // CmpEq with two equal constants should fold to LoadImm(dest, 1).
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let t2 = IrTemp(2);

    let ops = vec![
        IrOp::LoadImm(t0, 42),
        IrOp::LoadImm(t1, 42),
        IrOp::CmpEq(t2, t0, t1),
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t2)));
    optimize(&mut prog);

    let block = &prog.functions[0].blocks[0];
    assert_eq!(block.ops.len(), 1, "expected 1 op, got {:?}", block.ops);
    assert!(
        matches!(block.ops[0], IrOp::LoadImm(t, 1) if t == t2),
        "expected LoadImm(t2, 1), got {:?}",
        block.ops[0]
    );

    // CmpEq with two different constants should fold to LoadImm(dest, 0).
    let ops2 = vec![
        IrOp::LoadImm(t0, 10),
        IrOp::LoadImm(t1, 20),
        IrOp::CmpEq(t2, t0, t1),
    ];
    let mut prog2 = make_program(ops2, IrTerminator::Return(Some(t2)));
    optimize(&mut prog2);

    let block2 = &prog2.functions[0].blocks[0];
    assert_eq!(block2.ops.len(), 1, "expected 1 op, got {:?}", block2.ops);
    assert!(
        matches!(block2.ops[0], IrOp::LoadImm(t, 0) if t == t2),
        "expected LoadImm(t2, 0), got {:?}",
        block2.ops[0]
    );
}

#[test]
fn dead_code_removes_unused() {
    // t0 is loaded but never used anywhere — should be eliminated.
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);

    let ops = vec![
        IrOp::LoadImm(t0, 99), // dead — t0 never referenced
        IrOp::LoadImm(t1, 42), // alive — returned
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t1)));
    optimize(&mut prog);

    let block = &prog.functions[0].blocks[0];
    assert_eq!(block.ops.len(), 1, "expected 1 op, got {:?}", block.ops);
    assert!(
        matches!(block.ops[0], IrOp::LoadImm(t, 42) if t == t1),
        "expected only LoadImm(t1, 42), got {:?}",
        block.ops[0]
    );
}

#[test]
fn optimize_preserves_used_ops() {
    // Every op here is live — nothing should be removed.
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let v0 = VarId(0);

    let ops = vec![
        IrOp::LoadImm(t0, 5),
        IrOp::LoadVar(t1, v0),
        IrOp::StoreVar(v0, t0),
    ];
    let mut prog = make_program(ops.clone(), IrTerminator::Return(Some(t1)));
    optimize(&mut prog);

    let block = &prog.functions[0].blocks[0];
    // LoadImm(t0, 5) is used by StoreVar; LoadVar(t1, v0) is used by Return.
    // StoreVar has no dest so it's always kept.
    assert_eq!(block.ops.len(), 3, "expected 3 ops, got {:?}", block.ops);
}

// ---------------------------------------------------------------------------
// Strength reduction tests
// ---------------------------------------------------------------------------

#[test]
fn strength_reduce_power_of_2() {
    // Mul(t2, t0, t1) where t1 = 4 -> ShiftLeft(t2, t0, 2)
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let t2 = IrTemp(2);

    let ops = vec![
        IrOp::LoadImm(t0, 7),
        IrOp::LoadImm(t1, 4),
        IrOp::Mul(t2, t0, t1),
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t2)));
    strength_reduce(&mut prog);

    let block = &prog.functions[0].blocks[0];
    // The Mul should have been replaced with ShiftLeft
    let has_shift = block
        .ops
        .iter()
        .any(|op| matches!(op, IrOp::ShiftLeft(d, s, 2) if *d == t2 && *s == t0));
    assert!(
        has_shift,
        "expected ShiftLeft(t2, t0, 2), got {:?}",
        block.ops
    );
    // No Mul should remain
    let has_mul = block.ops.iter().any(|op| matches!(op, IrOp::Mul(..)));
    assert!(!has_mul, "Mul should have been replaced");
}

#[test]
fn strength_reduce_mul_by_3() {
    // Mul(t2, t0, t1) where t1 = 3 -> Add chain
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let t2 = IrTemp(2);

    let ops = vec![
        IrOp::LoadImm(t0, 5),
        IrOp::LoadImm(t1, 3),
        IrOp::Mul(t2, t0, t1),
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t2)));
    strength_reduce(&mut prog);

    let block = &prog.functions[0].blocks[0];
    // Mul should have been replaced by two Add ops
    let add_count = block
        .ops
        .iter()
        .filter(|op| matches!(op, IrOp::Add(..)))
        .count();
    assert_eq!(
        add_count, 2,
        "expected 2 Add ops for mul-by-3, got {:?}",
        block.ops
    );
    let has_mul = block.ops.iter().any(|op| matches!(op, IrOp::Mul(..)));
    assert!(!has_mul, "Mul should have been replaced");
}

#[test]
fn strength_reduce_div_by_power_of_two() {
    // Div(t2, t0, t1) where t1 = 4 -> ShiftRight(t2, t0, 2)
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let t2 = IrTemp(2);

    let ops = vec![
        IrOp::LoadImm(t0, 40),
        IrOp::LoadImm(t1, 4),
        IrOp::Div(t2, t0, t1),
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t2)));
    strength_reduce(&mut prog);

    let block = &prog.functions[0].blocks[0];
    assert!(
        block
            .ops
            .iter()
            .any(|op| matches!(op, IrOp::ShiftRight(d, s, 2) if *d == t2 && *s == t0)),
        "expected ShiftRight(t2, t0, 2), got {:?}",
        block.ops
    );
    assert!(
        !block.ops.iter().any(|op| matches!(op, IrOp::Div(..))),
        "Div should have been replaced"
    );
}

#[test]
fn strength_reduce_mod_by_power_of_two() {
    // Mod(t2, t0, t1) where t1 = 8 -> And(t2, t0, mask=7)
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let t2 = IrTemp(2);

    let ops = vec![
        IrOp::LoadImm(t0, 19),
        IrOp::LoadImm(t1, 8),
        IrOp::Mod(t2, t0, t1),
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t2)));
    strength_reduce(&mut prog);

    let block = &prog.functions[0].blocks[0];
    assert!(
        block
            .ops
            .iter()
            .any(|op| matches!(op, IrOp::And(d, a, _) if *d == t2 && *a == t0)),
        "expected And(t2, t0, _), got {:?}",
        block.ops
    );
    assert!(
        !block.ops.iter().any(|op| matches!(op, IrOp::Mod(..))),
        "Mod should have been replaced"
    );
}

#[test]
fn strength_reduce_shift_var_with_constant_amount() {
    // ShiftLeftVar(t2, t0, t1) where t1 = 3 -> ShiftLeft(t2, t0, 3).
    // Regression: before the fix, lowering silently emitted
    // ShiftLeft(..., 1) for *every* shift, so `x << 3` quietly
    // miscompiled to `x << 1`.
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let t2 = IrTemp(2);

    let ops = vec![
        IrOp::LoadImm(t0, 2),
        IrOp::LoadImm(t1, 3),
        IrOp::ShiftLeftVar(t2, t0, t1),
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t2)));
    strength_reduce(&mut prog);

    let block = &prog.functions[0].blocks[0];
    assert!(
        block
            .ops
            .iter()
            .any(|op| matches!(op, IrOp::ShiftLeft(d, s, 3) if *d == t2 && *s == t0)),
        "expected ShiftLeft(t2, t0, 3), got {:?}",
        block.ops
    );
}

#[test]
fn strength_reduce_leaves_non_power() {
    // Mul by 5 should NOT be replaced
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);
    let t2 = IrTemp(2);

    let ops = vec![
        IrOp::LoadImm(t0, 7),
        IrOp::LoadImm(t1, 5),
        IrOp::Mul(t2, t0, t1),
    ];
    let mut prog = make_program(ops, IrTerminator::Return(Some(t2)));
    strength_reduce(&mut prog);

    let block = &prog.functions[0].blocks[0];
    let has_mul = block.ops.iter().any(|op| matches!(op, IrOp::Mul(..)));
    assert!(has_mul, "Mul by 5 should not be replaced");
}

// ---------------------------------------------------------------------------
// Zero-page candidate analysis tests
// ---------------------------------------------------------------------------

#[test]
fn zp_candidates_by_frequency() {
    let v0 = VarId(0);
    let v1 = VarId(1);
    let v2 = VarId(2);
    let t0 = IrTemp(0);
    let t1 = IrTemp(1);

    // v0 accessed 3 times, v1 accessed 1 time, v2 accessed 2 times
    let ops = vec![
        IrOp::LoadVar(t0, v0),
        IrOp::StoreVar(v0, t0),
        IrOp::LoadVar(t1, v0),
        IrOp::LoadVar(t0, v2),
        IrOp::StoreVar(v2, t0),
        IrOp::LoadVar(t1, v1),
    ];
    let prog = make_program(ops, IrTerminator::Return(Some(t1)));
    let candidates = analyze_zp_candidates(&prog);

    assert!(!candidates.is_empty());
    // First should be v0 with count 3
    assert_eq!(candidates[0].0, v0);
    assert_eq!(candidates[0].1, 3);
    // v2 with count 2 should be before v1 with count 1
    let v2_idx = candidates.iter().position(|(v, _)| *v == v2).unwrap();
    let v1_idx = candidates.iter().position(|(v, _)| *v == v1).unwrap();
    assert!(
        v2_idx < v1_idx,
        "v2 (count 2) should come before v1 (count 1)"
    );
}

// ---------------------------------------------------------------------------
// Function inlining tests
// ---------------------------------------------------------------------------

#[test]
fn inline_removes_trivial() {
    // Create a program with a trivial (empty) function and a main function that calls it
    let t0 = IrTemp(0);

    let trivial_fn = IrFunction {
        name: "trivial".to_string(),
        blocks: vec![IrBasicBlock {
            label: "entry".to_string(),
            ops: vec![],
            terminator: IrTerminator::Return(None),
        }],
        locals: vec![],
        param_count: 0,
        has_return: false,
        bank: None,
        source_span: Span::new(0, 0, 0),
    };

    let main_fn = IrFunction {
        name: "main_fn".to_string(),
        blocks: vec![IrBasicBlock {
            label: "entry".to_string(),
            ops: vec![
                IrOp::Call(None, "trivial".to_string(), vec![]),
                IrOp::LoadImm(t0, 42),
            ],
            terminator: IrTerminator::Return(Some(t0)),
        }],
        locals: vec![],
        param_count: 0,
        has_return: true,
        bank: None,
        source_span: Span::new(0, 0, 0),
    };

    let mut prog = IrProgram {
        functions: vec![trivial_fn, main_fn],
        globals: vec![],
        rom_data: vec![],
        states: vec![],
        start_state: String::new(),
        var_map: std::collections::HashMap::new(),
    };

    inline_small_functions(&mut prog);

    // The trivial function should be removed
    assert_eq!(
        prog.functions.len(),
        1,
        "trivial function should have been removed"
    );
    assert_eq!(prog.functions[0].name, "main_fn");

    // The call to trivial should be removed from main_fn
    let has_call = prog.functions[0].blocks[0]
        .ops
        .iter()
        .any(|op| matches!(op, IrOp::Call(..)));
    assert!(!has_call, "call to trivial function should be removed");
}

// ---------------------------------------------------------------------------
// Cross-block LoadImm liveness (regression for stale-and-result bug)
// ---------------------------------------------------------------------------

/// A `LoadImm(result, 0)` in a predecessor block whose only consumer
/// is a branch terminator in a *successor* block must not be dropped
/// by the const-folding pass. This is the shape the logical-`and`
/// short-circuit false path lowers to, and dropping the `LoadImm`
/// leaves the zero-page slot holding whichever value the previous
/// `and` evaluation wrote — which was observable in the platformer
/// example as spurious enemy-stomp bounces firing whenever coin 2
/// happened to be in its pickup window.
#[test]
fn const_fold_preserves_loadimm_used_by_sibling_branch() {
    let cond = IrTemp(0);
    let result = IrTemp(1);
    let zero = IrTemp(2);

    // Shape mirrors `lower_logical_and`: an entry block that branches
    // on `cond`, a right-side block that writes `result` via an
    // `Or(result, <true-case>, zero)`, a false-side block that only
    // writes `LoadImm(result, 0)`, and a merge block whose terminator
    // reads `result`.
    let entry = IrBasicBlock {
        label: "entry".to_string(),
        ops: vec![IrOp::LoadImm(cond, 1)],
        terminator: IrTerminator::Branch(cond, "right".to_string(), "false_path".to_string()),
    };
    let right = IrBasicBlock {
        label: "right".to_string(),
        ops: vec![IrOp::LoadImm(zero, 0), IrOp::Or(result, cond, zero)],
        terminator: IrTerminator::Jump("end".to_string()),
    };
    // This is the block that previously tripped the bug: its
    // `LoadImm(result, 0)` is the only op, and `result` is not used
    // as a source operand anywhere *within* this block — but it is
    // read by the `end` block's branch terminator.
    let false_path = IrBasicBlock {
        label: "false_path".to_string(),
        ops: vec![IrOp::LoadImm(result, 0)],
        terminator: IrTerminator::Jump("end".to_string()),
    };
    let end = IrBasicBlock {
        label: "end".to_string(),
        ops: vec![],
        terminator: IrTerminator::Return(Some(result)),
    };

    let mut prog = IrProgram {
        functions: vec![IrFunction {
            name: "and_like".to_string(),
            blocks: vec![entry, right, false_path, end],
            locals: vec![],
            param_count: 0,
            has_return: true,
            bank: None,
            source_span: Span::new(0, 0, 0),
        }],
        globals: vec![],
        rom_data: vec![],
        states: vec![],
        start_state: String::new(),
        var_map: std::collections::HashMap::new(),
    };

    optimize(&mut prog);

    // Find the false_path block post-optimization and verify that
    // its LoadImm(result, 0) is still there.
    let func = &prog.functions[0];
    let fp = func
        .blocks
        .iter()
        .find(|b| b.label == "false_path")
        .expect("false_path block should survive as reachable");
    assert!(
        fp.ops
            .iter()
            .any(|op| matches!(op, IrOp::LoadImm(t, 0) if *t == result)),
        "false-path LoadImm(result, 0) must survive optimization; block ops were {:?}",
        fp.ops
    );
}
