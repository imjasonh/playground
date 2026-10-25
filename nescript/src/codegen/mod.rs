//! Code generation.
//!
//! Walks an `IrProgram` produced by `src/ir/lowering.rs` and emits 6502
//! `Instruction` sequences. The final pass is `peephole::optimize`, which
//! cleans up the IR codegen's temp-heavy output into something closer to
//! hand-written assembly.
//!
//! There used to be a legacy AST-based codegen in this module alongside
//! `IrCodeGen`. It's been removed — the IR path is canonical, and the
//! AST path was strictly a subset (no struct literal init, no function
//! return values, no runtime OAM cursor for looped draws, no match with
//! many arms, etc.). Every example and integration test now goes through
//! `IrCodeGen`.

pub mod ir_codegen;
pub mod peephole;

pub use ir_codegen::IrCodeGen;
