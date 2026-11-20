import C3BootProofs.Proofs.SvEc
import C3BootProofs.Proofs.Pv384Ds

/-!
# `sigstore::verify`: the P-256 check's divstep batch

The inversion of `s` in the inlined P-256 check runs batches of variable-time
divsteps on 64-bit words, like `p384_verify_prehash`'s (`Pv384Ds.lean`), with
the same `dsStep`. Here `f`'s high word lives in the frame at `sp + 0x74`
instead of a register; this file proves the loop at 0x1392 runs `dsStep`
once per iteration.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- The batch's state: `δ` in `s9:s7`, `f` in the word at `sp + 0x74` and
`s6`, `g` in `a1:a0`, `u` in `t0:a4`, `v` in `a7:t6`, `q` in `t4:s0`, and `r`
in `t1:a2`. -/
def EcDsRegs (M : Word → BitVec 8) (f : Fin 32 → Word) (s : Ds) : Prop :=
  W64 (f 23) (f 25) = s.δ ∧ W64 (f 22) (memLoad32 M (f 2 + 0x74)) = s.f ∧ W64 (f 10) (f 11) = s.g ∧
    W64 (f 14) (f 5) = s.u ∧ W64 (f 31) (f 17) = s.v ∧ W64 (f 8) (f 29) = s.q ∧ W64 (f 12) (f 6) = s.r

def ecA : List BInstr := [.aluImm .and a3 a0 0x1]
theorem ecA_end : blockEnd sigstoreVerifyCode 0x1392 ecA = some 0x1396 := by decide

def ecE : List BInstr :=
  [.aluImm .add a3 (23 : Fin 32) 0x2,
   .alu .add (9 : Fin 32) x0 a2,
   .alu .add (30 : Fin 32) x0 (6 : Fin 32),
   .alu .sltu a2 a3 (23 : Fin 32),
   .alu .add (28 : Fin 32) x0 (8 : Fin 32),
   .alu .add (25 : Fin 32) (25 : Fin 32) a2,
   .alu .add (7 : Fin 32) x0 (29 : Fin 32),
   .alu .add (23 : Fin 32) x0 a3,
   .alu .add a5 x0 a0,
   .alu .add (20 : Fin 32) x0 a1]
theorem ecE_end : blockEnd sigstoreVerifyCode 0x1398 ecE = some 0x13B0 := by decide

def ecP : List BInstr :=
  [.alu .sltu a3 a0 (22 : Fin 32),
   .lw a5 sp 0x74,
   .alu .sub a5 a1 a5,
   .alu .sub (20 : Fin 32) a5 a3,
   .aluImm .add (7 : Fin 32) x0 0x2,
   .alu .sltu a3 (7 : Fin 32) (23 : Fin 32),
   .alu .sub (9 : Fin 32) x0 (25 : Fin 32),
   .alu .sub a5 a0 (22 : Fin 32),
   .alu .sub (25 : Fin 32) (9 : Fin 32) a3,
   .alu .sltu a3 (8 : Fin 32) a4,
   .alu .sub (9 : Fin 32) (29 : Fin 32) (5 : Fin 32),
   .alu .sub (23 : Fin 32) (7 : Fin 32) (23 : Fin 32),
   .alu .sub (7 : Fin 32) (9 : Fin 32) a3,
   .alu .sltu a3 a2 (31 : Fin 32),
   .alu .sub (9 : Fin 32) (6 : Fin 32) (17 : Fin 32),
   .alu .sub (28 : Fin 32) (8 : Fin 32) a4,
   .alu .sub (30 : Fin 32) (9 : Fin 32) a3,
   .alu .sub (9 : Fin 32) a2 (31 : Fin 32),
   .alu .add (31 : Fin 32) x0 a2,
   .alu .add (17 : Fin 32) x0 (6 : Fin 32),
   .alu .add a4 x0 (8 : Fin 32),
   .alu .add (5 : Fin 32) x0 (29 : Fin 32),
   .alu .add (22 : Fin 32) x0 a0,
   .sw sp a1 0x74]
set_option maxHeartbeats 4000000 in
theorem ecP_end : blockEnd sigstoreVerifyCode 0x13C2 ecP = some 0x1412 := by decide

def ecN : List BInstr :=
  [.aluImm .add a3 (23 : Fin 32) 0x2,
   .alu .add a5 (22 : Fin 32) a0,
   .lw a0 sp 0x74,
   .alu .add a1 a1 a0,
   .alu .sltu (20 : Fin 32) a5 (22 : Fin 32),
   .alu .sltu a0 a3 (23 : Fin 32),
   .alu .add (20 : Fin 32) (20 : Fin 32) a1,
   .alu .add (25 : Fin 32) (25 : Fin 32) a0,
   .alu .add (28 : Fin 32) a4 (8 : Fin 32),
   .alu .sltu (7 : Fin 32) (28 : Fin 32) a4,
   .alu .add (29 : Fin 32) (29 : Fin 32) (5 : Fin 32),
   .alu .add (7 : Fin 32) (7 : Fin 32) (29 : Fin 32),
   .alu .add (9 : Fin 32) (31 : Fin 32) a2,
   .alu .sltu (30 : Fin 32) (9 : Fin 32) (31 : Fin 32),
   .alu .add (6 : Fin 32) (6 : Fin 32) (17 : Fin 32),
   .alu .add (30 : Fin 32) (30 : Fin 32) (6 : Fin 32),
   .alu .add (23 : Fin 32) x0 a3]
theorem ecN_end : blockEnd sigstoreVerifyCode 0x1414 ecN = some 0x1446 := by decide

def ecS : List BInstr :=
  [.aluImm .srl a5 a5 0x1,
   .aluImm .sll a0 (20 : Fin 32) 0x1F,
   .alu .or a0 a0 a5,
   .aluImm .srl a2 a4 0x1F,
   .aluImm .sll (5 : Fin 32) (5 : Fin 32) 0x1,
   .aluImm .sra a1 (20 : Fin 32) 0x1,
   .alu .or (5 : Fin 32) (5 : Fin 32) a2,
   .aluImm .srl a2 (31 : Fin 32) 0x1F,
   .aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x1,
   .aluImm .sll a4 a4 0x1,
   .alu .or (17 : Fin 32) (17 : Fin 32) a2,
   .aluImm .sll (31 : Fin 32) (31 : Fin 32) 0x1,
   .aluImm .add a6 a6 0xFFFFFFFF,
   .alu .add a2 x0 (9 : Fin 32),
   .alu .add (6 : Fin 32) x0 (30 : Fin 32),
   .alu .add (8 : Fin 32) x0 (28 : Fin 32),
   .alu .add (29 : Fin 32) x0 (7 : Fin 32)]
theorem ecS_end : blockEnd sigstoreVerifyCode 0x1446 ecS = some 0x1474 := by decide

def ecT : List BInstr := [.alu .slt a3 x0 (25 : Fin 32)]
theorem ecT_end : blockEnd sigstoreVerifyCode 0x13B6 ecT = some 0x13BA := by decide

def ecZ : List BInstr := [.alu .sltu a3 x0 (23 : Fin 32)]
theorem ecZ_end : blockEnd sigstoreVerifyCode 0x13BC ecZ = some 0x13C0 := by decide

set_option maxRecDepth 20000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
/-- The even case: `g` halves and the first row doubles. -/
theorem ecE_ok (M : Word → BitVec 8) (f : Fin 32 → Word) (hz : f 0 = 0) (s : Ds) (h : EcDsRegs M f s)
    (hg : s.g % 2 = 0) : EcDsRegs M (runBlock ecS (M, (runBlock ecE (M, f)).2)).2 (dsStep s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [dsStep, ite_eq_left hg]
  simp +decide only [EcDsRegs, runBlock, BInstr.run, ecE, ecS, upd, ↓reduceIte, aluEval, hz, BitVec.zero_add]
  simp only [W64, asr64, a0, a1, a2, a3, a4, a5, a6, BitVec.toNat_add, BitVec.toNat_sub, BitVec.ult, toNat_or_shl31,
    toNat_or_shl1, toNat_sra1, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at *
  have := (f 23).isLt; have := (f 25).isLt; have := (f 10).isLt; have := (f 11).isLt; have := (f 14).isLt
  have := (f 5).isLt; have := (f 31).isLt; have := (f 17).isLt; have := (f 22).isLt
  have := (memLoad32 M (f 2 + 0x74)).isLt
  have := (f 8).isLt; have := (f 29).isLt; have := (f 12).isLt; have := (f 6).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;>
    (try simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod] at *)
    <;> omega

set_option maxRecDepth 20000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
/-- The odd case with `δ ≤ 0`: `g` gains `f`, then halves. -/
theorem ecN_ok (M : Word → BitVec 8) (f : Fin 32 → Word) (hz : f 0 = 0) (s : Ds) (h : EcDsRegs M f s)
    (hg : s.g % 2 = 1) (hd : ¬ dsPos s.δ) : EcDsRegs M (runBlock ecS (M, (runBlock ecN (M, f)).2)).2 (dsStep s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [dsStep, ite_eq_right (show ¬ s.g % 2 = 0 by omega), ite_eq_right hd]
  simp +decide only [EcDsRegs, runBlock, BInstr.run, ecN, ecS, upd, ↓reduceIte, aluEval, hz, BitVec.zero_add, sp]
  simp only [W64, asr64, a0, a1, a2, a3, a4, a5, a6, BitVec.toNat_add, BitVec.toNat_sub, BitVec.ult, toNat_or_shl31,
    toNat_or_shl1, toNat_sra1, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at *
  have := (f 23).isLt; have := (f 25).isLt; have := (f 10).isLt; have := (f 11).isLt; have := (f 14).isLt
  have := (f 5).isLt; have := (f 31).isLt; have := (f 17).isLt; have := (f 22).isLt
  have := (memLoad32 M (f 2 + 0x74)).isLt
  have := (f 8).isLt; have := (f 29).isLt; have := (f 12).isLt; have := (f 6).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;>
    (try simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod] at *)
    <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
/-- The odd case with `δ > 0`: `f` and `g` swap, and `g` loses `f`, then halves. -/
theorem ecP_ok (M : Word → BitVec 8) (f : Fin 32 → Word) (hz : f 0 = 0) (s : Ds) (h : EcDsRegs M f s)
    (hg : s.g % 2 = 1) (hd : dsPos s.δ) :
    EcDsRegs (runBlock ecP (M, f)).1 (runBlock ecS ((runBlock ecP (M, f)).1, (runBlock ecP (M, f)).2)).2 (dsStep s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [dsStep, ite_eq_right (show ¬ s.g % 2 = 0 by omega), ite_eq_left hd]
  simp +decide only [EcDsRegs, runBlock, BInstr.run, ecP, ecS, upd, ↓reduceIte, aluEval, hz, BitVec.zero_add, sp,
    memLoad32_store32_same]
  simp only [W64, asr64, a0, a1, a2, a3, a4, a5, a6, BitVec.toNat_add, BitVec.toNat_sub, BitVec.ult, toNat_or_shl31,
    toNat_or_shl1, toNat_sra1, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at *
  have := (f 23).isLt; have := (f 25).isLt; have := (f 10).isLt; have := (f 11).isLt; have := (f 14).isLt
  have := (f 5).isLt; have := (f 31).isLt; have := (f 17).isLt; have := (f 22).isLt
  have := (memLoad32 M (f 2 + 0x74)).isLt
  have := (f 8).isLt; have := (f 29).isLt; have := (f 12).isLt; have := (f 6).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;>
    (try simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod] at *)
    <;> omega

end C3.RV32.Sv
