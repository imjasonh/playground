import C3BootProofs.Proofs.SvEc
import C3BootProofs.Proofs.Pv384Ds
import C3BootProofs.Proofs.Pv384CIt
import C3BootProofs.Proofs.Lowest
import C3BootProofs.Proofs.Prim

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

theorem EcDsRegs.congr {M : Word → BitVec 8} {f f' : Fin 32 → Word} {s : Ds} (h : EcDsRegs M f s)
    (e : ∀ q : Fin 32, q.val ∈ [2, 5, 6, 8, 10, 11, 12, 14, 17, 22, 23, 25, 29, 31] → f' q = f q) :
    EcDsRegs M f' s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [e 2 (by decide), e 5 (by decide), e 6 (by decide), e 8 (by decide), e 10 (by decide),
      e 11 (by decide), e 12 (by decide), e 14 (by decide), e 17 (by decide), e 22 (by decide), e 23 (by decide),
      e 25 (by decide), e 29 (by decide), e 31 (by decide)] <;> assumption

/-- The registers the loop keeps. -/
theorem ec_keep (M M' : Word → BitVec 8) (f : Fin 32 → Word) (hz : f 0 = 0) (X : List BInstr)
    (hX : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 16, 18, 19, 21, 24, 26, 27] → q ∉ X.filterMap BInstr.dst) :
    (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 24, 26, 27] → (runBlock ecS (M', (runBlock X (M, f)).2)).2 q = f q) ∧
      (runBlock ecS (M', (runBlock X (M, f)).2)).2 16 = f 16 + 0xFFFFFFFF := by
  have hz' : (runBlock X (M, f)).2 0 = 0 := runBlock_zero X M f hz
  constructor
  · intro q hq
    rw [runBlock_reg _ _ _ q hz' (by simp only [ecS]; revert hq; revert q; decide),
      runBlock_reg _ _ _ q hz (hX q (by revert hq; revert q; decide))]
  · have e : (runBlock X (M, f)).2 16 = f 16 := runBlock_reg _ _ _ 16 hz (hX 16 (by decide))
    simp +decide only [runBlock, BInstr.run, ecS, upd, ↓reduceIte, aluEval]
    rw [e]

/-- What one pass of the loop leaves: the step taken, the counter less one,
the other registers it keeps, memory changed at most in `f`'s high word, and
the code still in place. -/
def EcDsPost (Mx : Word → BitVec 8) (m : Machine) (s : Ds) (Mx' : Word → BitVec 8) (m' : Machine) (off : Nat) : Prop :=
  Steps m m' ∧ St Mx' SV m' off (reg m') ∧ EcDsRegs Mx' (reg m') s ∧
    (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 24, 26, 27] → reg m' q = reg m q) ∧
    (∀ x, Sep (reg m sp + 0x74) 4 x 1 → Mx' x = Mx x) ∧ CodeIn Mx' SV sigstoreVerifyCode

set_option maxHeartbeats 8000000 in
/-- **One divstep** of the loop at 0x1392, to the branch at 0x1474. -/
theorem ec_body {Mx : Word → BitVec 8} (hc : CodeIn Mx SV sigstoreVerifyCode) {m : Machine} {s : Ds}
    (st : St Mx SV m 0x1392 (reg m)) (h : EcDsRegs Mx (reg m) s)
    (hsa : (reg m sp + 0x74).toNat % 4 = 0) (hsc : Sep (reg m sp + 0x74) 4 SV sigstoreVerifyCode.length) :
    ∃ m' Mx', EcDsPost Mx m (dsStep s) Mx' m' 0x1474 ∧ reg m' 16 = reg m 16 + 0xFFFFFFFF := by
  have hz := st.zero
  obtain ⟨m1, c1, u1⟩ := st.block ecA hc ecA_end ⟨trivial, trivial⟩
  have s1 : St Mx SV m1 0x1396 (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have z1 := s1.zero
  have r1a3 : reg m1 a3 = reg m a0 &&& 1 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, ecA, upd, ↓reduceIte, aluEval]
  have r1k : ∀ q : Fin 32, q ≠ a3 → reg m1 q = reg m q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [ecA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simpa using hq)]
  have h1 : EcDsRegs Mx (reg m1) s := h.congr fun q hq => r1k q (by revert hq; revert q; decide)
  have sp1 : reg m1 sp = reg m sp := r1k sp (by decide)
  -- the shift and the counter, after the case's block, ending at 0x1474
  have fin : ∀ {m4 : Machine} {M4 : Word → BitVec 8} (X : List BInstr) (f0 : Fin 32 → Word), f0 0 = 0 →
      St M4 SV m4 0x1446 (reg m4) → reg m4 = (runBlock X (Mx, f0)).2 → Steps m m4 →
      EcDsRegs M4 (runBlock ecS (M4, (runBlock X (Mx, f0)).2)).2 (dsStep s) →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 16, 18, 19, 21, 24, 26, 27] → q ∉ X.filterMap BInstr.dst) →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 16, 18, 19, 21, 24, 26, 27] → f0 q = reg m q) →
      (∀ x, Sep (reg m sp + 0x74) 4 x 1 → M4 x = Mx x) → CodeIn M4 SV sigstoreVerifyCode →
      ∃ m' Mx', EcDsPost Mx m (dsStep s) Mx' m' 0x1474 ∧ reg m' 16 = reg m 16 + 0xFFFFFFFF := by
    intro m4 M4 X f0 hf0 s4 e4 c4 hd hX hk hM hC
    obtain ⟨m5, c5, u5⟩ := s4.block ecS hC ecS_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have e5 : reg m5 = (runBlock ecS (M4, (runBlock X (Mx, f0)).2)).2 := by
      funext q; rw [u5.regs, e4]
    obtain ⟨kk, kt⟩ := ec_keep Mx M4 f0 hf0 X hX
    refine ⟨m5, M4, ⟨c4.trans c5, ⟨u5.pc, u5.mem, fun _ => rfl⟩, by rw [e5]; exact hd, fun q hq => ?_, hM, hC⟩, ?_⟩
    · rw [e5, kk q hq, hk q (by revert hq; revert q; decide)]
    · rw [e5, kt, hk 16 (by decide)]
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 16, 18, 19, 21, 24, 26, 27] → reg m1 q = reg m q :=
    fun q hq => r1k q (by revert hq; revert q; decide)
  have pathN : ∀ {m5 : Machine}, St Mx SV m5 0x1414 (reg m5) → Steps m m5 → EcDsRegs Mx (reg m5) s →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 16, 18, 19, 21, 24, 26, 27] → reg m5 q = reg m q) → s.g % 2 = 1 →
      ¬ dsPos s.δ → ∃ m' Mx', EcDsPost Mx m (dsStep s) Mx' m' 0x1474 ∧ reg m' 16 = reg m 16 + 0xFFFFFFFF := by
    intro m5 s5 c5 h5 k5 hgo hnp
    have sp5 : reg m5 sp = reg m sp := k5 sp (by decide)
    obtain ⟨m6, c6, u6⟩ := s5.block ecN hc ecN_end ⟨trivial, trivial, by
      simp +decide only [BInstr.ok, BInstr.run, upd, ↓reduceIte]; rw [sp5]; exact hsa, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have M6 : (runBlock ecN (Mx, reg m5)).1 = Mx := by simp only [runBlock, BInstr.run, ecN]
    rw [M6] at u6
    exact fin ecN (reg m5) s5.zero ⟨u6.pc, u6.mem, fun _ => rfl⟩ (by funext q; rw [u6.regs]) (c5.trans c6)
      (ecN_ok Mx (reg m5) s5.zero s h5 hgo hnp) (by decide) k5 (fun _ _ => rfl) hc
  have pathP : ∀ {m5 : Machine}, St Mx SV m5 0x13C2 (reg m5) → Steps m m5 → EcDsRegs Mx (reg m5) s →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 16, 18, 19, 21, 24, 26, 27] → reg m5 q = reg m q) → s.g % 2 = 1 →
      dsPos s.δ → ∃ m' Mx', EcDsPost Mx m (dsStep s) Mx' m' 0x1474 ∧ reg m' 16 = reg m 16 + 0xFFFFFFFF := by
    intro m5 s5 c5 h5 k5 hgo hp
    have sp5 : reg m5 sp = reg m sp := k5 sp (by decide)
    have Pr : (runBlock ecP (Mx, reg m5)).2 sp = reg m sp := by
      rw [runBlock_reg _ _ _ sp s5.zero (by decide), sp5]
    obtain ⟨m6, c6, u6⟩ := s5.block ecP hc ecP_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, ecP, upd, ↓reduceIte, true_and, and_true]
      rw [sp5]; exact ⟨hsa, hsa, hsc⟩)
    have M6 : (runBlock ecP (Mx, reg m5)).1 = memStore32 Mx (reg m sp + 0x74) (reg m5 a1) := by
      simp +decide only [runBlock, BInstr.run, ecP, upd, ↓reduceIte]; rw [sp5]
    have C6 : CodeIn (runBlock ecP (Mx, reg m5)).1 SV sigstoreVerifyCode := by rw [M6]; exact hc.store32 hsc
    have s6 : St (runBlock ecP (Mx, reg m5)).1 SV m6 0x1412 (reg m6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
    obtain ⟨m7, d7, u7⟩ := s6.jump C6 sv_at_1412 (off' := 0x1446) (by decide) (by rw [s6.pc]; decide)
    exact fin ecP (reg m5) s5.zero u7.self (by funext q; rw [u7.regs, u6.regs]) (c5.trans (c6.trans (.single d7)))
      (ecP_ok Mx (reg m5) s5.zero s h5 hgo hp) (by decide) k5
      (fun x hx => by rw [M6, memStore32_get_sep hx]) C6
  have hδ := h1.1
  have hg := h1.2.2.1
  by_cases hge : s.g % 2 = 0
  · have ha3 : reg m1 a3 = 0 := by rw [r1a3, ← r1k 10 (by decide)]; exact (ds_odd hg).2 hge
    obtain ⟨m2, d2, u2⟩ := s1.notTaken hc 0x1398 sv_at_1396 (by decide)
      (by show (reg m1 a3 != reg m1 x0) = false; rw [ha3, z1]; rfl)
    have e2 : reg m2 = reg m1 := funext u2.regs
    obtain ⟨m3, c3, u3⟩ := u2.self.block ecE hc ecE_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial⟩
    have M3 : (runBlock ecE (Mx, reg m2)).1 = Mx := by simp only [runBlock, BInstr.run, ecE]
    rw [M3] at u3
    have s3 : St Mx SV m3 0x13B0 (reg m3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
    obtain ⟨m4, d4, u4⟩ := s3.jump hc sv_at_13b0 (off' := 0x1446) (by decide) (by rw [s3.pc]; decide)
    exact fin ecE (reg m1) z1 u4.self (by funext q; rw [u4.regs, u3.regs, e2])
      (c1.trans (.cons d2 (c3.trans (.single d4)))) (ecE_ok Mx (reg m1) z1 s h1 hge) (by decide) k1
      (fun _ _ => rfl) hc
  have hgo : s.g % 2 = 1 := by omega
  have ha3 : reg m1 a3 ≠ 0 := by
    rw [r1a3, ← r1k 10 (by decide)]; exact fun h0 => hge ((ds_odd hg).1 h0)
  obtain ⟨m2, d2, u2⟩ := s1.taken hc 0x13B2 sv_at_1396 (by decide)
    (by show (reg m1 a3 != reg m1 x0) = true; rw [z1]; simpa using ha3)
  have e2 : reg m2 = reg m1 := funext u2.regs
  by_cases h25 : reg m1 25 = 0
  · obtain ⟨m3, d3, u3⟩ := u2.self.taken hc 0x13BC sv_at_13b2 (by decide)
      (by show (reg m2 25 == reg m2 x0) = true; rw [e2, h25, z1]; rfl)
    have e3 : reg m3 = reg m1 := by funext q; rw [u3.regs, e2]
    obtain ⟨m4, c4, u4⟩ := u3.self.block ecZ hc ecZ_end ⟨trivial, trivial⟩
    have M4 : (runBlock ecZ (Mx, reg m3)).1 = Mx := by simp only [runBlock, BInstr.run, ecZ]
    rw [M4] at u4
    have s4 : St Mx SV m4 0x13C0 (reg m4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    have r4a3 : reg m4 a3 = if (0 : Word).ult (reg m1 23) then 1 else 0 := by
      rw [u4.regs, e3]; simp +decide only [runBlock, BInstr.run, ecZ, upd, ↓reduceIte, aluEval, z1]
    have r4k : ∀ q : Fin 32, q ≠ a3 → reg m4 q = reg m1 q := fun q hq => by
      rw [u4.regs, e3, runBlock_reg _ _ _ q z1
        (by simp only [ecZ, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simpa using hq)]
    have h4 : EcDsRegs Mx (reg m4) s := h1.congr fun q hq => r4k q (by revert hq; revert q; decide)
    have k4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 16, 18, 19, 21, 24, 26, 27] → reg m4 q = reg m q :=
      fun q hq => by rw [r4k q (by revert hq; revert q; decide), k1 q hq]
    by_cases h23 : reg m1 23 = 0
    · have hnp : ¬ dsPos s.δ := by rw [ds_pos_lo hδ h25]; simpa using h23
      obtain ⟨m5, d5, u5⟩ := s4.taken hc 0x1414 sv_at_13c0 (by decide)
        (by show (reg m4 a3 == reg m4 x0) = true; rw [r4a3, h23, s4.zero]; decide)
      exact pathN u5.self (c1.trans (.cons d2 (.cons d3 (c4.trans (.single d5)))))
        (h4.congr fun q _ => u5.regs q) (fun q hq => by rw [u5.regs, k4 q hq]) hgo hnp
    · have hp : dsPos s.δ := by rw [ds_pos_lo hδ h25]; exact h23
      have hu : (0 : Word).ult (reg m1 23) = true := by
        simp only [BitVec.ult, decide_eq_true_eq]; exact Nat.pos_of_ne_zero fun e => h23 (BitVec.eq_of_toNat_eq e)
      obtain ⟨m5, d5, u5⟩ := s4.notTaken hc 0x13C2 sv_at_13c0 (by decide)
        (by show (reg m4 a3 == reg m4 x0) = false; rw [r4a3, hu, s4.zero]; decide)
      exact pathP u5.self (c1.trans (.cons d2 (.cons d3 (c4.trans (.single d5)))))
        (h4.congr fun q _ => u5.regs q) (fun q hq => by rw [u5.regs, k4 q hq]) hgo hp
  · obtain ⟨m3, d3, u3⟩ := u2.self.notTaken hc 0x13B6 sv_at_13b2 (by decide)
      (by show (reg m2 25 == reg m2 x0) = false; rw [e2, z1]; simpa using h25)
    have e3 : reg m3 = reg m1 := by funext q; rw [u3.regs, e2]
    obtain ⟨m4, c4, u4⟩ := u3.self.block ecT hc ecT_end ⟨trivial, trivial⟩
    have M4 : (runBlock ecT (Mx, reg m3)).1 = Mx := by simp only [runBlock, BInstr.run, ecT]
    rw [M4] at u4
    have s4' : St Mx SV m4 0x13BA (reg m4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    obtain ⟨m4', d4', u4'⟩ := s4'.jump hc sv_at_13ba (off' := 0x13C0) (by decide) (by rw [s4'.pc]; decide)
    have s4 : St Mx SV m4' 0x13C0 (reg m4') := u4'.self
    have r4a3 : reg m4' a3 = if (0 : Word).slt (reg m1 25) then 1 else 0 := by
      rw [u4'.regs, u4.regs, e3]; simp +decide only [runBlock, BInstr.run, ecT, upd, ↓reduceIte, aluEval, z1]
    have r4k : ∀ q : Fin 32, q ≠ a3 → reg m4' q = reg m1 q := fun q hq => by
      rw [u4'.regs, u4.regs, e3, runBlock_reg _ _ _ q z1
        (by simp only [ecT, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simpa using hq)]
    have h4 : EcDsRegs Mx (reg m4') s := h1.congr fun q hq => r4k q (by revert hq; revert q; decide)
    have k4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 16, 18, 19, 21, 24, 26, 27] → reg m4' q = reg m q :=
      fun q hq => by rw [r4k q (by revert hq; revert q; decide), k1 q hq]
    have c4' : Steps m m4' := c1.trans (.cons d2 (.cons d3 (c4.trans (.single d4'))))
    by_cases hs : (0 : Word).slt (reg m1 25) = true
    · have hp : dsPos s.δ := (ds_pos_hi hδ h25).2 hs
      obtain ⟨m5, d5, u5⟩ := s4.notTaken hc 0x13C2 sv_at_13c0 (by decide)
        (by show (reg m4' a3 == reg m4' x0) = false; rw [r4a3, hs, s4.zero]; decide)
      exact pathP u5.self (c4'.trans (.single d5))
        (h4.congr fun q _ => u5.regs q) (fun q hq => by rw [u5.regs, k4 q hq]) hgo hp
    · have hnp : ¬ dsPos s.δ := fun hp => hs ((ds_pos_hi hδ h25).1 hp)
      obtain ⟨m5, d5, u5⟩ := s4.taken hc 0x1414 sv_at_13c0 (by decide)
        (by show (reg m4' a3 == reg m4' x0) = true; rw [r4a3, Bool.not_eq_true _ |>.mp hs, s4.zero]; decide)
      exact pathN u5.self (c4'.trans (.single d5))
        (h4.congr fun q _ => u5.regs q) (fun q hq => by rw [u5.regs, k4 q hq]) hgo hnp

/-- **The divstep loop** at 0x1392, with `k + 1` steps left in `a6`, runs
them all and leaves at 0x1478. -/
theorem ec_loop (k : Nat) :
    ∀ {m : Machine} {Mx : Word → BitVec 8} {s : Ds}, CodeIn Mx SV sigstoreVerifyCode → St Mx SV m 0x1392 (reg m) →
      EcDsRegs Mx (reg m) s → reg m 16 = BitVec.ofNat 32 (k + 1) → k + 1 < 2 ^ 32 →
      (reg m sp + 0x74).toNat % 4 = 0 → Sep (reg m sp + 0x74) 4 SV sigstoreVerifyCode.length →
      ∃ m' Mx', EcDsPost Mx m (dsIter (k + 1) s) Mx' m' 0x1478 := by
  induction k with
  | zero =>
    intro m Mx s hc st h h16 _ hsa hsc
    obtain ⟨m1, M1, ⟨c1, s1, h1, k1, f1, C1⟩, t1⟩ := ec_body hc st h hsa hsc
    have e : reg m1 16 = 0 := by rw [t1, h16]; decide
    obtain ⟨m2, d2, u2⟩ := s1.notTaken C1 0x1478 sv_at_1474 (by decide)
      (by show (reg m1 16 != reg m1 x0) = false; rw [e, s1.zero]; rfl)
    exact ⟨m2, M1, c1.trans (.single d2), u2.self, h1.congr fun q _ => u2.regs q,
      fun q hq => by rw [u2.regs, k1 q hq], f1, C1⟩
  | succ k ih =>
    intro m Mx s hc st h h16 hk hsa hsc
    obtain ⟨m1, M1, ⟨c1, s1, h1, k1, f1, C1⟩, t1⟩ := ec_body hc st h hsa hsc
    have e : reg m1 16 = BitVec.ofNat 32 (k + 1) := by
      rw [t1, h16]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl,
        show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_add_mod,
        show k + 1 + 1 + 4294967295 = k + 1 + 4294967296 by omega, Nat.add_mod_right]
    have hne : reg m1 16 ≠ 0 := by
      rw [e]; intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (0 : Word).toNat = 0 from rfl] at this
      omega
    obtain ⟨m2, d2, u2⟩ := s1.taken C1 0x1392 sv_at_1474 (by decide)
      (by show (reg m1 16 != reg m1 x0) = true; rw [s1.zero]; simpa using hne)
    have sp2 : reg m2 sp = reg m sp := by rw [u2.regs, k1 sp (by decide)]
    obtain ⟨m3, M3, c3, s3, h3, k3, f3, C3⟩ := ih C1 u2.self (h1.congr fun q _ => u2.regs q) (by rw [u2.regs, e])
      (by omega) (by rw [sp2]; exact hsa) (by rw [sp2]; exact hsc)
    refine ⟨m3, M3, c1.trans (.cons d2 c3), s3, h3, fun q hq => by rw [k3 q hq, u2.regs, k1 q hq],
      fun x hx => by rw [f3 x (by rw [sp2]; exact hx), f1 x hx], C3⟩

def ecScB : List BInstr := [.lw a2 a1 0x0, .aluImm .add a0 a0 0x1, .aluImm .add a1 a1 0x4]
theorem ecScB_end : blockEnd sigstoreVerifyCode 0x133E ecScB = some 0x1344 := by decide
def ecScA : List BInstr := [.aluImm .add a2 x0 0x7]
theorem ecScA_end : blockEnd sigstoreVerifyCode 0x1338 ecScA = some 0x133A := by decide
def ecScC : List BInstr := [.aluImm .add a1 x0 0x7]
theorem ecScC_end : blockEnd sigstoreVerifyCode 0x1346 ecScC = some 0x1348 := by decide

set_option maxHeartbeats 4000000 in
/-- **The scan** at 0x1338 for a nonzero limb of `g` at offset 0x1480, from
limb `i`: to 0x1556 when all 8 are zero, and to 0x134C otherwise. -/
theorem ec_scan {Mx : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (hc : CodeIn Mx SV sigstoreVerifyCode) :
    ∀ j i {m : Machine}, i + j = 8 → St Mx SV m 0x1338 (reg m) → reg m a0 = BitVec.ofNat 32 i + 0xFFFFFFFF →
      reg m a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 + BitVec.ofNat 32 (4 * i) →
      (∀ k, k < i → memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x1480 + BitVec.ofNat 32 (4 * k)) = 0) →
      ∃ m', Steps m m' ∧ (∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m' q = reg m q) ∧
        (((∀ k, k < 8 → memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x1480 + BitVec.ofNat 32 (4 * k)) = 0) ∧
          St Mx SV m' 0x1556 (reg m')) ∨
         ((¬ ∀ k, k < 8 → memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x1480 + BitVec.ofNat 32 (4 * k)) = 0) ∧
          St Mx SV m' 0x134C (reg m'))) := by
  intro j
  induction j with
  | zero =>
    intro i m hij st h0 _ hz
    obtain rfl : i = 8 := by omega
    obtain ⟨m1, c1, u1⟩ := st.block ecScA hc ecScA_end ⟨trivial, trivial⟩
    have s1 : St Mx SV m1 0x133A (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
    have r1a2 : reg m1 a2 = BitVec.ofNat 32 7 := by
      rw [u1.regs]; simp +decide only [runBlock, BInstr.run, ecScA, upd, ↓reduceIte, aluEval, st.zero]
    have k1 : ∀ q : Fin 32, q ≠ a2 → reg m1 q = reg m q := fun q h => by
      have hq : q ∉ ecScA.filterMap BInstr.dst := by
        simp only [ecScA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simpa using h
      rw [u1.regs, runBlock_reg _ _ _ q st.zero hq]
    obtain ⟨m2, d2, u2⟩ := s1.taken hc 0x1556 sv_at_133a (by decide)
      (by show (reg m1 a0 == reg m1 a2) = true; rw [k1 a0 (by decide), h0, r1a2]; decide)
    exact ⟨m2, c1.trans (.single d2), fun q _ _ h2' => by rw [u2.regs, k1 q h2'], .inl ⟨hz, u2.self⟩⟩
  | succ j ih =>
    intro i m hij st h0 h1 hz
    have hi : i < 8 := by omega
    obtain ⟨m1, c1, u1⟩ := st.block ecScA hc ecScA_end ⟨trivial, trivial⟩
    have s1 : St Mx SV m1 0x133A (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
    have r1a2 : reg m1 a2 = BitVec.ofNat 32 7 := by
      rw [u1.regs]; simp +decide only [runBlock, BInstr.run, ecScA, upd, ↓reduceIte, aluEval, st.zero]
    have k1 : ∀ q : Fin 32, q ≠ a2 → reg m1 q = reg m q := fun q h => by
      have hq : q ∉ ecScA.filterMap BInstr.dst := by
        simp only [ecScA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simpa using h
      rw [u1.regs, runBlock_reg _ _ _ q st.zero hq]
    have hne : reg m1 a0 ≠ reg m1 a2 := by
      rw [k1 a0 (by decide), h0, r1a2]
      cases i with
      | zero => decide
      | succ i =>
        rw [ofNat_pred i]; intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
    obtain ⟨m2, d2, u2⟩ := s1.notTaken hc 0x133E sv_at_133a (by decide)
      (by show (reg m1 a0 == reg m1 a2) = false; simpa using hne)
    have hal : (B + 0x21A0 + BitVec.ofNat 32 0x1480 + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0 := by
      rw [add_ofNat_assoc]; exact sv_al F (by omega) (by omega)
    have e2 : reg m2 = reg m1 := funext u2.regs
    obtain ⟨m3, c3, u3⟩ := u2.self.block ecScB hc ecScB_end
      ⟨by show (reg m2 a1 + 0x0).toNat % 4 = 0
          rw [e2, k1 a1 (by decide), h1, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]; exact hal,
        trivial, trivial, trivial⟩
    have s3 : St Mx SV m3 0x1344 (reg m3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
    have r3a2 : reg m3 a2 = memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x1480 + BitVec.ofNat 32 (4 * i)) := by
      rw [u3.regs, e2]; simp +decide only [runBlock, BInstr.run, ecScB, upd, ↓reduceIte, aluEval]
      rw [k1 a1 (by decide), h1, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]
    have r3a0 : reg m3 a0 = BitVec.ofNat 32 i := by
      rw [u3.regs, e2]; simp +decide only [runBlock, BInstr.run, ecScB, upd, ↓reduceIte, aluEval]
      rw [k1 a0 (by decide), h0, BitVec.add_assoc, show (0xFFFFFFFF : Word) + 0x1 = 0 from rfl]; exact BitVec.add_zero _
    have r3a1 : reg m3 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [u3.regs, e2]; simp +decide only [runBlock, BInstr.run, ecScB, upd, ↓reduceIte, aluEval]
      rw [k1 a1 (by decide), h1, BitVec.add_assoc, show BitVec.ofNat 32 (4 * i) + 0x4 = BitVec.ofNat 32 (4 * (i + 1)) by
        rw [show (0x4 : Word) = BitVec.ofNat 32 4 from rfl, BitVec.ofNat_add_ofNat, show 4 * i + 4 = 4 * (i + 1) by omega]]
    have k3 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m3 q = reg m q := fun q h0' h1' h2' => by
      have hq : q ∉ ecScB.filterMap BInstr.dst := by
        simp only [ecScB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0', h1', h2']
      rw [u3.regs, e2, runBlock_reg _ _ _ q s1.zero hq, k1 q h2']
    by_cases hw : memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x1480 + BitVec.ofNat 32 (4 * i)) = 0
    · obtain ⟨m4, d4, u4⟩ := s3.taken hc 0x1338 sv_at_1344 (by decide)
        (by show (reg m3 a2 == reg m3 x0) = true; rw [r3a2, hw, s3.zero]; rfl)
      obtain ⟨m5, c5, k5, h5⟩ := ih (i + 1) (by omega) u4.self (by rw [u4.regs, r3a0, ofNat_pred i])
        (by rw [u4.regs, r3a1])
        (fun k hk => by
          rcases Nat.lt_or_ge k i with h | h
          · exact hz k h
          · obtain rfl : k = i := by omega
            exact hw)
      exact ⟨m5, c1.trans (.cons d2 (c3.trans (.cons d4 c5))), fun q h0' h1' h2' => by
        rw [k5 q h0' h1' h2', u4.regs, k3 q h0' h1' h2'], h5⟩
    · obtain ⟨m4, d4, u4⟩ := s3.notTaken hc 0x1346 sv_at_1344 (by decide)
        (by show (reg m3 a2 == reg m3 x0) = false; rw [r3a2, s3.zero]; simpa using hw)
      obtain ⟨m5, c5, u5⟩ := u4.self.block ecScC hc ecScC_end ⟨trivial, trivial⟩
      have s5 : St Mx SV m5 0x1348 (reg m5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
      obtain ⟨m6, d6, u6⟩ := s5.notTaken hc 0x134C sv_at_1348 (by decide)
        (by
          show (reg m5 a1).ult (reg m5 a0) = false
          rw [u5.regs, u5.regs]
          simp +decide only [runBlock, BInstr.run, ecScC, upd, ↓reduceIte, aluEval, u4.regs, s3.zero]
          rw [r3a0]
          simp only [BitVec.ult, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega)]
          have : (0x7 : Word).toNat = 7 := rfl
          have : ((0 : Word) + 0x7).toNat = 7 := rfl
          simp only [decide_eq_false_iff_not]; omega)
      exact ⟨m6, c1.trans (.cons d2 (c3.trans (.cons d4 (c5.trans (.single d6))))), fun q h0' h1' h2' => by
        have hq : q ∉ ecScC.filterMap BInstr.dst := by
          simp only [ecScC, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simpa using h1'
        rw [u6.regs, u5.regs, runBlock_reg _ _ _ q (by rw [u4.regs]; exact s3.zero) hq,
          u4.regs, k3 q h0' h1' h2'], .inr ⟨fun h => hw (h i hi), u6.self⟩⟩

theorem sv_sp1 (B : Word) : B + 0x21A0 + 0xFFFFFFFF = B + BitVec.ofNat 32 0x219F := by
  rw [BitVec.add_assoc]; rfl

theorem svR_sp1 {B x : Word} (hx : SvR B x) : Sep (B + BitVec.ofNat 32 0x219F) 1 x 1 := by
  have := svR_lo (k := 1) hx (by decide) (by decide)
  rwa [sv_lo B 1 (by decide)] at this

/-- The inversion's code beyond `SvEcCode`. -/
structure SvIvCode (M : Word → BitVec 8) : Prop where
  umin : CodeIn M (BitVec.ofNat 32 u32MinAddress) u32MinCode
  low8 : CodeIn M (BitVec.ofNat 32 lowest8Address) lowest8Code
  sel64 : CodeIn M (BitVec.ofNat 32 selectI64Address) selectI64Code

theorem SvIvCode.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : SvIvCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvIvCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.umin (by decide) (by decide) hx, codeHi D.low8 (by decide) (by decide) hx,
    codeHi D.sel64 (by decide) (by decide) hx⟩

/-- **A call to `u32::min(a0, 62)`**. -/
theorem sv_uminF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o a : Word}
    (F : Fr B 0x3830) (C : SvCode M) (IC : SvIvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 u32MinAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = a) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = (if a.toNat < 62 then a else 62) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := u32Min_correct n1 (base := BitVec.ofNat 32 u32MinAddress)
    (by rw [mem1]; exact IC.umin) pc1 (by rw [r1 a0 (by decide), ha0])
    (by rw [sp1, sv_sp1]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [sp1, sv_sp1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [k2 sp (by decide) (by decide) (by decide)
    (by decide), sp1], fun r hr => ?_, a02, fun e he _ => ?_, fun x hx => ?_⟩
  · have hr' : r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ ra := by revert hr; revert r; decide
    obtain ⟨q10, q11, q12, q13, q1⟩ := hr'
    rw [k2 r q10 q11 q12 q13, r1 r q1]
  · rw [f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)), mem1]
  · rw [f2 x (svR_sp1 hx), mem1]

/-- **A call to `lowest` on 8 limbs** at offset `oc`, whose sign byte is at
`oc + 0x20`. -/
theorem sv_low8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {oc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (IC : SvIvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 lowest8Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ho : oc + 0x24 ≤ 0x1690) (ho4 : oc % 4 = 0)
    (hσ : (M (B + 0x21A0 + BitVec.ofNat 32 (oc + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (reg n' a0).toNat + 2 ^ 32 * (reg n' a1).toNat =
        lowestVal (M (B + 0x21A0 + BitVec.ofNat 32 (oc + 0x20))).toNat (accV M (B + 0x21A0 + BitVec.ofNat 32 oc) 2) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  have eS : BitVec.ofNat 32 lowest8Address + 0x22 = BitVec.ofNat 32 selectI64Address := by decide
  obtain ⟨n2, c2, pc2, sp2, k2, L2, f2⟩ := lowest8_correct n1 (P := BitVec.ofNat 32 lowest8Address)
    (by decide) (by rw [mem1]; exact IC.low8) (by rw [mem1, eS]; exact IC.sel64) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (sv_al F (by omega) ho4) (by rw [mem1, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]; exact hσ)
    (by rw [sp1, sv_sp1, eS]; exact F.sepHi (by decide) (by decide) (by decide))
  rw [mem1, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc] at L2
  rw [sp1, sv_sp1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, sp1],
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], L2,
    fun e he _ => ?_, fun x hx => ?_⟩
  · rw [f2 _ (fun h => by
      have := (sepS B (c := 0x219F) (n := 1) (d := 0x21A0 + e) (k := 1) (by omega) (by omega) (by omega)) 0
        (by decide) 0 (by decide)
      rw [add_ofNat_zero, add_ofNat_zero] at this; rw [← sv_base'] at h; exact this h.symm), mem1]
  · rw [f2 x (fun h => by
      have := svR_sp1 hx 0 (by decide) 0 (by decide)
      rw [add_ofNat_zero, add_ofNat_zero] at this; exact this h.symm), mem1]

end C3.RV32.Sv
