import C3BootProofs.Proofs.Pv384Lib

/-!
# `p384_verify_prehash`: the divstep batch

The inversion of `s` runs batches of up to 62 variable-time divsteps inline,
on the low 64 bits of `f` and `g`, a 64-bit `δ`, and a 2×2 matrix of 64-bit
entries, each held in a pair of registers. `dsStep` is one divstep on those
64-bit words, as naturals below `2 ^ 64`; this file proves the loop at 0x44E
runs `dsStep` once per iteration.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The 64-bit word whose low half is `lo` and high half `hi`. -/
abbrev W64 (lo hi : Word) : Nat := lo.toNat + 2 ^ 32 * hi.toNat

/-- Arithmetic shift right by one of a 64-bit word. -/
def asr64 (x : Nat) : Nat := x / 2 + (if 2 ^ 63 ≤ x then 2 ^ 63 else 0)

/-- `δ`, as a signed 64-bit word, is positive. -/
def dsPos (δ : Nat) : Prop := δ ≠ 0 ∧ δ < 2 ^ 63

instance (δ : Nat) : Decidable (dsPos δ) := inferInstanceAs (Decidable (_ ∧ _))

/-- The state of a divstep batch: `δ`, the low 64 bits of `f` and `g`, and
the matrix `[[u, v], [q, r]]`, each a 64-bit word. -/
structure Ds where
  δ : Nat
  f : Nat
  g : Nat
  u : Nat
  v : Nat
  q : Nat
  r : Nat

/-- One variable-time divstep. -/
def dsStep (s : Ds) : Ds :=
  if s.g % 2 = 0 then
    ⟨(s.δ + 2) % 2 ^ 64, s.f, asr64 s.g, 2 * s.u % 2 ^ 64, 2 * s.v % 2 ^ 64, s.q, s.r⟩
  else if dsPos s.δ then
    ⟨(2 + 2 ^ 64 - s.δ) % 2 ^ 64, s.g, asr64 ((s.g + 2 ^ 64 - s.f) % 2 ^ 64), 2 * s.q % 2 ^ 64,
      2 * s.r % 2 ^ 64, (s.q + 2 ^ 64 - s.u) % 2 ^ 64, (s.r + 2 ^ 64 - s.v) % 2 ^ 64⟩
  else
    ⟨(s.δ + 2) % 2 ^ 64, s.f, asr64 ((s.g + s.f) % 2 ^ 64), 2 * s.u % 2 ^ 64, 2 * s.v % 2 ^ 64,
      (s.q + s.u) % 2 ^ 64, (s.r + s.v) % 2 ^ 64⟩

/-- `n` divsteps. -/
def dsIter : Nat → Ds → Ds
  | 0, s => s
  | n + 1, s => dsIter n (dsStep s)

/-- The registers hold the batch's state: `δ` in `s5:s3`, `f` in `s11:s9`,
`g` in `a1:a0`, `u` in `a7:s1`, `v` in `a6:a2`, `q` in `t2:s8`, and `r` in
`t1:t5`. -/
def DsRegs (f : Fin 32 → Word) (s : Ds) : Prop :=
  W64 (f 21) (f 19) = s.δ ∧ W64 (f 27) (f 25) = s.f ∧ W64 (f 10) (f 11) = s.g ∧ W64 (f 9) (f 17) = s.u ∧
    W64 (f 12) (f 16) = s.v ∧ W64 (f 24) (f 7) = s.q ∧ W64 (f 30) (f 6) = s.r

theorem toNat_or_shl31 (a b : Word) : (a <<< 31 ||| b >>> 1).toNat = a.toNat % 2 * 2 ^ 31 + b.toNat / 2 := by
  have hb : (b >>> 1).toNat < 2 ^ 31 := by rw [BitVec.toNat_ushiftRight]; have := b.isLt; simp only [Nat.shiftRight_eq_div_pow]; omega
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  have e : (a.toNat <<< 31) % 2 ^ 32 = (a.toNat % 2) <<< 31 := by
    simp only [Nat.shiftLeft_eq]; have := a.isLt; omega
  rw [e, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals omega

theorem toNat_or_shl1 (a b : Word) : (a <<< 1 ||| b >>> 31).toNat = a.toNat * 2 % 2 ^ 32 + b.toNat / 2 ^ 31 := by
  have hb : (b >>> 31).toNat < 2 ^ 1 := by rw [BitVec.toNat_ushiftRight]; have := b.isLt; simp only [Nat.shiftRight_eq_div_pow]; omega
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  have e : (a.toNat <<< 1) % 2 ^ 32 = (a.toNat % 2 ^ 31) <<< 1 := by
    simp only [Nat.shiftLeft_eq]; have := a.isLt; omega
  rw [e, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals omega

theorem toNat_sra1 (a : Word) : (a.sshiftRight 1).toNat = a.toNat / 2 + (if 2 ^ 31 ≤ a.toNat then 2 ^ 31 else 0) := by
  have := a.isLt
  rw [BitVec.toNat_sshiftRight, BitVec.msb_eq_decide]
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one, show (32 - 1 : Nat) = 31 from rfl]
  by_cases h : 2 ^ 31 ≤ a.toNat
  · rw [decide_eq_true h, ite_eq_left rfl, ite_eq_left h]; omega
  · rw [decide_eq_false h, ite_eq_right (by decide), ite_eq_right h]; omega

def dsA : List BInstr :=
  [.aluImm .and a3 a0 0x1]
theorem dsA_end : blockEnd p384VerifyPrehashCode 0x44E dsA = some 0x452 := by decide

def dsE : List BInstr :=
  [.aluImm .add a3 (21 : Fin 32) 0x2,
   .alu .add a4 x0 (30 : Fin 32),
   .alu .add (31 : Fin 32) x0 (6 : Fin 32),
   .alu .sltu a5 a3 (21 : Fin 32),
   .alu .add (28 : Fin 32) x0 (24 : Fin 32),
   .alu .add (19 : Fin 32) (19 : Fin 32) a5,
   .alu .add (29 : Fin 32) x0 (7 : Fin 32),
   .alu .add (21 : Fin 32) x0 a3,
   .alu .add a5 x0 a0,
   .alu .add a3 x0 a1]
theorem dsE_end : blockEnd p384VerifyPrehashCode 0x454 dsE = some 0x46C := by decide

def dsN : List BInstr :=
  [.aluImm .add ra (21 : Fin 32) 0x2,
   .alu .add a5 (27 : Fin 32) a0,
   .alu .add a1 a1 (25 : Fin 32),
   .alu .sltu a3 a5 (27 : Fin 32),
   .alu .sltu a0 ra (21 : Fin 32),
   .alu .add a3 a3 a1,
   .alu .add (19 : Fin 32) (19 : Fin 32) a0,
   .alu .add (28 : Fin 32) (9 : Fin 32) (24 : Fin 32),
   .alu .sltu (29 : Fin 32) (28 : Fin 32) (9 : Fin 32),
   .alu .add (7 : Fin 32) (7 : Fin 32) (17 : Fin 32),
   .alu .add (29 : Fin 32) (29 : Fin 32) (7 : Fin 32),
   .alu .add a4 a2 (30 : Fin 32),
   .alu .sltu (31 : Fin 32) a4 a2,
   .alu .add (6 : Fin 32) (6 : Fin 32) a6,
   .alu .add (31 : Fin 32) (31 : Fin 32) (6 : Fin 32),
   .alu .add (21 : Fin 32) x0 ra]
theorem dsN_end : blockEnd p384VerifyPrehashCode 0x478 dsN = some 0x4A8 := by decide

def dsP : List BInstr :=
  [.alu .sltu a3 a0 (27 : Fin 32),
   .alu .sub a4 a1 (25 : Fin 32),
   .alu .sub a3 a4 a3,
   .aluImm .add (28 : Fin 32) x0 0x2,
   .alu .sltu a4 (28 : Fin 32) (21 : Fin 32),
   .alu .sub (8 : Fin 32) x0 (19 : Fin 32),
   .alu .sub a5 a0 (27 : Fin 32),
   .alu .sub (19 : Fin 32) (8 : Fin 32) a4,
   .alu .sltu a4 (24 : Fin 32) (9 : Fin 32),
   .alu .sub (8 : Fin 32) (7 : Fin 32) (17 : Fin 32),
   .alu .sub (21 : Fin 32) (28 : Fin 32) (21 : Fin 32),
   .alu .sub (29 : Fin 32) (8 : Fin 32) a4,
   .alu .sltu a4 (30 : Fin 32) a2,
   .alu .sub (8 : Fin 32) (6 : Fin 32) a6,
   .alu .sub (28 : Fin 32) (24 : Fin 32) (9 : Fin 32),
   .alu .sub (31 : Fin 32) (8 : Fin 32) a4,
   .alu .sub a4 (30 : Fin 32) a2,
   .alu .add a2 x0 (30 : Fin 32),
   .alu .add a6 x0 (6 : Fin 32),
   .alu .add (9 : Fin 32) x0 (24 : Fin 32),
   .alu .add (17 : Fin 32) x0 (7 : Fin 32),
   .alu .add (27 : Fin 32) x0 a0,
   .alu .add (25 : Fin 32) x0 a1]
theorem dsP_end : blockEnd p384VerifyPrehashCode 0x4B0 dsP = some 0x4FE := by decide

def dsS : List BInstr :=
  [.aluImm .srl a5 a5 0x1,
   .aluImm .sll a0 a3 0x1F,
   .alu .or a0 a0 a5,
   .aluImm .srl a5 (9 : Fin 32) 0x1F,
   .aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x1,
   .aluImm .sra a1 a3 0x1,
   .alu .or (17 : Fin 32) (17 : Fin 32) a5,
   .aluImm .srl a3 a2 0x1F,
   .aluImm .sll a6 a6 0x1,
   .aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x1,
   .alu .or a6 a6 a3,
   .aluImm .sll a2 a2 0x1,
   .aluImm .add (5 : Fin 32) (5 : Fin 32) 0xFFFFFFFF,
   .alu .add (30 : Fin 32) x0 a4,
   .alu .add (6 : Fin 32) x0 (31 : Fin 32),
   .alu .add (24 : Fin 32) x0 (28 : Fin 32),
   .alu .add (7 : Fin 32) x0 (29 : Fin 32)]
theorem dsS_end : blockEnd p384VerifyPrehashCode 0x4FE dsS = some 0x52C := by decide

def dsT : List BInstr :=
  [.alu .slt a3 x0 (19 : Fin 32)]
theorem dsT_end : blockEnd p384VerifyPrehashCode 0x472 dsT = some 0x476 := by decide

def dsZ : List BInstr :=
  [.alu .sltu a3 x0 (21 : Fin 32)]
theorem dsZ_end : blockEnd p384VerifyPrehashCode 0x4AA dsZ = some 0x4AE := by decide

set_option maxRecDepth 20000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
/-- The even case: `g` halves and the first row doubles. -/
theorem dsE_ok (M : Word → BitVec 8) (f : Fin 32 → Word) (hz : f 0 = 0) (s : Ds) (h : DsRegs f s)
    (hg : s.g % 2 = 0) : DsRegs (runBlock dsS (M, (runBlock dsE (M, f)).2)).2 (dsStep s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [dsStep, ite_eq_left hg]
  simp +decide only [DsRegs, runBlock, BInstr.run, dsE, dsS, upd, ↓reduceIte, aluEval, hz, BitVec.zero_add]
  simp only [W64, asr64, a0, a1, a2, a3, a4, a5, a6, BitVec.toNat_add, BitVec.toNat_sub, BitVec.ult, toNat_or_shl31,
    toNat_or_shl1, toNat_sra1, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at *
  have := (f 21).isLt; have := (f 19).isLt; have := (f 10).isLt; have := (f 11).isLt; have := (f 9).isLt
  have := (f 17).isLt; have := (f 12).isLt; have := (f 16).isLt; have := (f 27).isLt; have := (f 25).isLt
  have := (f 24).isLt; have := (f 7).isLt; have := (f 30).isLt; have := (f 6).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;>
    (try simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod] at *)
    <;> omega

set_option maxRecDepth 20000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
/-- The odd case with `δ ≤ 0`: `g` gains `f`, then halves. -/
theorem dsN_ok (M : Word → BitVec 8) (f : Fin 32 → Word) (hz : f 0 = 0) (s : Ds) (h : DsRegs f s)
    (hg : s.g % 2 = 1) (hd : ¬ dsPos s.δ) : DsRegs (runBlock dsS (M, (runBlock dsN (M, f)).2)).2 (dsStep s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [dsStep, ite_eq_right (show ¬ s.g % 2 = 0 by omega), ite_eq_right hd]
  simp +decide only [DsRegs, runBlock, BInstr.run, dsN, dsS, upd, ↓reduceIte, aluEval, hz, BitVec.zero_add]
  simp only [W64, asr64, a0, a1, a2, a3, a4, a5, a6, BitVec.toNat_add, BitVec.toNat_sub, BitVec.ult, toNat_or_shl31,
    toNat_or_shl1, toNat_sra1, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at *
  have := (f 21).isLt; have := (f 19).isLt; have := (f 10).isLt; have := (f 11).isLt; have := (f 9).isLt
  have := (f 17).isLt; have := (f 12).isLt; have := (f 16).isLt; have := (f 27).isLt; have := (f 25).isLt
  have := (f 24).isLt; have := (f 7).isLt; have := (f 30).isLt; have := (f 6).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;>
    (try simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod] at *)
    <;> omega

set_option maxRecDepth 20000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
/-- The odd case with `δ > 0`: `f` and `g` swap, and `g` loses `f`, then halves. -/
theorem dsP_ok (M : Word → BitVec 8) (f : Fin 32 → Word) (hz : f 0 = 0) (s : Ds) (h : DsRegs f s)
    (hg : s.g % 2 = 1) (hd : dsPos s.δ) : DsRegs (runBlock dsS (M, (runBlock dsP (M, f)).2)).2 (dsStep s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [dsStep, ite_eq_right (show ¬ s.g % 2 = 0 by omega), ite_eq_left hd]
  simp +decide only [DsRegs, runBlock, BInstr.run, dsP, dsS, upd, ↓reduceIte, aluEval, hz, BitVec.zero_add]
  simp only [W64, asr64, a0, a1, a2, a3, a4, a5, a6, BitVec.toNat_add, BitVec.toNat_sub, BitVec.ult, toNat_or_shl31,
    toNat_or_shl1, toNat_sra1, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at *
  have := (f 21).isLt; have := (f 19).isLt; have := (f 10).isLt; have := (f 11).isLt; have := (f 9).isLt
  have := (f 17).isLt; have := (f 12).isLt; have := (f 16).isLt; have := (f 27).isLt; have := (f 25).isLt
  have := (f 24).isLt; have := (f 7).isLt; have := (f 30).isLt; have := (f 6).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;>
    (try simp only [decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod] at *)
    <;> omega

theorem DsRegs.congr {f f' : Fin 32 → Word} {s : Ds} (h : DsRegs f s)
    (e : ∀ q : Fin 32, q.val ∈ [6, 7, 9, 10, 11, 12, 16, 17, 19, 21, 24, 25, 27, 30] → f' q = f q) : DsRegs f' s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [e 6 (by decide), e 7 (by decide), e 9 (by decide), e 10 (by decide), e 11 (by decide),
      e 12 (by decide), e 16 (by decide), e 17 (by decide), e 19 (by decide), e 21 (by decide), e 24 (by decide),
      e 25 (by decide), e 27 (by decide), e 30 (by decide)] <;> assumption

theorem ds_odd {lo hi : Word} {g : Nat} (h : W64 lo hi = g) : (lo &&& 1 = 0 ↔ g % 2 = 0) := by
  have e : (lo &&& 1).toNat = lo.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : Word).toNat = 1 from rfl, Nat.and_one_is_mod]
  constructor
  · intro h0; have := congrArg BitVec.toNat h0; rw [e, show (0 : Word).toNat = 0 from rfl] at this; simp only [W64] at h; omega
  · intro h0; apply BitVec.eq_of_toNat_eq; simp only [W64] at h; rw [e, show (0 : Word).toNat = 0 from rfl]; omega

theorem ds_pos_lo {lo hi : Word} {δ : Nat} (h : W64 lo hi = δ) (h0 : hi = 0) : (dsPos δ ↔ lo ≠ 0) := by
  subst h0; simp only [W64, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at h
  subst h; unfold dsPos
  have := lo.isLt
  constructor
  · intro ⟨h1, _⟩ e; exact h1 (by rw [e]; rfl)
  · intro h1; exact ⟨fun e => h1 (BitVec.eq_of_toNat_eq e), by omega⟩

theorem ds_pos_hi {lo hi : Word} {δ : Nat} (h : W64 lo hi = δ) (h0 : hi ≠ 0) :
    (dsPos δ ↔ (0 : Word).slt hi = true) := by
  have hl := lo.isLt; have hh := hi.isLt
  have hn : hi.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq e)
  simp only [W64] at h
  rw [BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  unfold dsPos
  simp only [show (0 : Word).toNat = 0 from rfl, decide_eq_true_eq]
  constructor
  · intro ⟨_, h2⟩; rw [ite_eq_left (by omega), ite_eq_left (by omega)]; omega
  · intro h2
    by_cases hc : 2 * hi.toNat < 2 ^ 32
    · exact ⟨by omega, by omega⟩
    · rw [ite_eq_left (by omega), ite_eq_right hc] at h2; omega

theorem runBlock_zero : ∀ (is : List BInstr) (M : Word → BitVec 8) (f : Fin 32 → Word), f 0 = 0 →
    (runBlock is (M, f)).2 0 = 0
  | [], _, _, h => h
  | i :: is, M, f, h => by
    cases i <;> exact runBlock_zero is _ _ (by simp [BInstr.run, upd, h])

/-- The registers the loop keeps. -/
theorem ds_keep (M : Word → BitVec 8) (f : Fin 32 → Word) (hz : f 0 = 0) (X : List BInstr)
    (hX : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 18, 20, 22, 23, 26] → q ∉ X.filterMap BInstr.dst) :
    (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 22, 23, 26] → (runBlock dsS (M, (runBlock X (M, f)).2)).2 q = f q) ∧
      (runBlock dsS (M, (runBlock X (M, f)).2)).2 5 = f 5 + 0xFFFFFFFF := by
  have hz' : (runBlock X (M, f)).2 0 = 0 := runBlock_zero X M f hz
  constructor
  · intro q hq
    rw [runBlock_reg _ _ _ q hz' (by simp only [dsS]; revert hq; revert q; decide),
      runBlock_reg _ _ _ q hz (hX q (by revert hq; revert q; decide))]
  · have e : (runBlock X (M, f)).2 5 = f 5 := runBlock_reg _ _ _ 5 hz (hX 5 (by decide))
    simp +decide only [runBlock, BInstr.run, dsS, upd, ↓reduceIte, aluEval]
    rw [e]

set_option maxHeartbeats 4000000 in
/-- **One divstep** of the loop at 0x44E, to the branch at 0x52C. -/
theorem ds_body {Mx : Word → BitVec 8} (hc : CodeIn Mx PV p384VerifyPrehashCode) {m : Machine} {s : Ds}
    (st : St Mx PV m 0x44E (reg m)) (h : DsRegs (reg m) s) :
    ∃ m', Steps m m' ∧ St Mx PV m' 0x52C (reg m') ∧ DsRegs (reg m') (dsStep s) ∧
      reg m' 5 = reg m 5 + 0xFFFFFFFF ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 22, 23, 26] → reg m' q = reg m q) := by
  have hz := st.zero
  obtain ⟨m1, c1, u1⟩ := st.block dsA hc dsA_end ⟨trivial, trivial⟩
  have s1 : St Mx PV m1 0x452 (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have z1 := s1.zero
  have r1a3 : reg m1 a3 = reg m a0 &&& 1 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, dsA, upd, ↓reduceIte, aluEval]
  have r1k : ∀ q : Fin 32, q ≠ a3 → reg m1 q = reg m q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [dsA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simpa using hq)]
  have h1 : DsRegs (reg m1) s := h.congr fun q hq => r1k q (by revert hq; revert q; decide)
  -- the shift and the loop branch, after the case's block, ending at 0x4FE
  have fin : ∀ {m4 : Machine} (X : List BInstr) (f0 : Fin 32 → Word), f0 0 = 0 → St Mx PV m4 0x4FE (reg m4) →
      reg m4 = (runBlock X (Mx, f0)).2 → Steps m m4 →
      DsRegs (runBlock dsS (Mx, (runBlock X (Mx, f0)).2)).2 (dsStep s) →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 18, 20, 22, 23, 26] → q ∉ X.filterMap BInstr.dst) →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 18, 20, 22, 23, 26] → f0 q = reg m q) →
      ∃ m', Steps m m' ∧ St Mx PV m' 0x52C (reg m') ∧ DsRegs (reg m') (dsStep s) ∧
        reg m' 5 = reg m 5 + 0xFFFFFFFF ∧
        (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 22, 23, 26] → reg m' q = reg m q) := by
    intro m4 X f0 hf0 s4 e4 c4 hd hX hk
    obtain ⟨m5, c5, u5⟩ := s4.block dsS hc dsS_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have e5 : reg m5 = (runBlock dsS (Mx, (runBlock X (Mx, f0)).2)).2 := by
      funext q; rw [u5.regs, e4]
    obtain ⟨kk, kt⟩ := ds_keep Mx f0 hf0 X hX
    refine ⟨m5, c4.trans c5, ⟨u5.pc, u5.mem, fun _ => rfl⟩, by rw [e5]; exact hd, ?_, fun q hq => ?_⟩
    · rw [e5, kt, hk 5 (by decide)]
    · rw [e5, kk q hq, hk q (by revert hq; revert q; decide)]
  have pathN : ∀ {m5 : Machine}, St Mx PV m5 0x478 (reg m5) → Steps m m5 → DsRegs (reg m5) s →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 18, 20, 22, 23, 26] → reg m5 q = reg m q) → s.g % 2 = 1 → ¬ dsPos s.δ →
      ∃ m', Steps m m' ∧ St Mx PV m' 0x52C (reg m') ∧ DsRegs (reg m') (dsStep s) ∧
        reg m' 5 = reg m 5 + 0xFFFFFFFF ∧
        (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 22, 23, 26] → reg m' q = reg m q) := by
    intro m5 s5 c5 h5 k5 hgo hnp
    obtain ⟨m6, c6, u6⟩ := s5.block dsN hc dsN_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have s6 : St Mx PV m6 0x4A8 (reg m6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
    obtain ⟨m7, d7, u7⟩ := s6.jump hc pv_at_4a8 (off' := 0x4FE) (by decide) (by rw [s6.pc]; decide)
    exact fin dsN (reg m5) s5.zero u7.self (by funext q; rw [u7.regs, u6.regs]) (c5.trans (c6.trans (.single d7)))
      (dsN_ok Mx (reg m5) s5.zero s h5 hgo hnp) (by decide) k5
  have pathP : ∀ {m5 : Machine}, St Mx PV m5 0x4B0 (reg m5) → Steps m m5 → DsRegs (reg m5) s →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 18, 20, 22, 23, 26] → reg m5 q = reg m q) → s.g % 2 = 1 → dsPos s.δ →
      ∃ m', Steps m m' ∧ St Mx PV m' 0x52C (reg m') ∧ DsRegs (reg m') (dsStep s) ∧
        reg m' 5 = reg m 5 + 0xFFFFFFFF ∧
        (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 22, 23, 26] → reg m' q = reg m q) := by
    intro m5 s5 c5 h5 k5 hgo hp
    obtain ⟨m6, c6, u6⟩ := s5.block dsP hc dsP_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    exact fin dsP (reg m5) s5.zero ⟨u6.pc, u6.mem, fun _ => rfl⟩ (by funext q; rw [u6.regs]) (c5.trans c6)
      (dsP_ok Mx (reg m5) s5.zero s h5 hgo hp) (by decide) k5
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 18, 20, 22, 23, 26] → reg m1 q = reg m q :=
    fun q hq => r1k q (by revert hq; revert q; decide)
  have hδ := h1.1
  have hg := h1.2.2.1
  by_cases hge : s.g % 2 = 0
  · have ha3 : reg m1 a3 = 0 := by rw [r1a3, ← r1k 10 (by decide)]; exact (ds_odd hg).2 hge
    obtain ⟨m2, d2, u2⟩ := s1.notTaken hc 0x454 pv_at_452 (by decide)
      (by show (reg m1 a3 != reg m1 x0) = false; rw [ha3, z1]; rfl)
    have e2 : reg m2 = reg m1 := funext u2.regs
    obtain ⟨m3, c3, u3⟩ := u2.self.block dsE hc dsE_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have s3 : St Mx PV m3 0x46C (reg m3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
    obtain ⟨m4, d4, u4⟩ := s3.jump hc pv_at_46c (off' := 0x4FE) (by decide) (by rw [s3.pc]; decide)
    exact fin dsE (reg m1) z1 u4.self (by funext q; rw [u4.regs, u3.regs, e2])
      (c1.trans (.cons d2 (c3.trans (.single d4)))) (dsE_ok Mx (reg m1) z1 s h1 hge) (by decide) k1
  have hgo : s.g % 2 = 1 := by omega
  have ha3 : reg m1 a3 ≠ 0 := by
    rw [r1a3, ← r1k 10 (by decide)]; exact fun h0 => hge ((ds_odd hg).1 h0)
  obtain ⟨m2, d2, u2⟩ := s1.taken hc 0x46E pv_at_452 (by decide)
    (by show (reg m1 a3 != reg m1 x0) = true; rw [z1]; simpa using ha3)
  have e2 : reg m2 = reg m1 := funext u2.regs
  by_cases h19 : reg m1 19 = 0
  · obtain ⟨m3, d3, u3⟩ := u2.self.taken hc 0x4AA pv_at_46e (by decide)
      (by show (reg m2 19 == reg m2 x0) = true; rw [e2, h19, z1]; rfl)
    have e3 : reg m3 = reg m1 := by funext q; rw [u3.regs, e2]
    obtain ⟨m4, c4, u4⟩ := u3.self.block dsZ hc dsZ_end ⟨trivial, trivial⟩
    have s4 : St Mx PV m4 0x4AE (reg m4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    have r4a3 : reg m4 a3 = if (0 : Word).ult (reg m1 21) then 1 else 0 := by
      rw [u4.regs, e3]; simp +decide only [runBlock, BInstr.run, dsZ, upd, ↓reduceIte, aluEval, z1]
    have r4k : ∀ q : Fin 32, q ≠ a3 → reg m4 q = reg m1 q := fun q hq => by
      rw [u4.regs, e3, runBlock_reg _ _ _ q z1
        (by simp only [dsZ, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simpa using hq)]
    have h4 : DsRegs (reg m4) s := h1.congr fun q hq => r4k q (by revert hq; revert q; decide)
    have k4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 18, 20, 22, 23, 26] → reg m4 q = reg m q :=
      fun q hq => by rw [r4k q (by revert hq; revert q; decide), k1 q hq]
    by_cases h21 : reg m1 21 = 0
    · have hnp : ¬ dsPos s.δ := by rw [ds_pos_lo hδ h19]; simpa using h21
      obtain ⟨m5, d5, u5⟩ := s4.taken hc 0x478 pv_at_4ae (by decide)
        (by show (reg m4 a3 == reg m4 x0) = true; rw [r4a3, h21, s4.zero]; decide)
      exact pathN u5.self (c1.trans (.cons d2 (.cons d3 (c4.trans (.single d5)))))
        (h4.congr fun q _ => u5.regs q) (fun q hq => by rw [u5.regs, k4 q hq]) hgo hnp
    · have hp : dsPos s.δ := by rw [ds_pos_lo hδ h19]; exact h21
      have hu : (0 : Word).ult (reg m1 21) = true := by
        simp only [BitVec.ult, decide_eq_true_eq]; exact Nat.pos_of_ne_zero fun e => h21 (BitVec.eq_of_toNat_eq e)
      obtain ⟨m5, d5, u5⟩ := s4.notTaken hc 0x4B0 pv_at_4ae (by decide)
        (by show (reg m4 a3 == reg m4 x0) = false; rw [r4a3, hu, s4.zero]; decide)
      exact pathP u5.self (c1.trans (.cons d2 (.cons d3 (c4.trans (.single d5)))))
        (h4.congr fun q _ => u5.regs q) (fun q hq => by rw [u5.regs, k4 q hq]) hgo hp
  · obtain ⟨m3, d3, u3⟩ := u2.self.notTaken hc 0x472 pv_at_46e (by decide)
      (by show (reg m2 19 == reg m2 x0) = false; rw [e2, z1]; simpa using h19)
    have e3 : reg m3 = reg m1 := by funext q; rw [u3.regs, e2]
    obtain ⟨m4, c4, u4⟩ := u3.self.block dsT hc dsT_end ⟨trivial, trivial⟩
    have s4 : St Mx PV m4 0x476 (reg m4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    have r4a3 : reg m4 a3 = if (0 : Word).slt (reg m1 19) then 1 else 0 := by
      rw [u4.regs, e3]; simp +decide only [runBlock, BInstr.run, dsT, upd, ↓reduceIte, aluEval, z1]
    have r4k : ∀ q : Fin 32, q ≠ a3 → reg m4 q = reg m1 q := fun q hq => by
      rw [u4.regs, e3, runBlock_reg _ _ _ q z1
        (by simp only [dsT, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simpa using hq)]
    have h4 : DsRegs (reg m4) s := h1.congr fun q hq => r4k q (by revert hq; revert q; decide)
    have k4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 18, 20, 22, 23, 26] → reg m4 q = reg m q :=
      fun q hq => by rw [r4k q (by revert hq; revert q; decide), k1 q hq]
    by_cases hs : (0 : Word).slt (reg m1 19) = true
    · have hp : dsPos s.δ := (ds_pos_hi hδ h19).2 hs
      obtain ⟨m5, d5, u5⟩ := s4.taken hc 0x4B0 pv_at_476 (by decide)
        (by show (reg m4 a3 != reg m4 x0) = true; rw [r4a3, hs, s4.zero]; decide)
      exact pathP u5.self (c1.trans (.cons d2 (.cons d3 (c4.trans (.single d5)))))
        (h4.congr fun q _ => u5.regs q) (fun q hq => by rw [u5.regs, k4 q hq]) hgo hp
    · have hnp : ¬ dsPos s.δ := fun hp => hs ((ds_pos_hi hδ h19).1 hp)
      obtain ⟨m5, d5, u5⟩ := s4.notTaken hc 0x478 pv_at_476 (by decide)
        (by show (reg m4 a3 != reg m4 x0) = false; rw [r4a3, Bool.not_eq_true _ |>.mp hs, s4.zero]; decide)
      exact pathN u5.self (c1.trans (.cons d2 (.cons d3 (c4.trans (.single d5)))))
        (h4.congr fun q _ => u5.regs q) (fun q hq => by rw [u5.regs, k4 q hq]) hgo hnp

/-- **The divstep loop** at 0x44E, with `k + 1` steps left in `t0`, runs
them all and leaves at 0x530. -/
theorem ds_loop {Mx : Word → BitVec 8} (hc : CodeIn Mx PV p384VerifyPrehashCode) (k : Nat) :
    ∀ {m : Machine} {s : Ds}, St Mx PV m 0x44E (reg m) → DsRegs (reg m) s →
      reg m 5 = BitVec.ofNat 32 (k + 1) → k + 1 < 2 ^ 32 →
      ∃ m', Steps m m' ∧ St Mx PV m' 0x530 (reg m') ∧ DsRegs (reg m') (dsIter (k + 1) s) ∧
        (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 22, 23, 26] → reg m' q = reg m q) := by
  induction k with
  | zero =>
    intro m s st h h5 _
    obtain ⟨m1, c1, s1, h1, t1, k1⟩ := ds_body hc st h
    have e : reg m1 5 = 0 := by rw [t1, h5]; decide
    obtain ⟨m2, d2, u2⟩ := s1.notTaken hc 0x530 pv_at_52c (by decide)
      (by show (reg m1 5 != reg m1 x0) = false; rw [e, s1.zero]; rfl)
    exact ⟨m2, c1.trans (.single d2), u2.self, h1.congr fun q _ => u2.regs q,
      fun q hq => by rw [u2.regs, k1 q hq]⟩
  | succ k ih =>
    intro m s st h h5 hk
    obtain ⟨m1, c1, s1, h1, t1, k1⟩ := ds_body hc st h
    have e : reg m1 5 = BitVec.ofNat 32 (k + 1) := by
      rw [t1, h5]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl,
        show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_add_mod,
        show k + 1 + 1 + 4294967295 = k + 1 + 4294967296 by omega, Nat.add_mod_right]
    have hne : reg m1 5 ≠ 0 := by
      rw [e]; intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (0 : Word).toNat = 0 from rfl] at this
      omega
    obtain ⟨m2, d2, u2⟩ := s1.taken hc 0x44E pv_at_52c (by decide)
      (by show (reg m1 5 != reg m1 x0) = true; rw [s1.zero]; simpa using hne)
    obtain ⟨m3, c3, s3, h3, k3⟩ := ih u2.self (h1.congr fun q _ => u2.regs q) (by rw [u2.regs, e]) (by omega)
    exact ⟨m3, c1.trans (.cons d2 c3), s3, h3, fun q hq => by rw [k3 q hq, u2.regs, k1 q hq]⟩

end C3.RV32.Pv
