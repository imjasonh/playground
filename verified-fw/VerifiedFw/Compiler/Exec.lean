/-
Lemmas about running code on the RISC-V model, used by `Correct.lean`.
-/
import VerifiedFw.Compiler.Compile

namespace VerifiedFw.Compiler

open VerifiedFw.RiscV VerifiedFw.Lang

/-- `m` runs to `m'` in zero or more steps without faulting. -/
inductive Star (p : Platform) : Machine → Machine → Prop
  | refl (m : Machine) : Star p m m
  | step {m₁ m₂ m₃ : Machine} : step p m₁ = some m₂ → Star p m₂ m₃ → Star p m₁ m₃

namespace Star

theorem trans {p : Platform} {a b c : Machine} (h₁ : Star p a b) (h₂ : Star p b c) :
    Star p a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem single {p : Platform} {a b : Machine} (h : RiscV.step p a = some b) : Star p a b :=
  .step h (.refl b)

end Star

/-! ## Machine updates -/

@[simp] theorem setReg_pc (m : Machine) (r : Reg) (v : Word) : (m.setReg r v).pc = m.pc := by
  unfold Machine.setReg; split <;> rfl
@[simp] theorem setReg_imem (m : Machine) (r : Reg) (v : Word) :
    (m.setReg r v).imem = m.imem := by
  unfold Machine.setReg; split <;> rfl
@[simp] theorem setReg_dmem (m : Machine) (r : Reg) (v : Word) :
    (m.setReg r v).dmem = m.dmem := by
  unfold Machine.setReg; split <;> rfl
@[simp] theorem setReg_trace (m : Machine) (r : Reg) (v : Word) :
    (m.setReg r v).trace = m.trace := by
  unfold Machine.setReg; split <;> rfl

theorem reg_setReg (m : Machine) (r x : Reg) (v : Word) :
    (m.setReg r v).reg x = if x = r ∧ r ≠ 0 then v else m.reg x := by
  unfold Machine.setReg Machine.reg
  by_cases hr : r = 0 <;> by_cases hx : x = r <;> simp_all

theorem reg_setReg_self (m : Machine) (r : Reg) (v : Word) (h : r ≠ 0) :
    (m.setReg r v).reg r = v := by
  simp [reg_setReg, h]

theorem reg_setReg_other (m : Machine) (r x : Reg) (v : Word) (h : x ≠ r) :
    (m.setReg r v).reg x = m.reg x := by
  simp [reg_setReg, h]

@[simp] theorem next_pc (m : Machine) : m.next.pc = m.pc + 4 := rfl
@[simp] theorem next_imem (m : Machine) : m.next.imem = m.imem := rfl
@[simp] theorem next_dmem (m : Machine) : m.next.dmem = m.dmem := rfl
@[simp] theorem next_trace (m : Machine) : m.next.trace = m.trace := rfl
@[simp] theorem next_reg (m : Machine) (x : Reg) : m.next.reg x = m.reg x := rfl

theorem exec_imem {p : Platform} {m m' : Machine} {i : Instr} (h : exec p m i = some m') :
    m'.imem = m.imem := by
  cases i <;> simp only [exec] at h <;> (try split at h) <;> (try split at h) <;>
    first | (cases h; simp) | contradiction | simp_all

theorem step_imem {p : Platform} {m m' : Machine} (h : step p m = some m') :
    m'.imem = m.imem := by
  unfold step at h
  split at h
  · split at h
    · exact exec_imem h
    · contradiction
  · contradiction

theorem Star.imem {p : Platform} {m m' : Machine} (h : Star p m m') : m'.imem = m.imem := by
  induction h with
  | refl => rfl
  | step hs _ ih => rw [ih, step_imem hs]

/-- The address `n` instructions after `pc`. -/
def after (pc : Word) (n : Nat) : Word := pc + .ofNat 32 (4 * n)

@[simp] theorem after_zero (pc : Word) : after pc 0 = pc := by simp [after]

theorem after_after (pc : Word) (a b : Nat) : after (after pc a) b = after pc (a + b) := by
  simp only [after, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem after_one (pc : Word) : pc + 4 = after pc 1 := rfl

theorem after_succ (pc : Word) (n : Nat) : after pc n + 4 = after pc (n + 1) := by
  rw [after_one, after_after]

theorem aligned_after {pc : Word} (h : aligned pc) (n : Nat) : aligned (after pc n) := by
  unfold aligned at *
  simp only [after, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## Code placement -/

/-- `code` sits in instruction memory starting at `pc`. -/
def CodeAt (imem : Word → Word) (pc : Word) (code : List Instr) : Prop :=
  ∀ k (h : k < code.length), imem (after pc k) = encode code[k]

theorem CodeAt.append {imem : Word → Word} {pc : Word} {a b : List Instr} :
    CodeAt imem pc (a ++ b) ↔ CodeAt imem pc a ∧ CodeAt imem (after pc a.length) b := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h (a.length + k) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simp only [Nat.add_sub_cancel_left] at this
      rwa [after_after]
  · rintro ⟨ha, hb⟩ k hk
    by_cases hka : k < a.length
    · rw [List.getElem_append_left hka]; exact ha k hka
    · rw [List.getElem_append_right (by omega)]
      have := hb (k - a.length) (by simp at hk; omega)
      rwa [after_after, Nat.add_sub_cancel' (by omega)] at this

theorem CodeAt.single {imem : Word → Word} {pc : Word} {i : Instr} :
    CodeAt imem pc [i] ↔ imem pc = encode i := by
  constructor
  · intro h; simpa using h 0 (by simp)
  · intro h k hk
    simp at hk; subst hk; simpa using h

/-! ## Running one instruction -/

theorem step_at {p : Platform} {m : Machine} {i : Instr} (hc : m.imem m.pc = encode i)
    (ha : aligned m.pc) : step p m = exec p m i := by
  simp [step, ha, hc, decode_encode]

/-! ## Arithmetic -/

theorem sext12_toNat (x : BitVec 12) :
    (sext12 x).toNat = if x.toNat < 2048 then x.toNat else x.toNat + (2 ^ 32 - 4096) := by
  simp only [sext12, BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  have := x.isLt
  by_cases h : x.toNat < 2048
  · have : ¬ (2 ^ (12 - 1) ≤ x.toNat) := by omega
    simp [h, this]; omega
  · have : 2 ^ (12 - 1) ≤ x.toNat := by omega
    simp [h, this]; omega

/-- What `loadImm` computes: `lui` of the upper part plus the sign-extended low
12 bits gives back the constant. -/
theorem loadImm_val (c : Word) :
    ((((c - sext12 (c.setWidth 12)) >>> 12).setWidth 20).setWidth 32 <<< 12) +
      sext12 (c.setWidth 12) = c := by
  apply BitVec.eq_of_toNat_eq
  have hc := c.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, BitVec.toNat_sub, sext12_toNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  split <;> omega

theorem sext12_zero : sext12 0 = 0 := rfl

theorem sext12_slot {i : Nat} (h : i < 512) : sext12 (slot i) = .ofNat 32 (4 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sext12_toNat, slot, BitVec.toNat_ofNat]
  split <;> omega

theorem jumpOffset_fwd {n : Nat} (h : n < 2 ^ 18) :
    jumpOffset (jumpBy n) = .ofNat 32 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [jumpOffset, jumpBy, BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.msb_eq_decide, BitVec.toNat_ofInt, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  split <;> simp_all <;> omega

theorem jumpOffset_back {n : Nat} (h : n < 2 ^ 18) :
    jumpOffset (jumpBy (-(n : Int))) + .ofNat 32 (4 * n) = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [jumpOffset, jumpBy, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide, BitVec.toNat_ofInt,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  split <;> simp_all <;> omega

theorem jumpOffset_zero : jumpOffset 0 = 0 := rfl

theorem branchOffset_four : branchOffset 4 = 8 := rfl

/-- Distinct RAM slots have distinct addresses. -/
theorem slot_ne {base : Word} {i j : Nat} (hi : i < 512) (hj : j < 512) (h : i ≠ j) :
    after base i ≠ after base j := by
  unfold after
  intro he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := base.isLt
  omega

end VerifiedFw.Compiler
