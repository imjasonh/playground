import C3BootProofs.Proofs.P384Add

/-!
# `<p384::arithmetic::field::FieldElement as ff::Field>::double`

P-384's field doubling as compiled, `ConstMontyForm::double` inlined: the operand copied to the frame and
shifted left a bit in place, limb by limb, a 12-limb `borrowing_sub` of the
modulus into a second buffer, and `Uint<12>::select` of the doubled value
when it is below the modulus, else the difference, into the result.
-/

namespace C3.RV32

open C3.Image

set_option exponentiation.threshold 400

section
set_option maxRecDepth 20000

theorem pd3_at_0 : fetchRel p384DoubleCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF80, 2) := by decide
theorem pd3_at_2 : fetchRel p384DoubleCode 0x2 = some (.store .sw sp ra 0x7C, 2) := by decide
theorem pd3_at_4 : fetchRel p384DoubleCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x78, 2) := by decide
theorem pd3_at_6 : fetchRel p384DoubleCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x74, 2) := by decide
theorem pd3_at_8 : fetchRel p384DoubleCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x70, 2) := by decide
theorem pd3_at_a : fetchRel p384DoubleCode 0xA = some (.store .sw sp (19 : Fin 32) 0x6C, 2) := by decide
theorem pd3_at_c : fetchRel p384DoubleCode 0xC = some (.store .sw sp (20 : Fin 32) 0x68, 2) := by decide
theorem pd3_at_e : fetchRel p384DoubleCode 0xE = some (.store .sw sp (21 : Fin 32) 0x64, 2) := by decide
theorem pd3_at_10 : fetchRel p384DoubleCode 0x10 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem pd3_at_12 : fetchRel p384DoubleCode 0x12 = some (.alu .add a0 x0 sp, 2) := by decide
theorem pd3_at_14 : fetchRel p384DoubleCode 0x14 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pd3_at_18 : fetchRel p384DoubleCode 0x18 = some (.alu .add (8 : Fin 32) x0 sp, 2) := by decide
theorem pd3_at_1a : fetchRel p384DoubleCode 0x1A = some (.auipc ra 0x1000, 4) := by decide
theorem pd3_at_1e : fetchRel p384DoubleCode 0x1E = some (.jalr ra ra 0xFFFFF8DC, 4) := by decide
theorem pd3_at_22 : fetchRel p384DoubleCode 0x22 = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem pd3_at_24 : fetchRel p384DoubleCode 0x24 = some (.aluImm .add a0 x0 0xC, 2) := by decide
theorem pd3_at_26 : fetchRel p384DoubleCode 0x26 = some (.branch .beq a0 x0 0x18, 2) := by decide
theorem pd3_at_28 : fetchRel p384DoubleCode 0x28 = some (.load .lw a1 (8 : Fin 32) 0x0, 2) := by decide
theorem pd3_at_2a : fetchRel p384DoubleCode 0x2A = some (.aluImm .sll a2 a1 0x1, 4) := by decide
theorem pd3_at_2e : fetchRel p384DoubleCode 0x2E = some (.alu .or a2 a2 (19 : Fin 32), 4) := by decide
theorem pd3_at_32 : fetchRel p384DoubleCode 0x32 = some (.aluImm .srl (19 : Fin 32) a1 0x1F, 4) := by decide
theorem pd3_at_36 : fetchRel p384DoubleCode 0x36 = some (.store .sw (8 : Fin 32) a2 0x0, 2) := by decide
theorem pd3_at_38 : fetchRel p384DoubleCode 0x38 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem pd3_at_3a : fetchRel p384DoubleCode 0x3A = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem pd3_at_3c : fetchRel p384DoubleCode 0x3C = some (.branch .bne a0 x0 0xFFFFFFEC, 2) := by decide
theorem pd3_at_3e : fetchRel p384DoubleCode 0x3E = some (.aluImm .add a0 sp 0x30, 2) := by decide
theorem pd3_at_40 : fetchRel p384DoubleCode 0x40 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pd3_at_44 : fetchRel p384DoubleCode 0x44 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pd3_at_46 : fetchRel p384DoubleCode 0x46 = some (.aluImm .add (20 : Fin 32) sp 0x30, 4) := by decide
theorem pd3_at_4a : fetchRel p384DoubleCode 0x4A = some (.auipc ra 0x1000, 4) := by decide
theorem pd3_at_4e : fetchRel p384DoubleCode 0x4E = some (.jalr ra ra 0xFFFFF844, 4) := by decide
theorem pd3_at_52 : fetchRel p384DoubleCode 0x52 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem pd3_at_54 : fetchRel p384DoubleCode 0x54 = some (.alu .add (21 : Fin 32) x0 sp, 2) := by decide
theorem pd3_at_56 : fetchRel p384DoubleCode 0x56 = some (.lui (8 : Fin 32) 0x3FCC5000, 4) := by decide
theorem pd3_at_5a : fetchRel p384DoubleCode 0x5A = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFC8C, 4) := by decide
theorem pd3_at_5e : fetchRel p384DoubleCode 0x5E = some (.aluImm .add (9 : Fin 32) x0 0xC, 2) := by decide
theorem pd3_at_60 : fetchRel p384DoubleCode 0x60 = some (.branch .beq (9 : Fin 32) x0 0x20, 2) := by decide
theorem pd3_at_62 : fetchRel p384DoubleCode 0x62 = some (.load .lw a0 (21 : Fin 32) 0x0, 4) := by decide
theorem pd3_at_66 : fetchRel p384DoubleCode 0x66 = some (.load .lw a1 (8 : Fin 32) 0x0, 2) := by decide
theorem pd3_at_68 : fetchRel p384DoubleCode 0x68 = some (.auipc ra 0xFFFEE000, 4) := by decide
theorem pd3_at_6c : fetchRel p384DoubleCode 0x6C = some (.jalr ra ra 0x360, 4) := by decide
theorem pd3_at_70 : fetchRel p384DoubleCode 0x70 = some (.alu .add a2 x0 a1, 2) := by decide
theorem pd3_at_72 : fetchRel p384DoubleCode 0x72 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem pd3_at_74 : fetchRel p384DoubleCode 0x74 = some (.store .sw (20 : Fin 32) a0 0x0, 4) := by decide
theorem pd3_at_78 : fetchRel p384DoubleCode 0x78 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem pd3_at_7a : fetchRel p384DoubleCode 0x7A = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem pd3_at_7c : fetchRel p384DoubleCode 0x7C = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem pd3_at_7e : fetchRel p384DoubleCode 0x7E = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem pd3_at_80 : fetchRel p384DoubleCode 0x80 = some (.store .sw sp (19 : Fin 32) 0x60, 2) := by decide
theorem pd3_at_82 : fetchRel p384DoubleCode 0x82 = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem pd3_at_84 : fetchRel p384DoubleCode 0x84 = some (.load .lw a0 sp 0x60, 2) := by decide
theorem pd3_at_86 : fetchRel p384DoubleCode 0x86 = some (.aluImm .sltu (8 : Fin 32) a0 0x1, 4) := by decide
theorem pd3_at_8a : fetchRel p384DoubleCode 0x8A = some (.alu .and (8 : Fin 32) (8 : Fin 32) a2, 2) := by decide
theorem pd3_at_8c : fetchRel p384DoubleCode 0x8C = some (.store .sb sp (8 : Fin 32) 0x60, 4) := by decide
theorem pd3_at_90 : fetchRel p384DoubleCode 0x90 = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem pd3_at_92 : fetchRel p384DoubleCode 0x92 = some (.load .lbu a0 sp 0x60, 4) := by decide
theorem pd3_at_96 : fetchRel p384DoubleCode 0x96 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem pd3_at_98 : fetchRel p384DoubleCode 0x98 = some (.alu .and a2 a2 a0, 2) := by decide
theorem pd3_at_9a : fetchRel p384DoubleCode 0x9A = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem pd3_at_9c : fetchRel p384DoubleCode 0x9C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pd3_at_9e : fetchRel p384DoubleCode 0x9E = some (.auipc ra 0xFFFEE000, 4) := by decide
theorem pd3_at_a2 : fetchRel p384DoubleCode 0xA2 = some (.jalr ra ra 0x32A, 4) := by decide
theorem pd3_at_a6 : fetchRel p384DoubleCode 0xA6 = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem pd3_at_a8 : fetchRel p384DoubleCode 0xA8 = some (.alu .add a2 x0 sp, 2) := by decide
theorem pd3_at_aa : fetchRel p384DoubleCode 0xAA = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem pd3_at_ac : fetchRel p384DoubleCode 0xAC = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem pd3_at_ae : fetchRel p384DoubleCode 0xAE = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pd3_at_b2 : fetchRel p384DoubleCode 0xB2 = some (.jalr ra ra 0xFFFFFE62, 4) := by decide
theorem pd3_at_b6 : fetchRel p384DoubleCode 0xB6 = some (.load .lw ra sp 0x7C, 2) := by decide
theorem pd3_at_b8 : fetchRel p384DoubleCode 0xB8 = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem pd3_at_ba : fetchRel p384DoubleCode 0xBA = some (.load .lw (9 : Fin 32) sp 0x74, 2) := by decide
theorem pd3_at_bc : fetchRel p384DoubleCode 0xBC = some (.load .lw (18 : Fin 32) sp 0x70, 2) := by decide
theorem pd3_at_be : fetchRel p384DoubleCode 0xBE = some (.load .lw (19 : Fin 32) sp 0x6C, 2) := by decide
theorem pd3_at_c0 : fetchRel p384DoubleCode 0xC0 = some (.load .lw (20 : Fin 32) sp 0x68, 2) := by decide
theorem pd3_at_c2 : fetchRel p384DoubleCode 0xC2 = some (.load .lw (21 : Fin 32) sp 0x64, 2) := by decide
theorem pd3_at_c4 : fetchRel p384DoubleCode 0xC4 = some (.aluImm .add sp sp 0x80, 2) := by decide
theorem pd3_at_c6 : fetchRel p384DoubleCode 0xC6 = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- The prologue's argument moves, from 0x10 to 0x1A. -/
def pdPro : List BInstr :=
  [.alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 sp, .aluImm .add a2 x0 0x30, .alu .add (8 : Fin 32) x0 sp]

def pdDblInit : List BInstr := [.aluImm .add (19 : Fin 32) x0 0x0, .aluImm .add a0 x0 0xC]

/-- One limb of the doubling, from 0x28 to 0x3C: the limb shifted left a
bit, with the bit shifted out of the limb below. -/
def pdDblBody : List BInstr :=
  [.lw a1 (8 : Fin 32) 0x0, .aluImm .sll a2 a1 0x1, .alu .or a2 a2 (19 : Fin 32), .aluImm .srl (19 : Fin 32) a1 0x1F,
   .sw (8 : Fin 32) a2 0x0, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, .aluImm .add a0 a0 0xFFFFFFFF]

/-- The choice, from 0x80 to 0x9E: 1 when there was no carry and the
subtraction borrowed. -/
def pdTail : List BInstr :=
  [.sw sp (19 : Fin 32) 0x60, .aluImm .add a0 sp 0x60, .lw a0 sp 0x60, .aluImm .sltu (8 : Fin 32) a0 0x1,
   .alu .and (8 : Fin 32) (8 : Fin 32) a2, .sb sp (8 : Fin 32) 0x60, .aluImm .add a0 sp 0x60,
   .lbu a0 sp 0x60, .aluImm .add a0 a0 0xFFFFFFFF, .alu .and a2 a2 a0, .alu .add a0 x0 (19 : Fin 32),
   .aluImm .add a1 x0 0x0]

def pdSelArgs : List BInstr :=
  [.aluImm .add a1 sp 0x30, .alu .add a2 x0 sp, .alu .add a0 x0 (18 : Fin 32), .alu .add a3 x0 (8 : Fin 32)]

/-- The registers `double` saves, at offsets from its `sp`. -/
abbrev pdPs : List (Fin 32 × Word) :=
  [(ra, 0x7C), ((8 : Fin 32), 0x78), ((9 : Fin 32), 0x74), ((18 : Fin 32), 0x70), ((19 : Fin 32), 0x6C),
   ((20 : Fin 32), 0x68), ((21 : Fin 32), 0x64)]

section
set_option maxRecDepth 20000
theorem pdSave_end : blockEnd p384DoubleCode 2 (saveBlock pdPs) = some 0x10 := by decide
theorem pdPro_end : blockEnd p384DoubleCode 0x10 pdPro = some 0x1A := by decide
theorem pdDblInit_end : blockEnd p384DoubleCode 0x22 pdDblInit = some 0x26 := by decide
theorem pdDblBody_end : blockEnd p384DoubleCode 0x28 pdDblBody = some 0x3C := by decide
theorem pdMid_end : blockEnd p384DoubleCode 0x3E p3Mid = some 0x4A := by decide
theorem pdSubInit_end : blockEnd p384DoubleCode 0x52 p3SubInit = some 0x60 := by decide
theorem pdSubTail_end : blockEnd p384DoubleCode 0x70 p3SubTail = some 0x7E := by decide
theorem pdTail_end : blockEnd p384DoubleCode 0x80 pdTail = some 0x9E := by decide
theorem pdSelArgs_end : blockEnd p384DoubleCode 0xA6 pdSelArgs = some 0xAE := by decide
theorem pdRestore_end : blockEnd p384DoubleCode 0xB6 (restoreBlock pdPs) = some 0xC4 := by decide
end

/-- The registers one limb of the doubling leaves alone. -/
def pdDblKeep (q : Fin 32) : Bool := q.val ∉ [0, 8, 10, 11, 12, 19]

set_option maxRecDepth 20000 in
theorem pdDblBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock pdDblBody (M, f)).1 = memStore32 M (f 8 + 0)
      (aluEval .or (aluEval .sll (memLoad32 M (f 8 + 0)) 1) (f 19)) ∧
    (runBlock pdDblBody (M, f)).2 19 = aluEval .srl (memLoad32 M (f 8 + 0)) 0x1F ∧
    (runBlock pdDblBody (M, f)).2 8 = f 8 + 4 ∧ (runBlock pdDblBody (M, f)).2 a0 = f a0 + 0xFFFFFFFF ∧
    ∀ q, pdDblKeep q = true → (runBlock pdDblBody (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, pdDblBody, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 4
  have h0 : q.val ≠ 0 := fun e => absurd (show pdDblKeep q = false by unfold pdDblKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
    pkeep_ne (r := a2) hq rfl, pkeep_ne (r := 19) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem pdDblBody_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h8 : (f 8 + 0).toNat % 4 = 0) (hs : Sep (f 8 + 0) 4 base len) : BlockOk base len pdDblBody (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, pdDblBody, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h8, h8, hs⟩

theorem or_low1 (x c : Word) (hx : x.toNat % 2 = 0) (hc : c.toNat ≤ 1) : (x ||| c).toNat = x.toNat + c.toNat := by
  have e : x.toNat = 2 ^ 1 * (x.toNat / 2) := by omega
  rw [BitVec.toNat_or, e, ← Nat.two_pow_add_eq_or_of_lt (by omega)]

theorem dbl_val (l c : Word) (hc : c.toNat ≤ 1) :
    (aluEval .or (aluEval .sll l 1) c).toNat + 2 ^ 32 * (aluEval .srl l 0x1F).toNat = 2 * l.toNat + c.toNat ∧
    (aluEval .srl l 0x1F).toNat ≤ 1 := by
  have hl := l.isLt
  have hs : (aluEval .sll l 1).toNat = l.toNat * 2 % 2 ^ 32 := by
    show (l <<< 1).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hr : (aluEval .srl l 0x1F).toNat = l.toNat / 2 ^ 31 := by
    show (l >>> 31).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have he : (aluEval .sll l 1).toNat % 2 = 0 := by rw [hs]; omega
  have ho : (aluEval .or (aluEval .sll l 1) c).toNat = (aluEval .sll l 1).toNat + c.toNat := or_low1 _ _ he hc
  rw [ho, hs, hr]
  constructor <;> omega

theorem dbl_arith {Acc L X s c c' l : Nat} (h1 : Acc + X * c = 2 * L) (h2 : s + 2 ^ 32 * c' = 2 * l + c) :
    Acc + s * X + X * 2 ^ 32 * c' = 2 * (L + l * X) := by
  have e : s * X + 2 ^ 32 * c' * X = 2 * (l * X) + c * X := by
    rw [← Nat.add_mul, h2, Nat.add_mul, Nat.mul_assoc]
  have e2 : X * 2 ^ 32 * c' = 2 ^ 32 * c' * X := by ac_rfl
  rw [Nat.mul_comm X c] at h1
  rw [e2]
  omega

/-- **One limb of the doubling**, from 0x28: shift limb `i` of the buffer at
`F` left a bit, bring in the carry, and store it back. -/
theorem pd_dbl_iter {M : Word → BitVec 8} {P F c : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x28 (reg n)) (hc : CodeIn M P p384DoubleCode) (hi : i < 12) (hF : F.toNat % 4 = 0)
    (sC : Sep (F + BitVec.ofNat 32 (4 * i)) 4 P p384DoubleCode.length)
    (r8 : reg n 8 = F + BitVec.ofNat 32 (4 * i)) (ra0 : reg n a0 = BitVec.ofNat 32 (12 - i)) (r19 : reg n 19 = c) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (F + BitVec.ofNat 32 (4 * i))
          (aluEval .or (aluEval .sll (memLoad32 M (F + BitVec.ofNat 32 (4 * i))) 1) c))
        P n' (if i + 1 < 12 then 0x28 else 0x3E) (reg n') ∧
      reg n' 19 = aluEval .srl (memLoad32 M (F + BitVec.ofNat 32 (4 * i))) 0x1F ∧
      reg n' 8 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, pdDblKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E19, E8, Ea0, Ek⟩ := pdDblBody_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block pdDblBody s hc pdDblBody_end
    (pdDblBody_ok (by rw [r8, add_lit_zero]; exact aligned_add hF (by omega)) (by rw [r8, add_lit_zero]; exact sC))
  rw [E1, r8, r19, add_lit_zero] at u1
  rw [r8, add_lit_zero] at E19
  have hc1 := CodeIn.store32 (v := aluEval .or (aluEval .sll (memLoad32 M (F + BitVec.ofNat 32 (4 * i))) 1) c) hc sC
  have ea0 : reg n1 a0 = BitVec.ofNat 32 (12 - (i + 1)) := by rw [u1.regs, Ea0, ra0, cnt12_dec i hi]
  have hb : branchTaken .bne (reg n1 a0) (reg n1 x0) = decide (i + 1 < 12) := by
    rw [ea0, u1.self.zero]; exact cnt12_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 19 = aluEval .srl (memLoad32 M (F + BitVec.ofNat 32 (4 * i))) 0x1F ∧
      reg n2 8 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, pdDblKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E19], by rw [h2, u1.regs, E8, r8, ptr4], by rw [h2, ea0],
      fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 12
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x28 pd3_at_3c (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x3E pd3_at_3c (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The doubling**, from limb `i` to the loop's exit at 0x3E: the buffer
at `F` and the carry in `s3` hold twice the buffer's value at the loop's
start, in `M1`. -/
theorem pd_dbl_loop {P F : Word} {M1 : Word → BitVec 8} (hF : F.toNat % 4 = 0)
    (hFw : F.toNat + 0x30 ≤ 2 ^ 32) (sC : Sep F 0x30 P p384DoubleCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {c : Word},
      St M P n 0x28 (reg n) → CodeIn M P p384DoubleCode → (∀ x, Sep F 0x30 x 1 → M x = M1 x) →
      (∀ j, i ≤ j → j < 12 → memLoad32 M (F + BitVec.ofNat 32 (4 * j)) = memLoad32 M1 (F + BitVec.ofNat 32 (4 * j))) →
      c.toNat ≤ 1 → accV M F i + 2 ^ (32 * i) * c.toNat = 2 * accV M1 F i →
      reg n 8 = F + BitVec.ofNat 32 (4 * i) → reg n a0 = BitVec.ofNat 32 (12 - i) → reg n 19 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x3E (reg n') ∧ CodeIn M' P p384DoubleCode ∧
        (∀ x, Sep F 0x30 x 1 → M' x = M1 x) ∧ (reg n' 19).toNat ≤ 1 ∧
        accV M' F 12 + 2 ^ (32 * 12) * (reg n' 19).toNat = 2 * accV M1 F 12 ∧
        ∀ q, pdDblKeep q = true → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {c : Word},
      St M P n 0x28 (reg n) → CodeIn M P p384DoubleCode → (∀ x, Sep F 0x30 x 1 → M x = M1 x) →
      (∀ j, i ≤ j → j < 12 → memLoad32 M (F + BitVec.ofNat 32 (4 * j)) = memLoad32 M1 (F + BitVec.ofNat 32 (4 * j))) →
      c.toNat ≤ 1 → accV M F i + 2 ^ (32 * i) * c.toNat = 2 * accV M1 F i →
      reg n 8 = F + BitVec.ofNat 32 (4 * i) → reg n a0 = BitVec.ofNat 32 (12 - i) → reg n 19 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x28 else 0x3E) (reg n') ∧
        CodeIn M' P p384DoubleCode ∧ (∀ x, Sep F 0x30 x 1 → M' x = M1 x) ∧
        (∀ j, i + 1 ≤ j → j < 12 →
          memLoad32 M' (F + BitVec.ofNat 32 (4 * j)) = memLoad32 M1 (F + BitVec.ofNat 32 (4 * j))) ∧
        (reg n' 19).toNat ≤ 1 ∧
        accV M' F (i + 1) + 2 ^ (32 * (i + 1)) * (reg n' 19).toNat = 2 * accV M1 F (i + 1) ∧
        reg n' 8 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, pdDblKeep q = true → reg n' q = reg n q := by
    intro i hi M n c s hc hfr hab hcb hv r8 ra0 r19
    have sCi : Sep (F + BitVec.ofNat 32 (4 * i)) 4 P p384DoubleCode.length := sC.sub (by omega)
    obtain ⟨n1, c1, u1, e19, e8, ea0, fr⟩ := pd_dbl_iter s hc hi hF sCi r8 ra0 r19
    have eL := hab i (Nat.le_refl i) hi
    rw [eL] at u1 e19
    obtain ⟨hv1, hc1⟩ := dbl_val (memLoad32 M1 (F + BitVec.ofNat 32 (4 * i))) c hcb
    refine ⟨n1, _, c1, u1, hc.store32 sCi, fun x hx => ?_, fun j hj1 hj2 => ?_, by rw [e19]; exact hc1, ?_, e8, ea0, fr⟩
    · rw [memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), hfr x hx]
    · rw [memLoad32_store32_sep (sep_offsets F (.inl (by omega)) (by omega) (by omega)), hab j (by omega) hj2]
    · rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same, accV_succ1,
        pow32_succ, e19]
      exact dbl_arith hv hv1
  intro m
  induction m with
  | zero =>
    intro i hi M n c s hc hfr hab hcb hv r8 ra0 r19
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M', c1, u1, hc1, hf1, _, hb1, hv1, _, _, fr⟩ := step 11 (by decide) s hc hfr hab hcb hv r8 ra0 r19
    exact ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, fr⟩
  | succ m ih =>
    intro i hi M n c s hc hfr hab hcb hv r8 ra0 r19
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M', c1, u1, hc1, hf1, ha1, hb1, hv1, e8, ea0, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hfr hab hcb hv r8 ra0 r19
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M'', c', u', hc', hf', hb', hv', fr'⟩ := ih (i + 1) (sel_succ hi) u1 hc1 hf1 ha1 hb1 hv1 e8 ea0 rfl
    exact ⟨n', M'', c1.trans c', u', hc', hf', hb', hv', fun q hq => by rw [fr' q hq, fr q hq]⟩

/-- `borrowing_sub`'s offset from `double`. -/
abbrev pdBsub (P : Word) : Word := P + 0xFFFEE3C8

/-- **One round of the final subtraction**, from 0x62: subtract limb `i` of
the modulus and the borrow from limb `i` of the accumulator, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem pd_sub_iter {M : Word → BitVec 8} {P F acc np D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x62 (reg n)) (hc : CodeIn M P p384DoubleCode) (hb : CodeIn M (pdBsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 12) (hF : F.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (pdBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P p384DoubleCode.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P p384DoubleCode.length)
    (rsp : reg n sp = F) (r9 : reg n (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * i))
    (r23 : reg n (8 : Fin 32) = np + BitVec.ofNat 32 (4 * i)) (r19 : reg n (20 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (r8 : reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 12 then 0x62 else 0x80) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (20 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
        q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc pd3_at_62 (off' := 0x66) (by decide)
    (by rw [r9, add_lit_zero]; exact aligned_add hacc (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc pd3_at_66 (off' := 0x68) (by decide)
    (by rw [upd_ne (by decide) (by decide), r23, add_lit_zero]; exact aligned_add hnp (by omega))
  rw [r9, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (8 : Fin 32) + 0)) a0 =
      memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (8 : Fin 32) + 0)) a1 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [r23, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0xFFFEE3C8 (by decide))
    pd3_at_68 pd3_at_6c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x68 + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P p384DoubleCode := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have e19 : reg n3 (20 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block p3SubTail u3 hc3 pdSubTail_end
    (p3SubTail_ok (by rw [e19]; exact aligned_add hD (by omega)) (by rw [e19]; exact sDC))
  obtain ⟨em4, t2, t9, t23, t19, t8, tk⟩ := p3SubTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, e19, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock p3SubTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have e8 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) := by
    rw [g4, t8, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, cnt12_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (9 : Fin 32)) (reg n4 x0) = decide (i + 1 < 12) := by
    rw [e8, u4'.zero]; exact cnt12_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (20 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
        q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, e8], fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => ?_⟩
    · rw [h5, g4, t9, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9, ptr4]
    · rw [h5, g4, t23, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r23, ptr4]
    · rw [h5, g4, t19, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, ptr4]
    · rw [h5, g4, tk q q2 q9 q23 q19 q8, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x62 pd3_at_7e (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x80 pd3_at_7e (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The final subtraction**, from round `i` to its end at 0x80: the
buffer at `D` gets the accumulator minus the modulus, and `a2` the borrow
out as a mask. -/
theorem pd_sub_loop {P F acc np D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hacc : acc.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 48 ≤ 2 ^ 32)
    (sFA : Sep (F + 0xFFFFFFFC) 4 acc 48) (sFN : Sep (F + 0xFFFFFFFC) 4 np 48) (sFD : Sep (F + 0xFFFFFFFC) 4 D 48)
    (sDA : Sep D 48 acc 48) (sDN : Sep D 48 np 48)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (pdBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P p384DoubleCode.length)
    (sDB : Sep D 48 (pdBsub P) borrowingSubCode.length) (sDC : Sep D 48 P p384DoubleCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x62 (reg n) → CodeIn M P p384DoubleCode → CodeIn M (pdBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (20 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x80 (reg n') ∧ CodeIn M' P p384DoubleCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc 12 + 2 ^ (32 * 12) * maskBit (reg n' a2) = accV M0 np 12 + accV M' D 12 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
          q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x62 (reg n) → CodeIn M P p384DoubleCode → CodeIn M (pdBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (20 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x62 else 0x80) (reg n') ∧
        CodeIn M' P p384DoubleCode ∧ CodeIn M' (pdBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 np (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (20 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
          q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, e9, e23, e19, e8, fr⟩ := pd_sub_iter (i := i) s hc hb hP hi hF hacc hnp hD
      sFB sFC (sDC.sub (by omega)) rsp r9 r23 r19 r8 ra2
    have eA : memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFA.subR (by omega)) (sDA.subR (by omega))
    have eN : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (pdBsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P p384DoubleCode := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, e9, e23, e19, e8, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e2]
      exact sub_arith hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, e9, e23, e19, e8, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 e9 e23 e19 e8 rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => by
      rw [fr' q q0 q1 q2 q3 q4 qr q9 q23 q19 q8, fr q q0 q1 q2 q3 q4 qr q9 q23 q19 q8]⟩



/-- Where `double` runs: its code and its callees' at their offsets from an
even `P`, the modulus where the image keeps it, the 0xD0 bytes of stack
below `sp0` that it, `borrowing_sub`, and `Uint<12>::select` use, the
12-word result at `out`, and the operand at `sf`, all apart where they
must be. -/
structure PDEnv (M : Word → BitVec 8) (P sp0 out sf : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384DoubleCode
  mset : CodeIn M (P + 0x88E) memsetCode
  bsub : CodeIn M (pdBsub P) borrowingSubCode
  stub : CodeIn M (P + 0x8F6) memcpyStubCode
  body : CodeIn M (P + 0x8FE) memcpyBodyCode
  sel : CodeIn M (P + 0xFFFFEF10) uintSelect12Code
  pmod : CodeIn M p3M p384ModulusData
  hsp : sp0.toNat % 4 = 0
  hS : 0xD0 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hsf : sf.toNat % 4 = 0
  hwo : out.toNat + 48 < 2 ^ 32
  sSC : Sep (sp0 + 0xFFFFFF30) 0xD0 P p384DoubleCode.length
  sSM : Sep (sp0 + 0xFFFFFF30) 0xD0 (P + 0x88E) memsetCode.length
  sSB : Sep (sp0 + 0xFFFFFF30) 0xD0 (pdBsub P) borrowingSubCode.length
  sSU : Sep (sp0 + 0xFFFFFF30) 0xD0 (P + 0x8F6) memcpyStubCode.length
  sSY : Sep (sp0 + 0xFFFFFF30) 0xD0 (P + 0x8FE) memcpyBodyCode.length
  sSL : Sep (sp0 + 0xFFFFFF30) 0xD0 (P + 0xFFFFEF10) uintSelect12Code.length
  sSP : Sep (sp0 + 0xFFFFFF30) 0xD0 p3M 48
  sOC : Sep out 48 P p384DoubleCode.length
  sOL : Sep out 48 (P + 0xFFFFEF10) uintSelect12Code.length
  sOY : Sep out 48 (P + 0x8FE) memcpyBodyCode.length
  sOS : Sep out 48 (sp0 + 0xFFFFFF30) 0xD0
  sFS : Sep sf 48 (sp0 + 0xFFFFFF30) 0xD0

theorem pdG_F (sp0 : Word) : sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x50 = sp0 + 0xFFFFFF80 := by
  rw [BitVec.add_assoc]; rfl

theorem pdG_w (sp0 : Word) (h : 0xD0 ≤ sp0.toNat) : (sp0 + 0xFFFFFF30).toNat + 0xD0 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFF30 : Word).toNat = 4294967088 := rfl
  have := sp0.isLt
  omega

/-- A range in the frame `F = G + 0x50` is in the region at `G`. -/
theorem pdinF {sp0 x : Word} {c l : Nat} (h : c + l ≤ 0x80) (hx : Sep (sp0 + 0xFFFFFF30) 0xD0 x 1) :
    Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) l x 1 := by
  rw [← pdG_F, add_ofNat_assoc]; exact hx.sub (by omega)

theorem pdinF' {sp0 b : Word} {c l k : Nat} (h : c + l ≤ 0x80) (hx : Sep (sp0 + 0xFFFFFF30) 0xD0 b k) :
    Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) l b k := by
  rw [← pdG_F, add_ofNat_assoc]; exact hx.sub (by omega)

theorem pdF4 (sp0 : Word) : sp0 + 0xFFFFFF80 + 0xFFFFFFFC = sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x4C := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem pdtoG {sp0 b : Word} {k : Nat} (h : Sep (sp0 + 0xFFFFFF30) 0xD0 b k) :
    Sep (sp0 + 0xFFFFFF80 + 0xFFFFFFFC) 0x84 b k := by
  rw [pdF4]; exact h.sub (by decide)

theorem pdtoG4 {sp0 b : Word} {k : Nat} (h : Sep (sp0 + 0xFFFFFF30) 0xD0 b k) :
    Sep (sp0 + 0xFFFFFF80 + 0xFFFFFFFC) 4 b k := by
  rw [pdF4]; exact h.sub (by decide)

set_option maxRecDepth 20000 in
theorem pdPs_range : ∀ p ∈ pdPs, p.2.toNat % 4 = 0 ∧ 0x64 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x80 := by decide

set_option maxRecDepth 20000 in
theorem pdPs_sp : ∀ p ∈ pdPs, p.1 ≠ sp := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `double`'s prologue, from entry to the doubling loop at 0x28: save the
registers and copy the operand to the frame at `F`. -/
theorem pd_pro (m : Machine) {P sp0 out sf : Word} (env : PDEnv m.mem P sp0 out sf) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = sf) (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x28 (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ pdPs → memLoad32 M (sp0 + 0xFFFFFF80 + o) = reg m r) ∧
      (∀ j, j < 12 → memLoad32 M (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 (4 * j)) =
        memLoad32 m.mem (sf + BitVec.ofNat 32 (4 * j))) ∧
      reg n sp = sp0 + 0xFFFFFF80 ∧ reg n 8 = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 (4 * 0) ∧
      reg n a0 = BitVec.ofNat 32 (12 - 0) ∧ reg n 19 = 0 ∧ reg n 18 = out ∧
      ∀ q, p3Keep q = true → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGw := pdG_w sp0 env.hS
  have hFa : (sp0 + 0xFFFFFF80).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF80) (by decide)
  have hFw : (sp0 + 0xFFFFFF80).toNat + 0x80 ≤ 2 ^ 32 := by
    rw [← pdG_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sFC : Sep (sp0 + 0xFFFFFF80) 0x80 P p384DoubleCode.length := by
    have := pdinF' (c := 0) (l := 0x80) (by decide) env.sSC; rwa [add_ofNat_zero] at this
  have fF : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → Sep (sp0 + 0xFFFFFF80) 0x80 x 1 := fun x hx => by
    have := pdinF (c := 0) (l := 0x80) (by decide) hx; rwa [add_ofNat_zero] at this
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code pd3_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80) sp = sp0 + 0xFFFFFF80 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock pdPs) u1 env.code pdSave_end (saveBlock_ok _ pdPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (pdPs_range p hp).1, frm_sep' sFC (by have := pdPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (sp0 + 0xFFFFFF80)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80)) pdPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside pdPs fun p hp => frm_sep' (fF x hx) (by have := pdPs_range p hp; omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF30) 0xD0 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have k2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q hq => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, hq]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFF80 := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block pdPro u2.self (cIn env.code env.sSC frSv) pdPro_end
    (by simp [BlockOk, BInstr.ok, pdPro])
  simp only [runBlock, BInstr.run, pdPro] at u3
  have g3 : ∀ q, reg m3 q = _ := u3.regs
  have e8 : P + 0x8F6 + 8 = P + 0x8FE := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m4, c4, u4, a04, k4⟩ := St.memcpyW (B := P + 0x8F6) (w := 12) (dst := sp0 + 0xFFFFFF80) (src := sf)
    (even_at P env.hP 0x8F6 (by decide)) u3.self (cIn env.code env.sSC frSv) (cIn env.stub env.sSU frSv)
    (by rw [e8]; exact cIn env.body env.sSY frSv) pd3_at_1a pd3_at_1e
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x1A + 8) (by decide))
    (by decide) (by omega) (by decide) hFa env.hsf
    (by have := pdinF' (c := 0) (l := 4 * 12) (by decide) env.sFS.symm; rwa [add_ofNat_zero] at this)
    (by rw [e8]; have := pdinF' (c := 0) (l := 4 * 12) (by decide) env.sSY; rwa [add_ofNat_zero] at this)
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact BitVec.zero_add _)
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte]; rw [k2 a1 (by decide), ha1])
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  obtain ⟨Mc, hMc⟩ : ∃ Mc, copyWords Msv (sp0 + 0xFFFFFF80) sf 12 = Mc := ⟨_, rfl⟩
  rw [hMc] at u4
  have frC : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → Mc x = m.mem x := fun x hx => by
    have h48 : Sep (sp0 + 0xFFFFFF80) (4 * 12) x 1 := by
      have := pdinF (c := 0) (l := 4 * 12) (by decide) hx; rwa [add_ofNat_zero] at this
    rw [← hMc, copyWords_outside 12 h48, frSv x hx]
  have cC := cIn env.code env.sSC frC
  obtain ⟨m5, c5, u5⟩ := St.block pdDblInit u4 cC pdDblInit_end (by simp [BlockOk, BInstr.ok, pdDblInit])
  simp only [runBlock, BInstr.run, pdDblInit] at u5
  have x10 : reg m5 a0 = 0xC := by rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨m6, d6, u6⟩ := u5.self.notTaken cC 0x28 pd3_at_26 (by decide) (by rw [x10, u5.self.zero]; decide)
  have k5 : ∀ q, q ≠ a0 → q ≠ (19 : Fin 32) → reg m6 q = reg m4 q := fun q h1 h2 => by
    rw [u6.regs, u5.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, u4.zero]
    · simp [upd, h0, h1, h2]
  have k3 : ∀ q, q.val ≠ 0 → q ≠ (18 : Fin 32) → q ≠ a0 → q ≠ a2 → q ≠ (8 : Fin 32) → reg m3 q = reg m2 q :=
    fun q h0 h18 h10 h12 h8 => by
      rw [g3]; simp only [upd_app, h0, h18, h10, h12, h8, ite_false]
  have k4' : ∀ q, p3Keep q = true → reg m4 q = reg m3 q := fun q hq => by
    have k := fun r (hr : p3Keep r = false) => pkeep_ne hq hr
    exact k4 q (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl) (k t0 rfl) (k t1 rfl)
      (k ra rfl)
  have r4 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ ra →
      reg m6 q = reg m3 q ∨ q = a0 ∨ q = (19 : Fin 32) := fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
    by_cases e0 : q = a0
    · exact .inr (.inl e0)
    by_cases e19 : q = (19 : Fin 32)
    · exact .inr (.inr e19)
    exact .inl (by rw [k5 q e0 e19, k4 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10])
  have sp6 : reg m6 sp = sp0 + 0xFFFFFF80 := by
    rw [k5 sp (by decide) (by decide), k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
      k3 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  refine ⟨m6, Mc, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.single d6))))), u6.self, frC, ?_, ?_, sp6,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro r o h
    obtain ⟨_, ho1, ho2⟩ := pdPs_range (r, o) h
    dsimp only at ho1 ho2
    have hs : Sep (sp0 + 0xFFFFFF80) (4 * 12) (sp0 + 0xFFFFFF80 + o) 4 := by
      have := sep_offsets (sp0 + 0xFFFFFF80) (c := 0) (n := 4 * 12) (d := o.toNat) (k := 4) (.inl (by omega))
        (by decide) (by omega)
      rwa [add_ofNat_zero, ofNat_toNat_self] at this
    rw [← hMc, copyWords_load_sep hs, ← hMsv]
    simp only [pdPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  · intro j hj
    rw [← hMc, copyWords_load 12 j hj (by omega)]
    exact load_frame frSv (env.sFS.symm.subR (c := 4 * j) (l := 4) (by omega))
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [sp2]; exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [u6.regs, x10]; rfl
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [u4.zero]; rfl
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a0 (by decide), ha0]; exact BitVec.zero_add _
  · intro q hq
    have k := fun r (hr : p3Keep r = false) => pkeep_ne hq hr
    rw [k5 q (k a0 rfl) (k 19 rfl), k4' q hq,
      k3 q (fun e => k 0 rfl (Fin.ext e)) (k 18 rfl) (k a0 rfl) (k a2 rfl) (k 8 rfl), k2 q (k sp rfl)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the doubling loop's exit at 0x3E to the subtraction loop at 0x62: zero the
difference buffer at `F + 0x30` and point at the sum and the modulus. -/
theorem pd_mid {M : Word → BitVec 8} {P F : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x3E (reg n)) (hc : CodeIn M P p384DoubleCode) (hms : CodeIn M (P + 0x88E) memsetCode)
    (hF : F.toNat % 4 = 0) (hFw : F.toNat + 0x80 ≤ 2 ^ 32)
    (sM : Sep (F + BitVec.ofNat 32 0x30) (4 * 12) (P + 0x88E) memsetCode.length)
    (sC : Sep (F + BitVec.ofNat 32 0x30) (4 * 12) P p384DoubleCode.length) (rsp : reg n sp = F) :
    ∃ n', Steps n n' ∧ St (fillWords M (F + BitVec.ofNat 32 0x30) 0 12) P n' 0x62 (reg n') ∧
      reg n' sp = F ∧ reg n' 21 = F + BitVec.ofNat 32 (4 * 0) ∧ reg n' 8 = p3M + BitVec.ofNat 32 (4 * 0) ∧
      reg n' 20 = F + BitVec.ofNat 32 0x30 + BitVec.ofNat 32 (4 * 0) ∧ reg n' 9 = BitVec.ofNat 32 (12 - 0) ∧
      reg n' a2 = 0 ∧
      ∀ q, p3MidKeep q = true → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block p3Mid s hc pdMid_end (by simp [BlockOk, BInstr.ok, p3Mid])
  simp only [runBlock, BInstr.run, p3Mid] at u1
  obtain ⟨n2, c2, u2, a02, k2⟩ := St.memsetW (B := P + 0x88E) (w := 12) (dst := F + BitVec.ofNat 32 0x30)
    (even_at P hP 0x88E (by decide)) u1.self hc hms pd3_at_4a pd3_at_4e
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x4A + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (aligned_add hF (by decide)) sM
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  have hc2 : CodeIn (fillWords M (F + BitVec.ofNat 32 0x30) 0 12) P p384DoubleCode := fun i hi => by
    rw [fillWords_outside 12 (sC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  obtain ⟨n3, c3, u3⟩ := St.block p3SubInit u2 hc2 pdSubInit_end (by simp [BlockOk, BInstr.ok, p3SubInit])
  simp only [runBlock, BInstr.run, p3SubInit] at u3
  have z2 : reg n2 0 = 0 := u2.zero
  have x9 : reg n3 9 = 0xC := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc2 0x62 pd3_at_60 (by decide) (by rw [x9, u3.self.zero]; decide)
  have k1 : ∀ q, p3MidKeep q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl]
  have k3 : ∀ q, p3MidKeep q = true → reg n4 q = reg n2 q := fun q hq => by
    rw [u4.regs, u3.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl,
      upd_kp hq rfl rfl]
  have sp2 : reg n2 sp = F := by
    rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k1 sp rfl, rsp]
  refine ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), u4.self, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [k3 sp rfl, sp2]
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]
    exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u1.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; exact (add_ofNat_zero _).symm
  · rw [u4.regs, x9]; rfl
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [z2]; rfl
  · rw [k3 q hq, k2 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl), k1 q hq]


/-- The registers from the subtraction loop's exit to the call to
`Uint<12>::select` leave alone. -/
def pdTailKeep (q : Fin 32) : Bool := q.val ∉ [0, 1, 8, 10, 11, 12, 13, 14]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the subtraction loop's exit at 0x80 to the call to
`Uint<12>::select` at 0xAE: the choice through a byte of the frame, a
`borrowing_sub` whose result goes unused, and the select's arguments. -/
theorem pd_tail {M : Word → BitVec 8} {P F c b : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x80 (reg n)) (hc : CodeIn M P p384DoubleCode) (hbs : CodeIn M (pdBsub P) borrowingSubCode)
    (hF : F.toNat % 4 = 0)
    (sC : Sep (F + 0xFFFFFFFC) 0x84 P p384DoubleCode.length)
    (sB : Sep (F + 0xFFFFFFFC) 0x84 (pdBsub P) borrowingSubCode.length)
    (rsp : reg n sp = F) (r19 : reg n 19 = c) (ra2 : reg n a2 = b) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0xAE (reg n') ∧
      (∀ x, Sep (F + BitVec.ofNat 32 0x60) 4 x 1 → Sep (F + 0xFFFFFFFC) 4 x 1 → M' x = M x) ∧
      reg n' sp = F ∧ reg n' a0 = reg n 18 ∧ reg n' a1 = F + 0x30 ∧ reg n' a2 = F ∧
      reg n' a3 = aluEval .and (aluEval .sltu c 1) b ∧
      ∀ q, pdTailKeep q = true → reg n' q = reg n q := by
  have frm4 : F + 0xFFFFFFFC + BitVec.ofNat 32 4 = F := by
    rw [BitVec.add_assoc, show (0xFFFFFFFC : Word) + BitVec.ofNat 32 4 = 0 from rfl]; exact add_lit_zero F
  have sCF : Sep F 0x80 P p384DoubleCode.length := by
    have := sC.sub (c := 4) (l := 0x80) (by decide); rwa [frm4] at this
  have a60 : (F + 0x60).toNat % 4 = 0 := fr_al hF (by decide)
  have s60 : Sep (F + 0x60) 4 P p384DoubleCode.length := frm_sep sCF (by decide)
  have s60' : Sep (F + 0x60) 1 P p384DoubleCode.length := by
    have := s60.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨n1, c1, u1⟩ := St.block pdTail s hc pdTail_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, pdTail, upd_app, ↓reduceIte, and_true, true_and]
    rw [rsp]; exact ⟨⟨a60, s60⟩, a60, s60'⟩)
  simp +decide only [runBlock, BInstr.run, pdTail, upd_app, ↓reduceIte] at u1
  rw [rsp, r19, memLoad32_store32_same, ra2] at u1
  obtain ⟨Mt0, hMt0⟩ : ∃ Mt0, memStore8 (memStore32 M (F + 96) c) (F + 96)
      (BitVec.extractLsb' 0 8 (aluEval AluOp.and (aluEval AluOp.sltu c 1) b)) = Mt0 := ⟨_, rfl⟩
  rw [hMt0] at u1
  have s1of4 : ∀ {a b : Word} {k : Nat}, Sep a 4 b k → Sep a 1 b k := fun h => by
    have := h.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  have code0 : ∀ {base : Word} {code : List Nat}, CodeIn M base code → Sep (F + 0x60) 4 base code.length →
      CodeIn Mt0 base code := fun h hs => by
    rw [← hMt0]; exact (h.store32 hs).store8 (s1of4 hs)
  have frm4' : ∀ {b : Word} {k : Nat}, Sep (F + 0xFFFFFFFC) 0x84 b k → Sep (F + 0x60) 4 b k := fun h => by
    have := h.sub (c := 0x64) (l := 4) (by decide)
    rwa [BitVec.add_assoc, show (0xFFFFFFFC : Word) + BitVec.ofNat 32 0x64 = 0x60 from rfl] at this
  have hb1 : CodeIn Mt0 (pdBsub P) borrowingSubCode := code0 hbs (frm4' sB)
  have hc1 : CodeIn Mt0 P p384DoubleCode := code0 hc (frm4' sC)
  have r1 : ∀ q, pdTailKeep q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; repeat rw [upd_kp hq rfl rfl]
  have sp1 : reg n1 sp = F := (r1 sp rfl).trans rsp
  have x8 : reg n1 8 = aluEval .and (aluEval .sltu c 1) b := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
  have x18 : reg n1 18 = reg n 18 := r1 18 rfl
  obtain ⟨n2, c2, u2, _, _, sp2, fr2, mem2⟩ := u1.self.bsubCall hc1 hb1 (even_at P hP 0xFFFEE3C8 (by decide))
    pd3_at_9e pd3_at_a2 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x9E + 8) (by decide))
    sp1 hF (by have := sB.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  have hc2 : CodeIn n2.mem P p384DoubleCode := fun i hi => by
    have h4 : Sep (F + 0xFFFFFFFC) 4 P p384DoubleCode.length := by
      have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [mem2 _ (h4.subR (c := i) (l := 1) (by omega))]; exact hc1 i hi
  obtain ⟨n3, c3, u3⟩ := St.block pdSelArgs u2 hc2 pdSelArgs_end (by simp [BlockOk, BInstr.ok, pdSelArgs])
  simp only [runBlock, BInstr.run, pdSelArgs] at u3
  refine ⟨n3, _, c1.trans (c2.trans c3), u3.self, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hG
    have h4 : Sep (F + 96) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have hne : x ≠ F + 96 := fun e => by
      have := hx.point (i := 0) (j := 0) (by decide) (by decide)
      rw [add_ofNat_zero, add_ofNat_zero] at this; exact this e.symm
    rw [mem2 x hG, ← hMt0, memStore8_ne hne, memStore32_get_sep h4]
  · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp2
  · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x18]
    exact BitVec.zero_add _
  · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; rfl
  · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact BitVec.zero_add _
  · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x8]
    exact BitVec.zero_add _
  · intro q hq
    rw [u3.regs]
    repeat rw [upd_kp hq rfl rfl]
    rw [fr2 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl), r1 q hq]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `double`'s epilogue, from 0xB6: restore the saved registers and return. -/
theorem pd_epi {P sp0 : Word} {Mx : Word → BitVec 8} {n : Machine} {v : Fin 32 → Word}
    (hFa : (sp0 + 0xFFFFFF80).toNat % 4 = 0) (s : St Mx P n 0xB6 (reg n)) (hc : CodeIn Mx P p384DoubleCode)
    (hsl : ∀ r o, (r, o) ∈ pdPs → memLoad32 Mx (sp0 + 0xFFFFFF80 + o) = v r)
    (rsp : reg n sp = sp0 + 0xFFFFFF80) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧ n'.mem = Mx ∧
      reg n' sp = sp0 ∧ (∀ r o, (r, o) ∈ pdPs → reg n' r = v r) ∧
      ∀ q, p3Keep q = true → reg n' q = reg n q := by
  obtain ⟨n3, c3, u3⟩ := St.block (restoreBlock pdPs) s hc pdRestore_end
    (restoreBlock_ok Mx _ pdPs (reg n) rsp pdPs_sp fun p hp => fr_al' hFa (pdPs_range p hp).1)
  simp only [restoreBlock_run Mx _ pdPs (reg n) rsp pdPs_sp] at u3
  have rsp3 : restoreRegs Mx (sp0 + 0xFFFFFF80) (reg n) pdPs sp = sp0 + 0xFFFFFF80 := by
    rw [restoreRegs_sp _ _ _ _ pdPs_sp]; exact rsp
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc pd3_at_c4 (off' := 0xC6) (by decide)
  obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.jalr hc pd3_at_c6
  refine ⟨n5, c3.trans (.cons d4 (.single d5)), ?_, mem5, ?_, ?_, ?_⟩
  · rw [pc5]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, hsl ra 0x7C (by decide)]
  · rw [regs5]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp3, BitVec.add_assoc]
    exact BitVec.add_zero _
  · intro r o h
    rw [regs5]
    simp only [pdPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hsl _ _ (by decide)
  · intro q hq
    rw [regs5, upd_kp hq rfl rfl]
    simp only [restoreRegs]
    repeat rw [upd_kp hq rfl rfl]

theorem pdKeep_dbl : ∀ q, p3Keep q = true → pdDblKeep q = true := by decide
theorem pdKeep_tail : ∀ q, p3Keep q = true → pdTailKeep q = true := by decide
theorem pdKeep_sel : ∀ q, p3Keep q = true → selKeep q = true := by decide

theorem pdG_D (sp0 : Word) : sp0 + 0xFFFFFF30 + BitVec.ofNat 32 0x80 = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem pdF_S (sp0 : Word) : sp0 + 0xFFFFFF80 + 0xFFFFFFB0 = sp0 + 0xFFFFFF30 := by
  rw [BitVec.add_assoc]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `<p384::arithmetic::field::FieldElement as ff::Field>::double`**,
called with the result at `out` and a 12-limb operand `A` at `sf`. It stores
`p3AddRes A A`, which is `2 A mod p` for an operand below `p`
(`p3AddRes_mod`). It returns with `sp` and every register but `a0` through
`a7`, `t0`, and `t1` as they were, and changes no memory outside the 0xD0
bytes of stack below `sp` and the result. -/
theorem p384Double_correct (m : Machine) {P sp0 out sf retAddr : Word}
    (env : PDEnv m.mem P sp0 out sf) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = sf)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem out 12) = p3AddRes (limbVal (wordsAt m.mem sf 12)) (limbVal (wordsAt m.mem sf 12)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  have hGw := pdG_w sp0 env.hS
  have hFa : (sp0 + 0xFFFFFF80).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF80) (by decide)
  have hFw : (sp0 + 0xFFFFFF80).toNat + 0x80 ≤ 2 ^ 32 := by
    rw [← pdG_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have toF : ∀ {b : Word} {k : Nat} {c l : Nat}, c + l ≤ 0x80 → Sep (sp0 + 0xFFFFFF30) 0xD0 b k →
      Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) l b k := fun h hs => pdinF' h hs
  have toF0 : ∀ (b : Word) (k l : Nat), l ≤ 0x80 → Sep (sp0 + 0xFFFFFF30) 0xD0 b k →
      Sep (sp0 + 0xFFFFFF80) l b k := fun b k l h hs => by
    have := pdinF' (c := 0) (l := l) (by omega) hs; rwa [add_ofNat_zero] at this
  have toS : ∀ {b : Word} {k : Nat}, Sep (sp0 + 0xFFFFFF30) 0xD0 b k → Sep (sp0 + 0xFFFFFF30) 0x50 b k := fun h => by
    have := h.sub (c := 0) (l := 0x50) (by decide); rwa [add_ofNat_zero] at this
  have cOf : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF30) 0xD0 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  -- the prologue and the copy
  obtain ⟨n1, M1, c1, s1, fr1, hsl, hcp, sp1, r8, ra0, r19, r18, k1⟩ := pd_pro m env hpc ha0 ha1 hsp
  -- the doubling
  obtain ⟨n2, M2, c2, s2, cM2, fr2, hc2, hv2, k2⟩ := pd_dbl_loop (M1 := M1) hFa (by omega)
    (toF0 _ _ _ (by decide) env.sSC) 11 0 rfl (M := M1) (n := n1) (c := 0) s1
    (cOf env.code env.sSC fr1) (fun _ _ => rfl) (fun _ _ _ => rfl) (Nat.zero_le 1) (by simp [accV]) r8 ra0 r19
  have frM2 : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → M2 x = m.mem x := fun x hx => by
    rw [fr2 x (toF0 _ _ _ (by decide) hx), fr1 x hx]
  have sp2 : reg n2 sp = sp0 + 0xFFFFFF80 := by rw [k2 sp rfl, sp1]
  -- zero the difference buffer
  obtain ⟨n3, c3, s3, sp3, r21_3, r8_3, r20_3, r9_3, ra2_3, k3⟩ := pd_mid env.hP s2 cM2
    (cOf env.mset env.sSM frM2) hFa hFw (toF (by decide) env.sSM) (toF (by decide) env.sSC) sp2
  obtain ⟨M3, hM3⟩ : ∃ M3, fillWords M2 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30) 0 12 = M3 := ⟨_, rfl⟩
  rw [hM3] at s3
  have frM3 : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, fillWords_outside 12 (pdinF (by decide) hx), frM2 x hx]
  -- the difference
  have hD : (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30).toNat % 4 = 0 := aligned_add hFa (by decide)
  have sDF : Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30) 48 (sp0 + 0xFFFFFF80) 48 := by
    have := sep_offsets (sp0 + 0xFFFFFF80) (c := 0x30) (n := 48) (d := 0) (k := 48) (.inr (by decide)) (by decide)
      (by decide)
    rwa [add_ofNat_zero] at this
  have sGo : ∀ d k, 0x4C + 4 ≤ d → d + k ≤ 0xD0 →
      Sep (sp0 + 0xFFFFFF80 + 0xFFFFFFFC) 4 (sp0 + 0xFFFFFF30 + BitVec.ofNat 32 d) k := fun d k h1 h2 => by
    rw [pdF4]; exact sep_offsets _ (.inl h1) (by decide) (by omega)
  have sFo : ∀ d k, d + k ≤ 0x80 →
      Sep (sp0 + 0xFFFFFF80 + 0xFFFFFFFC) 4 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 d) k := fun d k h2 => by
    rw [pdF4, ← pdG_F, add_ofNat_assoc]; exact sep_offsets _ (.inl (by omega)) (by decide) (by omega)
  obtain ⟨n4, M4, c4, s4, cM4, fr4, hb4, hv4, sp4, k4⟩ := pd_sub_loop (M0 := M3) env.hP hFa hFa
    (show p3M.toNat % 4 = 0 by decide) hD (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by have := sGo 0x50 48 (by decide) (by decide); rwa [pdG_F] at this)
    (pdtoG4 env.sSP)
    (by have := sGo 0x80 48 (by decide) (by decide); rwa [pdG_D] at this)
    sDF (toF (by decide) env.sSP) (pdtoG4 env.sSB) (pdtoG4 env.sSC) (toF (by decide) env.sSB) (toF (by decide) env.sSC)
    11 0 rfl s3 (cOf env.code env.sSC frM3) (cOf env.bsub env.sSB frM3) (fun _ _ _ => rfl) (.inl rfl)
    (by simp [accV, maskBit]) sp3 r21_3 r8_3 r20_3 r9_3 ra2_3
  have inD : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30) 48 x 1 :=
    fun x hx => pdinF (by decide) hx
  have frM4 : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → M4 x = m.mem x := fun x hx => by
    rw [fr4 x (pdtoG4 hx) (inD x hx), frM3 x hx]
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
      q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → reg n4 q = reg n3 q := k4
  have r19_4 : reg n4 19 = reg n2 19 := by
    rw [k4' 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k3 19 rfl]
  have r18_4 : reg n4 18 = out := by
    rw [k4' 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k3 18 rfl, k2 18 rfl, r18]
  -- the choice and the select's arguments
  obtain ⟨n5, M5, c5, s5, fr5, sp5, ra0_5, ra1_5, ra2_5, ra3_5, k5⟩ := pd_tail (c := reg n2 19)
    (b := reg n4 a2) env.hP s4 cM4 (cOf env.bsub env.sSB frM4) hFa (pdtoG env.sSC) (pdtoG env.sSB) sp4 r19_4 rfl
  have in60 : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x60) 4 x 1 :=
    fun x hx => pdinF (by decide) hx
  have frM5 : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → M5 x = m.mem x := fun x hx => by
    rw [fr5 x (in60 x hx) (pdtoG4 hx), frM4 x hx]
  have hcc := p3_choice01 (reg n2 19) (reg n4 a2) hc2 hb4
  -- the call to `Uint<12>::select`
  have cM5 := cOf env.code env.sSC frM5
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := s5.callRa cM5 pd3_at_ae pd3_at_b2 (cb := P + 0xFFFFEF10)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFEF10 (by decide))
  have r6 := PEnv.reg1 regs6 s5.zero
  have sp6 : reg m6 sp = sp0 + 0xFFFFFF80 := by rw [r6 _ (by decide), sp5]
  have eSel : reg m6 sp + 0xFFFFFFB0 = sp0 + 0xFFFFFF30 := by rw [sp6]; exact pdF_S sp0
  have eM : P + 0xFFFFEF10 + 0x197E = P + 0x88E := by rw [BitVec.add_assoc]; rfl
  have eU : P + 0xFFFFEF10 + 0x19E6 = P + 0x8F6 := by rw [BitVec.add_assoc]; rfl
  have eB : P + 0xFFFFEF10 + 0x19EE = P + 0x8FE := by rw [BitVec.add_assoc]; rfl
  have hF50 : 0x50 ≤ (sp0 + 0xFFFFFF80).toNat := by
    rw [← pdG_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have SE : SelEnv m6.mem (P + 0xFFFFEF10) (reg m6 sp) out (sp0 + 0xFFFFFF80 + 0x30) (sp0 + 0xFFFFFF80) := by
    rw [mem6]
    refine ⟨even_at P env.hP 0xFFFFEF10 (by decide), cOf env.sel env.sSL frM5, by rw [eM]; exact cOf env.mset env.sSM frM5,
      by rw [eU]; exact cOf env.stub env.sSU frM5, by rw [eB]; exact cOf env.body env.sSY frM5,
      by rw [sp6]; exact hFa, by rw [sp6]; exact hF50, env.hout,
      aligned_add hFa (by decide), hFa, env.hwo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eSel]; exact toS env.sSL
    · rw [eSel, eM]; exact toS env.sSM
    · rw [eSel, eU]; exact toS env.sSU
    · rw [eSel, eB]; exact toS env.sSY
    · rw [eSel]; exact (env.sOS.subR (c := 0) (l := 0x50) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
    · exact env.sOL
    · rw [eB]; exact env.sOY
    · rw [eSel]
      have := sep_offsets (sp0 + 0xFFFFFF30) (c := 0x80) (n := 48) (d := 0) (k := 0x50) (.inr (by decide)) (by decide)
        (by decide)
      rwa [add_ofNat_zero, pdG_D] at this
    · rw [eSel]
      have := sep_offsets (sp0 + 0xFFFFFF30) (c := 0x50) (n := 48) (d := 0) (k := 0x50) (.inr (by decide)) (by decide)
        (by decide)
      rwa [add_ofNat_zero, pdG_F] at this
  obtain ⟨m7, c7, pc7, sp7, w7, mem7, k7⟩ := uintSelect12_correct m6 SE pc6
    (by rw [r6 _ (by decide), ra0_5, r18_4]) (by rw [r6 _ (by decide), ra1_5]) (by rw [r6 _ (by decide), ra2_5])
    (by rw [r6 _ (by decide), ra3_5]) hcc (by rw [regs6]; simp +decide [upd])
    (even_clear _ (even_at P env.hP (0xAE + 8) (by decide)))
  rw [eSel] at mem7
  rw [sp6] at sp7
  have I7 : ∀ x, Sep (sp0 + 0xFFFFFF30) 0xD0 x 1 → Sep out 48 x 1 → m7.mem x = m.mem x := fun x hx ho => by
    rw [mem7 x (toS hx) ho, mem6, frM5 x hx]
  have hc7 : CodeIn m7.mem P p384DoubleCode := fun i hi => by
    rw [I7 _ (env.sSC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have u7 : St m7.mem P m7 0xB6 (reg m7) := ⟨pc7, rfl, fun _ => rfl⟩
  -- the saved registers are where the prologue put them
  have hsl7 : ∀ r o, (r, o) ∈ pdPs → memLoad32 m7.mem (sp0 + 0xFFFFFF80 + o) = reg m r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := pdPs_range (r, o) h
    dsimp only at ho1 ho2
    have e : sp0 + 0xFFFFFF80 + o = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 o.toNat := by rw [ofNat_toNat_self]
    have sF : ∀ c l, c + l ≤ o.toNat → Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) l (sp0 + 0xFFFFFF80 + o) 4 :=
      fun c l hcl => by rw [e]; exact sep_offsets _ (.inl hcl) (by omega) (by omega)
    have sG : Sep (sp0 + 0xFFFFFF80 + 0xFFFFFFFC) 4 (sp0 + 0xFFFFFF80 + o) 4 := by
      rw [e]; exact sFo _ 4 (by omega)
    have sS : Sep (sp0 + 0xFFFFFF30) 0x50 (sp0 + 0xFFFFFF80 + o) 4 := by
      rw [e, ← pdG_F, add_ofNat_assoc]
      have := sep_offsets (sp0 + 0xFFFFFF30) (c := 0) (n := 0x50) (d := 0x50 + o.toNat) (k := 4) (.inl (by omega))
        (by decide) (by omega)
      rwa [add_ofNat_zero] at this
    have sO : Sep out 48 (sp0 + 0xFFFFFF80 + o) 4 := by
      rw [e, ← pdG_F, add_ofNat_assoc]; exact env.sOS.subR (by omega)
    have s0F : Sep (sp0 + 0xFFFFFF80) 0x30 (sp0 + 0xFFFFFF80 + o) 4 := by
      have := sF 0 0x30 (by omega); rwa [add_ofNat_zero] at this
    rw [load_frame2 mem7 sS sO, mem6, load_frame2 fr5 (sF 0x60 4 (by omega)) sG,
      load_frame2 fr4 sG (sF 0x30 48 (by omega)), ← hM3,
      fillWords_load_sep (sF 0x30 (4 * 12) (by omega)), load_frame fr2 s0F, hsl r o h]
  have sp7' : reg m7 sp = sp0 + 0xFFFFFF80 := sp7
  -- the epilogue
  obtain ⟨n8, c8, pc8, mem8, sp8, sv8, k8⟩ := pd_epi (v := reg m) hFa u7 hc7 hsl7 sp7'
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans c8)))))),
    by rw [pc8, hra, hret], sp8, ?_, ?_, ?_⟩
  · intro q q10 q11 q12 q13 q14 q15 q16 q17 q5 q6
    have cat := (by decide : ∀ q : Fin 32, q = 0 ∨ q = sp ∨ q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
      q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ p3Keep q = true ∨
      q = a0 ∨ q = a1 ∨ q = a2 ∨ q = a3 ∨ q = a4 ∨ q = a5 ∨ q = a6 ∨ q = a7 ∨ q = t0 ∨ q = t1) q
    rcases cat with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; rfl
    · subst h; rw [sp8, hsp]
    · subst h; exact sv8 _ 0x7C (by decide)
    · subst h; exact sv8 _ 0x78 (by decide)
    · subst h; exact sv8 _ 0x74 (by decide)
    · subst h; exact sv8 _ 0x70 (by decide)
    · subst h; exact sv8 _ 0x6C (by decide)
    · subst h; exact sv8 _ 0x68 (by decide)
    · subst h; exact sv8 _ 0x64 (by decide)
    · have kq := fun r (hr : p3Keep r = false) => pkeep_ne h hr
      rw [k8 q h, k7 q (pdKeep_sel q h), r6 q (kq ra rfl), k5 q (pdKeep_tail q h), k4' q (kq a0 rfl) (kq a1 rfl)
        (kq a2 rfl) (kq a3 rfl) (kq a4 rfl) (kq ra rfl) (kq 21 rfl) (kq 8 rfl) (kq 20 rfl) (kq 9 rfl),
        k3 q (p3Keep_mid q h), k2 q (pdKeep_dbl q h), k1 q h]
    · exact absurd h q10
    · exact absurd h q11
    · exact absurd h q12
    · exact absurd h q13
    · exact absurd h q14
    · exact absurd h q15
    · exact absurd h q16
    · exact absurd h q17
    · exact absurd h q5
    · exact absurd h q6
  · have sGw : ∀ c, c + 4 ≤ 0x80 → Sep (sp0 + 0xFFFFFF80 + 0xFFFFFFFC) 4 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) 4 :=
      fun c hc => sFo c 4 hc
    have sFw : ∀ a n c, a + n ≤ 0x80 → c + 4 ≤ 0x80 → (a + n ≤ c ∨ c + 4 ≤ a) →
        Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 a) n (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) 4 :=
      fun a n c h1 h2 h3 => sep_offsets _ h3 (by omega) (by omega)
    have eOut : limbVal (wordsAt n8.mem out 12) = accV m7.mem out 12 := by rw [limbVal_wordsAt, mem8]
    have agS : accV m6.mem (sp0 + 0xFFFFFF80) 12 = accV M2 (sp0 + 0xFFFFFF80) 12 := accV_congr 12 fun j hj => by
      have e0 : sp0 + 0xFFFFFF80 + BitVec.ofNat 32 (4 * j) = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 (0 + 4 * j) := by
        rw [Nat.zero_add]
      rw [mem6, load_frame2 fr5 (sFw 0x60 4 (4 * j) (by decide) (by omega) (.inr (by omega))) (sGw (4 * j) (by omega)),
        load_frame2 fr4 (sGw (4 * j) (by omega)) (sFw 0x30 48 (4 * j) (by decide) (by omega) (.inr (by omega))),
        ← hM3, fillWords_load_sep (sFw 0x30 (4 * 12) (4 * j) (by decide) (by omega) (.inr (by omega)))]
    have agD : accV m6.mem (sp0 + 0xFFFFFF80 + 0x30) 12 = accV M4 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30) 12 :=
      accV_congr2 12 fun j hj => by
        have e : sp0 + 0xFFFFFF80 + 0x30 + BitVec.ofNat 32 (4 * j) =
            sp0 + 0xFFFFFF80 + BitVec.ofNat 32 (0x30 + 4 * j) := add_ofNat_assoc _ 0x30 (4 * j)
        rw [e, mem6, load_frame2 fr5 (sFw 0x60 4 (0x30 + 4 * j) (by decide) (by omega) (.inr (by omega)))
          (sGw (0x30 + 4 * j) (by omega)), add_ofNat_assoc]
    have hS3 : accV M3 (sp0 + 0xFFFFFF80) 12 = accV M2 (sp0 + 0xFFFFFF80) 12 := accV_congr 12 fun j hj => by
      rw [← hM3, fillWords_load_sep (sFw 0x30 (4 * 12) (4 * j) (by decide) (by omega) (.inr (by omega)))]
    have hP3 : accV M3 p3M 12 = p384 := p3M_val (cOf env.pmod env.sSP frM3)
    have hA : accV M1 (sp0 + 0xFFFFFF80) 12 = accV m.mem sf 12 := accV_congr2 12 fun j hj => hcp j hj
    rw [eOut, accV_sel w7, p3_choice _ _ hc2 hb4, agS, agD, limbVal_wordsAt]
    have hif : ∀ (Q : Prop) [Decidable Q] (X Y : Nat), (if (if Q then (1 : Word) else 0) = 1 then X else Y) =
        if Q then X else Y := fun Q _ X Y => by by_cases hq : Q <;> simp [hq]
    rw [hif]
    have e384 : (2 : Nat) ^ (32 * 12) = 2 ^ 384 := rfl
    refine p3_final (accV_lt _ _ 12) hc2 (mb_le1 _) ?_ ?_
    · rw [← hA, ← e384, hv2]; omega
    · rw [← hS3, ← hP3, ← e384]; exact hv4
  · intro x hx ho
    rw [mem8, I7 x hx ho]

end C3.RV32
