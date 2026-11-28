import C3BootProofs.Proofs.Leaves

/-!
# `FieldElement2625::from_bytes`'s `load3` and `load4`, as compiled

Each returns, as a `u64` in `a0` and `a1`, the little-endian number in three
or four bytes at an offset into a byte slice.
-/

namespace C3.RV32

open C3.Image

/-- `load3_at`'s instructions before its return. -/
def fl3Body : List BInstr :=
  [.alu .add a0 a0 a1, .lbu a1 a0 0x1, .lbu a2 a0 0x0, .lbu a0 a0 0x2, .aluImm .sll a1 a1 0x8,
   .alu .or a1 a1 a2, .aluImm .sll a0 a0 0x10, .alu .or a0 a0 a1, .aluImm .add a1 x0 0x0]

/-- `load4_at`'s instructions before its return. -/
def fl4Body : List BInstr :=
  [.alu .add a0 a0 a1, .lbu a1 a0 0x1, .lbu a2 a0 0x2, .lbu a3 a0 0x3, .lbu a0 a0 0x0,
   .aluImm .sll a1 a1 0x8, .aluImm .sll a2 a2 0x10, .aluImm .sll a3 a3 0x18, .alu .or a0 a0 a1,
   .alu .or a2 a2 a3, .alu .or a0 a0 a2, .aluImm .add a1 x0 0x0]

section
set_option maxRecDepth 20000
theorem fl3_at_18 : fetchRel feLoad3Code 0x18 = some (.jalr x0 ra 0x0, 2) := by decide
theorem fl4_at_20 : fetchRel feLoad4Code 0x20 = some (.jalr x0 ra 0x0, 2) := by decide
theorem fl3Body_end : blockEnd feLoad3Code 0 fl3Body = some 0x18 := by decide
theorem fl4Body_end : blockEnd feLoad4Code 0 fl4Body = some 0x20 := by decide
end

theorem zext_tn (b : BitVec 8) : ((b.zeroExtend 32 : Word)).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem sll_byte (b : BitVec 8) {s : Word} (hk : s.toNat ≤ 24) :
    (aluEval .sll (b.zeroExtend 32) s).toNat = b.toNat * 2 ^ s.toNat := by
  have hb := b.isLt
  rw [sll_nat _ _ (by omega), zext_tn]
  apply Nat.mod_eq_of_lt
  calc b.toNat * 2 ^ s.toNat < 2 ^ 8 * 2 ^ s.toNat := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
    _ = 2 ^ (8 + s.toNat) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)

set_option maxRecDepth 20000 in
/-- **`FieldElement2625::from_bytes::load3_at`** returns the little-endian
number in the three bytes at `q + i`. -/
theorem feLoad3_correct (m : Machine) {base retAddr q i : Word} (hc : CodeIn m.mem base feLoad3Code)
    (hpc : m.pc = base) (ha0 : reg m a0 = q) (ha1 : reg m a1 = i) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (reg m' a0).toNat = (m.mem (q + i)).toNat + 2 ^ 8 * (m.mem (q + i + 1)).toNat +
        2 ^ 16 * (m.mem (q + i + 2)).toNat ∧ reg m' a1 = 0 ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, c1, u1⟩ := St.block fl3Body s0 hc fl3Body_end (by simp [BlockOk, BInstr.ok, fl3Body])
  simp only [runBlock, BInstr.run, fl3Body] at u1
  simp +decide only [upd_app, ↓reduceIte] at u1
  obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.self.jalr hc fl3_at_18
  rw [ha0, ha1, show aluEval .add q i = q + i from rfl, add_lit_zero] at u1
  have b0 := (m.mem (q + i)).isLt
  refine ⟨n2, c1.trans (.single d2), ?_, ?_, ?_, fun r h0 h1 h2 => ?_, mem2⟩
  · rw [pc2, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hra, add_lit_zero, hret]
  · rw [regs2, u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    have v1 : (aluEval .sll ((m.mem (q + i + 1)).zeroExtend 32) 8).toNat = (m.mem (q + i + 1)).toNat * 2 ^ 8 := by
      rw [sll_byte _ (by decide)]; rfl
    have v2 : (aluEval .sll ((m.mem (q + i + 2)).zeroExtend 32) 0x10).toNat =
        (m.mem (q + i + 2)).toNat * 2 ^ 16 := by rw [sll_byte _ (by decide)]; rfl
    have w0 : ((m.mem (q + i)).zeroExtend 32 : Word).toNat < 2 ^ 8 := by rw [zext_tn]; exact b0
    have i1 : (aluEval .or (aluEval .sll ((m.mem (q + i + 1)).zeroExtend 32) 8) ((m.mem (q + i)).zeroExtend 32)).toNat =
        (m.mem (q + i + 1)).toNat * 2 ^ 8 + (m.mem (q + i)).toNat := by
      rw [or_nat _ _ (i := 8) (by rw [v1]; exact Nat.mul_mod_left _ _) w0, v1, zext_tn]
    rw [or_nat _ _ (i := 16) (by rw [v2]; exact Nat.mul_mod_left _ _) (by rw [i1]; omega), v2, i1]
    omega
  · rw [regs2, u1.regs]; simp +decide only [upd_app, ↓reduceIte]
  · rw [regs2, u1.regs]
    by_cases hv : r.val = 0
    · have : r = 0 := Fin.ext hv
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, hv, h0, h1, h2, ite_false]

set_option maxRecDepth 20000 in
/-- **`FieldElement2625::from_bytes::load4_at`** returns the little-endian
number in the four bytes at `q + i`. -/
theorem feLoad4_correct (m : Machine) {base retAddr q i : Word} (hc : CodeIn m.mem base feLoad4Code)
    (hpc : m.pc = base) (ha0 : reg m a0 = q) (ha1 : reg m a1 = i) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (reg m' a0).toNat = (m.mem (q + i)).toNat + 2 ^ 8 * (m.mem (q + i + 1)).toNat +
        2 ^ 16 * (m.mem (q + i + 2)).toNat + 2 ^ 24 * (m.mem (q + i + 3)).toNat ∧ reg m' a1 = 0 ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, c1, u1⟩ := St.block fl4Body s0 hc fl4Body_end (by simp [BlockOk, BInstr.ok, fl4Body])
  simp only [runBlock, BInstr.run, fl4Body] at u1
  simp +decide only [upd_app, ↓reduceIte] at u1
  obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.self.jalr hc fl4_at_20
  rw [ha0, ha1, show aluEval .add q i = q + i from rfl, add_lit_zero] at u1
  have b0 := (m.mem (q + i)).isLt
  have b2 := (m.mem (q + i + 2)).isLt
  refine ⟨n2, c1.trans (.single d2), ?_, ?_, ?_, fun r h0 h1 h2 h3 => ?_, mem2⟩
  · rw [pc2, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hra, add_lit_zero, hret]
  · rw [regs2, u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    have v1 : (aluEval .sll ((m.mem (q + i + 1)).zeroExtend 32) 8).toNat = (m.mem (q + i + 1)).toNat * 2 ^ 8 := by
      rw [sll_byte _ (by decide)]; rfl
    have v2 : (aluEval .sll ((m.mem (q + i + 2)).zeroExtend 32) 0x10).toNat =
        (m.mem (q + i + 2)).toNat * 2 ^ 16 := by rw [sll_byte _ (by decide)]; rfl
    have v3 : (aluEval .sll ((m.mem (q + i + 3)).zeroExtend 32) 0x18).toNat =
        (m.mem (q + i + 3)).toNat * 2 ^ 24 := by rw [sll_byte _ (by decide)]; rfl
    have i1 : (aluEval .or ((m.mem (q + i)).zeroExtend 32) (aluEval .sll ((m.mem (q + i + 1)).zeroExtend 32) 8)).toNat =
        (m.mem (q + i)).toNat + (m.mem (q + i + 1)).toNat * 2 ^ 8 := by
      rw [or_nat' _ _ (i := 8) (by rw [zext_tn]; exact b0) (by rw [v1]; exact Nat.mul_mod_left _ _), v1, zext_tn]
    have i2 : (aluEval .or (aluEval .sll ((m.mem (q + i + 2)).zeroExtend 32) 0x10)
        (aluEval .sll ((m.mem (q + i + 3)).zeroExtend 32) 0x18)).toNat =
        (m.mem (q + i + 2)).toNat * 2 ^ 16 + (m.mem (q + i + 3)).toNat * 2 ^ 24 := by
      rw [or_nat' _ _ (i := 24) (by rw [v2]; omega) (by rw [v3]; exact Nat.mul_mod_left _ _), v2, v3]
    rw [or_nat' _ _ (i := 16) (by rw [i1]; have := (m.mem (q + i + 1)).isLt; omega) (by rw [i2]; omega), i1, i2]
    omega
  · rw [regs2, u1.regs]; simp +decide only [upd_app, ↓reduceIte]
  · rw [regs2, u1.regs]
    by_cases hv : r.val = 0
    · have : r = 0 := Fin.ext hv
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, hv, h0, h1, h2, h3, ite_false]

end C3.RV32
