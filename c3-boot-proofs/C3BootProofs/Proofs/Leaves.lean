import C3BootProofs.Proofs.ShrWide12

/-!
# Small leaf functions, as compiled

`subtle::black_box::<u8>`, `<u8 as subtle::ConstantTimeEq>::ct_eq`, the
32-byte `<[u8] as subtle::ConstantTimeEq>::ct_eq`, `memcmp`,
`UintRef::is_nonzero`, and `__lshrdi3`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem bb_at_0 : fetchRel blackBoxU8Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem bb_at_2 : fetchRel blackBoxU8Code 0x2 = some (.store .sb sp a0 0xF, 4) := by decide
theorem bb_at_6 : fetchRel blackBoxU8Code 0x6 = some (.load .lbu a0 sp 0xF, 4) := by decide
theorem bb_at_a : fetchRel blackBoxU8Code 0xA = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem bb_at_c : fetchRel blackBoxU8Code 0xC = some (.jalr x0 ra 0x0, 2) := by decide
theorem ce_at_0 : fetchRel ctEqU8Code 0x0 = some (.alu .xor a0 a0 a1, 2) := by decide
theorem ce_at_2 : fetchRel ctEqU8Code 0x2 = some (.alu .sub a1 x0 a0, 4) := by decide
theorem ce_at_6 : fetchRel ctEqU8Code 0x6 = some (.alu .or a0 a0 a1, 2) := by decide
theorem ce_at_8 : fetchRel ctEqU8Code 0x8 = some (.aluImm .sll a0 a0 0x18, 2) := by decide
theorem ce_at_a : fetchRel ctEqU8Code 0xA = some (.aluImm .srl a0 a0 0x1F, 2) := by decide
theorem ce_at_c : fetchRel ctEqU8Code 0xC = some (.aluImm .xor a0 a0 0x1, 4) := by decide
theorem ce_at_10 : fetchRel ctEqU8Code 0x10 = some (.auipc (6 : Fin 32) 0xFFFFF000, 4) := by decide
theorem ce_at_14 : fetchRel ctEqU8Code 0x14 = some (.jalr x0 (6 : Fin 32) 0xFFFFF83E, 4) := by decide
theorem cs_at_0 : fetchRel ctEqSliceCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem cs_at_2 : fetchRel ctEqSliceCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem cs_at_4 : fetchRel ctEqSliceCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem cs_at_6 : fetchRel ctEqSliceCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem cs_at_8 : fetchRel ctEqSliceCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem cs_at_a : fetchRel ctEqSliceCode 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem cs_at_c : fetchRel ctEqSliceCode 0xC = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem cs_at_e : fetchRel ctEqSliceCode 0xE = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem cs_at_10 : fetchRel ctEqSliceCode 0x10 = some (.aluImm .add (18 : Fin 32) x0 0x1, 2) := by decide
theorem cs_at_12 : fetchRel ctEqSliceCode 0x12 = some (.aluImm .add (8 : Fin 32) x0 0x20, 4) := by decide
theorem cs_at_16 : fetchRel ctEqSliceCode 0x16 = some (.branch .beq (8 : Fin 32) x0 0x1E, 2) := by decide
theorem cs_at_18 : fetchRel ctEqSliceCode 0x18 = some (.load .lbu a1 (19 : Fin 32) 0x0, 4) := by decide
theorem cs_at_1c : fetchRel ctEqSliceCode 0x1C = some (.load .lbu a0 (9 : Fin 32) 0x0, 4) := by decide
theorem cs_at_20 : fetchRel ctEqSliceCode 0x20 = some (.auipc ra 0x0, 4) := by decide
theorem cs_at_24 : fetchRel ctEqSliceCode 0x24 = some (.jalr ra ra 0xFFFFFFC8, 4) := by decide
theorem cs_at_28 : fetchRel ctEqSliceCode 0x28 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem cs_at_2a : fetchRel ctEqSliceCode 0x2A = some (.alu .and (18 : Fin 32) a0 (18 : Fin 32), 4) := by decide
theorem cs_at_2e : fetchRel ctEqSliceCode 0x2E = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x1, 2) := by decide
theorem cs_at_30 : fetchRel ctEqSliceCode 0x30 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem cs_at_32 : fetchRel ctEqSliceCode 0x32 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE6, 2) := by decide
theorem cs_at_34 : fetchRel ctEqSliceCode 0x34 = some (.aluImm .and a0 (18 : Fin 32) 0xFF, 4) := by decide
theorem cs_at_38 : fetchRel ctEqSliceCode 0x38 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem cs_at_3a : fetchRel ctEqSliceCode 0x3A = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem cs_at_3c : fetchRel ctEqSliceCode 0x3C = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem cs_at_3e : fetchRel ctEqSliceCode 0x3E = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem cs_at_40 : fetchRel ctEqSliceCode 0x40 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem cs_at_42 : fetchRel ctEqSliceCode 0x42 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem cs_at_44 : fetchRel ctEqSliceCode 0x44 = some (.auipc (6 : Fin 32) 0xFFFFE000, 4) := by decide
theorem cs_at_48 : fetchRel ctEqSliceCode 0x48 = some (.jalr x0 (6 : Fin 32) 0x7F2, 4) := by decide
theorem mcx_at_0 : fetchRel memcmpCode 0x0 = some (.branch .beq a2 x0 0x16, 2) := by decide
theorem mcx_at_2 : fetchRel memcmpCode 0x2 = some (.load .lbu a3 a0 0x0, 4) := by decide
theorem mcx_at_6 : fetchRel memcmpCode 0x6 = some (.load .lbu a4 a1 0x0, 4) := by decide
theorem mcx_at_a : fetchRel memcmpCode 0xA = some (.branch .bne a3 a4 0x10, 4) := by decide
theorem mcx_at_e : fetchRel memcmpCode 0xE = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem mcx_at_10 : fetchRel memcmpCode 0x10 = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem mcx_at_12 : fetchRel memcmpCode 0x12 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem mcx_at_14 : fetchRel memcmpCode 0x14 = some (.branch .bne a2 x0 0xFFFFFFEE, 2) := by decide
theorem mcx_at_16 : fetchRel memcmpCode 0x16 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem mcx_at_18 : fetchRel memcmpCode 0x18 = some (.jalr x0 ra 0x0, 2) := by decide
theorem mcx_at_1a : fetchRel memcmpCode 0x1A = some (.alu .sub a0 a3 a4, 4) := by decide
theorem mcx_at_1e : fetchRel memcmpCode 0x1E = some (.jalr x0 ra 0x0, 2) := by decide
theorem nz_at_0 : fetchRel uintRefIsNonzeroCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem nz_at_2 : fetchRel uintRefIsNonzeroCode 0x2 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem nz_at_4 : fetchRel uintRefIsNonzeroCode 0x4 = some (.branch .beq a1 x0 0xC, 2) := by decide
theorem nz_at_6 : fetchRel uintRefIsNonzeroCode 0x6 = some (.load .lw a3 a0 0x0, 2) := by decide
theorem nz_at_8 : fetchRel uintRefIsNonzeroCode 0x8 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem nz_at_a : fetchRel uintRefIsNonzeroCode 0xA = some (.alu .or a2 a2 a3, 2) := by decide
theorem nz_at_c : fetchRel uintRefIsNonzeroCode 0xC = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem nz_at_e : fetchRel uintRefIsNonzeroCode 0xE = some (.branch .bne a1 x0 0xFFFFFFF8, 2) := by decide
theorem nz_at_10 : fetchRel uintRefIsNonzeroCode 0x10 = some (.store .sw sp a2 0xC, 2) := by decide
theorem nz_at_12 : fetchRel uintRefIsNonzeroCode 0x12 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem nz_at_14 : fetchRel uintRefIsNonzeroCode 0x14 = some (.load .lw a0 sp 0xC, 2) := by decide
theorem nz_at_16 : fetchRel uintRefIsNonzeroCode 0x16 = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem nz_at_1a : fetchRel uintRefIsNonzeroCode 0x1A = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem nz_at_1c : fetchRel uintRefIsNonzeroCode 0x1C = some (.jalr x0 ra 0x0, 2) := by decide
theorem ls_at_0 : fetchRel lshrdi3Code 0x0 = some (.aluImm .and a3 a2 0x20, 4) := by decide
theorem ls_at_4 : fetchRel lshrdi3Code 0x4 = some (.branch .bne a3 x0 0x18, 2) := by decide
theorem ls_at_6 : fetchRel lshrdi3Code 0x6 = some (.branch .beq a2 x0 0x14, 2) := by decide
theorem ls_at_8 : fetchRel lshrdi3Code 0x8 = some (.alu .sub a3 x0 a2, 4) := by decide
theorem ls_at_c : fetchRel lshrdi3Code 0xC = some (.alu .srl a0 a0 a2, 4) := by decide
theorem ls_at_10 : fetchRel lshrdi3Code 0x10 = some (.alu .sll a3 a1 a3, 4) := by decide
theorem ls_at_14 : fetchRel lshrdi3Code 0x14 = some (.alu .or a0 a0 a3, 2) := by decide
theorem ls_at_16 : fetchRel lshrdi3Code 0x16 = some (.alu .srl a1 a1 a2, 4) := by decide
theorem ls_at_1a : fetchRel lshrdi3Code 0x1A = some (.jalr x0 ra 0x0, 2) := by decide
theorem ls_at_1c : fetchRel lshrdi3Code 0x1C = some (.alu .srl a0 a1 a2, 4) := by decide
theorem ls_at_20 : fetchRel lshrdi3Code 0x20 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ls_at_22 : fetchRel lshrdi3Code 0x22 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The instructions `black_box::<u8>` runs before it returns. -/
def bbBody : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .sb sp a0 0xF, .lbu a0 sp 0xF, .aluImm .add sp sp 0x10]

section
set_option maxRecDepth 20000
theorem bbBody_end : blockEnd blackBoxU8Code 0 bbBody = some 0xC := by decide
end

set_option maxRecDepth 20000 in
/-- **`subtle::black_box::<u8>`** returns the low byte of its argument. It
writes the byte below `sp`. -/
theorem blackBoxU8_correct (m : Machine) {base retAddr : Word} (hc : CodeIn m.mem base blackBoxU8Code)
    (hpc : m.pc = base) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsep : Sep (reg m sp + 0xFFFFFFFF) 1 base blackBoxU8Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = ((reg m a0).extractLsb' 0 8).zeroExtend 32 ∧
      (∀ q, q ≠ a0 → reg m' q = reg m q) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFF) 1 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have e : reg m sp + 0xFFFFFFF0 + 0xF = reg m sp + 0xFFFFFFFF := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m1, c1, u1⟩ := St.block bbBody s0 hc bbBody_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, bbBody, upd_app, ↓reduceIte, and_true, true_and, aluEval]
    rw [e]; exact hsep)
  simp only [runBlock, BInstr.run, bbBody] at u1
  have hc1 : CodeIn (memStore8 m.mem (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) sp + 0xF)
      ((upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) a0).extractLsb' 0 8)) base blackBoxU8Code :=
    hc.store8 (by simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, e]; exact hsep)
  obtain ⟨m2, d2, pc2, mem2, regs2⟩ := u1.self.jalr hc1 bb_at_c
  refine ⟨m2, c1.trans (.single d2), ?_, ?_, fun q hq => ?_, fun x hx => ?_⟩
  · rw [pc2, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hra, hret]
  · rw [regs2, u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    simp only [memStore8, ite_true]
  · rw [regs2, u1.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s0.zero.symm
    by_cases hs : q = sp
    · subst hs; simp +decide only [upd_app, ↓reduceIte]
      rw [ev_add, ev_add, BitVec.add_assoc, show (4294967280 : Word) + 16 = 0 by decide, add_lit_zero]
    simp only [upd_app, h0, hs, hq, ite_false]
  · rw [mem2]
    simp +decide only [upd_app, ↓reduceIte, ev_add]
    rw [e]; exact memStore8_ne fun ex => hx.point (i := 0) (j := 0) (by decide) (by decide) (by
      rw [add_ofNat_zero, add_ofNat_zero]; exact ex.symm)


theorem srl_mod (x r : Word) : (aluEval .srl x r).toNat = x.toNat / 2 ^ (r.toNat % 32) := by
  show (x >>> (r.toNat % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A 64-bit value shifted right by `s` from 0 to 32 bits, word by word. -/
theorem lsr64 {lo hi s : Nat} (hs : s ≤ 32) :
    (lo + 2 ^ 32 * hi) / 2 ^ s = lo / 2 ^ s + hi % 2 ^ s * 2 ^ (32 - s) + 2 ^ 32 * (hi / 2 ^ s) := by
  have e := Nat.div_add_mod hi (2 ^ s)
  have e32 : (2 : Nat) ^ 32 = 2 ^ s * 2 ^ (32 - s) := by rw [← Nat.pow_add]; congr 1; omega
  have : lo + 2 ^ 32 * hi = lo + 2 ^ s * (2 ^ 32 * (hi / 2 ^ s) + hi % 2 ^ s * 2 ^ (32 - s)) := by
    conv => lhs; rw [← e]
    rw [e32]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [this, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s)]
  omega

/-- The instructions from 0x8 to 0x1A: the shift by 1 to 31 bits. -/
def lsBody : List BInstr :=
  [.alu .sub a3 x0 a2, .alu .srl a0 a0 a2, .alu .sll a3 a1 a3, .alu .or a0 a0 a3, .alu .srl a1 a1 a2]

section
set_option maxRecDepth 20000
theorem lsBody_end : blockEnd lshrdi3Code 0x8 lsBody = some 0x1A := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`__lshrdi3`** shifts the 64-bit value in `a0` (low word) and `a1` (high
word) right by `s` bits, for `s` from 0 to 63. -/
theorem lshrdi3_correct (m : Machine) {base retAddr lo hi : Word} {s : Nat} (hc : CodeIn m.mem base lshrdi3Code)
    (hpc : m.pc = base) (ha0 : reg m a0 = lo) (ha1 : reg m a1 = hi) (ha2 : reg m a2 = BitVec.ofNat 32 s)
    (hs : s < 64) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (reg m' a0).toNat + 2 ^ 32 * (reg m' a1).toNat = (lo.toNat + 2 ^ 32 * hi.toNat) / 2 ^ s ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → reg m' q = reg m q) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hsn : (BitVec.ofNat 32 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  have hlo := lo.isLt
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc ls_at_0 (off' := 4) (by decide)
  have e3 : upd (reg m) a3 (aluEval .and (reg m a2) 0x20) a3 = if 32 ≤ s then 0x20 else 0 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ha2]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 s &&& 0x20).toNat = _
    rw [BitVec.toNat_and, hsn]
    have : ∀ t, t < 64 → t &&& 32 = if 32 ≤ t then 32 else 0 := by decide
    rw [show (0x20 : Word).toNat = 32 from rfl, this s hs]; split <;> rfl
  have k1 : ∀ q, q ≠ a3 → upd (reg m) a3 (aluEval .and (reg m a2) 0x20) q = reg m q := fun q hq => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    exact upd_ne h0 hq
  have r1 : ∀ q, q ≠ a3 → reg n1 q = reg m q := fun q hq => by rw [u1.regs, k1 q hq]
  have e0 : reg n1 a0 = lo := (r1 a0 (by decide)).trans ha0
  have e1 : reg n1 a1 = hi := (r1 a1 (by decide)).trans ha1
  have e2 : reg n1 a2 = BitVec.ofNat 32 s := (r1 a2 (by decide)).trans ha2
  have era : reg n1 ra = retAddr := (r1 ra (by decide)).trans hra
  by_cases h32 : 32 ≤ s
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x1C ls_at_4 (by decide) (by
      rw [u1.regs, e3, if_pos h32, show reg n1 x0 = 0 from u1.self.zero]; decide)
    obtain ⟨n3, d3, u3⟩ := u2.alu hc ls_at_1c (off' := 0x20) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hc ls_at_20 (off' := 0x22) (by decide)
    obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.jalr hc ls_at_22
    refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), ?_, ?_, fun q h0' h1' h3' => ?_, ?_⟩
    · rw [pc5]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.regs, k1 ra (by decide), add_lit_zero, hra, hret]
    · rw [regs5, regs5]; simp +decide only [upd_app, ↓reduceIte]
      simp only [e0, e1, e2, ha0, ha1, ha2]
      rw [srl_mod, hsn, show (aluEval .add 0 0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
      conv => rhs; rw [show s = 32 + (s - 32) by omega]
      rw [div_hi hlo, show s % 32 = s - 32 by omega]
    · rw [regs5]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h0', h1', ite_false]; rw [u1.regs, k1 q h3']
    · exact mem5
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x6 ls_at_4 (by decide) (by
      rw [u1.regs, e3, if_neg h32, show reg n1 x0 = 0 from u1.self.zero]; decide)
    by_cases hs0 : s = 0
    · subst hs0
      obtain ⟨n3, d3, u3⟩ := u2.taken hc 0x1A ls_at_6 (by decide) (by
        rw [u1.regs, k1 a2 (by decide), ha2, show reg n1 x0 = 0 from u1.self.zero]; decide)
      obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc ls_at_1a
      refine ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), ?_, ?_, fun q h0' h1' h3' => ?_, ?_⟩
      · rw [pc4, u1.regs, k1 ra (by decide), add_lit_zero, hra, hret]
      · rw [regs4, regs4]; simp only [e0, e1, ha0, ha1]; rw [Nat.pow_zero, Nat.div_one]
      · rw [regs4]; exact r1 q h3'
      · exact mem4
    · obtain ⟨n3, d3, u3⟩ := u2.notTaken hc 0x8 ls_at_6 (by decide) (by
        rw [u1.regs, k1 a2 (by decide), ha2, show reg n1 x0 = 0 from u1.self.zero]
        simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h; rw [hsn] at this; exact hs0 this)
      obtain ⟨n4, c4, u4⟩ := St.block lsBody u3 hc lsBody_end (by simp [BlockOk, BInstr.ok, lsBody])
      simp only [runBlock, BInstr.run, lsBody] at u4
      obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.self.jalr hc ls_at_1a
      have r := r1
      refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (c4.trans (.single d5)))), ?_, ?_, fun q h0' h1' h3' => ?_, ?_⟩
      · rw [pc5, u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r ra (by decide), add_lit_zero, hra, hret]
      · rw [regs5, regs5, u4.regs, u4.regs]; simp +decide only [upd_app, ↓reduceIte]
        simp only [e0, e1, e2, show reg n1 x0 = 0 from u1.self.zero]
        have hneg : (aluEval .sub 0 (BitVec.ofNat 32 s)) = BitVec.ofNat 32 (32 - s) + 0xFFFFFFE0 := by
          apply BitVec.eq_of_toNat_eq
          show (0 - BitVec.ofNat 32 s).toNat = (BitVec.ofNat 32 (32 - s) + 0xFFFFFFE0).toNat
          rw [BitVec.toNat_sub, BitVec.toNat_add, hsn, ofNat_tn (by omega)]
          show (2 ^ 32 - s + 0) % 2 ^ 32 = (32 - s + 4294967264) % 2 ^ 32; omega
        have hsll : (aluEval .sll hi (aluEval .sub 0 (BitVec.ofNat 32 s))).toNat =
            hi.toNat % 2 ^ s * 2 ^ (32 - s) := by
          rw [← sll_carry hi (by omega) (by omega)]
          have h32 : (aluEval .sub 0 (BitVec.ofNat 32 s)).toNat % 32 = (BitVec.ofNat 32 (32 - s)).toNat % 32 := by
            rw [hneg, BitVec.toNat_add, ofNat_tn (by omega), show (0xFFFFFFE0 : Word).toNat = 4294967264 from rfl]
            omega
          show (hi <<< ((aluEval .sub 0 (BitVec.ofNat 32 s)).toNat % 32)).toNat =
            (hi <<< ((BitVec.ofNat 32 (32 - s)).toNat % 32)).toNat
          rw [h32]
        have hlow : (aluEval .srl lo (BitVec.ofNat 32 s)).toNat < 2 ^ (32 - s) := by
          rw [srl_mod, hsn, Nat.mod_eq_of_lt (by omega)]
          exact shDivLt (by rw [← Nat.pow_add, show s + (32 - s) = 32 by omega]; exact hlo)
        have hhigh : (aluEval .sll hi (aluEval .sub 0 (BitVec.ofNat 32 s))).toNat % 2 ^ (32 - s) = 0 := by
          rw [hsll]; exact Nat.mul_mod_left _ _
        rw [or_nat' _ _ hlow hhigh, srl_mod, srl_mod, hsn, Nat.mod_eq_of_lt (by omega), hsll, lsr64 (by omega)]
        all_goals omega
      · rw [regs5, u4.regs]
        by_cases h0 : q.val = 0
        · have : q = 0 := Fin.ext h0
          subst this; simp [upd]; exact hz.symm
        simp only [upd_app, h0, h0', h1', h3', ite_false]; exact r q h3'
      · rw [mem5]


/-- One byte of `memcmp`, from 0x2: compare byte `i` and either return the
difference or step to byte `i + 1`. -/
def mcStep : List BInstr := [.aluImm .add a2 a2 0xFFFFFFFF, .aluImm .add a1 a1 0x1, .aluImm .add a0 a0 0x1]

section
set_option maxRecDepth 20000
theorem mcStep_end : blockEnd memcmpCode 0xE mcStep = some 0x14 := by decide
end

theorem mc_cnt {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 (n - i) + 0xFFFFFFFF = BitVec.ofNat 32 (n - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, ofNat_tn (by omega), ofNat_tn (by omega)]
  show (n - i + 4294967295) % 2 ^ 32 = n - (i + 1); omega

theorem zext_ne {x y : BitVec 8} (h : x ≠ y) : aluEval .sub (x.zeroExtend 32) (y.zeroExtend 32) ≠ 0 := by
  intro e
  apply h
  have e2 : x.zeroExtend 32 = y.zeroExtend 32 := by
    have := congrArg (· + y.zeroExtend 32) e
    simp only [aluEval, BitVec.sub_add_cancel] at this; rw [zw] at this; exact this
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat e2
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := x.isLt; omega), Nat.mod_eq_of_lt (by have := y.isLt; omega)] at this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`memcmp`** returns 0 exactly when the `n` bytes at `p` equal the `n`
bytes at `q`. -/
theorem memcmp_correct (m : Machine) {base retAddr p q : Word} {n : Nat} (hc : CodeIn m.mem base memcmpCode)
    (hpc : m.pc = base) (ha0 : reg m a0 = p) (ha1 : reg m a1 = q) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hn : n < 2 ^ 32) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (reg m' a0 = 0 ↔ ∀ i, i < n → m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i)) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the loop, from byte `i` with `k` bytes left
  have loop : ∀ k i, i + k = n → 0 < k → ∀ {n1 : Machine}, St m.mem base n1 0x2 (reg n1) →
      reg n1 a0 = p + BitVec.ofNat 32 i → reg n1 a1 = q + BitVec.ofNat 32 i → reg n1 a2 = BitVec.ofNat 32 k →
      reg n1 ra = retAddr →
      (∀ j, j < i → m.mem (p + BitVec.ofNat 32 j) = m.mem (q + BitVec.ofNat 32 j)) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n1 r = reg m r) →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧
        (reg m' a0 = 0 ↔ ∀ i, i < n → m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i)) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
    intro k
    induction k with
    | zero => intro i _ hk; exact absurd hk (Nat.lt_irrefl 0)
    | succ k ih =>
      intro i hik _ n1 s1 r0 r1 r2 rra heq hkeep
      obtain ⟨n2, d2, u2⟩ := s1.lbu hc mcx_at_2 (off' := 6) (by decide)
      obtain ⟨n3, d3, u3⟩ := u2.lbu hc mcx_at_6 (off' := 0xA) (by decide)
      have e3 : upd (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32)) a4
          ((m.mem (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32) a1 + 0)).zeroExtend 32) a3 =
          (m.mem (p + BitVec.ofNat 32 i)).zeroExtend 32 := by
        simp +decide only [upd_app, ↓reduceIte]; rw [r0, add_lit_zero]
      have e4 : upd (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32)) a4
          ((m.mem (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32) a1 + 0)).zeroExtend 32) a4 =
          (m.mem (q + BitVec.ofNat 32 i)).zeroExtend 32 := by
        simp +decide only [upd_app, ↓reduceIte]; rw [r1, add_lit_zero]
      have k3 : ∀ r, r ≠ a3 → r ≠ a4 → upd (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32)) a4
          ((m.mem (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32) a1 + 0)).zeroExtend 32) r = reg n1 r :=
        fun r h3 h4 => by
          by_cases h0 : r.val = 0
          · have : r = 0 := Fin.ext h0
            subst this; simp [upd]; exact s1.zero.symm
          simp only [upd_app, h0, h3, h4, ite_false]
      have hi : i < n := by omega
      by_cases hd : m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i)
      · obtain ⟨n4, d4, u4⟩ := u3.notTaken hc 0xE mcx_at_a (by decide) (by
          rw [e3, e4, hd]; simp only [branchTaken, bne_self_eq_false])
        obtain ⟨n5, c5, u5⟩ := St.block mcStep u4 hc mcStep_end (by simp [BlockOk, BInstr.ok, mcStep])
        simp only [runBlock, BInstr.run, mcStep] at u5
        have g5 : ∀ r, reg n5 r = _ := u5.regs
        have r25 : reg n5 a2 = BitVec.ofNat 32 k := by
          rw [g5]; simp +decide only [upd_app, ↓reduceIte]
          rw [r2, ev_add, show k + 1 = (k + 1) - 0 by rfl, mc_cnt (by omega) (by omega),
            show k + 1 - (0 + 1) = k by omega]
        have keep5 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n5 r = reg m r :=
          fun r h0' h1' h2' h3' h4' => by
            rw [g5]
            by_cases h0 : r.val = 0
            · have : r = 0 := Fin.ext h0
              subst this; simp [upd]; exact hz.symm
            simp only [upd_app, h0, h0', h1', h2', h3', h4', ite_false]
            exact hkeep r h0' h1' h2' h3' h4'
        have heq' : ∀ j, j < i + 1 → m.mem (p + BitVec.ofNat 32 j) = m.mem (q + BitVec.ofNat 32 j) :=
          fun j hj => by
            rcases (by omega : j < i ∨ j = i) with h | h
            · exact heq j h
            · subst h; exact hd
        by_cases hk : k = 0
        · subst hk
          obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc 0x16 mcx_at_14 (by decide) (by
            rw [r25, u5.self.zero]; decide)
          obtain ⟨n7, d7, u7⟩ := u6.aluImm hc mcx_at_16 (off' := 0x18) (by decide)
          obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc mcx_at_18
          refine ⟨n8, .cons d2 (.cons d3 (.cons d4 (c5.trans (.cons d6 (.cons d7 (.single d8)))))), ?_, ?_,
            fun r h0' h1' h2' h3' h4' => ?_, mem8⟩
          · rw [pc8]; simp +decide only [upd_app, ↓reduceIte]
            rw [keep5 ra (by decide) (by decide) (by decide) (by decide) (by decide), add_lit_zero, hra, hret]
          · rw [regs8]; simp +decide only [upd_app, ↓reduceIte]
            rw [show reg n5 x0 = 0 from u5.self.zero]
            exact ⟨fun _ j hj => heq' j (by omega), fun _ => rfl⟩
          · rw [regs8]
            by_cases h0 : r.val = 0
            · have : r = 0 := Fin.ext h0
              subst this; simp [upd]; exact hz.symm
            simp only [upd_app, h0, h0', ite_false]; exact keep5 r h0' h1' h2' h3' h4'
        · obtain ⟨n6, d6, u6⟩ := u5.self.taken hc 0x2 mcx_at_14 (by decide) (by
            rw [r25, u5.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
            have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact hk this)
          obtain ⟨m', c', h1, h2, h3, h4⟩ := ih (i + 1) (by omega) (by omega) u6.self
            (by rw [u6.regs, g5]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, ev_add,
              show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc])
            (by rw [u6.regs, g5]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, ev_add,
              show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc])
            (by rw [u6.regs]; exact r25)
            (by rw [u6.regs, keep5 ra (by decide) (by decide) (by decide) (by decide) (by decide), hra])
            heq' (fun r h0' h1' h2' h3' h4' => by rw [u6.regs]; exact keep5 r h0' h1' h2' h3' h4')
          exact ⟨m', .cons d2 (.cons d3 (.cons d4 (c5.trans (.cons d6 c')))), h1, h2, h3, h4⟩
      · obtain ⟨n4, d4, u4⟩ := u3.taken hc 0x1A mcx_at_a (by decide) (by
          rw [e3, e4]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
          apply hd; apply BitVec.eq_of_toNat_eq
          have := congrArg BitVec.toNat h
          simp only [BitVec.toNat_setWidth] at this
          rwa [Nat.mod_eq_of_lt (by have := (m.mem (p + BitVec.ofNat 32 i)).isLt; omega),
            Nat.mod_eq_of_lt (by have := (m.mem (q + BitVec.ofNat 32 i)).isLt; omega)] at this)
        obtain ⟨n5, d5, u5⟩ := u4.alu hc mcx_at_1a (off' := 0x1E) (by decide)
        obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc mcx_at_1e
        refine ⟨n6, .cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6)))), ?_, ?_,
          fun r h0' h1' h2' h3' h4' => ?_, mem6⟩
        · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]
          rw [rra, add_lit_zero, hret]
        · rw [regs6]; simp +decide only [upd_app, ↓reduceIte]
          rw [r0, r1, add_lit_zero, add_lit_zero]
          exact ⟨fun h => absurd h (zext_ne hd), fun h => absurd (h i hi) hd⟩
        · rw [regs6]
          by_cases h0 : r.val = 0
          · have : r = 0 := Fin.ext h0
            subst this; simp [upd]; exact hz.symm
          simp only [upd_app, h0, h0', h3', h4', ite_false]; exact hkeep r h0' h1' h2' h3' h4'
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨n1, d1, u1⟩ := s0.taken hc 0x16 mcx_at_0 (by decide) (by rw [ha2, hz]; decide)
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc mcx_at_16 (off' := 0x18) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc mcx_at_18
    refine ⟨n3, .cons d1 (.cons d2 (.single d3)), ?_, ?_, fun r h0' _ _ _ _ => ?_, mem3⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hra, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]
      exact ⟨fun _ j hj => absurd hj (Nat.not_lt_zero j), fun _ => rfl⟩
    · rw [regs3]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h0', ite_false]
  · obtain ⟨n1, d1, u1⟩ := s0.notTaken hc 0x2 mcx_at_0 (by decide) (by
      rw [ha2, hz]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
      have := congrArg BitVec.toNat h; rw [ofNat_tn hn] at this; exact hn0 this)
    obtain ⟨m', c', h1, h2, h3, h4⟩ := loop n 0 (by omega) (by omega) u1.self
      (by rw [u1.regs, ha0, add_ofNat_zero]) (by rw [u1.regs, ha1, add_ofNat_zero]) (by rw [u1.regs, ha2])
      (by rw [u1.regs, hra]) (fun j hj => absurd hj (Nat.not_lt_zero j))
      (fun r _ _ _ _ _ => u1.regs r)
    exact ⟨m', .cons d1 c', h1, h2, h3, h4⟩


/-- One word of `is_nonzero`'s OR, from 0x6 to 0xE. -/
def nzBody : List BInstr :=
  [.lw a3 a0 0x0, .aluImm .add a0 a0 0x4, .alu .or a2 a2 a3, .aluImm .add a1 a1 0xFFFFFFFF]

/-- From 0x10 to 0x1C: the OR through the stack, as 0 or 1, and `sp` back. -/
def nzTail : List BInstr :=
  [.sw sp a2 0xC, .aluImm .add a0 sp 0xC, .lw a0 sp 0xC, .alu .sltu a0 x0 a0, .aluImm .add sp sp 0x10]

section
set_option maxRecDepth 20000
theorem nzBody_end : blockEnd uintRefIsNonzeroCode 0x6 nzBody = some 0xE := by decide
theorem nzTail_end : blockEnd uintRefIsNonzeroCode 0x10 nzTail = some 0x1C := by decide
theorem nzPre_end : blockEnd uintRefIsNonzeroCode 0x0 [.aluImm .add sp sp 0xFFFFFFF0, .aluImm .add a2 x0 0x0] =
    some 0x4 := by decide
end

theorem sltu0 (w : Word) : aluEval .sltu 0 w = if w = 0 then 0 else 1 := by
  by_cases h : w = 0
  · subst h; decide
  · rw [if_neg h]
    have : 0 < w.toNat := by
      rcases Nat.eq_zero_or_pos w.toNat with h' | h'
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h']; rfl)) h
      · exact h'
    show (if BitVec.ult 0 w then 1 else 0) = _
    rw [if_pos (by simp only [BitVec.ult, decide_eq_true_eq]; exact this)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`UintRef::is_nonzero`** returns 1 when one of the `len` words at
`ptr` is nonzero and 0 when all are zero. It writes the word below `sp`. -/
theorem uintRefIsNonzero_correct (m : Machine) {base retAddr ptr : Word} {len : Nat}
    (hc : CodeIn m.mem base uintRefIsNonzeroCode) (hpc : m.pc = base) (ha0 : reg m a0 = ptr)
    (ha1 : reg m a1 = BitVec.ofNat 32 len) (hlen : len < 2 ^ 32) (hptr : ptr.toNat % 4 = 0)
    (hsp : (reg m sp).toNat % 4 = 0) (hsep : Sep (reg m sp + 0xFFFFFFFC) 4 base uintRefIsNonzeroCode.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if ∀ i, i < len → memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have eF : reg m sp + 0xFFFFFFF0 + 0xC = reg m sp + 0xFFFFFFFC := by rw [BitVec.add_assoc]; rfl
  -- the tail, from 0x10 with the OR in `a2`
  have tail : ∀ {n1 : Machine} {acc : Word}, St m.mem base n1 0x10 (reg n1) → reg n1 a2 = acc →
      reg n1 sp = reg m sp + 0xFFFFFFF0 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ sp → reg n1 r = reg m r) →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧ reg m' a0 = (if acc = 0 then 0 else 1) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m' r = reg m r) ∧
        ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
    intro n1 acc s1 r2 rsp hk
    obtain ⟨n2, c2, u2⟩ := St.block nzTail s1 hc nzTail_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, nzTail, upd_app, ↓reduceIte, and_true, true_and]
      rw [rsp, eF]
      exact ⟨⟨aligned_add hsp (k := 0xFFFFFFFC) (by decide), hsep⟩, aligned_add hsp (k := 0xFFFFFFFC) (by decide)⟩)
    simp only [runBlock, BInstr.run, nzTail] at u2
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.self.jalr (hc.store32 (by rw [rsp, eF]; exact hsep)) nz_at_1c
    refine ⟨n3, c2.trans (.single d3), ?_, ?_, fun r h0' h1' h2' h3' => ?_, fun x hx => ?_⟩
    · rw [pc3, u2.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [hk ra (by decide) (by decide) (by decide) (by decide) (by decide), add_lit_zero, hra, hret]
    · rw [regs3, u2.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [rsp, eF, memLoad32_store32_same, r2, sltu0]
    · rw [regs3, u2.regs]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      by_cases hs : r = sp
      · subst hs; simp +decide only [upd_app, ↓reduceIte]
        rw [rsp, ev_add, BitVec.add_assoc, show (0xFFFFFFF0 : Word) + 0x10 = 0 by decide, add_lit_zero]
      simp only [upd_app, h0, hs, h0', ite_false]; exact hk r h0' h1' h2' h3' hs
    · rw [mem3, rsp, eF]
      exact memStore32_get_sep hx
  have or0 : ∀ x y : Word, aluEval .or x y = 0 ↔ x = 0 ∧ y = 0 := fun x y => BitVec.or_eq_zero_iff
  -- the loop, from word `i` with `k` words left
  have loop : ∀ k i, i + k = len → 0 < k → ∀ {n1 : Machine} {acc : Word}, St m.mem base n1 0x6 (reg n1) →
      reg n1 a0 = ptr + BitVec.ofNat 32 (4 * i) → reg n1 a1 = BitVec.ofNat 32 k → reg n1 a2 = acc →
      (acc = 0 ↔ ∀ j, j < i → memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * j)) = 0) →
      reg n1 sp = reg m sp + 0xFFFFFFF0 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ sp → reg n1 r = reg m r) →
      ∃ n' acc', Steps n1 n' ∧ St m.mem base n' 0x10 (reg n') ∧ reg n' a2 = acc' ∧
        (acc' = 0 ↔ ∀ j, j < len → memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * j)) = 0) ∧
        reg n' sp = reg m sp + 0xFFFFFFF0 ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ sp → reg n' r = reg m r) := by
    intro k
    induction k with
    | zero => intro i _ hk; exact absurd hk (Nat.lt_irrefl 0)
    | succ k ih =>
      intro i hik _ n1 acc s1 r0 r1 r2 hacc rsp hk
      obtain ⟨n2, c2, u2⟩ := St.block nzBody s1 hc nzBody_end (by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, nzBody, upd_app, ↓reduceIte, and_true, true_and]
        rw [r0, add_lit_zero]; exact aligned_add hptr (by omega))
      simp only [runBlock, BInstr.run, nzBody] at u2
      have g2 : ∀ r, reg n2 r = _ := u2.regs
      have w : reg n2 a2 = aluEval .or acc (memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i))) := by
        rw [g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, r2, add_lit_zero]
      have hacc' : aluEval .or acc (memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i))) = 0 ↔
          ∀ j, j < i + 1 → memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * j)) = 0 := by
        rw [or0, hacc]
        constructor
        · intro ⟨h1, h2⟩ j hj
          rcases (by omega : j < i ∨ j = i) with h | h
          · exact h1 j h
          · subst h; exact h2
        · intro h; exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
      have r21 : reg n2 a1 = BitVec.ofNat 32 k := by
        rw [g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, ev_add]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, ofNat_tn (by omega), ofNat_tn (by omega)]
        show (k + 1 + 4294967295) % 2 ^ 32 = k; omega
      have keep2 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ sp → reg n2 r = reg m r :=
        fun r h0' h1' h2' h3' hs => by
          rw [g2]
          by_cases h0 : r.val = 0
          · have : r = 0 := Fin.ext h0
            subst this; simp [upd]; exact hz.symm
          simp only [upd_app, h0, h0', h1', h2', h3', ite_false]; exact hk r h0' h1' h2' h3' hs
      have sp2 : reg n2 sp = reg m sp + 0xFFFFFFF0 := by
        rw [g2]; simp +decide only [upd_app, ↓reduceIte]; exact rsp
      by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x10 nz_at_e (by decide) (by rw [r21, u2.self.zero]; decide)
        exact ⟨n3, aluEval .or acc (memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i))), c2.trans (.single d3),
          u3.self, by rw [u3.regs, w], by rw [← show i + 1 = len by omega]; exact hacc', by rw [u3.regs, sp2],
          fun r h0' h1' h2' h3' hs => by rw [u3.regs]; exact keep2 r h0' h1' h2' h3' hs⟩
      · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x6 nz_at_e (by decide) (by
          rw [r21, u2.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
          have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact hk0 this)
        obtain ⟨n', acc', c', h1, h2, h3, h4, h5⟩ := ih (i + 1) (by omega) (by omega) u3.self
          (by rw [u3.regs, g2]; simp +decide only [upd_app, ↓reduceIte]
              rw [r0, ev_add, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2)
          (by rw [u3.regs, r21]) (by rw [u3.regs, w]) hacc' (by rw [u3.regs, sp2])
          (fun r h0' h1' h2' h3' hs => by rw [u3.regs]; exact keep2 r h0' h1' h2' h3' hs)
        exact ⟨n', acc', c2.trans (.cons d3 c'), h1, h2, h3, h4, h5⟩
  obtain ⟨n1, c1, u1⟩ := St.block _ s0 hc nzPre_end (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  have g1 : ∀ r, reg n1 r = _ := u1.regs
  have sp1 : reg n1 sp = reg m sp + 0xFFFFFFF0 := by rw [g1]; simp +decide only [upd_app, ↓reduceIte, ev_add]
  have a21 : reg n1 a2 = 0 := by
    rw [g1]; simp +decide only [upd_app, ↓reduceIte]
    first | done | (rw [hz]; rfl) | rfl
  have keep1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ sp → reg n1 r = reg m r :=
    fun r h0' h1' h2' h3' hs => by
      rw [g1]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h2', hs, ite_false]
  by_cases hl0 : len = 0
  · subst hl0
    obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x10 nz_at_4 (by decide) (by
      rw [g1]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1, show reg n1 x0 = 0 from u1.self.zero]; decide)
    obtain ⟨m', c', h1, h2, h3, h4⟩ := tail u2.self (by rw [u2.regs, a21]) (by rw [u2.regs, sp1])
      (fun r h0' h1' h2' h3' hs => by rw [u2.regs]; exact keep1 r h0' h1' h2' h3' hs)
    refine ⟨m', c1.trans (.cons d2 c'), h1, ?_, h3, h4⟩
    rw [h2, if_pos rfl, if_pos (fun i hi => absurd hi (Nat.not_lt_zero i))]
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x6 nz_at_4 (by decide) (by
      rw [g1]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1, show reg n1 x0 = 0 from u1.self.zero]
      simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
      have := congrArg BitVec.toNat h; rw [ofNat_tn hlen] at this; exact hl0 this)
    obtain ⟨n3, acc, c3, s3, r3, hacc, sp3, k3⟩ := loop len 0 (by omega) (by omega) u2.self
      (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, add_ofNat_zero])
      (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1])
      (by rw [u2.regs, a21]) ⟨fun _ j hj => absurd hj (Nat.not_lt_zero j), fun _ => rfl⟩
      (by rw [u2.regs, sp1]) (fun r h0' h1' h2' h3' hs => by rw [u2.regs]; exact keep1 r h0' h1' h2' h3' hs)
    obtain ⟨m', c', h1, h2, h3, h4⟩ := tail s3 r3 sp3 k3
    refine ⟨m', c1.trans (.cons d2 (c3.trans c')), h1, ?_, h3, h4⟩
    rw [h2]
    by_cases h : acc = 0
    · rw [if_pos h, if_pos (hacc.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hacc.mpr h'))]


/-- The instructions `ct_eq` for bytes runs before its tail call. -/
def ceBody : List BInstr :=
  [.alu .xor a0 a0 a1, .alu .sub a1 x0 a0, .alu .or a0 a0 a1, .aluImm .sll a0 a0 0x18, .aluImm .srl a0 a0 0x1F,
   .aluImm .xor a0 a0 0x1]

section
set_option maxRecDepth 20000
theorem ceBody_end : blockEnd ctEqU8Code 0 ceBody = some 0x10 := by decide
end

theorem ceBits : ∀ x : Nat, x < 256 →
    aluEval .xor (aluEval .srl (aluEval .sll (aluEval .or (BitVec.ofNat 32 x) (aluEval .sub 0 (BitVec.ofNat 32 x)))
      24) 31) 1 = if x = 0 then 1 else 0 := by decide +kernel

theorem zext_low01 {w : Word} (h : w = 0 ∨ w = 1) : (w.extractLsb' 0 8).zeroExtend 32 = w := by
  rcases h with rfl | rfl <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`<u8 as subtle::ConstantTimeEq>::ct_eq`** returns 1 when its two
bytes are equal and 0 when they differ. It ends with a tail call to
`black_box::<u8>`, which writes the byte below `sp`. -/
theorem ctEqU8_correct (m : Machine) {base retAddr x y : Word} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base ctEqU8Code) (hbb : CodeIn m.mem (base + 0xFFFFE84E) blackBoxU8Code)
    (hpc : m.pc = base) (ha0 : reg m a0 = x) (ha1 : reg m a1 = y) (hx : x.toNat < 256) (hy : y.toNat < 256)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsep : Sep (reg m sp + 0xFFFFFFFF) 1 (base + 0xFFFFE84E) blackBoxU8Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = (if x = y then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ t1 → reg m' r = reg m r) ∧
      ∀ z, Sep (reg m sp + 0xFFFFFFFF) 1 z 1 → m'.mem z = m.mem z := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, c1, u1⟩ := St.block ceBody s0 hc ceBody_end (by simp [BlockOk, BInstr.ok, ceBody])
  simp only [runBlock, BInstr.run, ceBody] at u1
  obtain ⟨n2, d2, u2⟩ := u1.self.auipc hc ce_at_10 (off' := 0x14) (by decide)
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc ce_at_14
  have k : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ t1 → reg n3 r = reg m r := fun r h0' h1' ht => by
    rw [regs3]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, ht, ite_false]; rw [u1.regs]; simp only [upd_app, h0, h0', h1', ite_false]
  have pcB : n3.pc = base + 0xFFFFE84E := by
    rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
    rw [show base + BitVec.ofNat 32 0x10 + 0xFFFFF000 + 0xFFFFF83E = base + 0xFFFFE84E by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at base hP 0xFFFFE84E (by decide))
  have hv : (x ^^^ y).toNat < 256 := by
    rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (n := 8) hx hy
  have e0 : reg n3 a0 = if x = y then 1 else 0 := by
    rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [ha0, ha1]
    have := ceBits _ hv
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    show aluEval .xor (aluEval .srl (aluEval .sll (aluEval .or (x ^^^ y) (aluEval .sub 0 (x ^^^ y))) 24) 31) 1 = _
    rw [this]
    by_cases h : x = y
    · rw [if_pos h, if_pos (by rw [h, BitVec.xor_self]; rfl)]
    · rw [if_neg h, if_neg (fun h' => h (by
        have := BitVec.eq_of_toNat_eq (x := x ^^^ y) (y := 0) (by rw [h']; rfl)
        exact BitVec.xor_eq_zero_iff.mp this))]
  have sp3 : reg n3 sp = reg m sp := k sp (by decide) (by decide) (by decide)
  obtain ⟨m4, c4, pc4, a04, k4, f4⟩ := blackBoxU8_correct n3 (by rw [mem3]; exact hbb) pcB
    (by rw [k ra (by decide) (by decide) (by decide), hra]) hret (by rw [sp3]; exact hsep)
  refine ⟨m4, c1.trans (.cons d2 (.cons d3 c4)), pc4, ?_, fun r h0' h1' ht => ?_, fun z hz' => ?_⟩
  · rw [a04, e0]; exact zext_low01 (by split <;> simp)
  · rw [k4 r h0', k r h0' h1' ht]
  · rw [f4 z (by rw [sp3]; exact hz'), mem3]


/-- The registers the slice `ct_eq` saves, at offsets from its `sp`. -/
abbrev csPs : List (Fin 32 × Word) :=
  [(ra, 0x1C), ((8 : Fin 32), 0x18), ((9 : Fin 32), 0x14), ((18 : Fin 32), 0x10), ((19 : Fin 32), 0xC)]

/-- From 0xC to 0x16: keep the pointers, the running result, and the count. -/
def csInit : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a1, .alu .add (9 : Fin 32) x0 a0, .aluImm .add (18 : Fin 32) x0 0x1,
   .aluImm .add (8 : Fin 32) x0 0x20]

/-- From 0x18 to the call at 0x20: load the two bytes. -/
def csHead : List BInstr := [.lbu a1 (19 : Fin 32) 0x0, .lbu a0 (9 : Fin 32) 0x0]

/-- From 0x28 to 0x32: step the pointers, fold the byte's result in, and
count down. -/
def csTail : List BInstr :=
  [.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1, .alu .and (18 : Fin 32) a0 (18 : Fin 32),
   .aluImm .add (19 : Fin 32) (19 : Fin 32) 0x1, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem csSave_end : blockEnd ctEqSliceCode 2 (saveBlock csPs) = some 0xC := by decide
theorem csInit_end : blockEnd ctEqSliceCode 0xC csInit = some 0x16 := by decide
theorem csHead_end : blockEnd ctEqSliceCode 0x18 csHead = some 0x20 := by decide
theorem csTail_end : blockEnd ctEqSliceCode 0x28 csTail = some 0x32 := by decide
theorem csRestore_end : blockEnd ctEqSliceCode 0x38 (restoreBlock csPs) = some 0x42 := by decide
theorem csPs_range : ∀ p ∈ csPs, p.2.toNat % 4 = 0 ∧ 0xC ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x20 := by decide
theorem csPs_sp : ∀ p ∈ csPs, p.1 ≠ sp := by decide
end


theorem zext8_eq {x y : BitVec 8} : x.zeroExtend 32 = y.zeroExtend 32 ↔ x = y := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (by have := x.isLt; omega), Nat.mod_eq_of_lt (by have := y.isLt; omega)] at this
  · intro h; rw [h]

theorem zext8_lt (x : BitVec 8) : (x.zeroExtend 32 : Word).toNat < 256 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]; exact x.isLt

theorem and01 {a b : Word} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    aluEval .and a b = if a = 1 ∧ b = 1 then 1 else 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The 32-byte `<[u8] as subtle::ConstantTimeEq>::ct_eq`** returns 1
when the 32 bytes at `p` equal the 32 bytes at `q` and 0 otherwise. It
calls `ct_eq` for bytes on each pair and ends with a tail call to
`black_box::<u8>`. -/
theorem ctEqSlice_correct (m : Machine) {base retAddr p q : Word} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base ctEqSliceCode) (hce : CodeIn m.mem (base + 0xFFFFFFE8) ctEqU8Code)
    (hbb : CodeIn m.mem (base + 0xFFFFE836) blackBoxU8Code)
    (hpc : m.pc = base) (ha0 : reg m a0 = p) (ha1 : reg m a1 = q) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0) (hS : 0x21 ≤ (reg m sp).toNat)
    (sRC : Sep (reg m sp + 0xFFFFFFDF) 0x21 base ctEqSliceCode.length)
    (sRE : Sep (reg m sp + 0xFFFFFFDF) 0x21 (base + 0xFFFFFFE8) ctEqU8Code.length)
    (sRB : Sep (reg m sp + 0xFFFFFFDF) 0x21 (base + 0xFFFFE836) blackBoxU8Code.length)
    (sP : Sep p 32 (reg m sp + 0xFFFFFFDF) 0x21) (sQ : Sep q 32 (reg m sp + 0xFFFFFFDF) 0x21) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (reg m' a0 = 0 ∨ reg m' a0 = 1) ∧
      (reg m' a0 = 1 ↔ ∀ i, i < 32 → m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i)) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ t1 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFDF) 0x21 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨R, hR⟩ : ∃ R, reg m sp + 0xFFFFFFDF = R := ⟨_, rfl⟩
  rw [hR] at sRC sRE sRB sP sQ ⊢
  have hRw : R.toNat + 0x21 = (reg m sp).toNat := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFFDF : Word).toNat = 4294967263 from rfl]
    have := (reg m sp).isLt; omega
  have eF : reg m sp + 0xFFFFFFE0 = R + BitVec.ofNat 32 1 := by rw [← hR, BitVec.add_assoc]; rfl
  have hFa : (R + BitVec.ofNat 32 1).toNat % 4 = 0 := by rw [← eF]; exact aligned_add hsp (k := 0xFFFFFFE0) (by decide)
  have sFC : Sep (R + BitVec.ofNat 32 1) 0x20 base ctEqSliceCode.length := sRC.sub (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep R 0x21 b code.length → (∀ x, Sep R 0x21 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc' hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  -- the prologue
  obtain ⟨m1, d1, u1⟩ := s0.aluImm hc cs_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = R + BitVec.ofNat 32 1 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, eF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock csPs) u1 hc csSave_end (saveBlock_ok _ csPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (csPs_range p hp).1, frm_sep' sFC (by have := csPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (R + BitVec.ofNat 32 1)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) csPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep R 0x21 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside csPs fun p hp => frm_sep' (hx.sub (c := 1) (l := 0x20) (by decide))
      (by have := csPs_range p hp; omega)
  have hslv : ∀ r o, (r, o) ∈ csPs → memLoad32 Msv (R + BitVec.ofNat 32 1 + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [csPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have keepNames : ∀ r : Fin 32, r.val ∉ [1, 2, 6, 8, 9, 10, 11, 18, 19] → r ≠ a0 ∧ r ≠ a1 ∧ r ≠ t1 ∧ r ≠ ra ∧
      r ≠ sp ∧ r ≠ (8 : Fin 32) ∧ r ≠ (9 : Fin 32) ∧ r ≠ (18 : Fin 32) ∧ r ≠ (19 : Fin 32) := fun r hr => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> exact hr (by decide)
  -- the loop, from byte `i` with `k` bytes left
  have loop : ∀ k i, i + k = 32 → 0 < k → ∀ {n1 : Machine} {M : Word → BitVec 8} {acc : Word},
      St M base n1 0x18 (reg n1) → (∀ x, Sep R 0x21 x 1 → M x = m.mem x) →
      (∀ r o, (r, o) ∈ csPs → memLoad32 M (R + BitVec.ofNat 32 1 + o) = reg m r) →
      reg n1 sp = R + BitVec.ofNat 32 1 → reg n1 9 = p + BitVec.ofNat 32 i → reg n1 19 = q + BitVec.ofNat 32 i →
      reg n1 8 = BitVec.ofNat 32 k → reg n1 18 = acc → (acc = 0 ∨ acc = 1) →
      (acc = 1 ↔ ∀ j, j < i → m.mem (p + BitVec.ofNat 32 j) = m.mem (q + BitVec.ofNat 32 j)) →
      (∀ r : Fin 32, r.val ∉ [1, 2, 6, 8, 9, 10, 11, 18, 19] → reg n1 r = reg m r) →
      ∃ n' M' acc', Steps n1 n' ∧ St M' base n' 0x34 (reg n') ∧ (∀ x, Sep R 0x21 x 1 → M' x = m.mem x) ∧
        (∀ r o, (r, o) ∈ csPs → memLoad32 M' (R + BitVec.ofNat 32 1 + o) = reg m r) ∧
        reg n' sp = R + BitVec.ofNat 32 1 ∧ reg n' 18 = acc' ∧ (acc' = 0 ∨ acc' = 1) ∧
        (acc' = 1 ↔ ∀ j, j < 32 → m.mem (p + BitVec.ofNat 32 j) = m.mem (q + BitVec.ofNat 32 j)) ∧
        (∀ r : Fin 32, r.val ∉ [1, 2, 6, 8, 9, 10, 11, 18, 19] → reg n' r = reg m r) := by
    intro k
    induction k with
    | zero => intro i _ hk; exact absurd hk (Nat.lt_irrefl 0)
    | succ k ih =>
      intro i hik _ n1 M acc s1 hfr hsl rsp r9 r19 r8 r18 hacc01 hacc hk
      have hcM := cIn hc sRC hfr
      obtain ⟨n2, c2, u2⟩ := St.block csHead s1 hcM csHead_end (by simp [BlockOk, BInstr.ok, csHead])
      simp only [runBlock, BInstr.run, csHead] at u2
      have g2 : ∀ r, reg n2 r = _ := u2.regs
      have hpi : M (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) := hfr _ (sP.symm.subR (by omega))
      have hqi : M (q + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) := hfr _ (sQ.symm.subR (by omega))
      obtain ⟨m3, d3, pc3, mem3, regs3⟩ := u2.self.callRa hcM cs_at_20 cs_at_24
        (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hP 0xFFFFFFE8 (by decide))
      have r3 : ∀ q, q ≠ ra → reg m3 q = reg n2 q := PEnv.reg1 regs3 u2.self.zero
      have hsp3 : reg m3 sp = R + BitVec.ofNat 32 1 := by
        rw [r3 sp (by decide), g2]; simp +decide only [upd_app, ↓reduceIte]; exact rsp
      have eR : R + BitVec.ofNat 32 1 + 0xFFFFFFFF = R := by rw [BitVec.add_assoc]; exact BitVec.add_zero R
      have ebb : base + BitVec.ofNat 32 0xFFFFFFE8 + 0xFFFFE84E = base + 0xFFFFE836 := by rw [BitVec.add_assoc]; rfl
      obtain ⟨m4, c4, pc4, a04, k4, f4⟩ := ctEqU8_correct m3 (even_at base hP 0xFFFFFFE8 (by decide))
        (by rw [mem3]; exact cIn hce sRE hfr) (by rw [mem3, ebb]; exact cIn hbb sRB hfr) pc3
        (by rw [r3 a0 (by decide), g2]; simp +decide only [upd_app, ↓reduceIte]; try rfl)
        (by rw [r3 a1 (by decide), g2]; simp +decide only [upd_app, ↓reduceIte]; try rfl)
        (zext8_lt _) (zext8_lt _)
        (by rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; try rfl)
        (even_clear _ (even_at base hP (0x20 + 8) (by decide)))
        (by rw [hsp3, eR, ebb]; have := sRB.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)
      have u4 : St m4.mem base m4 0x28 (reg m4) := ⟨by rw [pc4], rfl, fun _ => rfl⟩
      have fr4 : ∀ x, Sep R 0x21 x 1 → m4.mem x = m.mem x := fun x hx => by
        rw [f4 x (by rw [hsp3, eR]; have := hx.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this),
          mem3, hfr x hx]
      have k34 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ t1 → q ≠ ra → reg m4 q = reg n2 q := fun q h0' h1' ht hr =>
        (k4 q h0' h1' ht).trans (r3 q hr)
      obtain ⟨n5, c5, u5⟩ := St.block csTail u4 (cIn hc sRC fr4) csTail_end (by simp [BlockOk, BInstr.ok, csTail])
      simp only [runBlock, BInstr.run, csTail] at u5
      have g5 : ∀ r, reg n5 r = _ := u5.regs
      have eq_i : (if (m.mem (p + BitVec.ofNat 32 i)).zeroExtend 32 = (m.mem (q + BitVec.ofNat 32 i)).zeroExtend 32
          then (1 : Word) else 0) = if m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) then 1 else 0 := by
        by_cases h : m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i)
        · rw [if_pos (zext8_eq.mpr h), if_pos h]
        · rw [if_neg (fun h' => h (zext8_eq.mp h')), if_neg h]
      have a0v : reg m4 a0 = if m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) then 1 else 0 := by
        rw [a04, r9, r19, add_lit_zero, add_lit_zero, hpi, hqi]; exact eq_i
      have k12 : ∀ r : Fin 32, r.val ∉ [1, 2, 6, 8, 9, 10, 11, 18, 19] → reg m4 r = reg m r := fun r hr => by
        obtain ⟨h0', h1', ht, hra', _, _, _, _, _⟩ := keepNames r hr
        rw [k34 r h0' h1' ht hra', g2]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact hz.symm
        simp only [upd_app, h0, h0', h1', ite_false]; exact hk r hr
      have rr : ∀ r : Fin 32, r = (8 : Fin 32) ∨ r = (9 : Fin 32) ∨ r = (18 : Fin 32) ∨ r = (19 : Fin 32) ∨ r = sp →
          reg m4 r = reg n1 r := fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        · rw [k34 _ (by decide) (by decide) (by decide) (by decide), g2]; simp +decide only [upd_app, ↓reduceIte]
      have accv : aluEval .and (reg m4 a0) acc = if m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) ∧
          acc = 1 then 1 else 0 := by
        rw [a0v, and01 (by split <;> simp) hacc01]
        have h01 : ¬ ((0 : Word) = 1) := by decide
        by_cases h : m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i)
        · simp only [h, ↓reduceIte, true_and]
        · simp only [h, ↓reduceIte, false_and, h01]
      have acc01' : aluEval .and (reg m4 a0) acc = 0 ∨ aluEval .and (reg m4 a0) acc = 1 := by
        rw [accv]; split <;> simp
      have acc1' : aluEval .and (reg m4 a0) acc = 1 ↔
          ∀ j, j < i + 1 → m.mem (p + BitVec.ofNat 32 j) = m.mem (q + BitVec.ofNat 32 j) := by
        rw [accv]
        constructor
        · intro h
          have h' : m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) ∧ acc = 1 := by
            by_cases hn : m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) ∧ acc = 1
            · exact hn
            · rw [if_neg hn] at h; exact absurd h (by decide)
          intro j hj
          rcases (by omega : j < i ∨ j = i) with hj' | hj'
          · exact hacc.mp h'.2 j hj'
          · subst hj'; exact h'.1
        · intro h; rw [if_pos ⟨h i (by omega), hacc.mpr fun j hj => h j (by omega)⟩]
      have sl4 : ∀ r o, (r, o) ∈ csPs → memLoad32 m4.mem (R + BitVec.ofNat 32 1 + o) = reg m r := fun r o h => by
        obtain ⟨_, ho1, ho2⟩ := csPs_range (r, o) h
        dsimp only at ho1 ho2
        have e : R + BitVec.ofNat 32 1 + o = R + BitVec.ofNat 32 (1 + o.toNat) := by
          conv => lhs; rw [← ofNat_toNat_self o]
          rw [add_ofNat_assoc]
        rw [memLoad32_congr fun t ht => f4 _ (by
            rw [hsp3, eR, e, add_ofNat_assoc]
            have := sep_offsets R (c := 0) (n := 1) (d := 1 + o.toNat + t) (k := 1) (.inl (by omega)) (by omega)
              (by omega)
            rwa [add_ofNat_zero] at this), mem3, hsl r o h]
      have r9_5 : reg n5 9 = p + BitVec.ofNat 32 (i + 1) := by
        rw [g5]; simp +decide only [upd_app, ↓reduceIte]
        rw [rr 9 (by decide), r9, ev_add, show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]
      have r19_5 : reg n5 19 = q + BitVec.ofNat 32 (i + 1) := by
        rw [g5]; simp +decide only [upd_app, ↓reduceIte]
        rw [rr 19 (by decide), r19, ev_add, show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]
      have r8_5 : reg n5 8 = BitVec.ofNat 32 k := by
        rw [g5]; simp +decide only [upd_app, ↓reduceIte]
        rw [rr 8 (by decide), r8, ev_add]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, ofNat_tn (by omega), ofNat_tn (by omega)]
        show (k + 1 + 4294967295) % 2 ^ 32 = k; omega
      have r18_5 : reg n5 18 = aluEval .and (reg m4 a0) acc := by
        rw [g5]; simp +decide only [upd_app, ↓reduceIte]; rw [rr 18 (by decide), r18]
      have sp5 : reg n5 sp = R + BitVec.ofNat 32 1 := by
        rw [g5]; simp +decide only [upd_app, ↓reduceIte]; rw [rr sp (by decide), rsp]
      have keep5 : ∀ r : Fin 32, r.val ∉ [1, 2, 6, 8, 9, 10, 11, 18, 19] → reg n5 r = reg m r := fun r hr => by
        obtain ⟨_, _, _, _, _, h8, h9, h18, h19⟩ := keepNames r hr
        rw [g5]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact hz.symm
        simp only [upd_app, h0, h8, h9, h18, h19, ite_false]; exact k12 r hr
      by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨n6, d6, u6⟩ := u5.self.notTaken (cIn hc sRC fr4) 0x34 cs_at_32 (by decide) (by
          rw [r8_5, u5.self.zero]; decide)
        exact ⟨n6, m4.mem, _, c2.trans (d3.trans (c4.trans (c5.trans (.single d6)))), u6.self, fr4, sl4,
          by rw [u6.regs, sp5], by rw [u6.regs, r18_5], acc01',
          ⟨fun h j hj => acc1'.mp h j (by omega), fun h => acc1'.mpr fun j hj => h j (by omega)⟩,
          fun r hr => by rw [u6.regs]; exact keep5 r hr⟩
      · obtain ⟨n6, d6, u6⟩ := u5.self.taken (cIn hc sRC fr4) 0x18 cs_at_32 (by decide) (by
          rw [r8_5, u5.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
          have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact hk0 this)
        obtain ⟨n', M', acc', c', h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih (i + 1) (by omega) (by omega) u6.self fr4 sl4
          (by rw [u6.regs, sp5]) (by rw [u6.regs, r9_5]) (by rw [u6.regs, r19_5]) (by rw [u6.regs, r8_5])
          (by rw [u6.regs, r18_5]) acc01' acc1' (fun r hr => by rw [u6.regs]; exact keep5 r hr)
        exact ⟨n', M', acc', c2.trans (d3.trans (c4.trans (c5.trans (.cons d6 c')))), h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hcv := cIn hc sRC frSv
  obtain ⟨m3, c3, u3⟩ := St.block csInit u2.self hcv csInit_end (by simp [BlockOk, BInstr.ok, csInit])
  simp only [runBlock, BInstr.run, csInit] at u3
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) r := u2.regs
  obtain ⟨m4, d4, u4⟩ := u3.self.notTaken hcv 0x18 cs_at_16 (by decide) (by
    rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval]
    rw [show reg m3 x0 = 0 from u3.self.zero]; decide)
  have g4 : ∀ r, reg m4 r = reg m3 r := u4.regs
  obtain ⟨n5, M5, acc, c5, s5, fr5, sl5, sp5, r18_5, acc01, acc1, keep5⟩ := loop 32 0 rfl (by decide) u4.self frSv hslv
    (by rw [g4, g3]; simp +decide only [upd_app, ↓reduceIte]; rw [r2]; exact sp1)
    (by rw [g4, g3]; simp +decide only [upd_app, ↓reduceIte]; simp only [r2]; simp +decide only [upd_app, ↓reduceIte]
        rw [ha0, add_ofNat_zero]; exact zw _)
    (by rw [g4, g3]; simp +decide only [upd_app, ↓reduceIte]; simp only [r2]; simp +decide only [upd_app, ↓reduceIte]
        rw [ha1, add_ofNat_zero]; exact zw _)
    (by rw [g4, g3]; simp +decide only [upd_app, ↓reduceIte, aluEval]; try (rw [show reg m2 x0 = 0 from u2.self.zero]; rfl))
    (by rw [g4, g3]; simp +decide only [upd_app, ↓reduceIte, aluEval]; try (rw [show reg m2 x0 = 0 from u2.self.zero]; rfl))
    (.inr rfl) ⟨fun _ j hj => absurd hj (Nat.not_lt_zero j), fun _ => rfl⟩
    (fun r hr => by
      obtain ⟨h0', h1', _, _, hs, h8, h9, h18, h19⟩ := keepNames r hr
      rw [g4, g3]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h8, h9, h18, h19, ite_false]; rw [r2]; simp only [upd_app, h0, hs, ite_false])
  have hc5 := cIn hc sRC fr5
  obtain ⟨n6, d6, u6⟩ := s5.aluImm hc5 cs_at_34 (off' := 0x38) (by decide)
  have sp6 : reg n6 sp = R + BitVec.ofNat 32 1 := by rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5
  obtain ⟨n7, c7, u7⟩ := St.block (restoreBlock csPs) u6.self hc5 csRestore_end
    (restoreBlock_ok M5 _ csPs (reg n6) sp6 csPs_sp fun p hp => fr_al' hFa (csPs_range p hp).1)
  simp only [restoreBlock_run M5 _ csPs (reg n6) sp6 csPs_sp] at u7
  obtain ⟨n8, d8, u8⟩ := u7.aluImm hc5 cs_at_42 (off' := 0x44) (by decide)
  obtain ⟨n9, d9, u9⟩ := u8.auipc hc5 cs_at_44 (off' := 0x48) (by decide)
  obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.jalr hc5 cs_at_48
  have rsp7 : restoreRegs M5 (R + BitVec.ofNat 32 1) (reg n6) csPs sp = R + BitVec.ofNat 32 1 := by
    rw [restoreRegs_sp _ _ _ _ csPs_sp]; exact sp6
  have hsp0 : R + BitVec.ofNat 32 1 + 0x20 = reg m sp := by
    rw [← hR, BitVec.add_assoc, BitVec.add_assoc]
    rw [show (0xFFFFFFDF : Word) + (BitVec.ofNat 32 1 + 0x20) = 0 by decide, add_lit_zero]
  have rest : ∀ r o, (r, o) ∈ csPs → restoreRegs M5 (R + BitVec.ofNat 32 1) (reg n6) csPs r = reg m r :=
    fun r o h => by
      simp only [csPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        exact sl5 _ _ (by decide)
  have pcB : n10.pc = base + 0xFFFFE836 := by
    rw [pc10]; simp +decide only [upd_app, ↓reduceIte]
    rw [show base + BitVec.ofNat 32 0x44 + 0xFFFFE000 + 0x7F2 = base + 0xFFFFE836 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at base hP 0xFFFFE836 (by decide))
  have sp10 : reg n10 sp = reg m sp := by
    rw [regs10]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp7, ev_add, hsp0]
  have ra10 : reg n10 ra = retAddr := by
    rw [regs10]; simp +decide only [upd_app, ↓reduceIte]; rw [rest ra 0x1C (by decide), hra]
  have accw : reg n10 a0 = aluEval .and acc 0xFF := by
    rw [regs10]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; rw [u6.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [r18_5]
  have eacc : aluEval .and acc 0xFF = acc := by rcases acc01 with h | h <;> rw [h] <;> decide
  obtain ⟨m11, c11, pc11, a011, k11, f11⟩ := blackBoxU8_correct n10 (by rw [mem10]; exact cIn hbb sRB fr5) pcB
    ra10 hret (by rw [sp10, show reg m sp + 0xFFFFFFFF = R + BitVec.ofNat 32 0x20 by
      rw [← hR, BitVec.add_assoc]; rfl]; exact sRB.sub (by decide))
  have steps : Steps m m11 :=
    .cons d1 (c2.trans (c3.trans (.cons d4 (c5.trans (.cons d6 (c7.trans (.cons d8 (.cons d9 (.cons d10 c11)))))))))
  refine ⟨m11, steps, pc11, ?_, ?_, fun r h0' h1' ht => ?_, fun x hx => ?_⟩
  · rw [a011, accw, eacc]; rcases acc01 with h | h <;> rw [h] <;> decide
  · rw [a011, accw, eacc]
    rcases acc01 with h | h <;> rw [h]
    · constructor
      · intro h'; exact absurd ((zext_low01 (.inl rfl)).symm.trans h') (by decide)
      · intro h'; exact absurd (acc1.mpr h') (by rw [h]; decide)
    · rw [zext_low01 (.inr rfl)]; exact ⟨fun _ => acc1.mp h, fun _ => rfl⟩
  · rw [k11 r h0']
    by_cases hs : r = sp
    · subst hs; exact sp10
    rw [regs10]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, ht, hs, ite_false]
    by_cases hsv : r.val ∈ [1, 8, 9, 18, 19]
    · have : ∃ o, (r, o) ∈ csPs := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsv
        rcases hsv with h | h | h | h | h <;> rw [show r = ⟨_, by decide⟩ from Fin.ext h]
        · exact ⟨0x1C, by decide⟩
        · exact ⟨0x18, by decide⟩
        · exact ⟨0x14, by decide⟩
        · exact ⟨0x10, by decide⟩
        · exact ⟨0xC, by decide⟩
      obtain ⟨o, ho⟩ := this
      exact rest r o ho
    simp only [restoreRegs]
    have nq : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18, 19] → r ≠ w := fun w hw e => hsv (e ▸ hw)
    simp only [upd_app, h0, nq ra (by decide), nq 8 (by decide), nq 9 (by decide), nq 18 (by decide),
      nq 19 (by decide), ite_false]
    rw [u6.regs]; simp only [upd_app, h0, h0', ite_false]
    exact keep5 r (fun h => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at h hsv
      have : r.val ≠ 2 := fun e => hs (Fin.ext e)
      have : r.val ≠ 6 := fun e => ht (Fin.ext e)
      have : r.val ≠ 10 := fun e => h0' (Fin.ext e)
      have : r.val ≠ 11 := fun e => h1' (Fin.ext e)
      omega)
  · rw [f11 x (by rw [sp10, show reg m sp + 0xFFFFFFFF = R + BitVec.ofNat 32 0x20 by
      rw [← hR, BitVec.add_assoc]; rfl]; exact hx.sub (by decide)), mem10, fr5 x hx]

end C3.RV32
