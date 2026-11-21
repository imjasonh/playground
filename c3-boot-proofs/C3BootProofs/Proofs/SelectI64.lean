import C3BootProofs.Proofs.FlashRead

/-!
# `<ctutils::choice::Choice>::select_i64`

The out-of-line copy of `ctutils`'s constant-time select on `i64` that
`crypto_bigint`'s `safegcd` calls. It spills the choice byte to the stack
and reads it back, an optimization barrier, then masks: choice 0 gives the
first operand and choice 1 the second, each `i64` in two registers.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem sel_at_0 : fetchRel selectI64Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem sel_at_2 : fetchRel selectI64Code 0x2 = some (.store .sb sp a0 0xF, 4) := by decide
theorem sel_at_6 : fetchRel selectI64Code 0x6 = some (.aluImm .add a0 sp 0xF, 4) := by decide
theorem sel_at_a : fetchRel selectI64Code 0xA = some (.load .lbu a0 sp 0xF, 4) := by decide
theorem sel_at_e : fetchRel selectI64Code 0xE = some (.aluImm .sltu a5 a0 0x1, 4) := by decide
theorem sel_at_12 : fetchRel selectI64Code 0x12 = some (.alu .sub a0 x0 a0, 4) := by decide
theorem sel_at_16 : fetchRel selectI64Code 0x16 = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem sel_at_18 : fetchRel selectI64Code 0x18 = some (.alu .xor a4 a4 a2, 2) := by decide
theorem sel_at_1a : fetchRel selectI64Code 0x1A = some (.alu .xor a3 a3 a1, 2) := by decide
theorem sel_at_1c : fetchRel selectI64Code 0x1C = some (.alu .and a0 a0 a3, 2) := by decide
theorem sel_at_1e : fetchRel selectI64Code 0x1E = some (.alu .and a4 a4 a5, 2) := by decide
theorem sel_at_20 : fetchRel selectI64Code 0x20 = some (.alu .xor a0 a0 a1, 2) := by decide
theorem sel_at_22 : fetchRel selectI64Code 0x22 = some (.alu .xor a1 a4 a2, 4) := by decide
theorem sel_at_26 : fetchRel selectI64Code 0x26 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem sel_at_28 : fetchRel selectI64Code 0x28 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem xor_xor_cancel (a b : Word) : (a ^^^ b) ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem zero_and' (x : Word) : (0 : Word) &&& x = 0 := BitVec.zero_and

theorem and_zero' (x : Word) : x &&& (0 : Word) = 0 := BitVec.and_zero

theorem zero_xor' (x : Word) : (0 : Word) ^^^ x = x := BitVec.zero_xor

set_option maxHeartbeats 4000000 in
/-- **The compiled `<ctutils::choice::Choice>::select_i64`**, called with the
choice in `a0`'s low byte and two `i64`s, `a1:a2` and `a3:a4` (low word
first): with choice 0 it returns the first in `a0:a1`, and with choice 1 the
second. It returns with `sp` as it was, changes no register but `a0`, `a1`,
and `a3` through `a5`, and changes no memory but the byte below `sp`. -/
theorem selectI64_correct (m : Machine) {P retAddr : Word}
    (hc : CodeIn m.mem P selectI64Code) (hpc : m.pc = P) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hS : Sep (reg m sp + 0xFFFFFFFF) 1 P selectI64Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg m' q = reg m q) ∧
      ((reg m a0).extractLsb' 0 8 = 0 → reg m' a0 = reg m a1 ∧ reg m' a1 = reg m a2) ∧
      ((reg m a0).extractLsb' 0 8 = 1 → reg m' a0 = reg m a3 ∧ reg m' a1 = reg m a4) ∧
      ∀ x, x ≠ reg m sp + 0xFFFFFFFF → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨A, hA⟩ : ∃ A, reg m sp + 0xFFFFFFFF = A := ⟨_, rfl⟩
  obtain ⟨c, hcv⟩ : ∃ c, (reg m a0).extractLsb' 0 8 = c := ⟨_, rfl⟩
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc sel_at_0 (off' := 2) (by decide)
  have k1 := u1.oldReg hz
  have sp1 : reg n1 sp = reg m sp + 0xFFFFFFF0 := u1.newReg (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.sb hc sel_at_2 (off' := 6) (by decide)
  have eA : reg n1 sp + 0xF = A := by rw [sp1, ← hA, BitVec.add_assoc]; rfl
  rw [eA, k1 _ (by decide), hcv] at u2
  have hc2 : CodeIn (memStore8 m.mem A c) P selectI64Code := fun i hi => by
    have hne : P + BitVec.ofNat 32 i ≠ A := by
      have := hS 0 (by decide) i hi; rw [add_ofNat_zero, hA] at this; exact fun e => this e.symm
    show (if P + BitVec.ofNat 32 i = A then c else m.mem (P + BitVec.ofNat 32 i)) = _
    split
    · next h => exact absurd h hne
    · exact hc i hi
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc2 sel_at_6 (off' := 0xA) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.lbu hc2 sel_at_a (off' := 0xE) (by decide)
  have k3 := u3.oldReg u2.zero
  have k4 := u4.oldReg u3.self.zero
  have a0_4 : reg n4 a0 = c.zeroExtend 32 := by
    rw [u4.newReg (by decide), k3 _ (by decide), eA]
    show (if A = A then c else m.mem A).zeroExtend 32 = _
    split
    · rfl
    · next h => exact absurd rfl h
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc2 sel_at_e (off' := 0x12) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.alu hc2 sel_at_12 (off' := 0x16) (by decide)
  obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hc2 sel_at_16 (off' := 0x18) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.self.alu hc2 sel_at_18 (off' := 0x1A) (by decide)
  obtain ⟨n9, d9, u9⟩ := u8.self.alu hc2 sel_at_1a (off' := 0x1C) (by decide)
  obtain ⟨n10, d10, u10⟩ := u9.self.alu hc2 sel_at_1c (off' := 0x1E) (by decide)
  obtain ⟨n11, d11, u11⟩ := u10.self.alu hc2 sel_at_1e (off' := 0x20) (by decide)
  obtain ⟨n12, d12, u12⟩ := u11.self.alu hc2 sel_at_20 (off' := 0x22) (by decide)
  obtain ⟨n13, d13, u13⟩ := u12.self.alu hc2 sel_at_22 (off' := 0x26) (by decide)
  obtain ⟨n14, d14, u14⟩ := u13.self.aluImm hc2 sel_at_26 (off' := 0x28) (by decide)
  obtain ⟨n15, d15, pc15, mem15, regs15⟩ := u14.self.jalr hc2 sel_at_28
  have k5 := u5.oldReg u4.self.zero
  have k6 := u6.oldReg u5.self.zero
  have k7 := u7.oldReg u6.self.zero
  have k8 := u8.oldReg u7.self.zero
  have k9 := u9.oldReg u8.self.zero
  have k10 := u10.oldReg u9.self.zero
  have k11 := u11.oldReg u10.self.zero
  have k12 := u12.oldReg u11.self.zero
  have k13 := u13.oldReg u12.self.zero
  have k14 := u14.oldReg u13.self.zero
  -- the two masks and the operands' xors
  have r1 : ∀ q, q ≠ sp → q ≠ a0 → reg n4 q = reg m q := fun q h1 h2 => by
    rw [k4 q h2, k3 q h2, k1 q h1]
  have m0 : reg n12 a0 = (0 - c.zeroExtend 32) &&& (reg m a3 ^^^ reg m a1) ^^^ reg m a1 := by
    rw [u12.newReg (by decide)]; show reg n11 a0 ^^^ reg n11 a1 = _
    rw [k11 _ (by decide), u10.newReg (by decide)]; show reg n9 a0 &&& reg n9 a3 ^^^ _ = _
    rw [u9.newReg (by decide), k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), u6.newReg (by decide)]
    show (reg n5 0 - reg n5 a0) &&& (reg n8 a3 ^^^ reg n8 a1) ^^^ _ = _
    rw [u5.self.zero, k5 _ (by decide), a0_4, k11 _ (by decide), k10 _ (by decide), k9 _ (by decide),
      k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), r1 _ (by decide) (by decide),
      k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), r1 _ (by decide) (by decide)]
  have m1 : reg n13 a1 = (reg m a4 ^^^ reg m a2) &&& (aluEval .sltu (c.zeroExtend 32) 0x1 + 0xFFFFFFFF) ^^^
      reg m a2 := by
    rw [u13.newReg (by decide)]; show reg n12 a4 ^^^ reg n12 a2 = _
    rw [k12 _ (by decide), u11.newReg (by decide)]; show reg n10 a4 &&& reg n10 a5 ^^^ _ = _
    rw [k10 _ (by decide), k9 _ (by decide), u8.newReg (by decide), k10 _ (by decide), k9 _ (by decide),
      k8 _ (by decide), u7.newReg (by decide)]
    show (reg n7 a4 ^^^ reg n7 a2) &&& (reg n6 a5 + 0xFFFFFFFF) ^^^ _ = _
    rw [k6 _ (by decide), u5.newReg (by decide), a0_4, k12 _ (by decide), k11 _ (by decide),
      k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide),
      r1 _ (by decide) (by decide)]
    simp only [k7 a2 (by decide), k6 a2 (by decide), k5 a2 (by decide), r1 a2 (by decide) (by decide)]
  have keep : ∀ q, q ≠ sp → q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg n14 q = reg m q :=
    fun q h1 h2 h3 h4 h5 h6 => by
      rw [k14 q h1, k13 q h3, k12 q h2, k11 q h5, k10 q h2, k9 q h4, k8 q h5, k7 q h6, k6 q h2, k5 q h6, r1 q h1 h2]
  have sp14 : reg n14 sp = reg m sp := by
    rw [u14.newReg (by decide)]; show reg n13 sp + 0x10 = _
    rw [k13 _ (by decide), k12 _ (by decide), k11 _ (by decide), k10 _ (by decide), k9 _ (by decide),
      k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide),
      sp1, BitVec.add_assoc]
    exact BitVec.add_zero _
  refine ⟨n15, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
    (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.single d15)))))))))))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc15, keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), add_lit_zero, hra,
      hret]
  · rw [regs15, sp14]
  · intro q h2 h3 h4 h5 h6
    by_cases h1 : q = sp
    · subst h1; rw [regs15, sp14]
    · rw [regs15, keep q h1 h2 h3 h4 h5 h6]
  · intro h0
    rw [hcv] at h0; subst h0
    rw [regs15, k14 _ (by decide), k13 _ (by decide), m0, regs15, k14 _ (by decide), m1]
    exact ⟨by rw [show (0 : BitVec 8).zeroExtend 32 = 0 from rfl, show (0 : Word) - 0 = 0 from rfl, zero_and',
      zero_xor'], by rw [show aluEval .sltu ((0 : BitVec 8).zeroExtend 32) 0x1 + 0xFFFFFFFF = 0 from rfl,
      and_zero', zero_xor']⟩
  · intro h0
    rw [hcv] at h0; subst h0
    rw [regs15, k14 _ (by decide), k13 _ (by decide), m0, regs15, k14 _ (by decide), m1]
    refine ⟨?_, ?_⟩
    · rw [show (0 : Word) - (1 : BitVec 8).zeroExtend 32 = 0xFFFFFFFF from rfl, BitVec.and_comm, and_ones,
        xor_xor_cancel]
    · rw [show aluEval .sltu ((1 : BitVec 8).zeroExtend 32) 0x1 + 0xFFFFFFFF = 0xFFFFFFFF from rfl, and_ones,
        xor_xor_cancel]
  · intro x hx
    rw [mem15, ← hA] at *
    show (if x = reg m sp + 0xFFFFFFFF then c else m.mem x) = _
    split
    · next h => exact absurd h hx
    · rfl

end C3.RV32
