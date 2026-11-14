import C3BootProofs.Proofs.SelectI64
import C3BootProofs.Proofs.LincombShift12

/-!
# `SignedInt::lowest` at 12 and 8 limbs

The compiled function reads the low 64 bits of the magnitude and the sign
byte, clears the top bit, computes the negation, and tail-calls the proved
`Choice::select_i64` to pick one of the two by the sign.
-/

namespace C3.RV32

open C3.Image

theorem lw12_at_0 : fetchRel lowest12Code 0x0 = some (.load .lw a2 a0 0x4, 2) := by decide
theorem lw12_at_2 : fetchRel lowest12Code 0x2 = some (.load .lw a1 a0 0x0, 2) := by decide
theorem lw12_at_4 : fetchRel lowest12Code 0x4 = some (.load .lbu a0 a0 0x30, 4) := by decide
theorem lw12_at_8 : fetchRel lowest12Code 0x8 = some (.aluImm .sll a2 a2 0x1, 2) := by decide
theorem lw12_at_a : fetchRel lowest12Code 0xA = some (.alu .sub a3 x0 a1, 4) := by decide
theorem lw12_at_e : fetchRel lowest12Code 0xE = some (.alu .sltu a4 x0 a1, 4) := by decide
theorem lw12_at_12 : fetchRel lowest12Code 0x12 = some (.aluImm .srl a2 a2 0x1, 2) := by decide
theorem lw12_at_14 : fetchRel lowest12Code 0x14 = some (.alu .sub a4 x0 a4, 4) := by decide
theorem lw12_at_18 : fetchRel lowest12Code 0x18 = some (.alu .sub a4 a4 a2, 2) := by decide
theorem lw12_at_1a : fetchRel lowest12Code 0x1A = some (.auipc (6 : Fin 32) 0xFFFFE000, 4) := by decide
theorem lw12_at_1e : fetchRel lowest12Code 0x1E = some (.jalr x0 (6 : Fin 32) 0xBE, 4) := by decide

theorem lw8_at_0 : fetchRel lowest8Code 0x0 = some (.load .lw a2 a0 0x4, 2) := by decide
theorem lw8_at_2 : fetchRel lowest8Code 0x2 = some (.load .lw a1 a0 0x0, 2) := by decide
theorem lw8_at_4 : fetchRel lowest8Code 0x4 = some (.load .lbu a0 a0 0x20, 4) := by decide
theorem lw8_at_8 : fetchRel lowest8Code 0x8 = some (.aluImm .sll a2 a2 0x1, 2) := by decide
theorem lw8_at_a : fetchRel lowest8Code 0xA = some (.alu .sub a3 x0 a1, 4) := by decide
theorem lw8_at_e : fetchRel lowest8Code 0xE = some (.alu .sltu a4 x0 a1, 4) := by decide
theorem lw8_at_12 : fetchRel lowest8Code 0x12 = some (.aluImm .srl a2 a2 0x1, 2) := by decide
theorem lw8_at_14 : fetchRel lowest8Code 0x14 = some (.alu .sub a4 x0 a4, 4) := by decide
theorem lw8_at_18 : fetchRel lowest8Code 0x18 = some (.alu .sub a4 a4 a2, 2) := by decide
theorem lw8_at_1a : fetchRel lowest8Code 0x1A = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem lw8_at_1e : fetchRel lowest8Code 0x1E = some (.jalr x0 (6 : Fin 32) 0x8, 4) := by decide

/-- The `i64` that `SignedInt::lowest` returns, as a 64-bit word, for the
low 64 bits `v` of a magnitude with sign byte `σ`: the low 63 bits, negated
when `σ` is 1. -/
def lowestVal (σ v : Nat) : Nat := if σ = 1 then (2 ^ 64 - v % 2 ^ 63) % 2 ^ 64 else v % 2 ^ 63

/-- The words `lowest` hands to `select_i64`: the magnitude with its top bit
cleared, and its negation. -/
theorem lowest_arith (lo hi : Word) :
    lo.toNat + 2 ^ 32 * ((hi <<< (1 % 32)) >>> (1 % 32)).toNat = (lo.toNat + 2 ^ 32 * hi.toNat) % 2 ^ 63 ∧
      (0 - lo).toNat + 2 ^ 32 * (((0 : Word) - (if (0 : Word).ult lo then (1 : Word) else 0)) - (hi <<< (1 % 32)) >>> (1 % 32)).toNat =
        (2 ^ 64 - (lo.toNat + 2 ^ 32 * hi.toNat) % 2 ^ 63) % 2 ^ 64 := by
  have hl := lo.isLt
  have hh := hi.isLt
  have e1 : ((hi <<< (1 % 32)) >>> (1 % 32)).toNat = hi.toNat % 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, show (1 % 32 : Nat) = 1 from rfl, Nat.pow_one]
    omega
  rw [e1]
  refine ⟨by omega, ?_⟩
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, e1]
  by_cases h0 : lo.toNat = 0
  · have hu : (0 : Word).ult lo = false := by simp [BitVec.ult, h0]
    rw [hu]; simp only [Bool.false_eq_true, ite_false]
    show (2 ^ 32 - lo.toNat + 0) % 2 ^ 32 + 2 ^ 32 * ((2 ^ 32 - hi.toNat % 2 ^ 31 + (2 ^ 32 - 0 + 0) % 2 ^ 32) % 2 ^ 32) = _
    omega
  · have hu : (0 : Word).ult lo = true := by simp [BitVec.ult]; omega
    rw [hu]; simp only [ite_true]
    show (2 ^ 32 - lo.toNat + 0) % 2 ^ 32 + 2 ^ 32 * ((2 ^ 32 - hi.toNat % 2 ^ 31 + (2 ^ 32 - 1 + 0) % 2 ^ 32) % 2 ^ 32) = _
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `SignedInt<12>::lowest`**, called with `a0` pointing at a
`SignedInt<12>` whose sign byte is 0 or 1: it returns in `a0` and `a1` the
words of `lowestVal` of the sign and the magnitude's low 64 bits. It changes
only `a0` through `a5` and `t1`, and writes only the byte below `sp`. -/
theorem lowest12_correct (m : Machine) {P p retAddr : Word} (hP : P.toNat % 2 = 0)
    (hc : CodeIn m.mem P lowest12Code) (hs : CodeIn m.mem (P + 0xFFFFE0D8) selectI64Code)
    (hpc : m.pc = P) (ha0 : reg m a0 = p) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hal : p.toNat % 4 = 0) (hσ : (m.mem (p + 0x30)).toNat ≤ 1)
    (hS : Sep (reg m sp + 0xFFFFFFFF) 1 (P + 0xFFFFE0D8) selectI64Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ q, q.val ∉ [6, 10, 11, 12, 13, 14, 15] → reg m' q = reg m q) ∧
      (reg m' a0).toNat + 2 ^ 32 * (reg m' a1).toNat = lowestVal (m.mem (p + 0x30)).toNat (accV m.mem p 2) ∧
      ∀ x, x ≠ reg m sp + 0xFFFFFFFF → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := s0.lwE hc lw12_at_0 (off' := 2) (by decide)
    (by rw [ha0]; exact fr_al' hal (by decide)) (v := memLoad32 m.mem (p + 4)) (by rw [ha0])
  have k1 := u1.oldReg s0.zero
  obtain ⟨n2, d2, u2⟩ := u1.self.lwE hc lw12_at_2 (off' := 4) (by decide)
    (by rw [k1 _ (by decide), ha0, add_lit_zero]; exact hal) (v := memLoad32 m.mem p)
    (by rw [k1 _ (by decide), ha0, add_lit_zero])
  have k2 := u2.oldReg u1.self.zero
  obtain ⟨n3, d3, u3⟩ := u2.self.lbu hc lw12_at_4 (off' := 8) (by decide)
  have k3 := u3.oldReg u2.self.zero
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc lw12_at_8 (off' := 0xA) (by decide)
  have k4 := u4.oldReg u3.self.zero
  obtain ⟨n5, d5, u5⟩ := u4.self.alu hc lw12_at_a (off' := 0xE) (by decide)
  have k5 := u5.oldReg u4.self.zero
  obtain ⟨n6, d6, u6⟩ := u5.self.alu hc lw12_at_e (off' := 0x12) (by decide)
  have k6 := u6.oldReg u5.self.zero
  obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hc lw12_at_12 (off' := 0x14) (by decide)
  have k7 := u7.oldReg u6.self.zero
  obtain ⟨n8, d8, u8⟩ := u7.self.alu hc lw12_at_14 (off' := 0x18) (by decide)
  have k8 := u8.oldReg u7.self.zero
  obtain ⟨n9, d9, u9⟩ := u8.self.alu hc lw12_at_18 (off' := 0x1A) (by decide)
  have k9 := u9.oldReg u8.self.zero
  obtain ⟨n10, d10, u10⟩ := u9.self.auipc hc lw12_at_1a (off' := 0x1E) (by decide)
  have k10 := u10.oldReg u9.self.zero
  obtain ⟨n11, d11, pc11, mem11, regs11⟩ := u10.self.jalr hc lw12_at_1e
  have keep : ∀ q : Fin 32, q.val ∉ [6, 10, 11, 12, 13, 14] → reg n11 q = reg m q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [6, 10, 11, 12, 13, 14] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [regs11, k10 q (nq 6 (by decide)), k9 q (nq a4 (by decide)), k8 q (nq a4 (by decide)),
      k7 q (nq a2 (by decide)), k6 q (nq a4 (by decide)), k5 q (nq a3 (by decide)), k4 q (nq a2 (by decide)),
      k3 q (nq a0 (by decide)), k2 q (nq a1 (by decide)), k1 q (nq a2 (by decide))]
  have r2 : ∀ q : Fin 32, q.val ∉ [6, 10, 12, 13, 14] → reg n11 q = reg n2 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [6, 10, 12, 13, 14] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [regs11, k10 q (nq 6 (by decide)), k9 q (nq a4 (by decide)), k8 q (nq a4 (by decide)),
      k7 q (nq a2 (by decide)), k6 q (nq a4 (by decide)), k5 q (nq a3 (by decide)), k4 q (nq a2 (by decide)),
      k3 q (nq a0 (by decide))]
  have lo11 : reg n11 a1 = memLoad32 m.mem p := by rw [r2 _ (by decide), u2.newReg (by decide)]
  have sg11 : reg n11 a0 = (m.mem (p + 0x30)).zeroExtend 32 := by
    rw [regs11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide),
      k5 _ (by decide), k4 _ (by decide), u3.newReg (by decide)]
    show (m.mem (reg n2 a0 + 0x30)).zeroExtend 32 = _
    rw [k2 _ (by decide), k1 _ (by decide), ha0]
  have hi11 : reg n11 a2 = (memLoad32 m.mem (p + 4) <<< (1 % 32)) >>> (1 % 32) := by
    rw [regs11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), u7.newReg (by decide)]
    show reg n6 a2 >>> ((1 : Word).toNat % 32) = _
    rw [k6 _ (by decide), k5 _ (by decide), u4.newReg (by decide)]
    show (reg n3 a2 <<< ((1 : Word).toNat % 32)) >>> ((1 : Word).toNat % 32) = _
    rw [k3 _ (by decide), k2 _ (by decide), u1.newReg (by decide)]; rfl
  have nl11 : reg n11 a3 = 0 - memLoad32 m.mem p := by
    rw [regs11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide),
      u5.newReg (by decide)]
    show reg n4 x0 - reg n4 a1 = _
    rw [u4.self.zero, k4 _ (by decide), k3 _ (by decide), u2.newReg (by decide)]
  have a2_6 : reg n6 a2 = memLoad32 m.mem (p + 4) <<< (1 % 32) := by
    rw [k6 _ (by decide), k5 _ (by decide), u4.newReg (by decide)]
    show reg n3 a2 <<< ((1 : Word).toNat % 32) = _
    rw [k3 _ (by decide), k2 _ (by decide), u1.newReg (by decide)]; rfl
  have a1_5 : reg n5 a1 = memLoad32 m.mem p := by
    rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), u2.newReg (by decide)]
  have a4_6 : reg n6 a4 = if (0 : Word).ult (memLoad32 m.mem p) then (1 : Word) else 0 := by
    rw [u6.newReg (by decide)]; show aluEval .sltu (reg n5 x0) (reg n5 a1) = _; rw [u5.self.zero, a1_5]; rfl
  have a2_7 : reg n7 a2 = (memLoad32 m.mem (p + 4) <<< (1 % 32)) >>> (1 % 32) := by
    rw [u7.newReg (by decide)]; show reg n6 a2 >>> ((1 : Word).toNat % 32) = _; rw [a2_6]; rfl
  have a4_8 : reg n8 a4 = (0 : Word) - (if (0 : Word).ult (memLoad32 m.mem p) then (1 : Word) else 0) := by
    rw [u8.newReg (by decide)]; show reg n7 x0 - reg n7 a4 = _; rw [u7.self.zero, k7 _ (by decide), a4_6]
  have nh11 : reg n11 a4 = ((0 : Word) - (if (0 : Word).ult (memLoad32 m.mem p) then (1 : Word) else 0)) -
      (memLoad32 m.mem (p + 4) <<< (1 % 32)) >>> (1 % 32) := by
    rw [regs11, k10 _ (by decide), u9.newReg (by decide)]
    show reg n8 a4 - reg n8 a2 = _
    rw [a4_8, k8 _ (by decide), a2_7]
  have pcS : n11.pc = P + 0xFFFFE0D8 := by
    rw [pc11, u10.newReg (by decide)]
    rw [show P + BitVec.ofNat 32 0x1A + 0xFFFFE000 + 0xBE = P + 0xFFFFE0D8 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P hP 0xFFFFE0D8 (by decide))
  obtain ⟨n12, c12, pc12, sp12, k12, z12, o12, fr12⟩ := selectI64_correct n11 (by rw [mem11]; exact hs) pcS
    (by rw [keep _ (by decide), hra]) hret (by rw [keep _ (by decide)]; exact hS)
  rw [sg11, zext_lo] at z12 o12
  rw [keep _ (by decide)] at fr12
  refine ⟨n12, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.cons d11 c12)))))))))), pc12, by rw [sp12, keep _ (by decide)], fun q hq => ?_, ?_,
    fun x hx => by rw [fr12 x hx, mem11]⟩
  · have nq : ∀ r : Fin 32, r.val ∈ [6, 10, 11, 12, 13, 14, 15] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k12 q (nq a0 (by decide)) (nq a1 (by decide)) (nq a3 (by decide)) (nq a4 (by decide)) (nq a5 (by decide)),
      keep q (fun h => hq (by revert h; revert q; decide))]
  · obtain ⟨A0, A1⟩ := lowest_arith (memLoad32 m.mem p) (memLoad32 m.mem (p + 4))
    unfold lowestVal
    rw [accV_two]
    rcases (by omega : (m.mem (p + 0x30)).toNat = 0 ∨ (m.mem (p + 0x30)).toNat = 1) with h | h
    · obtain ⟨e0, e1⟩ := z12 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      rw [e0, e1, lo11, hi11, ite_eq_right (by omega)]; exact A0
    · obtain ⟨e0, e1⟩ := o12 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      rw [e0, e1, nl11, nh11, ite_eq_left h]; exact A1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `SignedInt<8>::lowest`**, called with `a0` pointing at a
`SignedInt<8>` whose sign byte is 0 or 1: it returns in `a0` and `a1` the
words of `lowestVal` of the sign and the magnitude's low 64 bits. It changes
only `a0` through `a5` and `t1`, and writes only the byte below `sp`. -/
theorem lowest8_correct (m : Machine) {P p retAddr : Word} (hP : P.toNat % 2 = 0)
    (hc : CodeIn m.mem P lowest8Code) (hs : CodeIn m.mem (P + 0x22) selectI64Code)
    (hpc : m.pc = P) (ha0 : reg m a0 = p) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hal : p.toNat % 4 = 0) (hσ : (m.mem (p + 0x20)).toNat ≤ 1)
    (hS : Sep (reg m sp + 0xFFFFFFFF) 1 (P + 0x22) selectI64Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ q, q.val ∉ [6, 10, 11, 12, 13, 14, 15] → reg m' q = reg m q) ∧
      (reg m' a0).toNat + 2 ^ 32 * (reg m' a1).toNat = lowestVal (m.mem (p + 0x20)).toNat (accV m.mem p 2) ∧
      ∀ x, x ≠ reg m sp + 0xFFFFFFFF → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := s0.lwE hc lw8_at_0 (off' := 2) (by decide)
    (by rw [ha0]; exact fr_al' hal (by decide)) (v := memLoad32 m.mem (p + 4)) (by rw [ha0])
  have k1 := u1.oldReg s0.zero
  obtain ⟨n2, d2, u2⟩ := u1.self.lwE hc lw8_at_2 (off' := 4) (by decide)
    (by rw [k1 _ (by decide), ha0, add_lit_zero]; exact hal) (v := memLoad32 m.mem p)
    (by rw [k1 _ (by decide), ha0, add_lit_zero])
  have k2 := u2.oldReg u1.self.zero
  obtain ⟨n3, d3, u3⟩ := u2.self.lbu hc lw8_at_4 (off' := 8) (by decide)
  have k3 := u3.oldReg u2.self.zero
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc lw8_at_8 (off' := 0xA) (by decide)
  have k4 := u4.oldReg u3.self.zero
  obtain ⟨n5, d5, u5⟩ := u4.self.alu hc lw8_at_a (off' := 0xE) (by decide)
  have k5 := u5.oldReg u4.self.zero
  obtain ⟨n6, d6, u6⟩ := u5.self.alu hc lw8_at_e (off' := 0x12) (by decide)
  have k6 := u6.oldReg u5.self.zero
  obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hc lw8_at_12 (off' := 0x14) (by decide)
  have k7 := u7.oldReg u6.self.zero
  obtain ⟨n8, d8, u8⟩ := u7.self.alu hc lw8_at_14 (off' := 0x18) (by decide)
  have k8 := u8.oldReg u7.self.zero
  obtain ⟨n9, d9, u9⟩ := u8.self.alu hc lw8_at_18 (off' := 0x1A) (by decide)
  have k9 := u9.oldReg u8.self.zero
  obtain ⟨n10, d10, u10⟩ := u9.self.auipc hc lw8_at_1a (off' := 0x1E) (by decide)
  have k10 := u10.oldReg u9.self.zero
  obtain ⟨n11, d11, pc11, mem11, regs11⟩ := u10.self.jalr hc lw8_at_1e
  have keep : ∀ q : Fin 32, q.val ∉ [6, 10, 11, 12, 13, 14] → reg n11 q = reg m q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [6, 10, 11, 12, 13, 14] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [regs11, k10 q (nq 6 (by decide)), k9 q (nq a4 (by decide)), k8 q (nq a4 (by decide)),
      k7 q (nq a2 (by decide)), k6 q (nq a4 (by decide)), k5 q (nq a3 (by decide)), k4 q (nq a2 (by decide)),
      k3 q (nq a0 (by decide)), k2 q (nq a1 (by decide)), k1 q (nq a2 (by decide))]
  have r2 : ∀ q : Fin 32, q.val ∉ [6, 10, 12, 13, 14] → reg n11 q = reg n2 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [6, 10, 12, 13, 14] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [regs11, k10 q (nq 6 (by decide)), k9 q (nq a4 (by decide)), k8 q (nq a4 (by decide)),
      k7 q (nq a2 (by decide)), k6 q (nq a4 (by decide)), k5 q (nq a3 (by decide)), k4 q (nq a2 (by decide)),
      k3 q (nq a0 (by decide))]
  have lo11 : reg n11 a1 = memLoad32 m.mem p := by rw [r2 _ (by decide), u2.newReg (by decide)]
  have sg11 : reg n11 a0 = (m.mem (p + 0x20)).zeroExtend 32 := by
    rw [regs11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide),
      k5 _ (by decide), k4 _ (by decide), u3.newReg (by decide)]
    show (m.mem (reg n2 a0 + 0x20)).zeroExtend 32 = _
    rw [k2 _ (by decide), k1 _ (by decide), ha0]
  have hi11 : reg n11 a2 = (memLoad32 m.mem (p + 4) <<< (1 % 32)) >>> (1 % 32) := by
    rw [regs11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), u7.newReg (by decide)]
    show reg n6 a2 >>> ((1 : Word).toNat % 32) = _
    rw [k6 _ (by decide), k5 _ (by decide), u4.newReg (by decide)]
    show (reg n3 a2 <<< ((1 : Word).toNat % 32)) >>> ((1 : Word).toNat % 32) = _
    rw [k3 _ (by decide), k2 _ (by decide), u1.newReg (by decide)]; rfl
  have nl11 : reg n11 a3 = 0 - memLoad32 m.mem p := by
    rw [regs11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide),
      u5.newReg (by decide)]
    show reg n4 x0 - reg n4 a1 = _
    rw [u4.self.zero, k4 _ (by decide), k3 _ (by decide), u2.newReg (by decide)]
  have a2_6 : reg n6 a2 = memLoad32 m.mem (p + 4) <<< (1 % 32) := by
    rw [k6 _ (by decide), k5 _ (by decide), u4.newReg (by decide)]
    show reg n3 a2 <<< ((1 : Word).toNat % 32) = _
    rw [k3 _ (by decide), k2 _ (by decide), u1.newReg (by decide)]; rfl
  have a1_5 : reg n5 a1 = memLoad32 m.mem p := by
    rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), u2.newReg (by decide)]
  have a4_6 : reg n6 a4 = if (0 : Word).ult (memLoad32 m.mem p) then (1 : Word) else 0 := by
    rw [u6.newReg (by decide)]; show aluEval .sltu (reg n5 x0) (reg n5 a1) = _; rw [u5.self.zero, a1_5]; rfl
  have a2_7 : reg n7 a2 = (memLoad32 m.mem (p + 4) <<< (1 % 32)) >>> (1 % 32) := by
    rw [u7.newReg (by decide)]; show reg n6 a2 >>> ((1 : Word).toNat % 32) = _; rw [a2_6]; rfl
  have a4_8 : reg n8 a4 = (0 : Word) - (if (0 : Word).ult (memLoad32 m.mem p) then (1 : Word) else 0) := by
    rw [u8.newReg (by decide)]; show reg n7 x0 - reg n7 a4 = _; rw [u7.self.zero, k7 _ (by decide), a4_6]
  have nh11 : reg n11 a4 = ((0 : Word) - (if (0 : Word).ult (memLoad32 m.mem p) then (1 : Word) else 0)) -
      (memLoad32 m.mem (p + 4) <<< (1 % 32)) >>> (1 % 32) := by
    rw [regs11, k10 _ (by decide), u9.newReg (by decide)]
    show reg n8 a4 - reg n8 a2 = _
    rw [a4_8, k8 _ (by decide), a2_7]
  have pcS : n11.pc = P + 0x22 := by
    rw [pc11, u10.newReg (by decide)]
    rw [show P + BitVec.ofNat 32 0x1A + 0x0 + 0x8 = P + 0x22 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P hP 0x22 (by decide))
  obtain ⟨n12, c12, pc12, sp12, k12, z12, o12, fr12⟩ := selectI64_correct n11 (by rw [mem11]; exact hs) pcS
    (by rw [keep _ (by decide), hra]) hret (by rw [keep _ (by decide)]; exact hS)
  rw [sg11, zext_lo] at z12 o12
  rw [keep _ (by decide)] at fr12
  refine ⟨n12, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.cons d11 c12)))))))))), pc12, by rw [sp12, keep _ (by decide)], fun q hq => ?_, ?_,
    fun x hx => by rw [fr12 x hx, mem11]⟩
  · have nq : ∀ r : Fin 32, r.val ∈ [6, 10, 11, 12, 13, 14, 15] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k12 q (nq a0 (by decide)) (nq a1 (by decide)) (nq a3 (by decide)) (nq a4 (by decide)) (nq a5 (by decide)),
      keep q (fun h => hq (by revert h; revert q; decide))]
  · obtain ⟨A0, A1⟩ := lowest_arith (memLoad32 m.mem p) (memLoad32 m.mem (p + 4))
    unfold lowestVal
    rw [accV_two]
    rcases (by omega : (m.mem (p + 0x20)).toNat = 0 ∨ (m.mem (p + 0x20)).toNat = 1) with h | h
    · obtain ⟨e0, e1⟩ := z12 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      rw [e0, e1, lo11, hi11, ite_eq_right (by omega)]; exact A0
    · obtain ⟨e0, e1⟩ := o12 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      rw [e0, e1, nl11, nh11, ite_eq_left h]; exact A1

end C3.RV32
