import C3BootProofs.Proofs.Leaves

/-!
# `__ashldi3`, as compiled

compiler-rt's 64-bit left shift: the value in `a0` (low word) and `a1`
(high word) shifted left by `a2` bits, modulo `2^64`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem ashl_at_0 : fetchRel ashldi3Code 0x0 = some (.aluImm .and a3 a2 0x20, 4) := by decide
theorem ashl_at_4 : fetchRel ashldi3Code 0x4 = some (.branch .bne a3 x0 0x18, 2) := by decide
theorem ashl_at_6 : fetchRel ashldi3Code 0x6 = some (.branch .beq a2 x0 0x14, 2) := by decide
theorem ashl_at_1a : fetchRel ashldi3Code 0x1A = some (.jalr x0 ra 0x0, 2) := by decide
theorem ashl_at_1c : fetchRel ashldi3Code 0x1C = some (.alu .sll a1 a0 a2, 4) := by decide
theorem ashl_at_20 : fetchRel ashldi3Code 0x20 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem ashl_at_22 : fetchRel ashldi3Code 0x22 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem sll_mod (x r : Word) : (aluEval .sll x r).toNat = x.toNat * 2 ^ (r.toNat % 32) % 2 ^ 32 := by
  show (x <<< (r.toNat % 32)).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- A 64-bit value shifted left by `s` from 0 to 32 bits, word by word. -/
theorem lsl64 {lo hi s : Nat} (hs : s ≤ 32) (hlo : lo < 2 ^ 32) :
    (lo + 2 ^ 32 * hi) * 2 ^ s % 2 ^ 64 = lo * 2 ^ s % 2 ^ 32 + 2 ^ 32 * (hi * 2 ^ s % 2 ^ 32 + lo / 2 ^ (32 - s)) := by
  obtain ⟨P, hP⟩ : ∃ P, 2 ^ s = P := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ (32 - s) = Q := ⟨_, rfl⟩
  have hPQ : P * Q = 2 ^ 32 := by rw [← hP, ← hQ, ← Nat.pow_add]; congr 1; omega
  have hP0 : 0 < P := by rw [← hP]; exact Nat.two_pow_pos s
  have hQ0 : 0 < Q := by rw [← hQ]; exact Nat.two_pow_pos _
  have split : ∀ x, x * P = x % Q * P + 2 ^ 32 * (x / Q) := fun x => by
    conv => lhs; rw [← Nat.mod_add_div x Q]
    rw [← hPQ]; simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  have h1 : lo % Q * P < 2 ^ 32 := by
    rw [← hPQ, Nat.mul_comm P Q]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hQ0) hP0
  have h2 : hi % Q * P + P ≤ 2 ^ 32 := by
    rw [← hPQ, Nat.mul_comm P Q, ← Nat.succ_mul]; exact Nat.mul_le_mul_right P (Nat.mod_lt _ hQ0)
  have h3 : lo / Q < P := shDivLt (by rw [Nat.mul_comm, hPQ]; exact hlo)
  rw [hP, hQ, Nat.add_mul, Nat.mul_assoc, split lo, split hi]
  generalize lo % Q * P = x at *
  generalize hi % Q * P = z at *
  generalize lo / Q = y at *
  generalize hi / Q = w at *
  omega

theorem lsl64_hi {lo hi t : Nat} : (lo + 2 ^ 32 * hi) * 2 ^ (32 + t) % 2 ^ 64 = 2 ^ 32 * (lo * 2 ^ t % 2 ^ 32) := by
  rw [Nat.pow_add, show (lo + 2 ^ 32 * hi) * (2 ^ 32 * 2 ^ t) = 2 ^ 32 * (lo * 2 ^ t + 2 ^ 32 * (hi * 2 ^ t)) by
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm],
    show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mul_mod_mul_left, Nat.add_mul_mod_self_left]

/-- The instructions from 0x8 to 0x1A: the shift by 1 to 31 bits. -/
def ashlBody : List BInstr :=
  [.alu .sub a3 x0 a2, .alu .srl a3 a0 a3, .alu .sll a0 a0 a2, .alu .sll a1 a1 a2, .alu .or a1 a1 a3]

section
set_option maxRecDepth 20000
theorem ashlBody_end : blockEnd ashldi3Code 0x8 ashlBody = some 0x1A := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`__ashldi3`** shifts the 64-bit value in `a0` (low word) and `a1` (high
word) left by `s` bits, for `s` from 0 to 63, modulo `2^64`. -/
theorem ashldi3_correct (m : Machine) {base retAddr lo hi : Word} {s : Nat} (hc : CodeIn m.mem base ashldi3Code)
    (hpc : m.pc = base) (ha0 : reg m a0 = lo) (ha1 : reg m a1 = hi) (ha2 : reg m a2 = BitVec.ofNat 32 s)
    (hs : s < 64) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (reg m' a0).toNat + 2 ^ 32 * (reg m' a1).toNat = (lo.toNat + 2 ^ 32 * hi.toNat) * 2 ^ s % 2 ^ 64 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → reg m' q = reg m q) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hsn : (BitVec.ofNat 32 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  have hlo := lo.isLt
  have hhi := hi.isLt
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc ashl_at_0 (off' := 4) (by decide)
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
  by_cases h32 : 32 ≤ s
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x1C ashl_at_4 (by decide) (by
      rw [u1.regs, e3, ite_eq_left h32, show reg n1 x0 = 0 from u1.self.zero]; decide)
    obtain ⟨n3, d3, u3⟩ := u2.alu hc ashl_at_1c (off' := 0x20) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hc ashl_at_20 (off' := 0x22) (by decide)
    obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.jalr hc ashl_at_22
    refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), ?_, ?_, fun q h0' h1' h3' => ?_, ?_⟩
    · rw [pc5]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.regs, k1 ra (by decide), add_lit_zero, hra, hret]
    · rw [regs5, regs5]; simp +decide only [upd_app, ↓reduceIte]
      simp only [e0, e2]
      rw [sll_mod, hsn, show (aluEval .add 0 0 : Word).toNat = 0 from rfl, Nat.zero_add]
      conv => rhs; rw [show s = 32 + (s - 32) by omega]
      rw [lsl64_hi, show s % 32 = s - 32 by omega]
    · rw [regs5]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h0', h1', ite_false]; rw [u1.regs, k1 q h3']
    · exact mem5
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x6 ashl_at_4 (by decide) (by
      rw [u1.regs, e3, ite_eq_right h32, show reg n1 x0 = 0 from u1.self.zero]; decide)
    by_cases hs0 : s = 0
    · subst hs0
      obtain ⟨n3, d3, u3⟩ := u2.taken hc 0x1A ashl_at_6 (by decide) (by
        rw [u1.regs, k1 a2 (by decide), ha2, show reg n1 x0 = 0 from u1.self.zero]; decide)
      obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc ashl_at_1a
      refine ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), ?_, ?_, fun q h0' h1' h3' => ?_, ?_⟩
      · rw [pc4, u1.regs, k1 ra (by decide), add_lit_zero, hra, hret]
      · rw [regs4, regs4]; simp only [e0, e1]; rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
      · rw [regs4]; exact r1 q h3'
      · exact mem4
    · obtain ⟨n3, d3, u3⟩ := u2.notTaken hc 0x8 ashl_at_6 (by decide) (by
        rw [u1.regs, k1 a2 (by decide), ha2, show reg n1 x0 = 0 from u1.self.zero]
        simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h; rw [hsn] at this; exact hs0 this)
      obtain ⟨n4, c4, u4⟩ := St.block ashlBody u3 hc ashlBody_end (by simp [BlockOk, BInstr.ok, ashlBody])
      simp only [runBlock, BInstr.run, ashlBody] at u4
      obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.self.jalr hc ashl_at_1a
      refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (c4.trans (.single d5)))), ?_, ?_, fun q h0' h1' h3' => ?_, ?_⟩
      · rw [pc5, u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r1 ra (by decide), add_lit_zero, hra, hret]
      · rw [regs5, regs5, u4.regs, u4.regs]; simp +decide only [upd_app, ↓reduceIte]
        simp only [e0, e1, e2, show reg n1 x0 = 0 from u1.self.zero]
        have hneg : (aluEval .sub 0 (BitVec.ofNat 32 s)).toNat % 32 = 32 - s := by
          show (0 - BitVec.ofNat 32 s).toNat % 32 = 32 - s
          rw [BitVec.toNat_sub, hsn]
          show (2 ^ 32 - s + 0) % 2 ^ 32 % 32 = 32 - s; omega
        have hlow : (aluEval .srl lo (aluEval .sub 0 (BitVec.ofNat 32 s))).toNat < 2 ^ s := by
          rw [srl_mod, hneg]
          exact shDivLt (by rw [← Nat.pow_add, show 32 - s + s = 32 by omega]; exact hlo)
        have hhigh : (aluEval .sll hi (BitVec.ofNat 32 s)).toNat % 2 ^ s = 0 := by
          rw [sll_nat _ _ (by rw [hsn]; omega), hsn,
            Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : s ≤ 32)), Nat.mul_mod_left]
        rw [or_nat _ _ hhigh hlow, srl_mod, hneg, sll_nat _ _ (by rw [hsn]; omega),
          sll_nat _ _ (by rw [hsn]; omega), hsn, lsl64 (by omega) hlo]
      · rw [regs5, u4.regs]
        by_cases h0 : q.val = 0
        · have : q = 0 := Fin.ext h0
          subst this; simp [upd]; exact hz.symm
        simp only [upd_app, h0, h0', h1', h3', ite_false]; exact r1 q h3'
      · rw [mem5]

end C3.RV32
