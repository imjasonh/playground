import C3BootProofs.Proofs.Ed25519VerifyWrap4
import C3BootProofs.Proofs.DerTlv

/-!
# `ed25519_verify`, offsets 0x158E to 0x16CC: the multiplication's setup

The function negates `A` into `F + 0x540`, writes the NAF digits of `k` and
`s` to `F + 0x7F0` and `F + 0x8F0`, finds the highest index where either is
nonzero, builds the NAF tables of `-A` and the basepoint at `F + 0x9F0` and
`F + 0xEF0`, and sets `r` at `F + 0x13F0` to the identity.
-/

namespace C3.RV32

open C3.Image

/-- The highest index below `k` where digit `a` or `b` is nonzero, and `0`
when there is none. -/
def nafTop (a b : Nat → BitVec 8) : Nat → Nat
  | 0 => 0
  | k + 1 => if (a k != 0 || b k != 0) = true then k else nafTop a b k

theorem nafTop_congr {a b a' b' : Nat → BitVec 8} :
    ∀ k, (∀ j, j < k → a j = a' j ∧ b j = b' j) → nafTop a b k = nafTop a' b' k
  | 0, _ => rfl
  | k + 1, h => by
    show (if (a k != 0 || b k != 0) = true then k else nafTop a b k) =
      (if (a' k != 0 || b' k != 0) = true then k else nafTop a' b' k)
    rw [(h k (by omega)).1, (h k (by omega)).2, nafTop_congr k fun j hj => h j (by omega)]

theorem nafTop_le (a b : Nat → BitVec 8) : ∀ k, nafTop a b k ≤ k - 1
  | 0 => Nat.zero_le _
  | k + 1 => by
    unfold nafTop
    split
    · omega
    · have := nafTop_le a b k; omega

theorem add_m1 (x : Word) : aluEval .add x 0xFFFFFFFF = x - 1 := by
  apply BitVec.eq_of_toNat_eq
  show (x + 0xFFFFFFFF).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_sub, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl,
    show (1 : Word).toNat = 1 from rfl]
  have := x.isLt; omega

theorem ze_bne : ∀ b : BitVec 8, branchTaken .bne (b.zeroExtend 32) 0 = (b != 0) := by decide
theorem ze_beq : ∀ b : BitVec 8, branchTaken .beq (b.zeroExtend 32) 0 = (b == 0) := by decide

theorem fwB {M M' : Word → BitVec 8} {F : Word} {c e : Nat}
    (h : ∀ j, j < 40 → M' (F + BitVec.ofNat 32 (c + j)) = M (F + BitVec.ofNat 32 (e + j))) :
    feW M' (F + BitVec.ofNat 32 c) = feW M (F + BitVec.ofNat 32 e) :=
  feW_eq2 fun i hi => vk_ld2 fun j hj => by
    simp only [add_ofNat_assoc, Nat.add_assoc]
    exact h _ (by omega)

theorem nafScalar_congr {M M' : Word → BitVec 8} {s : Word}
    (h : ∀ i, i < 32 → M' (s + BitVec.ofNat 32 i) = M (s + BitVec.ofNat 32 i)) : nafScalar M' s = nafScalar M s := by
  have e : ∀ o : Word, o.toNat + 4 ≤ 32 → memLoad32 M' (s + o) = memLoad32 M (s + o) := fun o ho =>
    vk_ld2 fun j hj => by
      have := h (o.toNat + j) (by omega)
      rwa [← add_ofNat_assoc, ofNat_toNat_self] at this
  have e0 : memLoad32 M' s = memLoad32 M s := vk_ld2 fun j hj => h j (by omega)
  unfold nafScalar
  rw [e0, e 4 (by decide), e 8 (by decide), e 12 (by decide), e 16 (by decide), e 20 (by decide), e 24 (by decide),
    e 28 (by decide)]

theorem ptB {M M' : Word → BitVec 8} {F : Word} {c e : Nat}
    (h : ∀ j, j < 160 → M' (F + BitVec.ofNat 32 (c + j)) = M (F + BitVec.ofNat 32 (e + j))) :
    ptAt M' (F + BitVec.ofNat 32 c) = ptAt M (F + BitVec.ofNat 32 e) := by
  unfold ptAt
  simp only [add_ofNat_assoc]
  refine Prod.ext (fwB fun j hj => h j (by omega)) (Prod.ext (fwB fun j hj => ?_) (Prod.ext (fwB fun j hj => ?_)
    (fwB fun j hj => ?_)))
  · rw [Nat.add_assoc, Nat.add_assoc]; exact h _ (by omega)
  · rw [Nat.add_assoc, Nat.add_assoc]; exact h _ (by omega)
  · rw [Nat.add_assoc, Nat.add_assoc]; exact h _ (by omega)

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

theorem fwRo (C : EvCtx M0 F pk sig msg len) {Mx : Word → BitVec 8} {nx : Machine} {ox : Nat}
    (Dx : EvSt M0 Ms F r0 Mx nx ox) {a : Nat} (h1 : 0x3FCC4000 ≤ a) (h2 : a + 40 ≤ 0x3FCC5400) :
    feW Mx (BitVec.ofNat 32 a) = feW M0 (BitVec.ofNat 32 a) :=
  feW_eq2 fun i hi => vk_ld2 fun j hj => by
    simp only [add_ofNat_assoc]; exact Dx.roM C (a := a) (k := 40) h1 h2 _ (by omega)

theorem ptRo (C : EvCtx M0 F pk sig msg len) {Mx : Word → BitVec 8} {nx : Machine} {ox : Nat}
    (Dx : EvSt M0 Ms F r0 Mx nx ox) {a : Nat} (h1 : 0x3FCC4000 ≤ a) (h2 : a + 160 ≤ 0x3FCC5400) :
    ptAt Mx (BitVec.ofNat 32 a) = ptAt M0 (BitVec.ofNat 32 a) := by
  unfold ptAt
  simp only [BitVec.ofNat_add_ofNat]
  rw [fwRo C Dx h1 (by omega), fwRo C Dx (a := a + 40) (by omega) (by omega), fwRo C Dx (a := a + 80) (by omega) (by omega),
    fwRo C Dx (a := a + 120) (by omega) (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- The search at offset 0x1612, from candidate `k - 1` down: `s1` becomes
`nafTop` of the digits at `F + 0x7F0` and `F + 0x8F0`. -/
theorem ev_srch (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} :
    ∀ k {n : Machine}, k ≤ 256 → EvSt M0 Ms F r0 M n 0x1612 →
      reg n a3 = BitVec.ofNat 32 k - 1 → reg n a0 = BitVec.ofNat 32 k → reg n a2 = BitVec.ofNat 32 (min k 255) →
      reg n a1 = 0xFFFFFFFF → reg n 18 = F + BitVec.ofNat 32 0x7F0 → reg n 8 = F + BitVec.ofNat 32 0x8F0 →
      ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 M n' 0x1638 ∧
        reg n' 9 = BitVec.ofNat 32 (nafTop (fun j => M (F + BitVec.ofNat 32 (0x7F0 + j)))
          (fun j => M (F + BitVec.ofNat 32 (0x8F0 + j))) k) ∧
        ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → reg n' q = reg n q
  | 0, n, _, D, h13, h10, h12, h11, h18, h8 => by
    obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1614) [.alu .add (9 : Fin 32) x0 a2] (bEnd1 ev_at_1612 rfl)
      ⟨trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have e3 : reg n1 a3 = reg n a3 := by rw [hr1, evb_reg a3 D.st.zero (by decide)]
    have e1 : reg n1 a1 = reg n a1 := by rw [hr1, evb_reg a1 D.st.zero (by decide)]
    obtain ⟨n2, d2, u2⟩ := D1.st.taken (D1.code C) 0x1638 ev_at_1614 rfl (by rw [e3, e1, h13, h11]; rfl)
    refine ⟨n2, c1.trans (Steps.single d2), D1.jmp u2, ?_, fun q hq h9 => ?_⟩
    · rw [u2.regs, hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.st.zero, h12]
      exact BitVec.zero_add _
    · rw [u2.regs, hr1, evb_reg q D.st.zero (by revert h9; revert hq; revert q; decide)]
  | k + 1, n, hk, D, h13, h10, h12, h11, h18, h8 => by
    have z0 := D.st.zero
    have hk3 : BitVec.ofNat 32 (k + 1) - 1 = BitVec.ofNat 32 k := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega
    obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1614) [.alu .add (9 : Fin 32) x0 a2] (bEnd1 ev_at_1612 rfl)
      ⟨trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have k1 : ∀ q : Fin 32, q ≠ 9 → reg n1 q = reg n q := fun q hq => by
      rw [hr1]; simp only [runBlock, BInstr.run]; exact upd_ne' hq z0
    obtain ⟨n2, d2, u2⟩ := D1.st.notTaken (D1.code C) 0x1618 ev_at_1614 rfl (by
      rw [k1 a3 (by decide), k1 a1 (by decide), h13, h11, hk3]
      show (BitVec.ofNat 32 k == 0xFFFFFFFF) = false
      exact beq_eq_false_iff_ne.mpr fun e => by
        have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact absurd this (by show k ≠ 4294967295; omega))
    have D2 := D1.jmp u2
    have eA : F + BitVec.ofNat 32 0x7F0 + BitVec.ofNat 32 k = F + BitVec.ofNat 32 (0x7F0 + k) := add_ofNat_assoc F _ _
    have eB : F + BitVec.ofNat 32 0x8F0 + BitVec.ofNat 32 k = F + BitVec.ofNat 32 (0x8F0 + k) := add_ofNat_assoc F _ _
    obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x1622)
      [.alu .add a2 x0 a3, .alu .add a3 a3 (18 : Fin 32), .lbu a3 a3 0, .aluImm .add a0 a0 0xFFFFFFFF]
      (blockEnd_cons' ev_at_1618 rfl (blockEnd_cons' ev_at_161a rfl (blockEnd_cons' ev_at_161c rfl
        (blockEnd_cons' ev_at_1620 rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have r2 : ∀ q : Fin 32, q ≠ 9 → reg n2 q = reg n q := fun q hq => by rw [u2.regs, k1 q hq]
    have va3 : reg n3 a3 = (M (F + BitVec.ofNat 32 (0x7F0 + k))).zeroExtend 32 := by
      rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
      rw [r2 a3 (by decide), r2 18 (by decide), h13, h18, hk3, add_lit_zero]
      show (M (BitVec.ofNat 32 k + (F + BitVec.ofNat 32 0x7F0))).zeroExtend 32 = _
      rw [BitVec.add_comm, eA]
    have k3 : ∀ q : Fin 32, q ≠ a0 → q ≠ a2 → q ≠ a3 → reg n3 q = reg n2 q := fun q h0 h2 h3 => by
      rw [hr3, evb_reg q D2.st.zero (by revert h3 h2 h0; revert q; decide)]
    have va0 : reg n3 a0 = BitVec.ofNat 32 k := by
      rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [r2 a0 (by decide), h10]
      apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
      omega
    have va2 : reg n3 a2 = BitVec.ofNat 32 k := by
      rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [r2 a3 (by decide), h13, hk3]; (try rw [D2.st.zero]); exact BitVec.zero_add _
    have nt : nafTop (fun j => M (F + BitVec.ofNat 32 (0x7F0 + j))) (fun j => M (F + BitVec.ofNat 32 (0x8F0 + j))) (k + 1) =
        if (M (F + BitVec.ofNat 32 (0x7F0 + k)) != 0 || M (F + BitVec.ofNat 32 (0x8F0 + k)) != 0) = true then k
        else nafTop (fun j => M (F + BitVec.ofNat 32 (0x7F0 + j))) (fun j => M (F + BitVec.ofNat 32 (0x8F0 + j))) k := rfl
    by_cases ha : M (F + BitVec.ofNat 32 (0x7F0 + k)) = 0
    · obtain ⟨n4, d4, u4⟩ := D3.st.notTaken (D3.code C) 0x1624 ev_at_1622 rfl (by
        rw [va3, D3.st.zero, ze_bne, ha]; rfl)
      have D4 := D3.jmp u4
      obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x1632)
        [.alu .add a3 (8 : Fin 32) a2, .lbu a4 a3 0, .aluImm .add a3 a2 0xFFFFFFFF, .alu .add (9 : Fin 32) x0 a2]
        (blockEnd_cons' ev_at_1624 rfl (blockEnd_cons' ev_at_1628 rfl (blockEnd_cons' ev_at_162c rfl
          (blockEnd_cons' ev_at_1630 rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
        (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
      have r4 : ∀ q : Fin 32, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ 9 → reg n4 q = reg n q := fun q h0 h2 h3 h9 => by
        rw [u4.regs, k3 q h0 h2 h3, r2 q h9]
      have va4 : reg n5 a4 = (M (F + BitVec.ofNat 32 (0x8F0 + k))).zeroExtend 32 := by
        rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [r4 8 (by decide) (by decide) (by decide) (by decide), h8, u4.regs, va2, add_lit_zero]
        show (M (F + BitVec.ofNat 32 0x8F0 + BitVec.ofNat 32 k)).zeroExtend 32 = _
        rw [eB]
      have v9 : reg n5 9 = BitVec.ofNat 32 k := by
        rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u4.regs, va2]; (try rw [D4.st.zero]); exact BitVec.zero_add _
      have k5 : ∀ q : Fin 32, q ≠ a3 → q ≠ a4 → q ≠ 9 → reg n5 q = reg n4 q := fun q h3 h4 h9 => by
        rw [hr5, evb_reg q D4.st.zero (by revert h9 h4 h3; revert q; decide)]
      by_cases hb : M (F + BitVec.ofNat 32 (0x8F0 + k)) = 0
      · obtain ⟨n6, d6, u6⟩ := D5.st.taken (D5.code C) 0x1612 ev_at_1632 rfl (by rw [va4, D5.st.zero, ze_beq, hb]; rfl)
        have D6 := D5.jmp u6
        obtain ⟨n7, c7, D7, v97, k7⟩ := ev_srch C k (by omega) D6
          (by rw [u6.regs, hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u4.regs, va2, add_m1])
          (by rw [u6.regs, k5 a0 (by decide) (by decide) (by decide), u4.regs, va0])
          (by rw [u6.regs, k5 a2 (by decide) (by decide) (by decide), u4.regs, va2, Nat.min_eq_left (by omega)])
          (by rw [u6.regs, k5 a1 (by decide) (by decide) (by decide), r4 a1 (by decide) (by decide) (by decide) (by decide), h11])
          (by rw [u6.regs, k5 18 (by decide) (by decide) (by decide), r4 18 (by decide) (by decide) (by decide) (by decide), h18])
          (by rw [u6.regs, k5 8 (by decide) (by decide) (by decide), r4 8 (by decide) (by decide) (by decide) (by decide), h8])
        refine ⟨n7, c1.trans ((Steps.single d2).trans (c3.trans ((Steps.single d4).trans (c5.trans
          ((Steps.single d6).trans c7))))), D7, ?_, fun q hq h9 => ?_⟩
        · rw [v97, nt, ha, hb]; rfl
        · rw [k7 q hq h9, u6.regs, k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) h9,
            r4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) h9]
      · obtain ⟨n6, d6, u6⟩ := D5.st.notTaken (D5.code C) 0x1634 ev_at_1632 rfl (by
          rw [va4, D5.st.zero, ze_beq]; exact beq_eq_false_iff_ne.mpr hb)
        have D6 := D5.jmp u6
        obtain ⟨n7, d7, u7⟩ := D6.st.jump (D6.code C) ev_at_1634 (off' := 0x1638) (by decide) (by rw [D6.st.pc]; decide)
        refine ⟨n7, c1.trans ((Steps.single d2).trans (c3.trans ((Steps.single d4).trans (c5.trans
          ((Steps.single d6).trans (Steps.single d7)))))), D6.jmp u7, ?_, fun q hq h9 => ?_⟩
        · rw [u7.regs, u6.regs, v9, nt, ha]
          rw [ite_eq_left (by simp only [ha, bne_self_eq_false, Bool.false_or]; exact bne_iff_ne.mpr hb)]
        · rw [u7.regs, u6.regs, k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) h9,
            r4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) h9]
    · obtain ⟨n4, d4, u4⟩ := D3.st.taken (D3.code C) 0x1636 ev_at_1622 rfl (by
        rw [va3, D3.st.zero, ze_bne]; exact bne_iff_ne.mpr ha)
      have D4 := D3.jmp u4
      obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x1638) [.alu .add (9 : Fin 32) x0 a0] (bEnd1 ev_at_1636 rfl)
        ⟨trivial, trivial⟩ rfl
        (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
      refine ⟨n5, c1.trans ((Steps.single d2).trans (c3.trans ((Steps.single d4).trans c5))), D5, ?_, fun q hq h9 => ?_⟩
      · rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u4.regs]; rw [va0, nt]; (try rw [D3.st.zero])
        rw [ite_eq_left (by simp only [bne_iff_ne.mpr ha, Bool.true_or])]; exact BitVec.zero_add _
      · rw [hr5, evb_reg q D4.st.zero (by revert h9; revert q; decide), u4.regs,
          k3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r2 q h9]
  
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x158E: `-A` from the point at `F + 0x600` to `F + 0x540`, and
the NAF digits of the scalars at `F + 0x520` (`k`) and `F + 0x6C0` (`s`) to
`F + 0x7F0` and `F + 0x8F0`. -/
theorem ev_p6a (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x158E) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1604 ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → reg n' q = reg n q) ∧ reg n' 8 = F + BitVec.ofNat 32 0x8F0 ∧
      ptAt M' (F + BitVec.ofNat 32 0x540) = (negL (feW M (F + BitVec.ofNat 32 0x600)), feW M (F + BitVec.ofNat 32 0x628),
        feW M (F + BitVec.ofNat 32 0x650), negL (feW M (F + BitVec.ofNat 32 0x678))) ∧
      (∀ k, k < 256 → M' (F + BitVec.ofNat 32 (0x7F0 + k)) = nafSpec (nafScalar M (F + BitVec.ofNat 32 0x520)) k) ∧
      (∀ k, k < 256 → M' (F + BitVec.ofNat 32 (0x8F0 + k)) = nafSpec (nafScalar M (F + BitVec.ofNat 32 0x6C0)) k) ∧
      ∀ c, c < 0x16A0 → (c < 0x540 ∨ (0x5E0 ≤ c ∧ c < 0x7F0) ∨ 0x9F0 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1596) [.aluImm .add a0 sp 0x540, .aluImm .add a1 sp 0x600]
    (blockEnd_cons' ev_at_158e rfl (blockEnd_cons' ev_at_1592 rfl rfl)) ⟨trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, c2, D2, k2, w2, f2⟩ := D1.feNeg C (d := 0x540) (e := 0x600) ev_at_1596 ev_at_159a (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x15AA)
    [.aluImm .add a1 sp 0x628, .aluImm .add a0 sp 0x568, .aluImm .add a2 x0 0x28]
    (blockEnd_cons' ev_at_159e rfl (blockEnd_cons' ev_at_15a2 rfl (blockEnd_cons' ev_at_15a6 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n4, c4, D4, k4, fz4⟩ := D3.memcpy C (d := 0x568) (s := F + BitVec.ofNat 32 0x628) (N := 0x28)
    ev_at_15aa ev_at_15ae (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x15BE)
    [.aluImm .add a1 sp 0x650, .aluImm .add a0 sp 0x590, .aluImm .add a2 x0 0x28]
    (blockEnd_cons' ev_at_15b2 rfl (blockEnd_cons' ev_at_15b6 rfl (blockEnd_cons' ev_at_15ba rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6, fz6⟩ := D5.memcpy C (d := 0x590) (s := F + BitVec.ofNat 32 0x650) (N := 0x28)
    ev_at_15be ev_at_15c2 (by decide) (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x15CE) [.aluImm .add a1 sp 0x678, .aluImm .add a0 sp 0x5B8]
    (blockEnd_cons' ev_at_15c6 rfl (blockEnd_cons' ev_at_15ca rfl rfl)) ⟨trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n8, c8, D8, k8, w8, f8⟩ := D7.feNeg C (d := 0x5B8) (e := 0x678) ev_at_15ce ev_at_15d2 (by decide) (by decide)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; rfl)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; rfl)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0x15E2)
    [.aluImm .add (9 : Fin 32) sp 0x6C0, .aluImm .add a0 sp 0x7F0, .aluImm .add a1 sp 0x520]
    (blockEnd_cons' ev_at_15d6 rfl (blockEnd_cons' ev_at_15da rfl (blockEnd_cons' ev_at_15de rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n10, c10, D10, k10, w10, f10⟩ := D9.naf C (d := 0x7F0) (e := 0x520) ev_at_15e2 ev_at_15e6 (by decide) (by decide)
    (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; rfl)
    (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; rfl)
    (by decide) (by decide) (by decide)
  obtain ⟨n11, c11, D11, hr11⟩ := D10.block C (off' := 0x15FC)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0xF1, .alu .add a1 x0 (9 : Fin 32), .aluImm .add (8 : Fin 32) sp 0x7FF,
      .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xF1]
    (blockEnd_cons' ev_at_15ea rfl (blockEnd_cons' ev_at_15ee rfl (blockEnd_cons' ev_at_15f2 rfl
      (blockEnd_cons' ev_at_15f4 rfl (blockEnd_cons' ev_at_15f8 rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v9 : reg n10 9 = F + BitVec.ofNat 32 0x6C0 := by
    rw [k10 9 (by decide), hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; rfl
  obtain ⟨n12, c12, D12, k12, w12, f12⟩ := D11.naf C (d := 0x8F0) (e := 0x6C0) ev_at_15fc ev_at_1600 (by decide)
    (by decide)
    (by rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D10.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v9]; exact BitVec.zero_add _)
    (by decide) (by decide) (by decide)
  -- the frames
  have g12 : ∀ c, c < 0x16A0 → (c < 0x8F0 ∨ 0x9F0 ≤ c) → n12.mem (F + BitVec.ofNat 32 c) = n10.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => f12 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))
  have g10 : ∀ c, c < 0x16A0 → (c < 0x7F0 ∨ 0x8F0 ≤ c) → n10.mem (F + BitVec.ofNat 32 c) = n8.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => f10 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))
  have g8 : ∀ c, c < 0x16A0 → (c < 0x5B8 ∨ 0x5E0 ≤ c) → n8.mem (F + BitVec.ofNat 32 c) = n6.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => f8 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))
  have g6 : ∀ c, c < 0x16A0 → (c < 0x590 ∨ 0x5B8 ≤ c) → n6.mem (F + BitVec.ofNat 32 c) = n4.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => cp_out C fz6 (by decide) hc hh
  have g4 : ∀ c, c < 0x16A0 → (c < 0x568 ∨ 0x590 ≤ c) → n4.mem (F + BitVec.ofNat 32 c) = n2.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => cp_out C fz4 (by decide) hc hh
  have g2 : ∀ c, c < 0x16A0 → (c < 0x540 ∨ 0x568 ≤ c) → n2.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
    fun c hc hh => f2 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))
  -- the frame from n8 on, outside the NAFs
  have h8n : ∀ c, c < 0x16A0 → (c < 0x7F0 ∨ 0x9F0 ≤ c) → n12.mem (F + BitVec.ofNat 32 c) = n8.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by rcases hh with hh | hh <;> rw [g12 c hc (by omega), g10 c hc (by omega)]
  refine ⟨n12, n12.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (c11.trans c12)))))))))), D12, fun q hq h8 h9 => ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_,
    fun c hc hh => ?_⟩
  · rw [k12 q hq, hr11, evb_reg q D10.st.zero (by revert h8; revert hq; revert q; decide), k10 q hq, hr9,
      evb_reg q D8.st.zero (by revert h9; revert hq; revert q; decide), k8 q hq, hr7,
      evb_reg q D6.st.zero (by revert hq; revert q; decide), k6 q hq, hr5, evb_reg q D4.st.zero (by revert hq; revert q; decide),
      k4 q hq, hr3, evb_reg q D2.st.zero (by revert hq; revert q; decide), k2 q hq, hr1,
      evb_reg q D.st.zero (by revert hq; revert q; decide)]
  · rw [k12 8 (by decide), hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D10.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  · unfold ptAt
    rw [add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · show feW n12.mem (F + BitVec.ofNat 32 0x540) = negL (feW M (F + BitVec.ofNat 32 0x600))
      rw [← w2]; exact fwB (c := 0x540) (e := 0x540) fun j hj => by
        rw [h8n _ (by omega) (Or.inl (by omega)), g8 _ (by omega) (Or.inl (by omega)), g6 _ (by omega) (Or.inl (by omega)),
          g4 _ (by omega) (Or.inl (by omega))]
    · show feW n12.mem (F + BitVec.ofNat 32 0x568) = feW M (F + BitVec.ofNat 32 0x628)
      refine (fwB (c := 0x568) (e := 0x628) fun j hj => ?_)
      rw [h8n _ (by omega) (Or.inl (by omega)), g8 _ (by omega) (Or.inl (by omega)), g6 _ (by omega) (Or.inl (by omega)),
        cp_at C fz4 (by decide) hj, add_ofNat_assoc]
      exact g2 _ (by omega) (Or.inr (by omega)) |>.trans rfl
    · show feW n12.mem (F + BitVec.ofNat 32 0x590) = feW M (F + BitVec.ofNat 32 0x650)
      refine (fwB (c := 0x590) (e := 0x650) fun j hj => ?_)
      rw [h8n _ (by omega) (Or.inl (by omega)), g8 _ (by omega) (Or.inl (by omega)),
        cp_at C fz6 (by decide) hj, add_ofNat_assoc, g4 _ (by omega) (Or.inr (by omega)), g2 _ (by omega) (Or.inr (by omega))]
    · show feW n12.mem (F + BitVec.ofNat 32 0x5B8) = negL (feW M (F + BitVec.ofNat 32 0x678))
      have e6 : feW n6.mem (F + BitVec.ofNat 32 0x678) = feW M (F + BitVec.ofNat 32 0x678) :=
        fwB (c := 0x678) (e := 0x678) fun j hj => by
          rw [g6 _ (by omega) (Or.inr (by omega)), g4 _ (by omega) (Or.inr (by omega)), g2 _ (by omega) (Or.inr (by omega))]
      rw [← e6, ← w8]
      exact fwB (c := 0x5B8) (e := 0x5B8) fun j hj => h8n _ (by omega) (Or.inl (by omega))
  · rw [g12 _ (by omega) (Or.inl (by omega)), ← add_ofNat_assoc, w10 k hk]
    congr 1; exact nafScalar_congr fun i hi => by
      rw [add_ofNat_assoc, g8 _ (by omega) (Or.inl (by omega)), g6 _ (by omega) (Or.inl (by omega)),
        g4 _ (by omega) (Or.inl (by omega)), g2 _ (by omega) (Or.inl (by omega))]
  · rw [← add_ofNat_assoc, w12 k hk]
    congr 1; exact nafScalar_congr fun i hi => by
      rw [add_ofNat_assoc, g10 _ (by omega) (Or.inl (by omega)), g8 _ (by omega) (Or.inr (by omega)),
        g6 _ (by omega) (Or.inr (by omega)), g4 _ (by omega) (Or.inr (by omega)), g2 _ (by omega) (Or.inr (by omega))]
  · rcases hh with hh | hh | hh
    · rw [h8n c hc (Or.inl (by omega)), g8 c hc (by omega), g6 c hc (by omega), g4 c hc (by omega), g2 c hc (by omega)]
    · rw [h8n c hc (Or.inl (by omega)), g8 c hc (by omega), g6 c hc (by omega), g4 c hc (by omega), g2 c hc (by omega)]
    · rw [h8n c hc (Or.inr hh), g8 c hc (by omega), g6 c hc (by omega), g4 c hc (by omega), g2 c hc (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x1638: the NAF tables of the point at `F + 0x540` and of the
basepoint to `F + 0x9F0` and `F + 0xEF0`, the identity `(0, 1, 1)` to
`F + 0x13F0`, and the loop's registers for the top index `i` in `s1`. -/
theorem ev_p6c (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1638)
    {i : Nat} (hi : i < 256) (h9 : reg n 9 = BitVec.ofNat 32 i) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x16CC ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 18, 19, 20, 21, 22] → reg n' q = reg n q) ∧
      reg n' 9 = F + BitVec.ofNat 32 (0x7F0 + i) ∧ reg n' 21 = F + BitVec.ofNat 32 (0x8F0 + i) ∧
      reg n' 20 = 0 - BitVec.ofNat 32 i ∧ reg n' 22 = 1 ∧
      reg n' 18 = F + BitVec.ofNat 32 0x1418 ∧ reg n' 19 = F + BitVec.ofNat 32 0x1440 ∧
      (∀ j, j < 8 → ptAt M' (F + BitVec.ofNat 32 (0x9F0 + 160 * j)) =
        nafTab (ptAt M (F + BitVec.ofNat 32 0x540)) (feW M0 apnD) j) ∧
      (∀ j, j < 8 → ptAt M' (F + BitVec.ofNat 32 (0xEF0 + 160 * j)) =
        nafTab (ptAt M0 (BitVec.ofNat 32 0x3FCC4A54)) (feW M0 apnD) j) ∧
      (∀ j, j < 40 → M' (F + BitVec.ofNat 32 (0x13F0 + j)) = 0) ∧
      feW M' (F + BitVec.ofNat 32 0x1418) = feW M0 (BitVec.ofNat 32 0x3FCC4948) ∧
      feW M' (F + BitVec.ofNat 32 0x1440) = feW M0 (BitVec.ofNat 32 0x3FCC4948) ∧
      ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0x1468 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1644)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x1F1, .aluImm .add a1 sp 0x540]
    (blockEnd_cons' (off' := 0x163C) ev_at_1638 rfl (blockEnd_cons' (off' := 0x1640) ev_at_163c rfl
      (blockEnd_cons' (off' := 0x1644) ev_at_1640 rfl rfl))) ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, c2, D2, k2, w2, f2⟩ := D1.nafTbl C (d := 0x9F0) (A := F + BitVec.ofNat 32 0x540) ev_at_1644 ev_at_1648
    (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl)
    (by decide) (by decide) (C.al (by decide)) (by rw [C.fN (by decide)]; have := C.hhi; omega) (C.zF (by decide)).symm
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x165C)
    [.lui a1 0x3FCC5000, .aluImm .add a1 a1 0xFFFFFA54, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x6F1]
    (blockEnd_cons' (off' := 0x1650) ev_at_164c rfl (blockEnd_cons' (off' := 0x1654) ev_at_1650 rfl
      (blockEnd_cons' (off' := 0x1658) ev_at_1654 rfl (blockEnd_cons' (off' := 0x165C) ev_at_1658 rfl rfl))))
    ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n4, c4, D4, k4, w4, f4⟩ := D3.nafTbl C (d := 0xEF0) (A := BitVec.ofNat 32 0x3FCC4A54) ev_at_165c ev_at_1660
    (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D2.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (by decide) (by decide) (by decide) (C.zS (C.ro (by decide) (by decide)))
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x1672)
    [.lui a0 0x1000, .aluImm .add a0 a0 0x3F0, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x28, .aluImm .add a1 x0 0x0]
    (blockEnd_cons' (off' := 0x1666) ev_at_1664 rfl (blockEnd_cons' (off' := 0x166A) ev_at_1666 rfl
      (blockEnd_cons' (off' := 0x166C) ev_at_166a rfl (blockEnd_cons' (off' := 0x1670) ev_at_166c rfl
      (blockEnd_cons' (off' := 0x1672) ev_at_1670 rfl rfl))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6⟩ := D5.memset C (d := 0x13F0) (b := 0) (N := 0x28) ev_at_1672 ev_at_1676 (by decide) (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D4.st.zero]); try rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D4.st.zero]); try rfl)
    (by decide)
  obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x1694)
    [.lui a0 0x1000, .aluImm .add a0 a0 0x418, .alu .add (18 : Fin 32) sp a0, .lui (8 : Fin 32) 0x3FCC5000,
      .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFF948, .aluImm .add a2 x0 0x28, .alu .add a0 x0 (18 : Fin 32),
      .alu .add a1 x0 (8 : Fin 32)]
    (blockEnd_cons' (off' := 0x167C) ev_at_167a rfl (blockEnd_cons' (off' := 0x1680) ev_at_167c rfl
      (blockEnd_cons' (off' := 0x1684) ev_at_1680 rfl (blockEnd_cons' (off' := 0x1688) ev_at_1684 rfl
      (blockEnd_cons' (off' := 0x168C) ev_at_1688 rfl (blockEnd_cons' (off' := 0x1690) ev_at_168c rfl
      (blockEnd_cons' (off' := 0x1692) ev_at_1690 rfl (blockEnd_cons' (off' := 0x1694) ev_at_1692 rfl rfl))))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n8, c8, D8, k8, fz8⟩ := D7.memcpy C (d := 0x1418) (s := BitVec.ofNat 32 0x3FCC4948) (N := 0x28)
    ev_at_1694 ev_at_1698 (by decide) (by decide)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; exact (BitVec.zero_add _).trans rfl)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zS (C.ro (by decide) (by decide))) (C.fS (C.ro (by decide) (by decide)) (by decide)) (by decide)
  obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0x16AE)
    [.lui a0 0x1000, .aluImm .add a0 a0 0x440, .alu .add (19 : Fin 32) sp a0, .aluImm .add a2 x0 0x28,
      .alu .add a0 x0 (19 : Fin 32), .alu .add a1 x0 (8 : Fin 32)]
    (blockEnd_cons' (off' := 0x169E) ev_at_169c rfl (blockEnd_cons' (off' := 0x16A2) ev_at_169e rfl
      (blockEnd_cons' (off' := 0x16A6) ev_at_16a2 rfl (blockEnd_cons' (off' := 0x16AA) ev_at_16a6 rfl
      (blockEnd_cons' (off' := 0x16AC) ev_at_16aa rfl (blockEnd_cons' (off' := 0x16AE) ev_at_16ac rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v8 : reg n8 8 = BitVec.ofNat 32 0x3FCC4948 := by
    rw [k8 8 (by decide), hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
  obtain ⟨n10, c10, D10, k10, fz10⟩ := D9.memcpy C (d := 0x1440) (s := BitVec.ofNat 32 0x3FCC4948) (N := 0x28)
    ev_at_16ae ev_at_16b2 (by decide) (by decide)
    (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact (BitVec.zero_add _).trans rfl)
    (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v8]; exact BitVec.zero_add _)
    (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zS (C.ro (by decide) (by decide))) (C.fS (C.ro (by decide) (by decide)) (by decide)) (by decide)
  obtain ⟨n11, c11, D11, hr11⟩ := D10.block C (off' := 0x16CC)
    [.alu .sub (20 : Fin 32) x0 (9 : Fin 32), .aluImm .add (21 : Fin 32) sp 0x7FF, .aluImm .add (21 : Fin 32) (21 : Fin 32) 0xF1,
      .aluImm .add a0 sp 0x7F0, .alu .add (21 : Fin 32) (21 : Fin 32) (9 : Fin 32), .alu .add (9 : Fin 32) (9 : Fin 32) a0,
      .aluImm .add (22 : Fin 32) x0 0x1]
    (blockEnd_cons' (off' := 0x16BA) ev_at_16b6 rfl (blockEnd_cons' (off' := 0x16BE) ev_at_16ba rfl
      (blockEnd_cons' (off' := 0x16C2) ev_at_16be rfl (blockEnd_cons' (off' := 0x16C6) ev_at_16c2 rfl
      (blockEnd_cons' (off' := 0x16C8) ev_at_16c6 rfl (blockEnd_cons' (off' := 0x16CA) ev_at_16c8 rfl
      (blockEnd_cons' (off' := 0x16CC) ev_at_16ca rfl rfl)))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  -- registers
  have back : ∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 18, 19, 20, 21, 22] → q ≠ 9 → reg n10 q = reg n q :=
    fun q hq hn h9' => by
      rw [k10 q hq, hr9, evb_reg q D8.st.zero (by revert hn; revert q; decide), k8 q hq, hr7,
        evb_reg q D6.st.zero (by revert hn; revert q; decide), k6 q hq, hr5, evb_reg q D4.st.zero (by revert hq; revert q; decide),
        k4 q hq, hr3, evb_reg q D2.st.zero (by revert hq; revert q; decide), k2 q hq, hr1,
        evb_reg q D.st.zero (by revert hq; revert q; decide)]
  have r9 : reg n10 9 = BitVec.ofNat 32 i := by
    rw [k10 9 (by decide), hr9, evb_reg 9 D8.st.zero (by decide), k8 9 (by decide), hr7, evb_reg 9 D6.st.zero (by decide),
      k6 9 (by decide), hr5, evb_reg 9 D4.st.zero (by decide), k4 9 (by decide), hr3, evb_reg 9 D2.st.zero (by decide),
      k2 9 (by decide), hr1, evb_reg 9 D.st.zero (by decide), h9]
  -- memory
  have g10 : ∀ c, c < 0x16A0 → (c < 0x1440 ∨ 0x1468 ≤ c) → n10.mem (F + BitVec.ofNat 32 c) = n8.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => cp_out C fz10 (by decide) hc hh
  have g86 : ∀ c, c < 0x16A0 → (c < 0x13F0 ∨ 0x1440 ≤ c) → n8.mem (F + BitVec.ofNat 32 c) = n4.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by
      rcases hh with hh | hh <;>
        rw [cp_out C fz8 (by decide) hc (by omega), fb_out C (by decide) hc (by omega)]
  have g4 : ∀ c, c < 0x16A0 → (c < 0xEF0 ∨ 0x13F0 ≤ c) → n4.mem (F + BitVec.ofNat 32 c) = n2.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => f4 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))
  have g2 : ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xEF0 ≤ c) → n2.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
    fun c hc hh => f2 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))
  have g64 : ∀ c, c < 0x16A0 → c < 0x13F0 → n10.mem (F + BitVec.ofNat 32 c) = n4.mem (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by rw [g10 c hc (Or.inl (by omega)), g86 c hc (Or.inl hh)]
  refine ⟨n11, n10.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans c11))))))))), D11, fun q hq hn => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_,
    fun c hc hh => ?_⟩
  · rw [hr11, evb_reg q D10.st.zero (by revert hn; revert q; decide), back q hq (by revert hn; revert q; decide)
      (by revert hn; revert q; decide)]
  · rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [r9, D10.hsp]
    show BitVec.ofNat 32 i + (F + BitVec.ofNat 32 0x7F0) = _
    rw [BitVec.add_comm, add_ofNat_assoc]
  · rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [r9, D10.hsp]
    show F + BitVec.ofNat 32 0x7FF + BitVec.ofNat 32 0xF1 + BitVec.ofNat 32 i = _
    rw [add_ofNat_assoc, add_ofNat_assoc]; exact congrArg (fun x => F + BitVec.ofNat 32 x) (by omega)
  · rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [r9, D10.st.zero]; rfl
  · rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D10.st.zero]); try rfl
  · rw [hr11, evb_reg 18 D10.st.zero (by decide), k10 18 (by decide), hr9, evb_reg 18 D8.st.zero (by decide),
      k8 18 (by decide), hr7]
    simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; try rfl
  · rw [hr11, evb_reg 19 D10.st.zero (by decide), k10 19 (by decide), hr9]
    simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; try rfl
  · rw [ptB (M := n2.mem) (c := 0x9F0 + 160 * j) (e := 0x9F0 + 160 * j) fun b hb => by
        rw [g64 _ (by omega) (by omega), g4 _ (by omega) (Or.inl (by omega))],
      ← add_ofNat_assoc, w2 j hj]
    congr 1; exact fwRo C D (a := 0x3FCC4A2C) (by decide) (by decide)
  · rw [ptB (M := n4.mem) (c := 0xEF0 + 160 * j) (e := 0xEF0 + 160 * j) fun b hb => g64 _ (by omega) (by omega),
      ← add_ofNat_assoc, w4 j hj, ptRo C D2 (by decide) (by decide)]
    congr 1; exact fwRo C D2 (a := 0x3FCC4A2C) (by decide) (by decide)
  · rw [g10 _ (by omega) (Or.inl (by omega)), cp_out C fz8 (by decide) (by omega) (Or.inl (by omega)), ← add_ofNat_assoc,
      fb_in hj (by decide)]; rfl
  · rw [feW_eq2 (M := n8.mem) (M' := n10.mem) (a := F + BitVec.ofNat 32 0x1418) (b := F + BitVec.ofNat 32 0x1418)
      fun i hi => vk_ld2 fun j hj => by
        simp only [add_ofNat_assoc]; exact g10 _ (by omega) (Or.inl (by omega))]
    rw [← fwRo C D7 (a := 0x3FCC4948) (by decide) (by decide)]
    exact feW_eq2 fun i hi => vk_ld2 fun j hj => by
      simp only [add_ofNat_assoc, Nat.add_assoc]; exact cp_at C fz8 (j := 4 * i + j) (by decide) (by omega)
  · rw [← fwRo C D9 (a := 0x3FCC4948) (by decide) (by decide)]
    exact feW_eq2 fun i hi => vk_ld2 fun j hj => by
      simp only [add_ofNat_assoc, Nat.add_assoc]; exact cp_at C fz10 (j := 4 * i + j) (by decide) (by omega)
  · rcases hh with hh | hh
    · rw [g10 c hc (Or.inl (by omega)), g86 c hc (Or.inl (by omega)), g4 c hc (Or.inl (by omega)), g2 c hc (Or.inl hh)]
    · rw [g10 c hc (Or.inr hh), g86 c hc (Or.inr (by omega)), g4 c hc (Or.inr (by omega)), g2 c hc (Or.inr (by omega))]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The setup of the double-base multiplication**, from offset 0x158E. -/
theorem ev_p6 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x158E)
    (h18 : reg n 18 = F + BitVec.ofNat 32 0x7F0) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x16CC ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 18, 19, 20, 21, 22] → reg n' q = reg n q) ∧
      reg n' 9 = F + BitVec.ofNat 32 (0x7F0 + nafTop (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x520)))
        (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x6C0))) 256) ∧
      reg n' 21 = F + BitVec.ofNat 32 (0x8F0 + nafTop (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x520)))
        (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x6C0))) 256) ∧
      reg n' 20 = 0 - BitVec.ofNat 32 (nafTop (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x520)))
        (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x6C0))) 256) ∧ reg n' 22 = 1 ∧
      reg n' 18 = F + BitVec.ofNat 32 0x1418 ∧ reg n' 19 = F + BitVec.ofNat 32 0x1440 ∧
      (∀ k, k < 256 → M' (F + BitVec.ofNat 32 (0x7F0 + k)) = nafSpec (nafScalar M (F + BitVec.ofNat 32 0x520)) k) ∧
      (∀ k, k < 256 → M' (F + BitVec.ofNat 32 (0x8F0 + k)) = nafSpec (nafScalar M (F + BitVec.ofNat 32 0x6C0)) k) ∧
      (∀ j, j < 8 → ptAt M' (F + BitVec.ofNat 32 (0x9F0 + 160 * j)) =
        nafTab (negL (feW M (F + BitVec.ofNat 32 0x600)), feW M (F + BitVec.ofNat 32 0x628),
          feW M (F + BitVec.ofNat 32 0x650), negL (feW M (F + BitVec.ofNat 32 0x678))) (feW M0 apnD) j) ∧
      (∀ j, j < 8 → ptAt M' (F + BitVec.ofNat 32 (0xEF0 + 160 * j)) =
        nafTab (ptAt M0 (BitVec.ofNat 32 0x3FCC4A54)) (feW M0 apnD) j) ∧
      (∀ j, j < 40 → M' (F + BitVec.ofNat 32 (0x13F0 + j)) = 0) ∧
      feW M' (F + BitVec.ofNat 32 0x1418) = feW M0 (BitVec.ofNat 32 0x3FCC4948) ∧
      feW M' (F + BitVec.ofNat 32 0x1440) = feW M0 (BitVec.ofNat 32 0x3FCC4948) ∧
      ∀ c, c < 0x16A0 → (c < 0x540 ∨ (0x5E0 ≤ c ∧ c < 0x7F0) ∨ 0x1468 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, M1, c1, D1, k1, v8, hA, ha, hb, fr1⟩ := ev_p6a C D
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C (off' := 0x1612)
    [.aluImm .add a0 x0 0x100, .aluImm .add a3 x0 0xFF, .aluImm .add a1 x0 0xFFFFFFFF, .aluImm .add a2 x0 0xFF]
    (blockEnd_cons' ev_at_1604 rfl (blockEnd_cons' ev_at_1608 rfl (blockEnd_cons' ev_at_160c rfl
      (blockEnd_cons' ev_at_160e rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n3, c3, D3, v9, k3⟩ := ev_srch C 256 (by decide) D2
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, D1.st.zero]; try rfl)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, D1.st.zero]; try rfl)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, D1.st.zero]; try rfl)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, D1.st.zero]; try rfl)
    (by rw [hr2, evb_reg 18 D1.st.zero (by decide), k1 18 (by decide) (by decide) (by decide), h18])
    (by rw [hr2, evb_reg 8 D1.st.zero (by decide), v8])
  rw [nafTop_congr 256 fun j hj => ⟨ha j hj, hb j hj⟩] at v9
  have hi := nafTop_le (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x520))) (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x6C0))) 256
  obtain ⟨n4, M4, c4, D4, k4, r9, r21, r20, r22, r18, r19, tA, tB, z0, o1, o2, fr4⟩ := ev_p6c C D3 (by omega) v9
  have back : ∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 18, 19, 20, 21, 22] → reg n4 q = reg n q := fun q hq hn => by
    rw [k4 q hq hn, k3 q hq (by revert hn; revert q; decide), hr2, evb_reg q D1.st.zero (by revert hq; revert q; decide),
      k1 q hq (by revert hn; revert q; decide) (by revert hn; revert q; decide)]
  refine ⟨n4, M4, c1.trans (c2.trans (c3.trans c4)), D4, back, r9, r21, r20, r22, r18, r19, fun k hk => ?_, fun k hk => ?_,
    fun j hj => ?_, tB, z0, o1, o2, fun c hc hh => ?_⟩
  · rw [fr4 _ (by omega) (Or.inl (by omega)), ha k hk]
  · rw [fr4 _ (by omega) (Or.inl (by omega)), hb k hk]
  · rw [tA j hj, hA]
  · rcases hh with hh | hh | hh
    · rw [fr4 c hc (Or.inl (by omega)), fr1 c hc (Or.inl hh)]
    · rw [fr4 c hc (Or.inl (by omega)), fr1 c hc (Or.inr (Or.inl hh))]
    · rw [fr4 c hc (Or.inr hh), fr1 c hc (Or.inr (Or.inr (by omega)))]

end

end C3.RV32




