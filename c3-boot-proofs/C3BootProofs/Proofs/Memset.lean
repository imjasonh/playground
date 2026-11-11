import C3BootProofs.Proofs.ImageHelpers

/-! # `memset`, for word-aligned buffers -/

namespace C3.RV32

open C3.ImageV0

/-- Memory after storing the word `v` at each of the `k` words from `dst`. -/
def fillWords (M : Word → BitVec 8) (dst v : Word) : Nat → Word → BitVec 8
  | 0 => M
  | k + 1 => memStore32 (fillWords M dst v k) (dst + BitVec.ofNat 32 (4 * k)) v

theorem fillWords_outside {M : Word → BitVec 8} {dst v x : Word} :
    ∀ k, Sep dst (4 * k) x 1 → fillWords M dst v k x = M x
  | 0, _ => rfl
  | k + 1, h => by
    simp only [fillWords]
    rw [memStore32_get_sep (h.sub (c := 4 * k) (l := 4) (by omega)),
      fillWords_outside k (h.sub (c := 0) (l := 4 * k) (by omega) |> fun h' => by
        rwa [add_ofNat_zero] at h')]

/-- The word `memset` stores: the low byte of `b` in each of its bytes. -/
def fillWord (b : Word) : Word := aluEval .mul (aluEval .and b 0xFF) (0x1010000 + 0x101)

section

set_option maxRecDepth 20000

theorem mz_at_0 : fetchRel memsetCode 0x0 = some (.aluImm .add a3 x0 0x10, 2) := by decide
theorem mz_at_2 : fetchRel memsetCode 0x2 = some (.branch .bltu a2 a3 0x50, 4) := by decide
theorem mz_at_6 : fetchRel memsetCode 0x6 = some (.alu .sub a3 x0 a0, 4) := by decide
theorem mz_at_a : fetchRel memsetCode 0xA = some (.aluImm .and a3 a3 0x3, 2) := by decide
theorem mz_at_c : fetchRel memsetCode 0xC = some (.alu .add a4 a0 a3, 4) := by decide
theorem mz_at_10 : fetchRel memsetCode 0x10 = some (.branch .bgeu a0 a4 0x12, 4) := by decide
theorem mz_at_22 : fetchRel memsetCode 0x22 = some (.alu .sub a2 a2 a3, 2) := by decide
theorem mz_at_24 : fetchRel memsetCode 0x24 = some (.aluImm .and a3 a2 0xFFFFFFFC, 4) := by decide
theorem mz_at_28 : fetchRel memsetCode 0x28 = some (.alu .add a3 a3 a4, 2) := by decide
theorem mz_at_2a : fetchRel memsetCode 0x2A = some (.branch .bgeu a4 a3 0x1C, 4) := by decide
theorem mz_at_2e : fetchRel memsetCode 0x2E = some (.lui a5 0x1010000, 4) := by decide
theorem mz_at_32 : fetchRel memsetCode 0x32 = some (.aluImm .and a6 a1 0xFF, 4) := by decide
theorem mz_at_36 : fetchRel memsetCode 0x36 = some (.aluImm .add a5 a5 0x101, 4) := by decide
theorem mz_at_3a : fetchRel memsetCode 0x3A = some (.alu .mul a5 a6 a5, 4) := by decide
theorem mz_at_3e : fetchRel memsetCode 0x3E = some (.store .sw a4 a5 0x0, 2) := by decide
theorem mz_at_40 : fetchRel memsetCode 0x40 = some (.aluImm .add a4 a4 0x4, 2) := by decide
theorem mz_at_42 : fetchRel memsetCode 0x42 = some (.branch .bltu a4 a3 0xFFFFFFFC, 4) := by decide
theorem mz_at_46 : fetchRel memsetCode 0x46 = some (.aluImm .and a2 a2 0x3, 2) := by decide
theorem mz_at_48 : fetchRel memsetCode 0x48 = some (.alu .add a4 a3 a2, 4) := by decide
theorem mz_at_4c : fetchRel memsetCode 0x4C = some (.branch .bltu a3 a4 0x10, 4) := by decide
theorem mz_at_50 : fetchRel memsetCode 0x50 = some (.jal x0 0x16, 2) := by decide
theorem mz_at_66 : fetchRel memsetCode 0x66 = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- The word loop at 0x3E: with `j` words stored and `k` left, it stores the
rest and leaves the loop at 0x46. -/
theorem memset_loop {B dst v : Word} {M0 : Word → BitVec 8} {w : Nat}
    (hc : ∀ j, j ≤ w → CodeIn (fillWords M0 dst v j) B memsetCode)
    (hdst : dst.toNat % 4 = 0) (hwrap : dst.toNat + 4 * w < 2 ^ 32) :
    ∀ k j (n : Machine), j + k = w → 0 < k →
      St (fillWords M0 dst v j) B n 0x3E (reg n) → reg n a4 = dst + BitVec.ofNat 32 (4 * j) →
      reg n a5 = v → reg n a3 = dst + BitVec.ofNat 32 (4 * w) →
      ∃ n', Steps n n' ∧ St (fillWords M0 dst v w) B n' 0x46 (reg n') ∧
        reg n' a4 = dst + BitVec.ofNat 32 (4 * w) ∧ (∀ r, r ≠ a4 → reg n' r = reg n r) := by
  intro k
  induction k with
  | zero => intro _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n hjk _ s h4 h5 h3
    have hcj := hc j (by omega)
    obtain ⟨n1, d1, u1⟩ := s.sw hcj mz_at_3e (off' := 0x40) (by decide)
      (by rw [h4, add_lit_zero]; exact aligned_add hdst (k := 4 * j) (by omega))
    rw [h4, h5, add_lit_zero] at u1
    have hst : memStore32 (fillWords M0 dst v j) (dst + BitVec.ofNat 32 (4 * j)) v =
        fillWords M0 dst v (j + 1) := rfl
    rw [hst] at u1
    have hcj1 := hc (j + 1) (by omega)
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hcj1 mz_at_40 (off' := 0x42) (by decide)
    have e4 : dst + BitVec.ofNat 32 (4 * j) + 4 = dst + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2
    have ult : (dst + BitVec.ofNat 32 (4 * (j + 1))).ult (dst + BitVec.ofNat 32 (4 * w)) = decide (j + 1 < w) := by
      simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat]
      apply decide_eq_decide.mpr
      rw [Nat.mod_eq_of_lt (a := 4 * (j + 1)) (by omega), Nat.mod_eq_of_lt (a := 4 * w) (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      constructor <;> intro h <;> omega
    have r2 : ∀ r, reg n2 r = upd (reg n) a4 (dst + BitVec.ofNat 32 (4 * (j + 1))) r := fun r => by
      rw [u2.regs]; simp +decide only [upd, aluEval, h4, e4]
    have u2' : St (fillWords M0 dst v (j + 1)) B n2 0x42 (reg n2) := u2.self
    by_cases hlt : j + 1 < w
    · obtain ⟨n3, d3, u3⟩ := u2'.taken hcj1 0x3E mz_at_42 (by decide) (by
        rw [r2, r2]; simp +decide only [upd, ite_false, ite_true, branchTaken]
        rw [h3, ult]; simpa using hlt)
      obtain ⟨n4, c4, u4, h44, f4⟩ := ih (j + 1) n3 (by omega) (by omega) u3.self
        (by rw [u3.regs, r2]; simp +decide [upd]) (by rw [u3.regs, r2]; simp +decide [upd, h5])
        (by rw [u3.regs, r2]; simp +decide [upd, h3])
      refine ⟨n4, .cons d1 (.cons d2 (.cons d3 c4)), u4, h44, fun r q4 => ?_⟩
      rw [f4 r q4, u3.regs, r2]; simp [upd, q4]
      by_cases h0 : r = 0
      · subst h0; exact fun _ => s.zero.symm
      · simp [h0]
    · have hj : j + 1 = w := by omega
      obtain ⟨n3, d3, u3⟩ := u2'.notTaken hcj1 0x46 mz_at_42 (by decide) (by
        rw [r2, r2]; simp +decide only [upd, ite_false, ite_true, branchTaken]
        rw [h3, ult]; simpa using hlt)
      rw [hj] at u3
      refine ⟨n3, .cons d1 (.cons d2 (.single d3)), u3.self, ?_, fun r q4 => ?_⟩
      · rw [u3.regs, r2]; simp +decide [upd, hj]
      · rw [u3.regs, r2]; simp [upd, q4]
        by_cases h0 : r = 0
        · subst h0; exact fun _ => s.zero.symm
        · simp [h0]

/-- **The compiled `memset` is correct for word-aligned buffers.** Called with
`dst` 4-byte aligned and a length of `4 * w` bytes for `w` at least 4, it
stores `fillWord b` at each of the `w` words (`fillWords`), returns `dst` in
`a0`, and changes only `a2` through `a6` among the other registers. It uses
no stack. -/
theorem memset_aligned (m : Machine) (base retAddr dst b : Word) (w : Nat)
    (hcode : CodeAt m base memsetCode) (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = dst) (ha1 : reg m a1 = b) (ha2 : reg m a2 = BitVec.ofNat 32 (4 * w))
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hw : 4 ≤ w) (hwrap : dst.toNat + 4 * w < 2 ^ 32)
    (hmask : BitVec.ofNat 32 (4 * w) &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * w))
    (hdst : dst.toNat % 4 = 0) (hDC : Sep dst (4 * w) base memsetCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = fillWords m.mem dst (fillWord b) w ∧ reg m' a0 = dst ∧
      ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg m' r = reg m r := by
  have hcB : ∀ j, j ≤ w → CodeIn (fillWords m.mem dst (fillWord b) j) base memsetCode :=
    fun j hj i hi => by
      rw [fillWords_outside j ((hDC.subR (c := i) (l := 1) (by omega)).sub (c := 0) (l := 4 * j) (by omega)
        |> fun h' => by rwa [add_ofNat_zero] at h')]
      exact hcode i hi
  have hc0 := hcB 0 (by omega)
  have u0 : St (fillWords m.mem dst (fillWord b) 0) base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := u0.zero
  have sub0 : ∀ x : Word, x - 0 = x := fun x => BitVec.eq_of_toNat_eq (by simp)
  have z0 : (0 - dst) &&& 3 = 0 := and3_word (by
    rw [BitVec.toNat_sub, show (0 : Word).toNat = 0 from rfl]; omega)
  have w3 : BitVec.ofNat 32 (4 * w) &&& 3 = 0 := and3_word (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * w) (by omega)]; omega)
  obtain ⟨n1, d1, v1⟩ := u0.aluImm hc0 mz_at_0 (off' := 0x2) (by decide)
  have h16 : (BitVec.ofNat 32 (4 * w)).ult (0 + 0x10) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4 * w < 2 ^ 32 by omega)]
    apply decide_eq_false; show ¬ 4 * w < 16; omega
  obtain ⟨n2, d2, v2⟩ := v1.notTaken hc0 0x6 mz_at_2 (by decide) (by
    simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval, ha2, hz]
    exact h16)
  obtain ⟨n3, d3, v3⟩ := v2.alu hc0 mz_at_6 (off' := 0xA) (by decide)
  obtain ⟨n4, d4, v4⟩ := v3.aluImm hc0 mz_at_a (off' := 0xC) (by decide)
  obtain ⟨n5, d5, v5⟩ := v4.alu hc0 mz_at_c (off' := 0x10) (by decide)
  have va3 : aluEval .and (aluEval .sub 0 dst) 3 = 0 := z0
  obtain ⟨n6, d6, v6⟩ := v5.taken hc0 0x22 mz_at_10 (by decide) (by
    simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval, hz, ha0]
    rw [show (0 - dst) &&& 3 = 0 from z0, add_lit_zero]; simp [BitVec.ult])
  obtain ⟨n7, d7, v7⟩ := v6.alu hc0 mz_at_22 (off' := 0x24) (by decide)
  obtain ⟨n8, d8, v8⟩ := v7.aluImm hc0 mz_at_24 (off' := 0x28) (by decide)
  obtain ⟨n9, d9, v9⟩ := v8.alu hc0 mz_at_28 (off' := 0x2A) (by decide)
  have q9 : reg n9 a4 = dst ∧ reg n9 a3 = dst + BitVec.ofNat 32 (4 * w) ∧
      reg n9 a2 = BitVec.ofNat 32 (4 * w) ∧
      ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n9 r = reg m r := by
    have e : ∀ r, reg n9 r = _ := v9.regs
    refine ⟨?_, ?_, ?_, fun r q2 q3 q4 => ?_⟩
    · rw [e]; simp +decide only [upd, ite_false, ite_true, aluEval, ha0, hz]
      rw [show (0 - dst) &&& 3 = 0 from z0, add_lit_zero]
    · rw [e]; simp +decide only [upd, ite_false, ite_true, aluEval, ha0, ha2, hz]
      rw [show (0 - dst) &&& 3 = 0 from z0, add_lit_zero, sub0, hmask, BitVec.add_comm]
    · rw [e]; simp +decide only [upd, ite_false, ite_true, aluEval, ha0, ha2, hz]
      rw [show (0 - dst) &&& 3 = 0 from z0, sub0]
    · rw [e]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd, hz]
      · simp [upd, h0, q2, q3, q4]
  obtain ⟨q9a4, q9a3, q9a2, k9⟩ := q9
  have v9' : St (fillWords m.mem dst (fillWord b) 0) base n9 0x2A (reg n9) := v9.self
  have hge : dst.ult (dst + BitVec.ofNat 32 (4 * w)) = true := by
    simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 4 * w) (by omega), Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true (by omega)
  obtain ⟨n10, d10, v10⟩ := v9'.notTaken hc0 0x2E mz_at_2a (by decide) (by
    simp only [branchTaken]; rw [q9a4, q9a3, hge]; rfl)
  obtain ⟨n11, d11, v11⟩ := v10.lui hc0 mz_at_2e (off' := 0x32) (by decide)
  obtain ⟨n12, d12, v12⟩ := v11.aluImm hc0 mz_at_32 (off' := 0x36) (by decide)
  obtain ⟨n13, d13, v13⟩ := v12.aluImm hc0 mz_at_36 (off' := 0x3A) (by decide)
  obtain ⟨n14, d14, v14⟩ := v13.alu hc0 mz_at_3a (off' := 0x3E) (by decide)
  have r14 : ∀ r, r ≠ a5 → r ≠ a6 → reg n14 r = reg n9 r := fun r h5 h6 => by
    rw [v14.regs]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact v9'.zero.symm
    · simp [upd, h0, h5, h6]
  have r14a5 : reg n14 a5 = fillWord b := by
    rw [v14.regs]; simp +decide only [upd, ite_false, ite_true]
    rw [k9 a1 (by decide) (by decide) (by decide), ha1]; rfl
  obtain ⟨n15, c15, v15, h15a4, f15⟩ := memset_loop hcB hdst hwrap w 0 n14 (by omega) (by omega) v14.self
    (by rw [r14 a4 (by decide) (by decide), q9a4]; exact (add_ofNat_zero dst).symm) r14a5
    (by rw [r14 a3 (by decide) (by decide), q9a3])
  have hcw := hcB w (Nat.le_refl w)
  obtain ⟨n16, d16, v16⟩ := v15.aluImm hcw mz_at_46 (off' := 0x48) (by decide)
  obtain ⟨n17, d17, v17⟩ := v16.alu hcw mz_at_48 (off' := 0x4C) (by decide)
  have a3_15 : reg n15 a3 = dst + BitVec.ofNat 32 (4 * w) := by
    rw [f15 a3 (by decide), r14 a3 (by decide) (by decide), q9a3]
  have a2_15 : reg n15 a2 = BitVec.ofNat 32 (4 * w) := by
    rw [f15 a2 (by decide), r14 a2 (by decide) (by decide), q9a2]
  obtain ⟨n18, d18, v18⟩ := v17.notTaken hcw 0x50 mz_at_4c (by decide) (by
    simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval]
    rw [a3_15, a2_15, w3, add_lit_zero]; simp [BitVec.ult])
  obtain ⟨n19, d19, v19⟩ := v18.jump hcw mz_at_50 (off' := 0x66) (by decide)
    (by rw [v18.pc, BitVec.add_assoc]; exact even_bit0 (even_at _ hbase 0x66 (by decide)))
  obtain ⟨n20, d20, pc20, mem20, regs20⟩ := v19.jalr hcw mz_at_66
  have keep : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg n15 r = reg m r := fun r q2 q3 q4 q5 q6 => by
    rw [f15 r q4, r14 r q5 q6, k9 r q2 q3 q4]
  refine ⟨n20, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (c15.trans (.cons d16 (.cons d17 (.cons d18
    (.cons d19 (.single d20))))))))))))))))))),
    ?_, mem20, ?_, ?_⟩
  · rw [pc20]; simp +decide only [upd, ite_false]
    rw [keep ra (by decide) (by decide) (by decide) (by decide) (by decide), hra, add_lit_zero, hret]
  · rw [regs20]; simp +decide only [upd, ite_false]
    rw [keep a0 (by decide) (by decide) (by decide) (by decide) (by decide), ha0]
  · intro r q2 q3 q4 q5 q6
    rw [regs20]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q4]; exact keep r q2 q3 q4 q5 q6

end C3.RV32
