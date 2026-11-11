import C3BootProofs.Proofs.FieldWideArith

/-!
# `widening_mul_fixed::<8, 8>`, as compiled

`crypto_bigint`'s `widening_mul_fixed::<8, 8>` multiplies two 8-limb numbers
with two nested loops into a 16-word accumulator on its stack, which it
zeroes with `memset` first and copies out with `memcpy` last.
-/

namespace C3.RV32

open C3.ImageV0

/-- The inner loop's add of the accumulator word at `r` and the carry. -/
def wmPath (r : Fin 32) : List BInstr :=
  [.lw a5 r 0x0, .alu .add (28 : Fin 32) (28 : Fin 32) a5, .alu .sltu a5 (28 : Fin 32) a5,
   .alu .add a4 a4 (28 : Fin 32), .alu .sltu (28 : Fin 32) a4 (28 : Fin 32), .alu .add a2 a2 a5,
   .alu .add (28 : Fin 32) (28 : Fin 32) a2, .sw r a4 0x0]

section
set_option maxRecDepth 20000
theorem wmPathA_end : blockEnd wideMulCode 0x6A (wmPath a1) = some 0x7E := by decide
theorem wmPathB_end : blockEnd wideMulCode 0x80 (wmPath a3) = some 0x94 := by decide
end

theorem wmPath_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {B : Word} {r : Fin 32} (hr0 : r.val ≠ 0)
    (hr : r ≠ a5 ∧ r ≠ (28 : Fin 32) ∧ r ≠ a4 ∧ r ≠ a2) (hal : (f r + 0).toNat % 4 = 0)
    (hs : Sep (f r + 0) 4 B wideMulCode.length) : BlockOk B wideMulCode.length (wmPath r) (M, f) := by
  obtain ⟨h5, h28, h4, h2⟩ := hr
  simp only [BlockOk, BInstr.ok, BInstr.run, wmPath]
  refine ⟨hal, trivial, trivial, trivial, trivial, trivial, trivial, ?_, trivial⟩
  simp only [upd, hr0, h5, h28, h4, h2, ite_false]
  exact ⟨hal, hs⟩

/-- The path's effect: the new word at `r`, and the new carry in `t3`. -/
theorem wmPath_run {M : Word → BitVec 8} {f : Fin 32 → Word} {r : Fin 32} {x y t : Word} (hr0 : r.val ≠ 0)
    (hr : r ≠ a5 ∧ r ≠ (28 : Fin 32) ∧ r ≠ a4 ∧ r ≠ a2) (hz : f 0 = 0)
    (h4 : f a4 = aluEval .mul y x) (h2 : f a2 = aluEval .mulhu y x) (h28 : f (28 : Fin 32) = t) :
    (runBlock (wmPath r) (M, f)).1 = memStore32 M (f r + 0) (wmWord y x (memLoad32 M (f r + 0)) t) ∧
    (runBlock (wmPath r) (M, f)).2 (28 : Fin 32) = wmCarry y x (memLoad32 M (f r + 0)) t ∧
    ∀ q, q ≠ a5 → q ≠ (28 : Fin 32) → q ≠ a4 → q ≠ a2 → (runBlock (wmPath r) (M, f)).2 q = f q := by
  obtain ⟨n5, n28, n4, n2⟩ := hr
  simp only [runBlock, BInstr.run, wmPath]
  refine ⟨?_, ?_, fun q q5 q28 q4 q2 => ?_⟩
  · simp only [upd, hr0, n5, n28, n4, n2, ite_false]
    simp +decide only [↓reduceIte, h4, h28]
    rfl
  · simp +decide only [upd, ↓reduceIte, h4, h2, h28]
    rfl
  · by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, q5, q28, q4, q2]

theorem ofNat_add4 (b : Word) (k : Nat) : b + BitVec.ofNat 32 (4 * k) + 4 = b + BitVec.ofNat 32 (4 * (k + 1)) := by
  rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2

theorem ofNat_add1 (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]

theorem cnt_dec : ∀ j : Nat, j < 8 → BitVec.ofNat 32 (8 - j) + 0xFFFFFFFF = BitVec.ofNat 32 (8 - (j + 1)) := by
  decide

theorem cnt_ne : ∀ j : Nat, j < 8 → (BitVec.ofNat 32 (8 - (j + 1)) != 0) = decide (j + 1 < 8) := by decide

/-- The end of an inner-loop pass, from 0x94: advance the pointers, the
column, and the count, and loop while columns are left. -/
theorem wm_tail {M : Word → BitVec 8} {B acc bp : Word} {n : Machine} {i j : Nat}
    (s : St M B n 0x94 (reg n)) (hc : CodeIn M B wideMulCode) (hj : j < 8)
    (ra3 : reg n a3 = acc + BitVec.ofNat 32 (4 * (i + j))) (ra1 : reg n a1 = acc + BitVec.ofNat 32 (4 * (i + j)))
    (ra0 : reg n a0 = BitVec.ofNat 32 (i + j)) (r9 : reg n (9 : Fin 32) = bp + BitVec.ofNat 32 (4 * j))
    (r8 : reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - j)) :
    ∃ n', Steps n n' ∧ St M B n' (if j + 1 < 8 then 0x5C else 0xA0) (reg n') ∧
      reg n' a3 = acc + BitVec.ofNat 32 (4 * (i + (j + 1))) ∧ reg n' a1 = acc + BitVec.ofNat 32 (4 * (i + (j + 1))) ∧
      reg n' a0 = BitVec.ofNat 32 (i + (j + 1)) ∧ reg n' (9 : Fin 32) = bp + BitVec.ofNat 32 (4 * (j + 1)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (j + 1)) ∧
      ∀ q, q ≠ a3 → q ≠ a1 → q ≠ a0 → q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc wm_at_94 (off' := 0x96) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.aluImm hc wm_at_96 (off' := 0x98) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc wm_at_98 (off' := 0x9A) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc wm_at_9a (off' := 0x9C) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc wm_at_9c (off' := 0x9E) (by decide)
  have e3 : reg n5 a3 = acc + BitVec.ofNat 32 (4 * (i + (j + 1))) := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ra3, ofNat_add4]; rfl
  have e1 : reg n5 a1 = acc + BitVec.ofNat 32 (4 * (i + (j + 1))) := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ra1, ofNat_add4]; rfl
  have e0 : reg n5 a0 = BitVec.ofNat 32 (i + (j + 1)) := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ra0, ofNat_add1]; rfl
  have e9 : reg n5 (9 : Fin 32) = bp + BitVec.ofNat 32 (4 * (j + 1)) := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [r9, ofNat_add4]
  have e8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 (8 - (j + 1)) := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [r8]; exact cnt_dec j hj
  have fr : ∀ q, q ≠ a3 → q ≠ a1 → q ≠ a0 → q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → reg n5 q = reg n q :=
    fun q q3 q1 q0 q9 q8 => by
      rw [u5.regs]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd, hz]
      · simp [upd, h0, q3, q1, q0, q9, q8]
  have u5' : St M B n5 0x9E (reg n5) := u5.self
  have hb : branchTaken .bne (reg n5 (8 : Fin 32)) (reg n5 x0) = decide (j + 1 < 8) := by
    rw [e8, u5'.zero]; exact cnt_ne j hj
  by_cases hl : j + 1 < 8
  · obtain ⟨n6, d6, u6⟩ := u5'.taken hc 0x5C wm_at_9e (by decide) (by rw [hb]; exact decide_eq_true hl)
    refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), by rw [ite_eq_left hl]; exact u6.self,
      by rw [u6.regs]; exact e3, by rw [u6.regs]; exact e1, by rw [u6.regs]; exact e0, by rw [u6.regs]; exact e9,
      by rw [u6.regs]; exact e8, fun q q3 q1 q0 q9 q8 => by rw [u6.regs]; exact fr q q3 q1 q0 q9 q8⟩
  · obtain ⟨n6, d6, u6⟩ := u5'.notTaken hc 0xA0 wm_at_9e (by decide) (by rw [hb]; exact decide_eq_false hl)
    refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), by rw [ite_eq_right hl]; exact u6.self,
      by rw [u6.regs]; exact e3, by rw [u6.regs]; exact e1, by rw [u6.regs]; exact e0, by rw [u6.regs]; exact e9,
      by rw [u6.regs]; exact e8, fun q q3 q1 q0 q9 q8 => by rw [u6.regs]; exact fr q q3 q1 q0 q9 q8⟩

theorem ult8 : ∀ k : Nat, k < 16 → (BitVec.ofNat 32 k).ult 8 = decide (k < 8) := by decide

/-- **One pass of the inner loop**, from 0x5C: add `y * x` and the carry to
the accumulator word at column `i + j`, for `y` the `j`-th word of the
second operand and `x` the row's word of the first. -/
theorem wm_iter {M : Word → BitVec 8} {B acc bp x t : Word} {n : Machine} {i j : Nat}
    (s : St M B n 0x5C (reg n)) (hc : CodeIn M B wideMulCode) (hB : B.toNat % 2 = 0) (hj : j < 8)
    (hij : i + j < 16) (hacc : acc.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0)
    (hS : Sep (acc + BitVec.ofNat 32 (4 * (i + j))) 4 B wideMulCode.length)
    (r9 : reg n (9 : Fin 32) = bp + BitVec.ofNat 32 (4 * j)) (r7 : reg n (7 : Fin 32) = x)
    (r28 : reg n (28 : Fin 32) = t) (ra0 : reg n a0 = BitVec.ofNat 32 (i + j))
    (ra1 : reg n a1 = acc + BitVec.ofNat 32 (4 * (i + j))) (ra3 : reg n a3 = acc + BitVec.ofNat 32 (4 * (i + j)))
    (r6 : reg n (6 : Fin 32) = 8) (r8 : reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - j)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (acc + BitVec.ofNat 32 (4 * (i + j)))
        (wmWord (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + j)))) t))
        B n' (if j + 1 < 8 then 0x5C else 0xA0) (reg n') ∧
      reg n' (9 : Fin 32) = bp + BitVec.ofNat 32 (4 * (j + 1)) ∧ reg n' (7 : Fin 32) = x ∧
      reg n' (28 : Fin 32) = wmCarry (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x
        (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + j)))) t ∧
      reg n' a0 = BitVec.ofNat 32 (i + (j + 1)) ∧ reg n' a1 = acc + BitVec.ofNat 32 (4 * (i + (j + 1))) ∧
      reg n' a3 = acc + BitVec.ofNat 32 (4 * (i + (j + 1))) ∧ reg n' (6 : Fin 32) = 8 ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (j + 1)) ∧
      ∀ q, q ≠ (9 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ (8 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ a2 →
        q ≠ a4 → q ≠ a5 → reg n' q = reg n q := by
  have hz := s.zero
  have hal : (acc + BitVec.ofNat 32 (4 * (i + j))).toNat % 4 = 0 := aligned_add hacc (by omega)
  obtain ⟨n1, d1, u1⟩ := s.lw hc wm_at_5c (off' := 0x5E) (by decide)
    (by rw [r9, add_lit_zero]; exact aligned_add hbp (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.alu hc wm_at_5e (off' := 0x62) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.alu hc wm_at_62 (off' := 0x66) (by decide)
  rw [r9, add_lit_zero] at u3
  have u3' := u3.self
  have g4 : reg n3 a4 = aluEval .mul (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte, r7]
  have g2 : reg n3 a2 = aluEval .mulhu (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte, r7]
  have fr3 : ∀ q, q ≠ a4 → q ≠ a2 → reg n3 q = reg n q := fun q q4 q2 => by
    rw [u3.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q4, q2]
  have g28 : reg n3 (28 : Fin 32) = t := by rw [fr3 _ (by decide) (by decide), r28]
  have hb : branchTaken .bgeu (reg n3 a0) (reg n3 (6 : Fin 32)) = !decide (i + j < 8) := by
    rw [fr3 a0 (by decide) (by decide), fr3 _ (by decide) (by decide), ra0, r6]
    show (!(BitVec.ofNat 32 (i + j)).ult 8) = _
    rw [ult8 _ hij]
  -- both paths store at the same word
  have common : ∀ (r : Fin 32) (o : Nat) {n4 : Machine}, r.val ≠ 0 → (r ≠ a5 ∧ r ≠ (28 : Fin 32) ∧ r ≠ a4 ∧ r ≠ a2) →
      reg n3 r = acc + BitVec.ofNat 32 (4 * (i + j)) → St M B n4 o (reg n3) →
      blockEnd wideMulCode o (wmPath r) = some (o + 20) →
      ∃ n5, Steps n4 n5 ∧ St (memStore32 M (acc + BitVec.ofNat 32 (4 * (i + j)))
          (wmWord (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + j)))) t))
          B n5 (o + 20) (reg n5) ∧
        reg n5 (28 : Fin 32) = wmCarry (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x
          (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + j)))) t ∧
        ∀ q, q ≠ a5 → q ≠ (28 : Fin 32) → q ≠ a4 → q ≠ a2 → reg n5 q = reg n3 q := by
    intro r o n4 hr0 hr hrv s4 he
    have ok := wmPath_ok (M := M) (f := reg n3) hr0 hr (by rw [hrv, add_lit_zero]; exact hal)
      (by rw [hrv, add_lit_zero]; exact hS)
    obtain ⟨n5, c5, u5⟩ := St.block (wmPath r) s4 hc he ok
    obtain ⟨em, et, ek⟩ := wmPath_run (M := M) (f := reg n3) hr0 hr u3'.zero g4 g2 g28
    rw [em, hrv, add_lit_zero] at u5
    rw [hrv, add_lit_zero] at et
    refine ⟨n5, c5, u5.self, by rw [u5.regs, et], fun q q5 q28 q4 q2 => by rw [u5.regs, ek q q5 q28 q4 q2]⟩
  -- after either path, at 0x94
  have tail : ∀ {M' : Word → BitVec 8} {n5 : Machine}, St M' B n5 0x94 (reg n5) → CodeIn M' B wideMulCode →
      (∀ q, q ≠ a5 → q ≠ (28 : Fin 32) → q ≠ a4 → q ≠ a2 → reg n5 q = reg n3 q) →
      ∃ n', Steps n5 n' ∧ St M' B n' (if j + 1 < 8 then 0x5C else 0xA0) (reg n') ∧
        reg n' (9 : Fin 32) = bp + BitVec.ofNat 32 (4 * (j + 1)) ∧ reg n' (7 : Fin 32) = x ∧
        reg n' (28 : Fin 32) = reg n5 (28 : Fin 32) ∧
        reg n' a0 = BitVec.ofNat 32 (i + (j + 1)) ∧ reg n' a1 = acc + BitVec.ofNat 32 (4 * (i + (j + 1))) ∧
        reg n' a3 = acc + BitVec.ofNat 32 (4 * (i + (j + 1))) ∧ reg n' (6 : Fin 32) = 8 ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (j + 1)) ∧
        ∀ q, q ≠ (9 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ (8 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ a2 →
          q ≠ a4 → q ≠ a5 → reg n' q = reg n q := by
    intro M' n5 s5 hc' k5
    have p : ∀ q, q ≠ a5 → q ≠ (28 : Fin 32) → q ≠ a4 → q ≠ a2 → reg n5 q = reg n q := fun q q5 q28 q4 q2 => by
      rw [k5 q q5 q28 q4 q2, fr3 q q4 q2]
    obtain ⟨n', c', u', e3, e1, e0, e9, e8, fr⟩ := wm_tail (i := i) (acc := acc) (bp := bp) s5 hc' hj
      (by rw [p _ (by decide) (by decide) (by decide) (by decide), ra3])
      (by rw [p _ (by decide) (by decide) (by decide) (by decide), ra1])
      (by rw [p _ (by decide) (by decide) (by decide) (by decide), ra0])
      (by rw [p _ (by decide) (by decide) (by decide) (by decide), r9])
      (by rw [p _ (by decide) (by decide) (by decide) (by decide), r8])
    refine ⟨n', c', u', e9, ?_, fr _ (by decide) (by decide) (by decide) (by decide) (by decide), e0, e1, e3, ?_, e8,
      fun q q9 q0 q1 q3 q8 q28 q2 q4 q5 => by rw [fr q q3 q1 q0 q9 q8, p q q5 q28 q4 q2]⟩
    · rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide),
        p _ (by decide) (by decide) (by decide) (by decide), r7]
    · rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide),
        p _ (by decide) (by decide) (by decide) (by decide), r6]
  by_cases hlo : i + j < 8
  · obtain ⟨n4, d4, u4⟩ := u3'.notTaken hc 0x6A wm_at_66 (by decide) (by rw [hb]; simp [hlo])
    obtain ⟨n5, c5, u5, e28, k5⟩ := common a1 0x6A (by decide) (by decide)
      (by rw [fr3 a1 (by decide) (by decide), ra1]) u4 wmPathA_end
    have hc5 := CodeIn.store32 (v := wmWord (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + j)))) t) hc hS
    obtain ⟨n6, d6, u6⟩ := u5.jump hc5 wm_at_7e (off' := 0x94) (by decide)
      (by rw [u5.pc, BitVec.add_assoc]; exact even_bit0 (even_at B hB 0x94 (by decide)))
    have k6 : ∀ q, q ≠ a5 → q ≠ (28 : Fin 32) → q ≠ a4 → q ≠ a2 → reg n6 q = reg n3 q := fun q q5 q28 q4 q2 => by
      rw [u6.regs, k5 q q5 q28 q4 q2]
    obtain ⟨n', c', u', e9, e7, e28', rest⟩ := tail u6.self hc5 k6
    refine ⟨n', (Steps.cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans (.cons d6 c'))))) ), u', e9, e7, ?_, rest⟩
    rw [e28', u6.regs, e28]
  · obtain ⟨n4, d4, u4⟩ := u3'.taken hc 0x80 wm_at_66 (by decide) (by rw [hb]; simp [hlo])
    obtain ⟨n5, c5, u5, e28, k5⟩ := common a3 0x80 (by decide) (by decide)
      (by rw [fr3 a3 (by decide) (by decide), ra3]) u4 wmPathB_end
    have hc5 := CodeIn.store32 (v := wmWord (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + j)))) t) hc hS
    obtain ⟨n', c', u', e9, e7, e28', rest⟩ := tail u5 hc5 k5
    refine ⟨n', (Steps.cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans c'))))), u', e9, e7, ?_, rest⟩
    rw [e28', e28]

theorem inner_arith {A0 A1 A' t t1 t' x bj w W Bj B8 Pi Pj P8 : Nat}
    (h1 : A1 + w * (Pi * Pj) = A0 + W * (Pi * Pj)) (h2 : W + 2 ^ 32 * t1 = bj * x + w + t)
    (h3 : A' + t' * P8 + x * (Bj + bj * Pj) * Pi = A1 + t1 * (Pi * Pj * 2 ^ 32) + x * B8 * Pi) :
    A' + t' * P8 + x * Bj * Pi = A0 + t * (Pi * Pj) + x * B8 * Pi := by
  have e2 : W * (Pi * Pj) + t1 * (Pi * Pj * 2 ^ 32) = (bj * x + w + t) * (Pi * Pj) := by
    rw [← h2, Nat.add_mul]; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  simp only [Nat.add_mul, Nat.mul_add] at h3 e2
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] at h1 h3 e2 ⊢
  omega

theorem pow_split (i j : Nat) : 2 ^ (32 * (i + j)) = 2 ^ (32 * i) * 2 ^ (32 * j) := by
  rw [Nat.mul_add, Nat.pow_add]

theorem pow_split1 (i j : Nat) : 2 ^ (32 * (i + (j + 1))) = 2 ^ (32 * i) * 2 ^ (32 * j) * 2 ^ 32 := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.pow_add, Nat.mul_assoc]

theorem acc_frame {M : Word → BitVec 8} {acc a v : Word} {k : Nat} (hk : k < 16) (h : Sep acc 64 a 1) :
    memStore32 M (acc + BitVec.ofNat 32 (4 * k)) v a = M a :=
  memStore32_ne fun i hi e => by
    have := h.point (i := 4 * k + i) (j := 0) (by omega) (by decide)
    rw [add_ofNat_zero, ← add_ofNat_assoc] at this
    exact this e.symm

theorem accV_bp {M : Word → BitVec 8} {acc bp v : Word} {k : Nat} (hk : k < 16) (hAB : Sep acc 64 bp 32) :
    ∀ n, n ≤ 8 → accV (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) v) bp n = accV M bp n :=
  fun n hn => accV_congr n fun l hl => memLoad32_store32_sep ((hAB.sub (c := 4 * k) (l := 4) (by omega)).subR (by omega))

/-- **The inner loop**, from column `j` of row `i` to its end at 0xA0: add
`x` times the second operand's words `j..7` into the accumulator. -/
theorem wm_inner {B acc bp x : Word} {i : Nat} (hB : B.toNat % 2 = 0) (hi : i < 8)
    (hacc : acc.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0) (haw : acc.toNat + 64 ≤ 2 ^ 32)
    (hAB : Sep acc 64 bp 32) (hAC : Sep acc 64 B wideMulCode.length) :
    ∀ m j, j + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine} {t : Word},
      St M B n 0x5C (reg n) → CodeIn M B wideMulCode →
      reg n (9 : Fin 32) = bp + BitVec.ofNat 32 (4 * j) → reg n (7 : Fin 32) = x → reg n (28 : Fin 32) = t →
      reg n a0 = BitVec.ofNat 32 (i + j) → reg n a1 = acc + BitVec.ofNat 32 (4 * (i + j)) →
      reg n a3 = acc + BitVec.ofNat 32 (4 * (i + j)) → reg n (6 : Fin 32) = 8 →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - j) →
      ∃ n' M', Steps n n' ∧ St M' B n' 0xA0 (reg n') ∧ CodeIn M' B wideMulCode ∧
        reg n' (9 : Fin 32) = bp + BitVec.ofNat 32 (4 * 8) ∧ reg n' (7 : Fin 32) = x ∧
        reg n' a0 = BitVec.ofNat 32 (i + 8) ∧ reg n' a1 = acc + BitVec.ofNat 32 (4 * (i + 8)) ∧
        reg n' a3 = acc + BitVec.ofNat 32 (4 * (i + 8)) ∧ reg n' (6 : Fin 32) = 8 ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - 8) ∧
        accV M' acc 16 + (reg n' (28 : Fin 32)).toNat * 2 ^ (32 * (i + 8)) + x.toNat * accV M bp j * 2 ^ (32 * i) =
          accV M acc 16 + t.toNat * 2 ^ (32 * (i + j)) + x.toNat * accV M bp 8 * 2 ^ (32 * i) ∧
        (∀ a, Sep acc 64 a 1 → M' a = M a) ∧
        (∀ k, i + 8 ≤ k → k < 16 →
          memLoad32 M' (acc + BitVec.ofNat 32 (4 * k)) = memLoad32 M (acc + BitVec.ofNat 32 (4 * k))) ∧
        ∀ q, q ≠ (9 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ (8 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ a2 →
          q ≠ a4 → q ≠ a5 → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro j hj M n t s hc r9 r7 r28 ra0 ra1 ra3 r6 r8
    have j7 : j = 7 := by omega
    subst j7
    obtain ⟨n1, c1, u1, e9, e7, e28, e0, e1, e3, e6, e8, fr⟩ := wm_iter (i := i) s hc hB (by decide) (by omega)
      hacc hbp (hAC.sub (by omega)) r9 r7 r28 ra0 ra1 ra3 r6 r8
    refine ⟨n1, _, c1, u1, CodeIn.store32 hc (hAC.sub (by omega)), e9, e7, e0, e1, e3, e6, e8, ?_,
      fun a ha => acc_frame (by omega) ha,
      fun k hk1 hk2 => memLoad32_store32_sep (sep_offsets acc (.inl (by omega)) (by omega) (by omega)), fr⟩
    rw [e28]
    have h1 := accV_store (M := M) (b := acc) (k := i + 7)
      (v := wmWord (memLoad32 M (bp + BitVec.ofNat 32 (4 * 7))) x (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + 7)))) t)
      16 (by omega) (by omega)
    have h2 := wm_step (memLoad32 M (bp + BitVec.ofNat 32 (4 * 7))) x
      (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + 7)))) t
    rw [pow_split i 7] at h1
    have h3 : accV (memStore32 M (acc + BitVec.ofNat 32 (4 * (i + 7)))
          (wmWord (memLoad32 M (bp + BitVec.ofNat 32 (4 * 7))) x (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + 7)))) t))
          acc 16 +
        (wmCarry (memLoad32 M (bp + BitVec.ofNat 32 (4 * 7))) x
          (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + 7)))) t).toNat * 2 ^ (32 * (i + 8)) +
        x.toNat * (accV M bp 7 + (memLoad32 M (bp + BitVec.ofNat 32 (4 * 7))).toNat * 2 ^ (32 * 7)) * 2 ^ (32 * i) =
      accV (memStore32 M (acc + BitVec.ofNat 32 (4 * (i + 7)))
          (wmWord (memLoad32 M (bp + BitVec.ofNat 32 (4 * 7))) x (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + 7)))) t))
          acc 16 +
        (wmCarry (memLoad32 M (bp + BitVec.ofNat 32 (4 * 7))) x
          (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + 7)))) t).toNat * (2 ^ (32 * i) * 2 ^ (32 * 7) * 2 ^ 32) +
        x.toNat * accV M bp 8 * 2 ^ (32 * i) := by
      rw [show i + 8 = i + (7 + 1) from rfl, pow_split1 i 7]; rfl
    have := inner_arith h1 h2 h3
    rw [pow_split i 7]
    exact this
  | succ m ih =>
    intro j hj M n t s hc r9 r7 r28 ra0 ra1 ra3 r6 r8
    have hl : j + 1 < 8 := by omega
    obtain ⟨n1, c1, u1, e9, e7, e28, e0, e1, e3, e6, e8, fr⟩ := wm_iter (i := i) s hc hB (by omega) (by omega)
      hacc hbp (hAC.sub (by omega)) r9 r7 r28 ra0 ra1 ra3 r6 r8
    rw [ite_eq_left hl] at u1
    rw [← Nat.add_assoc] at e0 e1 e3
    obtain ⟨n', M', c', u', hc', f9, f7, f0, f1, f3, f6, f8, hv, hm, hw, fr'⟩ :=
      ih (j + 1) (by omega) u1 (CodeIn.store32 hc (hAC.sub (by omega))) e9 e7 e28 e0 e1 e3 e6 e8
    refine ⟨n', M', c1.trans c', u', hc', f9, f7, f0, f1, f3, f6, f8, ?_,
      fun a ha => by rw [hm a ha, acc_frame (by omega) ha],
      fun k hk1 hk2 => by
        rw [hw k hk1 hk2]; exact memLoad32_store32_sep (sep_offsets acc (.inl (by omega)) (by omega) (by omega)),
      fun q q9 q0 q1 q3 q8 q28 q2 q4 q5 => by
        rw [fr' q q9 q0 q1 q3 q8 q28 q2 q4 q5, fr q q9 q0 q1 q3 q8 q28 q2 q4 q5]⟩
    rw [accV_bp (by omega) hAB _ (by omega), accV_bp (by omega) hAB _ (by omega)] at hv
    have h1 := accV_store (M := M) (b := acc) (k := i + j)
      (v := wmWord (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + j)))) t)
      16 (by omega) (by omega)
    have h2 := wm_step (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))) x
      (memLoad32 M (acc + BitVec.ofNat 32 (4 * (i + j)))) t
    rw [pow_split i j] at h1
    rw [pow_split1 i j, show accV M bp (j + 1) = accV M bp j +
      (memLoad32 M (bp + BitVec.ofNat 32 (4 * j))).toNat * 2 ^ (32 * j) from rfl] at hv
    have := inner_arith h1 h2 hv
    rw [pow_split i j]
    exact this

/-- The registers one row of the outer loop leaves alone. -/
def rowKeep (q : Fin 32) : Bool := q.val ∉ [5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 22, 28]

theorem rowKeep_ne {q r : Fin 32} (h : rowKeep q = true) (hr : rowKeep r = false) : q ≠ r :=
  fun e => by rw [e, hr] at h; exact Bool.false_ne_true h

theorem sll2 : ∀ i : Nat, i < 8 → aluEval .sll (BitVec.ofNat 32 i) 2 = BitVec.ofNat 32 (4 * i) := by decide

theorem hi_addr (acc : Word) (i : Nat) : BitVec.ofNat 32 (4 * i) + (acc + 0x20) = acc + BitVec.ofNat 32 (4 * (i + 8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show _ = (acc.toNat + (4 * (i + 8)) % 2 ^ 32) % 2 ^ 32
  have : (0x20 : Word).toNat = 32 := rfl
  rw [this]; omega

theorem row_arith {A Ai x B8 Pi : Nat} (h : A = Ai * B8) : A + x * B8 * Pi = (Ai + x * Pi) * B8 := by
  rw [h, Nat.add_mul]; simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem accV_frame {M M0 : Word → BitVec 8} {acc b : Word} {n : Nat} (hf : ∀ a, Sep acc 64 a 1 → M a = M0 a)
    (hs : Sep acc 64 b (4 * n)) : accV M b n = accV M0 b n :=
  accV_congr n fun l hl => memLoad32_congr fun q hq => hf _ (by
    have := hs.subR (c := 4 * l + q) (l := 1) (by omega)
    rwa [← add_ofNat_assoc] at this)

/-- **One row of the outer loop**, from 0x42: add `a[i]` times the second
operand into the accumulator at word `i`, and its last carry at word `i + 8`. -/
theorem row_ne : ∀ i : Nat, i < 8 → (BitVec.ofNat 32 (i + 1) != 8) = decide (i + 1 < 8) := by decide

theorem wm_row {B acc ap bp : Word} {M0 : Word → BitVec 8} {i : Nat} (hB : B.toNat % 2 = 0) (hi : i < 8)
    (hacc : acc.toNat % 4 = 0) (hap : ap.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0) (haw : acc.toNat + 64 ≤ 2 ^ 32)
    (hAA : Sep acc 64 ap 32) (hAB : Sep acc 64 bp 32) (hAC : Sep acc 64 B wideMulCode.length)
    {M : Word → BitVec 8} {n : Machine} (s : St M B n 0x42 (reg n)) (hc : CodeIn M B wideMulCode)
    (hfr : ∀ a, Sep acc 64 a 1 → M a = M0 a)
    (hz : ∀ k, i + 8 ≤ k → k < 16 → memLoad32 M (acc + BitVec.ofNat 32 (4 * k)) = 0)
    (hv : accV M acc 16 = accV M0 ap i * accV M0 bp 8)
    (r5 : reg n (5 : Fin 32) = BitVec.ofNat 32 i) (r16 : reg n a6 = acc + BitVec.ofNat 32 (4 * i))
    (r22 : reg n (22 : Fin 32) = acc + BitVec.ofNat 32 (4 * i)) (r6 : reg n (6 : Fin 32) = 8)
    (r21 : reg n (21 : Fin 32) = ap) (r19 : reg n (19 : Fin 32) = bp) (r20 : reg n (20 : Fin 32) = acc + 0x20) :
    ∃ n' M', Steps n n' ∧ St M' B n' (if i + 1 < 8 then 0x42 else 0xB0) (reg n') ∧ CodeIn M' B wideMulCode ∧
      (∀ a, Sep acc 64 a 1 → M' a = M0 a) ∧
      (∀ k, i + 1 + 8 ≤ k → k < 16 → memLoad32 M' (acc + BitVec.ofNat 32 (4 * k)) = 0) ∧
      accV M' acc 16 = accV M0 ap (i + 1) * accV M0 bp 8 ∧
      reg n' (5 : Fin 32) = BitVec.ofNat 32 (i + 1) ∧ reg n' a6 = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (22 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      ∀ q, rowKeep q = true → reg n' q = reg n q := by
  have hz0 := s.zero
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc wm_at_42 (off' := 0x44) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.aluImm hc wm_at_44 (off' := 0x48) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.alu hc wm_at_48 (off' := 0x4C) (by decide)
  have g3 : reg n3 a0 = ap + BitVec.ofNat 32 (4 * i) := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte, r21, r5]; rw [sll2 i hi]; rfl
  obtain ⟨n4, d4, u4⟩ := u3.self.lw hc wm_at_4c (off' := 0x50) (by decide)
    (by rw [g3, add_lit_zero]; exact aligned_add hap (by omega))
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc wm_at_50 (off' := 0x52) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.alu hc wm_at_52 (off' := 0x54) (by decide)
  obtain ⟨n7, d7, u7⟩ := u6.alu hc wm_at_54 (off' := 0x56) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.alu hc wm_at_56 (off' := 0x58) (by decide)
  obtain ⟨n9, d9, u9⟩ := u8.alu hc wm_at_58 (off' := 0x5A) (by decide)
  rw [g3, add_lit_zero] at u9
  have hx : memLoad32 M (ap + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (ap + BitVec.ofNat 32 (4 * i)) :=
    memLoad32_congr fun q hq => hfr _ (by
      have := hAA.subR (c := 4 * i + q) (l := 1) (by omega)
      rwa [← add_ofNat_assoc] at this)
  have hz3 := u3.self.zero
  -- the prologue's registers, from `reg n3`
  have p3 : ∀ q, q ≠ (28 : Fin 32) → q ≠ a7 → q ≠ a0 → reg n3 q = reg n q := fun q q28 q17 q0 => by
    rw [u3.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz0]
    · simp [upd, h0, q28, q17, q0]
  have p9 : ∀ q, q ≠ (7 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a3 →
      reg n9 q = reg n3 q := fun q q7 q8 q9 q0 q1 q3 => by
    rw [u9.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz3]
    · simp [upd, h0, q7, q8, q9, q0, q1, q3]
  have e28 : reg n9 (28 : Fin 32) = 0 := by
    rw [p9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd, ↓reduceIte, hz0]
  have e17 : reg n9 a7 = BitVec.ofNat 32 (4 * i) := by
    rw [p9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd, ↓reduceIte, r5]; exact sll2 i hi
  have e7 : reg n9 (7 : Fin 32) = memLoad32 M0 (ap + BitVec.ofNat 32 (4 * i)) := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]; exact hx
  have e8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 (8 - 0) := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
  have e9 : reg n9 (9 : Fin 32) = bp + BitVec.ofNat 32 (4 * 0) := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [p3 _ (by decide) (by decide) (by decide), r19]
    show (0 : Word) + bp = bp + 0
    exact (BitVec.zero_add bp).trans (BitVec.add_zero bp).symm
  have e0 : reg n9 a0 = BitVec.ofNat 32 (i + 0) := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [p3 _ (by decide) (by decide) (by decide), r5]; exact BitVec.zero_add _
  have e1 : reg n9 a1 = acc + BitVec.ofNat 32 (4 * (i + 0)) := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [p3 _ (by decide) (by decide) (by decide), r22]; exact BitVec.zero_add _
  have e3 : reg n9 a3 = acc + BitVec.ofNat 32 (4 * (i + 0)) := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [p3 _ (by decide) (by decide) (by decide), r16]; exact BitVec.zero_add _
  have e6 : reg n9 (6 : Fin 32) = 8 := by
    rw [p9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      p3 _ (by decide) (by decide) (by decide), r6]
  obtain ⟨n10, d10, u10⟩ := u9.self.notTaken hc 0x5C wm_at_5a (by decide)
    (by rw [e8, u9.self.zero]; decide)
  obtain ⟨n', M', c', u', hc', f9, f7, f0, f1, f3, f6, f8, hval, hm, hw, fr'⟩ :=
    wm_inner (x := memLoad32 M0 (ap + BitVec.ofNat 32 (4 * i))) hB hi hacc hbp haw hAB hAC 7 0 rfl
      (t := 0) u10.self hc ((u10.regs _).trans e9) ((u10.regs _).trans e7) ((u10.regs _).trans e28)
      ((u10.regs _).trans e0) ((u10.regs _).trans e1) ((u10.regs _).trans e3)
      ((u10.regs _).trans e6) ((u10.regs _).trans e8)
  have pre : ∀ q, q ≠ (7 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 →
      q ≠ a4 → q ≠ a5 → q ≠ (28 : Fin 32) → q ≠ a7 → reg n' q = reg n q :=
    fun q q7 q8 q9 q0 q1 q2 q3 q4 q5 q28 q17 => by
      rw [fr' q q9 q0 q1 q3 q8 q28 q2 q4 q5, u10.regs, p9 q q7 q8 q9 q0 q1 q3, p3 q q28 q17 q0]
  have g17 : reg n' a7 = BitVec.ofNat 32 (4 * i) := by
    rw [fr' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), u10.regs, e17]
  have g20 : reg n' (20 : Fin 32) = acc + 0x20 := by
    rw [pre _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), r20]
  have hcar := hc'
  obtain ⟨m1, d11, v1⟩ := u'.alu hc' wm_at_a0 (off' := 0xA2) (by decide)
  obtain ⟨m2, d12, v2⟩ := v1.aluImm hc' wm_at_a2 (off' := 0xA4) (by decide)
  have ha7 : upd (upd (reg n') a7 (aluEval .add (reg n' a7) (reg n' (20 : Fin 32)))) (5 : Fin 32)
      (aluEval .add (upd (reg n') a7 (aluEval .add (reg n' a7) (reg n' (20 : Fin 32))) (5 : Fin 32)) 1) a7 + 0 =
      acc + BitVec.ofNat 32 (4 * (i + 8)) := by
    simp +decide only [upd, ↓reduceIte]; rw [g17, g20, add_lit_zero]; exact hi_addr acc i
  obtain ⟨m3, d13, v3⟩ := v2.sw hc' wm_at_a4 (off' := 0xA8) (by decide)
    (by rw [ha7]; exact aligned_add hacc (by omega))
  rw [ha7] at v3
  have hcf : CodeIn (memStore32 M' (acc + BitVec.ofNat 32 (4 * (i + 8))) (reg n' (28 : Fin 32))) B wideMulCode :=
    CodeIn.store32 hc' (hAC.sub (by omega))
  obtain ⟨m4, d14, v4⟩ := v3.aluImm hcf wm_at_a8 (off' := 0xAA) (by decide)
  obtain ⟨m5, d15, v5⟩ := v4.aluImm hcf wm_at_aa (off' := 0xAC) (by decide)
  have k5 : reg m5 (5 : Fin 32) = BitVec.ofNat 32 (i + 1) := by
    rw [v5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [pre _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), r5]; exact ofNat_add1 i
  have k16 : reg m5 a6 = acc + BitVec.ofNat 32 (4 * (i + 1)) := by
    rw [v5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [pre _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), r16]; exact ofNat_add4 acc i
  have k22 : reg m5 (22 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) := by
    rw [v5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [pre _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), r22]; exact ofNat_add4 acc i
  have k6 : reg m5 (6 : Fin 32) = 8 := by
    rw [v5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [pre _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), r6]
  have hz' := u'.zero
  have kk : ∀ q, rowKeep q = true → reg m5 q = reg n q := fun q hq => by
    have q5 := rowKeep_ne hq (r := 5) (by decide)
    have q7 := rowKeep_ne hq (r := 7) (by decide)
    have q8 := rowKeep_ne hq (r := 8) (by decide)
    have q9 := rowKeep_ne hq (r := 9) (by decide)
    have q10 := rowKeep_ne hq (r := a0) (by decide)
    have q11 := rowKeep_ne hq (r := a1) (by decide)
    have q12 := rowKeep_ne hq (r := a2) (by decide)
    have q13 := rowKeep_ne hq (r := a3) (by decide)
    have q14 := rowKeep_ne hq (r := a4) (by decide)
    have q15 := rowKeep_ne hq (r := a5) (by decide)
    have q16 := rowKeep_ne hq (r := a6) (by decide)
    have q17 := rowKeep_ne hq (r := a7) (by decide)
    have q22 := rowKeep_ne hq (r := 22) (by decide)
    have q28 := rowKeep_ne hq (r := 28) (by decide)
    rw [v5.regs, ← pre q q7 q8 q9 q10 q11 q12 q13 q14 q15 q28 q17]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz']
    · have qz : q ≠ 0 := fun e => h0 (by rw [e]; rfl)
      simp [upd, qz, q5, q16, q17, q22]
  have v5' := v5.self
  have hb : branchTaken .bne (reg m5 (5 : Fin 32)) (reg m5 (6 : Fin 32)) = decide (i + 1 < 8) := by
    rw [k5, k6]; exact row_ne i hi
  -- memory
  have hold : memLoad32 M' (acc + BitVec.ofNat 32 (4 * (i + 8))) = 0 := by
    rw [hw (i + 8) (by omega) (by omega), hz (i + 8) (by omega) (by omega)]
  have hframe : ∀ a, Sep acc 64 a 1 →
      memStore32 M' (acc + BitVec.ofNat 32 (4 * (i + 8))) (reg n' (28 : Fin 32)) a = M0 a := fun a ha => by
    rw [acc_frame (by omega) ha, hm a ha, hfr a ha]
  have hzero : ∀ k, i + 1 + 8 ≤ k → k < 16 →
      memLoad32 (memStore32 M' (acc + BitVec.ofNat 32 (4 * (i + 8))) (reg n' (28 : Fin 32)))
        (acc + BitVec.ofNat 32 (4 * k)) = 0 := fun k hk1 hk2 => by
    rw [memLoad32_store32_sep (sep_offsets acc (.inl (by omega)) (by omega) (by omega)),
      hw k (by omega) hk2, hz k (by omega) hk2]
  have hvalue : accV (memStore32 M' (acc + BitVec.ofNat 32 (4 * (i + 8))) (reg n' (28 : Fin 32))) acc 16 =
      accV M0 ap (i + 1) * accV M0 bp 8 := by
    have hs := accV_store (M := M') (b := acc) (k := i + 8) (v := reg n' (28 : Fin 32)) 16 (by omega) (by omega)
    rw [hold, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero] at hs
    rw [show accV M bp 0 = 0 from rfl, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.zero_mul,
      Nat.zero_mul, Nat.add_zero, Nat.add_zero, accV_frame (b := bp) (n := 8) hfr hAB] at hval
    rw [hs, hval, Nat.add_zero, row_arith hv]
    rfl
  by_cases hl : i + 1 < 8
  · obtain ⟨m6, d16, v6⟩ := v5'.taken hcf 0x42 wm_at_ac (by decide) (by rw [hb]; exact decide_eq_true hl)
    refine ⟨m6, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
      (.cons d10 (c'.trans (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.single d16)))))))))))))))),
      by rw [ite_eq_left hl]; exact v6.self, hcf, hframe, hzero, hvalue,
      (v6.regs _).trans k5, (v6.regs _).trans k16, (v6.regs _).trans k22, fun q hq => (v6.regs _).trans (kk q hq)⟩
  · obtain ⟨m6, d16, v6⟩ := v5'.notTaken hcf 0xB0 wm_at_ac (by decide) (by rw [hb]; exact decide_eq_false hl)
    refine ⟨m6, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
      (.cons d10 (c'.trans (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.single d16)))))))))))))))),
      by rw [ite_eq_right hl]; exact v6.self, hcf, hframe, hzero, hvalue,
      (v6.regs _).trans k5, (v6.regs _).trans k16, (v6.regs _).trans k22, fun q hq => (v6.regs _).trans (kk q hq)⟩

/-- **The outer loop**, from row `i` to its end at 0xB0. -/
theorem wm_rows {B acc ap bp : Word} {M0 : Word → BitVec 8} (hB : B.toNat % 2 = 0)
    (hacc : acc.toNat % 4 = 0) (hap : ap.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0) (haw : acc.toNat + 64 ≤ 2 ^ 32)
    (hAA : Sep acc 64 ap 32) (hAB : Sep acc 64 bp 32) (hAC : Sep acc 64 B wideMulCode.length) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine}, St M B n 0x42 (reg n) → CodeIn M B wideMulCode →
      (∀ a, Sep acc 64 a 1 → M a = M0 a) →
      (∀ k, i + 8 ≤ k → k < 16 → memLoad32 M (acc + BitVec.ofNat 32 (4 * k)) = 0) →
      accV M acc 16 = accV M0 ap i * accV M0 bp 8 →
      reg n (5 : Fin 32) = BitVec.ofNat 32 i → reg n a6 = acc + BitVec.ofNat 32 (4 * i) →
      reg n (22 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) → reg n (6 : Fin 32) = 8 →
      reg n (21 : Fin 32) = ap → reg n (19 : Fin 32) = bp → reg n (20 : Fin 32) = acc + 0x20 →
      ∃ n' M', Steps n n' ∧ St M' B n' 0xB0 (reg n') ∧ CodeIn M' B wideMulCode ∧
        (∀ a, Sep acc 64 a 1 → M' a = M0 a) ∧ accV M' acc 16 = accV M0 ap 8 * accV M0 bp 8 ∧
        ∀ q, rowKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hz hv r5 r16 r22 r6 r21 r19 r20
    have i7 : i = 7 := by omega
    subst i7
    obtain ⟨n', M', c', u', hc', hf', _, hv', _, _, _, kk⟩ :=
      wm_row hB (by decide) hacc hap hbp haw hAA hAB hAC s hc hfr hz hv r5 r16 r22 r6 r21 r19 r20
    exact ⟨n', M', c', u', hc', hf', hv', kk⟩
  | succ m ih =>
    intro i hi M n s hc hfr hz hv r5 r16 r22 r6 r21 r19 r20
    have hl : i + 1 < 8 := by omega
    obtain ⟨n1, M1, c1, u1, hc1, hf1, hz1, hv1, k5, k16, k22, kk⟩ :=
      wm_row hB (by omega) hacc hap hbp haw hAA hAB hAC s hc hfr hz hv r5 r16 r22 r6 r21 r19 r20
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hv', kk'⟩ := ih (i + 1) (by omega) u1 hc1 hf1 hz1 hv1 k5 k16 k22
      ((kk _ (by decide)).trans r6) ((kk _ (by decide)).trans r21) ((kk _ (by decide)).trans r19)
      ((kk _ (by decide)).trans r20)
    exact ⟨n', M', c1.trans c', u', hc', hf', hv', fun q hq => (kk' q hq).trans (kk q hq)⟩

end C3.RV32
