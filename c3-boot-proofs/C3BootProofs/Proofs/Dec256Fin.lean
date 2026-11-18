import C3BootProofs.Proofs.Dec256Main

/-!
# P-256 point decompression: the final squaring

After the exponentiation, `decompress` squares `β = α^((p + 1) / 4)` to
check it against `α`. That squaring is another inlined copy of
`mul_montgomery_form::<8>`, which unlike the exponentiation's reads the
Montgomery factor from the parameters and loads both operands through one
pointer. This file proves it over the arithmetic lemmas of `MontMul12.lean`
and `MontMul8.lean`.
-/

namespace C3.RV32.Gd

open C3.Image C3.RV32.Dq

set_option maxRecDepth 20000

/-- The inner loop's body in the final squaring: the operand's limb is read
0x20 bytes below the modulus's. -/
def gfBody : List BInstr :=
  [.lw a0 (8 : Fin 32) 0xFFFFFFE0, .lw a3 (8 : Fin 32) 0, .alu .mul a5 a0 (31 : Fin 32), .alu .mulhu a4 a3 (21 : Fin 32),
   .alu .mul a3 a3 (21 : Fin 32), .lw (9 : Fin 32) a1 0, .alu .mulhu a0 a0 (31 : Fin 32), .alu .add a4 a4 (22 : Fin 32),
   .alu .add (9 : Fin 32) (9 : Fin 32) a5, .alu .add a2 a2 a3, .alu .sltu a5 (9 : Fin 32) a5, .alu .sltu a3 a2 a3,
   .alu .add (9 : Fin 32) (9 : Fin 32) a2, .alu .add a0 a0 a5, .alu .add a3 a3 a4, .alu .sltu a2 (9 : Fin 32) a2,
   .alu .add a0 a0 a3, .aluImm .add (8 : Fin 32) (8 : Fin 32) 4, .alu .add a2 a2 a0, .alu .sltu (22 : Fin 32) a0 a3,
   .alu .sltu a0 a2 a0, .sw a1 (9 : Fin 32) 0xFFFFFFFC, .alu .add (22 : Fin 32) (22 : Fin 32) a0, .aluImm .add a1 a1 4,
   .aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFFFF]

theorem gfBody_end : blockEnd p256DecompressCode 0x5EA gfBody = some 0x632 := by decide

/-- `mmCols` with the high carry summed the other way round, as the final
squaring computes it. -/
def gfCols (N Y O U X CL CH : Word) : Word × Word × Word :=
  let th0 := aluEval .mulhu N U
  let tl0 := aluEval .mul Y X
  let tn1 := aluEval .mul N U
  let ty1 := aluEval .mulhu Y X
  let th1 := aluEval .add th0 CH
  let ta1 := aluEval .add O tl0
  let cl1 := aluEval .add CL tn1
  let tl1 := aluEval .sltu ta1 tl0
  let tn2 := aluEval .sltu cl1 tn1
  let ta2 := aluEval .add ta1 cl1
  let ty2 := aluEval .add ty1 tl1
  let th2 := aluEval .add tn2 th1
  let cl2 := aluEval .sltu ta2 cl1
  let ty3 := aluEval .add ty2 th2
  let cl3 := aluEval .add cl2 ty3
  let ch1 := aluEval .sltu ty3 th2
  let th3 := aluEval .sltu cl3 ty3
  (ta2, cl3, aluEval .add ch1 th3)

theorem gfCols_eq (N Y O U X CL CH : Word) : gfCols N Y O U X CL CH = mmCols N Y O U X CL CH := by
  simp only [gfCols, mmCols]
  generalize aluEval .sltu (aluEval .add CL (aluEval .mul N U)) (aluEval .mul N U) = tn2
  generalize aluEval .add (aluEval .mulhu N U) CH = th1
  rw [show aluEval .add tn2 th1 = aluEval .add th1 tn2 from BitVec.add_comm _ _]

set_option maxRecDepth 20000 in
theorem gfBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock gfBody (M, f)).1 = memStore32 M (f a1 + 0xFFFFFFFC)
        (mmCols (memLoad32 M (f (8 : Fin 32) + 0)) (memLoad32 M (f (8 : Fin 32) + 0xFFFFFFE0)) (memLoad32 M (f a1 + 0))
          (f (21 : Fin 32)) (f (31 : Fin 32)) (f a2) (f (22 : Fin 32))).1 ∧
    (runBlock gfBody (M, f)).2 a2 = (mmCols (memLoad32 M (f (8 : Fin 32) + 0))
        (memLoad32 M (f (8 : Fin 32) + 0xFFFFFFE0)) (memLoad32 M (f a1 + 0)) (f (21 : Fin 32)) (f (31 : Fin 32)) (f a2)
        (f (22 : Fin 32))).2.1 ∧
    (runBlock gfBody (M, f)).2 (22 : Fin 32) = (mmCols (memLoad32 M (f (8 : Fin 32) + 0))
        (memLoad32 M (f (8 : Fin 32) + 0xFFFFFFE0)) (memLoad32 M (f a1 + 0)) (f (21 : Fin 32)) (f (31 : Fin 32)) (f a2)
        (f (22 : Fin 32))).2.2 ∧
    (runBlock gfBody (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 4 ∧
    (runBlock gfBody (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock gfBody (M, f)).2 (23 : Fin 32) = f (23 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (8 : Fin 32) → q ≠ a1 → q ≠ a2 → q ≠ (22 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ a0 → q ≠ a3 → q ≠ a4 →
      q ≠ a5 → q ≠ (9 : Fin 32) → (runBlock gfBody (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, gfBody]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q8 q11 q12 q22 q23 q10 q13 q14 q15 q9 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rw [← gfCols_eq]; rfl
  · simp +decide only [upd, ↓reduceIte]; rw [← gfCols_eq]; rfl
  · simp +decide only [upd, ↓reduceIte]; rw [← gfCols_eq]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, q8, q11, q12, q22, q23, q10, q13, q14, q15, q9]

/-- The registers the loop body leaves alone. -/
def gfBodyKeep (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15, 22, 23]

theorem gfBody_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hy : (f (8 : Fin 32) + 0xFFFFFFE0).toNat % 4 = 0) (hn : (f (8 : Fin 32) + 0).toNat % 4 = 0)
    (ho : (f a1 + 0).toNat % 4 = 0) (hs : (f a1 + 0xFFFFFFFC).toNat % 4 = 0)
    (hsep : Sep (f a1 + 0xFFFFFFFC) 4 base len) : BlockOk base len gfBody (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, gfBody, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hy, hn, ho, hs, hsep⟩

theorem yoff (yp : Word) (c : Nat) : yp + 0x20 + BitVec.ofNat 32 c + 0xFFFFFFE0 = yp + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 c), ← BitVec.add_assoc 0x20,
    show (0x20 : Word) + 0xFFFFFFE0 = 0#32 from rfl, BitVec.zero_add]

/-- **One pass of the inner loop**, from 0x5EA: column `k + 1` of a pass,
which stores the accumulator's word `k`. -/
theorem gf_iter {M : Word → BitVec 8} {B yp acc U X CL CH : Word} {n : Machine} {k : Nat}
    (s : St M B n 0x5EA (reg n)) (hc : CodeIn M B p256DecompressCode) (hk : k < 7)
    (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hS : Sep (acc + BitVec.ofNat 32 (4 * k)) 4 B p256DecompressCode.length)
    (r8 : reg n (8 : Fin 32) = yp + 0x20 + BitVec.ofNat 32 (4 * (k + 1)))
    (r11 : reg n a1 = acc + BitVec.ofNat 32 (4 * (k + 1)))
    (r21 : reg n (21 : Fin 32) = U) (r31 : reg n (31 : Fin 32) = X) (r12 : reg n a2 = CL)
    (r22 : reg n (22 : Fin 32) = CH) (r23 : reg n (23 : Fin 32) = BitVec.ofNat 32 (7 - k)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (acc + BitVec.ofNat 32 (4 * k))
        (mmCols (memLoad32 M (yp + 0x20 + BitVec.ofNat 32 (4 * (k + 1))))
          (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1))))
          (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) U X CL CH).1)
        B n' (if k + 1 < 7 then 0x5EA else 0x636) (reg n') ∧
      reg n' a2 = (mmCols (memLoad32 M (yp + 0x20 + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.1 ∧
      reg n' (22 : Fin 32) = (mmCols (memLoad32 M (yp + 0x20 + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.2 ∧
      reg n' (8 : Fin 32) = yp + 0x20 + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a1 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (23 : Fin 32) = BitVec.ofNat 32 (7 - (k + 1)) ∧
      ∀ q, gfBodyKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hy8 : reg n (8 : Fin 32) + 0xFFFFFFE0 = yp + BitVec.ofNat 32 (4 * (k + 1)) := by rw [r8, yoff]
  have hnp : (yp + 0x20).toNat % 4 = 0 := aligned_add hyp (by decide)
  have ok := gfBody_ok (M := M) (f := reg n) (base := B) (len := p256DecompressCode.length)
    (by rw [hy8]; exact aligned_add hyp (by omega))
    (by rw [r8, add_lit_zero]; exact aligned_add hnp (by omega))
    (by rw [r11, add_lit_zero]; exact aligned_add hacc (by omega))
    (by rw [r11, back4 acc k]; exact aligned_add hacc (by omega))
    (by rw [r11, back4 acc k]; exact hS)
  obtain ⟨n1, c1, u1⟩ := St.block gfBody s hc gfBody_end ok
  obtain ⟨em, e12, e22, e8, e11, e23, fr⟩ := gfBody_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [em, hy8, r8, r11, r21, r31, r12, r22, add_lit_zero, add_lit_zero, back4 acc k] at u1'
  have g : ∀ q, reg n1 q = (runBlock gfBody (M, reg n)).2 q := u1.regs
  have hb : branchTaken .bne (reg n1 (23 : Fin 32)) (reg n1 x0) = decide (k + 1 < 7) := by
    rw [g, e23, r23, cnt7_dec k hk, u1'.zero]; exact cnt7_ne k hk
  have hc1 := CodeIn.store32 (v := (mmCols (memLoad32 M (yp + 0x20 + BitVec.ofNat 32 (4 * (k + 1))))
    (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
    U X CL CH).1) hc hS
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a2 = (mmCols (memLoad32 M (yp + 0x20 + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.1 ∧
      reg n2 (22 : Fin 32) = (mmCols (memLoad32 M (yp + 0x20 + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.2 ∧
      reg n2 (8 : Fin 32) = yp + 0x20 + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 a1 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 (23 : Fin 32) = BitVec.ofNat 32 (7 - (k + 1)) ∧
      ∀ q, gfBodyKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [h2, g, e12, hy8, r8, r11, r21, r31, r12, r22, add_lit_zero, add_lit_zero]
    · rw [h2, g, e22, hy8, r8, r11, r21, r31, r12, r22, add_lit_zero, add_lit_zero]
    · rw [h2, g, e8, r8, ptr4]
    · rw [h2, g, e11, r11, ptr4]
    · rw [h2, g, e23, r23, cnt7_dec k hk]
    · rw [h2, g]
      exact fr q (pkeep_ne (r := 8) hq rfl) (pkeep_ne (r := a1) hq rfl) (pkeep_ne (r := a2) hq rfl)
        (pkeep_ne (r := 22) hq rfl) (pkeep_ne (r := 23) hq rfl) (pkeep_ne (r := a0) hq rfl)
        (pkeep_ne (r := a3) hq rfl) (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a5) hq rfl)
        (pkeep_ne (r := 9) hq rfl)
  by_cases hl : k + 1 < 7
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x5EA gd_at_632 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0x636 gd_at_632 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The inner loop**, from column `k + 1` of a pass to its end at 0x636:
columns `k + 1..7` of the pass. -/
theorem gf_inner {B acc yp U X : Word} {M0 : Word → BitVec 8}
    (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0) (hw : acc.toNat + 32 ≤ 2 ^ 32)
    (hAY : Sep acc 32 yp 32) (hAN : Sep acc 32 (yp + 0x20) 32) (hAC : Sep acc 32 B p256DecompressCode.length) :
    ∀ m k, k + m + 1 = 7 → ∀ {M : Word → BitVec 8} {n : Machine} {CL CH : Word},
      St M B n 0x5EA (reg n) → CodeIn M B p256DecompressCode →
      (∀ a, Sep acc 32 a 1 → M a = M0 a) →
      (∀ i, k ≤ i → i < 8 →
        memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) →
      2 ^ 32 * accV M acc k + (CL.toNat + 2 ^ 32 * CH.toNat) * 2 ^ (32 * (k + 1)) =
        X.toNat * accV M0 yp (k + 1) + accV M0 acc (k + 1) + U.toNat * accV M0 (yp + 0x20) (k + 1) →
      CL.toNat + 2 ^ 32 * CH.toNat ≤ 2 * 2 ^ 32 - 2 →
      reg n (8 : Fin 32) = yp + 0x20 + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a1 = acc + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n (21 : Fin 32) = U → reg n (31 : Fin 32) = X → reg n a2 = CL → reg n (22 : Fin 32) = CH →
      reg n (23 : Fin 32) = BitVec.ofNat 32 (7 - k) →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x636 (reg n') ∧ CodeIn M' B p256DecompressCode ∧
        2 ^ 32 * accV M' acc 7 + ((reg n' a2).toNat + 2 ^ 32 * (reg n' (22 : Fin 32)).toNat) * 2 ^ (32 * 8) =
          X.toNat * accV M0 yp 8 + accV M0 acc 8 + U.toNat * accV M0 (yp + 0x20) 8 ∧
        (reg n' a2).toNat + 2 ^ 32 * (reg n' (22 : Fin 32)).toNat ≤ 2 * 2 ^ 32 - 2 ∧
        (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
        memLoad32 M' (acc + BitVec.ofNat 32 (4 * 7)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * 7)) ∧
        reg n' (8 : Fin 32) = yp + 0x20 + BitVec.ofNat 32 (4 * 8) ∧
        reg n' a1 = acc + BitVec.ofNat 32 (4 * 8) ∧
        reg n' (23 : Fin 32) = 0 ∧
        ∀ q, gfBodyKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r8 r11 r21 r31 r12 r22 r23
    have k10 : k = 6 := by omega
    subst k10
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (yp + 0x20 + BitVec.ofNat 32 (4 * (6 + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (6 + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (6 + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e12, e22, e8, e11, e23, fr⟩ := gf_iter (k := 6) s hc (by decide) hyp hacc
      (hAC.sub (by omega)) r8 r11 r21 r31 r12 r22 r23
    rw [hcol] at u1 e12 e22
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step8 (k := 6) (by decide) hw hAY hAN hfr hab hinv hbd hcol
    refine ⟨n1, _, c1, u1, CodeIn.store32 hc (hAC.sub (by omega)), ?_, ?_, i3, i4 7 (by decide) (by decide),
      e8, e11, e23, fr⟩
    · rw [e12, e22, show (8 : Nat) = 6 + 2 from rfl]; exact i1
    · rw [e12, e22]; exact i2
  | succ m ih =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r8 r11 r21 r31 r12 r22 r23
    have hl : k + 1 < 7 := by omega
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (yp + 0x20 + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e12, e22, e8, e11, e23, fr⟩ := gf_iter (k := k) s hc (by omega) hyp hacc
      (hAC.sub (by omega)) r8 r11 r21 r31 r12 r22 r23
    rw [hcol] at u1 e12 e22
    rw [ite_eq_left hl] at u1
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step8 (k := k) (by omega) hw hAY hAN hfr hab hinv hbd hcol
    have k7 : reg n1 (21 : Fin 32) = U := by rw [fr _ rfl, r21]
    have k6 : reg n1 (31 : Fin 32) = X := by rw [fr _ rfl, r31]
    obtain ⟨n', M', c', u', hc', f1, f2, f3, f4, f8, f11, f23, fr'⟩ :=
      ih (k + 1) (by omega) u1 (CodeIn.store32 hc (hAC.sub (by omega))) i3 i4 i1 i2 e8 e11 k7 k6 e12 e22 e23
    exact ⟨n', M', c1.trans c', u', hc', f1, f2, f3, f4, f8, f11, f23,
      fun q hq => by rw [fr' q hq, fr q hq]⟩

theorem neg_m1_mul (a : Word) : aluEval .sub 0 (aluEval .mul 0xFFFFFFFF a) = aluEval .mul 1 a := by
  show 0 - 0xFFFFFFFF * a = 1 * a
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_mul, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl,
    show (0 : Word).toNat = 0 from rfl, show (1 : Word).toNat = 1 from rfl]
  have := a.isLt; omega

/-- The first column of a pass as the final squaring computes it: the factor
`u = -(k · t)` from the Montgomery constant `k` it reads, then the two-word
carry out. -/
def gfHead (Y0 X O0 K N0 : Word) : Word × Word × Word :=
  let a0 := aluEval .mul Y0 X
  let a1 := aluEval .add O0 a0
  let u := aluEval .sub 0 (aluEval .mul K a1)
  let a2 := aluEval .mulhu Y0 X
  let a3 := aluEval .mul u N0
  let s1 := aluEval .mulhu u N0
  let c1 := aluEval .sltu a1 a0
  let h1 := aluEval .add c1 a2
  let lo := aluEval .add a1 a3
  let h2 := aluEval .add h1 s1
  let c2 := aluEval .sltu lo a3
  let cl := aluEval .add c2 h2
  let o1 := aluEval .sltu h2 s1
  let o2 := aluEval .sltu cl h2
  (u, cl, aluEval .add o1 o2)

theorem gfHead_eq (Y0 X O0 N0 : Word) : gfHead Y0 X O0 0xFFFFFFFF N0 = mmHead Y0 X O0 1 N0 := by
  simp only [gfHead, mmHead, neg_m1_mul]

def gfHeadBlock : List BInstr :=
  [.aluImm .sll a1 (30 : Fin 32) 0x2, .alu .add a1 a1 (5 : Fin 32), .lw (31 : Fin 32) a1 0x0,
   .alu .mul a1 (7 : Fin 32) (31 : Fin 32), .lw a2 sp 0x1DC, .alu .add a2 a2 a1, .alu .mul a4 (18 : Fin 32) a2,
   .alu .sub (21 : Fin 32) x0 a4, .alu .mulhu a4 (7 : Fin 32) (31 : Fin 32), .alu .mul (9 : Fin 32) (21 : Fin 32) (28 : Fin 32),
   .alu .mulhu (8 : Fin 32) (21 : Fin 32) (28 : Fin 32), .alu .sltu a1 a2 a1, .alu .add a1 a1 a4,
   .alu .add a2 a2 (9 : Fin 32), .alu .add a1 a1 (8 : Fin 32), .alu .sltu a2 a2 (9 : Fin 32), .alu .add a2 a2 a1,
   .alu .sltu a4 a1 (8 : Fin 32), .alu .sltu a1 a2 a1, .aluImm .add (23 : Fin 32) x0 0x7, .alu .add (22 : Fin 32) a4 a1,
   .alu .add a1 x0 (17 : Fin 32), .alu .add (8 : Fin 32) x0 (16 : Fin 32)]

def gfTailBlock : List BInstr :=
  [.alu .add (19 : Fin 32) (19 : Fin 32) a2, .alu .add a4 (22 : Fin 32) (29 : Fin 32), .alu .sltu a1 (19 : Fin 32) a2,
   .sw sp (19 : Fin 32) 0x1F8, .alu .add (19 : Fin 32) a4 a1, .aluImm .add (30 : Fin 32) (30 : Fin 32) 0x1,
   .aluImm .add (29 : Fin 32) x0 0x0]

theorem gfHeadBlock_end : blockEnd p256DecompressCode 0x59C gfHeadBlock = some 0x5E6 := by decide
theorem gfTailBlock_end : blockEnd p256DecompressCode 0x636 gfTailBlock = some 0x64C := by decide

/-- The registers the start of a pass leaves alone. -/
def gfHeadKeep (q : Fin 32) : Bool := q.val ∉ [8, 9, 11, 12, 14, 21, 22, 23, 31]

set_option maxRecDepth 20000 in
theorem gfHeadBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock gfHeadBlock (M, f)).1 = M ∧
    (runBlock gfHeadBlock (M, f)).2 (31 : Fin 32) =
      memLoad32 M (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (5 : Fin 32)) + 0) ∧
    (runBlock gfHeadBlock (M, f)).2 (21 : Fin 32) = (gfHead (f (7 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (5 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0x1DC)) (f (18 : Fin 32)) (f (28 : Fin 32))).1 ∧
    (runBlock gfHeadBlock (M, f)).2 a2 = (gfHead (f (7 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (5 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0x1DC)) (f (18 : Fin 32)) (f (28 : Fin 32))).2.1 ∧
    (runBlock gfHeadBlock (M, f)).2 (22 : Fin 32) = (gfHead (f (7 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (5 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0x1DC)) (f (18 : Fin 32)) (f (28 : Fin 32))).2.2 ∧
    (runBlock gfHeadBlock (M, f)).2 (23 : Fin 32) = BitVec.ofNat 32 (7 - 0) ∧
    (runBlock gfHeadBlock (M, f)).2 a1 = f (17 : Fin 32) ∧
    (runBlock gfHeadBlock (M, f)).2 (8 : Fin 32) = f (16 : Fin 32) ∧
    ∀ q, gfHeadKeep q = true → (runBlock gfHeadBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, gfHeadBlock]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a1) hq rfl,
        pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a4) hq rfl, pkeep_ne (r := 21) hq rfl, pkeep_ne (r := 22) hq rfl,
        pkeep_ne (r := 23) hq rfl, pkeep_ne (r := 31) hq rfl]

theorem gfHeadBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hx : (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (5 : Fin 32)) + 0).toNat % 4 = 0)
    (hs : (f sp + 0x1DC).toNat % 4 = 0) : BlockOk base len gfHeadBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, gfHeadBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hx, hs⟩

/-- The registers the end of a pass leaves alone. -/
def gfTailKeep (q : Fin 32) : Bool := q.val ∉ [11, 14, 19, 29, 30]

set_option maxRecDepth 20000 in
theorem gfTailBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock gfTailBlock (M, f)).1 = memStore32 M (f sp + 0x1F8) (aluEval .add (f (19 : Fin 32)) (f a2)) ∧
    (runBlock gfTailBlock (M, f)).2 (19 : Fin 32) = aluEval .add (aluEval .add (f (22 : Fin 32)) (f (29 : Fin 32)))
      (aluEval .sltu (aluEval .add (f (19 : Fin 32)) (f a2)) (f a2)) ∧
    (runBlock gfTailBlock (M, f)).2 (30 : Fin 32) = f (30 : Fin 32) + 1 ∧
    (runBlock gfTailBlock (M, f)).2 (29 : Fin 32) = 0 ∧
    ∀ q, gfTailKeep q = true → (runBlock gfTailBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, gfTailBlock]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a4) hq rfl,
        pkeep_ne (r := 19) hq rfl, pkeep_ne (r := 29) hq rfl, pkeep_ne (r := 30) hq rfl]

theorem gfTailBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hs : (f sp + 0x1F8).toNat % 4 = 0) (hsep : Sep (f sp + 0x1F8) 4 base len) :
    BlockOk base len gfTailBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, gfTailBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hs, hsep⟩

/-- The registers a pass leaves alone. -/
def gfPassKeep (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15, 19, 21, 22, 23, 29, 30, 31]

theorem gfPassKeep_head : ∀ q, gfPassKeep q = true → gfHeadKeep q = true := by decide
theorem gfPassKeep_body : ∀ q, gfPassKeep q = true → gfBodyKeep q = true := by decide
theorem gfPassKeep_tail : ∀ q, gfPassKeep q = true → gfTailKeep q = true := by decide

set_option exponentiation.threshold 400 in
/-- **One pass of the outer loop**, from 0x59C: add limb `i` of the operand
times the operand, and `u` times the modulus, to the accumulator and its top
carry in `s3`, and shift the sum down a word. -/
theorem gf_pass {B acc xp : Word} {M0 : Word → BitVec 8} {i : Nat} (hi : i < 8)
    (hxp : xp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAX : Sep acc 32 xp 32) (hAN : Sep acc 32 (xp + 0x20) 32)
    (hAC : Sep acc 32 B p256DecompressCode.length) (hN0 : memLoad32 M0 (xp + 0x20) = 0xFFFFFFFF)
    {M : Word → BitVec 8} {n : Machine} (s : St M B n 0x59C (reg n)) (hc : CodeIn M B p256DecompressCode)
    (hfr : ∀ a, Sep acc 32 a 1 → M a = M0 a)
    (r30 : reg n (30 : Fin 32) = BitVec.ofNat 32 i) (r5 : reg n (5 : Fin 32) = xp)
    (r7 : reg n (7 : Fin 32) = memLoad32 M0 xp) (r28 : reg n (28 : Fin 32) = 0xFFFFFFFF)
    (r18 : reg n (18 : Fin 32) = 0xFFFFFFFF) (rsp : reg n sp + 0x1DC = acc)
    (r16 : reg n a6 = xp + 0x20 + BitVec.ofNat 32 (4 * (0 + 1)))
    (r17 : reg n (17 : Fin 32) = acc + BitVec.ofNat 32 (4 * (0 + 1)))
    (r29 : reg n (29 : Fin 32) = 0) (r6 : reg n (6 : Fin 32) = 8) :
    ∃ n' M', Steps n n' ∧ St M' B n' (if i + 1 < 8 then 0x59C else 0x650) (reg n') ∧
      CodeIn M' B p256DecompressCode ∧ (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
      (∃ u : Nat, u < 2 ^ 32 ∧ 2 ^ 32 * (accV M' acc 8 + (reg n' (19 : Fin 32)).toNat * 2 ^ (32 * 8)) =
        accV M acc 8 + (reg n (19 : Fin 32)).toNat * 2 ^ (32 * 8) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 xp 8 + u * accV M0 (xp + 0x20) 8) ∧
      reg n' (30 : Fin 32) = BitVec.ofNat 32 (i + 1) ∧ reg n' (29 : Fin 32) = 0 ∧
      ∀ q, gfPassKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hX : aluEval .add (aluEval .sll (reg n (30 : Fin 32)) 2) (reg n (5 : Fin 32)) + 0 =
      xp + BitVec.ofNat 32 (4 * i) := by
    rw [r30, r5, sll8 i hi, add_lit_zero]; exact BitVec.add_comm _ _
  have ok1 := gfHeadBlock_ok (M := M) (f := reg n) (base := B) (len := p256DecompressCode.length)
    (by rw [hX]; exact aligned_add hxp (by omega)) (by rw [rsp]; exact hacc)
  obtain ⟨n1, c1, u1⟩ := St.block gfHeadBlock s hc gfHeadBlock_end ok1
  obtain ⟨hm1, h6, h7, h9, h28, h29, h30, h10, hfr1⟩ := gfHeadBlock_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [hm1] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock gfHeadBlock (M, reg n)).2 q := u1.regs
  rw [hX] at h6 h7 h9 h28
  rw [rsp, r7, r18, r28, gfHead_eq] at h7 h9 h28
  have eX : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
    load_frame hfr (hAX.subR (by omega))
  obtain ⟨u, cl, ch, hH⟩ : ∃ u cl ch, mmHead (memLoad32 M0 xp) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
      (memLoad32 M acc) 1 0xFFFFFFFF = (u, cl, ch) := ⟨_, _, _, rfl⟩
  have hd := mm_head (memLoad32 M0 xp) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) (memLoad32 M acc) 1
    0xFFFFFFFF (by decide)
  rw [hH] at hd h7 h9 h28
  simp only at hd h7 h9 h28
  obtain ⟨hd, bd⟩ := hd
  have hb : branchTaken .beq (reg n1 (23 : Fin 32)) (reg n1 x0) = false := by
    rw [g1, h29, u1'.zero]; decide
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc 0x5EA gd_at_5e6 (by decide) hb
  have g2 : ∀ q, reg n2 q = (runBlock gfHeadBlock (M, reg n)).2 q := fun q => by rw [u2.regs, g1]
  have eY0 : memLoad32 M (xp + BitVec.ofNat 32 (4 * 0)) = memLoad32 M0 xp := by
    rw [load_frame hfr (hAX.subR (c := 4 * 0) (l := 4) (by omega)), Nat.mul_zero, add_ofNat_zero]
  have eN0 : memLoad32 M (xp + 0x20 + BitVec.ofNat 32 (4 * 0)) = 0xFFFFFFFF := by
    rw [load_frame hfr (hAN.subR (c := 4 * 0) (l := 4) (by omega)), Nat.mul_zero, add_ofNat_zero, hN0]
  have eO0 : memLoad32 M (acc + BitVec.ofNat 32 (4 * 0)) = memLoad32 M acc := by
    rw [Nat.mul_zero, add_ofNat_zero]
  have inv0 : 2 ^ 32 * accV M acc 0 + (cl.toNat + 2 ^ 32 * ch.toNat) * 2 ^ (32 * (0 + 1)) =
      (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M xp (0 + 1) + accV M acc (0 + 1) +
        u.toNat * accV M (xp + 0x20) (0 + 1) := by
    show 2 ^ 32 * 0 + _ * 2 ^ 32 = _ * (0 + (memLoad32 M (xp + BitVec.ofNat 32 (4 * 0))).toNat * 1) +
      (0 + (memLoad32 M (acc + BitVec.ofNat 32 (4 * 0))).toNat * 1) +
      _ * (0 + (memLoad32 M (xp + 0x20 + BitVec.ofNat 32 (4 * 0))).toNat * 1)
    rw [eY0, eN0, eO0]
    simp only [Nat.zero_add, Nat.mul_one, Nat.mul_zero]
    omega
  obtain ⟨n3, M1, c3, u3, hc3, I1, I2, I3, I4, f8, f11, f23, fr3⟩ :=
    gf_inner (M0 := M) (U := u) (X := memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) hxp hacc hw hAX hAN hAC
      6 0 (by decide) u2.self hc (fun _ _ => rfl) (fun _ _ _ => rfl) inv0 bd
      (by rw [g2, h10, r16]) (by rw [g2, h30, r17]) (by rw [g2, h7]) (by rw [g2, h6])
      (by rw [g2, h9]) (by rw [g2, h28]) (by rw [g2, h29])
  have k3 : ∀ q, gfPassKeep q = true → reg n3 q = reg n q := fun q hq => by
    rw [fr3 q (gfPassKeep_body q hq), g2, hfr1 q (gfPassKeep_head q hq)]
  have hb3 : ∀ q, gfHeadKeep q = true → gfBodyKeep q = true → reg n3 q = reg n q := fun q h1 h2 => by
    rw [fr3 q h2, g2, hfr1 q h1]
  have s25 : reg n3 sp + 0x1F8 = acc + BitVec.ofNat 32 (4 * 7) := by rw [k3 sp rfl, ← rsp, BitVec.add_assoc]; rfl
  have ok3 := gfTailBlock_ok (M := M1) (f := reg n3) (base := B) (len := p256DecompressCode.length)
    (by rw [s25]; exact aligned_add hacc (by omega)) (by rw [s25]; exact hAC.sub (by omega))
  obtain ⟨n4, c4, u4⟩ := St.block gfTailBlock u3 hc3 gfTailBlock_end ok3
  obtain ⟨hm4, t27, t5, t17, tfr⟩ := gfTailBlock_run (M := M1) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [hm4, s25] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock gfTailBlock (M1, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := aluEval .add (reg n3 (19 : Fin 32)) (reg n3 a2)) hc3
    (hAC.sub (c := 4 * 7) (by omega))
  have e5 : reg n4 (30 : Fin 32) = BitVec.ofNat 32 (i + 1) := by
    rw [g4, t5, hb3 (30 : Fin 32) rfl rfl, r30, ofNat_succ]
  have e17 : reg n4 (29 : Fin 32) = 0 := by rw [g4, t17]
  have k4 : ∀ q, gfPassKeep q = true → reg n4 q = reg n q := fun q hq => by
    rw [g4, tfr q (gfPassKeep_tail q hq), k3 q hq]
  have hb4 : branchTaken .bne (reg n4 (30 : Fin 32)) (reg n4 (6 : Fin 32)) = decide (i + 1 < 8) := by
    rw [e5, k4 _ rfl, r6]; exact pass_ne8 i hi
  have arith : 2 ^ 32 * (accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 7))
        (aluEval .add (reg n3 (19 : Fin 32)) (reg n3 a2))) acc 8 + (reg n4 (19 : Fin 32)).toNat * 2 ^ (32 * 8)) =
      accV M acc 8 + (reg n (19 : Fin 32)).toNat * 2 ^ (32 * 8) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 xp 8 + u.toNat * accV M0 (xp + 0x20) 8 := by
    have hA : accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 7)) (aluEval .add (reg n3 (19 : Fin 32)) (reg n3 a2)))
        acc 8 = accV M1 acc 7 + (aluEval .add (reg n3 (19 : Fin 32)) (reg n3 a2)).toNat * 2 ^ (32 * 7) := by
      rw [show (8 : Nat) = 7 + 1 from rfl, accV_succ1, accV_store_above (by omega) 7 (Nat.le_refl 7),
        memLoad32_store32_same]
    have ac := add_carry (reg n3 (19 : Fin 32)) (reg n3 a2)
    have hch : (reg n3 (22 : Fin 32)).toNat ≤ 1 := by omega
    have hcy : (aluEval .sltu (aluEval .add (reg n3 (19 : Fin 32)) (reg n3 a2)) (reg n3 a2)).toNat ≤ 1 := by
      have := (reg n3 (19 : Fin 32)).isLt; have := (reg n3 a2).isLt; omega
    have h27 : (reg n4 (19 : Fin 32)).toNat = (reg n3 (22 : Fin 32)).toNat +
        (aluEval .sltu (aluEval .add (reg n3 (19 : Fin 32)) (reg n3 a2)) (reg n3 a2)).toNat := by
      rw [g4, t27, hb3 (29 : Fin 32) rfl rfl, r29, show aluEval .add (reg n3 (22 : Fin 32)) 0 = reg n3 (22 : Fin 32) from
        BitVec.add_zero _, add_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    have p12 : (2 : Nat) ^ (32 * 8) = 2 ^ (32 * 7) * 2 ^ 32 := pow32_succ 7
    rw [eX, accV_frame32 (b := xp) (n := 8) hfr hAX, accV_frame32 (b := xp + 0x20) (n := 8) hfr hAN, p12] at I1
    rw [hA, h27, p12, hb3 (19 : Fin 32) rfl rfl]
    rw [hb3 (19 : Fin 32) rfl rfl] at ac
    exact mm_tail_arith I1 ac
  have fr4 : ∀ a, Sep acc 32 a 1 → memStore32 M1 (acc + BitVec.ofNat 32 (4 * 7))
      (aluEval .add (reg n3 (19 : Fin 32)) (reg n3 a2)) a = M0 a := fun a ha => by
    rw [memStore32_ne fun j hj e => (ha.point (i := 4 * 7 + j) (j := 0) (by omega) (by decide)) (by
      rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm), I3 a ha, hfr a ha]
  by_cases hl : i + 1 < 8
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x59C gd_at_64c (by decide) (by rw [hb4]; exact decide_eq_true hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e5], by rw [g5, e17], fun q hq => by rw [g5, k4 q hq]⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x650 gd_at_64c (by decide) (by rw [hb4]; exact decide_eq_false hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e5], by rw [g5, e17], fun q hq => by rw [g5, k4 q hq]⟩

set_option exponentiation.threshold 400 in
/-- **The outer loop**, from pass `i` to its end at 0x650. The accumulator
and its top carry hold a sum `T` with `2^(32 i) T = X_i X + U N`, for `X_i`
the operand's low `i` limbs and some `U`, and `T < 2N`. -/
theorem gf_outer {B acc xp : Word} {M0 : Word → BitVec 8}
    (hxp : xp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAX : Sep acc 32 xp 32) (hAN : Sep acc 32 (xp + 0x20) 32)
    (hAC : Sep acc 32 B p256DecompressCode.length) (hN0 : memLoad32 M0 (xp + 0x20) = 0xFFFFFFFF)
    (hYN : accV M0 xp 8 < accV M0 (xp + 0x20) 8) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x59C (reg n) → CodeIn M B p256DecompressCode → (∀ a, Sep acc 32 a 1 → M a = M0 a) →
      (∃ U, 2 ^ (32 * i) * (accV M acc 8 + (reg n (19 : Fin 32)).toNat * 2 ^ (32 * 8)) =
        accV M0 xp i * accV M0 xp 8 + U * accV M0 (xp + 0x20) 8) →
      accV M acc 8 + (reg n (19 : Fin 32)).toNat * 2 ^ (32 * 8) < 2 * accV M0 (xp + 0x20) 8 →
      reg n (30 : Fin 32) = BitVec.ofNat 32 i → reg n (5 : Fin 32) = xp →
      reg n (7 : Fin 32) = memLoad32 M0 xp → reg n (28 : Fin 32) = 0xFFFFFFFF → reg n (18 : Fin 32) = 0xFFFFFFFF →
      reg n sp + 0x1DC = acc →
      reg n a6 = xp + 0x20 + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (17 : Fin 32) = acc + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (29 : Fin 32) = 0 → reg n (6 : Fin 32) = 8 →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x650 (reg n') ∧ CodeIn M' B p256DecompressCode ∧
        (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
        (∃ U, 2 ^ (32 * 8) * (accV M' acc 8 + (reg n' (19 : Fin 32)).toNat * 2 ^ (32 * 8)) =
          accV M0 xp 8 * accV M0 xp 8 + U * accV M0 (xp + 0x20) 8) ∧
        accV M' acc 8 + (reg n' (19 : Fin 32)).toNat * 2 ^ (32 * 8) < 2 * accV M0 (xp + 0x20) 8 ∧
        ∀ q, gfPassKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hinv hbd r30 r5 r7 r28 r18 rsp r16 r17 r29 r6
    have i11 : i = 7 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e5, e17, k1⟩ := gf_pass (i := 7) (by decide) hxp hacc
      hw hAX hAN hAC hN0 s hc hfr r30 r5 r7 r28 r18 rsp r16 r17 r29 r6
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * 7))).isLt hu hYN
    refine ⟨n1, M1, c1, u1, hc1, hf1, ⟨U + 2 ^ (32 * 7) * u, ?_⟩, a2, k1⟩
    rw [pow32_succ 7] at a1 ⊢
    rw [a1, accV_succ1 M0 xp 7]
  | succ m ih =>
    intro i hi M n s hc hfr hinv hbd r30 r5 r7 r28 r18 rsp r16 r17 r29 r6
    have hl : i + 1 < 8 := idx_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e5, e17, k1⟩ := gf_pass (i := i)
      (Nat.lt_trans (Nat.lt_succ_self i) hl) hxp hacc hw hAX hAN hAC hN0 s hc hfr r30 r5 r7 r28 r18 rsp r16 r17
      r29 r6
    rw [ite_eq_left hl] at u1
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).isLt hu hYN
    have inv1 : ∃ U, 2 ^ (32 * (i + 1)) * (accV M1 acc 8 + (reg n1 (19 : Fin 32)).toNat * 2 ^ (32 * 8)) =
        accV M0 xp (i + 1) * accV M0 xp 8 + U * accV M0 (xp + 0x20) 8 :=
      ⟨U + 2 ^ (32 * i) * u, by rw [pow32_succ i, a1, accV_succ1 M0 xp i]⟩
    obtain ⟨n', M', c', u', hc', hf', hv', hb', k'⟩ := ih (i + 1) (idx_succ hi) u1 hc1 hf1 inv1 a2 e5
      (by rw [k1 _ rfl, r5]) (by rw [k1 _ rfl, r7]) (by rw [k1 _ rfl, r28]) (by rw [k1 _ rfl, r18])
      (by rw [k1 _ rfl, rsp]) (by rw [k1 _ rfl, r16]) (by rw [k1 _ rfl, r17]) e17 (by rw [k1 _ rfl, r6])
    exact ⟨n', M', c1.trans c', u', hc', hf', hv', hb', fun q hq => by rw [k' q hq, k1 q hq]⟩

end C3.RV32.Gd
