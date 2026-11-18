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

end C3.RV32.Gd
