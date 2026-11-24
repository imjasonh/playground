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

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.P2 C3.RV32.Fs

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

/-! ## The final subtraction -/

/-- The end of a subtraction round, from 0x67A: keep the borrow, store the
difference, and advance the pointers and the count. -/
def gfSubTail : List BInstr :=
  [.alu .add a2 x0 a1, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, .sw (18 : Fin 32) a0 0x0,
   .aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

theorem gfSubTail_end : blockEnd p256DecompressCode 0x67A gfSubTail = some 0x688 := by decide

set_option maxRecDepth 20000 in
theorem gfSubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock gfSubTail (M, f)).1 = memStore32 M (f (18 : Fin 32) + 0) (f a0) ∧
    (runBlock gfSubTail (M, f)).2 a2 = f a1 ∧
    (runBlock gfSubTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock gfSubTail (M, f)).2 (20 : Fin 32) = f (20 : Fin 32) + 4 ∧
    (runBlock gfSubTail (M, f)).2 (18 : Fin 32) = f (18 : Fin 32) + 4 ∧
    (runBlock gfSubTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ (8 : Fin 32) →
      (runBlock gfSubTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, gfSubTail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q26 q8 q23 q24 q9 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q26, q8, q23, q24, q9]

theorem gfSubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (18 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (18 : Fin 32) + 0) 4 base len) :
    BlockOk base len gfSubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, gfSubTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One round of the final subtraction**, from 0x66C: subtract limb `i` of
the modulus and the borrow from limb `i` of the accumulator, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem gf_sub_iter {M : Word → BitVec 8} {F acc np D b : Word} {n : Machine} {i : Nat}
    (s : St M GD n 0x66C (reg n)) (hc : CodeIn M GD p256DecompressCode) (hb : CodeIn M BSUB borrowingSubCode)
    (hi : i < 8) (hF : F.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 BSUB borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 GD p256DecompressCode.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 GD p256DecompressCode.length)
    (rsp : reg n sp = F) (r8 : reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i))
    (r23 : reg n (20 : Fin 32) = np + BitVec.ofNat 32 (4 * i)) (r24 : reg n (18 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (r9 : reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i)) (r26 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b))
        GD n' (if i + 1 < 8 then 0x66C else 0x68A) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
        (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (20 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (18 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) →
        q ≠ (18 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc gd_at_66c (off' := 0x66E) (by decide)
    (by rw [r8, add_lit_zero]; exact aligned_add hacc (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc gd_at_66e (off' := 0x672) (by decide)
    (by rw [upd_ne (by decide) (by decide), r23, add_lit_zero]; exact aligned_add hnp (by omega))
  have e0 : reg n2 a0 = memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]; rw [r8, add_lit_zero]
  have e1 : reg n2 a1 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]; rw [r23, add_lit_zero]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  have e2 : reg n2 a2 = b := by rw [k2 a2 (by decide) (by decide), r26]
  obtain ⟨n4, c4, u4, a04, a14, sp4, fr4, mem4⟩ := u2.self.bsubCall hc hb (by decide)
    gd_at_672 gd_at_676 (by decide) (by decide)
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [e0, e1, e2] at a04 a14
  have hc4 : CodeIn n4.mem GD p256DecompressCode := fun j hj => by
    rw [mem4 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n4 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr4 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have e24 : reg n4 (18 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r24, add_lit_zero]
  obtain ⟨n5, c5, u5⟩ := St.block gfSubTail u4 hc4 gfSubTail_end
    (gfSubTail_ok (by rw [e24]; exact aligned_add hD (by omega)) (by rw [e24]; exact sDC))
  obtain ⟨em5, t26, t8, t23, t24, t9, tk⟩ := gfSubTail_run (M := n4.mem) (f := reg n4) u4.zero
  have u5' := u5.self
  rw [em5, e24, a04] at u5'
  have g5 : ∀ q, reg n5 q = (runBlock gfSubTail (n4.mem, reg n4)).2 q := u5.regs
  have hc5 := CodeIn.store32 (v := bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) hc4 sDC
  have e9 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) := by
    rw [g5, t9, k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9, cnt8_dec i hi]
  have hb5 : branchTaken .bne (reg n5 (8 : Fin 32)) (reg n5 x0) = decide (i + 1 < 8) := by
    rw [e9, u5'.zero]; exact cnt8_ne i hi
  have post : ∀ n6 : Machine, (∀ q, reg n6 q = reg n5 q) →
      reg n6 a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
        (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n6 sp = F ∧ reg n6 (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n6 (20 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n6 (18 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n6 (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) →
        q ≠ (18 : Fin 32) → q ≠ (8 : Fin 32) → reg n6 q = reg n q := fun n6 h6 => by
    refine ⟨by rw [h6, g5, t26, a14],
      by rw [h6, g5, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp4], ?_, ?_, ?_, by rw [h6, e9],
      fun q q0 q1 q2 q3 q4 qr q8 q23 q24 q9 => ?_⟩
    · rw [h6, g5, t8, k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, ptr4]
    · rw [h6, g5, t23, k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r23, ptr4]
    · rw [h6, g5, t24, k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r24, ptr4]
    · rw [h6, g5, tk q q2 q8 q23 q24 q9, k4 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 8
  · obtain ⟨n6, d6, u6⟩ := u5'.taken hc5 0x66C gd_at_688 (by decide) (by rw [hb5]; exact decide_eq_true hl)
    exact ⟨n6, n4.mem, .cons d1 (.cons d2 (c4.trans (c5.trans (.single d6)))), by rw [ite_eq_left hl]; exact u6.self,
      mem4, post n6 u6.regs⟩
  · obtain ⟨n6, d6, u6⟩ := u5'.notTaken hc5 0x68A gd_at_688 (by decide) (by rw [hb5]; exact decide_eq_false hl)
    exact ⟨n6, n4.mem, .cons d1 (.cons d2 (c4.trans (c5.trans (.single d6)))), by rw [ite_eq_right hl]; exact u6.self,
      mem4, post n6 u6.regs⟩

set_option exponentiation.threshold 400 in
/-- **The final subtraction**, from round `i` to its end at 0x68A: the
buffer at `D` gets the accumulator minus the modulus, and `a2` the borrow
out as a mask. -/
theorem gf_sub_loop {F acc np D : Word} {M0 : Word → BitVec 8} (hF : F.toNat % 4 = 0)
    (hacc : acc.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 32 ≤ 2 ^ 32)
    (sFA : Sep (F + 0xFFFFFFFC) 4 acc 32) (sFN : Sep (F + 0xFFFFFFFC) 4 np 32) (sFD : Sep (F + 0xFFFFFFFC) 4 D 32)
    (sDA : Sep D 32 acc 32) (sDN : Sep D 32 np 32)
    (sFB : Sep (F + 0xFFFFFFFC) 4 BSUB borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 GD p256DecompressCode.length)
    (sDB : Sep D 32 BSUB borrowingSubCode.length) (sDC : Sep D 32 GD p256DecompressCode.length) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M GD n 0x66C (reg n) → CodeIn M GD p256DecompressCode → CodeIn M BSUB borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (20 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (18 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' GD n' 0x68A (reg n') ∧ CodeIn M' GD p256DecompressCode ∧
        CodeIn M' BSUB borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc 8 + 2 ^ (32 * 8) * maskBit (reg n' a2) = accV M0 np 8 + accV M' D 8 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) →
          q ≠ (18 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M GD n 0x66C (reg n) → CodeIn M GD p256DecompressCode → CodeIn M BSUB borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (20 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (18 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' GD n' (if i + 1 < 8 then 0x66C else 0x68A) (reg n') ∧
        CodeIn M' GD p256DecompressCode ∧ CodeIn M' BSUB borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) =
          accV M0 np (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (20 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (18 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) →
          q ≠ (18 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r8 r23 r24 r9 r26
    obtain ⟨n1, Mb, c1, u1, hMb, e26, esp, e8, e23, e24, e9, fr⟩ := gf_sub_iter (i := i) s hc hb hi hF hacc hnp hD
      sFB sFC (sDC.sub (by omega)) rsp r8 r23 r24 r9 r26
    have eA : memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFA.subR (by omega)) (sDA.subR (by omega))
    have eN : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    rw [eA, eN] at u1 e26
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb BSUB borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb GD p256DecompressCode := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e26]; exact bm, ?_, esp, e8, e23, e24, e9, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e26]
      exact sub_arith hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp r8 r23 r24 r9 r26
    have i11 : i = 7 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 7 (by decide) s hc hb hfr hbm hv rsp r8 r23 r24 r9 r26
    exact ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp r8 r23 r24 r9 r26
    have hl : i + 1 < 8 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, e8, e23, e24, e9, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp r8 r23 r24 r9 r26
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hb', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 e8 e23 e24 e9 rfl
    exact ⟨n', M', c1.trans c', u', hc', hb', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr q8 q23 q24 q9 => by
      rw [fr' q q0 q1 q2 q3 q4 qr q8 q23 q24 q9, fr q q0 q1 q2 q3 q4 qr q8 q23 q24 q9]⟩

def gfP1 : List BInstr :=
  [.aluImm .add a0 sp 0x21C, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0, .aluImm .add (18 : Fin 32) sp 0x21C]
def gfP2 : List BInstr :=
  [.aluImm .add a2 x0 0x0, .aluImm .add (9 : Fin 32) sp 0x1DC, .aluImm .add (8 : Fin 32) x0 0x8]
def gfP4 : List BInstr :=
  [.sw sp (19 : Fin 32) 0x43C, .aluImm .add a0 sp 0x43C, .lw a0 sp 0x43C, .aluImm .sltu (8 : Fin 32) a0 0x1,
   .alu .and (8 : Fin 32) (8 : Fin 32) a2, .sb sp (8 : Fin 32) 0x43C, .aluImm .add a0 sp 0x43C, .lbu a0 sp 0x43C,
   .aluImm .add a0 a0 0xFFFFFFFF, .alu .and a2 a2 a0, .alu .add a0 x0 (19 : Fin 32), .aluImm .add a1 x0 0x0]
def gfP5 : List BInstr :=
  [.aluImm .add a0 sp 0x43C, .aluImm .add a1 sp 0x21C, .aluImm .add a2 sp 0x1DC, .alu .add a3 x0 (8 : Fin 32)]

theorem gfP1_end : blockEnd p256DecompressCode 0x650 gfP1 = some 0x65C := by decide
theorem gfP2_end : blockEnd p256DecompressCode 0x664 gfP2 = some 0x66A := by decide
theorem gfP4_end : blockEnd p256DecompressCode 0x68A gfP4 = some 0x6B0 := by decide
theorem gfP5_end : blockEnd p256DecompressCode 0x6B8 gfP5 = some 0x6C2 := by decide

/-- The registers the end of the final squaring leaves alone. -/
def gfPostKeep (q : Fin 32) : Bool :=
  q.val ∉ [1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 28, 29, 30, 31]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The end of the final squaring**, from 0x650 to 0x6CA: the conditional
subtraction of the modulus, which leaves at `S + 0x43C` the accumulator when
the top carry `s3` is zero and the subtraction borrowed, and the difference
otherwise. -/
theorem gf_sq_post {M : Word → BitVec 8} {S : Word} {n : Machine} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0x650 (reg n)) (rsp : reg n sp = S) (r20 : reg n (20 : Fin 32) = S + BitVec.ofNat 32 0x170) :
    ∃ (n' : Machine) (Dv : Nat) (b : Word), Steps n n' ∧ St n'.mem GD n' 0x6CA (reg n') ∧ GdCode n'.mem ∧
      (b = 0 ∨ b = 0xFFFFFFFF) ∧ Dv < 2 ^ 256 ∧
      accV M (S + BitVec.ofNat 32 0x1DC) 8 + 2 ^ 256 * maskBit b = accV M (S + BitVec.ofNat 32 0x170) 8 + Dv ∧
      accV n'.mem (S + BitVec.ofNat 32 0x43C) 8 =
        (if (reg n (19 : Fin 32)).toNat = 0 ∧ maskBit b = 1 then accV M (S + BitVec.ofNat 32 0x1DC) 8 else Dv) ∧
      (∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x21C) 32 x 1 →
        Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → n'.mem x = M x) ∧
      ∀ q, gfPostKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hb4 : (S + 0xFFFFFFFC).toNat = S.toNat - 4 := F.below 4 (by decide) (by decide)
  have hb40 : (S + 0xFFFFFFC0).toNat = S.toNat - 0x40 := F.below 0x40 (by decide) (by decide)
  have lowS : ∀ (c : Nat) (B : Word) (k : Nat), 0 < k → k ≤ 0x100 → B.toNat = S.toNat - k → ∀ d l, d + l ≤ 0x710 →
      Sep B k (S + BitVec.ofNat 32 d) l := fun c B k hk hk' hB d l hd =>
    sep_of_le (by rw [hB, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have hiB : ∀ (B : Word) (k : Nat), B.toNat + k ≤ S.toNat → ∀ x : Word, 0x40000000 ≤ x.toNat → Sep B k x 1 :=
    fun B k h x hx => sep_of_le (by omega) (by have := x.isLt; omega)
  -- clear the buffer at S + 0x21C
  obtain ⟨n1, c1, u1⟩ := s.block gfP1 C.self gfP1_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gfP1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, mem2, k2⟩ := c_memset (dst := S + BitVec.ofNat 32 0x21C) (b := 0) (N := 32)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0x65C (reg n1)) C.self C.K.K gd_at_65c gd_at_660 (by decide) (by decide)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gfP1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gfP1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gfP1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    (by rw [F.at 0x21C (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  obtain ⟨M2, hM2⟩ : ∃ M2, fillBytes M (S + BitVec.ofNat 32 0x21C) ((0 : Word).extractLsb' 0 8) 32 = M2 := ⟨_, rfl⟩
  rw [hM2] at mem2
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M2 x = M x := fun x hx => by
    rw [← hM2, fillBytes_sep (F.hiOut (c := 0x21C) (n := 32) (by decide) hx) (Nat.le_refl _)]
  have C2 := C.hi h2hi
  have k2' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (18 : Fin 32) →
      reg n2 q = reg n q := fun q h0 h1 h2 h3 h4 h5 h6 hr h18 => by
    have hb : q ∉ gfP1.filterMap BInstr.dst := by simp only [gfP1]; revert h0 h1 h2 h18; revert q; decide
    rw [k2 q h0 h2 h3 h4 h5 h6 hr, r1, runBlock_reg _ _ _ q hz hb]
  have e18 : reg n2 (18 : Fin 32) = S + BitVec.ofNat 32 0x21C := by
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r1]
    simp +decide only [runBlock, BInstr.run, gfP1, upd, ↓reduceIte]; rw [rsp]; rfl
  have sp2 : reg n2 sp = S := by
    rw [k2' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact rsp
  -- the subtraction
  have u2' : St M2 GD n2 0x664 (reg n2) := ⟨u2.pc, mem2, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := u2'.block gfP2 C2.self gfP2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gfP2 (M2, reg n2)).2 q := fun q => by rw [u3.regs]
  have t3 : St M2 GD n3 0x66A (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have e8 : reg n3 (8 : Fin 32) = 8 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, gfP2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl
  obtain ⟨n4, d4, u4⟩ := t3.notTaken C2.self 0x66C gd_at_66a (by decide) (by
    show (reg n3 (8 : Fin 32) == reg n3 x0) = false; rw [e8, t3.zero]; rfl)
  have k3 : ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → reg n4 q = reg n2 q :=
    fun q h12 h9 h8 => by
      have hb : q ∉ gfP2.filterMap BInstr.dst := by simp only [gfP2]; revert h12 h9 h8; revert q; decide
      rw [u4.regs, r3, runBlock_reg _ _ _ q u2.zero hb]
  have sB : Sep (S + 0xFFFFFFFC) 4 BSUB borrowingSubCode.length :=
    sep_of_le (by rw [hb4, show BSUB.toNat = (img% borrowingSubAddress) from rfl]; omega) (by decide)
  have sFC : Sep (S + 0xFFFFFFFC) 4 GD p256DecompressCode.length :=
    sep_of_le (by rw [hb4, show GD.toNat = (img% p256DecompressAddress) from rfl]; omega) (by decide)
  obtain ⟨n5, M5, c5, u5, hc5, hbs5, fr5, hm5, hv5, sp5, k5⟩ := gf_sub_loop (F := S) (acc := S + BitVec.ofNat 32 0x1DC)
    (np := S + BitVec.ofNat 32 0x170) (D := S + BitVec.ofNat 32 0x21C) (M0 := M2) (by omega)
    (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)
    (by rw [F.at _ (by decide)]; omega)
    (lowS 0 _ 4 (by decide) (by decide) hb4 _ _ (by decide)) (lowS 0 _ 4 (by decide) (by decide) hb4 _ _ (by decide))
    (lowS 0 _ 4 (by decide) (by decide) hb4 _ _ (by decide))
    (sepS S (.inr (by decide)) (by decide) (by decide)) (sepS S (.inr (by decide)) (by decide) (by decide))
    sB sFC (F.sepHi (by decide) (by decide) (by decide)) (F.sepHi (by decide) (by decide) (by decide))
    7 0 (by decide) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St M2 GD n4 0x66C (reg n4)) C2.self C2.K.K.bsub (fun _ _ _ => rfl)
    (.inl rfl) (by simp [accV, maskBit])
    (by rw [k3 sp (by decide) (by decide) (by decide)]; exact sp2)
    (by rw [Nat.mul_zero, add_ofNat_zero, u4.regs, r3]; simp +decide only [runBlock, BInstr.run, gfP2, upd, ↓reduceIte]
        rw [sp2]; rfl)
    (by rw [Nat.mul_zero, add_ofNat_zero, k3 20 (by decide) (by decide) (by decide),
        k2' 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        r20])
    (by rw [Nat.mul_zero, add_ofNat_zero, k3 18 (by decide) (by decide) (by decide), e18])
    (by rw [u4.regs, e8]; rfl)
    (by rw [u4.regs, r3]; simp +decide only [runBlock, BInstr.run, gfP2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
  have lo4 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFFC) 4 x 1 := fun x hx =>
    hiB _ 4 (by rw [hb4]; omega) x hx
  have lo50 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFC0) 0x40 x 1 := fun x hx =>
    hiB _ 0x40 (by rw [hb40]; omega) x hx
  have h5hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M5 x = M x := fun x hx => by
    rw [fr5 x (lo4 x hx) (F.hiOut (c := 0x21C) (n := 32) (by decide) hx), h2hi x hx]
  have C5 := C.hi h5hi
  have s27 : reg n5 (19 : Fin 32) = reg n (19 : Fin 32) := by
    rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k3 _ (by decide) (by decide) (by decide),
      k2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  -- the choice
  obtain ⟨mc, hmc⟩ : ∃ mc, reg n (19 : Fin 32) = mc := ⟨_, rfl⟩
  obtain ⟨bw, hbw⟩ : ∃ bw, reg n5 a2 = bw := ⟨_, rfl⟩
  rw [hbw] at hm5 hv5
  have e27 : reg n5 (19 : Fin 32) = mc := by rw [s27, hmc]
  obtain ⟨cc, hcc⟩ : ∃ cc, aluEval .and (aluEval .sltu mc 1) bw = cc := ⟨_, rfl⟩
  have hcv := choice_val mc bw hm5
  rw [hcc] at hcv
  have hc01 : cc = 0 ∨ cc = 1 := by
    rw [hcv]; by_cases h : mc.toNat = 0 ∧ maskBit bw = 1
    · rw [ite_eq_left h]; exact .inr rfl
    · rw [ite_eq_right h]; exact .inl rfl
  have u5' : St M5 GD n5 0x68A (reg n5) := u5
  have a43C : (S + BitVec.ofNat 32 0x43C).toNat % 4 = 0 := by rw [F.at _ (by decide)]; omega
  obtain ⟨n8, c8, u8⟩ := u5'.block gfP4 hc5 gfP4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gfP4]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp5]
    exact ⟨⟨a43C, F.sepHi (by decide) (by decide) (by decide)⟩, a43C, F.sepHi (by decide) (by decide) (by decide)⟩)
  have r8 : ∀ q, reg n8 q = (runBlock gfP4 (M5, reg n5)).2 q := fun q => by rw [u8.regs]
  have m8 : n8.mem = memStore8 (memStore32 M5 (S + BitVec.ofNat 32 0x43C) mc) (S + BitVec.ofNat 32 0x43C)
      (cc.extractLsb' 0 8) := by
    rw [u8.mem]; simp +decide only [runBlock, BInstr.run, gfP4, upd, ↓reduceIte]
    rw [sp5, e27, hbw, memLoad32_store32_same, ← hcc]; rfl
  have v8 : reg n8 (8 : Fin 32) = cc := by
    rw [r8]; simp +decide only [runBlock, BInstr.run, gfP4, upd, ↓reduceIte]
    rw [sp5, e27, hbw, memLoad32_store32_same, ← hcc]
  have k8 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (8 : Fin 32) → reg n8 q = reg n5 q := fun q h0 h1 h2 h8 => by
    have hb : q ∉ gfP4.filterMap BInstr.dst := by simp only [gfP4]; revert h0 h1 h2 h8; revert q; decide
    rw [r8, runBlock_reg _ _ _ q u5'.zero hb]
  have hc8 : CodeIn n8.mem GD p256DecompressCode := by
    rw [m8]; exact CodeIn.store8 (CodeIn.store32 C5.self (F.sepHi (by decide) (by decide) (by decide)))
      (F.sepHi (by decide) (by decide) (by decide))
  have h8hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n8.mem x = M x := fun x hx => by
    rw [m8, memStore8_ne (fun e => (F.hiOut (c := 0x43C) (n := 1) (by decide) hx) 0 (by decide) 0 (by decide)
      (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (F.hiOut (c := 0x43C) (n := 4) (by decide) hx), h5hi x hx]
  have C8 := C.hi h8hi
  -- borrowing_sub, whose result goes unused
  obtain ⟨n9, c9, u9, _, _, sp9, fr9, mem9⟩ := (⟨u8.pc, rfl, fun _ => rfl⟩ : St n8.mem GD n8 0x6B0 (reg n8)).bsubCall
    C8.self C8.K.K.bsub (by decide) gd_at_6b0 gd_at_6b4 (by decide) (by decide)
    (by rw [k8 sp (by decide) (by decide) (by decide) (by decide)]; exact sp5) (by omega) sB
  have h9hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n9.mem x = M x := fun x hx => by
    rw [mem9 x (lo4 x hx), h8hi x hx]
  have C9 := C.hi h9hi
  have k9 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (8 : Fin 32) → reg n9 q = reg n5 q :=
    fun q h0 h1 h2 h3 h4 hr h8 => by rw [fr9 q h0 h1 h2 h3 h4 hr, k8 q h0 h1 h2 h8]
  have e8' : reg n9 (8 : Fin 32) = cc := by rw [fr9 _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), v8]
  -- select into S + 0x43C
  obtain ⟨n10, c10, u10⟩ := u9.block gfP5 C9.self gfP5_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r10 : ∀ q, reg n10 q = (runBlock gfP5 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  obtain ⟨n11, c11, u11, vals, fr11, sp11x, k11⟩ := c2_sel (out := S + BitVec.ofNat 32 0x43C)
    (ap := S + BitVec.ofNat 32 0x21C) (bp := S + BitVec.ofNat 32 0x1DC) (c := cc) (S := S)
    (⟨u10.pc, u10.mem, fun _ => rfl⟩ : St n9.mem GD n10 0x6C2 (reg n10)) C9.self C9.K F gd_at_6c2 gd_at_6c6 (by decide)
    (by decide)
    (by rw [r10, runBlock_reg _ _ _ sp u9.zero (by decide)]; exact sp9)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, gfP5, upd, ↓reduceIte]; rw [sp9]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, gfP5, upd, ↓reduceIte]; rw [sp9]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, gfP5, upd, ↓reduceIte]; rw [sp9]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, gfP5, upd, ↓reduceIte]; rw [e8']
        exact BitVec.zero_add _)
    hc01 (by decide) (by decide) (by decide) rfl rfl rfl (by decide) (by decide) (by decide)
  have k11' : ∀ q, sel8Keep q = true → q ≠ ra → reg n11 q = reg n9 q := fun q hq hr => by
    have hb : q ∉ gfP5.filterMap BInstr.dst := by simp only [gfP5]; revert hq; revert q; decide
    rw [k11 q hq hr, r10, runBlock_reg _ _ _ q u9.zero hb]
  -- the frame, through each step
  have frame : ∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x21C) 32 x 1 →
      Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → n11.mem x = M x := by
    intro x h50 h21C h43C
    have h4 : Sep (S + 0xFFFFFFFC) 4 x 1 := by
      have := h50.sub (c := 0x3C) (l := 4) (by decide)
      rwa [show S + 0xFFFFFFC0 + BitVec.ofNat 32 0x3C = S + 0xFFFFFFFC by rw [BitVec.add_assoc]; rfl] at this
    rw [fr11 x h50 h43C, mem9 x h4, m8,
      memStore8_ne (fun e => h43C 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (h43C.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
      fr5 x h4 h21C, ← hM2, fillBytes_sep h21C (Nat.le_refl _)]
  -- the two operands of the select, word by word
  have below4 : ∀ c, c + 4 ≤ 0x710 → Sep (S + 0xFFFFFFFC) 4 (S + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_of_le (by rw [hb4, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  have n9w : ∀ d, d + 4 ≤ 0x43C → memLoad32 n9.mem (S + BitVec.ofNat 32 d) = memLoad32 M5 (S + BitVec.ofNat 32 d) :=
    fun d hd => by
      rw [load_frame mem9 (below4 _ (by omega)), m8, ld_ofNat, ld_ofNat]
      have h62 : ∀ j, j < 4 → Sep (S + BitVec.ofNat 32 0x43C) 4 (S + BitVec.ofNat 32 d + BitVec.ofNat 32 j) 1 :=
        fun j hj => by rw [add_ofNat_assoc]; exact sepS S (.inr (by omega)) (by decide) (by omega)
      rw [memStore8_ne (fun e => (h62 3 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
        memStore8_ne (fun e => (h62 2 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
        memStore8_ne (fun e => (h62 1 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
        memStore8_ne (fun e => (h62 0 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
        memStore32_get_sep (h62 3 (by decide)), memStore32_get_sep (h62 2 (by decide)),
        memStore32_get_sep (h62 1 (by decide)), memStore32_get_sep (h62 0 (by decide)), ← ld_ofNat]
  have n9acc : ∀ i, i < 8 → memLoad32 n9.mem (S + BitVec.ofNat 32 0x1DC + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (S + BitVec.ofNat 32 0x1DC + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [add_ofNat_assoc, n9w _ (by omega),
      load_frame2 fr5 (below4 _ (by omega)) (sepS S (c := 0x21C) (n := 32) (d := 0x1DC + 4 * i) (k := 4)
        (.inr (by omega)) (by decide) (by omega)), ← hM2,
      fill_word_out (sepS S (c := 0x21C) (n := 32) (d := 0x1DC + 4 * i) (k := 4) (.inr (by omega)) (by decide) (by omega))]
  have n9d : ∀ i, i < 8 → memLoad32 n9.mem (S + BitVec.ofNat 32 0x21C + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M5 (S + BitVec.ofNat 32 0x21C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [add_ofNat_assoc, n9w _ (by omega)]
  have n11acc : ∀ i, i < 8 → memLoad32 n11.mem (S + BitVec.ofNat 32 0x43C + BitVec.ofNat 32 (4 * i)) =
      if cc = 1 then memLoad32 M (S + BitVec.ofNat 32 0x1DC + BitVec.ofNat 32 (4 * i))
      else memLoad32 M5 (S + BitVec.ofNat 32 0x21C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [vals i hi, n9acc i hi, n9d i hi]
  have hdv : accV M5 (S + BitVec.ofNat 32 0x21C) 8 < 2 ^ 256 := accV_lt M5 _ 8
  have sA : ∀ d, d + 4 ≤ 0x21C → Sep (S + BitVec.ofNat 32 0x21C) 32 (S + BitVec.ofNat 32 d) 4 :=
    fun d hd => sepS S (.inr (by omega)) (by decide) (by omega)
  have eA : accV M2 (S + BitVec.ofNat 32 0x1DC) 8 = accV M (S + BitVec.ofNat 32 0x1DC) 8 :=
    accV_congr2 8 fun i hi => by
      rw [← hM2, add_ofNat_assoc, fill_word_out (sA _ (by omega))]
  have eN : accV M2 (S + BitVec.ofNat 32 0x170) 8 = accV M (S + BitVec.ofNat 32 0x170) 8 :=
    accV_congr2 8 fun i hi => by
      rw [← hM2, add_ofNat_assoc, fill_word_out (sA _ (by omega))]
  rw [eA, eN] at hv5
  refine ⟨n11, accV M5 (S + BitVec.ofNat 32 0x21C) 8, bw,
    c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (c8.trans (c9.trans (c10.trans c11))))))),
    u11, C.hi fun x hx => by rw [fr11 x (lo50 x hx) (F.hiOut (c := 0x43C) (n := 32) (by decide) hx), h9hi x hx],
    hm5, hdv, hv5, ?_, frame, ?_⟩
  · rw [hmc]
    by_cases hcd : mc.toNat = 0 ∧ maskBit bw = 1
    · rw [ite_eq_left hcd]
      have h1 : cc = 1 := by rw [hcv, ite_eq_left hcd]
      exact accV_congr2 8 fun i hi => by rw [n11acc i hi, ite_eq_left h1]
    · rw [ite_eq_right hcd]
      have h0 : cc ≠ 1 := by rw [hcv, ite_eq_right hcd]; decide
      exact accV_congr2 8 fun i hi => by rw [n11acc i hi, ite_eq_right h0]
  · intro q hq
    have ne : ∀ r : Fin 32, gfPostKeep r = false → q ≠ r := fun r hr => pkeep_ne hq hr
    rw [k11' q (by revert hq; revert q; decide) (ne ra rfl),
      k9 q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne ra rfl) (ne 8 rfl),
      k5 q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne ra rfl) (ne 9 rfl) (ne 20 rfl)
        (ne 18 rfl) (ne 8 rfl),
      k3 q (ne a2 rfl) (ne 9 rfl) (ne 8 rfl),
      k2' q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne a5 rfl) (ne a6 rfl) (ne ra rfl) (ne 18 rfl)]

/-! ## Setting up the final squaring -/

def gfQ1 : List BInstr := [.aluImm .add a0 sp 0x150, .aluImm .add a1 sp 0x65C, .aluImm .add a2 x0 0x20]
def gfQ2 : List BInstr :=
  [.lw (25 : Fin 32) sp 0x18, .lw (26 : Fin 32) sp 0x14, .lw (27 : Fin 32) sp 0x10, .aluImm .add (20 : Fin 32) sp 0x170,
   .lui a1 0x3FCC5000, .aluImm .add a1 a1 0xFFFFFB38, .aluImm .add a2 x0 0x6C, .alu .add a0 x0 (20 : Fin 32)]
def gfQ3 : List BInstr :=
  [.lw (18 : Fin 32) sp 0x1D0, .aluImm .add a0 sp 0x1DC, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]
def gfQ4 : List BInstr :=
  [.aluImm .add (19 : Fin 32) x0 0x0, .aluImm .add (29 : Fin 32) x0 0x0, .aluImm .add (30 : Fin 32) x0 0x0,
   .lw (7 : Fin 32) sp 0x150, .lw (28 : Fin 32) sp 0x170, .aluImm .add a6 sp 0x174, .aluImm .add a7 sp 0x1E0,
   .aluImm .add (6 : Fin 32) x0 0x8, .aluImm .add (5 : Fin 32) sp 0x150]

theorem gfQ1_end : blockEnd p256DecompressCode 0x536 gfQ1 = some 0x540 := by decide
theorem gfQ2_end : blockEnd p256DecompressCode 0x548 gfQ2 = some 0x560 := by decide
theorem gfQ3_end : blockEnd p256DecompressCode 0x568 gfQ3 = some 0x574 := by decide
theorem gfQ4_end : blockEnd p256DecompressCode 0x57C gfQ4 = some 0x598 := by decide

theorem p2params_k : wordAt p256ParamsData 0x60 0 = 0xFFFFFFFF := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **The start of the final squaring**, from 0x536 to the outer loop at
0x59C: copy `β` to `S + 0x150` and the parameters to `S + 0x170`, reload
`s9..s11`, clear the accumulator at `S + 0x1DC`, and load the loop's
registers. -/
theorem gf_sq_pre {M : Word → BitVec 8} {S : Word} {n : Machine} (C : GdCode M) (D : GdData M) (F : Fr S 0x710)
    (s : St M GD n 0x536 (reg n)) (rsp : reg n sp = S) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x59C (reg n') ∧ GdCode n'.mem ∧ GdData n'.mem ∧
      (∀ i, i < 8 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0x150 + 4 * i)) =
        memLoad32 M (S + BitVec.ofNat 32 (0x65C + 4 * i))) ∧
      (∀ i, i < 8 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0x170 + 4 * i)) = memLoad32 M (P2N + BitVec.ofNat 32 (4 * i))) ∧
      (∀ i, i < 8 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0x1DC + 4 * i)) = 0) ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x150) 0xAC x 1 → n'.mem x = M x) ∧
      reg n' (25 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x18) ∧
      reg n' (26 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x14) ∧
      reg n' (27 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x10) ∧
      reg n' sp = S ∧ reg n' (19 : Fin 32) = 0 ∧ reg n' (29 : Fin 32) = 0 ∧ reg n' (30 : Fin 32) = 0 ∧
      reg n' (7 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x65C) ∧ reg n' (28 : Fin 32) = 0xFFFFFFFF ∧
      reg n' (18 : Fin 32) = 0xFFFFFFFF ∧ reg n' a6 = S + BitVec.ofNat 32 0x174 ∧
      reg n' (17 : Fin 32) = S + BitVec.ofNat 32 0x1E0 ∧ reg n' (6 : Fin 32) = 8 ∧
      reg n' (5 : Fin 32) = S + BitVec.ofNat 32 0x150 ∧ reg n' (20 : Fin 32) = S + BitVec.ofNat 32 0x170 ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have below16 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0x8B0 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x190) (l := 16) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  have al : ∀ c, c + 4 ≤ 0x710 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  -- copy β
  obtain ⟨n1, c1, u1⟩ := s.block gfQ1 C.self gfQ1_end ⟨trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gfQ1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x150) (src := S + BitVec.ofNat 32 0x65C)
    (S := S) (N := 32) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0x540 (reg n1)) C.self C.K.K gd_at_540 gd_at_544
    (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gfQ1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gfQ1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gfQ1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    ⟨C.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr2' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x150) 32 x 1 → n2.mem x = M x :=
    fun x a b => by rw [fr2 x a, copyBytes_sep b (Nat.le_refl _)]
  have C2 := C.hi fun x hx => fr2' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D2 : GdData n2.mem := D.of F fun x hx => fr2' x (below16 hx) (fr_inFrame (by decide) hx)
  have g1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] →
      reg n2 q = reg n q := fun q hq => by
    rw [kc k2 q hq, r1, runBlock_reg _ _ _ q hz (by simp only [gfQ1]; revert hq; revert q; decide)]
  have sp2 : reg n2 sp = S := by rw [g1 sp (by decide)]; exact rsp
  -- reload s9..s11, and copy the parameters
  obtain ⟨n3, c3, u3⟩ := u2.block gfQ2 C2.self gfQ2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gfQ2]; simp +decide only [upd, ↓reduceIte, and_true]
    rw [sp2]; exact ⟨al 0x18 (by decide) (by decide), al 0x14 (by decide) (by decide), al 0x10 (by decide) (by decide)⟩)
  have r3 : ∀ q, reg n3 q = (runBlock gfQ2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have e320 : reg n3 (20 : Fin 32) = S + BitVec.ofNat 32 0x170 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, gfQ2, upd, ↓reduceIte]; rw [sp2]; rfl
  obtain ⟨n4, c4, u4, fr4, k4⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x170) (src := P2N) (S := S) (N := 0x6C)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GD n3 0x560 (reg n3)) C2.self C2.K.K gd_at_560 gd_at_564 (by decide)
    (by decide) (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gfQ2, upd, ↓reduceIte]; rw [sp2]; (try rw [u2.zero])
        exact BitVec.zero_add _)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gfQ2, upd, ↓reduceIte]; try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gfQ2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    ⟨C2.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr4' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x170) 0x6C x 1 → n4.mem x = n2.mem x :=
    fun x a b => by rw [fr4 x a, copyBytes_sep b (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => fr4' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D4 : GdData n4.mem := D2.of F fun x hx => fr4' x (below16 hx) (fr_inFrame (by decide) hx)
  have g3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 21, 22, 23, 24, 31] → reg n3 q = reg n2 q :=
    fun q hq => by rw [r3, runBlock_reg _ _ _ q u2.zero (by simp only [gfQ2]; revert hq; revert q; decide)]
  have v3 : ∀ q : Fin 32, q.val ∈ [25, 26, 27] → reg n4 q = reg n3 q := fun q hq => kc k4 q (by revert hq; revert q; decide)
  have sp4 : reg n4 sp = S := by rw [kc k4 sp (by decide), g3 sp (by decide)]; exact sp2
  have hp4 : ∀ i, i < 27 → memLoad32 n4.mem (S + BitVec.ofNat 32 (0x170 + 4 * i)) =
      memLoad32 n2.mem (P2N + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [load_frame fr4 (l16 _ (by omega)), ← add_ofNat_assoc, cp_word (by omega) (by decide)]
  -- the Montgomery constant, and clear the accumulator
  obtain ⟨n5, c5, u5⟩ := u4.block gfQ3 C4.self gfQ3_end (by
    simp only [BlockOk, BInstr.ok, gfQ3]; simp +decide only [and_true]
    rw [sp4]; exact al 0x1D0 (by decide) (by decide))
  have r5 : ∀ q, reg n5 q = (runBlock gfQ3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  obtain ⟨n6, c6, u6, mem6, k6⟩ := c_memset (dst := S + BitVec.ofNat 32 0x1DC) (b := 0) (N := 32)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem GD n5 0x574 (reg n5)) C4.self C4.K.K gd_at_574 gd_at_578 (by decide)
    (by decide)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gfQ3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gfQ3, upd, ↓reduceIte]; (try rw [u4.zero]); try rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gfQ3, upd, ↓reduceIte]; (try rw [u4.zero]); try rfl)
    (by rw [F.at 0x1DC (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h6 : ∀ x, Sep (S + BitVec.ofNat 32 0x1DC) 32 x 1 → n6.mem x = n4.mem x := fun x hx => by
    rw [mem6, fillBytes_sep hx (Nat.le_refl _)]
  have C6 := C4.hi fun x hx => h6 x (F.hiOut (by decide) hx)
  have D6 : GdData n6.mem := D4.of F fun x hx => h6 x (fr_inFrame (by decide) hx)
  have g5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 6, 7, 8, 9, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] →
      reg n6 q = reg n5 q := fun q hq => by
    rw [k6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)]
  have g45 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 5, 6, 8, 9, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] → reg n5 q = reg n4 q :=
    fun q hq => by rw [r5, runBlock_reg _ _ _ q u4.zero (by simp only [gfQ3]; revert hq; revert q; decide)]
  have sp6 : reg n6 sp = S := by rw [g5 sp (by decide), g45 sp (by decide)]; exact sp4
  have e618 : reg n6 (18 : Fin 32) = 0xFFFFFFFF := by
    rw [g5 18 (by decide), r5]; simp +decide only [runBlock, BInstr.run, gfQ3, upd, ↓reduceIte]; rw [sp4]
    have := hp4 0x18 (by decide)
    rw [show 0x170 + 4 * 0x18 = 0x1D0 from rfl] at this
    rw [show S + 0x1D0 = S + BitVec.ofNat 32 0x1D0 from rfl, this, show 4 * 0x18 = 0x60 + 4 * 0 from rfl,
      code_word D2.D.params 0x60 0 (by decide), p2params_k]
  -- the loop's registers
  obtain ⟨n7, c7, u7⟩ := u6.block gfQ4 C6.self gfQ4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gfQ4]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp6]; exact ⟨al 0x150 (by decide) (by decide), al 0x170 (by decide) (by decide)⟩)
  have r7 : ∀ q, reg n7 q = (runBlock gfQ4 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have t7 : St n6.mem GD n7 0x598 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
  have e76 : reg n7 (6 : Fin 32) = 8 := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl
  obtain ⟨n8, d8, u8⟩ := t7.notTaken C6.self 0x59C gd_at_598 (by decide) (by
    show (reg n7 (6 : Fin 32) == reg n7 x0) = false; rw [e76, t7.zero]; rfl)
  have g8 : ∀ q, reg n8 q = (runBlock gfQ4 (n6.mem, reg n6)).2 q := fun q => by rw [u8.regs, r7]
  -- memory, word by word
  have w6 : ∀ d, d + 4 ≤ 0x710 → (d + 4 ≤ 0x150 ∨ 0x1DC ≤ d) → (d + 4 ≤ 0x1DC ∨ 0x1FC ≤ d) →
      memLoad32 n6.mem (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := fun d hd h1 h2 =>
    memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, h6 _ (sepS S (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega))
        (by decide) (by omega)),
        fr4' _ (F.lowB hb16 (by decide) (by omega))
          (sepS S (by rcases h1 with h | h; exact .inr (by omega); exact .inl (by omega)) (by decide) (by omega)),
        fr2' _ (F.lowB hb16 (by decide) (by omega))
          (sepS S (by rcases h1 with h | h; exact .inr (by omega); exact .inl (by omega)) (by decide) (by omega))]
  have wb : ∀ i, i < 8 → memLoad32 n6.mem (S + BitVec.ofNat 32 (0x150 + 4 * i)) =
      memLoad32 M (S + BitVec.ofNat 32 (0x65C + 4 * i)) := fun i hi => by
    have e1 : memLoad32 n6.mem (S + BitVec.ofNat 32 (0x150 + 4 * i)) =
        memLoad32 n2.mem (S + BitVec.ofNat 32 (0x150 + 4 * i)) := memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, h6 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
        fr4' _ (F.lowB hb16 (by decide) (by omega))
          (sepS S (.inr (by omega)) (by decide) (by omega))]
    rw [e1, load_frame fr2 (l16 _ (by omega)), ← add_ofNat_assoc S 0x150, cp_word (by omega) (by decide),
      add_ofNat_assoc]
  have wp : ∀ i, i < 27 → memLoad32 n6.mem (S + BitVec.ofNat 32 (0x170 + 4 * i)) =
      memLoad32 M (P2N + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    have e1 : memLoad32 n6.mem (S + BitVec.ofNat 32 (0x170 + 4 * i)) =
        memLoad32 n4.mem (S + BitVec.ofNat 32 (0x170 + 4 * i)) := memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, h6 _ (sepS S (.inr (by omega)) (by decide) (by omega))]
    rw [e1, hp4 i hi, show 4 * i = 0 + 4 * i by omega,
      code_word D2.D.params 0 i (by have : p256ParamsData.length = 0x6C := rfl; omega),
      code_word D.D.params 0 i (by have : p256ParamsData.length = 0x6C := rfl; omega)]
  have w2 : ∀ d, d + 4 ≤ 0x150 → memLoad32 n2.mem (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
    fun d hd => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc]
      exact fr2' _ (F.lowB hb16 (by decide) (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.single d8))))))),
    ⟨u8.pc, by rw [u8.mem], fun _ => rfl⟩, by rw [u8.mem]; exact C6, by rw [u8.mem]; exact D6,
    fun i hi => by rw [u8.mem]; exact wb i hi, fun i hi => by rw [u8.mem]; exact wp i (by omega),
    fun i hi => by rw [u8.mem, mem6, ← add_ofNat_assoc]; exact fill_word0 (by omega) (by decide),
    fun x h16 h150 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have s170 : Sep (S + BitVec.ofNat 32 0x170) 0x6C x 1 := by
      have := h150.sub (c := 0x20) (l := 0x6C) (by decide); rwa [add_ofNat_assoc] at this
    have s1DC : Sep (S + BitVec.ofNat 32 0x1DC) 32 x 1 := by
      have := h150.sub (c := 0x8C) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have s150 : Sep (S + BitVec.ofNat 32 0x150) 32 x 1 := by
      have := h150.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
    rw [u8.mem, h6 x s1DC, fr4' x h16 s170, fr2' x h16 s150]
  · rw [g8, runBlock_reg _ _ _ 25 u6.zero (by decide), g5 25 (by decide), g45 25 (by decide), v3 25 (by decide), r3]
    simp +decide only [runBlock, BInstr.run, gfQ2, upd, ↓reduceIte]; rw [sp2]
    exact w2 0x18 (by decide)
  · rw [g8, runBlock_reg _ _ _ 26 u6.zero (by decide), g5 26 (by decide), g45 26 (by decide), v3 26 (by decide), r3]
    simp +decide only [runBlock, BInstr.run, gfQ2, upd, ↓reduceIte]; rw [sp2]
    exact w2 0x14 (by decide)
  · rw [g8, runBlock_reg _ _ _ 27 u6.zero (by decide), g5 27 (by decide), g45 27 (by decide), v3 27 (by decide), r3]
    simp +decide only [runBlock, BInstr.run, gfQ2, upd, ↓reduceIte]; rw [sp2]
    exact w2 0x10 (by decide)
  · rw [g8, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6
  · rw [g8]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl
  · rw [g8]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl
  · rw [g8]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl
  · rw [g8]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; rw [sp6]
    have := wb 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this; exact this
  · rw [g8]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; rw [sp6]
    have := wp 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero, add_ofNat_zero] at this
    rw [show S + 0x170 = S + BitVec.ofNat 32 0x170 from rfl, this]; exact D.D.N0
  · rw [g8, runBlock_reg _ _ _ 18 u6.zero (by decide)]; exact e618
  · rw [g8]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; rw [sp6]; rfl
  · rw [g8]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; rw [sp6]; rfl
  · rw [g8]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl
  · rw [g8]; simp +decide only [runBlock, BInstr.run, gfQ4, upd, ↓reduceIte]; rw [sp6]; rfl
  · rw [g8, runBlock_reg _ _ _ 20 u6.zero (by decide), g5 20 (by decide), g45 20 (by decide), kc k4 20 (by decide), e320]
  · rw [g8, runBlock_reg _ _ _ 3 u6.zero (by decide), g5 3 (by decide), g45 3 (by decide), kc k4 3 (by decide),
      g3 3 (by decide), g1 3 (by decide)]
  · rw [g8, runBlock_reg _ _ _ 4 u6.zero (by decide), g5 4 (by decide), g45 4 (by decide), kc k4 4 (by decide),
      g3 4 (by decide), g1 4 (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **The final squaring**, from 0x536 to 0x6CA: `decompress` copies `β`
to `S + 0x150` and leaves its Montgomery square at `S + 0x43C`. -/
theorem gf_sq {M : Word → BitVec 8} {S : Word} {n : Machine} (C : GdCode M) (D : GdData M) (F : Fr S 0x710)
    (s : St M GD n 0x536 (reg n)) (rsp : reg n sp = S) (hB : accV M (S + BitVec.ofNat 32 0x65C) 8 < p256) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x6CA (reg n') ∧ GdCode n'.mem ∧ GdData n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x43C) 8 =
        p2fm (accV M (S + BitVec.ofNat 32 0x65C) 8) (accV M (S + BitVec.ofNat 32 0x65C) 8) ∧
      accV n'.mem (S + BitVec.ofNat 32 0x150) 8 = accV M (S + BitVec.ofNat 32 0x65C) 8 ∧
      reg n' (25 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x18) ∧
      reg n' (26 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x14) ∧
      reg n' (27 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x10) ∧ reg n' sp = S ∧
      (∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x150) 0xEC x 1 →
        Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → n'.mem x = M x) ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1, C1, D1, wb, wp, wz, fr1, e25, e26, e27, sp1, e19, e29, e30, e7, e28, e18, e16, e17, e6, e5, e20,
    g3, g4⟩ := gf_sq_pre C D F s rsp
  have hxn : S + BitVec.ofNat 32 0x150 + 0x20 = S + BitVec.ofNat 32 0x170 := by rw [BitVec.add_assoc]; rfl
  have eX : accV n1.mem (S + BitVec.ofNat 32 0x150) 8 = accV M (S + BitVec.ofNat 32 0x65C) 8 :=
    accV_congr2 8 fun i hi => by rw [add_ofNat_assoc, add_ofNat_assoc, wb i hi]
  have eN : accV n1.mem (S + BitVec.ofNat 32 0x170) 8 = p256 := by
    rw [← D.D.N]; exact accV_congr2 8 fun i hi => by rw [add_ofNat_assoc, wp i hi]; rfl
  have eA0 : accV n1.mem (S + BitVec.ofNat 32 0x1DC) 8 = 0 :=
    accV_zero 8 fun i hi => by rw [add_ofNat_assoc]; exact wz i hi
  have eN0 : memLoad32 n1.mem (S + BitVec.ofNat 32 0x170) = 0xFFFFFFFF := by
    have := wp 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero, add_ofNat_zero] at this
    rw [this]; exact D.D.N0
  -- the loop
  obtain ⟨n2, M2, c2, u2, hc2, hf2, ⟨U, hU⟩, hbd2, k2⟩ := gf_outer (B := GD) (acc := S + BitVec.ofNat 32 0x1DC)
    (xp := S + BitVec.ofNat 32 0x150) (M0 := n1.mem)
    (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)
    (sepS S (.inr (by decide)) (by decide) (by decide))
    (by rw [hxn]; exact sepS S (.inr (by decide)) (by decide) (by decide)) (F.sepHi (by decide) (by decide) (by decide))
    (by rw [hxn]; exact eN0) (by rw [hxn, eX, eN]; exact hB) 7 0 (by decide) u1 C1.self (fun _ _ => rfl)
    ⟨0, by rw [eA0, e19, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero, Nat.mul_zero, Nat.zero_mul,
      Nat.add_zero, show accV n1.mem (S + BitVec.ofNat 32 0x150) 0 = 0 from rfl, Nat.zero_mul]⟩
    (by rw [eA0, e19, hxn, eN]; unfold p256; decide)
    (by rw [e30]; rfl) e5
    (by rw [e7]; have := wb 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this; exact this.symm)
    e28 e18 (by rw [sp1]; rfl) (by rw [e16, hxn, add_ofNat_assoc]) (by rw [e17, add_ofNat_assoc]) e29 e6
  have C2 : GdCode M2 := C1.hi fun x hx => hf2 x (F.hiOut (c := 0x1DC) (n := 32) (by decide) hx)
  have D2 : GdData M2 := D1.of F fun x hx => hf2 x (fr_inFrame (by decide) hx)
  have sp2 : reg n2 sp = S := by rw [k2 sp rfl]; exact sp1
  obtain ⟨n3, Dv, b, c3, u3, C3, hb, hDv, hsub, hres, fr3, k3⟩ := gf_sq_post C2 F u2 sp2 (by rw [k2 20 rfl, e20])
  -- the arithmetic
  have eN2 : accV M2 (S + BitVec.ofNat 32 0x170) 8 = p256 := by
    rw [← eN]
    exact accV_congr2 8 fun i hi => memLoad32_congr fun q hq => hf2 _ (by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact sepS S (c := 0x1DC) (n := 32) (d := 0x170 + (4 * i + q)) (k := 1) (.inr (by omega)) (by decide) (by omega))
  rw [eN2] at hsub
  obtain ⟨A, hA⟩ : ∃ A, accV M2 (S + BitVec.ofNat 32 0x1DC) 8 = A := ⟨_, rfl⟩
  obtain ⟨mc, hmc⟩ : ∃ mc, (reg n2 (19 : Fin 32)).toNat = mc := ⟨_, rfl⟩
  rw [hA] at hsub
  rw [hA, hmc] at hres
  rw [hA, hmc, show (2 : Nat) ^ (32 * 8) = 2 ^ 256 from rfl, hxn, eN, eX] at hU
  rw [hA, hmc, show (2 : Nat) ^ (32 * 8) = 2 ^ 256 from rfl, hxn, eN] at hbd2
  have hNl : p256 < 2 ^ 256 := by unfold p256; decide
  have fin := mm_final_arith hDv hNl hbd2 hsub (mb_le1 b)
  have hR : accV n3.mem (S + BitVec.ofNat 32 0x43C) 8 = (A + mc * 2 ^ 256) % p256 := by rw [hres, fin]
  have hval : accV n3.mem (S + BitVec.ofNat 32 0x43C) 8 =
      p2fm (accV M (S + BitVec.ofNat 32 0x65C) 8) (accV M (S + BitVec.ofNat 32 0x65C) 8) :=
    p2_mont (by rw [hR]; exact Nat.mod_lt _ (by unfold p256; decide)) (by rw [hR]; exact mont_congr8 rfl hU)
  have hb40 : (S + 0xFFFFFFC0).toNat = S.toNat - 0x40 := F.below 0x40 (by decide) (by decide)
  have low40 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0x8B0 x 1 → Sep (S + 0xFFFFFFC0) 0x40 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x160) (l := 0x40) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x160 = S + 0xFFFFFFC0 by rw [BitVec.add_assoc]; rfl] at this
  have frame : ∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x150) 0xEC x 1 →
      Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → n3.mem x = M x := by
    intro x h40 h150 h43C
    have h21C : Sep (S + BitVec.ofNat 32 0x21C) 32 x 1 := by
      have := h150.sub (c := 0xCC) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have h1DC : Sep (S + BitVec.ofNat 32 0x1DC) 32 x 1 := by
      have := h150.sub (c := 0x8C) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have h16 : Sep (S + 0xFFFFFFF0) 16 x 1 := by
      have := h40.sub (c := 0x30) (l := 16) (by decide)
      rwa [show S + 0xFFFFFFC0 + BitVec.ofNat 32 0x30 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
    have hAC : Sep (S + BitVec.ofNat 32 0x150) 0xAC x 1 := by
      have := h150.sub (c := 0) (l := 0xAC) (by decide); rwa [add_ofNat_zero] at this
    rw [fr3 x h40 h21C h43C, hf2 x h1DC, fr1 x h16 hAC]
  have kk : ∀ q : Fin 32, q.val ∈ [3, 4, 25, 26, 27] → reg n3 q = reg n1 q := fun q hq => by
    rw [k3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide)]
  refine ⟨n3, c1.trans (c2.trans c3), u3, C3,
    D2.of F fun x hx => fr3 x (low40 hx) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx), hval, ?_,
    by rw [kk 25 (by decide), e25], by rw [kk 26 (by decide), e26], by rw [kk 27 (by decide), e27],
    by rw [k3 sp rfl, sp2], frame, by rw [kk 3 (by decide), g3], by rw [kk 4 (by decide), g4]⟩
  rw [← eX]
  exact accV_congr2 8 fun i hi => memLoad32_congr fun q hq => by
    rw [add_ofNat_assoc, add_ofNat_assoc]
    rw [fr3 _ (F.lowB hb40 (by decide) (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))
      (sepS S (.inr (by omega)) (by decide) (by omega)),
      hf2 _ (sepS S (.inr (by omega)) (by decide) (by omega))]

end C3.RV32.Gd
