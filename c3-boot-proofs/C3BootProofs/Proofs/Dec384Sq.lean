import C3BootProofs.Proofs.Dec384At

/-!
# P-384 point decompression: the inlined Montgomery squaring

`AffinePoint<NistP384>::decompress` raises `x³ + ax + b` to `(p + 1) / 4`
with crypto-bigint's windowed exponentiation, inlined. Its squarings are an
inlined copy of `mul_montgomery_form::<12>`'s loop, specialized to P-384:
the Montgomery factor `-p⁻¹ mod 2³²` is 1 and the modulus's low limb is
`2³² - 1`. This file proves that loop over the arithmetic lemmas of
`MontMul12.lean`.
-/

namespace C3.RV32.Dq

open C3.Image

set_option maxRecDepth 20000

theorem mulhu_comm (a b : Word) : aluEval .mulhu a b = aluEval .mulhu b a := by
  show BitVec.ofNat 32 _ = BitVec.ofNat 32 _; rw [Nat.mul_comm]

theorem mul_comm' (a b : Word) : aluEval .mul a b = aluEval .mul b a := BitVec.mul_comm a b

/-- The inner loop's body in `decompress`: `mmBody` with the two products by
the factor `u` written the other way round. -/
def dqBody : List BInstr :=
  [.lw a3 (30 : Fin 32) 0, .lw a4 a2 0, .alu .mulhu a1 (7 : Fin 32) a3, .alu .mul a5 a4 (6 : Fin 32),
   .alu .mul a3 (7 : Fin 32) a3, .lw (8 : Fin 32) a0 0, .alu .mulhu a4 a4 (6 : Fin 32), .alu .add a1 a1 (28 : Fin 32),
   .aluImm .add a2 a2 4, .alu .add (8 : Fin 32) (8 : Fin 32) a5, .alu .add (9 : Fin 32) (9 : Fin 32) a3,
   .alu .sltu a5 (8 : Fin 32) a5, .alu .sltu a3 (9 : Fin 32) a3, .alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32),
   .alu .add a4 a4 a5, .alu .add a1 a1 a3, .alu .sltu (9 : Fin 32) (8 : Fin 32) (9 : Fin 32), .alu .add a4 a4 a1,
   .sw a0 (8 : Fin 32) 0xFFFFFFFC, .alu .add (9 : Fin 32) (9 : Fin 32) a4, .alu .sltu (28 : Fin 32) a4 a1,
   .alu .sltu a1 (9 : Fin 32) a4, .aluImm .add a0 a0 4, .alu .add (28 : Fin 32) (28 : Fin 32) a1,
   .aluImm .add (30 : Fin 32) (30 : Fin 32) 4, .aluImm .add (29 : Fin 32) (29 : Fin 32) 0xFFFFFFFF]

theorem dqBody_end : blockEnd p384DecompressCode 0x3D4 dqBody = some 0x41E := by decide

set_option maxRecDepth 20000 in
theorem dqBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock dqBody (M, f)).1 = memStore32 M (f a0 + 0xFFFFFFFC)
        (mmCols (memLoad32 M (f (30 : Fin 32) + 0)) (memLoad32 M (f a2 + 0)) (memLoad32 M (f a0 + 0))
          (f (7 : Fin 32)) (f (6 : Fin 32)) (f (9 : Fin 32)) (f (28 : Fin 32))).1 ∧
    (runBlock dqBody (M, f)).2 (9 : Fin 32) = (mmCols (memLoad32 M (f (30 : Fin 32) + 0)) (memLoad32 M (f a2 + 0))
        (memLoad32 M (f a0 + 0)) (f (7 : Fin 32)) (f (6 : Fin 32)) (f (9 : Fin 32)) (f (28 : Fin 32))).2.1 ∧
    (runBlock dqBody (M, f)).2 (28 : Fin 32) = (mmCols (memLoad32 M (f (30 : Fin 32) + 0))
        (memLoad32 M (f a2 + 0)) (memLoad32 M (f a0 + 0)) (f (7 : Fin 32)) (f (6 : Fin 32)) (f (9 : Fin 32))
        (f (28 : Fin 32))).2.2 ∧
    (runBlock dqBody (M, f)).2 (30 : Fin 32) = f (30 : Fin 32) + 4 ∧
    (runBlock dqBody (M, f)).2 a2 = f a2 + 4 ∧
    (runBlock dqBody (M, f)).2 a0 = f a0 + 4 ∧
    (runBlock dqBody (M, f)).2 (29 : Fin 32) = f (29 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (30 : Fin 32) → q ≠ a2 → q ≠ a0 → q ≠ (9 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
      q ≠ a3 → q ≠ a4 → q ≠ a1 → q ≠ a5 → q ≠ (8 : Fin 32) → (runBlock dqBody (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, dqBody]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q q30 q12 q10 q9 q28 q29 q13 q14 q11 q15 q8 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; unfold mmCols; (try rw [mulhu_comm (f 7)]); (try rw [mul_comm' (f 7)]); try rfl
  · simp +decide only [upd, ↓reduceIte]; unfold mmCols; (try rw [mulhu_comm (f 7)]); (try rw [mul_comm' (f 7)]); try rfl
  · simp +decide only [upd, ↓reduceIte]; unfold mmCols; (try rw [mulhu_comm (f 7)]); (try rw [mul_comm' (f 7)]); try rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, q30, q12, q10, q9, q28, q29, q13, q14, q11, q15, q8]

/-- The registers the loop body leaves alone. -/
def dqBodyKeep (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15, 28, 29, 30]

theorem dqBody_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hn : (f (30 : Fin 32) + 0).toNat % 4 = 0) (hy : (f a2 + 0).toNat % 4 = 0)
    (ho : (f a0 + 0).toNat % 4 = 0) (hs : (f a0 + 0xFFFFFFFC).toNat % 4 = 0)
    (hsep : Sep (f a0 + 0xFFFFFFFC) 4 base len) : BlockOk base len dqBody (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, dqBody, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hn, hy, ho, hs, hsep⟩

/-- **One pass of the inner loop**, from 0x3D4: column `k + 1` of a pass,
which stores the accumulator's word `k`. -/
theorem dq_iter {M : Word → BitVec 8} {B np yp acc U X CL CH : Word} {n : Machine} {k : Nat}
    (s : St M B n 0x3D4 (reg n)) (hc : CodeIn M B p384DecompressCode) (hk : k < 11)
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hS : Sep (acc + BitVec.ofNat 32 (4 * k)) 4 B p384DecompressCode.length)
    (r30 : reg n (30 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)))
    (r12 : reg n a2 = yp + BitVec.ofNat 32 (4 * (k + 1)))
    (r10 : reg n a0 = acc + BitVec.ofNat 32 (4 * (k + 1)))
    (r7 : reg n (7 : Fin 32) = U) (r6 : reg n (6 : Fin 32) = X) (r9 : reg n (9 : Fin 32) = CL)
    (r28 : reg n (28 : Fin 32) = CH) (r29 : reg n (29 : Fin 32) = BitVec.ofNat 32 (11 - k)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (acc + BitVec.ofNat 32 (4 * k))
        (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1))))
          (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) U X CL CH).1)
        B n' (if k + 1 < 11 then 0x3D4 else 0x422) (reg n') ∧
      reg n' (9 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.1 ∧
      reg n' (28 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.2 ∧
      reg n' (30 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a2 = yp + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a0 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (29 : Fin 32) = BitVec.ofNat 32 (11 - (k + 1)) ∧
      ∀ q, dqBodyKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have ok := dqBody_ok (M := M) (f := reg n) (base := B) (len := p384DecompressCode.length)
    (by rw [r30, add_lit_zero]; exact aligned_add hnp (by omega))
    (by rw [r12, add_lit_zero]; exact aligned_add hyp (by omega))
    (by rw [r10, add_lit_zero]; exact aligned_add hacc (by omega))
    (by rw [r10, back4 acc k]; exact aligned_add hacc (by omega))
    (by rw [r10, back4 acc k]; exact hS)
  obtain ⟨n1, c1, u1⟩ := St.block dqBody s hc dqBody_end ok
  obtain ⟨em, e9, e28, e30, e12, e10, e29, fr⟩ := dqBody_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [em, r30, r12, r10, r7, r6, r9, r28, add_lit_zero, add_lit_zero, add_lit_zero, back4 acc k] at u1'
  have g : ∀ q, reg n1 q = (runBlock dqBody (M, reg n)).2 q := u1.regs
  have hb : branchTaken .bne (reg n1 (29 : Fin 32)) (reg n1 x0) = decide (k + 1 < 11) := by
    rw [g, e29, r29, cnt11_dec k hk, u1'.zero]; exact cnt11_ne k hk
  have hc1 := CodeIn.store32 (v := (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
    (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
    U X CL CH).1) hc hS
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 (9 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.1 ∧
      reg n2 (28 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.2 ∧
      reg n2 (30 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 a2 = yp + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 a0 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 (29 : Fin 32) = BitVec.ofNat 32 (11 - (k + 1)) ∧
      ∀ q, dqBodyKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [h2, g, e9, r30, r12, r10, r7, r6, r9, r28, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e28, r30, r12, r10, r7, r6, r9, r28, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e30, r30, ptr4]
    · rw [h2, g, e12, r12, ptr4]
    · rw [h2, g, e10, r10, ptr4]
    · rw [h2, g, e29, r29, cnt11_dec k hk]
    · rw [h2, g]
      exact fr q (pkeep_ne (r := 30) hq rfl) (pkeep_ne (r := a2) hq rfl) (pkeep_ne (r := a0) hq rfl)
        (pkeep_ne (r := 9) hq rfl) (pkeep_ne (r := 28) hq rfl) (pkeep_ne (r := 29) hq rfl)
        (pkeep_ne (r := a3) hq rfl) (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a1) hq rfl)
        (pkeep_ne (r := a5) hq rfl) (pkeep_ne (r := 8) hq rfl)
  by_cases hl : k + 1 < 11
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x3D4 dp_at_41e (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0x422 dp_at_41e (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The inner loop**, from column `k + 1` of a pass to its end at 0x422:
columns `k + 1..11` of the pass. -/
theorem dq_inner {B acc yp np U X : Word} {M0 : Word → BitVec 8}
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0) (hw : acc.toNat + 48 ≤ 2 ^ 32)
    (hAY : Sep acc 48 yp 48) (hAN : Sep acc 48 np 48) (hAC : Sep acc 48 B p384DecompressCode.length) :
    ∀ m k, k + m + 1 = 11 → ∀ {M : Word → BitVec 8} {n : Machine} {CL CH : Word},
      St M B n 0x3D4 (reg n) → CodeIn M B p384DecompressCode →
      (∀ a, Sep acc 48 a 1 → M a = M0 a) →
      (∀ i, k ≤ i → i < 12 →
        memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) →
      2 ^ 32 * accV M acc k + (CL.toNat + 2 ^ 32 * CH.toNat) * 2 ^ (32 * (k + 1)) =
        X.toNat * accV M0 yp (k + 1) + accV M0 acc (k + 1) + U.toNat * accV M0 np (k + 1) →
      CL.toNat + 2 ^ 32 * CH.toNat ≤ 2 * 2 ^ 32 - 2 →
      reg n (30 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a2 = yp + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a0 = acc + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n (7 : Fin 32) = U → reg n (6 : Fin 32) = X → reg n (9 : Fin 32) = CL → reg n (28 : Fin 32) = CH →
      reg n (29 : Fin 32) = BitVec.ofNat 32 (11 - k) →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x422 (reg n') ∧ CodeIn M' B p384DecompressCode ∧
        2 ^ 32 * accV M' acc 11 + ((reg n' (9 : Fin 32)).toNat + 2 ^ 32 * (reg n' (28 : Fin 32)).toNat) * 2 ^ (32 * 12) =
          X.toNat * accV M0 yp 12 + accV M0 acc 12 + U.toNat * accV M0 np 12 ∧
        (reg n' (9 : Fin 32)).toNat + 2 ^ 32 * (reg n' (28 : Fin 32)).toNat ≤ 2 * 2 ^ 32 - 2 ∧
        (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
        memLoad32 M' (acc + BitVec.ofNat 32 (4 * 11)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * 11)) ∧
        reg n' (30 : Fin 32) = np + BitVec.ofNat 32 (4 * 12) ∧
        reg n' a2 = yp + BitVec.ofNat 32 (4 * 12) ∧
        reg n' a0 = acc + BitVec.ofNat 32 (4 * 12) ∧
        reg n' (29 : Fin 32) = 0 ∧
        ∀ q, dqBodyKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r30 r12 r10 r7 r6 r9 r28 r29
    have k10 : k = 10 := by omega
    subst k10
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (10 + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (10 + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (10 + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e9, e28, e30, e12, e10, e29, fr⟩ := dq_iter (k := 10) s hc (by decide) hnp hyp hacc
      (hAC.sub (by omega)) r30 r12 r10 r7 r6 r9 r28 r29
    rw [hcol] at u1 e9 e28
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step (k := 10) (by decide) hw hAY hAN hfr hab hinv hbd hcol
    refine ⟨n1, _, c1, u1, CodeIn.store32 hc (hAC.sub (by omega)), ?_, ?_, i3, i4 11 (by decide) (by decide),
      e30, e12, e10, e29, fr⟩
    · rw [e9, e28, show (12 : Nat) = 10 + 2 from rfl]; exact i1
    · rw [e9, e28]; exact i2
  | succ m ih =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r30 r12 r10 r7 r6 r9 r28 r29
    have hl : k + 1 < 11 := by omega
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e9, e28, e30, e12, e10, e29, fr⟩ := dq_iter (k := k) s hc (by omega) hnp hyp hacc
      (hAC.sub (by omega)) r30 r12 r10 r7 r6 r9 r28 r29
    rw [hcol] at u1 e9 e28
    rw [ite_eq_left hl] at u1
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step (k := k) (by omega) hw hAY hAN hfr hab hinv hbd hcol
    have k7 : reg n1 (7 : Fin 32) = U := by rw [fr _ rfl, r7]
    have k6 : reg n1 (6 : Fin 32) = X := by rw [fr _ rfl, r6]
    obtain ⟨n', M', c', u', hc', f1, f2, f3, f4, f30, f12, f10, f29, fr'⟩ :=
      ih (k + 1) (by omega) u1 (CodeIn.store32 hc (hAC.sub (by omega))) i3 i4 i1 i2 e30 e12 e10 k7 k6 e9 e28 e29
    exact ⟨n', M', c1.trans c', u', hc', f1, f2, f3, f4, f30, f12, f10, f29,
      fun q hq => by rw [fr' q hq, fr q hq]⟩

/-- The first column of a pass as `decompress` computes it, for P-384's
factor 1 and low modulus limb `2³² - 1`: the factor `u`, then the two-word
carry out. -/
def dqHead (Y0 X O0 N0 : Word) : Word × Word × Word :=
  let a0 := aluEval .mul Y0 X
  let a1 := aluEval .mulhu Y0 X
  let u := aluEval .add a0 O0
  let a2 := aluEval .mulhu u N0
  let c1 := aluEval .sltu u a0
  let h1 := aluEval .add c1 a1
  let c2 := aluEval .sltu 0 u
  let h2 := aluEval .add h1 a2
  let cl := aluEval .add c2 h2
  let o1 := aluEval .sltu h2 a2
  let o2 := aluEval .sltu cl h2
  (u, cl, aluEval .add o1 o2)

theorem sltu_neg (a : Word) :
    aluEval .sltu (aluEval .add a (aluEval .mul a 0xFFFFFFFF)) (aluEval .mul a 0xFFFFFFFF) = aluEval .sltu 0 a := by
  by_cases ha : a = 0
  · subst ha; decide
  · have hn : a.toNat ≠ 0 := fun h => ha (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hm : (a * 0xFFFFFFFF).toNat = 2 ^ 32 - a.toNat := by
      rw [BitVec.toNat_mul, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
      have := a.isLt
      rw [Nat.mul_sub, Nat.mul_one]
      rw [show a.toNat * 2 ^ 32 - a.toNat = (a.toNat - 1) * 2 ^ 32 + (2 ^ 32 - a.toNat) by
        rw [Nat.sub_mul, Nat.one_mul]; omega]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hs : (a + a * 0xFFFFFFFF).toNat = 0 := by
      rw [BitVec.toNat_add, hm]; have := a.isLt
      rw [show a.toNat + (2 ^ 32 - a.toNat) = 2 ^ 32 by omega]
    show (if (a + a * 0xFFFFFFFF).ult (a * 0xFFFFFFFF) then (1 : Word) else 0) = if (0 : Word).ult a then 1 else 0
    have l1 : (a + a * 0xFFFFFFFF).ult (a * 0xFFFFFFFF) = true := by
      simp only [BitVec.ult, hs, hm]; exact decide_eq_true (by have := a.isLt; omega)
    have l2 : (0 : Word).ult a = true := by
      simp only [BitVec.ult]; exact decide_eq_true (by show 0 < a.toNat; omega)
    rw [l1, l2]

theorem dqHead_eq (Y0 X O0 : Word) : dqHead Y0 X O0 0xFFFFFFFF = mmHead Y0 X O0 1 0xFFFFFFFF := by
  unfold dqHead mmHead
  simp only
  rw [show aluEval .add O0 (aluEval .mul Y0 X) = aluEval .add (aluEval .mul Y0 X) O0 from BitVec.add_comm _ _,
    show aluEval .mul 1 (aluEval .add (aluEval .mul Y0 X) O0) = aluEval .add (aluEval .mul Y0 X) O0 from
      BitVec.one_mul _, sltu_neg]

def dqHeadBlock : List BInstr :=
  [.aluImm .sll a0 (5 : Fin 32) 0x2, .alu .add a0 a0 (19 : Fin 32), .lw (6 : Fin 32) a0 0x0, .alu .mul a0 a6 (6 : Fin 32),
   .lw a4 (25 : Fin 32) 0x0, .alu .mulhu a1 a6 (6 : Fin 32), .alu .add (7 : Fin 32) a0 a4,
   .alu .mulhu a2 (7 : Fin 32) (23 : Fin 32), .alu .sltu a0 (7 : Fin 32) a0, .alu .add a0 a0 a1,
   .alu .sltu (9 : Fin 32) x0 (7 : Fin 32), .alu .add a0 a0 a2, .aluImm .add (29 : Fin 32) x0 0xB,
   .alu .add (9 : Fin 32) (9 : Fin 32) a0, .alu .sltu a1 a0 a2, .alu .sltu a0 (9 : Fin 32) a0,
   .alu .add (30 : Fin 32) x0 (21 : Fin 32), .alu .add (28 : Fin 32) a1 a0, .alu .add a0 x0 (26 : Fin 32),
   .alu .add a2 x0 (18 : Fin 32)]

def dqTailBlock : List BInstr :=
  [.alu .add (27 : Fin 32) (27 : Fin 32) (9 : Fin 32), .alu .add a1 (28 : Fin 32) (17 : Fin 32),
   .alu .sltu a0 (27 : Fin 32) (9 : Fin 32), .sw (25 : Fin 32) (27 : Fin 32) 0x2C, .alu .add (27 : Fin 32) a1 a0,
   .aluImm .add (5 : Fin 32) (5 : Fin 32) 0x1, .aluImm .add (17 : Fin 32) x0 0x0]

theorem dqHeadBlock_end : blockEnd p384DecompressCode 0x390 dqHeadBlock = some 0x3D0 := by decide
theorem dqTailBlock_end : blockEnd p384DecompressCode 0x422 dqTailBlock = some 0x438 := by decide

/-- The registers the start of a pass leaves alone. -/
def dqHeadKeep (q : Fin 32) : Bool := q.val ∉ [6, 7, 9, 10, 11, 12, 14, 28, 29, 30]

set_option maxRecDepth 20000 in
theorem dqHeadBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock dqHeadBlock (M, f)).1 = M ∧
    (runBlock dqHeadBlock (M, f)).2 (6 : Fin 32) =
      memLoad32 M (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (19 : Fin 32)) + 0) ∧
    (runBlock dqHeadBlock (M, f)).2 (7 : Fin 32) = (dqHead (f a6)
      (memLoad32 M (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (19 : Fin 32)) + 0))
      (memLoad32 M (f (25 : Fin 32) + 0)) (f (23 : Fin 32))).1 ∧
    (runBlock dqHeadBlock (M, f)).2 (9 : Fin 32) = (dqHead (f a6)
      (memLoad32 M (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (19 : Fin 32)) + 0))
      (memLoad32 M (f (25 : Fin 32) + 0)) (f (23 : Fin 32))).2.1 ∧
    (runBlock dqHeadBlock (M, f)).2 (28 : Fin 32) = (dqHead (f a6)
      (memLoad32 M (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (19 : Fin 32)) + 0))
      (memLoad32 M (f (25 : Fin 32) + 0)) (f (23 : Fin 32))).2.2 ∧
    (runBlock dqHeadBlock (M, f)).2 (29 : Fin 32) = BitVec.ofNat 32 (11 - 0) ∧
    (runBlock dqHeadBlock (M, f)).2 (30 : Fin 32) = f (21 : Fin 32) ∧
    (runBlock dqHeadBlock (M, f)).2 a0 = f (26 : Fin 32) ∧
    (runBlock dqHeadBlock (M, f)).2 a2 = f (18 : Fin 32) ∧
    ∀ q, dqHeadKeep q = true → (runBlock dqHeadBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, dqHeadBlock]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := 6) hq rfl, pkeep_ne (r := 7) hq rfl, pkeep_ne (r := 9) hq rfl,
        pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a4) hq rfl,
        pkeep_ne (r := 28) hq rfl, pkeep_ne (r := 29) hq rfl, pkeep_ne (r := 30) hq rfl]

theorem dqHeadBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hx : (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (19 : Fin 32)) + 0).toNat % 4 = 0)
    (hs : (f (25 : Fin 32) + 0).toNat % 4 = 0) : BlockOk base len dqHeadBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, dqHeadBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hx, hs⟩

/-- The registers the end of a pass leaves alone. -/
def dqTailKeep (q : Fin 32) : Bool := q.val ∉ [5, 10, 11, 17, 27]

set_option maxRecDepth 20000 in
theorem dqTailBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock dqTailBlock (M, f)).1 = memStore32 M (f (25 : Fin 32) + 0x2C) (aluEval .add (f (27 : Fin 32)) (f (9 : Fin 32))) ∧
    (runBlock dqTailBlock (M, f)).2 (27 : Fin 32) = aluEval .add (aluEval .add (f (28 : Fin 32)) (f (17 : Fin 32)))
      (aluEval .sltu (aluEval .add (f (27 : Fin 32)) (f (9 : Fin 32))) (f (9 : Fin 32))) ∧
    (runBlock dqTailBlock (M, f)).2 (5 : Fin 32) = f (5 : Fin 32) + 1 ∧
    (runBlock dqTailBlock (M, f)).2 (17 : Fin 32) = 0 ∧
    ∀ q, dqTailKeep q = true → (runBlock dqTailBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, dqTailBlock]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
        pkeep_ne (r := 27) hq rfl, pkeep_ne (r := 17) hq rfl, pkeep_ne (r := 5) hq rfl]

theorem dqTailBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hs : (f (25 : Fin 32) + 0x2C).toNat % 4 = 0) (hsep : Sep (f (25 : Fin 32) + 0x2C) 4 base len) :
    BlockOk base len dqTailBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, dqTailBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hs, hsep⟩

/-- The registers a pass leaves alone. -/
def dqPassKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 27, 28, 29, 30]

theorem dqPassKeep_head : ∀ q, dqPassKeep q = true → dqHeadKeep q = true := by decide
theorem dqPassKeep_body : ∀ q, dqPassKeep q = true → dqBodyKeep q = true := by decide
theorem dqPassKeep_tail : ∀ q, dqPassKeep q = true → dqTailKeep q = true := by decide

set_option exponentiation.threshold 400 in
/-- **One pass of the outer loop**, from 0x390: add limb `i` of the operand
times the operand, and `u` times the modulus, to the accumulator and its top
carry in `s11`, and shift the sum down a word. -/
theorem dq_pass {B acc xp np : Word} {M0 : Word → BitVec 8} {i : Nat} (hi : i < 12)
    (hxp : xp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAX : Sep acc 48 xp 48) (hAN : Sep acc 48 np 48)
    (hAC : Sep acc 48 B p384DecompressCode.length) (hN0 : memLoad32 M0 np = 0xFFFFFFFF)
    {M : Word → BitVec 8} {n : Machine} (s : St M B n 0x390 (reg n)) (hc : CodeIn M B p384DecompressCode)
    (hfr : ∀ a, Sep acc 48 a 1 → M a = M0 a)
    (r5 : reg n (5 : Fin 32) = BitVec.ofNat 32 i) (r19 : reg n (19 : Fin 32) = xp)
    (r16 : reg n a6 = memLoad32 M0 xp) (r23 : reg n (23 : Fin 32) = 0xFFFFFFFF) (r25 : reg n (25 : Fin 32) = acc)
    (r21 : reg n (21 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)))
    (r26 : reg n (26 : Fin 32) = acc + BitVec.ofNat 32 (4 * (0 + 1)))
    (r18 : reg n (18 : Fin 32) = xp + BitVec.ofNat 32 (4 * (0 + 1)))
    (r17 : reg n (17 : Fin 32) = 0) (r22 : reg n (22 : Fin 32) = 12) :
    ∃ n' M', Steps n n' ∧ St M' B n' (if i + 1 < 12 then 0x390 else 0x43C) (reg n') ∧
      CodeIn M' B p384DecompressCode ∧ (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
      (∃ u : Nat, u < 2 ^ 32 ∧ 2 ^ 32 * (accV M' acc 12 + (reg n' (27 : Fin 32)).toNat * 2 ^ (32 * 12)) =
        accV M acc 12 + (reg n (27 : Fin 32)).toNat * 2 ^ (32 * 12) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 xp 12 + u * accV M0 np 12) ∧
      reg n' (5 : Fin 32) = BitVec.ofNat 32 (i + 1) ∧ reg n' (17 : Fin 32) = 0 ∧
      ∀ q, dqPassKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hX : aluEval .add (aluEval .sll (reg n (5 : Fin 32)) 2) (reg n (19 : Fin 32)) + 0 =
      xp + BitVec.ofNat 32 (4 * i) := by
    rw [r5, r19, sll12 i hi, add_lit_zero]; exact BitVec.add_comm _ _
  have ok1 := dqHeadBlock_ok (M := M) (f := reg n) (base := B) (len := p384DecompressCode.length)
    (by rw [hX]; exact aligned_add hxp (by omega)) (by rw [r25, add_lit_zero]; exact hacc)
  obtain ⟨n1, c1, u1⟩ := St.block dqHeadBlock s hc dqHeadBlock_end ok1
  obtain ⟨hm1, h6, h7, h9, h28, h29, h30, h10, h12, hfr1⟩ := dqHeadBlock_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [hm1] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock dqHeadBlock (M, reg n)).2 q := u1.regs
  rw [hX] at h6 h7 h9 h28
  rw [r25, add_lit_zero, r16, r23, dqHead_eq] at h7 h9 h28
  have eX : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
    load_frame hfr (hAX.subR (by omega))
  obtain ⟨u, cl, ch, hH⟩ : ∃ u cl ch, mmHead (memLoad32 M0 xp) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
      (memLoad32 M acc) 1 0xFFFFFFFF = (u, cl, ch) := ⟨_, _, _, rfl⟩
  have hd := mm_head (memLoad32 M0 xp) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) (memLoad32 M acc) 1
    0xFFFFFFFF (by decide)
  rw [hH] at hd h7 h9 h28
  simp only at hd h7 h9 h28
  obtain ⟨hd, bd⟩ := hd
  have hb : branchTaken .beq (reg n1 (29 : Fin 32)) (reg n1 x0) = false := by
    rw [g1, h29, u1'.zero]; decide
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc 0x3D4 dp_at_3d0 (by decide) hb
  have g2 : ∀ q, reg n2 q = (runBlock dqHeadBlock (M, reg n)).2 q := fun q => by rw [u2.regs, g1]
  have eY0 : memLoad32 M (xp + BitVec.ofNat 32 (4 * 0)) = memLoad32 M0 xp := by
    rw [load_frame hfr (hAX.subR (c := 4 * 0) (l := 4) (by omega)), Nat.mul_zero, add_ofNat_zero]
  have eN0 : memLoad32 M (np + BitVec.ofNat 32 (4 * 0)) = 0xFFFFFFFF := by
    rw [load_frame hfr (hAN.subR (c := 4 * 0) (l := 4) (by omega)), Nat.mul_zero, add_ofNat_zero, hN0]
  have eO0 : memLoad32 M (acc + BitVec.ofNat 32 (4 * 0)) = memLoad32 M acc := by
    rw [Nat.mul_zero, add_ofNat_zero]
  have inv0 : 2 ^ 32 * accV M acc 0 + (cl.toNat + 2 ^ 32 * ch.toNat) * 2 ^ (32 * (0 + 1)) =
      (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M xp (0 + 1) + accV M acc (0 + 1) +
        u.toNat * accV M np (0 + 1) := by
    show 2 ^ 32 * 0 + _ * 2 ^ 32 = _ * (0 + (memLoad32 M (xp + BitVec.ofNat 32 (4 * 0))).toNat * 1) +
      (0 + (memLoad32 M (acc + BitVec.ofNat 32 (4 * 0))).toNat * 1) +
      _ * (0 + (memLoad32 M (np + BitVec.ofNat 32 (4 * 0))).toNat * 1)
    rw [eY0, eN0, eO0]
    simp only [Nat.zero_add, Nat.mul_one, Nat.mul_zero]
    omega
  obtain ⟨n3, M1, c3, u3, hc3, I1, I2, I3, I4, f30, f12, f10, f29, fr3⟩ :=
    dq_inner (M0 := M) (U := u) (X := memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) hnp hxp hacc hw hAX hAN hAC
      10 0 (by decide) u2.self hc (fun _ _ => rfl) (fun _ _ _ => rfl) inv0 bd
      (by rw [g2, h30, r21]) (by rw [g2, h12, r18]) (by rw [g2, h10, r26]) (by rw [g2, h7]) (by rw [g2, h6])
      (by rw [g2, h9]) (by rw [g2, h28]) (by rw [g2, h29])
  have k3 : ∀ q, dqPassKeep q = true → reg n3 q = reg n q := fun q hq => by
    rw [fr3 q (dqPassKeep_body q hq), g2, hfr1 q (dqPassKeep_head q hq)]
  have hb3 : ∀ q, dqHeadKeep q = true → dqBodyKeep q = true → reg n3 q = reg n q := fun q h1 h2 => by
    rw [fr3 q h2, g2, hfr1 q h1]
  have s25 : reg n3 (25 : Fin 32) = acc := by rw [k3 _ rfl, r25]
  have hacc44 : acc + 0x2C = acc + BitVec.ofNat 32 (4 * 11) := rfl
  have ok3 := dqTailBlock_ok (M := M1) (f := reg n3) (base := B) (len := p384DecompressCode.length)
    (by rw [s25, hacc44]; exact aligned_add hacc (by omega)) (by rw [s25, hacc44]; exact hAC.sub (by omega))
  obtain ⟨n4, c4, u4⟩ := St.block dqTailBlock u3 hc3 dqTailBlock_end ok3
  obtain ⟨hm4, t27, t5, t17, tfr⟩ := dqTailBlock_run (M := M1) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [hm4, s25, hacc44] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock dqTailBlock (M1, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := aluEval .add (reg n3 (27 : Fin 32)) (reg n3 (9 : Fin 32))) hc3
    (hAC.sub (c := 4 * 11) (by omega))
  have e5 : reg n4 (5 : Fin 32) = BitVec.ofNat 32 (i + 1) := by
    rw [g4, t5, hb3 (5 : Fin 32) rfl rfl, r5, ofNat_succ]
  have e17 : reg n4 (17 : Fin 32) = 0 := by rw [g4, t17]
  have k4 : ∀ q, dqPassKeep q = true → reg n4 q = reg n q := fun q hq => by
    rw [g4, tfr q (dqPassKeep_tail q hq), k3 q hq]
  have hb4 : branchTaken .bne (reg n4 (5 : Fin 32)) (reg n4 (22 : Fin 32)) = decide (i + 1 < 12) := by
    rw [e5, k4 _ rfl, r22]; exact pass_ne i hi
  have arith : 2 ^ 32 * (accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 11))
        (aluEval .add (reg n3 (27 : Fin 32)) (reg n3 (9 : Fin 32)))) acc 12 + (reg n4 (27 : Fin 32)).toNat * 2 ^ (32 * 12)) =
      accV M acc 12 + (reg n (27 : Fin 32)).toNat * 2 ^ (32 * 12) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 xp 12 + u.toNat * accV M0 np 12 := by
    have hA : accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 11)) (aluEval .add (reg n3 (27 : Fin 32)) (reg n3 (9 : Fin 32))))
        acc 12 = accV M1 acc 11 + (aluEval .add (reg n3 (27 : Fin 32)) (reg n3 (9 : Fin 32))).toNat * 2 ^ (32 * 11) := by
      rw [show (12 : Nat) = 11 + 1 from rfl, accV_succ1, accV_store_above (by omega) 11 (Nat.le_refl 11),
        memLoad32_store32_same]
    have ac := add_carry (reg n3 (27 : Fin 32)) (reg n3 (9 : Fin 32))
    have hch : (reg n3 (28 : Fin 32)).toNat ≤ 1 := by omega
    have hcy : (aluEval .sltu (aluEval .add (reg n3 (27 : Fin 32)) (reg n3 (9 : Fin 32))) (reg n3 (9 : Fin 32))).toNat ≤ 1 := by
      have := (reg n3 (27 : Fin 32)).isLt; have := (reg n3 (9 : Fin 32)).isLt; omega
    have h27 : (reg n4 (27 : Fin 32)).toNat = (reg n3 (28 : Fin 32)).toNat +
        (aluEval .sltu (aluEval .add (reg n3 (27 : Fin 32)) (reg n3 (9 : Fin 32))) (reg n3 (9 : Fin 32))).toNat := by
      rw [g4, t27, hb3 (17 : Fin 32) rfl rfl, r17, show aluEval .add (reg n3 (28 : Fin 32)) 0 = reg n3 (28 : Fin 32) from
        BitVec.add_zero _, add_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    have p12 : (2 : Nat) ^ (32 * 12) = 2 ^ (32 * 11) * 2 ^ 32 := pow32_succ 11
    rw [eX, accV_frame48 (b := xp) (n := 12) hfr hAX, accV_frame48 (b := np) (n := 12) hfr hAN, p12] at I1
    rw [hA, h27, p12, hb3 (27 : Fin 32) rfl rfl]
    rw [hb3 (27 : Fin 32) rfl rfl] at ac
    exact mm_tail_arith I1 ac
  have fr4 : ∀ a, Sep acc 48 a 1 → memStore32 M1 (acc + BitVec.ofNat 32 (4 * 11))
      (aluEval .add (reg n3 (27 : Fin 32)) (reg n3 (9 : Fin 32))) a = M0 a := fun a ha => by
    rw [memStore32_ne fun j hj e => (ha.point (i := 4 * 11 + j) (j := 0) (by omega) (by decide)) (by
      rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm), I3 a ha, hfr a ha]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x390 dp_at_438 (by decide) (by rw [hb4]; exact decide_eq_true hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e5], by rw [g5, e17], fun q hq => by rw [g5, k4 q hq]⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x43C dp_at_438 (by decide) (by rw [hb4]; exact decide_eq_false hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e5], by rw [g5, e17], fun q hq => by rw [g5, k4 q hq]⟩

set_option exponentiation.threshold 400 in
/-- **The outer loop**, from pass `i` to its end at 0x43C. The accumulator
and its top carry hold a sum `T` with `2^(32 i) T = X_i X + U N`, for `X_i`
the operand's low `i` limbs and some `U`, and `T < 2N`. -/
theorem dq_outer {B acc xp np : Word} {M0 : Word → BitVec 8}
    (hxp : xp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAX : Sep acc 48 xp 48) (hAN : Sep acc 48 np 48)
    (hAC : Sep acc 48 B p384DecompressCode.length) (hN0 : memLoad32 M0 np = 0xFFFFFFFF)
    (hYN : accV M0 xp 12 < accV M0 np 12) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x390 (reg n) → CodeIn M B p384DecompressCode → (∀ a, Sep acc 48 a 1 → M a = M0 a) →
      (∃ U, 2 ^ (32 * i) * (accV M acc 12 + (reg n (27 : Fin 32)).toNat * 2 ^ (32 * 12)) =
        accV M0 xp i * accV M0 xp 12 + U * accV M0 np 12) →
      accV M acc 12 + (reg n (27 : Fin 32)).toNat * 2 ^ (32 * 12) < 2 * accV M0 np 12 →
      reg n (5 : Fin 32) = BitVec.ofNat 32 i → reg n (19 : Fin 32) = xp →
      reg n a6 = memLoad32 M0 xp → reg n (23 : Fin 32) = 0xFFFFFFFF → reg n (25 : Fin 32) = acc →
      reg n (21 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (26 : Fin 32) = acc + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (18 : Fin 32) = xp + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (17 : Fin 32) = 0 → reg n (22 : Fin 32) = 12 →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x43C (reg n') ∧ CodeIn M' B p384DecompressCode ∧
        (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
        (∃ U, 2 ^ (32 * 12) * (accV M' acc 12 + (reg n' (27 : Fin 32)).toNat * 2 ^ (32 * 12)) =
          accV M0 xp 12 * accV M0 xp 12 + U * accV M0 np 12) ∧
        accV M' acc 12 + (reg n' (27 : Fin 32)).toNat * 2 ^ (32 * 12) < 2 * accV M0 np 12 ∧
        ∀ q, dqPassKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hinv hbd r5 r19 r16 r23 r25 r21 r26 r18 r17 r22
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e5, e17, k1⟩ := dq_pass (i := 11) (by decide) hxp hnp hacc
      hw hAX hAN hAC hN0 s hc hfr r5 r19 r16 r23 r25 r21 r26 r18 r17 r22
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * 11))).isLt hu hYN
    refine ⟨n1, M1, c1, u1, hc1, hf1, ⟨U + 2 ^ (32 * 11) * u, ?_⟩, a2, k1⟩
    rw [pow32_succ 11] at a1 ⊢
    rw [a1, accV_succ1 M0 xp 11]
  | succ m ih =>
    intro i hi M n s hc hfr hinv hbd r5 r19 r16 r23 r25 r21 r26 r18 r17 r22
    have hl : i + 1 < 12 := idx_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e5, e17, k1⟩ := dq_pass (i := i)
      (Nat.lt_trans (Nat.lt_succ_self i) hl) hxp hnp hacc hw hAX hAN hAC hN0 s hc hfr r5 r19 r16 r23 r25 r21 r26
      r18 r17 r22
    rw [ite_eq_left hl] at u1
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).isLt hu hYN
    have inv1 : ∃ U, 2 ^ (32 * (i + 1)) * (accV M1 acc 12 + (reg n1 (27 : Fin 32)).toNat * 2 ^ (32 * 12)) =
        accV M0 xp (i + 1) * accV M0 xp 12 + U * accV M0 np 12 :=
      ⟨U + 2 ^ (32 * i) * u, by rw [pow32_succ i, a1, accV_succ1 M0 xp i]⟩
    obtain ⟨n', M', c', u', hc', hf', hv', hb', k'⟩ := ih (i + 1) (idx_succ hi) u1 hc1 hf1 inv1 a2 e5
      (by rw [k1 _ rfl, r19]) (by rw [k1 _ rfl, r16]) (by rw [k1 _ rfl, r23]) (by rw [k1 _ rfl, r25])
      (by rw [k1 _ rfl, r21]) (by rw [k1 _ rfl, r26]) (by rw [k1 _ rfl, r18]) e17 (by rw [k1 _ rfl, r22])
    exact ⟨n', M', c1.trans c', u', hc', hf', hv', hb', fun q hq => by rw [k' q hq, k1 q hq]⟩

end C3.RV32.Dq
