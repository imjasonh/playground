import C3BootProofs.Proofs.Dec256Calls

/-!
# P-256 point decompression: the inlined Montgomery squaring

`AffinePoint<NistP256>::decompress` raises `x³ + ax + b` to `(p + 1) / 4`
with crypto-bigint's windowed exponentiation, inlined. Its squarings are an
inlined copy of `mul_montgomery_form::<8>`'s loop, specialized to P-256:
the Montgomery factor `-p⁻¹ mod 2³²` is 1 and the modulus's low limb is
`2³² - 1`. This file proves that loop over the arithmetic lemmas of
`MontMul12.lean` and `MontMul8.lean`, as `Dec384Sq.lean` does for P-384.
-/

namespace C3.RV32.Gd

open C3.Image C3.RV32.Dq

set_option maxRecDepth 20000


theorem gdBody_end : blockEnd p256DecompressCode 0x39C dqBody = some 0x3E6 := by decide

/-- **One pass of the inner loop**, from 0x39C: column `k + 1` of a pass,
which stores the accumulator's word `k`. -/
theorem gd_iter {M : Word → BitVec 8} {B np yp acc U X CL CH : Word} {n : Machine} {k : Nat}
    (s : St M B n 0x39C (reg n)) (hc : CodeIn M B p256DecompressCode) (hk : k < 7)
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hS : Sep (acc + BitVec.ofNat 32 (4 * k)) 4 B p256DecompressCode.length)
    (r30 : reg n (30 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)))
    (r12 : reg n a2 = yp + BitVec.ofNat 32 (4 * (k + 1)))
    (r10 : reg n a0 = acc + BitVec.ofNat 32 (4 * (k + 1)))
    (r7 : reg n (7 : Fin 32) = U) (r6 : reg n (6 : Fin 32) = X) (r9 : reg n (9 : Fin 32) = CL)
    (r28 : reg n (28 : Fin 32) = CH) (r29 : reg n (29 : Fin 32) = BitVec.ofNat 32 (7 - k)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (acc + BitVec.ofNat 32 (4 * k))
        (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1))))
          (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) U X CL CH).1)
        B n' (if k + 1 < 7 then 0x39C else 0x3EA) (reg n') ∧
      reg n' (9 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.1 ∧
      reg n' (28 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.2 ∧
      reg n' (30 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a2 = yp + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a0 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (29 : Fin 32) = BitVec.ofNat 32 (7 - (k + 1)) ∧
      ∀ q, dqBodyKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have ok := dqBody_ok (M := M) (f := reg n) (base := B) (len := p256DecompressCode.length)
    (by rw [r30, add_lit_zero]; exact aligned_add hnp (by omega))
    (by rw [r12, add_lit_zero]; exact aligned_add hyp (by omega))
    (by rw [r10, add_lit_zero]; exact aligned_add hacc (by omega))
    (by rw [r10, back4 acc k]; exact aligned_add hacc (by omega))
    (by rw [r10, back4 acc k]; exact hS)
  obtain ⟨n1, c1, u1⟩ := St.block dqBody s hc gdBody_end ok
  obtain ⟨em, e9, e28, e30, e12, e10, e29, fr⟩ := dqBody_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [em, r30, r12, r10, r7, r6, r9, r28, add_lit_zero, add_lit_zero, add_lit_zero, back4 acc k] at u1'
  have g : ∀ q, reg n1 q = (runBlock dqBody (M, reg n)).2 q := u1.regs
  have hb : branchTaken .bne (reg n1 (29 : Fin 32)) (reg n1 x0) = decide (k + 1 < 7) := by
    rw [g, e29, r29, cnt7_dec k hk, u1'.zero]; exact cnt7_ne k hk
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
      reg n2 (29 : Fin 32) = BitVec.ofNat 32 (7 - (k + 1)) ∧
      ∀ q, dqBodyKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [h2, g, e9, r30, r12, r10, r7, r6, r9, r28, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e28, r30, r12, r10, r7, r6, r9, r28, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e30, r30, ptr4]
    · rw [h2, g, e12, r12, ptr4]
    · rw [h2, g, e10, r10, ptr4]
    · rw [h2, g, e29, r29, cnt7_dec k hk]
    · rw [h2, g]
      exact fr q (pkeep_ne (r := 30) hq rfl) (pkeep_ne (r := a2) hq rfl) (pkeep_ne (r := a0) hq rfl)
        (pkeep_ne (r := 9) hq rfl) (pkeep_ne (r := 28) hq rfl) (pkeep_ne (r := 29) hq rfl)
        (pkeep_ne (r := a3) hq rfl) (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a1) hq rfl)
        (pkeep_ne (r := a5) hq rfl) (pkeep_ne (r := 8) hq rfl)
  by_cases hl : k + 1 < 7
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x39C gd_at_3e6 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0x3EA gd_at_3e6 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The inner loop**, from column `k + 1` of a pass to its end at 0x3EA:
columns `k + 1..11` of the pass. -/
theorem gd_inner {B acc yp np U X : Word} {M0 : Word → BitVec 8}
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0) (hw : acc.toNat + 32 ≤ 2 ^ 32)
    (hAY : Sep acc 32 yp 32) (hAN : Sep acc 32 np 32) (hAC : Sep acc 32 B p256DecompressCode.length) :
    ∀ m k, k + m + 1 = 7 → ∀ {M : Word → BitVec 8} {n : Machine} {CL CH : Word},
      St M B n 0x39C (reg n) → CodeIn M B p256DecompressCode →
      (∀ a, Sep acc 32 a 1 → M a = M0 a) →
      (∀ i, k ≤ i → i < 8 →
        memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) →
      2 ^ 32 * accV M acc k + (CL.toNat + 2 ^ 32 * CH.toNat) * 2 ^ (32 * (k + 1)) =
        X.toNat * accV M0 yp (k + 1) + accV M0 acc (k + 1) + U.toNat * accV M0 np (k + 1) →
      CL.toNat + 2 ^ 32 * CH.toNat ≤ 2 * 2 ^ 32 - 2 →
      reg n (30 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a2 = yp + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a0 = acc + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n (7 : Fin 32) = U → reg n (6 : Fin 32) = X → reg n (9 : Fin 32) = CL → reg n (28 : Fin 32) = CH →
      reg n (29 : Fin 32) = BitVec.ofNat 32 (7 - k) →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x3EA (reg n') ∧ CodeIn M' B p256DecompressCode ∧
        2 ^ 32 * accV M' acc 7 + ((reg n' (9 : Fin 32)).toNat + 2 ^ 32 * (reg n' (28 : Fin 32)).toNat) * 2 ^ (32 * 8) =
          X.toNat * accV M0 yp 8 + accV M0 acc 8 + U.toNat * accV M0 np 8 ∧
        (reg n' (9 : Fin 32)).toNat + 2 ^ 32 * (reg n' (28 : Fin 32)).toNat ≤ 2 * 2 ^ 32 - 2 ∧
        (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
        memLoad32 M' (acc + BitVec.ofNat 32 (4 * 7)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * 7)) ∧
        reg n' (30 : Fin 32) = np + BitVec.ofNat 32 (4 * 8) ∧
        reg n' a2 = yp + BitVec.ofNat 32 (4 * 8) ∧
        reg n' a0 = acc + BitVec.ofNat 32 (4 * 8) ∧
        reg n' (29 : Fin 32) = 0 ∧
        ∀ q, dqBodyKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r30 r12 r10 r7 r6 r9 r28 r29
    have k10 : k = 6 := by omega
    subst k10
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (6 + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (6 + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (6 + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e9, e28, e30, e12, e10, e29, fr⟩ := gd_iter (k := 6) s hc (by decide) hnp hyp hacc
      (hAC.sub (by omega)) r30 r12 r10 r7 r6 r9 r28 r29
    rw [hcol] at u1 e9 e28
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step8 (k := 6) (by decide) hw hAY hAN hfr hab hinv hbd hcol
    refine ⟨n1, _, c1, u1, CodeIn.store32 hc (hAC.sub (by omega)), ?_, ?_, i3, i4 7 (by decide) (by decide),
      e30, e12, e10, e29, fr⟩
    · rw [e9, e28, show (8 : Nat) = 6 + 2 from rfl]; exact i1
    · rw [e9, e28]; exact i2
  | succ m ih =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r30 r12 r10 r7 r6 r9 r28 r29
    have hl : k + 1 < 7 := by omega
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e9, e28, e30, e12, e10, e29, fr⟩ := gd_iter (k := k) s hc (by omega) hnp hyp hacc
      (hAC.sub (by omega)) r30 r12 r10 r7 r6 r9 r28 r29
    rw [hcol] at u1 e9 e28
    rw [ite_eq_left hl] at u1
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step8 (k := k) (by omega) hw hAY hAN hfr hab hinv hbd hcol
    have k7 : reg n1 (7 : Fin 32) = U := by rw [fr _ rfl, r7]
    have k6 : reg n1 (6 : Fin 32) = X := by rw [fr _ rfl, r6]
    obtain ⟨n', M', c', u', hc', f1, f2, f3, f4, f30, f12, f10, f29, fr'⟩ :=
      ih (k + 1) (by omega) u1 (CodeIn.store32 hc (hAC.sub (by omega))) i3 i4 i1 i2 e30 e12 e10 k7 k6 e9 e28 e29
    exact ⟨n', M', c1.trans c', u', hc', f1, f2, f3, f4, f30, f12, f10, f29,
      fun q hq => by rw [fr' q hq, fr q hq]⟩

def gdHeadBlock : List BInstr :=
  [.aluImm .sll a0 (5 : Fin 32) 0x2, .alu .add a0 a0 (18 : Fin 32), .lw (6 : Fin 32) a0 0x0, .alu .mul a0 a6 (6 : Fin 32),
   .lw a4 sp 0x67C, .alu .mulhu a1 a6 (6 : Fin 32), .alu .add (7 : Fin 32) a0 a4,
   .alu .mulhu a2 (7 : Fin 32) (22 : Fin 32), .alu .sltu a0 (7 : Fin 32) a0, .alu .add a0 a0 a1,
   .alu .sltu (9 : Fin 32) x0 (7 : Fin 32), .alu .add a0 a0 a2, .aluImm .add (29 : Fin 32) x0 0x7,
   .alu .add (9 : Fin 32) (9 : Fin 32) a0, .alu .sltu a1 a0 a2, .alu .sltu a0 (9 : Fin 32) a0,
   .alu .add (30 : Fin 32) x0 (21 : Fin 32), .alu .add (28 : Fin 32) a1 a0, .alu .add a0 x0 (25 : Fin 32),
   .alu .add a2 x0 (19 : Fin 32)]

def gdTailBlock : List BInstr :=
  [.alu .add (20 : Fin 32) (20 : Fin 32) (9 : Fin 32), .alu .add a1 (28 : Fin 32) (17 : Fin 32),
   .alu .sltu a0 (20 : Fin 32) (9 : Fin 32), .sw sp (20 : Fin 32) 0x698, .alu .add (20 : Fin 32) a1 a0,
   .aluImm .add (5 : Fin 32) (5 : Fin 32) 0x1, .aluImm .add (17 : Fin 32) x0 0x0]

theorem gdHeadBlock_end : blockEnd p256DecompressCode 0x358 gdHeadBlock = some 0x398 := by decide
theorem gdTailBlock_end : blockEnd p256DecompressCode 0x3EA gdTailBlock = some 0x400 := by decide

/-- The registers the start of a pass leaves alone. -/
def gdHeadKeep (q : Fin 32) : Bool := q.val ∉ [6, 7, 9, 10, 11, 12, 14, 28, 29, 30]

set_option maxRecDepth 20000 in
theorem gdHeadBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock gdHeadBlock (M, f)).1 = M ∧
    (runBlock gdHeadBlock (M, f)).2 (6 : Fin 32) =
      memLoad32 M (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (18 : Fin 32)) + 0) ∧
    (runBlock gdHeadBlock (M, f)).2 (7 : Fin 32) = (dqHead (f a6)
      (memLoad32 M (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (18 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0x67C)) (f (22 : Fin 32))).1 ∧
    (runBlock gdHeadBlock (M, f)).2 (9 : Fin 32) = (dqHead (f a6)
      (memLoad32 M (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (18 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0x67C)) (f (22 : Fin 32))).2.1 ∧
    (runBlock gdHeadBlock (M, f)).2 (28 : Fin 32) = (dqHead (f a6)
      (memLoad32 M (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (18 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0x67C)) (f (22 : Fin 32))).2.2 ∧
    (runBlock gdHeadBlock (M, f)).2 (29 : Fin 32) = BitVec.ofNat 32 (7 - 0) ∧
    (runBlock gdHeadBlock (M, f)).2 (30 : Fin 32) = f (21 : Fin 32) ∧
    (runBlock gdHeadBlock (M, f)).2 a0 = f (25 : Fin 32) ∧
    (runBlock gdHeadBlock (M, f)).2 a2 = f (19 : Fin 32) ∧
    ∀ q, gdHeadKeep q = true → (runBlock gdHeadBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, gdHeadBlock]
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

theorem gdHeadBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hx : (aluEval .add (aluEval .sll (f (5 : Fin 32)) 2) (f (18 : Fin 32)) + 0).toNat % 4 = 0)
    (hs : (f sp + 0x67C).toNat % 4 = 0) : BlockOk base len gdHeadBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, gdHeadBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hx, hs⟩

/-- The registers the end of a pass leaves alone. -/
def gdTailKeep (q : Fin 32) : Bool := q.val ∉ [5, 10, 11, 17, 20]

set_option maxRecDepth 20000 in
theorem gdTailBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock gdTailBlock (M, f)).1 = memStore32 M (f sp + 0x698) (aluEval .add (f (20 : Fin 32)) (f (9 : Fin 32))) ∧
    (runBlock gdTailBlock (M, f)).2 (20 : Fin 32) = aluEval .add (aluEval .add (f (28 : Fin 32)) (f (17 : Fin 32)))
      (aluEval .sltu (aluEval .add (f (20 : Fin 32)) (f (9 : Fin 32))) (f (9 : Fin 32))) ∧
    (runBlock gdTailBlock (M, f)).2 (5 : Fin 32) = f (5 : Fin 32) + 1 ∧
    (runBlock gdTailBlock (M, f)).2 (17 : Fin 32) = 0 ∧
    ∀ q, gdTailKeep q = true → (runBlock gdTailBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, gdTailBlock]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
        pkeep_ne (r := 20) hq rfl, pkeep_ne (r := 17) hq rfl, pkeep_ne (r := 5) hq rfl]

theorem gdTailBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hs : (f sp + 0x698).toNat % 4 = 0) (hsep : Sep (f sp + 0x698) 4 base len) :
    BlockOk base len gdTailBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, gdTailBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hs, hsep⟩

/-- The registers a pass leaves alone. -/
def gdPassKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 20, 28, 29, 30]

theorem gdPassKeep_head : ∀ q, gdPassKeep q = true → gdHeadKeep q = true := by decide
theorem gdPassKeep_body : ∀ q, gdPassKeep q = true → dqBodyKeep q = true := by decide
theorem gdPassKeep_tail : ∀ q, gdPassKeep q = true → gdTailKeep q = true := by decide

set_option exponentiation.threshold 400 in
/-- **One pass of the outer loop**, from 0x358: add limb `i` of the operand
times the operand, and `u` times the modulus, to the accumulator and its top
carry in `s4`, and shift the sum down a word. -/
theorem gd_pass {B acc xp np : Word} {M0 : Word → BitVec 8} {i : Nat} (hi : i < 8)
    (hxp : xp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAX : Sep acc 32 xp 32) (hAN : Sep acc 32 np 32)
    (hAC : Sep acc 32 B p256DecompressCode.length) (hN0 : memLoad32 M0 np = 0xFFFFFFFF)
    {M : Word → BitVec 8} {n : Machine} (s : St M B n 0x358 (reg n)) (hc : CodeIn M B p256DecompressCode)
    (hfr : ∀ a, Sep acc 32 a 1 → M a = M0 a)
    (r5 : reg n (5 : Fin 32) = BitVec.ofNat 32 i) (r18 : reg n (18 : Fin 32) = xp)
    (r16 : reg n a6 = memLoad32 M0 xp) (r22 : reg n (22 : Fin 32) = 0xFFFFFFFF) (rsp : reg n sp + 0x67C = acc)
    (r21 : reg n (21 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)))
    (r25 : reg n (25 : Fin 32) = acc + BitVec.ofNat 32 (4 * (0 + 1)))
    (r19 : reg n (19 : Fin 32) = xp + BitVec.ofNat 32 (4 * (0 + 1)))
    (r17 : reg n (17 : Fin 32) = 0) (r27 : reg n (27 : Fin 32) = 8) :
    ∃ n' M', Steps n n' ∧ St M' B n' (if i + 1 < 8 then 0x358 else 0x404) (reg n') ∧
      CodeIn M' B p256DecompressCode ∧ (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
      (∃ u : Nat, u < 2 ^ 32 ∧ 2 ^ 32 * (accV M' acc 8 + (reg n' (20 : Fin 32)).toNat * 2 ^ (32 * 8)) =
        accV M acc 8 + (reg n (20 : Fin 32)).toNat * 2 ^ (32 * 8) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 xp 8 + u * accV M0 np 8) ∧
      reg n' (5 : Fin 32) = BitVec.ofNat 32 (i + 1) ∧ reg n' (17 : Fin 32) = 0 ∧
      ∀ q, gdPassKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hX : aluEval .add (aluEval .sll (reg n (5 : Fin 32)) 2) (reg n (18 : Fin 32)) + 0 =
      xp + BitVec.ofNat 32 (4 * i) := by
    rw [r5, r18, sll8 i hi, add_lit_zero]; exact BitVec.add_comm _ _
  have ok1 := gdHeadBlock_ok (M := M) (f := reg n) (base := B) (len := p256DecompressCode.length)
    (by rw [hX]; exact aligned_add hxp (by omega)) (by rw [rsp]; exact hacc)
  obtain ⟨n1, c1, u1⟩ := St.block gdHeadBlock s hc gdHeadBlock_end ok1
  obtain ⟨hm1, h6, h7, h9, h28, h29, h30, h10, h12, hfr1⟩ := gdHeadBlock_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [hm1] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock gdHeadBlock (M, reg n)).2 q := u1.regs
  rw [hX] at h6 h7 h9 h28
  rw [rsp, r16, r22, dqHead_eq] at h7 h9 h28
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
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc 0x39C gd_at_398 (by decide) hb
  have g2 : ∀ q, reg n2 q = (runBlock gdHeadBlock (M, reg n)).2 q := fun q => by rw [u2.regs, g1]
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
    gd_inner (M0 := M) (U := u) (X := memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) hnp hxp hacc hw hAX hAN hAC
      6 0 (by decide) u2.self hc (fun _ _ => rfl) (fun _ _ _ => rfl) inv0 bd
      (by rw [g2, h30, r21]) (by rw [g2, h12, r19]) (by rw [g2, h10, r25]) (by rw [g2, h7]) (by rw [g2, h6])
      (by rw [g2, h9]) (by rw [g2, h28]) (by rw [g2, h29])
  have k3 : ∀ q, gdPassKeep q = true → reg n3 q = reg n q := fun q hq => by
    rw [fr3 q (gdPassKeep_body q hq), g2, hfr1 q (gdPassKeep_head q hq)]
  have hb3 : ∀ q, gdHeadKeep q = true → dqBodyKeep q = true → reg n3 q = reg n q := fun q h1 h2 => by
    rw [fr3 q h2, g2, hfr1 q h1]
  have s25 : reg n3 sp + 0x698 = acc + BitVec.ofNat 32 (4 * 7) := by rw [k3 sp rfl, ← rsp, BitVec.add_assoc]; rfl
  have ok3 := gdTailBlock_ok (M := M1) (f := reg n3) (base := B) (len := p256DecompressCode.length)
    (by rw [s25]; exact aligned_add hacc (by omega)) (by rw [s25]; exact hAC.sub (by omega))
  obtain ⟨n4, c4, u4⟩ := St.block gdTailBlock u3 hc3 gdTailBlock_end ok3
  obtain ⟨hm4, t27, t5, t17, tfr⟩ := gdTailBlock_run (M := M1) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [hm4, s25] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock gdTailBlock (M1, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := aluEval .add (reg n3 (20 : Fin 32)) (reg n3 (9 : Fin 32))) hc3
    (hAC.sub (c := 4 * 7) (by omega))
  have e5 : reg n4 (5 : Fin 32) = BitVec.ofNat 32 (i + 1) := by
    rw [g4, t5, hb3 (5 : Fin 32) rfl rfl, r5, ofNat_succ]
  have e17 : reg n4 (17 : Fin 32) = 0 := by rw [g4, t17]
  have k4 : ∀ q, gdPassKeep q = true → reg n4 q = reg n q := fun q hq => by
    rw [g4, tfr q (gdPassKeep_tail q hq), k3 q hq]
  have hb4 : branchTaken .bne (reg n4 (5 : Fin 32)) (reg n4 (27 : Fin 32)) = decide (i + 1 < 8) := by
    rw [e5, k4 _ rfl, r27]; exact pass_ne8 i hi
  have arith : 2 ^ 32 * (accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 7))
        (aluEval .add (reg n3 (20 : Fin 32)) (reg n3 (9 : Fin 32)))) acc 8 + (reg n4 (20 : Fin 32)).toNat * 2 ^ (32 * 8)) =
      accV M acc 8 + (reg n (20 : Fin 32)).toNat * 2 ^ (32 * 8) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 xp 8 + u.toNat * accV M0 np 8 := by
    have hA : accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 7)) (aluEval .add (reg n3 (20 : Fin 32)) (reg n3 (9 : Fin 32))))
        acc 8 = accV M1 acc 7 + (aluEval .add (reg n3 (20 : Fin 32)) (reg n3 (9 : Fin 32))).toNat * 2 ^ (32 * 7) := by
      rw [show (8 : Nat) = 7 + 1 from rfl, accV_succ1, accV_store_above (by omega) 7 (Nat.le_refl 7),
        memLoad32_store32_same]
    have ac := add_carry (reg n3 (20 : Fin 32)) (reg n3 (9 : Fin 32))
    have hch : (reg n3 (28 : Fin 32)).toNat ≤ 1 := by omega
    have hcy : (aluEval .sltu (aluEval .add (reg n3 (20 : Fin 32)) (reg n3 (9 : Fin 32))) (reg n3 (9 : Fin 32))).toNat ≤ 1 := by
      have := (reg n3 (20 : Fin 32)).isLt; have := (reg n3 (9 : Fin 32)).isLt; omega
    have h27 : (reg n4 (20 : Fin 32)).toNat = (reg n3 (28 : Fin 32)).toNat +
        (aluEval .sltu (aluEval .add (reg n3 (20 : Fin 32)) (reg n3 (9 : Fin 32))) (reg n3 (9 : Fin 32))).toNat := by
      rw [g4, t27, hb3 (17 : Fin 32) rfl rfl, r17, show aluEval .add (reg n3 (28 : Fin 32)) 0 = reg n3 (28 : Fin 32) from
        BitVec.add_zero _, add_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    have p12 : (2 : Nat) ^ (32 * 8) = 2 ^ (32 * 7) * 2 ^ 32 := pow32_succ 7
    rw [eX, accV_frame32 (b := xp) (n := 8) hfr hAX, accV_frame32 (b := np) (n := 8) hfr hAN, p12] at I1
    rw [hA, h27, p12, hb3 (20 : Fin 32) rfl rfl]
    rw [hb3 (20 : Fin 32) rfl rfl] at ac
    exact mm_tail_arith I1 ac
  have fr4 : ∀ a, Sep acc 32 a 1 → memStore32 M1 (acc + BitVec.ofNat 32 (4 * 7))
      (aluEval .add (reg n3 (20 : Fin 32)) (reg n3 (9 : Fin 32))) a = M0 a := fun a ha => by
    rw [memStore32_ne fun j hj e => (ha.point (i := 4 * 7 + j) (j := 0) (by omega) (by decide)) (by
      rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm), I3 a ha, hfr a ha]
  by_cases hl : i + 1 < 8
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x358 gd_at_400 (by decide) (by rw [hb4]; exact decide_eq_true hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e5], by rw [g5, e17], fun q hq => by rw [g5, k4 q hq]⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x404 gd_at_400 (by decide) (by rw [hb4]; exact decide_eq_false hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e5], by rw [g5, e17], fun q hq => by rw [g5, k4 q hq]⟩

set_option exponentiation.threshold 400 in
/-- **The outer loop**, from pass `i` to its end at 0x404. The accumulator
and its top carry hold a sum `T` with `2^(32 i) T = X_i X + U N`, for `X_i`
the operand's low `i` limbs and some `U`, and `T < 2N`. -/
theorem gd_outer {B acc xp np : Word} {M0 : Word → BitVec 8}
    (hxp : xp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAX : Sep acc 32 xp 32) (hAN : Sep acc 32 np 32)
    (hAC : Sep acc 32 B p256DecompressCode.length) (hN0 : memLoad32 M0 np = 0xFFFFFFFF)
    (hYN : accV M0 xp 8 < accV M0 np 8) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x358 (reg n) → CodeIn M B p256DecompressCode → (∀ a, Sep acc 32 a 1 → M a = M0 a) →
      (∃ U, 2 ^ (32 * i) * (accV M acc 8 + (reg n (20 : Fin 32)).toNat * 2 ^ (32 * 8)) =
        accV M0 xp i * accV M0 xp 8 + U * accV M0 np 8) →
      accV M acc 8 + (reg n (20 : Fin 32)).toNat * 2 ^ (32 * 8) < 2 * accV M0 np 8 →
      reg n (5 : Fin 32) = BitVec.ofNat 32 i → reg n (18 : Fin 32) = xp →
      reg n a6 = memLoad32 M0 xp → reg n (22 : Fin 32) = 0xFFFFFFFF → reg n sp + 0x67C = acc →
      reg n (21 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (25 : Fin 32) = acc + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (19 : Fin 32) = xp + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (17 : Fin 32) = 0 → reg n (27 : Fin 32) = 8 →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x404 (reg n') ∧ CodeIn M' B p256DecompressCode ∧
        (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
        (∃ U, 2 ^ (32 * 8) * (accV M' acc 8 + (reg n' (20 : Fin 32)).toNat * 2 ^ (32 * 8)) =
          accV M0 xp 8 * accV M0 xp 8 + U * accV M0 np 8) ∧
        accV M' acc 8 + (reg n' (20 : Fin 32)).toNat * 2 ^ (32 * 8) < 2 * accV M0 np 8 ∧
        ∀ q, gdPassKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hinv hbd r5 r18 r16 r22 rsp r21 r25 r19 r17 r27
    have i11 : i = 7 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e5, e17, k1⟩ := gd_pass (i := 7) (by decide) hxp hnp hacc
      hw hAX hAN hAC hN0 s hc hfr r5 r18 r16 r22 rsp r21 r25 r19 r17 r27
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * 7))).isLt hu hYN
    refine ⟨n1, M1, c1, u1, hc1, hf1, ⟨U + 2 ^ (32 * 7) * u, ?_⟩, a2, k1⟩
    rw [pow32_succ 7] at a1 ⊢
    rw [a1, accV_succ1 M0 xp 7]
  | succ m ih =>
    intro i hi M n s hc hfr hinv hbd r5 r18 r16 r22 rsp r21 r25 r19 r17 r27
    have hl : i + 1 < 8 := idx_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e5, e17, k1⟩ := gd_pass (i := i)
      (Nat.lt_trans (Nat.lt_succ_self i) hl) hxp hnp hacc hw hAX hAN hAC hN0 s hc hfr r5 r18 r16 r22 rsp r21 r25
      r19 r17 r27
    rw [ite_eq_left hl] at u1
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).isLt hu hYN
    have inv1 : ∃ U, 2 ^ (32 * (i + 1)) * (accV M1 acc 8 + (reg n1 (20 : Fin 32)).toNat * 2 ^ (32 * 8)) =
        accV M0 xp (i + 1) * accV M0 xp 8 + U * accV M0 np 8 :=
      ⟨U + 2 ^ (32 * i) * u, by rw [pow32_succ i, a1, accV_succ1 M0 xp i]⟩
    obtain ⟨n', M', c', u', hc', hf', hv', hb', k'⟩ := ih (i + 1) (idx_succ hi) u1 hc1 hf1 inv1 a2 e5
      (by rw [k1 _ rfl, r18]) (by rw [k1 _ rfl, r16]) (by rw [k1 _ rfl, r22]) (by rw [k1 _ rfl, rsp])
      (by rw [k1 _ rfl, r21]) (by rw [k1 _ rfl, r25]) (by rw [k1 _ rfl, r19]) e17 (by rw [k1 _ rfl, r27])
    exact ⟨n', M', c1.trans c', u', hc', hf', hv', hb', fun q hq => by rw [k' q hq, k1 q hq]⟩

/-! ## The final subtraction -/

/-- The end of a subtraction round, from 0x438: keep the borrow, store the
difference, and advance the pointers and the count. -/
def gdSubTail : List BInstr :=
  [.alu .add (26 : Fin 32) x0 a1, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, .sw (24 : Fin 32) a0 0x0,
   .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x4,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]

theorem gdSubTail_end : blockEnd p256DecompressCode 0x438 gdSubTail = some 0x446 := by decide

set_option maxRecDepth 20000 in
theorem gdSubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock gdSubTail (M, f)).1 = memStore32 M (f (24 : Fin 32) + 0) (f a0) ∧
    (runBlock gdSubTail (M, f)).2 (26 : Fin 32) = f a1 ∧
    (runBlock gdSubTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 4 ∧
    (runBlock gdSubTail (M, f)).2 (23 : Fin 32) = f (23 : Fin 32) + 4 ∧
    (runBlock gdSubTail (M, f)).2 (24 : Fin 32) = f (24 : Fin 32) + 4 ∧
    (runBlock gdSubTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (26 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) →
      (runBlock gdSubTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, gdSubTail]
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

theorem gdSubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (24 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (24 : Fin 32) + 0) 4 base len) :
    BlockOk base len gdSubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, gdSubTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One round of the final subtraction**, from 0x428: subtract limb `i` of
the modulus and the borrow from limb `i` of the accumulator, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem gd_sub_iter {M : Word → BitVec 8} {F acc np D b : Word} {n : Machine} {i : Nat}
    (s : St M GD n 0x428 (reg n)) (hc : CodeIn M GD p256DecompressCode) (hb : CodeIn M BSUB borrowingSubCode)
    (hi : i < 8) (hF : F.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 BSUB borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 GD p256DecompressCode.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 GD p256DecompressCode.length)
    (rsp : reg n sp = F) (r8 : reg n (8 : Fin 32) = acc + BitVec.ofNat 32 (4 * i))
    (r23 : reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i)) (r24 : reg n (24 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (r9 : reg n (9 : Fin 32) = BitVec.ofNat 32 (8 - i)) (r26 : reg n (26 : Fin 32) = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b))
        GD n' (if i + 1 < 8 then 0x428 else 0x448) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' (26 : Fin 32) = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
        (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (8 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (24 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) →
        q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (26 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc gd_at_428 (off' := 0x42A) (by decide)
    (by rw [r8, add_lit_zero]; exact aligned_add hacc (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc gd_at_42a (off' := 0x42E) (by decide)
    (by rw [upd_ne (by decide) (by decide), r23, add_lit_zero]; exact aligned_add hnp (by omega))
  obtain ⟨n3, d3, u3⟩ := u2.self.alu hc gd_at_42e (off' := 0x430) (by decide)
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
  have u3' := u3.self
  have g3a0 : reg n3 a0 = memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by
    rw [u3.regs, updz u2.self.zero (by decide), e0]
  have g3a1 : reg n3 a1 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by
    rw [u3.regs, updz u2.self.zero (by decide), e1]
  have g3a2 : reg n3 a2 = b := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]; rw [u2.self.zero, k2 26 (by decide) (by decide), r26]
    exact BitVec.zero_add _
  have k3' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n3 q = reg n q := fun q q0 q1 q2 => by
    rw [u3.regs, updz u2.self.zero q2, k2 q q0 q1]
  obtain ⟨n4, c4, u4, a04, a14, sp4, fr4, mem4⟩ := u3'.bsubCall hc hb (by decide)
    gd_at_430 gd_at_434 (by decide) (by decide)
    (by rw [k3' sp (by decide) (by decide) (by decide), rsp]) hF sFB
  rw [g3a0, g3a1, g3a2] at a04 a14
  have hc4 : CodeIn n4.mem GD p256DecompressCode := fun j hj => by
    rw [mem4 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n4 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr4 q q0 q1 q2 q3 q4 qr, k3' q q0 q1 q2]
  have e24 : reg n4 (24 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r24, add_lit_zero]
  obtain ⟨n5, c5, u5⟩ := St.block gdSubTail u4 hc4 gdSubTail_end
    (gdSubTail_ok (by rw [e24]; exact aligned_add hD (by omega)) (by rw [e24]; exact sDC))
  obtain ⟨em5, t26, t8, t23, t24, t9, tk⟩ := gdSubTail_run (M := n4.mem) (f := reg n4) u4.zero
  have u5' := u5.self
  rw [em5, e24, a04] at u5'
  have g5 : ∀ q, reg n5 q = (runBlock gdSubTail (n4.mem, reg n4)).2 q := u5.regs
  have hc5 := CodeIn.store32 (v := bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) hc4 sDC
  have e9 : reg n5 (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) := by
    rw [g5, t9, k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9, cnt8_dec i hi]
  have hb5 : branchTaken .bne (reg n5 (9 : Fin 32)) (reg n5 x0) = decide (i + 1 < 8) := by
    rw [e9, u5'.zero]; exact cnt8_ne i hi
  have post : ∀ n6 : Machine, (∀ q, reg n6 q = reg n5 q) →
      reg n6 (26 : Fin 32) = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
        (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n6 sp = F ∧ reg n6 (8 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n6 (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n6 (24 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n6 (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) →
        q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (26 : Fin 32) → reg n6 q = reg n q := fun n6 h6 => by
    refine ⟨by rw [h6, g5, t26, a14],
      by rw [h6, g5, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp4], ?_, ?_, ?_, by rw [h6, e9],
      fun q q0 q1 q2 q3 q4 qr q8 q23 q24 q9 q26 => ?_⟩
    · rw [h6, g5, t8, k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, ptr4]
    · rw [h6, g5, t23, k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r23, ptr4]
    · rw [h6, g5, t24, k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r24, ptr4]
    · rw [h6, g5, tk q q26 q8 q23 q24 q9, k4 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 8
  · obtain ⟨n6, d6, u6⟩ := u5'.taken hc5 0x428 gd_at_446 (by decide) (by rw [hb5]; exact decide_eq_true hl)
    exact ⟨n6, n4.mem, .cons d1 (.cons d2 (.cons d3 (c4.trans (c5.trans (.single d6))))), by rw [ite_eq_left hl]; exact u6.self,
      mem4, post n6 u6.regs⟩
  · obtain ⟨n6, d6, u6⟩ := u5'.notTaken hc5 0x448 gd_at_446 (by decide) (by rw [hb5]; exact decide_eq_false hl)
    exact ⟨n6, n4.mem, .cons d1 (.cons d2 (.cons d3 (c4.trans (c5.trans (.single d6))))), by rw [ite_eq_right hl]; exact u6.self,
      mem4, post n6 u6.regs⟩

set_option exponentiation.threshold 400 in
/-- **The final subtraction**, from round `i` to its end at 0x448: the
buffer at `D` gets the accumulator minus the modulus, and `s4` the borrow
out as a mask. -/
theorem gd_sub_loop {F acc np D : Word} {M0 : Word → BitVec 8} (hF : F.toNat % 4 = 0)
    (hacc : acc.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 32 ≤ 2 ^ 32)
    (sFA : Sep (F + 0xFFFFFFFC) 4 acc 32) (sFN : Sep (F + 0xFFFFFFFC) 4 np 32) (sFD : Sep (F + 0xFFFFFFFC) 4 D 32)
    (sDA : Sep D 32 acc 32) (sDN : Sep D 32 np 32)
    (sFB : Sep (F + 0xFFFFFFFC) 4 BSUB borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 GD p256DecompressCode.length)
    (sDB : Sep D 32 BSUB borrowingSubCode.length) (sDC : Sep D 32 GD p256DecompressCode.length) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M GD n 0x428 (reg n) → CodeIn M GD p256DecompressCode → CodeIn M BSUB borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (8 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (24 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n (26 : Fin 32) = b →
      ∃ n' M', Steps n n' ∧ St M' GD n' 0x448 (reg n') ∧ CodeIn M' GD p256DecompressCode ∧
        CodeIn M' BSUB borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' (26 : Fin 32) = 0 ∨ reg n' (26 : Fin 32) = 0xFFFFFFFF) ∧
        accV M0 acc 8 + 2 ^ (32 * 8) * maskBit (reg n' (26 : Fin 32)) = accV M0 np 8 + accV M' D 8 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) →
          q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (26 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M GD n 0x428 (reg n) → CodeIn M GD p256DecompressCode → CodeIn M BSUB borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (8 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (24 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n (26 : Fin 32) = b →
      ∃ n' M', Steps n n' ∧ St M' GD n' (if i + 1 < 8 then 0x428 else 0x448) (reg n') ∧
        CodeIn M' GD p256DecompressCode ∧ CodeIn M' BSUB borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' (26 : Fin 32) = 0 ∨ reg n' (26 : Fin 32) = 0xFFFFFFFF) ∧
        accV M0 acc (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' (26 : Fin 32)) =
          accV M0 np (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (8 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (24 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) →
          q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (26 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r8 r23 r24 r9 r26
    obtain ⟨n1, Mb, c1, u1, hMb, e26, esp, e8, e23, e24, e9, fr⟩ := gd_sub_iter (i := i) s hc hb hi hF hacc hnp hD
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
    exact ⟨n', M', c1.trans c', u', hc', hb', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr q8 q23 q24 q9 q26 => by
      rw [fr' q q0 q1 q2 q3 q4 qr q8 q23 q24 q9 q26, fr q q0 q1 q2 q3 q4 qr q8 q23 q24 q9 q26]⟩

end C3.RV32.Gd
