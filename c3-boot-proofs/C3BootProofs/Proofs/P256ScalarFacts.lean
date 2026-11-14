import C3BootProofs.Proofs.ScalarMontFacts
import C3BootProofs.Proofs.MontMul12Main

/-!
# Facts for P-256's `Scalar::mul`'s generated proof

The instruction facts `P256ScalarBody.lean` needs beyond `ScalarMontFacts.lean`'s:
`borrowing_sub`'s difference and borrow as one equation over words, masking
with a borrow, and what a call to `borrowing_sub` leaves of the frame.
-/

namespace C3.RV32

/-- Where `Scalar::mul` at `B` calls `borrowing_sub`. -/
def psmBsub (B : Word) : Word := B + 0xFFFF01CE

/-- Limb `i` of the 16 that `widening_mul_fixed::<8, 8>` leaves in the frame
at `F + 0x2C`, and zero past them: `barrett_reduce`'s input. -/
def psmIn (M : Word → BitVec 8) (F : Word) (i : Nat) : Nat :=
  if i < 16 then (memLoad32 M (F + BitVec.ofNat 32 (0x2C + 4 * i))).toNat else 0

/-- `borrowing_sub`'s difference `d` and borrow mask `w` for `l - r` with the
borrow mask `b` in, as one equation over words. -/
theorem psm_bsub {l r b d w : Word} (hd : bsubD l r b = d) (hw : bsubB l r d = w) (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    (d.toNat + r.toNat + b.toNat / 4294967295 = l.toNat + 2 ^ 32 * (w.toNat / 4294967295)) ∧
      (w = 0 ∨ w = 0xFFFFFFFF) := by
  obtain ⟨h1, h2⟩ := bsub_val l r b hb
  rw [hd] at h1 h2; rw [hw] at h1 h2
  have mb : ∀ x : Word, x = 0 ∨ x = 0xFFFFFFFF → maskBit x = x.toNat / 4294967295 := by
    intro x hx; rcases hx with rfl | rfl <;> decide
  exact ⟨by rw [← mb b hb, ← mb w h2]; exact h1, h2⟩

theorem psm_mask {w : Word} (h : w = 0 ∨ w = 0xFFFFFFFF) : w.toNat = 0 ∨ w.toNat = 4294967295 := by
  rcases h with rfl | rfl <;> decide

/-- A word masked with a borrow mask. -/
theorem tn_andM {m c v : Word} (h : aluEval .and m c = v) (hm : m = 0 ∨ m = 0xFFFFFFFF) :
    v.toNat = c.toNat * (m.toNat / 4294967295) := by
  rw [← h]; show (m &&& c).toNat = _
  rw [BitVec.and_comm]
  have := c.isLt
  rcases hm with rfl | rfl
  · rw [and_low (k := 0) (by decide) (by decide)]
    show c.toNat % 1 = c.toNat * 0
    omega
  · rw [and_low (k := 32) (by decide) (by decide)]
    show c.toNat % 2 ^ 32 = c.toNat * 1
    omega

theorem tn_andM' {m c v : Word} (h : aluEval .and c m = v) (hm : m = 0 ∨ m = 0xFFFFFFFF) :
    v.toNat = c.toNat * (m.toNat / 4294967295) := by
  apply tn_andM (m := m) (c := c) _ hm
  rw [← h]; show m &&& c = c &&& m; exact BitVec.and_comm m c

/-- Code apart from the word below the frame stays in place across a call
that writes only that word. -/
theorem psm_code {M M' : Word → BitVec 8} {F b : Word} {code : List Nat} (hc : CodeIn M b code)
    (hs : Sep (F + 0xFFFFFFFC) 4 b code.length) (hm : ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → M' x = M x) :
    CodeIn M' b code :=
  fun i hi => by rw [hm _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi

/-- A frame slot stays put across a call that writes only the word below the
frame. -/
theorem psm_slot {M M' : Word → BitVec 8} {F : Word} {o : Nat} (hF : 4 ≤ F.toNat) (hw : F.toNat + o + 4 ≤ 2 ^ 32)
    (hm : ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → M' x = M x) :
    memLoad32 M' (F + BitVec.ofNat 32 o) = memLoad32 M (F + BitVec.ofNat 32 o) := by
  apply memLoad32_congr
  intro q hq
  apply hm
  intro i hi j hj e
  have e1 : (F + 0xFFFFFFFC + BitVec.ofNat 32 i).toNat = F.toNat - 4 + i := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (0xFFFFFFFC : Word).toNat = 0xFFFFFFFC := rfl
    rw [this]; have := F.isLt; omega
  have e2 : (F + BitVec.ofNat 32 o + BitVec.ofNat 32 q + BitVec.ofNat 32 j).toNat = F.toNat + o + q + j := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    have := F.isLt; omega
  have := congrArg BitVec.toNat e
  rw [e1, e2] at this
  omega

/-- A word apart from the word below the frame stays put across a call that
writes only that word. -/
theorem psm_slotS {M M' : Word → BitVec 8} {F a : Word} (hs : Sep a 4 (F + 0xFFFFFFFC) 4)
    (hm : ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → M' x = M x) : memLoad32 M' a = memLoad32 M a :=
  memLoad32_congr fun j hj => hm _ fun i hi l hl e => hs j hj i hi (by
    rw [add_ofNat_assoc] at e; have : l = 0 := by omega
    subst this; rw [Nat.add_zero] at e; exact e.symm)

/-- Code apart from the frame, the word below it, and the result stays in
place while the memory outside those three agrees. -/
theorem psm_code3 {M M0 : Word → BitVec 8} {F O b : Word} {code : List Nat} (hc : CodeIn M0 b code)
    (s1 : Sep F 0xA0 b code.length) (s2 : Sep (F + 0xFFFFFFFC) 4 b code.length) (s3 : Sep O 32 b code.length)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 4 x 1 → Sep O 32 x 1 → M x = M0 x) : CodeIn M b code :=
  fun i hi => by
    rw [fr _ (s1.subR (c := i) (l := 1) (by omega)) (s2.subR (c := i) (l := 1) (by omega))
      (s3.subR (c := i) (l := 1) (by omega))]
    exact hc i hi

theorem and_fe_eq (a : Word) : a &&& 0xFFFFFFFE = BitVec.ofNat 32 (a.toNat / 2 ^ 1 * 2 ^ 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : ∀ j : Fin 32, (0xFFFFFFFE : Word).getLsbD j.val = decide (1 ≤ j.val) := by decide
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hm ⟨i, hi⟩, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  simp only [BitVec.getLsbD, hi, decide_true, Bool.true_and]
  by_cases h : 1 ≤ i
  · rw [decide_eq_true h, Nat.sub_add_cancel h]; exact Bool.and_true _
  · rw [decide_eq_false h]; exact Bool.and_false _

/-- Word `i` of the `n` words at `b` is digit `i` of their value in base 2^32. -/
theorem accV_digit (M : Word → BitVec 8) (b : Word) :
    ∀ n i, i < n → accV M b n / 2 ^ (32 * i) % 2 ^ 32 = (memLoad32 M (b + BitVec.ofNat 32 (4 * i))).toNat
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    have hl := accV_lt M b n
    have hd : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
    show (accV M b n + (memLoad32 M (b + BitVec.ofNat 32 (4 * n))).toNat * 2 ^ (32 * n)) / 2 ^ (32 * i) % 2 ^ 32 = _
    by_cases hi : i = n
    · subst hi
      rw [Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hl, Nat.zero_add, Nat.mod_eq_of_lt (BitVec.isLt _)]
    · have hin : i < n := by omega
      have e : 2 ^ (32 * n) = 2 ^ (32 * i) * (2 ^ 32 * 2 ^ (32 * (n - i - 1))) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      rw [e, ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ (32 * i)), Nat.mul_assoc, Nat.add_mul_div_left _ _ hd,
        ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ 32), Nat.mul_assoc, Nat.add_mul_mod_self_left]
      exact accV_digit M b n i hin

/-- A word's value from an exact identity with quotients. -/
theorem psm_key32 {A R X Y : Nat} (h : A + 2 ^ 32 * X = R + 2 ^ 32 * Y) (hA : A < 2 ^ 32) : A = R % 2 ^ 32 := by
  omega

/-- A word with its low bit cleared. -/
theorem tn_andFE {a v : Word} (h : aluEval .and a 0xFFFFFFFE = v) : v.toNat = a.toNat / 2 * 2 := by
  rw [← h]; show (a &&& 0xFFFFFFFE).toNat = _
  rw [and_fe_eq, BitVec.toNat_ofNat]; have := a.isLt; omega

/-! The products by `0xFFFFFFFF` and `0xFFFFFFFE` with their quotients as
small numbers: `omega` can't always bound `a * 4294967295 / 2 ^ 32` itself,
because it doesn't search the dark shadow. -/

theorem psm_hiFF {a r : Word} (h : r.toNat = a.toNat * 4294967295 / 2 ^ 32) :
    r.toNat = a.toNat * 4294967295 / 2 ^ 32 ∧ r.toNat + (a.toNat + 4294967295) / 4294967296 = a.toNat :=
  ⟨h, by have := a.isLt; omega⟩

theorem psm_hiFE {a r : Word} (h : r.toNat = a.toNat * 4294967294 / 2 ^ 32) :
    r.toNat = a.toNat * 4294967294 / 2 ^ 32 ∧ r.toNat + (2 * a.toNat + 4294967295) / 4294967296 = a.toNat :=
  ⟨h, by have := a.isLt; omega⟩

theorem psm_loFF {a r : Word} (h : r.toNat = a.toNat * 4294967295 % 2 ^ 32) :
    r.toNat = a.toNat * 4294967295 % 2 ^ 32 ∧ r.toNat + a.toNat = 4294967296 * ((a.toNat + 4294967295) / 4294967296) :=
  ⟨h, by have := a.isLt; omega⟩

theorem psm_loFE {a r : Word} (h : r.toNat = a.toNat * 4294967294 % 2 ^ 32) :
    r.toNat = a.toNat * 4294967294 % 2 ^ 32 ∧
      r.toNat + 2 * a.toNat = 4294967296 * ((2 * a.toNat + 4294967295) / 4294967296) :=
  ⟨h, by have := a.isLt; omega⟩

end C3.RV32
