import C3BootProofs.Models.Ed25519DecBytes
import C3BootProofs.Models.Ed25519Formulas
import C3BootProofs.Models.Ed25519RecoverX
import C3BootProofs.Models.Ed25519Limbs
import C3BootProofs.Proofs.EdNafTable

/-!
# `decompress`, from the primality of `p`

`decOK` proves `DecOK`. The proof reads no exponent: whatever root
candidate `sqrt_ratio_i` computes, it reports success only when the root
it returns, squared and times `v`, is `u` (`srTail_ok`). The three `ct_eq`
checks compare canonical encodings, which `to_bytes` writes as the value
modulo `p` (`feToBytes_val`). With `v x² = u` for `u = y² - 1` and
`v = d y² + 1`, `(x, y)` is on the curve, and the sign step picks the root
that `recoverX` picks.
-/

namespace C3.RV32.EdM

open C3.Models

local notation "𝔭" => ((Ed25519.p : Nat) : Int)
local notation "𝔡" => ((Ed25519.d : Nat) : Int)

theorem mulL_redB (a b : List Nat) : RedB (mulL a b) := feReduce_redB ..

theorem sqL_redB (l : List Nat) : RedB (sqL l) := feReduce_redB ..

theorem negL_redB (l : List Nat) : RedB (negL l) := feReduce_redB ..

/-- The canonical bytes of limbs below 2^62 spell their value. -/
theorem bytesL_fv {l : List Nat} (h : Lim (2 ^ 62) l) : leB32 (bytesL l) = fv l := by
  have e1 := feToBytes_reduce _ (feReduce_redB (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) (l.getD 4 0)
    (l.getD 5 0) (l.getD 6 0) (l.getD 7 0) (l.getD 8 0) (l.getD 9 0))
  have e2 := (feReduce_val (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) (l.getD 4 0) (l.getD 5 0)
    (l.getD 6 0) (l.getD 7 0) (l.getD 8 0) (l.getD 9 0) (h.2 0 (by decide)) (h.2 1 (by decide))
    (h.2 2 (by decide)) (h.2 3 (by decide)) (h.2 4 (by decide)) (h.2 5 (by decide)) (h.2 6 (by decide))
    (h.2 7 (by decide)) (h.2 8 (by decide)) (h.2 9 (by decide))).2
  exact e1.trans e2

/-- `ct_eq` reports equal values. -/
theorem feEqL_fv {a b : List Nat} (ha : Lim (2 ^ 62) a) (hb : Lim (2 ^ 62) b) (h : feEqL a b = true) :
    fv a = fv b := by
  unfold feEqL at h
  rw [← bytesL_fv ha, ← bytesL_fv hb, of_decide_eq_true h]

/-- `is_negative` is the low bit of the value. -/
theorem isNegL_eq {l : List Nat} (h : Lim (2 ^ 62) l) : isNegL l = (fv l % 2 == 1) := by
  have e := bytesL_fv h
  unfold leB32 at e
  unfold isNegL
  rw [show (bytesL l).getD 0 0 % 2 = fv l % 2 by omega]

theorem condNegL_true (l : List Nat) : condNegL l true = negL l := by
  unfold condNegL negL
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  exact wl_red ..

theorem condNegL_false (l : List Nat) : condNegL l false = l := rfl

theorem neg_meq {R : Nat} (hR : R < Ed25519.p) :
    MEq Ed25519.p (((Ed25519.p - R) % Ed25519.p : Nat) : Int) (-(R : Int)) := by
  refine (natMod _ _).trans ?_
  rw [Int.natCast_sub (Nat.le_of_lt hR)]
  exact sm (by ring_mod [p_sub * 1])

/-- `conditional_negate(is_negative)` keeps the square and leaves an even
value. -/
theorem finish_ok {l : List Nat} {V U : Int} (h : Lim (2 ^ 26) l) (hm : MEq Ed25519.p (V * fv l * fv l) U) :
    Lim (2 ^ 26) (condNegL l (isNegL l)) ∧ fv (condNegL l (isNegL l)) % 2 = 0 ∧
      MEq Ed25519.p (V * fv (condNegL l (isNegL l)) * fv (condNegL l (isNegL l))) U := by
  rw [isNegL_eq (h.mono (by decide))]
  have hl := fv_lt l
  by_cases hodd : fv l % 2 = 1
  · rw [show (fv l % 2 == 1) = true from beq_iff_eq.mpr hodd, condNegL_true]
    have hn := feNeg_ok l h
    refine ⟨hn.1, ?_, ?_⟩
    · have hpo : Ed25519.p % 2 = 1 := by decide
      rw [hn.2, Nat.mod_eq_of_lt (show Ed25519.p - fv l < Ed25519.p by omega)]
      omega
    · have m := neg_meq hl
      rw [← hn.2] at m
      exact sm (by ring_mod [(ms m) * (V * ((fv (negL l) : Int) - fv l)), (ms hm) * 1])
  · rw [show (fv l % 2 == 1) = false from beq_eq_false_iff_ne.mpr hodd, condNegL_false]
    exact ⟨h, by omega, hm⟩

/-- `sqrt_ratio_i` after its root candidate `r`. -/
def srTail (sq u v r : List Nat) : Bool × List Nat :=
  let check := mulL v (sqL r)
  let cs := feEqL check u
  let fs := feEqL check (negL u)
  let fsi := feEqL check (mulL (negL u) sq)
  let r := if fs || fsi then mulL sq r else r
  (cs || fs, condNegL r (isNegL r))

theorem decSqrtRatio_tail (sq u v : List Nat) : ∃ r, RedB r ∧ decSqrtRatio sq u v = srTail sq u v r :=
  ⟨_, mulL_redB _ _, rfl⟩

set_option linter.unusedSimpArgs false in
/-- **`sqrt_ratio_i` is sound**: when it reports a square, its root `r`
is even and `v r² = u`. -/
theorem srTail_ok (hp : IsPrime Ed25519.p) {sq u v r : List Nat} (hs : Lim (2 ^ 26) sq)
    (hsv : fv sq = Ed25519.sqrtM1) (hu : Lim (2 ^ 26) u) (hv : Lim (2 ^ 27) v) (hr : Lim (2 ^ 26) r)
    (h : (srTail sq u v r).1 = true) :
    Lim (2 ^ 26) (srTail sq u v r).2 ∧ fv (srTail sq u v r).2 % 2 = 0 ∧
      MEq Ed25519.p ((fv v : Int) * fv (srTail sq u v r).2 * fv (srTail sq u v r).2) (fv u) := by
  have hsq := sqL_ok (hr.mono (by decide))
  have hc := mulL_ok (hv.mono (by decide)) (hsq.1.mono (by decide))
  have hn := feNeg_ok u hu
  have hni := mulL_ok (hn.1.mono (by decide)) (hs.mono (by decide))
  have hri := mulL_ok (hs.mono (by decide)) (hr.mono (by decide))
  have hi := sqrtM1_int
  rw [← hsv] at hi
  have m1 := mq_mul hc.2
  have m2 := mq_mul hsq.2
  have mC : MEq Ed25519.p (fv (mulL v (sqL r))) ((fv v : Int) * fv r * fv r) :=
    sm (by ring_mod [(ms m1) * 1, (ms m2) * (fv v : Int)])
  have mN := neg_meq (fv_lt u)
  rw [← hn.2] at mN
  have m3 := mq_mul hni.2
  have mNI : MEq Ed25519.p (fv (mulL (negL u) sq)) (-(fv u : Int) * fv sq) :=
    sm (by ring_mod [(ms m3) * 1, (ms mN) * (fv sq : Int)])
  have mRI := mq_mul hri.2
  have lC : Lim (2 ^ 62) (mulL v (sqL r)) := hc.1.mono (by decide)
  have lu : Lim (2 ^ 62) u := hu.mono (by decide)
  unfold srTail at h ⊢
  dsimp only at h ⊢
  generalize hcs : feEqL (mulL v (sqL r)) u = cs at h
  generalize hfs : feEqL (mulL v (sqL r)) (negL u) = fs at h ⊢
  generalize hfsi : feEqL (mulL v (sqL r)) (mulL (negL u) sq) = fsi
  refine finish_ok ?_ ?_
  · cases fs <;> cases fsi
    · simp only [Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]; exact hr
    all_goals (simp only [Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]; exact hri.1)
  · cases fs
    · cases cs
      · cases h
      have eu := feEqL_fv lC lu hcs
      rw [eu] at mC
      cases fsi
      · simp only [Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        exact mC.symm
      · simp only [Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        have eni := feEqL_fv lC (hni.1.mono (by decide)) hfsi
        rw [eu] at eni
        rw [← eni] at mNI
        have hU : MEq Ed25519.p ((fv u : Int) * (1 + fv sq)) 0 := sm (by ring_mod [(ms mNI) * 1])
        rcases hp.meq_mul_zero hU with hU0 | hI
        · exact sm (by ring_mod [(ms mRI) * ((fv v : Int) * ((fv (mulL sq r) : Int) + (fv sq : Int) * fv r)),
            hi * ((fv v : Int) * fv r * fv r), (ms mC) * 1, (ms hU0) * (-2)])
        · exact absurd (sm (by ring_mod [hi * 1, (ms hI) * (1 - (fv sq : Int))]) : MEq Ed25519.p 2 0) two_ne
    · simp only [Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      have en := feEqL_fv lC (hn.1.mono (by decide)) hfs
      rw [en] at mC
      exact sm (by ring_mod [(ms mRI) * ((fv v : Int) * ((fv (mulL sq r) : Int) + (fv sq : Int) * fv r)),
        hi * ((fv v : Int) * fv r * fv r), (ms mC) * 1, (ms mN) * (-1)])

set_option maxHeartbeats 4000000 in
theorem decLoad_bnd (b : List Nat) (hB : Byt b) : Lim (2 ^ 32) (decLoad b) := by
  have b0 := hB 0; have b1 := hB 1; have b2 := hB 2; have b3 := hB 3; have b4 := hB 4; have b5 := hB 5
  have b6 := hB 6; have b7 := hB 7; have b8 := hB 8; have b9 := hB 9; have b10 := hB 10; have b11 := hB 11
  have b12 := hB 12; have b13 := hB 13; have b14 := hB 14; have b15 := hB 15; have b16 := hB 16
  have b17 := hB 17; have b18 := hB 18; have b19 := hB 19; have b20 := hB 20; have b21 := hB 21
  have b22 := hB 22; have b23 := hB 23; have b24 := hB 24; have b25 := hB 25; have b26 := hB 26
  have b27 := hB 27; have b28 := hB 28; have b29 := hB 29; have b30 := hB 30; have b31 := hB 31
  refine ⟨rfl, fun i hi => ?_⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [decLoad, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceAdd] <;> omega

set_option maxHeartbeats 4000000 in
/-- `from_bytes`'s limbs spell the low 255 bits. -/
theorem decLoad_val (b : List Nat) (hB : Byt b) :
    (decLoad b).getD 0 0 + 2 ^ 26 * (decLoad b).getD 1 0 + 2 ^ 51 * (decLoad b).getD 2 0 +
      2 ^ 77 * (decLoad b).getD 3 0 + 2 ^ 102 * (decLoad b).getD 4 0 + 2 ^ 128 * (decLoad b).getD 5 0 +
      2 ^ 153 * (decLoad b).getD 6 0 + 2 ^ 179 * (decLoad b).getD 7 0 + 2 ^ 204 * (decLoad b).getD 8 0 +
      2 ^ 230 * (decLoad b).getD 9 0 = leB32 b % 2 ^ 255 := by
  have b0 := hB 0; have b1 := hB 1; have b2 := hB 2; have b3 := hB 3; have b4 := hB 4; have b5 := hB 5
  have b6 := hB 6; have b7 := hB 7; have b8 := hB 8; have b9 := hB 9; have b10 := hB 10; have b11 := hB 11
  have b12 := hB 12; have b13 := hB 13; have b14 := hB 14; have b15 := hB 15; have b16 := hB 16
  have b17 := hB 17; have b18 := hB 18; have b19 := hB 19; have b20 := hB 20; have b21 := hB 21
  have b22 := hB 22; have b23 := hB 23; have b24 := hB 24; have b25 := hB 25; have b26 := hB 26
  have b27 := hB 27; have b28 := hB 28; have b29 := hB 29; have b30 := hB 30; have b31 := hB 31
  simp only [decLoad, leB32, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceAdd]
  omega

theorem leNum_leB32 {b : List Nat} (hb : b.length = 32) : Ed25519.leNum b = leB32 b := by
  rw [leNum_lv, hb]
  simp only [lv, leB32]
  omega

/-- `y`: `reduce` of `from_bytes`'s limbs is the low 255 bits. -/
theorem decY (b : List Nat) (hlen : b.length = 32) (hB : Byt b) (hlt : Ed25519.leNum b % 2 ^ 255 < Ed25519.p) :
    Lim (2 ^ 26) (redL (decLoad b)) ∧ fv (redL (decLoad b)) = Ed25519.leNum b % 2 ^ 255 := by
  have hL := decLoad_bnd b hB
  have l62 : ∀ i, i < 10 → (decLoad b).getD i 0 < 2 ^ 62 := fun i hi => Nat.lt_trans (hL.2 i hi) (by decide)
  obtain ⟨h1, h2⟩ := feReduce_val _ _ _ _ _ _ _ _ _ _ (l62 0 (by decide)) (l62 1 (by decide)) (l62 2 (by decide))
    (l62 3 (by decide)) (l62 4 (by decide)) (l62 5 (by decide)) (l62 6 (by decide)) (l62 7 (by decide))
    (l62 8 (by decide)) (l62 9 (by decide))
  refine ⟨h1, ?_⟩
  unfold redL
  rw [h2, decLoad_val b hB, ← leNum_leB32 hlen, Nat.mod_eq_of_lt hlt]

/-- **`decompress` is sound**, given that `p` is prime. -/
theorem decOK (hp : IsPrime Ed25519.p) : DecOK := by
  intro one dl sq b E h1 hone hd hdv hs hsv hlen hB hlt hdec
  obtain ⟨hY, hYv⟩ := decY b hlen hB hlt
  rw [(leNum_clearTop b hlen hB).2]
  have hc : b.getD 31 0 / 128 = 0 ∨ b.getD 31 0 / 128 = 1 := by have := hB 31; omega
  unfold decSpec at hdec
  dsimp only at hdec
  generalize b.getD 31 0 / 128 = c at hc hdec ⊢
  generalize Ed25519.leNum b % 2 ^ 255 = y at hYv hlt ⊢
  generalize redL (decLoad b) = Y at hY hYv hdec
  have hYY := sqL_ok (hY.mono (by decide))
  have hu := subL_ok (hYY.1.mono (by decide)) (h1.mono (by decide))
  have hm := mulL_ok (hYY.1.mono (by decide)) (hd.mono (by decide))
  have hv := addL_ok hm.1 h1 (by decide)
  have mYY : MEq Ed25519.p (fv (sqL Y)) ((y : Int) * y) := by
    have m := mq_mul hYY.2
    rwa [hYv] at m
  have mU : MEq Ed25519.p (fv (subL (sqL Y) one)) ((y : Int) * y - 1) := by
    have m := mq_sub (fv_lt one) hu.2
    rw [hone] at m
    push_cast at m
    exact sm (by ring_mod [(ms m) * 1, (ms mYY) * 1])
  have mM : MEq Ed25519.p (fv (mulL (sqL Y) dl)) ((y : Int) * y * 𝔡) := by
    have m := mq_mul hm.2
    rw [hdv] at m
    exact sm (by ring_mod [(ms m) * 1, (ms mYY) * 𝔡])
  have mV : MEq Ed25519.p (fv (addL (mulL (sqL Y) dl) one)) (𝔡 * y * y + 1) := by
    have m := mq_add hv.2
    rw [hone] at m
    push_cast at m
    exact sm (by ring_mod [(ms m) * 1, (ms mM) * 1])
  obtain ⟨r, hrB, hr⟩ := decSqrtRatio_tail sq (subL (sqL Y) one) (addL (mulL (sqL Y) dl) one)
  have key := srTail_ok hp hs hsv hu.1 (hv.1.mono (by decide)) hrB.lim
  rw [hr] at hdec
  generalize srTail sq (subL (sqL Y) one) (addL (mulL (sqL Y) dl) one) r = s at key hdec
  generalize fv (subL (sqL Y) one) = U at key mU
  generalize fv (addL (mulL (sqL Y) dl) one) = V at key mV
  have hs1 : s.1 = true := by
    by_cases h : s.1 = true
    · exact h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)] at hdec
      cases hdec
  rw [ite_eq_left_of_eq_true _ _ (eq_true hs1)] at hdec
  obtain ⟨hxL, hxE, hxM⟩ := key hs1
  cases hdec
  suffices H : ∀ X : List Nat, Lim (2 ^ 26) X → MEq Ed25519.p ((fv X : Int) * fv X) ((fv s.2 : Int) * fv s.2) →
      (fv X % 2 = c ∨ (fv X = 0 ∧ c = 1)) →
      ∃ x, OnCurve (x, y) ∧ ERep (X, Y, one, mulL X Y) (x, y) ∧
        (Ed25519.recoverX y c = some x ∨ (c = 1 ∧ (y = 1 ∨ y = Ed25519.p - 1))) by
    rcases hc with rfl | rfl
    · exact H s.2 hxL (MEq.refl _) (Or.inl hxE)
    · rw [show condNegL s.2 (1 == 1) = negL s.2 from condNegL_true s.2]
      have hn := feNeg_ok s.2 hxL
      have m := neg_meq (fv_lt s.2)
      rw [← hn.2] at m
      refine H _ hn.1 (sm (by ring_mod [(ms m) * ((fv (negL s.2) : Int) - fv s.2)])) ?_
      by_cases hz : fv s.2 = 0
      · exact Or.inr ⟨by rw [hn.2, hz, Nat.sub_zero, Nat.mod_self], rfl⟩
      · left
        have hpo : Ed25519.p % 2 = 1 := by decide
        have := fv_lt s.2
        rw [hn.2, Nat.mod_eq_of_lt (show Ed25519.p - fv s.2 < Ed25519.p by omega)]
        omega
  intro X hXL hXsq hpar
  have hcurve : CurveI (fv X) y := by
    unfold CurveI
    ring_mod [(ms hXsq) * (-(V : Int)), (ms hxM) * (-1), (ms mV) * ((fv X : Int) * fv X), (ms mU) * (-1)]
  have hon : OnCurve (fv X, y) := onCurve_of (fv_lt X) hlt hcurve
  have hXY := mulL_ok (hXL.mono (by decide)) (hY.mono (by decide))
  refine ⟨fv X, hon, ⟨hXL, hY, h1, hXY.1, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show fv one ≠ 0
    rw [hone]; exact Nat.one_ne_zero
  · show fv X = fv X * fv one % Ed25519.p
    rw [hone, Nat.mul_one, Nat.mod_eq_of_lt (fv_lt X)]
  · show fv Y = y * fv one % Ed25519.p
    rw [hone, Nat.mul_one, hYv, Nat.mod_eq_of_lt hlt]
  · show fv X * fv Y % Ed25519.p = fv one * fv (mulL X Y) % Ed25519.p
    rw [hone, Nat.one_mul, hXY.2, Nat.mod_mod]
  rcases hpar with hpar | ⟨hX0, hc1⟩
  · left
    rw [← hpar]
    exact recoverX_ok hp _ _ hon
  · right
    refine ⟨hc1, ?_⟩
    have h0 : ((fv X : Int) - 0) % 𝔭 = 0 := by rw [hX0]; decide
    have hyy : MEq Ed25519.p ((y : Int) * y) 1 :=
      sm (by ring_mod [hcurve * 1, h0 * ((fv X : Int) * (1 + 𝔡 * y * y))])
    rcases pm_one hp hyy with hy1 | hy1
    · exact Or.inl (nat_of_meq hlt one_lt_p hy1)
    · refine Or.inr (nat_of_meq hlt (Nat.sub_lt p_pos Nat.one_pos) (hy1.trans ?_))
      rw [Int.natCast_sub (Nat.le_of_lt one_lt_p)]
      exact sm (by ring_mod [p_sub * (-1)])

end C3.RV32.EdM
