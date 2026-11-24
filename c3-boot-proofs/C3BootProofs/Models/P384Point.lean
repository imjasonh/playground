import C3BootProofs.Models.EcdsaRep
import C3BootProofs.Proofs.Pv384Main

/-!
# P-384 points in the check's main loop

`P384AddOk` and `P384DblOk` state that the compiled complete formulas
represent the curve's addition. Given those, `mlLoop` is `gLoop` over a
`LoopOps` instance, and the affine `x` comes out of the inversion of `Z`.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Pv C3.RV32.P3 C3.RV32.Dq C3.Image

/-- The compiled addition `ptAddT` (Renes, Costello, and Batina's complete
formula for `a = -3`, in Montgomery form) represents P-384's addition on
every pair of points on the curve, the point at infinity included. -/
def P384AddOk : Prop :=
  ∀ A B a b, PRep C3.p384.p A a → PRep C3.p384.p B b → EC.OnC C3.p384 a → EC.OnC C3.p384 b →
    PRep C3.p384.p (ptAddT A B) (C3.p384.add a b)

/-- The compiled doubling `ptDblT` represents P-384's doubling on every
point on the curve, the point at infinity included. -/
def P384DblOk : Prop :=
  ∀ A a, PRep C3.p384.p A a → EC.OnC C3.p384 a → PRep C3.p384.p (ptDblT A) (C3.p384.add a a)

set_option exponentiation.threshold 800 in
theorem p384_p : C3.p384.p = RV32.p384 := by unfold RV32.p384; decide

set_option exponentiation.threshold 800 in
theorem negPt_rep {A : Pt} {a : ECPoint} (h : PRep C3.p384.p A a) : PRep C3.p384.p (negPt A) (EC.neg C3.p384 a) := by
  obtain ⟨X, Y, Z⟩ := A
  refine neg_rep (by decide) (fun hY => ?_) h
  rw [p384_p] at hY ⊢
  have hp : RV32.p384 < 2 ^ 384 := by unfold RV32.p384; decide
  unfold negY
  by_cases h0 : Y = 0
  · rw [ite_eq_left h0, h0, Nat.sub_zero, Nat.mod_self]
  · rw [ite_eq_right h0, show RV32.p384 + 2 ^ 384 - Y = (RV32.p384 - Y) + 2 ^ 384 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

set_option exponentiation.threshold 800 in
theorem idPt_val : idPt = (0, 2 ^ 384 % C3.p384.p, 0) := by
  unfold idPt
  decide

set_option exponentiation.threshold 800 in
theorem idPt_rep : PRep C3.p384.p idPt none := by
  rw [idPt_val]
  exact ⟨by decide, Nat.mod_lt _ (by decide), by decide, rfl, by decide, rfl⟩

theorem idPt_uniq (a : ECPoint) (h : PRep C3.p384.p idPt a) : a = none := by
  rw [idPt_val] at h
  rcases a with _ | ⟨x, y⟩
  · rfl
  · exact absurd rfl h.2.2.2.2.2.1

/-- The loop's point operations, given the two formulas' correctness. -/
theorem p384Ops (hadd : P384AddOk) (hdbl : P384DblOk) :
    LoopOps C3.p384 (PRep C3.p384.p) ptAddT negPt ptDblT idPt where
  add := hadd
  dbl := hdbl
  neg := fun _ _ h => negPt_rep h
  id := idPt_rep
  uniq := idPt_uniq

theorem mlAdd_eq (T : Nat → Pt) (acc : Pt) (b : Nat) : mlAdd T acc b = gAdd ptAddT negPt T acc b := rfl

theorem mlPair_eq (T : Nat → Pt) (D : List Nat) (k : Nat) (st : Pt × Bool) :
    mlPair T D k st = gPair ptAddT negPt 0x181 T D k st := by
  unfold mlPair gPair
  rw [mlAdd_eq]
  by_cases h : 0x181 < k + 1
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    generalize gAdd ptAddT negPt T st.1 (D.getD k 0) = o
    rcases o with _ | _ | a <;> rfl

theorem mlIter_eq (T0 T1 : Nat → Pt) (D0 D1 : List Nat) (k : Nat) (st : Pt × Bool) :
    mlIter T0 T1 D0 D1 k st = gIter ptAddT negPt ptDblT 0x181 T0 T1 D0 D1 k st := by
  unfold mlIter gIter
  rw [mlPair_eq]
  congr 1
  funext st'
  exact mlPair_eq T1 D1 k st'

theorem mlLoop_eq (T0 T1 : Nat → Pt) (D0 D1 : List Nat) :
    ∀ k st, mlLoop T0 T1 D0 D1 k st = gLoop ptAddT negPt ptDblT 0x181 T0 T1 D0 D1 k st
  | 0, _ => rfl
  | k + 1, st => by
    rw [mlLoop, gLoop, mlIter_eq]
    congr 1
    funext st'
    exact mlLoop_eq T0 T1 D0 D1 k st'

theorem mlRun_eq (T0 T1 : Nat → Pt) (D0 D1 : List Nat) (L : Nat) :
    mlRun T0 T1 D0 D1 L = (gLoop ptAddT negPt ptDblT 0x181 T0 T1 D0 D1 L (idPt, false)).map Prod.fst := by
  unfold mlRun
  by_cases h : L = 0
  · rw [ite_eq_left h, h]; rfl
  · rw [ite_eq_right h, mlLoop_eq]

set_option exponentiation.threshold 800 in
theorem pvG_val : pvG = (C3.p384.gx * 2 ^ 384 % C3.p384.p, C3.p384.gy * 2 ^ 384 % C3.p384.p, 2 ^ 384 % C3.p384.p) := by
  unfold pvG
  decide

set_option exponentiation.threshold 800 in
theorem montOne_val : dataVal p384MontOneData 0 12 = 2 ^ 384 % C3.p384.p := by decide

set_option exponentiation.threshold 800 in
set_option maxRecDepth 10000 in
theorem p3_rinv : 2 ^ 384 * p3RInv % C3.p384.p = 1 := by rw [p384_p]; unfold RV32.p384 p3RInv; decide

set_option exponentiation.threshold 800 in
/-- **The affine `x`**: with `zinv Z ≡ R²`, the Montgomery product of `X`
and `zinv`, taken out of Montgomery form, is `x`. -/
theorem p3fm_affine_x {X Y Z x y zinv : Nat} (h : PRep C3.p384.p (X, Y, Z) (some (x, y)))
    (hz : MEq C3.p384.p ((zinv : Int) * Z) ((2 ^ 768 % C3.p384.p : Nat) : Int)) :
    p3fm (p3fm X zinv) 1 = x := by
  have e2 : (2 : Nat) ^ 384 * 2 ^ 384 = 2 ^ 768 := by rw [← Nat.pow_add]
  have e := mont_affine_x p3_rinv h (by rw [e2]; exact hz)
  unfold p3fm
  rw [← p384_p]
  exact e

end C3.Models
