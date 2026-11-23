import C3BootProofs.Models.EcdsaLoop
import C3BootProofs.Proofs.SvEcMl3

/-!
# P-256 points in the check's main loop

`PRep p P a` says the projective triple `P` represents the affine point
`a` modulo `p`. Montgomery form scales all three coordinates by the same
factor, so it doesn't change what a triple represents. `P256AddOk` and
`P256DblOk` state that the compiled complete formulas represent the curve's
addition. Given those, `mlLoop2` is `gLoop` over a `LoopOps` instance, and
the affine `x` comes out of the inversion of `Z`.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Sv C3.RV32.P2 C3.Image

/-- The triple `P` represents `a` modulo `p`: every coordinate is below
`p`, the point at infinity is `(0 : Y : 0)` with `Y ≠ 0`, and `(x, y)` is
`(x Z : y Z : Z)` with `Z ≠ 0`. -/
def PRep (p : Nat) (P : Nat × Nat × Nat) : ECPoint → Prop
  | none => P.1 < p ∧ P.2.1 < p ∧ P.2.2 < p ∧ P.1 = 0 ∧ P.2.1 ≠ 0 ∧ P.2.2 = 0
  | some (x, y) => P.1 < p ∧ P.2.1 < p ∧ P.2.2 < p ∧ x < p ∧ y < p ∧ P.2.2 ≠ 0 ∧
      MEq p P.1 ((x : Int) * P.2.2) ∧ MEq p P.2.1 ((y : Int) * P.2.2)

/-- The compiled addition `ptAdd2` (Renes, Costello, and Batina's complete
formula for `a = -3`, in Montgomery form) represents P-256's addition on
every pair of points on the curve, the point at infinity included. -/
def P256AddOk : Prop :=
  ∀ A B a b, PRep C3.p256.p A a → PRep C3.p256.p B b → EC.OnC C3.p256 a → EC.OnC C3.p256 b →
    PRep C3.p256.p (ptAdd2 A B) (C3.p256.add a b)

/-- The compiled doubling `ptDbl2` represents P-256's doubling on every
point on the curve, the point at infinity included. -/
def P256DblOk : Prop :=
  ∀ A a, PRep C3.p256.p A a → EC.OnC C3.p256 a → PRep C3.p256.p (ptDbl2 A) (C3.p256.add a a)

theorem p256_p : C3.p256.p = RV32.p256 := by unfold RV32.p256; decide

theorem negPt2_rep {A : Pt2} {a : ECPoint} (h : PRep C3.p256.p A a) : PRep C3.p256.p (negPt2 A) (EC.neg C3.p256 a) := by
  obtain ⟨X, Y, Z⟩ := A
  have hp : 0 < C3.p256.p := by decide
  have hsub : ∀ {y : Nat}, y < C3.p256.p → subGen 0 y = (C3.p256.p - y) % C3.p256.p := fun hy => by
    rw [subGen_field (by rw [← p256_p]; exact hp) (by rw [← p256_p]; exact hy), ← p256_p, Nat.zero_add]
  rcases a with _ | ⟨x, y⟩
  · dsimp only [PRep] at h ⊢
    obtain ⟨hX, hY, hZ, eX, eY, eZ⟩ := h
    refine ⟨hX, ?_, hZ, eX, ?_, eZ⟩
    · show subGen 0 Y < C3.p256.p
      rw [hsub hY]; exact Nat.mod_lt _ hp
    · show subGen 0 Y ≠ 0
      rw [hsub hY, Nat.mod_eq_of_lt (by omega)]; omega
  · dsimp only [PRep] at h ⊢
    obtain ⟨hX, hY, hZ, hx, hy, hZ0, eX, eY⟩ := h
    refine ⟨hX, ?_, hZ, hx, Nat.mod_lt _ hp, hZ0, eX, ?_⟩
    · show subGen 0 Y < C3.p256.p
      rw [hsub hY]; exact Nat.mod_lt _ hp
    · show MEq C3.p256.p (subGen 0 Y : Nat) ((((C3.p256.p - y) % C3.p256.p : Nat) : Int) * Z)
      rw [hsub hY]
      refine (natMod _ _).trans (MEq.trans ?_ ((natMod _ _).mul (MEq.refl _)).symm)
      have e1 : (((C3.p256.p - Y : Nat) : Int)) = -(Y : Int) + (C3.p256.p : Int) * 1 := by omega
      have e2 : (((C3.p256.p - y : Nat) : Int)) * Z = -((y : Int) * Z) + (C3.p256.p : Int) * Z := by
        rw [show (((C3.p256.p - y : Nat) : Int)) = (C3.p256.p : Int) - y by omega, Int.sub_mul, Int.sub_eq_add_neg,
          Int.add_comm]
      rw [e1, e2]
      exact (MEq.add_mul_self 1).trans ((eY.neg).trans (MEq.add_mul_self _).symm)

theorem idPt2_val : idPt2 = (0, 2 ^ 256 % C3.p256.p, 0) := by
  unfold idPt2
  decide

theorem idPt2_rep : PRep C3.p256.p idPt2 none := by
  rw [idPt2_val]
  exact ⟨by decide, Nat.mod_lt _ (by decide), by decide, rfl, by decide, rfl⟩

theorem idPt2_uniq (a : ECPoint) (h : PRep C3.p256.p idPt2 a) : a = none := by
  rw [idPt2_val] at h
  rcases a with _ | ⟨x, y⟩
  · rfl
  · exact absurd rfl h.2.2.2.2.2.1

/-- The loop's point operations, given the two formulas' correctness. -/
theorem p256Ops (hadd : P256AddOk) (hdbl : P256DblOk) :
    LoopOps C3.p256 (PRep C3.p256.p) ptAdd2 negPt2 ptDbl2 idPt2 where
  add := hadd
  dbl := hdbl
  neg := fun _ _ h => negPt2_rep h
  id := idPt2_rep
  uniq := idPt2_uniq

theorem mlAdd2_eq (T : Nat → Pt2) (acc : Pt2) (b : Nat) : mlAdd2 T acc b = gAdd ptAdd2 negPt2 T acc b := rfl

theorem mlPair2_eq (T : Nat → Pt2) (D : List Nat) (k : Nat) (st : Pt2 × Bool) :
    mlPair2 T D k st = gPair ptAdd2 negPt2 0x101 T D k st := by
  unfold mlPair2 gPair
  rw [mlAdd2_eq]
  by_cases h : 0x101 < k + 1
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    generalize gAdd ptAdd2 negPt2 T st.1 (D.getD k 0) = o
    rcases o with _ | _ | a <;> rfl

theorem mlIter2_eq (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) (k : Nat) (st : Pt2 × Bool) :
    mlIter2 T0 T1 D0 D1 k st = gIter ptAdd2 negPt2 ptDbl2 0x101 T0 T1 D0 D1 k st := by
  unfold mlIter2 gIter
  rw [mlPair2_eq]
  congr 1
  funext st'
  exact mlPair2_eq T1 D1 k st'

theorem mlLoop2_eq (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) :
    ∀ k st, mlLoop2 T0 T1 D0 D1 k st = gLoop ptAdd2 negPt2 ptDbl2 0x101 T0 T1 D0 D1 k st
  | 0, _ => rfl
  | k + 1, st => by
    rw [mlLoop2, gLoop, mlIter2_eq]
    congr 1
    funext st'
    exact mlLoop2_eq T0 T1 D0 D1 k st'

/-- An affine point in Montgomery form, with `Z` the Montgomery 1. -/
theorem mont_rep {x y : Nat} (hx : x < C3.p256.p) (hy : y < C3.p256.p) :
    PRep C3.p256.p (x * 2 ^ 256 % C3.p256.p, y * 2 ^ 256 % C3.p256.p, 2 ^ 256 % C3.p256.p) (some (x, y)) := by
  have hp : 0 < C3.p256.p := by decide
  refine ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp, hx, hy, (show 2 ^ 256 % C3.p256.p ≠ 0 by decide), ?_, ?_⟩ <;>
  · show MEq _ ((_ % C3.p256.p : Nat) : Int) (_ * ((2 ^ 256 % C3.p256.p : Nat) : Int))
    refine (natMod _ _).trans (MEq.trans ?_ ((MEq.refl _).mul (natMod _ _)).symm)
    rw [Int.natCast_mul]
    exact MEq.refl _

theorem p2fm_eq (a b : Nat) : p2fm a b = a * b * p2RInv % C3.p256.p := by rw [p256_p]; rfl

set_option exponentiation.threshold 600 in
set_option maxRecDepth 10000 in
/-- **The affine `x`**: with `zinv Z ≡ R²`, the Montgomery product of `X`
and `zinv`, taken out of Montgomery form, is `x`. -/
theorem p2fm_affine_x {X Y Z x y zinv : Nat} (h : PRep C3.p256.p (X, Y, Z) (some (x, y)))
    (hz : MEq C3.p256.p ((zinv : Int) * Z) ((2 ^ 512 % C3.p256.p : Nat) : Int)) :
    p2fm (p2fm X zinv) 1 = x := by
  obtain ⟨-, -, -, hx, -, -, eX, -⟩ := h
  have hp : 0 < C3.p256.p := by decide
  have hRI : MEq C3.p256.p ((2 ^ 256 : Nat) * (p2RInv : Int)) 1 := by
    rw [← Int.natCast_mul]; exact MEq.natCast.mpr (by rw [p256_p]; unfold RV32.p256 p2RInv; decide)
  rw [p2fm_eq, p2fm_eq, Nat.mul_one]
  apply EC.eq_of_meq (Nat.mod_lt _ hp) hx
  refine (natMod _ _).trans ?_
  rw [Int.natCast_mul]
  refine ((natMod _ _).mul (MEq.refl _)).trans ?_
  rw [Int.natCast_mul, Int.natCast_mul]
  have e1 : MEq C3.p256.p ((X : Int) * zinv) ((x : Int) * ((2 ^ 256 : Nat) * (2 ^ 256 : Nat))) := by
    refine (eX.mul (MEq.refl _)).trans ?_
    rw [Int.mul_assoc, Int.mul_comm (Z : Int)]
    refine (MEq.refl _).mul (hz.trans ((natMod _ _).trans ?_))
    rw [← Int.natCast_mul]; exact MEq.refl _
  refine ((e1.mul (MEq.refl _)).mul (MEq.refl _)).trans ?_
  have e2 : (x : Int) * ((2 ^ 256 : Nat) * (2 ^ 256 : Nat)) * p2RInv * p2RInv =
      x * (((2 ^ 256 : Nat) * (p2RInv : Int)) * ((2 ^ 256 : Nat) * (p2RInv : Int))) := by
    rw [Int.mul_assoc, Int.mul_assoc]
    congr 1
  rw [e2]
  refine ((MEq.refl _).mul (hRI.mul hRI)).trans ?_
  rw [Int.mul_one, Int.mul_one]
  exact MEq.refl _

end C3.Models
