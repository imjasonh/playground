import C3BootProofs.Models.Ed25519Model
import C3BootProofs.Models.Ed25519Formulas
import C3BootProofs.Models.Ed25519Laws
import C3BootProofs.Models.Ed25519Bytes2

/-!
# `is_small_order` finds every point of small order, from the primality of `p`

`mul 8 P` is three doublings, and `isoStep` is `projC` of `edDoubleSpec`,
so `edDbl_ok` and `edProj_ok` make `isoTimes8` represent `mul 8 P`. When that
is `(0, 1)`, its `X` is `0` and its `Y` is `Z`, so both of `isoSpec`'s byte
comparisons hold.
-/

namespace C3.RV32.EdM

open C3.Models

/-- **`mul 8 P` is three doublings.** -/
theorem mul_eight (hp : IsPrime Ed25519.p) (P : Nat × Nat) (hP : OnCurve P) :
    Ed25519.mul 8 P =
      Ed25519.add (Ed25519.add (Ed25519.add P P) (Ed25519.add P P))
        (Ed25519.add (Ed25519.add P P) (Ed25519.add P P)) := by
  have G := edGroupLaws hp
  rw [mul_eq_nsmul G P hP, show (8 : Nat) = 4 + 4 from rfl, nsmul_add G P hP, show (4 : Nat) = 2 + 2 from rfl,
    nsmul_add G P hP, show (2 : Nat) = 1 + 1 from rfl, nsmul_add G P hP, nsmul_one P hP]

theorem lim_feOneL : Lim (3 * 2 ^ 26) feOneL := ⟨rfl, by decide⟩

theorem lim_feZeroL : Lim (3 * 2 ^ 26) feZeroL := ⟨rfl, by decide⟩

/-- `bytesL` of a product of limbs below `3 · 2^26` depends only on the product's value. -/
theorem bytesL_mul_eq {a b c d : List Nat} (la : Lim (3 * 2 ^ 26) a) (lb : Lim (3 * 2 ^ 26) b)
    (lc : Lim (3 * 2 ^ 26) c) (ld : Lim (3 * 2 ^ 26) d) (h : fv a * fv b % Ed25519.p = fv c * fv d % Ed25519.p) :
    bytesL (mulL a b) = bytesL (mulL c d) := by
  obtain ⟨l1, e1⟩ := mulL_ok la lb
  obtain ⟨l2, e2⟩ := mulL_ok lc ld
  rw [bytesL_eq l1, bytesL_eq l2, e1, e2, h]

theorem isoStep_eq (X Y Z : List Nat) : isoStep X Y Z = projC (edDoubleSpec X Y Z) := rfl

theorem isoTimes8_eq (X Y Z : List Nat) :
    isoTimes8 X Y Z =
      projC (edDoubleSpec (isoStep (isoStep X Y Z).1 (isoStep X Y Z).2.1 (isoStep X Y Z).2.2).1
        (isoStep (isoStep X Y Z).1 (isoStep X Y Z).2.1 (isoStep X Y Z).2.2).2.1
        (isoStep (isoStep X Y Z).1 (isoStep X Y Z).2.1 (isoStep X Y Z).2.2).2.2) := rfl

/-- **`is_small_order` finds every point of small order**, given that `p` is prime. -/
theorem iso_ok (hp : IsPrime Ed25519.p) : IsoOK := by
  intro E P hP hE hiso
  have F := edFormulas hp
  have G := edGroupLaws hp
  have hD := G.closed P P hP hP
  have hD2 := G.closed _ _ hD hD
  have hD4 := G.closed _ _ hD2 hD2
  have r1 : PRep (isoStep E.1 E.2.1 E.2.2.1) (Ed25519.add P P) := by
    rw [isoStep_eq]
    exact F.proj (edDoubleSpec E.1 E.2.1 E.2.2.1) _ hD (F.dbl (E.1, E.2.1, E.2.2.1) P hP (prep_of_erep hE))
  have r3 : PRep (isoTimes8 E.1 E.2.1 E.2.2.1) (Ed25519.mul 8 P) := by
    rw [mul_eight hp P hP, isoTimes8_eq]
    generalize isoStep E.1 E.2.1 E.2.2.1 = q at r1
    have r2 : PRep (isoStep q.1 q.2.1 q.2.2) (Ed25519.add (Ed25519.add P P) (Ed25519.add P P)) := by
      rw [isoStep_eq]
      exact F.proj (edDoubleSpec q.1 q.2.1 q.2.2) _ hD2 (F.dbl q _ hD r1)
    generalize isoStep q.1 q.2.1 q.2.2 = q2 at r2
    exact F.proj (edDoubleSpec q2.1 q2.2.1 q2.2.2) _ hD4 (F.dbl q2 _ hD2 r2)
  unfold Ed25519.smallOrder
  cases h8 : (Ed25519.mul 8 P == Ed25519.zero)
  · rfl
  exfalso
  rw [beq_iff_eq.mp h8] at r3
  obtain ⟨lX, lY, lZ, -, hX, hY⟩ := r3
  have hZ : fv (isoTimes8 E.1 E.2.1 E.2.2.1).2.2 < Ed25519.p := fv_lt _
  have e1 : bytesL (mulL (isoTimes8 E.1 E.2.1 E.2.2.1).1 feOneL) =
      bytesL (mulL feZeroL (isoTimes8 E.1 E.2.1 E.2.2.1).2.2) := by
    refine bytesL_mul_eq (lX.mono (by decide)) lim_feOneL lim_feZeroL (lZ.mono (by decide)) ?_
    rw [hX]
    show 0 * _ % Ed25519.p * fv feOneL % Ed25519.p = fv feZeroL * _ % Ed25519.p
    rw [Nat.zero_mul, Nat.zero_mod, Nat.zero_mul, Nat.zero_mod, show fv feZeroL = 0 by rfl, Nat.zero_mul,
      Nat.zero_mod]
  have e2 : bytesL (mulL (isoTimes8 E.1 E.2.1 E.2.2.1).2.1 feOneL) =
      bytesL (mulL feOneL (isoTimes8 E.1 E.2.1 E.2.2.1).2.2) := by
    refine bytesL_mul_eq (lY.mono (by decide)) lim_feOneL lim_feOneL (lZ.mono (by decide)) ?_
    rw [hY]
    show 1 * _ % Ed25519.p * fv feOneL % Ed25519.p = fv feOneL * _ % Ed25519.p
    rw [show fv feOneL = 1 by rfl, Nat.one_mul, Nat.mul_one, Nat.mod_mod]
  have ht : isoSpec E.1 E.2.1 E.2.2.1 = true := by
    unfold isoSpec
    dsimp only
    rw [e1, e2, decide_eq_true rfl, decide_eq_true rfl]
    rfl
  rw [ht] at hiso
  exact Bool.noConfusion hiso

end C3.RV32.EdM
