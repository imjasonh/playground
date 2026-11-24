import C3BootProofs.Models.Ed25519Laws

/-!
# The algebra of the Ed25519 point formulas

Each theorem here is one limb formula's algebra modulo `p`: given what each
intermediate value is congruent to, the formula's output represents the
point it should. `Ed25519Formulas.lean` supplies those congruences from the
limb arithmetic. Each step is a `ring_mod` certificate whose cofactors
substitute the hypotheses one at a time.
-/

namespace C3.RV32.EdM

open C3.Models

local notation "𝔭" => ((Ed25519.p : Nat) : Int)
local notation "𝔡" => ((Ed25519.d : Nat) : Int)

theorem ne_of_meq {a b : Int} (h : MEq Ed25519.p a b) (hb : ¬ MEq Ed25519.p b 0) : ¬ MEq Ed25519.p a 0 :=
  fun ha => hb (h.symm.trans ha)

/-- From `X = x Z`, `Y = y Z`, and `X Y = Z T` with `Z ≠ 0`, `T = x y Z`. -/
theorem t_of_rep (hp : IsPrime Ed25519.p) {x y X Y Z T : Int} (hX : MEq Ed25519.p X (x * Z))
    (hY : MEq Ed25519.p Y (y * Z)) (hXY : MEq Ed25519.p (X * Y) (Z * T)) (hZ : ¬ MEq Ed25519.p Z 0) :
    MEq Ed25519.p T (x * y * Z) :=
  hp.meq_cancel hZ (sm (by ring_mod [(ms hXY) * (-1), (ms hX) * Y, (ms hY) * (x * Z)]))

/-- `ProjectivePoint::double`'s algebra for `P = (x, y)` on the curve, with
`u` and `v` the coordinates of `P + P`. -/
theorem dbl_alg (hp : IsPrime Ed25519.p) {x y u v X Y Z XX YY ZZ2 S A B X' T' : Int}
    (c : CurveI x y)
    (hu : MEq Ed25519.p (u * (1 + 𝔡 * x * x * y * y)) (x * y + y * x))
    (hv : MEq Ed25519.p (v * (1 - 𝔡 * x * x * y * y)) (y * y + x * x))
    (n1 : ¬ MEq Ed25519.p (1 + 𝔡 * x * x * y * y) 0) (n2 : ¬ MEq Ed25519.p (1 - 𝔡 * x * x * y * y) 0)
    (hX : MEq Ed25519.p X (x * Z)) (hY : MEq Ed25519.p Y (y * Z)) (hZ : ¬ MEq Ed25519.p Z 0)
    (hXX : MEq Ed25519.p XX (X * X)) (hYY : MEq Ed25519.p YY (Y * Y)) (hZZ2 : MEq Ed25519.p ZZ2 (2 * (Z * Z)))
    (hS : MEq Ed25519.p S ((X + Y) * (X + Y))) (hA : MEq Ed25519.p A (YY + XX)) (hB : MEq Ed25519.p B (YY - XX))
    (hX' : MEq Ed25519.p X' (S - A)) (hT' : MEq Ed25519.p T' (ZZ2 - B)) :
    MEq Ed25519.p X' (u * B) ∧ MEq Ed25519.p A (v * T') ∧ ¬ MEq Ed25519.p B 0 ∧ ¬ MEq Ed25519.p T' 0 := by
  have hB' : MEq Ed25519.p B (Z * Z * (1 + 𝔡 * x * x * y * y)) :=
    sm (by ring_mod [(ms hB) * 1, (ms hYY) * 1, (ms hXX) * (-1), (ms hY) * (Y + y * Z), (ms hX) * (-(X + x * Z)),
      c * (Z * Z)])
  have hT'' : MEq Ed25519.p T' (Z * Z * (1 - 𝔡 * x * x * y * y)) :=
    sm (by ring_mod [(ms hT') * 1, (ms hZZ2) * 1, (ms hB') * (-1)])
  refine ⟨sm ?_, sm ?_, ne_of_meq hB' (hp.meq_mul_ne (hp.meq_mul_ne hZ hZ) n1),
    ne_of_meq hT'' (hp.meq_mul_ne (hp.meq_mul_ne hZ hZ) n2)⟩
  · ring_mod [(ms hX') * 1, (ms hS) * 1, (ms hA) * (-1), (ms hYY) * (-1), (ms hXX) * (-1), (ms hX) * (2 * Y),
      (ms hY) * (2 * x * Z), (ms hB') * (-u), (ms hu) * (-(Z * Z))]
  · ring_mod [(ms hA) * 1, (ms hYY) * 1, (ms hXX) * 1, (ms hY) * (Y + y * Z), (ms hX) * (X + x * Z),
      (ms hT'') * (-v), (ms hv) * (-(Z * Z))]

/-- The algebra of `EdwardsPoint + ProjectiveNielsPoint` for `(x₁, y₁)`
and `(x₂, y₂)`, with `u` and `v` the coordinates of their sum. -/
theorem addN_alg (hp : IsPrime Ed25519.p)
    {x₁ y₁ x₂ y₂ u v X₁ Y₁ Z₁ T₁ N₁ N₂ Z₂ N₄ a s PP MM TT ZZ z Xc Yc Zc Tc : Int}
    (hu : MEq Ed25519.p (u * (1 + 𝔡 * x₁ * x₂ * y₁ * y₂)) (x₁ * y₂ + y₁ * x₂))
    (hv : MEq Ed25519.p (v * (1 - 𝔡 * x₁ * x₂ * y₁ * y₂)) (y₁ * y₂ + x₁ * x₂))
    (n1 : ¬ MEq Ed25519.p (1 + 𝔡 * x₁ * x₂ * y₁ * y₂) 0) (n2 : ¬ MEq Ed25519.p (1 - 𝔡 * x₁ * x₂ * y₁ * y₂) 0)
    (hX₁ : MEq Ed25519.p X₁ (x₁ * Z₁)) (hY₁ : MEq Ed25519.p Y₁ (y₁ * Z₁))
    (hT₁ : MEq Ed25519.p T₁ (x₁ * y₁ * Z₁)) (hZ₁ : ¬ MEq Ed25519.p Z₁ 0)
    (hN₁ : MEq Ed25519.p N₁ ((y₂ + x₂) * Z₂)) (hN₂ : MEq Ed25519.p N₂ ((y₂ - x₂) * Z₂))
    (hN₄ : MEq Ed25519.p N₄ (2 * 𝔡 * x₂ * y₂ * Z₂)) (hZ₂ : ¬ MEq Ed25519.p Z₂ 0)
    (ha : MEq Ed25519.p a (Y₁ + X₁)) (hs : MEq Ed25519.p s (Y₁ - X₁))
    (hPP : MEq Ed25519.p PP (a * N₁)) (hMM : MEq Ed25519.p MM (s * N₂)) (hTT : MEq Ed25519.p TT (T₁ * N₄))
    (hZZ : MEq Ed25519.p ZZ (Z₁ * Z₂)) (hz : MEq Ed25519.p z (ZZ + ZZ))
    (hXc : MEq Ed25519.p Xc (PP - MM)) (hYc : MEq Ed25519.p Yc (PP + MM))
    (hZc : MEq Ed25519.p Zc (z + TT)) (hTc : MEq Ed25519.p Tc (z - TT)) :
    MEq Ed25519.p Xc (u * Zc) ∧ MEq Ed25519.p Yc (v * Tc) ∧ ¬ MEq Ed25519.p Zc 0 ∧ ¬ MEq Ed25519.p Tc 0 := by
  have hZc' : MEq Ed25519.p Zc (2 * Z₁ * Z₂ * (1 + 𝔡 * x₁ * x₂ * y₁ * y₂)) :=
    sm (by ring_mod [(ms hZc) * 1, (ms hz) * 1, (ms hZZ) * 2, (ms hTT) * 1, (ms hT₁) * N₄,
      (ms hN₄) * (x₁ * y₁ * Z₁)])
  have hTc' : MEq Ed25519.p Tc (2 * Z₁ * Z₂ * (1 - 𝔡 * x₁ * x₂ * y₁ * y₂)) :=
    sm (by ring_mod [(ms hTc) * 1, (ms hz) * 1, (ms hZZ) * 2, (ms hTT) * (-1), (ms hT₁) * (-N₄),
      (ms hN₄) * (-(x₁ * y₁ * Z₁))])
  have hXc' : MEq Ed25519.p Xc (2 * Z₁ * Z₂ * (x₁ * y₂ + y₁ * x₂)) :=
    sm (by ring_mod [(ms hXc) * 1, (ms hPP) * 1, (ms hMM) * (-1), (ms ha) * N₁, (ms hs) * (-N₂),
      (ms hN₁) * (Y₁ + X₁), (ms hN₂) * (-(Y₁ - X₁)), (ms hY₁) * ((y₂ + x₂) * Z₂ - (y₂ - x₂) * Z₂),
      (ms hX₁) * ((y₂ + x₂) * Z₂ + (y₂ - x₂) * Z₂)])
  have hYc' : MEq Ed25519.p Yc (2 * Z₁ * Z₂ * (y₁ * y₂ + x₁ * x₂)) :=
    sm (by ring_mod [(ms hYc) * 1, (ms hPP) * 1, (ms hMM) * 1, (ms ha) * N₁, (ms hs) * N₂,
      (ms hN₁) * (Y₁ + X₁), (ms hN₂) * (Y₁ - X₁), (ms hY₁) * ((y₂ + x₂) * Z₂ + (y₂ - x₂) * Z₂),
      (ms hX₁) * ((y₂ + x₂) * Z₂ - (y₂ - x₂) * Z₂)])
  have h2 : ¬ MEq Ed25519.p (2 * Z₁ * Z₂) 0 := hp.meq_mul_ne (hp.meq_mul_ne two_ne hZ₁) hZ₂
  exact ⟨sm (by ring_mod [(ms hXc') * 1, (ms hZc') * (-u), (ms hu) * (-(2 * Z₁ * Z₂))]),
    sm (by ring_mod [(ms hYc') * 1, (ms hTc') * (-v), (ms hv) * (-(2 * Z₁ * Z₂))]),
    ne_of_meq hZc' (hp.meq_mul_ne h2 n1), ne_of_meq hTc' (hp.meq_mul_ne h2 n2)⟩

/-- The algebra of `CompletedPoint::as_extended` and `as_projective`. -/
theorem ext_alg (hp : IsPrime Ed25519.p) {x y X Y Z T E₁ E₂ E₃ E₄ : Int}
    (hX : MEq Ed25519.p X (x * Z)) (hY : MEq Ed25519.p Y (y * T)) (hZ : ¬ MEq Ed25519.p Z 0)
    (hT : ¬ MEq Ed25519.p T 0) (h₁ : MEq Ed25519.p E₁ (X * T)) (h₂ : MEq Ed25519.p E₂ (Y * Z))
    (h₃ : MEq Ed25519.p E₃ (Z * T)) (h₄ : MEq Ed25519.p E₄ (X * Y)) :
    ¬ MEq Ed25519.p E₃ 0 ∧ MEq Ed25519.p E₁ (x * E₃) ∧ MEq Ed25519.p E₂ (y * E₃) ∧
      MEq Ed25519.p (E₁ * E₂) (E₃ * E₄) :=
  ⟨ne_of_meq h₃ (hp.meq_mul_ne hZ hT), sm (by ring_mod [(ms h₁) * 1, (ms hX) * T, (ms h₃) * (-x)]),
    sm (by ring_mod [(ms h₂) * 1, (ms hY) * Z, (ms h₃) * (-y)]),
    sm (by ring_mod [(ms h₁) * E₂, (ms h₂) * (X * T), (ms h₃) * (-E₄), (ms h₄) * (-(Z * T))])⟩

/-- The algebra of `EdwardsPoint::as_projective_niels`. -/
theorem niels_alg (hp : IsPrime Ed25519.p) {x y X Y Z T D N₁ N₂ N₄ : Int}
    (hX : MEq Ed25519.p X (x * Z)) (hY : MEq Ed25519.p Y (y * Z)) (hXY : MEq Ed25519.p (X * Y) (Z * T))
    (hZ : ¬ MEq Ed25519.p Z 0) (hD : MEq Ed25519.p D (2 * 𝔡)) (h₁ : MEq Ed25519.p N₁ (Y + X))
    (h₂ : MEq Ed25519.p N₂ (Y - X)) (h₄ : MEq Ed25519.p N₄ (T * D)) :
    MEq Ed25519.p N₁ ((y + x) * Z) ∧ MEq Ed25519.p N₂ ((y - x) * Z) ∧
      MEq Ed25519.p N₄ (2 * 𝔡 * x * y * Z) := by
  have hT := t_of_rep hp hX hY hXY hZ
  exact ⟨sm (by ring_mod [(ms h₁) * 1, (ms hY) * 1, (ms hX) * 1]),
    sm (by ring_mod [(ms h₂) * 1, (ms hY) * 1, (ms hX) * (-1)]),
    sm (by ring_mod [(ms h₄) * 1, (ms hT) * D, (ms hD) * (x * y * Z)])⟩

end C3.RV32.EdM
