import C3BootProofs.Models.EcdsaGroup
import C3BootProofs.Models.WeierstrassRing

/-!
# The sum of two points is on the curve

`addClosed_of_prime` proves `EC.AddClosed c` for every curve whose `p` is
prime, with any `a` and `b`. The lemmas before it turn the `x` and `y` that
`Curve.add` computes into congruences that `curve_mod` can use: the slope
`l` of a chord or tangent, `x₃ ≡ l² - x₁ - x₂`, and `y₃ ≡ l (x₁ - x₃) - y₁`.
-/

namespace C3.Models.EC

theorem meq_pow_one {p : Nat} {x y : Int} (h : MEq p x y) : MEq p (x ^ 1) y := by
  rw [Int.pow_one]; exact h

/-- The curve's equation at a point on it, with `y²` on the left. -/
theorem onC_eq {c : Curve} {x y : Nat} (h : OnC c (some (x, y))) :
    MEq c.p ((y : Int) ^ 2) ((x : Int) ^ 3 + c.a * x + c.b) := by
  have e := MEq.iff_sub.mp h.2.2
  curve_mod [] [e * 1]

/-- The curve's equation as a congruence to zero. -/
theorem onC_sub {c : Curve} {x y : Nat} (h : OnC c (some (x, y))) :
    MEq c.p ((y : Int) ^ 2 - ((x : Int) ^ 3 + c.a * x + c.b)) 0 :=
  MEq.iff_sub.mp (onC_eq h)

theorem meq_x3c {p L x1 x2 : Nat} (hx1 : x1 < p) (hx2 : x2 < p) :
    MEq p (((L + 2 * p - x1 - x2) % p : Nat) : Int) ((L : Int) - x1 - x2) := by
  refine (natMod _ _).trans ?_
  rw [show ((L + 2 * p - x1 - x2 : Nat) : Int) = (L : Int) - x1 - x2 + p * 2 by omega]
  exact MEq.add_mul_self 2

theorem meq_x3d {p L x : Nat} (hx : x < p) :
    MEq p (((L + 2 * p - 2 * x) % p : Nat) : Int) ((L : Int) - 2 * x) := by
  refine (natMod _ _).trans ?_
  rw [show ((L + 2 * p - 2 * x : Nat) : Int) = (L : Int) - 2 * x + p * 2 by omega]
  exact MEq.add_mul_self 2

theorem meq_y3 {p l x1 x3 y1 : Nat} (hx3 : x3 < p) (hy1 : y1 < p) :
    MEq p (((l * (x1 + p - x3) + p - y1) % p : Nat) : Int) ((l : Int) * ((x1 : Int) - x3) - y1) := by
  refine (natMod _ _).trans ?_
  have e1 : ((x1 + p - x3 : Nat) : Int) = (x1 : Int) - x3 + p := by omega
  have e2 : ((l * (x1 + p - x3) + p - y1 : Nat) : Int) = ((l * (x1 + p - x3) : Nat) : Int) + p - y1 := by
    generalize l * (x1 + p - x3) = M; omega
  rw [e2, Int.natCast_mul, e1,
    show (l : Int) * ((x1 : Int) - x3 + p) + p - y1 = (l : Int) * ((x1 : Int) - x3) - y1 + p * (l + 1) by
      ring_eq]
  exact MEq.add_mul_self _

/-- The `x` of the chord's third point: `x₂² ≡ 2 y₁ l + l² (x₂ - x₁) - x₁ x₂ - x₁² - a`,
where `y₂ ≡ y₁ + l (x₂ - x₁)`. -/
theorem chord_x2 {p : Nat} (hp : IsPrime p) {a b x1 y1 x2 y2 l : Int} (hD : ¬ MEq p (x2 - x1) 0)
    (h1 : MEq p (y1 ^ 2) (x1 ^ 3 + a * x1 + b)) (h2 : MEq p (y2 ^ 2 - (x2 ^ 3 + a * x2 + b)) 0)
    (hl : MEq p (y2 ^ 1) (y1 + l * (x2 - x1))) :
    MEq p (x2 ^ 2) (2 * y1 * l + l * l * (x2 - x1) - x1 * x2 - x1 * x1 - a) := by
  have hE : MEq p ((x2 - x1) * (x2 ^ 2 - (2 * y1 * l + l * l * (x2 - x1) - x1 * x2 - x1 * x1 - a))) 0 := by
    curve_mod [hl, h1] [h2 * (-1)]
  rcases hp.meq_mul_zero hE with h | h
  · exact absurd h hD
  · exact MEq.iff_sub.mpr h

theorem sub_ne_of_ne {p x1 x2 : Nat} (hx1 : x1 < p) (hx2 : x2 < p) (hx : x1 ≠ x2) :
    ¬ MEq p ((x2 : Int) - x1) 0 := fun h => hx (eq_of_meq hx1 hx2 (MEq.iff_sub.mpr h).symm)

/-- The congruences of a chord's sum: `y₂`, `x₂²`, `x₃`, and `y₃` as `curve_mod` rules. -/
theorem chord_rules {c : Curve} (hp : IsPrime c.p) {x1 y1 x2 y2 l : Nat} (ha : OnC c (some (x1, y1)))
    (hb : OnC c (some (x2, y2))) (hx : x1 ≠ x2) (hl : MEq c.p ((l : Int) * ((x2 : Int) - x1)) ((y2 : Int) - y1)) :
    MEq c.p ((y2 : Int) ^ 1) ((y1 : Int) + l * ((x2 : Int) - x1)) ∧
      MEq c.p ((x2 : Int) ^ 2) (2 * (y1 : Int) * l + l * l * ((x2 : Int) - x1) - x1 * x2 - x1 * x1 - c.a) ∧
      MEq c.p (((l * l + 2 * c.p - x1 - x2) % c.p : Nat) : Int) ((l : Int) * l - x1 - x2) := by
  have ry2 : MEq c.p ((y2 : Int) ^ 1) ((y1 : Int) + l * ((x2 : Int) - x1)) := by
    refine meq_pow_one (MEq.iff_sub.mpr ?_)
    have := (MEq.iff_sub.mp hl).neg
    rw [Int.neg_zero] at this
    refine MEq.trans (MEq.of_eq ?_) this
    ring_eq
  refine ⟨ry2, chord_x2 hp (sub_ne_of_ne ha.1 hb.1 hx) (onC_eq ha) (onC_sub hb) ry2, ?_⟩
  have := meq_x3c (L := l * l) ha.1 hb.1
  rwa [Int.natCast_mul] at this

theorem onC_chord {c : Curve} (hp : IsPrime c.p) {x1 y1 x2 y2 l : Nat} (ha : OnC c (some (x1, y1)))
    (hb : OnC c (some (x2, y2))) (hx : x1 ≠ x2) (hl : MEq c.p ((l : Int) * ((x2 : Int) - x1)) ((y2 : Int) - y1)) :
    OnC c (some ((l * l + 2 * c.p - x1 - x2) % c.p,
      (l * (x1 + c.p - (l * l + 2 * c.p - x1 - x2) % c.p) + c.p - y1) % c.p)) := by
  obtain ⟨ry2, rx2, ex3⟩ := chord_rules hp ha hb hx hl
  have hx3 := Nat.mod_lt (l * l + 2 * c.p - x1 - x2) hp.pos
  generalize (l * l + 2 * c.p - x1 - x2) % c.p = x3 at hx3 ex3 ⊢
  have ey3 := meq_y3 (l := l) (x1 := x1) hx3 ha.2.1
  have hy3 := Nat.mod_lt (l * (x1 + c.p - x3) + c.p - y1) hp.pos
  generalize (l * (x1 + c.p - x3) + c.p - y1) % c.p = y3 at hy3 ey3 ⊢
  refine ⟨hx3, hy3, ?_⟩
  have r1 := onC_eq ha
  curve_mod (fuel := 3) [meq_pow_one ey3, meq_pow_one ex3, ry2, rx2, r1] []

/-- The slope of the tangent, as `add` computes it, times `2 y` is `3 x² + a`. -/
theorem tangent_slope {c : Curve} (hp : IsPrime c.p) {x1 y1 : Nat} (hs : (y1 + y1) % c.p ≠ 0) :
    MEq c.p ((((3 * x1 * x1 + c.a) * c.inv (2 * y1 % c.p) % c.p : Nat) : Int) * (2 * (y1 : Int)))
      ((3 * x1 * x1 + c.a : Nat) : Int) := by
  have h2 : (2 * y1 % c.p) % c.p ≠ 0 := by rw [Nat.mod_mod, Nat.two_mul]; exact hs
  have hinv : MEq c.p (((2 * y1 % c.p : Nat) : Int) * (c.inv (2 * y1 % c.p) : Int)) 1 := modInv_prime hp h2
  have hE1 := MEq.iff_sub.mp hinv
  have hE2 : MEq c.p (((2 * y1 % c.p : Nat) : Int) - 2 * (y1 : Int)) 0 := MEq.iff_sub.mp (natMod (2 * y1) c.p)
  refine ((natMod _ _).mul (MEq.refl _)).trans ?_
  curve_mod [] [hE1 * ((3 * x1 * x1 + c.a : Nat) : Int),
    hE2 * (-(((3 * x1 * x1 + c.a : Nat) : Int) * (c.inv (2 * y1 % c.p) : Int)))]

theorem onC_tangent {c : Curve} (hp : IsPrime c.p) {x1 y1 l : Nat} (ha : OnC c (some (x1, y1)))
    (hl : MEq c.p ((l : Int) * (2 * (y1 : Int))) ((3 * x1 * x1 + c.a : Nat) : Int)) :
    OnC c (some ((l * l + 2 * c.p - 2 * x1) % c.p,
      (l * (x1 + c.p - (l * l + 2 * c.p - 2 * x1) % c.p) + c.p - y1) % c.p)) := by
  have ex3 := meq_x3d (L := l * l) ha.1
  rw [Int.natCast_mul] at ex3
  have hx3 := Nat.mod_lt (l * l + 2 * c.p - 2 * x1) hp.pos
  generalize (l * l + 2 * c.p - 2 * x1) % c.p = x3 at hx3 ex3 ⊢
  have ey3 := meq_y3 (l := l) (x1 := x1) hx3 ha.2.1
  have hy3 := Nat.mod_lt (l * (x1 + c.p - x3) + c.p - y1) hp.pos
  generalize (l * (x1 + c.p - x3) + c.p - y1) % c.p = y3 at hy3 ey3 ⊢
  refine ⟨hx3, hy3, ?_⟩
  have r1 := onC_eq ha
  have hE := MEq.iff_sub.mp hl
  curve_mod (fuel := 3) [meq_pow_one ey3, meq_pow_one ex3, r1] [hE * ((l : Int) ^ 2 - 3 * x1)]

/-- **The sum of two points on a curve is on the curve**, for every curve
whose `p` is prime. -/
theorem addClosed_of_prime {c : Curve} (hp : IsPrime c.p) : AddClosed c := by
  intro a b ha hb
  rcases a with _ | ⟨x1, y1⟩
  · rw [add_none_left]; exact hb
  rcases b with _ | ⟨x2, y2⟩
  · rw [add_none_right]; exact ha
  by_cases hx : x1 = x2
  · subst hx
    simp only [Curve.add, ↓reduceIte]
    by_cases hs : (y1 + y2) % c.p = 0
    · rw [ite_eq_left hs]; trivial
    rw [ite_eq_right hs]
    have := same_x hp ha.2.1 hb.2.1 ha.2.2 hb.2.2 hs
    subst this
    exact onC_tangent hp ha (tangent_slope hp hs)
  · simp only [Curve.add, ite_eq_right hx]
    exact onC_chord hp ha hb hx (chord hp ha.1 hb.1 ha.2.1 hx)

end C3.Models.EC
