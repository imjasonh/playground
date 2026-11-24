import C3BootProofs.Models.WeierstrassClosed
import C3BootProofs.Models.EcdsaRcb

/-!
# Algorithm 4 represents the addition

`rcbAddOk_of` proves `RcbAddOk c` for every curve with a prime `p ≥ 3`,
`a = -3`, and no point of order 2 (`NoRoot c`: `x³ + a x + b` has no root
modulo `p`). The last hypothesis is needed: algorithm 4 returns `(0, 0, 0)`
for `P` and `P + T` when `T` has order 2 (Bosma and Lenstra).

For points `a` and `b` on the curve, `scaled_affine` shows that algorithm
4 at the triples `crep a` and `crep b` (`(x, y, 1)`, or `(0, 1, 0)` for
infinity) is a nonzero multiple of `crep (a + b)` modulo `p`. Its `z` is
`(x₂ - x₁)³ y₄` for a chord, where `(x₄, y₄) = a - b`, and `8 y₁³` for a
tangent; at `b = -a` its `y` is `(2 y₁)³ y'`, where `(x', y') = 2 a`. Each
is nonzero because no point has `y ≡ 0`. Algorithm 4 has degree 2 in each
argument, so `scaled_add` extends this to all representing triples.
-/

namespace C3.Models.EC

/-- `x³ + a x + b` has no root modulo `p`: no point of `c` has order 2. -/
def NoRoot (c : Curve) : Prop := ∀ x : Nat, ¬ MEq c.p ((x : Int) ^ 3 + c.a * x + c.b) 0

/-- The triple `(x, y, 1)` of an affine point, or `(0, 1, 0)` for infinity. -/
def crep : ECPoint → Int × Int × Int
  | none => (0, 1, 0)
  | some (x, y) => (x, y, 1)

/-- `P` is a nonzero multiple of `crep a` modulo `p`. -/
def Scaled (p : Nat) (P : Int × Int × Int) (a : ECPoint) : Prop :=
  ∃ μ : Int, ¬ MEq p μ 0 ∧ MEq p P.1 (μ * (crep a).1) ∧ MEq p P.2.1 (μ * (crep a).2.1) ∧
    MEq p P.2.2 (μ * (crep a).2.2)

theorem sq_eq (x : Int) : x ^ 2 = x * x := by rw [Int.pow_succ, Int.pow_one]

theorem cube_eq (x : Int) : x ^ 3 = x * x * x := by rw [Int.pow_succ, sq_eq]

theorem one_ne {p : Nat} (hp : IsPrime p) : ¬ MEq p 1 0 := by
  intro h
  have := MEq.natCast.mp (show MEq p ((1 : Nat) : Int) ((0 : Nat) : Int) from h)
  rw [Nat.zero_mod, Nat.mod_eq_of_lt hp.1] at this
  exact absurd this (by decide)

theorem two_ne {p : Nat} (hp3 : 3 ≤ p) : ¬ MEq p 2 0 := by
  intro h
  have := MEq.natCast.mp (show MEq p ((2 : Nat) : Int) ((0 : Nat) : Int) from h)
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at this
  exact absurd this (by decide)

/-- No point on a curve without roots has `y ≡ 0`. -/
theorem y_ne {c : Curve} (hr : NoRoot c) {x y : Nat} (h : OnC c (some (x, y))) : ¬ MEq c.p (y : Int) 0 := by
  intro hy
  have e := (onC_eq h).symm.trans (show MEq c.p ((y : Int) ^ 2) 0 by
    have := hy.mul hy; rwa [Int.zero_mul, ← sq_eq] at this)
  exact hr x e

theorem two_y_ne {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hr : NoRoot c) {x y : Nat}
    (h : OnC c (some (x, y))) : (y + y) % c.p ≠ 0 := by
  intro hs
  have e : MEq c.p (2 * (y : Int)) 0 := by
    have := MEq.natCast.mpr (show (y + y) % c.p = 0 % c.p by rw [hs, Nat.zero_mod])
    rw [Int.natCast_add, Int.natCast_zero, ← Int.two_mul] at this
    exact this
  rcases hp.meq_mul_zero e with e | e
  · exact two_ne hp3 e
  · exact y_ne hr h e

theorem a_rule {c : Curve} (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) : MEq c.p ((c.a : Int) ^ 1) (-3) := by
  rw [Int.pow_one, show (c.a : Int) = -3 + c.p * 1 by rw [hca]; omega]
  exact MEq.add_mul_self 1

theorem neg_meq {p y : Nat} (hy : y < p) : MEq p (((p - y) % p : Nat) : Int) (-(y : Int)) := by
  refine (natMod _ _).trans ?_
  rw [show ((p - y : Nat) : Int) = -(y : Int) + p * 1 by omega]
  exact MEq.add_mul_self 1

theorem mul3_ne {p : Nat} (hp : IsPrime p) {a b c : Int} (ha : ¬ MEq p a 0) (hb : ¬ MEq p b 0)
    (hc : ¬ MEq p c 0) : ¬ MEq p (a * b * c) 0 :=
  hp.meq_mul_ne (hp.meq_mul_ne ha hb) hc

/-! ## Affine arguments -/

theorem scaled_nn {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) :
    Scaled c.p (rcbAddI c.b 0 1 0 0 1 0) none := by
  have ha := a_rule hp3 hca
  refine ⟨1, one_ne hp, ?_, ?_, ?_⟩ <;> simp only [rcbAdd, crep] <;> curve_mod [] []

theorem scaled_ns {c : Curve} (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c) {x2 y2 : Nat}
    (hb : OnC c (some (x2, y2))) : Scaled c.p (rcbAddI c.b 0 1 0 x2 y2 1) (some (x2, y2)) := by
  have ha := a_rule hp3 hca
  have r2 := onC_eq hb
  refine ⟨y2, y_ne hr hb, ?_, ?_, ?_⟩ <;> simp only [rcbAdd, crep] <;> curve_mod [r2, ha] []

theorem scaled_sn {c : Curve} (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c) {x1 y1 : Nat}
    (ha' : OnC c (some (x1, y1))) : Scaled c.p (rcbAddI c.b x1 y1 1 0 1 0) (some (x1, y1)) := by
  have ha := a_rule hp3 hca
  have r1 := onC_eq ha'
  refine ⟨y1, y_ne hr ha', ?_, ?_, ?_⟩ <;> simp only [rcbAdd, crep] <;> curve_mod [r1, ha] []

/-- At `b = -a`, algorithm 4's `y` is `(2 y₁)³ y'`, where `(x', y') = 2 a`. -/
theorem scaled_opp {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c)
    {x1 y1 y2 : Nat} (ha' : OnC c (some (x1, y1))) (hs : (y1 + y2) % c.p = 0) :
    Scaled c.p (rcbAddI c.b x1 y1 1 x1 y2 1) none := by
  have ha := a_rule hp3 hca
  have r1 := onC_eq ha'
  have ry2 : MEq c.p ((y2 : Int) ^ 1) (-(y1 : Int)) := by
    have e := MEq.natCast.mpr (show (y1 + y2) % c.p = 0 % c.p by rw [hs, Nat.zero_mod])
    rw [Int.natCast_add, Int.natCast_zero] at e
    refine meq_pow_one (MEq.trans ?_ ((e.sub (MEq.refl (y1 : Int))).trans (MEq.of_eq (Int.zero_sub _))))
    exact MEq.of_eq (by omega)
  have hl := tangent_slope (x1 := x1) hp (two_y_ne hp hp3 hr ha')
  have hq := onC_tangent hp ha' hl
  generalize (3 * x1 * x1 + c.a) * c.inv (2 * y1 % c.p) % c.p = l at hl hq
  have ex3 := meq_x3d (L := l * l) ha'.1
  rw [Int.natCast_mul] at ex3
  generalize (l * l + 2 * c.p - 2 * x1) % c.p = x3 at hq ex3
  have ey3 := meq_y3 (l := l) (x1 := x1) hq.1 ha'.2.1
  generalize (l * (x1 + c.p - x3) + c.p - y1) % c.p = y3 at hq ey3
  have hE := MEq.iff_sub.mp hl
  have hF2 : MEq c.p (rcbAddI c.b x1 y1 1 x1 y2 1).2.1 ((2 * (y1 : Int)) ^ 3 * y3) := by
    simp only [rcbAdd]
    curve_mod (fuel := 3) [meq_pow_one ey3, meq_pow_one ex3, ry2, r1, ha]
      [hE * (6 * (l : Int) * x1 ^ 2 * y1 + 4 * (l : Int) ^ 2 * y1 ^ 2 + 9 * (x1 : Int) ^ 4 -
        12 * (x1 : Int) * y1 ^ 2 - 6 * (l : Int) * y1 - 18 * (x1 : Int) ^ 2 + 9)]
  have h2y : ¬ MEq c.p (2 * (y1 : Int)) 0 := hp.meq_mul_ne (two_ne hp3) (y_ne hr ha')
  refine ⟨(rcbAddI c.b x1 y1 1 x1 y2 1).2.1, fun h => ?_, ?_, ?_, ?_⟩
  · have h0 := hF2.symm.trans h
    rw [cube_eq] at h0
    exact hp.meq_mul_ne (mul3_ne hp h2y h2y h2y) (y_ne hr hq) h0
  · refine MEq.trans ?_ (MEq.of_eq (Int.mul_zero _).symm)
    simp only [rcbAdd]
    curve_mod [ry2, r1, ha] []
  · exact MEq.of_eq (Int.mul_one _).symm
  · refine MEq.trans ?_ (MEq.of_eq (Int.mul_zero _).symm)
    simp only [rcbAdd]
    curve_mod [ry2, r1, ha] []

/-- At `b = a`, algorithm 4's `z` is `8 y₁³`. -/
theorem scaled_tangent {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c)
    {x1 y1 l : Nat} (ha' : OnC c (some (x1, y1)))
    (hl : MEq c.p ((l : Int) * (2 * (y1 : Int))) ((3 * x1 * x1 + c.a : Nat) : Int)) :
    Scaled c.p (rcbAddI c.b x1 y1 1 x1 y1 1) (some ((l * l + 2 * c.p - 2 * x1) % c.p,
      (l * (x1 + c.p - (l * l + 2 * c.p - 2 * x1) % c.p) + c.p - y1) % c.p)) := by
  have ha := a_rule hp3 hca
  have r1 := onC_eq ha'
  have hF3 : MEq c.p (rcbAddI c.b x1 y1 1 x1 y1 1).2.2 (8 * (y1 : Int) ^ 3) := by
    simp only [rcbAdd]
    curve_mod [r1, ha] []
  have ex3 := meq_x3d (L := l * l) ha'.1
  rw [Int.natCast_mul] at ex3
  have hx3 := Nat.mod_lt (l * l + 2 * c.p - 2 * x1) hp.pos
  generalize (l * l + 2 * c.p - 2 * x1) % c.p = x3 at hx3 ex3 ⊢
  have ey3 := meq_y3 (l := l) (x1 := x1) hx3 ha'.2.1
  generalize (l * (x1 + c.p - x3) + c.p - y1) % c.p = y3 at ey3 ⊢
  have hE := MEq.iff_sub.mp hl
  have hy := y_ne hr ha'
  refine ⟨(rcbAddI c.b x1 y1 1 x1 y1 1).2.2, fun h => ?_, ?_, ?_, MEq.of_eq (Int.mul_one _).symm⟩
  · have h0 := hF3.symm.trans h
    rw [show (8 : Int) * (y1 : Int) ^ 3 = 2 * 2 * 2 * ((y1 : Int) * y1 * y1) by rw [cube_eq]; ring_eq] at h0
    exact hp.meq_mul_ne (mul3_ne hp (two_ne hp3) (two_ne hp3) (two_ne hp3)) (mul3_ne hp hy hy hy) h0
  · have h1 : MEq c.p (rcbAddI c.b x1 y1 1 x1 y1 1).1 ((x3 : Int) * (8 * (y1 : Int) ^ 3)) := by
      simp only [rcbAdd]
      curve_mod (fuel := 3) [meq_pow_one ex3, r1, ha]
        [hE * (-4 * (l : Int) * y1 ^ 2 - 6 * (x1 : Int) ^ 2 * y1 + 6 * y1)]
    exact h1.trans (((MEq.refl _).mul hF3.symm).trans (MEq.of_eq (Int.mul_comm _ _)))
  · have h2 : MEq c.p (rcbAddI c.b x1 y1 1 x1 y1 1).2.1 ((y3 : Int) * (8 * (y1 : Int) ^ 3)) := by
      simp only [rcbAdd]
      curve_mod (fuel := 3) [meq_pow_one ey3, meq_pow_one ex3, r1, ha]
        [hE * (6 * (l : Int) * x1 ^ 2 * y1 + 4 * (l : Int) ^ 2 * y1 ^ 2 + 9 * (x1 : Int) ^ 4 -
          12 * (x1 : Int) * y1 ^ 2 - 6 * (l : Int) * y1 - 18 * (x1 : Int) ^ 2 + 9)]
    exact h2.trans (((MEq.refl _).mul hF3.symm).trans (MEq.of_eq (Int.mul_comm _ _)))

/-- For a chord, algorithm 4's `z` is `(x₂ - x₁)³ y₄`, where `(x₄, y₄) = a - b`. -/
theorem scaled_chord {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c)
    {x1 y1 x2 y2 l : Nat} (ha' : OnC c (some (x1, y1))) (hb : OnC c (some (x2, y2))) (hx : x1 ≠ x2)
    (hl : MEq c.p ((l : Int) * ((x2 : Int) - x1)) ((y2 : Int) - y1)) :
    Scaled c.p (rcbAddI c.b x1 y1 1 x2 y2 1) (some ((l * l + 2 * c.p - x1 - x2) % c.p,
      (l * (x1 + c.p - (l * l + 2 * c.p - x1 - x2) % c.p) + c.p - y1) % c.p)) := by
  have ha := a_rule hp3 hca
  have r1 := onC_eq ha'
  have hF3 : MEq c.p (rcbAddI c.b x1 y1 1 x2 y2 1).2.2 0 → False := by
    have hb' : OnC c (some (x2, (c.p - y2) % c.p)) := onC_neg hp.pos hb
    have hl' := chord (y2 := (c.p - y2) % c.p) hp ha'.1 hb.1 ha'.2.1 hx
    generalize ((c.p - y2) % c.p + c.p - y1) * c.inv ((x2 + c.p - x1) % c.p) % c.p = l' at hl'
    have hq := onC_chord hp ha' hb' hx hl'
    obtain ⟨ry2', rx2', ex4⟩ := chord_rules hp ha' hb' hx hl'
    generalize (l' * l' + 2 * c.p - x1 - x2) % c.p = x4 at hq ex4
    have ey4 := meq_y3 (l := l') (x1 := x1) hq.1 ha'.2.1
    generalize (l' * (x1 + c.p - x4) + c.p - y1) % c.p = y4 at hq ey4
    have ey2 : MEq c.p ((y2 : Int) ^ 1) (-(y1 : Int) - l' * ((x2 : Int) - x1)) := by
      have e := (neg_meq hb.2.1).symm.trans (by rw [← Int.pow_one (((c.p - y2) % c.p : Nat) : Int)]; exact ry2')
      refine meq_pow_one ((MEq.of_eq (Int.neg_neg _).symm).trans ?_)
      exact e.neg.trans (MEq.of_eq (by ring_eq))
    intro h
    have h3 : MEq c.p (((x2 : Int) - x1) ^ 3 * y4) 0 := by
      refine MEq.trans ?_ h
      simp only [rcbAdd]
      curve_mod (fuel := 3) [meq_pow_one ey4, meq_pow_one ex4, ey2, rx2', r1, ha] []
    have hD := sub_ne_of_ne ha'.1 hb.1 hx
    rw [cube_eq] at h3
    exact hp.meq_mul_ne (mul3_ne hp hD hD hD) (y_ne hr hq) h3
  obtain ⟨ry2, rx2, ex3⟩ := chord_rules hp ha' hb hx hl
  have hx3 := Nat.mod_lt (l * l + 2 * c.p - x1 - x2) hp.pos
  generalize (l * l + 2 * c.p - x1 - x2) % c.p = x3 at hx3 ex3 ⊢
  have ey3 := meq_y3 (l := l) (x1 := x1) hx3 ha'.2.1
  generalize (l * (x1 + c.p - x3) + c.p - y1) % c.p = y3 at ey3 ⊢
  refine ⟨(rcbAddI c.b x1 y1 1 x2 y2 1).2.2, hF3, ?_, ?_, MEq.of_eq (Int.mul_one _).symm⟩
  · simp only [rcbAdd, crep]
    curve_mod (fuel := 3) [meq_pow_one ey3, meq_pow_one ex3, ry2, rx2, r1, ha] []
  · simp only [rcbAdd, crep]
    curve_mod (fuel := 3) [meq_pow_one ey3, meq_pow_one ex3, ry2, rx2, r1, ha] []

theorem scaled_ss {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c)
    {x1 y1 x2 y2 : Nat} (ha' : OnC c (some (x1, y1))) (hb : OnC c (some (x2, y2))) :
    Scaled c.p (rcbAddI c.b x1 y1 1 x2 y2 1) (c.add (some (x1, y1)) (some (x2, y2))) := by
  by_cases hx : x1 = x2
  · subst hx
    by_cases hs : (y1 + y2) % c.p = 0
    · simp only [Curve.add, ↓reduceIte, hs]
      exact scaled_opp hp hp3 hca hr ha' hs
    · simp only [Curve.add, ↓reduceIte, hs]
      obtain rfl := same_x hp ha'.2.1 hb.2.1 ha'.2.2 hb.2.2 hs
      exact scaled_tangent hp hp3 hca hr ha' (tangent_slope hp hs)
  · simp only [Curve.add, hx, ↓reduceIte]
    exact scaled_chord hp hp3 hca hr ha' hb hx (chord hp ha'.1 hb.1 ha'.2.1 hx)

theorem scaled_affine {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c)
    {a b : ECPoint} (ha : OnC c a) (hb : OnC c b) :
    Scaled c.p (rcbAddI c.b (crep a).1 (crep a).2.1 (crep a).2.2 (crep b).1 (crep b).2.1 (crep b).2.2)
      (c.add a b) := by
  rcases a with _ | ⟨x1, y1⟩ <;> rcases b with _ | ⟨x2, y2⟩
  · exact scaled_nn hp hp3 hca
  · rw [add_none_left]; exact scaled_ns hp3 hca hr hb
  · rw [add_none_right]; exact scaled_sn hp3 hca hr ha
  · exact scaled_ss hp hp3 hca hr ha hb

/-! ## Projective arguments -/

/-- Algorithm 4 has degree 2 in each argument. -/
theorem rcb_hom (b x1 y1 z1 x2 y2 z2 k m : Int) :
    (rcbAddI b (k * x1) (k * y1) (k * z1) (m * x2) (m * y2) (m * z2)).1 =
        k * k * (m * m) * (rcbAddI b x1 y1 z1 x2 y2 z2).1 ∧
      (rcbAddI b (k * x1) (k * y1) (k * z1) (m * x2) (m * y2) (m * z2)).2.1 =
        k * k * (m * m) * (rcbAddI b x1 y1 z1 x2 y2 z2).2.1 ∧
      (rcbAddI b (k * x1) (k * y1) (k * z1) (m * x2) (m * y2) (m * z2)).2.2 =
        k * k * (m * m) * (rcbAddI b x1 y1 z1 x2 y2 z2).2.2 := by
  simp only [rcbAdd]
  refine ⟨?_, ?_, ?_⟩ <;> ring_eq

theorem rcb_meq {p : Nat} {b x1 y1 z1 x2 y2 z2 X1 Y1 Z1 X2 Y2 Z2 : Int} (h1 : MEq p x1 X1) (h2 : MEq p y1 Y1)
    (h3 : MEq p z1 Z1) (h4 : MEq p x2 X2) (h5 : MEq p y2 Y2) (h6 : MEq p z2 Z2) :
    MEq p (rcbAddI b x1 y1 z1 x2 y2 z2).1 (rcbAddI b X1 Y1 Z1 X2 Y2 Z2).1 ∧
      MEq p (rcbAddI b x1 y1 z1 x2 y2 z2).2.1 (rcbAddI b X1 Y1 Z1 X2 Y2 Z2).2.1 ∧
      MEq p (rcbAddI b x1 y1 z1 x2 y2 z2).2.2 (rcbAddI b X1 Y1 Z1 X2 Y2 Z2).2.2 :=
  rcbAdd_rel (fun h h' => MEq.mul h h') (fun h h' => MEq.add h h') (fun h h' => MEq.sub h h')
    (fun h => MEq.add h h) (MEq.refl b) h1 h2 h3 h4 h5 h6

/-- Algorithm 4 at nonzero multiples of `crep a` and `crep b` is a nonzero
multiple of `crep (a + b)`. -/
theorem scaled_add {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c)
    {A B : Int × Int × Int} {a b : ECPoint} (hA : Scaled c.p A a) (hB : Scaled c.p B b) (ha : OnC c a)
    (hb : OnC c b) : Scaled c.p (rcbAddI c.b A.1 A.2.1 A.2.2 B.1 B.2.1 B.2.2) (c.add a b) := by
  obtain ⟨μ, hμ, a1, a2, a3⟩ := hA
  obtain ⟨ν, hν, b1, b2, b3⟩ := hB
  obtain ⟨l, hl, s1, s2, s3⟩ := scaled_affine hp hp3 hca hr ha hb
  obtain ⟨r1, r2, r3⟩ := rcb_meq (b := (c.b : Int)) a1 a2 a3 b1 b2 b3
  obtain ⟨e1, e2, e3⟩ := rcb_hom c.b (crep a).1 (crep a).2.1 (crep a).2.2 (crep b).1 (crep b).2.1 (crep b).2.2 μ ν
  refine ⟨μ * μ * (ν * ν) * l, hp.meq_mul_ne (hp.meq_mul_ne (hp.meq_mul_ne hμ hμ) (hp.meq_mul_ne hν hν)) hl,
    ?_, ?_, ?_⟩
  · exact r1.trans ((MEq.of_eq e1).trans (((MEq.refl _).mul s1).trans (MEq.of_eq (Int.mul_assoc _ _ _).symm)))
  · exact r2.trans ((MEq.of_eq e2).trans (((MEq.refl _).mul s2).trans (MEq.of_eq (Int.mul_assoc _ _ _).symm)))
  · exact r3.trans ((MEq.of_eq e3).trans (((MEq.refl _).mul s3).trans (MEq.of_eq (Int.mul_assoc _ _ _).symm)))

theorem natCast_ne {p n : Nat} (hn : n < p) (h0 : n ≠ 0) : ¬ MEq p (n : Int) 0 := by
  intro h
  have := MEq.natCast.mp (show MEq p (n : Int) ((0 : Nat) : Int) from h)
  rw [Nat.mod_eq_of_lt hn, Nat.zero_mod] at this
  exact h0 this

theorem scaled_of_prep {p X Y Z : Nat} {a : ECPoint} (h : PRep p (X, Y, Z) a) :
    Scaled p ((X : Int), (Y : Int), (Z : Int)) a := by
  rcases a with _ | ⟨x, y⟩
  · obtain ⟨_, hY, _, hX0, hY0, hZ0⟩ := h
    have hX : X = 0 := hX0
    have hZ : Z = 0 := hZ0
    subst hX hZ
    exact ⟨Y, natCast_ne hY hY0, MEq.of_eq (Int.mul_zero _).symm, MEq.of_eq (Int.mul_one _).symm,
      MEq.of_eq (Int.mul_zero _).symm⟩
  · obtain ⟨_, _, hZ, _, _, hZ0, hX, hY⟩ := h
    exact ⟨Z, natCast_ne hZ hZ0, hX.trans (MEq.of_eq (Int.mul_comm _ _)),
      hY.trans (MEq.of_eq (Int.mul_comm _ _)), MEq.of_eq (Int.mul_one _).symm⟩

theorem prep_of_scaled {c : Curve} {X Y Z : Nat} {s : ECPoint} (hs : OnC c s) (hX : X < c.p) (hY : Y < c.p)
    (hZ : Z < c.p) (h : Scaled c.p ((X : Int), (Y : Int), (Z : Int)) s) : PRep c.p (X, Y, Z) s := by
  obtain ⟨μ, hμ, h1, h2, h3⟩ := h
  rcases s with _ | ⟨x, y⟩
  · have e1 : MEq c.p (X : Int) 0 := h1.trans (MEq.of_eq (Int.mul_zero _))
    have e3 : MEq c.p (Z : Int) 0 := h3.trans (MEq.of_eq (Int.mul_zero _))
    refine ⟨hX, hY, hZ, Decidable.byContradiction fun h0 => natCast_ne hX h0 e1, fun e => ?_,
      Decidable.byContradiction fun h0 => natCast_ne hZ h0 e3⟩
    have e' : Y = 0 := e
    subst e'
    exact hμ ((MEq.of_eq (Int.mul_one μ).symm).trans h2.symm)
  · have hz : MEq c.p (Z : Int) μ := h3.trans (MEq.of_eq (Int.mul_one μ))
    refine ⟨hX, hY, hZ, hs.1, hs.2.1, fun e => ?_, ?_, ?_⟩
    · have e' : Z = 0 := e
      subst e'
      exact hμ hz.symm
    · exact h1.trans ((MEq.of_eq (Int.mul_comm μ x)).trans ((MEq.refl (x : Int)).mul hz.symm))
    · exact h2.trans ((MEq.of_eq (Int.mul_comm μ y)).trans ((MEq.refl (y : Int)).mul hz.symm))

/-- **Algorithm 4 represents the addition** on a curve with prime `p ≥ 3`,
`a = -3`, and no point of order 2. -/
theorem rcbAddOk_of {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c) :
    RcbAddOk c := by
  rintro ⟨X1, Y1, Z1⟩ ⟨X2, Y2, Z2⟩ ⟨X, Y, Z⟩ a b hA hB ha hb hX hY hZ e1 e2 e3
  obtain ⟨μ, hμ, s1, s2, s3⟩ := scaled_add hp hp3 hca hr (scaled_of_prep hA) (scaled_of_prep hB) ha hb
  exact prep_of_scaled (addClosed_of_prime hp a b ha hb) hX hY hZ ⟨μ, hμ, e1.trans s1, e2.trans s2, e3.trans s3⟩

end C3.Models.EC
