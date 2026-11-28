import C3BootProofs.Models.WeierstrassAssocPoly

/-!
# The addition is associative

For affine points `a`, `b`, and `d`, `addAssoc_of` writes `a + b` and
`b + d` with the slopes of their lines (`add_slope`), and algorithm 4 at
the affine triples of `(a + b, d)` and of `(a, b + d)` is a nonzero
multiple of `crep ((a + b) + d)` and of `crep (a + (b + d))`
(`scaled_add`). `assoc_x` and `assoc_y` say the two triples are
proportional, so `eq_of_scaled` gives the same point. When `b = -a` or
`d = -b`, the same argument compares one side with `d` or with `a`. Sums
with the point at infinity are associative by `add_none_left` and
`add_none_right`.
-/

namespace C3.Models.EC

open C3.Ring

theorem scaled_crep {p : Nat} (hp : IsPrime p) (a : ECPoint) : Scaled p (crep a) a :=
  ⟨1, one_ne hp, MEq.of_eq (Int.one_mul _).symm, MEq.of_eq (Int.one_mul _).symm,
    MEq.of_eq (Int.one_mul _).symm⟩

/-- Two proportional triples that are nonzero multiples of points on the
curve represent the same point. -/
theorem eq_of_scaled {c : Curve} (hp : IsPrime c.p) {L R : Int × Int × Int} {u v : ECPoint} (hu : OnC c u)
    (hv : OnC c v) (hL : Scaled c.p L u) (hR : Scaled c.p R v) (ex : MEq c.p (L.1 * R.2.2) (R.1 * L.2.2))
    (ey : MEq c.p (L.2.1 * R.2.2) (R.2.1 * L.2.2)) : u = v := by
  obtain ⟨l, hl, l1, l2, l3⟩ := hL
  obtain ⟨r, hr, r1, r2, r3⟩ := hR
  have e := (l2.mul r3).symm.trans (ey.trans (r2.mul l3))
  have hlr := hp.meq_mul_ne hl hr
  rcases u with _ | ⟨x, y⟩ <;> rcases v with _ | ⟨x', y'⟩
  · rfl
  · refine absurd ((MEq.of_eq ?_).trans (e.trans (MEq.of_eq ?_))) hlr
    · show l * r = l * 1 * (r * 1)
      rw [Int.mul_one, Int.mul_one]
    · show r * y' * (l * 0) = 0
      rw [Int.mul_zero, Int.mul_zero]
  · refine absurd ((MEq.of_eq ?_).trans (e.symm.trans (MEq.of_eq ?_))) hlr
    · show l * r = r * 1 * (l * 1)
      rw [Int.mul_one, Int.mul_one, Int.mul_comm]
    · show l * y * (r * 0) = 0
      rw [Int.mul_zero, Int.mul_zero]
  · have ex' := (l1.mul r3).symm.trans (ex.trans (r1.mul l3))
    have hx : MEq c.p ((x : Int) * (l * r)) ((x' : Int) * (l * r)) :=
      (MEq.of_eq (by show (x : Int) * (l * r) = l * x * (r * 1); rw [Int.mul_one]; ac_rfl)).trans
        (ex'.trans (MEq.of_eq (by show r * x' * (l * 1) = (x' : Int) * (l * r); rw [Int.mul_one]; ac_rfl)))
    have hy : MEq c.p ((y : Int) * (l * r)) ((y' : Int) * (l * r)) :=
      (MEq.of_eq (by show (y : Int) * (l * r) = l * y * (r * 1); rw [Int.mul_one]; ac_rfl)).trans
        (e.trans (MEq.of_eq (by show r * y' * (l * 1) = (y' : Int) * (l * r); rw [Int.mul_one]; ac_rfl)))
    rw [eq_of_meq hu.1 hv.1 (hp.meq_cancel hlr hx), eq_of_meq hu.2.1 hv.2.1 (hp.meq_cancel hlr hy)]

theorem add_eq_none {c : Curve} {x1 y1 x2 y2 : Nat} (h : c.add (some (x1, y1)) (some (x2, y2)) = none) :
    x1 = x2 ∧ (y1 + y2) % c.p = 0 := by
  by_cases hx : x1 = x2
  · subst hx
    refine ⟨rfl, Decidable.byContradiction fun hs => ?_⟩
    simp only [Curve.add, ↓reduceIte, hs] at h
    cases h
  · simp only [Curve.add, hx, ↓reduceIte] at h
    cases h

/-- A sum of two affine points that isn't infinity is the third point on
a line through them, with some slope `l`. -/
theorem add_slope {c : Curve} (hp : IsPrime c.p) {x1 y1 x2 y2 : Nat} (ha : OnC c (some (x1, y1)))
    (hb : OnC c (some (x2, y2))) (hne : c.add (some (x1, y1)) (some (x2, y2)) ≠ none) :
    ∃ l x4 y4 : Nat, c.add (some (x1, y1)) (some (x2, y2)) = some (x4, y4) ∧
      MEq c.p ((y2 : Int) ^ 1) ((y1 : Int) + l * ((x2 : Int) - x1)) ∧
      MEq c.p ((x2 : Int) ^ 2) (2 * (y1 : Int) * l + l * l * ((x2 : Int) - x1) - x1 * x2 - x1 * x1 - c.a) ∧
      MEq c.p ((x4 : Int) ^ 1) ((l : Int) * l - x1 - x2) ∧
      MEq c.p ((y4 : Int) ^ 1) ((l : Int) * ((x1 : Int) - x4) - y1) := by
  by_cases hx : x1 = x2
  · subst hx
    by_cases hs : (y1 + y2) % c.p = 0
    · exact absurd (by simp only [Curve.add, ↓reduceIte, hs]) hne
    obtain rfl := same_x hp ha.2.1 hb.2.1 ha.2.2 hb.2.2 hs
    have hl := tangent_slope (x1 := x1) hp hs
    have hE := MEq.iff_sub.mp hl
    refine ⟨(3 * x1 * x1 + c.a) * c.inv (2 * y1 % c.p) % c.p,
      ((3 * x1 * x1 + c.a) * c.inv (2 * y1 % c.p) % c.p *
        ((3 * x1 * x1 + c.a) * c.inv (2 * y1 % c.p) % c.p) + 2 * c.p - 2 * x1) % c.p, _,
      by simp only [Curve.add, ↓reduceIte, hs], ?_, ?_,
      meq_pow_one ((meq_x3d ha.1).trans (MEq.of_eq (by rw [Int.natCast_mul]; omega))),
      meq_pow_one (meq_y3 (Nat.mod_lt _ hp.pos) ha.2.1)⟩
    · curve_mod [] []
    · curve_mod [] [hE * (-1)]
  · have hl := chord (y2 := y2) hp ha.1 hb.1 ha.2.1 hx
    obtain ⟨ry2, rx2, ex4⟩ := chord_rules hp ha hb hx hl
    exact ⟨_, _, _, by simp only [Curve.add, hx, ↓reduceIte], ry2, rx2, meq_pow_one ex4,
      meq_pow_one (meq_y3 (Nat.mod_lt _ hp.pos) ha.2.1)⟩

/-- **The addition is associative** on a curve with prime `p ≥ 3`, `a = -3`,
and no point of order 2. -/
theorem addAssoc_of {c : Curve} (hp : IsPrime c.p) (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) (hr : NoRoot c) :
    AddAssoc c := by
  intro a b d ha hb hd
  rcases a with _ | ⟨x1, y1⟩
  · rw [add_none_left, add_none_left]
  rcases b with _ | ⟨x2, y2⟩
  · rw [add_none_right, add_none_left]
  rcases d with _ | ⟨x3, y3⟩
  · rw [add_none_right, add_none_right]
  have hC := addClosed_of_prime hp
  have ra := a_rule hp3 hca
  have r1 := onC_eq ha
  have sc := scaled_crep hp
  by_cases hab : c.add (some (x1, y1)) (some (x2, y2)) = none
  · obtain ⟨hx, hs⟩ := add_eq_none hab
    subst hx
    have ry2 := opp_rule hs
    rw [hab, add_none_left]
    by_cases hbd : c.add (some (x1, y2)) (some (x3, y3)) = none
    · obtain ⟨hx, hs'⟩ := add_eq_none hbd
      subst hx
      rw [hbd, add_none_right]
      have ry3 := opp_rule hs'
      rw [Int.pow_one] at ry2 ry3
      rw [eq_of_meq hd.2.1 ha.2.1 (ry3.trans (ry2.neg.trans (MEq.of_eq (Int.neg_neg _))))]
    · obtain ⟨l, x5, y5, he, ry3, rx3, ex5, ey5⟩ := add_slope hp hb hd hbd
      have h5 : OnC c (some (x5, y5)) := he ▸ hC _ _ hb hd
      rw [he]
      refine eq_of_scaled hp hd (hC _ _ ha h5) (sc (some (x3, y3)))
        (scaled_add (A := ((x1 : Int), (y1 : Int), 1)) (B := ((x5 : Int), (y5 : Int), 1)) hp hp3 hca hr
          (sc (some (x1, y1))) (sc (some (x5, y5))) ha h5) ?_ ?_
      · show MEq c.p ((x3 : Int) * (rcbAddI c.b x1 y1 1 x5 y5 1).2.2) ((rcbAddI c.b x1 y1 1 x5 y5 1).1 * 1)
        simp only [rcbAdd]
        curve_mod [ey5, ex5, ry3, rx3, ry2, r1, ra] []
      · show MEq c.p ((y3 : Int) * (rcbAddI c.b x1 y1 1 x5 y5 1).2.2) ((rcbAddI c.b x1 y1 1 x5 y5 1).2.1 * 1)
        simp only [rcbAdd]
        curve_mod [ey5, ex5, ry3, rx3, ry2, r1, ra] []
  · obtain ⟨l1, x4, y4, he4, ry2, rx2, ex4, ey4⟩ := add_slope hp ha hb hab
    have h4 : OnC c (some (x4, y4)) := he4 ▸ hC _ _ ha hb
    rw [he4]
    by_cases hbd : c.add (some (x2, y2)) (some (x3, y3)) = none
    · obtain ⟨hx, hs'⟩ := add_eq_none hbd
      subst hx
      have ry3 := opp_rule hs'
      rw [hbd, add_none_right]
      refine eq_of_scaled hp (hC _ _ h4 hd) ha
        (scaled_add (A := ((x4 : Int), (y4 : Int), 1)) (B := ((x2 : Int), (y3 : Int), 1)) hp hp3 hca hr
          (sc (some (x4, y4))) (sc (some (x2, y3))) h4 hd) (sc (some (x1, y1))) ?_ ?_
      · show MEq c.p ((rcbAddI c.b x4 y4 1 x2 y3 1).1 * 1) ((x1 : Int) * (rcbAddI c.b x4 y4 1 x2 y3 1).2.2)
        simp only [rcbAdd]
        curve_mod [ey4, ex4, ry3, ry2, rx2, r1, ra] []
      · show MEq c.p ((rcbAddI c.b x4 y4 1 x2 y3 1).2.1 * 1) ((y1 : Int) * (rcbAddI c.b x4 y4 1 x2 y3 1).2.2)
        simp only [rcbAdd]
        curve_mod [ey4, ex4, ry3, ry2, rx2, r1, ra] []
    · obtain ⟨l3, x5, y5, he5, ry3, rx3, ex5, ey5⟩ := add_slope hp hb hd hbd
      have h5 : OnC c (some (x5, y5)) := he5 ▸ hC _ _ hb hd
      rw [he5]
      exact eq_of_scaled hp (hC _ _ h4 hd) (hC _ _ ha h5)
        (scaled_add (A := ((x4 : Int), (y4 : Int), 1)) (B := ((x3 : Int), (y3 : Int), 1)) hp hp3 hca hr
          (sc (some (x4, y4))) (sc (some (x3, y3))) h4 hd)
        (scaled_add (A := ((x1 : Int), (y1 : Int), 1)) (B := ((x5 : Int), (y5 : Int), 1)) hp hp3 hca hr
          (sc (some (x1, y1))) (sc (some (x5, y5))) ha h5)
        (assoc_x ey4 ex4 ey5 ex5 ry3 ry2 rx3 rx2 r1 ra) (assoc_y ey4 ex4 ey5 ex5 ry3 ry2 rx3 rx2 r1 ra)

end C3.Models.EC
