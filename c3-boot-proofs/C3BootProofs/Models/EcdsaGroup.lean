import C3BootProofs.Models.EcdsaField

/-!
# The group of a curve's points, and scalar multiples

`AbGrp` is an abelian group given by its operations and axioms, with
integer multiples `zs` and the rule `zs (j + k) g = zs j g + zs k g`. The
points of a curve form one when the addition is associative and keeps
points on the curve (`AddAssoc` and `AddClosed`, carried as hypotheses);
commutativity and inverses are proved here from the prime modulus.
`Curve.mul k q` is then the multiple `zs k q`.
-/

namespace C3.Models

/-- An abelian group by its operations and axioms. -/
structure AbGrp (G : Type) where
  add : G → G → G
  zero : G
  neg : G → G
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add a (neg a) = zero

namespace AbGrp

variable {G : Type} (A : AbGrp G)

theorem add_zero (a : G) : A.add a A.zero = a := by rw [A.add_comm, A.zero_add]

theorem neg_unique {a b : G} (h : A.add a b = A.zero) : b = A.neg a := by
  calc b = A.add A.zero b := (A.zero_add b).symm
    _ = A.add (A.add a (A.neg a)) b := by rw [A.add_neg]
    _ = A.add (A.neg a) (A.add a b) := by rw [A.add_comm a, A.add_assoc]
    _ = A.neg a := by rw [h, A.add_zero]

theorem neg_add (a b : G) : A.neg (A.add a b) = A.add (A.neg a) (A.neg b) := by
  refine (A.neg_unique ?_).symm
  calc A.add (A.add a b) (A.add (A.neg a) (A.neg b))
      = A.add (A.add a (A.neg a)) (A.add b (A.neg b)) := by
        rw [A.add_assoc, A.add_assoc, ← A.add_assoc b, A.add_comm b (A.neg a), A.add_assoc]
    _ = A.zero := by rw [A.add_neg, A.add_neg, A.zero_add]

theorem neg_zero : A.neg A.zero = A.zero := (A.neg_unique (A.zero_add A.zero)).symm

/-- `n` times `g`. -/
def ns (g : G) : Nat → G
  | 0 => A.zero
  | n + 1 => A.add g (ns g n)

/-- `k` times `g`, for an integer `k`. -/
def zs (k : Int) (g : G) : G :=
  match k with
  | .ofNat n => A.ns g n
  | .negSucc n => A.neg (A.ns g (n + 1))

theorem zs_zero (g : G) : A.zs 0 g = A.zero := rfl

theorem zs_ofNat (n : Nat) (g : G) : A.zs (n : Int) g = A.ns g n := rfl

theorem zs_succ (k : Int) (g : G) : A.zs (k + 1) g = A.add g (A.zs k g) := by
  match k with
  | .ofNat n =>
    rfl
  | .negSucc 0 =>
    rw [show Int.negSucc 0 + 1 = 0 by decide]
    show A.zs 0 g = A.add g (A.neg (A.add g A.zero))
    rw [A.add_zero, A.add_neg]; rfl
  | .negSucc (m + 1) =>
    rw [show Int.negSucc (m + 1) + 1 = Int.negSucc m by rw [Int.negSucc_eq, Int.negSucc_eq]; omega]
    show A.neg (A.ns g (m + 1)) = A.add g (A.neg (A.add g (A.ns g (m + 1))))
    rw [A.neg_add, ← A.add_assoc, A.add_neg, A.zero_add]

theorem zs_pred (k : Int) (g : G) : A.zs (k - 1) g = A.add (A.neg g) (A.zs k g) := by
  have h := A.zs_succ (k - 1) g
  rw [Int.sub_add_cancel] at h
  rw [h, ← A.add_assoc, A.add_comm (A.neg g), A.add_neg, A.zero_add]

theorem zs_add_nat (j : Int) (g : G) : ∀ n : Nat, A.zs (j + n) g = A.add (A.zs j g) (A.zs n g)
  | 0 => by rw [Int.natCast_zero, Int.add_zero, zs_zero, A.add_zero]
  | n + 1 => by
    rw [Int.natCast_add, Int.natCast_one, ← Int.add_assoc, A.zs_succ, zs_add_nat j g n, A.zs_succ,
      ← A.add_assoc, A.add_comm g, A.add_assoc]

theorem zs_sub_nat (j : Int) (g : G) : ∀ n : Nat, A.zs (j - n) g = A.add (A.zs j g) (A.zs (-(n : Int)) g)
  | 0 => by rw [Int.natCast_zero, Int.sub_zero, Int.neg_zero, zs_zero, A.add_zero]
  | n + 1 => by
    rw [show j - ((n + 1 : Nat) : Int) = j - n - 1 by omega,
      show -((n + 1 : Nat) : Int) = -(n : Int) - 1 by omega, A.zs_pred, zs_sub_nat j g n, A.zs_pred,
      ← A.add_assoc, A.add_comm (A.neg g), A.add_assoc]

theorem zs_add (j k : Int) (g : G) : A.zs (j + k) g = A.add (A.zs j g) (A.zs k g) := by
  match k with
  | .ofNat n => exact A.zs_add_nat j g n
  | .negSucc n =>
    have e : Int.negSucc n = -((n + 1 : Nat) : Int) := by rw [Int.negSucc_eq]; omega
    rw [e, ← Int.sub_eq_add_neg]; exact A.zs_sub_nat j g (n + 1)

theorem zs_one (g : G) : A.zs 1 g = g := by
  show A.add g A.zero = g; exact A.add_zero g

theorem zs_neg (k : Int) (g : G) : A.zs (-k) g = A.neg (A.zs k g) := by
  refine A.neg_unique ?_
  rw [← A.zs_add, Int.add_right_neg]; rfl

theorem zs_two_mul (k : Int) (g : G) : A.zs (2 * k) g = A.add (A.zs k g) (A.zs k g) := by
  rw [Int.two_mul, A.zs_add]

end AbGrp

/-! ## The points of a curve -/

namespace EC

/-- A point of the curve: infinity, or coordinates below `p` that satisfy
the curve's equation. -/
def OnC (c : Curve) : ECPoint → Prop
  | none => True
  | some (x, y) => x < c.p ∧ y < c.p ∧ MEq c.p (y * y) (x * x * x + c.a * x + c.b)

/-- The negation of a point. -/
def neg (c : Curve) : ECPoint → ECPoint
  | none => none
  | some (x, y) => some (x, (c.p - y) % c.p)

/-- The sum of two points on the curve is on the curve. -/
def AddClosed (c : Curve) : Prop := ∀ a b, OnC c a → OnC c b → OnC c (c.add a b)

/-- The addition is associative on the curve's points. -/
def AddAssoc (c : Curve) : Prop :=
  ∀ a b d, OnC c a → OnC c b → OnC c d → c.add (c.add a b) d = c.add a (c.add b d)

theorem add_none_left (c : Curve) (a : ECPoint) : c.add none a = a := by cases a <;> rfl

theorem add_none_right (c : Curve) (a : ECPoint) : c.add a none = a := by
  rcases a with _ | ⟨x, y⟩ <;> rfl

theorem onC_neg {c : Curve} (hp : 0 < c.p) {a : ECPoint} (h : OnC c a) : OnC c (neg c a) := by
  rcases a with _ | ⟨x, y⟩
  · trivial
  · obtain ⟨hx, hy, he⟩ := h
    refine ⟨hx, Nat.mod_lt _ hp, ?_⟩
    have e : MEq c.p (((c.p - y) % c.p : Nat) : Int) (-(y : Int)) :=
      (natMod _ _).trans (by
        rw [show (((c.p - y : Nat)) : Int) = (c.p : Int) * 1 + -(y : Int) by omega, Int.add_comm]
        exact MEq.add_mul_self 1)
    refine ((e.mul e).trans ?_).trans he
    rw [Int.neg_mul_neg]; exact MEq.refl _

theorem add_neg_self (c : Curve) {a : ECPoint} (h : OnC c a) : c.add a (neg c a) = none := by
  rcases a with _ | ⟨x, y⟩
  · rfl
  · obtain ⟨-, hy, -⟩ := h
    have h0 : (y + (c.p - y) % c.p) % c.p = 0 := by
      by_cases hy0 : y = 0
      · subst hy0; rw [Nat.sub_zero, Nat.mod_self, Nat.zero_add, Nat.zero_mod]
      · rw [Nat.mod_eq_of_lt (show c.p - y < c.p by omega), show y + (c.p - y) = c.p by omega, Nat.mod_self]
    simp only [Curve.add, neg, ↓reduceIte, h0]

/-- Equal residues below `p` are equal. -/
theorem eq_of_meq {p x y : Nat} (hx : x < p) (hy : y < p) (h : MEq p x y) : x = y := by
  have := MEq.natCast.mp h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem meq_sub {p x y : Nat} (hy : y < p) : MEq p ((x + p - y : Nat) : Int) ((x : Int) - y) := by
  rw [show ((x + p - y : Nat) : Int) = (x : Int) - y + (p : Int) * 1 by omega]
  exact MEq.add_mul_self 1

/-- The slope of a chord, as `add` computes it, times the run is the rise. -/
theorem chord {c : Curve} (hp : IsPrime c.p) {x1 y1 x2 y2 : Nat} (hx1 : x1 < c.p) (hx2 : x2 < c.p)
    (hy1 : y1 < c.p) (hne : x1 ≠ x2) :
    MEq c.p (((y2 + c.p - y1) * c.inv ((x2 + c.p - x1) % c.p) % c.p : Nat) * ((x2 : Int) - x1))
      ((y2 : Int) - y1) := by
  have hd : (x2 + c.p - x1) % c.p ≠ 0 := by
    by_cases hlt : x2 + c.p - x1 < c.p
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hinv := modInv_prime (a := (x2 + c.p - x1) % c.p) hp (by rw [Nat.mod_mod]; exact hd)
  have hD : MEq c.p (((x2 + c.p - x1) % c.p : Nat) : Int) ((x2 : Int) - x1) := (natMod _ _).trans (meq_sub hx1)
  refine ((natMod _ _).mul (MEq.refl _)).trans ?_
  rw [Int.natCast_mul]
  have e1 : MEq c.p ((((y2 + c.p - y1 : Nat) : Int) * (c.inv ((x2 + c.p - x1) % c.p) : Int)) * ((x2 : Int) - x1))
      (((y2 + c.p - y1 : Nat) : Int) * ((c.inv ((x2 + c.p - x1) % c.p) : Int) *
        (((x2 + c.p - x1) % c.p : Nat) : Int))) := by
    rw [Int.mul_assoc]; exact (MEq.refl _).mul ((MEq.refl _).mul hD.symm)
  refine e1.trans ?_
  have e2 : MEq c.p ((c.inv ((x2 + c.p - x1) % c.p) : Int) * (((x2 + c.p - x1) % c.p : Nat) : Int)) 1 := by
    rw [Int.mul_comm]; exact hinv
  refine ((MEq.refl _).mul e2).trans ?_
  rw [Int.mul_one]; exact meq_sub hy1

/-- Points with the same `x` on the curve have `y`s equal or opposite. -/
theorem same_x {c : Curve} (hp : IsPrime c.p) {x y1 y2 : Nat} (hy1 : y1 < c.p) (hy2 : y2 < c.p)
    (h1 : MEq c.p (y1 * y1) (x * x * x + c.a * x + c.b)) (h2 : MEq c.p (y2 * y2) (x * x * x + c.a * x + c.b))
    (hs : (y1 + y2) % c.p ≠ 0) : y1 = y2 := by
  have h : MEq c.p (((y1 : Int) - y2) * ((y1 : Int) + y2)) 0 := by
    have e : ((y1 : Int) - y2) * ((y1 : Int) + y2) = (y1 : Int) * y1 - (y2 : Int) * y2 := by
      rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (y2 : Int) y1]; omega
    have h1' : MEq c.p ((y1 : Int) * y1) ((x * x * x + c.a * x + c.b : Nat) : Int) := by rw [← Int.natCast_mul]; exact h1
    have h2' : MEq c.p ((y2 : Int) * y2) ((x * x * x + c.a * x + c.b : Nat) : Int) := by rw [← Int.natCast_mul]; exact h2
    rw [e]; exact MEq.iff_sub.mp (h1'.trans h2'.symm)
  rcases hp.meq_mul_zero h with h | h
  · exact eq_of_meq hy1 hy2 (MEq.iff_sub.mpr h)
  · exact absurd (MEq.natCast.mp (show MEq c.p ((y1 + y2 : Nat) : Int) ((0 : Nat) : Int) by
      rw [Int.natCast_add]; exact h)) (by rw [Nat.zero_mod]; exact hs)

theorem add_comm {c : Curve} (hp : IsPrime c.p) {a b : ECPoint} (ha : OnC c a) (hb : OnC c b) :
    c.add a b = c.add b a := by
  rcases a with _ | ⟨x1, y1⟩
  · rw [add_none_left, add_none_right]
  rcases b with _ | ⟨x2, y2⟩
  · rw [add_none_left, add_none_right]
  obtain ⟨hx1, hy1, he1⟩ := ha
  obtain ⟨hx2, hy2, he2⟩ := hb
  by_cases hx : x1 = x2
  · subst hx
    simp only [Curve.add, ↓reduceIte]
    by_cases hs : (y1 + y2) % c.p = 0
    · rw [ite_eq_left hs, ite_eq_left (by rw [Nat.add_comm]; exact hs)]
    · rw [ite_eq_right hs, ite_eq_right (by rw [Nat.add_comm]; exact hs)]
      rw [same_x hp hy1 hy2 he1 he2 hs]
  · simp only [Curve.add, ite_eq_right hx, ite_eq_right (Ne.symm hx)]
    generalize hl1 : (y2 + c.p - y1) * c.inv ((x2 + c.p - x1) % c.p) % c.p = l1
    generalize hl2 : (y1 + c.p - y2) * c.inv ((x1 + c.p - x2) % c.p) % c.p = l2
    have c1 := chord (y2 := y2) hp hx1 hx2 hy1 hx
    have c2 := chord (y2 := y1) hp hx2 hx1 hy2 (Ne.symm hx)
    rw [hl1] at c1; rw [hl2] at c2
    have hdne : ¬ MEq c.p ((x2 : Int) - x1) 0 := fun h =>
      hx (eq_of_meq hx1 hx2 (MEq.iff_sub.mpr h).symm)
    have hl : l1 = l2 := by
      refine eq_of_meq (hl1 ▸ Nat.mod_lt _ hp.pos) (hl2 ▸ Nat.mod_lt _ hp.pos) (hp.meq_cancel hdne (c1.trans ?_))
      have : (l2 : Int) * ((x2 : Int) - x1) = -((l2 : Int) * ((x1 : Int) - x2)) := by
        rw [← Int.mul_neg, Int.neg_sub]
      rw [this, show (y2 : Int) - y1 = -((y1 : Int) - y2) by omega]
      exact c2.symm.neg
    subst hl
    have hx3 : (l1 * l1 + 2 * c.p - x1 - x2) % c.p = (l1 * l1 + 2 * c.p - x2 - x1) % c.p := by
      rw [Nat.sub_right_comm]
    rw [hx3]
    generalize hx3' : (l1 * l1 + 2 * c.p - x2 - x1) % c.p = x3
    have hx3lt : x3 < c.p := hx3' ▸ Nat.mod_lt _ hp.pos
    congr 2
    refine eq_of_meq (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) ?_
    refine (natMod _ _).trans (MEq.trans ?_ (natMod _ _).symm)
    refine (meq_sub hy1).trans (MEq.trans ?_ (meq_sub hy2).symm)
    rw [Int.natCast_mul, Int.natCast_mul]
    refine (((MEq.refl _).mul (meq_sub hx3lt)).sub (MEq.refl _)).trans
      (MEq.trans ?_ (((MEq.refl _).mul (meq_sub hx3lt)).sub (MEq.refl _)).symm)
    rw [MEq.iff_sub]
    have e : (l1 : Int) * ((x1 : Int) - x3) - y1 - ((l1 : Int) * ((x2 : Int) - x3) - y2) =
        -((l1 : Int) * ((x2 : Int) - x1) - ((y2 : Int) - y1)) := by
      rw [Int.mul_sub, Int.mul_sub, Int.mul_sub]; omega
    rw [e]
    have := (MEq.iff_sub.mp c1).neg
    rwa [Int.neg_zero] at this

/-- The points of the curve, as a type. -/
abbrev Pts (c : Curve) := { a : ECPoint // OnC c a }

/-- The group of the curve's points, given that the addition is associative
and keeps points on the curve. -/
def grp (c : Curve) (hp : IsPrime c.p) (hc : AddClosed c) (ha : AddAssoc c) : AbGrp (Pts c) where
  add a b := ⟨c.add a.1 b.1, hc _ _ a.2 b.2⟩
  zero := ⟨none, trivial⟩
  neg a := ⟨neg c a.1, onC_neg hp.pos a.2⟩
  add_assoc a b d := Subtype.ext (ha _ _ _ a.2 b.2 d.2)
  add_comm a b := Subtype.ext (add_comm hp a.2 b.2)
  zero_add a := Subtype.ext (add_none_left c a.1)
  add_neg a := Subtype.ext (add_neg_self c a.2)

/-- `Curve.mul` is the multiple the group defines. -/
theorem mul_eq {c : Curve} (hp : IsPrime c.p) (hc : AddClosed c) (ha : AddAssoc c) (q : Pts c) :
    ∀ k : Nat, c.mul k q.1 = ((grp c hp hc ha).zs k q).1 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rw [Curve.mul]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, hk]; rfl
    · rw [ite_eq_right hk]
      have hlt : k / 2 < k := Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
      have e2 : ((grp c hp hc ha).zs ((k / 2 : Nat) : Int) q).1 = c.mul (k / 2) q.1 := (ih _ hlt).symm
      have hd : c.add (c.mul (k / 2) q.1) (c.mul (k / 2) q.1) = ((grp c hp hc ha).zs ((2 * (k / 2) : Nat) : Int) q).1 := by
        rw [show ((2 * (k / 2) : Nat) : Int) = 2 * ((k / 2 : Nat) : Int) by omega, AbGrp.zs_two_mul, ← e2]; rfl
      by_cases hodd : k % 2 = 1
      · rw [ite_eq_left hodd, hd]
        have : (k : Int) = ((2 * (k / 2) : Nat) : Int) + 1 := by omega
        rw [this, AbGrp.zs_add, AbGrp.zs_one]; rfl
      · rw [ite_eq_right hodd, hd]
        congr 3; omega

end EC

end C3.Models
