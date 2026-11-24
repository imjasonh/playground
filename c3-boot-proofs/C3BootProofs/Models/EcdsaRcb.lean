import C3BootProofs.Models.EcdsaRep

/-!
# Complete projective formulas for `a = -3`, for any curve

`rcbAdd` and `rcbDbl` are Renes, Costello, and Batina's complete addition
and doubling for `a = -3` (algorithms 4 and 6), over any field operations,
in the order of `primeorder`'s source. Over Montgomery operations they are
the compiled point formulas of both curves; over the integers they are
polynomials.

`mont_add_rep` and `mont_dbl_rep` reduce the Montgomery formulas to two
statements about the integer polynomials: `RcbAddOk`, that algorithm 4
represents the curve's addition, and `RcbDblPoly`, the polynomial identity
that makes algorithm 6 algorithm 4 at `P = Q` on the curve.
-/

namespace C3.Models

/-- Algorithm 4 over the operations `m`, `a`, `s`, and `d` (product, sum,
difference, and double), with curve constant `b`. -/
def rcbAdd {α : Type} (m a s : α → α → α) (d : α → α) (b x1 y1 z1 x2 y2 z2 : α) : α × α × α :=
  let xx := m x1 x2
  let yy := m y1 y2
  let zz := m z1 z2
  let xyPairs := s (m (a x1 y1) (a x2 y2)) (a xx yy)
  let yzPairs := s (m (a y1 z1) (a y2 z2)) (a yy zz)
  let xzPairs := s (m (a x1 z1) (a x2 z2)) (a xx zz)
  let bzzPart := s xzPairs (m b zz)
  let bzz3Part := a (d bzzPart) bzzPart
  let yyMBzz3 := s yy bzz3Part
  let yyPBzz3 := a yy bzz3Part
  let zz3 := a (d zz) zz
  let bxzPart := s (m b xzPairs) (a zz3 xx)
  let bxz3Part := a (d bxzPart) bxzPart
  let xx3MZz3 := s (a (d xx) xx) zz3
  (s (m yyPBzz3 xyPairs) (m yzPairs bxz3Part),
   a (m yyPBzz3 yyMBzz3) (m xx3MZz3 bxz3Part),
   a (m yyMBzz3 yzPairs) (m xyPairs xx3MZz3))

/-- Algorithm 6, the doubling, over the same operations. -/
def rcbDbl {α : Type} (m a s : α → α → α) (d : α → α) (b X Y Z : α) : α × α × α :=
  let xx := m X X
  let yy := m Y Y
  let zz := m Z Z
  let xy2 := d (m X Y)
  let xz2 := d (m X Z)
  let bzz := s (m b zz) xz2
  let bzz3 := a (d bzz) bzz
  let yymb := s yy bzz3
  let yypb := a yy bzz3
  let yf := m yypb yymb
  let xf := m yymb xy2
  let zz3 := a (d zz) zz
  let bxz2 := s (m b xz2) (a zz3 xx)
  let bxz6 := a (d bxz2) bxz2
  let xx3mzz3 := s (a (d xx) xx) zz3
  let y := a yf (m xx3mzz3 bxz6)
  let yz2 := d (m Y Z)
  let x := s xf (m bxz6 yz2)
  let z := d (d (m yz2 yy))
  (x, y, z)

/-- Algorithm 4 over the integers. -/
abbrev rcbAddI (b x1 y1 z1 x2 y2 z2 : Int) : Int × Int × Int :=
  rcbAdd (· * ·) (· + ·) (· - ·) (fun x => x + x) b x1 y1 z1 x2 y2 z2

/-- Algorithm 6 over the integers. -/
abbrev rcbDblI (b X Y Z : Int) : Int × Int × Int :=
  rcbDbl (· * ·) (· + ·) (· - ·) (fun x => x + x) b X Y Z

/-- **Algorithm 4 represents the addition of `c`** (for `a = -3`): for any
two triples that represent points on `c`, every triple congruent modulo
`p` to algorithm 4's integer result represents their sum. -/
def RcbAddOk (c : Curve) : Prop :=
  ∀ (A B P : Nat × Nat × Nat) (a b : ECPoint), PRep c.p A a → PRep c.p B b → EC.OnC c a → EC.OnC c b →
    P.1 < c.p → P.2.1 < c.p → P.2.2 < c.p →
    MEq c.p P.1 (rcbAddI c.b A.1 A.2.1 A.2.2 B.1 B.2.1 B.2.2).1 →
    MEq c.p P.2.1 (rcbAddI c.b A.1 A.2.1 A.2.2 B.1 B.2.1 B.2.2).2.1 →
    MEq c.p P.2.2 (rcbAddI c.b A.1 A.2.1 A.2.2 B.1 B.2.1 B.2.2).2.2 → PRep c.p P (c.add a b)

/-- **The doubling identity**, a polynomial identity in `ℤ[b, X, Y, Z]`:
algorithm 6 at `(X, Y, Z)` has the `x` and `y` of algorithm 4 at
`(X, Y, Z) + (X, Y, Z)`, and its `z` is algorithm 4's `z` plus `6 Y E`,
where `E = Y² Z - X³ + 3 X Z² - b Z³` vanishes on the curve. -/
def RcbDblPoly : Prop :=
  ∀ b X Y Z : Int, (rcbDblI b X Y Z).1 = (rcbAddI b X Y Z X Y Z).1 ∧
    (rcbDblI b X Y Z).2.1 = (rcbAddI b X Y Z X Y Z).2.1 ∧
    (rcbDblI b X Y Z).2.2 = (rcbAddI b X Y Z X Y Z).2.2 + 6 * Y * (Y * Y * Z - X * X * X + 3 * X * Z * Z - b * Z * Z * Z)

/-! ## Related operations give related results -/

theorem rcbAdd_rel {α β : Type} {r : α → β → Prop} {m a s : α → α → α} {d : α → α} {m' a' s' : β → β → β}
    {d' : β → β} (hm : ∀ {x y X Y}, r x X → r y Y → r (m x y) (m' X Y))
    (ha : ∀ {x y X Y}, r x X → r y Y → r (a x y) (a' X Y)) (hs : ∀ {x y X Y}, r x X → r y Y → r (s x y) (s' X Y))
    (hd : ∀ {x X}, r x X → r (d x) (d' X)) {b x1 y1 z1 x2 y2 z2 : α} {B X1 Y1 Z1 X2 Y2 Z2 : β} (hb : r b B)
    (h1 : r x1 X1) (h2 : r y1 Y1) (h3 : r z1 Z1) (h4 : r x2 X2) (h5 : r y2 Y2) (h6 : r z2 Z2) :
    r (rcbAdd m a s d b x1 y1 z1 x2 y2 z2).1 (rcbAdd m' a' s' d' B X1 Y1 Z1 X2 Y2 Z2).1 ∧
    r (rcbAdd m a s d b x1 y1 z1 x2 y2 z2).2.1 (rcbAdd m' a' s' d' B X1 Y1 Z1 X2 Y2 Z2).2.1 ∧
    r (rcbAdd m a s d b x1 y1 z1 x2 y2 z2).2.2 (rcbAdd m' a' s' d' B X1 Y1 Z1 X2 Y2 Z2).2.2 := by
  have xx := hm h1 h4
  have yy := hm h2 h5
  have zz := hm h3 h6
  have xyP := hs (hm (ha h1 h2) (ha h4 h5)) (ha xx yy)
  have yzP := hs (hm (ha h2 h3) (ha h5 h6)) (ha yy zz)
  have xzP := hs (hm (ha h1 h3) (ha h4 h6)) (ha xx zz)
  have bzz := hs xzP (hm hb zz)
  have bzz3 := ha (hd bzz) bzz
  have yyM := hs yy bzz3
  have yyP := ha yy bzz3
  have zz3 := ha (hd zz) zz
  have bxz := hs (hm hb xzP) (ha zz3 xx)
  have bxz3 := ha (hd bxz) bxz
  have x3m := hs (ha (hd xx) xx) zz3
  exact ⟨hs (hm yyP xyP) (hm yzP bxz3), ha (hm yyP yyM) (hm x3m bxz3), ha (hm yyM yzP) (hm xyP x3m)⟩

theorem rcbDbl_rel {α β : Type} {r : α → β → Prop} {m a s : α → α → α} {d : α → α} {m' a' s' : β → β → β}
    {d' : β → β} (hm : ∀ {x y X Y}, r x X → r y Y → r (m x y) (m' X Y))
    (ha : ∀ {x y X Y}, r x X → r y Y → r (a x y) (a' X Y)) (hs : ∀ {x y X Y}, r x X → r y Y → r (s x y) (s' X Y))
    (hd : ∀ {x X}, r x X → r (d x) (d' X)) {b x y z : α} {B X Y Z : β} (hb : r b B) (h1 : r x X) (h2 : r y Y)
    (h3 : r z Z) :
    r (rcbDbl m a s d b x y z).1 (rcbDbl m' a' s' d' B X Y Z).1 ∧
    r (rcbDbl m a s d b x y z).2.1 (rcbDbl m' a' s' d' B X Y Z).2.1 ∧
    r (rcbDbl m a s d b x y z).2.2 (rcbDbl m' a' s' d' B X Y Z).2.2 := by
  have xx := hm h1 h1
  have yy := hm h2 h2
  have zz := hm h3 h3
  have xy2 := hd (hm h1 h2)
  have xz2 := hd (hm h1 h3)
  have bzz := hs (hm hb zz) xz2
  have bzz3 := ha (hd bzz) bzz
  have yymb := hs yy bzz3
  have yypb := ha yy bzz3
  have zz3 := ha (hd zz) zz
  have bxz2 := hs (hm hb xz2) (ha zz3 xx)
  have bxz6 := ha (hd bxz2) bxz2
  have x3m := hs (ha (hd xx) xx) zz3
  have yz2 := hd (hm h2 h3)
  exact ⟨hs (hm yymb xy2) (hm bxz6 yz2), ha (hm yypb yymb) (hm x3m bxz6), hd (hd (hm yz2 yy))⟩

/-! ## Montgomery operations -/

/-- The Montgomery product modulo `p`, where `Ri` is the inverse of the
Montgomery factor. -/
def mm (p Ri x y : Nat) : Nat := x * y * Ri % p

def ma (p x y : Nat) : Nat := (x + y) % p

def ms (p x y : Nat) : Nat := (x + p - y) % p

def md (p x : Nat) : Nat := (x + x) % p

/-- `x` is the Montgomery form of `X` modulo `p` with factor `R`. -/
def MRel (p R : Nat) (x : Nat) (X : Int) : Prop := x < p ∧ MEq p x (X * R)

theorem natCast_meq {p a b : Nat} (h : a % p = b) (hb : b < p) : MEq p (a : Int) b :=
  MEq.natCast.mpr (by rw [h, Nat.mod_eq_of_lt hb])

theorem mrel_mm {p R Ri : Nat} (hp : 1 < p) (hR : R * Ri % p = 1) {x y : Nat} {X Y : Int} (hx : MRel p R x X)
    (hy : MRel p R y Y) : MRel p R (mm p Ri x y) (X * Y) := by
  have h0 : 0 < p := by omega
  have hRR : MEq p ((R : Int) * Ri) 1 := by
    have := natCast_meq hR hp
    rwa [Int.natCast_mul, Int.natCast_one] at this
  refine ⟨Nat.mod_lt _ h0, ?_⟩
  unfold mm
  have e1 := natMod (x * y * Ri) p
  rw [Int.natCast_mul, Int.natCast_mul] at e1
  refine e1.trans (((hx.2.mul hy.2).mul (MEq.refl (Ri : Int))).trans ?_)
  refine (MEq.of_eq (show X * R * (Y * R) * Ri = X * Y * R * (R * Ri) by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm])).trans ?_
  have := (MEq.refl (X * Y * R)).mul hRR
  rwa [Int.mul_one] at this

theorem mrel_ma {p R : Nat} (hp : 0 < p) {x y : Nat} {X Y : Int} (hx : MRel p R x X) (hy : MRel p R y Y) :
    MRel p R (ma p x y) (X + Y) := by
  refine ⟨Nat.mod_lt _ hp, ?_⟩
  unfold ma
  have e1 := natMod (x + y) p
  rw [Int.natCast_add] at e1
  rw [Int.add_mul]
  exact e1.trans (hx.2.add hy.2)

theorem mrel_ms {p R : Nat} (hp : 0 < p) {x y : Nat} {X Y : Int} (hx : MRel p R x X) (hy : MRel p R y Y) :
    MRel p R (ms p x y) (X - Y) := by
  refine ⟨Nat.mod_lt _ hp, ?_⟩
  unfold ms
  have e1 := natMod (x + p - y) p
  rw [Int.ofNat_sub (by have := hy.1; omega), Int.natCast_add] at e1
  have e2 : MEq p ((x : Int) + p - y) ((x : Int) - y) := by
    rw [show (x : Int) + p - y = (x - y) + p * 1 by omega]
    exact MEq.add_mul_self 1
  rw [Int.sub_mul]
  exact e1.trans (e2.trans (hx.2.sub hy.2))

theorem mrel_md {p R : Nat} (hp : 0 < p) {x : Nat} {X : Int} (hx : MRel p R x X) : MRel p R (md p x) (X + X) := by
  refine ⟨Nat.mod_lt _ hp, ?_⟩
  unfold md
  have e1 := natMod (x + x) p
  rw [Int.natCast_add] at e1
  rw [Int.add_mul]
  exact e1.trans (hx.2.add hx.2)

/-- A coordinate below `p` is the Montgomery form of itself times `Ri`. -/
theorem mrel_unscale {p R Ri x : Nat} (hR : R * Ri % p = 1) (hx : x < p) :
    MRel p R x ((x * Ri % p : Nat) : Int) := by
  refine ⟨hx, ?_⟩
  have e : (x * Ri % p) * R % p = x := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm Ri, hR, Nat.mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt hx]
  have := natCast_meq e hx
  rw [Int.natCast_mul] at this
  exact this.symm

/-- The value a Montgomery form stands for, reduced below `p`. -/
theorem mrel_out {p R Ri o : Nat} {I : Int} (hp : 1 < p) (hR : R * Ri % p = 1) (h : MRel p R o I) :
    MEq p ((o * Ri % p : Nat) : Int) I := by
  have hRR : MEq p ((R : Int) * Ri) 1 := by
    have := natCast_meq hR hp
    rwa [Int.natCast_mul, Int.natCast_one] at this
  have e1 := natMod (o * Ri) p
  rw [Int.natCast_mul] at e1
  refine e1.trans ((h.2.mul (MEq.refl (Ri : Int))).trans ?_)
  have := (MEq.refl I).mul hRR
  rw [Int.mul_one, ← Int.mul_assoc] at this
  exact this

/-! ## Scaling a projective triple -/

theorem prep_lt {p : Nat} {P : Nat × Nat × Nat} {a : ECPoint} (h : PRep p P a) :
    P.1 < p ∧ P.2.1 < p ∧ P.2.2 < p := by
  cases a with
  | none => exact ⟨h.1, h.2.1, h.2.2.1⟩
  | some q => exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem mul_unit_ne {p k k' y : Nat} (hk : k * k' % p = 1) (hy : y < p) (h0 : y ≠ 0) : y * k % p ≠ 0 := by
  intro h
  have e : y * k * k' % p = y := by
    rw [Nat.mul_assoc, Nat.mul_mod, hk, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hy]
  rw [Nat.mul_mod, h, Nat.zero_mul, Nat.zero_mod] at e
  exact h0 e.symm

/-- Scaling all three coordinates by a unit modulo `p` doesn't change the
point a triple represents. -/
theorem prep_scale {p k k' X Y Z : Nat} {a : ECPoint} (hk : k * k' % p = 1) (h : PRep p (X, Y, Z) a) :
    PRep p (X * k % p, Y * k % p, Z * k % p) a := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with e | e
    · subst e
      cases a with
      | none => exact absurd h.1 (Nat.not_lt_zero _)
      | some q => exact absurd h.1 (Nat.not_lt_zero _)
    · exact e
  match a, h with
  | none, ⟨_, hY, _, hX0, hY0, hZ0⟩ =>
    refine ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp, ?_, mul_unit_ne hk hY hY0, ?_⟩
    · show X * k % p = 0
      rw [show X = 0 from hX0, Nat.zero_mul, Nat.zero_mod]
    · show Z * k % p = 0
      rw [show Z = 0 from hZ0, Nat.zero_mul, Nat.zero_mod]
  | some (x, y), ⟨_, _, hZ, hx, hy, hZ0, hX, hY⟩ =>
    refine ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp, hx, hy, mul_unit_ne hk hZ hZ0, ?_, ?_⟩
    · show MEq p ((X * k % p : Nat) : Int) (x * ((Z * k % p : Nat) : Int))
      have e1 := natMod (X * k) p
      have e2 := natMod (Z * k) p
      rw [Int.natCast_mul] at e1 e2
      refine e1.trans (((hX.mul (MEq.refl (k : Int)))).trans ?_)
      rw [Int.mul_assoc]
      exact (MEq.refl (x : Int)).mul e2.symm
    · show MEq p ((Y * k % p : Nat) : Int) (y * ((Z * k % p : Nat) : Int))
      have e1 := natMod (Y * k) p
      have e2 := natMod (Z * k) p
      rw [Int.natCast_mul] at e1 e2
      refine e1.trans (((hY.mul (MEq.refl (k : Int)))).trans ?_)
      rw [Int.mul_assoc]
      exact (MEq.refl (y : Int)).mul e2.symm

/-! ## The curve equation in projective coordinates -/

/-- A triple that represents a point on a curve with `a = -3` satisfies
`Y² Z - X³ + 3 X Z² - b Z³ ≡ 0`. -/
theorem curveE_zero {c : Curve} (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) {X Y Z : Nat} {a : ECPoint}
    (h : PRep c.p (X, Y, Z) a) (hc : EC.OnC c a) :
    MEq c.p ((Y : Int) * Y * Z - X * X * X + 3 * X * Z * Z - c.b * Z * Z * Z) 0 := by
  match a, h, hc with
  | none, ⟨_, _, _, hX0, _, hZ0⟩, _ =>
    have hX : X = 0 := hX0
    have hZ : Z = 0 := hZ0
    subst hX hZ
    simp only [Int.natCast_zero, Int.mul_zero, Int.sub_zero, Int.add_zero]
    exact MEq.refl 0
  | some (x, y), ⟨_, _, _, _, _, _, hX, hY⟩, ⟨_, _, he⟩ =>
    have ha : (c.a : Int) = (c.p : Int) - 3 := by rw [hca]; omega
    have e1 : MEq c.p ((Y : Int) * Y * Z - X * X * X + 3 * X * Z * Z - c.b * Z * Z * Z)
        ((y * Z) * (y * Z) * Z - (x * Z) * (x * Z) * (x * Z) + 3 * (x * Z) * Z * Z - c.b * Z * Z * Z) :=
      ((((hY.mul hY).mul (MEq.refl _)).sub ((hX.mul hX).mul hX)).add
        ((((MEq.refl 3).mul hX).mul (MEq.refl _)).mul (MEq.refl _))).sub (MEq.refl _)
    refine e1.trans ?_
    have e2 : ((y : Int) * Z) * (y * Z) * Z - (x * Z) * (x * Z) * (x * Z) + 3 * (x * Z) * Z * Z - c.b * Z * Z * Z =
        Z * Z * Z * (y * y - (x * x * x + c.a * x + c.b)) + c.p * (Z * Z * Z * x) := by
      rw [ha]
      simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    rw [e2]
    have e3 : MEq c.p (Z * Z * Z * ((y : Int) * y - (x * x * x + c.a * x + c.b))) 0 := by
      have := (MEq.refl ((Z : Int) * Z * Z)).mul (MEq.iff_sub.mp he)
      rwa [Int.mul_zero] at this
    have := e3.add (MEq.add_mul_self (p := c.p) (a := 0) ((Z : Int) * Z * Z * x))
    rwa [Int.zero_add, Int.zero_add] at this

/-! ## The Montgomery formulas -/

/-- **Algorithm 4 in Montgomery form represents the addition of `c`**,
given `RcbAddOk c`. -/
theorem mont_add_rep {c : Curve} (hp : 1 < c.p) {R Ri bM : Nat} (hR : R * Ri % c.p = 1) (hbl : bM < c.p)
    (hb : MEq c.p bM ((c.b : Int) * R)) (hadd : RcbAddOk c) {A B : Nat × Nat × Nat} {a b : ECPoint}
    (hA : PRep c.p A a) (hB : PRep c.p B b) (ha : EC.OnC c a) (hb' : EC.OnC c b) :
    PRep c.p (rcbAdd (mm c.p Ri) (ma c.p) (ms c.p) (md c.p) bM A.1 A.2.1 A.2.2 B.1 B.2.1 B.2.2) (c.add a b) := by
  obtain ⟨X1, Y1, Z1⟩ := A
  obtain ⟨X2, Y2, Z2⟩ := B
  have h0 : 0 < c.p := by omega
  have hRi : Ri * R % c.p = 1 := by rw [Nat.mul_comm]; exact hR
  have hA' := prep_scale hRi hA
  have hB' := prep_scale hRi hB
  have lA := prep_lt hA
  have lB := prep_lt hB
  obtain ⟨r1, r2, r3⟩ := rcbAdd_rel (r := MRel c.p R) (mrel_mm hp hR) (mrel_ma h0) (mrel_ms h0) (mrel_md h0)
    ⟨hbl, hb⟩ (mrel_unscale hR lA.1) (mrel_unscale hR lA.2.1) (mrel_unscale hR lA.2.2)
    (mrel_unscale hR lB.1) (mrel_unscale hR lB.2.1) (mrel_unscale hR lB.2.2)
  generalize rcbAdd (mm c.p Ri) (ma c.p) (ms c.p) (md c.p) bM X1 Y1 Z1 X2 Y2 Z2 = O at r1 r2 r3 ⊢
  obtain ⟨o1, o2, o3⟩ := O
  have hP := hadd _ _ (o1 * Ri % c.p, o2 * Ri % c.p, o3 * Ri % c.p) _ _ hA' hB' ha hb' (Nat.mod_lt _ h0)
    (Nat.mod_lt _ h0) (Nat.mod_lt _ h0) (mrel_out hp hR r1) (mrel_out hp hR r2) (mrel_out hp hR r3)
  have hs := prep_scale hR hP
  have e : ∀ o, o < c.p → o * Ri % c.p * R % c.p = o := fun o ho => by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, hRi, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt ho]
  rwa [e o1 r1.1, e o2 r2.1, e o3 r3.1] at hs

/-- **Algorithm 6 in Montgomery form represents the doubling on `c`**,
given `RcbAddOk c` and the doubling identity. -/
theorem mont_dbl_rep {c : Curve} (hp3 : 3 ≤ c.p) (hca : c.a = c.p - 3) {R Ri bM : Nat} (hR : R * Ri % c.p = 1)
    (hbl : bM < c.p) (hb : MEq c.p bM ((c.b : Int) * R)) (hadd : RcbAddOk c) (hpoly : RcbDblPoly)
    {A : Nat × Nat × Nat} {a : ECPoint} (hA : PRep c.p A a) (ha : EC.OnC c a) :
    PRep c.p (rcbDbl (mm c.p Ri) (ma c.p) (ms c.p) (md c.p) bM A.1 A.2.1 A.2.2) (c.add a a) := by
  obtain ⟨X1, Y1, Z1⟩ := A
  have hp : 1 < c.p := by omega
  have h0 : 0 < c.p := by omega
  have hRi : Ri * R % c.p = 1 := by rw [Nat.mul_comm]; exact hR
  have hA' := prep_scale hRi hA
  have lA := prep_lt hA
  obtain ⟨r1, r2, r3⟩ := rcbDbl_rel (r := MRel c.p R) (mrel_mm hp hR) (mrel_ma h0) (mrel_ms h0) (mrel_md h0)
    ⟨hbl, hb⟩ (mrel_unscale hR lA.1) (mrel_unscale hR lA.2.1) (mrel_unscale hR lA.2.2)
  obtain ⟨q1, q2, q3⟩ := hpoly c.b ((X1 * Ri % c.p : Nat) : Int) ((Y1 * Ri % c.p : Nat) : Int)
    ((Z1 * Ri % c.p : Nat) : Int)
  have hE := curveE_zero hp3 hca hA' ha
  generalize rcbDbl (mm c.p Ri) (ma c.p) (ms c.p) (md c.p) bM X1 Y1 Z1 = O at r1 r2 r3 ⊢
  obtain ⟨o1, o2, o3⟩ := O
  have m1 := mrel_out hp hR r1
  have m2 := mrel_out hp hR r2
  have m3 := mrel_out hp hR r3
  rw [q1] at m1
  rw [q2] at m2
  rw [q3] at m3
  have m3' := m3.trans ((MEq.refl _).add ((MEq.refl _).mul hE))
  rw [Int.mul_zero, Int.add_zero] at m3'
  have hP := hadd _ _ (o1 * Ri % c.p, o2 * Ri % c.p, o3 * Ri % c.p) _ _ hA' hA' ha ha (Nat.mod_lt _ h0)
    (Nat.mod_lt _ h0) (Nat.mod_lt _ h0) m1 m2 m3'
  have hs := prep_scale hR hP
  have e : ∀ o, o < c.p → o * Ri % c.p * R % c.p = o := fun o ho => by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, hRi, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt ho]
  rwa [e o1 r1.1, e o2 r2.1, e o3 r3.1] at hs

end C3.Models
