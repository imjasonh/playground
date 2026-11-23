import C3BootProofs.Models.EcdsaGroup

/-!
# The interleaved wNAF main loop, for any point representation

`gLoop` is the compiled double-scalar loop with the point operations as
parameters; `mlLoop2` (P-256) and `mlLoop` (P-384) are instances. Given that
the operations represent the curve's addition, doubling, and negation
(`LoopOps`), `gLoop_spec` shows the loop ends at `u G + v Q`, where `u` and
`v` are the signed sums of the digits.
-/

namespace C3.Models

section Loop

variable {P : Type} (addF : P → P → P) (negF : P → P) (dblF : P → P) (K : Nat)

/-- What the loop does with the digit byte `b` of a pair whose table is `T`. -/
def gAdd (T : Nat → P) (acc : P) (b : Nat) : Option (Option P) :=
  if b = 0 then some none
  else if b < 128 then (if 16 ≤ b then none else some (some (addF acc (T (b / 2)))))
  else if b = 128 ∨ 8 ≤ (256 - b) / 2 then none
  else some (some (addF acc (negF (T ((256 - b) / 2)))))

/-- The step for one pair at position `k`. -/
def gPair (T : Nat → P) (D : List Nat) (k : Nat) (st : P × Bool) : Option (P × Bool) :=
  if K < k + 1 then some st
  else match gAdd addF negF T st.1 (D.getD k 0) with
    | none => none
    | some none => some st
    | some (some a) => some (a, true)

/-- One position of the main loop. -/
def gIter (T0 T1 : Nat → P) (D0 D1 : List Nat) (k : Nat) (st : P × Bool) : Option (P × Bool) :=
  (gPair addF negF K T0 D0 k (if st.2 then dblF st.1 else st.1, st.2)).bind (gPair addF negF K T1 D1 k)

/-- The main loop from position `k - 1` down to 0. -/
def gLoop (T0 T1 : Nat → P) (D0 D1 : List Nat) : Nat → P × Bool → Option (P × Bool)
  | 0, st => some st
  | k + 1, st => (gIter addF negF dblF K T0 T1 D0 D1 k st).bind (gLoop T0 T1 D0 D1 k)

end Loop

/-- The signed digit a byte holds. -/
def dval (b : Nat) : Int := if b < 128 then b else (b : Int) - 256

/-- A digit byte the loop accepts: zero, or an odd digit of magnitude below
16. -/
def DigOk (b : Nat) : Prop := b = 0 ∨ (b % 2 = 1 ∧ b < 16) ∨ (b % 2 = 1 ∧ 241 ≤ b ∧ b < 256)

/-- The signed sum of the first `k` digits, each weighted by its position. -/
def dsum (D : List Nat) : Nat → Int
  | 0 => 0
  | k + 1 => dval (D.getD k 0) * 2 ^ k + dsum D k

/-- The point operations represent the curve's group law. -/
structure LoopOps {P : Type} (c : Curve) (rep : P → ECPoint → Prop) (addF : P → P → P) (negF : P → P)
    (dblF : P → P) (idP : P) : Prop where
  add : ∀ A B a b, rep A a → rep B b → EC.OnC c a → EC.OnC c b → rep (addF A B) (c.add a b)
  dbl : ∀ A a, rep A a → EC.OnC c a → rep (dblF A) (c.add a a)
  neg : ∀ A a, rep A a → rep (negF A) (EC.neg c a)
  id : rep idP none
  uniq : ∀ a, rep idP a → a = none

section Spec

variable {c : Curve} (hp : IsPrime c.p) (hc : EC.AddClosed c) (ha : EC.AddAssoc c)
variable {P : Type} {rep : P → ECPoint → Prop} {addF : P → P → P} {negF : P → P} {dblF : P → P} {idP : P}

local notation "GG" => EC.grp c hp hc ha

/-- `a g0 + b g1`. -/
def lc (g0 g1 : EC.Pts c) (a b : Int) : EC.Pts c := (GG).add ((GG).zs a g0) ((GG).zs b g1)

theorem grp_add_val (x y : EC.Pts c) : ((GG).add x y).1 = c.add x.1 y.1 := rfl

theorem grp_neg_val (x : EC.Pts c) : ((GG).neg x).1 = EC.neg c x.1 := rfl

theorem tbl_rep (L : LoopOps c rep addF negF dblF idP) {T : Nat → P} {Pt : P} {g : EC.Pts c}
    (h0 : T 0 = Pt) (hs : ∀ j, T (j + 1) = addF (T j) (dblF Pt)) (hg : rep Pt g.1) :
    ∀ j : Nat, rep (T j) ((GG).zs (2 * (j : Int) + 1) g).1 := by
  intro j
  induction j with
  | zero => rw [h0]; simpa [AbGrp.zs_one] using hg
  | succ j ih =>
    rw [hs]
    have hd : rep (dblF Pt) ((GG).zs 2 g).1 := by
      have := L.dbl _ _ hg g.2
      rwa [show (2 : Int) = 2 * 1 by rfl, AbGrp.zs_two_mul, AbGrp.zs_one]
    have := L.add _ _ _ _ ih hd (Subtype.property _) (Subtype.property _)
    rw [← grp_add_val hp hc ha, ← AbGrp.zs_add] at this
    rwa [show 2 * ((j + 1 : Nat) : Int) + 1 = 2 * (j : Int) + 1 + 2 by omega]

/-- The flag invariant: an unmarked accumulator is the image's identity. -/
def FlagOk (idP : P) (st : P × Bool) : Prop := st.2 = false → st.1 = idP

theorem gAdd_spec (L : LoopOps c rep addF negF dblF idP) {T : Nat → P} {g : EC.Pts c}
    (hT : ∀ j : Nat, j < 8 → rep (T j) ((GG).zs (2 * (j : Int) + 1) g).1)
    {acc : P} {X : EC.Pts c} (hX : rep acc X.1) {b : Nat} (hb : DigOk b) :
    (b = 0 ∧ gAdd addF negF T acc b = some none) ∨
      ∃ A, gAdd addF negF T acc b = some (some A) ∧ rep A ((GG).add X ((GG).zs (dval b) g)).1 := by
  rcases hb with rfl | ⟨hodd, hlt⟩ | ⟨hodd, hge, hlt⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · have hb0 : b ≠ 0 := by omega
    refine Or.inr ⟨_, by
      unfold gAdd; rw [ite_eq_right hb0, ite_eq_left (by omega : b < 128), ite_eq_right (by omega)], ?_⟩
    have := L.add _ _ _ _ hX (hT (b / 2) (by omega)) X.2 (Subtype.property _)
    rw [← grp_add_val hp hc ha] at this
    rwa [show dval b = 2 * ((b / 2 : Nat) : Int) + 1 by unfold dval; rw [ite_eq_left (by omega)]; omega]
  · have hb0 : b ≠ 0 := by omega
    refine Or.inr ⟨_, by
      unfold gAdd
      rw [ite_eq_right hb0, ite_eq_right (by omega : ¬ b < 128), ite_eq_right (by omega)], ?_⟩
    have hj : (256 - b) / 2 < 8 := by omega
    have hn := L.neg _ _ (hT _ hj)
    rw [← grp_neg_val hp hc ha, ← AbGrp.zs_neg] at hn
    have := L.add _ _ _ _ hX hn X.2 (Subtype.property _)
    rw [← grp_add_val hp hc ha] at this
    rwa [show dval b = -(2 * (((256 - b) / 2 : Nat) : Int) + 1) by
      unfold dval; rw [ite_eq_right (by omega)]; omega]

theorem gPair_spec (L : LoopOps c rep addF negF dblF idP) {K : Nat} {T : Nat → P} {g : EC.Pts c}
    (hT : ∀ j : Nat, j < 8 → rep (T j) ((GG).zs (2 * (j : Int) + 1) g).1)
    {D : List Nat} {k : Nat} (hk : k < K) (hD : DigOk (D.getD k 0))
    {st : P × Bool} {X : EC.Pts c} (hX : rep st.1 X.1) (hF : FlagOk idP st) :
    ∃ st', gPair addF negF K T D k st = some st' ∧
      rep st'.1 ((GG).add X ((GG).zs (dval (D.getD k 0)) g)).1 ∧ FlagOk idP st' := by
  unfold gPair
  rw [ite_eq_right (by omega)]
  rcases gAdd_spec hp hc ha L hT hX hD with ⟨h0, he⟩ | ⟨A, he, hA⟩
  · rw [he]
    refine ⟨st, rfl, ?_, hF⟩
    rw [h0]; show rep st.1 ((GG).add X (GG).zero).1; rw [AbGrp.add_zero]; exact hX
  · rw [he]; exact ⟨(A, true), rfl, hA, fun h => by cases h⟩

theorem lc_add_left (g0 g1 : EC.Pts c) (a b d : Int) :
    lc hp hc ha g0 g1 (a + d) b = (GG).add (lc hp hc ha g0 g1 a b) ((GG).zs d g0) := by
  unfold lc
  rw [AbGrp.zs_add, (GG).add_assoc, (GG).add_comm ((GG).zs d g0), ← (GG).add_assoc]

theorem lc_add_right (g0 g1 : EC.Pts c) (a b d : Int) :
    lc hp hc ha g0 g1 a (b + d) = (GG).add (lc hp hc ha g0 g1 a b) ((GG).zs d g1) := by
  unfold lc
  rw [AbGrp.zs_add, (GG).add_assoc]

theorem lc_two (g0 g1 : EC.Pts c) (a b : Int) :
    lc hp hc ha g0 g1 (2 * a) (2 * b) = (GG).add (lc hp hc ha g0 g1 a b) (lc hp hc ha g0 g1 a b) := by
  unfold lc
  rw [AbGrp.zs_two_mul, AbGrp.zs_two_mul]
  generalize (GG).zs a g0 = x
  generalize (GG).zs b g1 = y
  rw [(GG).add_assoc, (GG).add_assoc]
  congr 1
  rw [← (GG).add_assoc x y y, (GG).add_comm ((GG).add x y) y]

/-- The doubling at the top of a position. -/
theorem dbl_spec (L : LoopOps c rep addF negF dblF idP) {g0 g1 : EC.Pts c} {a b : Int} {st : P × Bool}
    (hX : rep st.1 (lc hp hc ha g0 g1 a b).1) (hF : FlagOk idP st) :
    rep (if st.2 then dblF st.1 else st.1) (lc hp hc ha g0 g1 (2 * a) (2 * b)).1 := by
  rw [lc_two]
  cases h : st.2
  · have e := hF h
    rw [e] at hX ⊢
    have hn := L.uniq _ hX
    have : lc hp hc ha g0 g1 a b = (GG).zero := Subtype.ext hn
    rw [this, (GG).zero_add]; exact L.id
  · exact L.dbl _ _ hX (Subtype.property _)

theorem gLoop_spec (L : LoopOps c rep addF negF dblF idP) {K : Nat} {T0 T1 : Nat → P} {g0 g1 : EC.Pts c}
    (hT0 : ∀ j : Nat, j < 8 → rep (T0 j) ((GG).zs (2 * (j : Int) + 1) g0).1)
    (hT1 : ∀ j : Nat, j < 8 → rep (T1 j) ((GG).zs (2 * (j : Int) + 1) g1).1)
    {D0 D1 : List Nat} (hD0 : ∀ k, DigOk (D0.getD k 0)) (hD1 : ∀ k, DigOk (D1.getD k 0)) :
    ∀ k, k ≤ K → ∀ (st : P × Bool) (a b : Int), rep st.1 (lc hp hc ha g0 g1 a b).1 → FlagOk idP st →
      ∃ st', gLoop addF negF dblF K T0 T1 D0 D1 k st = some st' ∧
        rep st'.1 (lc hp hc ha g0 g1 (a * 2 ^ k + dsum D0 k) (b * 2 ^ k + dsum D1 k)).1 ∧ FlagOk idP st' := by
  intro k
  induction k with
  | zero => intro _ st a b hX hF; exact ⟨st, rfl, by simpa [dsum] using hX, hF⟩
  | succ k ih =>
    intro hk st a b hX hF
    have h1 := dbl_spec hp hc ha L hX hF
    have hF1 : FlagOk idP (if st.2 then dblF st.1 else st.1, st.2) := by
      intro h; simp only at h; rw [h]; exact hF h
    obtain ⟨st1, e1, r1, f1⟩ := gPair_spec hp hc ha L (K := K) (k := k) hT0 (by omega) (hD0 k) h1 hF1
    rw [← lc_add_left] at r1
    obtain ⟨st2, e2, r2, f2⟩ := gPair_spec hp hc ha L (K := K) (k := k) hT1 (by omega) (hD1 k) r1 f1
    rw [← lc_add_right] at r2
    obtain ⟨st3, e3, r3, f3⟩ := ih (by omega) st2 _ _ r2 f2
    refine ⟨st3, ?_, ?_, f3⟩
    · show (gIter addF negF dblF K T0 T1 D0 D1 k st).bind _ = _
      unfold gIter; rw [e1]; simp only [Option.bind_some]; rw [e2]; simp only [Option.bind_some]; exact e3
    · have ea : (2 * a + dval (D0.getD k 0)) * 2 ^ k + dsum D0 k = a * 2 ^ (k + 1) + dsum D0 (k + 1) := by
        simp only [dsum, Int.pow_succ, Int.add_mul, Int.mul_comm 2 a, Int.mul_assoc, Int.mul_comm 2 ((2 : Int) ^ k)]
        omega
      have eb : (2 * b + dval (D1.getD k 0)) * 2 ^ k + dsum D1 k = b * 2 ^ (k + 1) + dsum D1 (k + 1) := by
        simp only [dsum, Int.pow_succ, Int.add_mul, Int.mul_comm 2 b, Int.mul_assoc, Int.mul_comm 2 ((2 : Int) ^ k)]
        omega
      rwa [ea, eb] at r3

end Spec

end C3.Models
