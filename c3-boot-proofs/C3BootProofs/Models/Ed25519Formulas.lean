import C3BootProofs.Models.Ed25519Ladder
import C3BootProofs.Models.Ed25519FeArith
import C3BootProofs.Models.Ed25519FormulasAlg

/-!
# The Ed25519 limb formulas, from the primality of `p`

`edFormulas` proves `EdFormulas` from `IsPrime Ed25519.p`. The limb lemmas
in `Ed25519FeArith.lean` give each `mulL`, `sqL`, `sq2L`, `addL`, and `subL`
its value modulo `p` and its limb bound, and the theorems in
`Ed25519FormulasAlg.lean` turn those values into the representations.

The bounds that `PRep`, `ERep`, `CRep`, and `NRep` state are the ones the
formulas need: `mul` takes limbs below 3 · 2^26, `square` below 2^27,
`square2` below 2^26, and `sub` below 2^27, and each returns limbs below
2^26. The largest sum is the Niels formulas' `2ZZ + TT`, below 3 · 2^26.
-/

namespace C3.RV32.EdM

open C3.Models

local notation "𝔭" => ((Ed25519.p : Nat) : Int)
local notation "𝔡" => ((Ed25519.d : Nat) : Int)

theorem getElem!_getD' (l : List Nat) (i : Nat) : l[i]! = l.getD i 0 := by
  rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]; rfl

theorem mulL_ok {a b : List Nat} (ha : Lim (3 * 2 ^ 26) a) (hb : Lim (3 * 2 ^ 26) b) :
    Lim (2 ^ 26) (mulL a b) ∧ fv (mulL a b) = fv a * fv b % Ed25519.p :=
  feMulSpec_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ha.2 0 (by decide)) (ha.2 1 (by decide))
    (ha.2 2 (by decide)) (ha.2 3 (by decide)) (ha.2 4 (by decide)) (ha.2 5 (by decide)) (ha.2 6 (by decide))
    (ha.2 7 (by decide)) (ha.2 8 (by decide)) (ha.2 9 (by decide)) (hb.2 0 (by decide)) (hb.2 1 (by decide))
    (hb.2 2 (by decide)) (hb.2 3 (by decide)) (hb.2 4 (by decide)) (hb.2 5 (by decide)) (hb.2 6 (by decide))
    (hb.2 7 (by decide)) (hb.2 8 (by decide)) (hb.2 9 (by decide))

theorem sqL_ok {l : List Nat} (h : Lim (2 ^ 27) l) :
    Lim (2 ^ 26) (sqL l) ∧ fv (sqL l) = fv l * fv l % Ed25519.p := by
  have e := feSq_ok (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) (l.getD 4 0) (l.getD 5 0) (l.getD 6 0)
    (l.getD 7 0) (l.getD 8 0) (l.getD 9 0) (h.2 0 (by decide)) (h.2 1 (by decide)) (h.2 2 (by decide))
    (h.2 3 (by decide)) (h.2 4 (by decide)) (h.2 5 (by decide)) (h.2 6 (by decide)) (h.2 7 (by decide))
    (h.2 8 (by decide)) (h.2 9 (by decide))
  unfold sqL feSquareSpec
  simp only [getElem!_getD'] at e ⊢
  exact e

theorem sq2L_ok {l : List Nat} (h : Lim (2 ^ 26) l) :
    Lim (2 ^ 26) (sq2L l) ∧ fv (sq2L l) = 2 * (fv l * fv l) % Ed25519.p := by
  have e := feSq2_ok (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) (l.getD 4 0) (l.getD 5 0) (l.getD 6 0)
    (l.getD 7 0) (l.getD 8 0) (l.getD 9 0) (h.2 0 (by decide)) (h.2 1 (by decide)) (h.2 2 (by decide))
    (h.2 3 (by decide)) (h.2 4 (by decide)) (h.2 5 (by decide)) (h.2 6 (by decide)) (h.2 7 (by decide))
    (h.2 8 (by decide)) (h.2 9 (by decide))
  unfold sq2L dblRed
  simp only [getElem!_getD'] at e ⊢
  exact e

theorem addL_ok {a b : List Nat} {A B : Nat} (ha : Lim A a) (hb : Lim B b) (hAB : A + B ≤ 2 ^ 32) :
    Lim (A + B) (addL a b) ∧ fv (addL a b) = (fv a + fv b) % Ed25519.p := by
  unfold addL
  simp only [getElem!_getD']
  exact feAdd_ok ha hb hAB

theorem subL_ok {a b : List Nat} (ha : Lim (2 ^ 27) a) (hb : Lim (2 ^ 27) b) :
    Lim (2 ^ 26) (subL a b) ∧ fv (subL a b) = (fv a + Ed25519.p - fv b) % Ed25519.p := by
  unfold subL feSubSpec
  simp only [getElem!_getD']
  exact feSub_ok ha hb

theorem mq {r e : Nat} (h : r = e % Ed25519.p) : MEq Ed25519.p r e := by
  rw [h]; exact natMod _ _

theorem mq_sub {r a b : Nat} (hb : b < Ed25519.p) (h : r = (a + Ed25519.p - b) % Ed25519.p) :
    MEq Ed25519.p r ((a : Int) - b) := by
  have e : ((a + Ed25519.p - b : Nat) : Int) = a + 𝔭 - b := by omega
  have m := mq h
  rw [e] at m
  exact sm (by ring_mod [(ms m) * 1, p_sub * 1])

theorem mq_nat {a b : Nat} (h : a % Ed25519.p = b % Ed25519.p) : MEq Ed25519.p a b := MEq.natCast.mpr h

theorem eq_of_mq {r e : Nat} (hr : r < Ed25519.p) (h : MEq Ed25519.p r e) : r = e % Ed25519.p :=
  meq_eq (h.trans (natMod e Ed25519.p).symm) hr (Nat.mod_lt _ p_pos)

theorem ne_fv {l : List Nat} (h : fv l ≠ 0) : ¬ MEq Ed25519.p (fv l) 0 := by
  intro hm
  have hl := fv_lt l
  unfold MEq at hm
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.zero_emod] at hm
  omega

theorem fv_ne {l : List Nat} (h : ¬ MEq Ed25519.p (fv l) 0) : fv l ≠ 0 := by
  intro h0
  apply h
  rw [h0]
  rfl

theorem mq_mul {r a b : Nat} (h : r = a * b % Ed25519.p) : MEq Ed25519.p r ((a : Int) * b) := by
  have m := mq h
  push_cast at m
  exact m

theorem mq_add {r a b : Nat} (h : r = (a + b) % Ed25519.p) : MEq Ed25519.p r ((a : Int) + b) := by
  have m := mq h
  push_cast at m
  exact m

theorem eq_mul {r a b : Nat} (hr : r < Ed25519.p) (h : MEq Ed25519.p r ((a : Int) * b)) : r = a * b % Ed25519.p :=
  eq_of_mq hr (by push_cast; exact h)

theorem mq_xy {X Y Z T : Nat} (h : X * Y % Ed25519.p = Z * T % Ed25519.p) :
    MEq Ed25519.p ((X : Int) * Y) ((Z : Int) * T) := by
  have m := mq_nat h
  push_cast at m
  exact m

theorem edDbl_ok (hp : IsPrime Ed25519.p) : EdDblOK := by
  rintro ⟨X, Y, Z⟩ ⟨x, y⟩ hP ⟨lX, lY, lZ, hZ, hX, hY⟩
  obtain ⟨hu, hv, n1, n2⟩ := add_char hp (x, y) (x, y) hP hP
  have c := curveI_of hP
  dsimp only at hu hv n1 n2 c lX lY lZ hZ hX hY ⊢
  obtain ⟨lXX, eXX⟩ := sqL_ok (lX.mono (by decide))
  obtain ⟨lYY, eYY⟩ := sqL_ok (lY.mono (by decide))
  obtain ⟨lZZ, eZZ⟩ := sq2L_ok lZ
  obtain ⟨lXY, eXY⟩ := addL_ok lX lY (by decide)
  obtain ⟨lS, eS⟩ := sqL_ok (lXY.mono (by decide))
  obtain ⟨lA, eA⟩ := addL_ok lYY lXX (by decide)
  obtain ⟨lB, eB⟩ := subL_ok (lYY.mono (by decide)) (lXX.mono (by decide))
  obtain ⟨lX', eX'⟩ := subL_ok (lS.mono (by decide)) (lA.mono (by decide))
  obtain ⟨lT', eT'⟩ := subL_ok (lZZ.mono (by decide)) (lB.mono (by decide))
  have mXY := mq_add eXY
  have mS0 := mq_mul eS
  have mS : MEq Ed25519.p (fv (sqL (addL X Y))) ((((fv X : Nat) : Int) + fv Y) * (((fv X : Nat) : Int) + fv Y)) :=
    sm (by ring_mod [(ms mS0) * 1, (ms mXY) * (((fv (addL X Y) : Nat) : Int) + fv X + fv Y)])
  have mZZ : MEq Ed25519.p (fv (sq2L Z)) (2 * (((fv Z : Nat) : Int) * fv Z)) := by
    have m := mq eZZ
    push_cast at m
    exact m
  obtain ⟨m1, m2, m3, m4⟩ := dbl_alg hp c hu hv n1 n2 (mq_mul hX) (mq_mul hY) (ne_fv hZ) (mq_mul eXX)
    (mq_mul eYY) mZZ mS (mq_add eA) (mq_sub (fv_lt _) eB) (mq_sub (fv_lt _) eX') (mq_sub (fv_lt _) eT')
  unfold edDoubleSpec
  exact ⟨lX'.mono (by decide), lA.mono (by decide), lB.mono (by decide), lT'.mono (by decide), fv_ne m3,
    fv_ne m4, eq_mul (fv_lt _) m1, eq_mul (fv_lt _) m2⟩

theorem edExt_ok (hp : IsPrime Ed25519.p) : EdExtOK := by
  rintro ⟨X, Y, Z, T⟩ ⟨x, y⟩ _ ⟨lX, lY, lZ, lT, hZ, hT, hX, hY⟩
  dsimp only at lX lY lZ lT hZ hT hX hY ⊢
  obtain ⟨l1, e1⟩ := mulL_ok lX lT
  obtain ⟨l2, e2⟩ := mulL_ok lY lZ
  obtain ⟨l3, e3⟩ := mulL_ok lZ lT
  obtain ⟨l4, e4⟩ := mulL_ok lX lY
  obtain ⟨m3, m1, m2, m4⟩ := ext_alg hp (mq_mul hX) (mq_mul hY) (ne_fv hZ) (ne_fv hT) (mq_mul e1) (mq_mul e2)
    (mq_mul e3) (mq_mul e4)
  unfold extL
  refine ⟨l1, l2, l3, l4, fv_ne m3, eq_mul (fv_lt _) m1, eq_mul (fv_lt _) m2, ?_⟩
  have m := m4
  rw [← Int.natCast_mul, ← Int.natCast_mul] at m
  exact MEq.natCast.mp m

theorem edProj_ok (hp : IsPrime Ed25519.p) : EdProjOK := by
  rintro ⟨X, Y, Z, T⟩ ⟨x, y⟩ _ ⟨lX, lY, lZ, lT, hZ, hT, hX, hY⟩
  dsimp only at lX lY lZ lT hZ hT hX hY ⊢
  obtain ⟨l1, e1⟩ := mulL_ok lX lT
  obtain ⟨l2, e2⟩ := mulL_ok lY lZ
  obtain ⟨l3, e3⟩ := mulL_ok lZ lT
  obtain ⟨l4, e4⟩ := mulL_ok lX lY
  obtain ⟨m3, m1, m2, -⟩ := ext_alg hp (mq_mul hX) (mq_mul hY) (ne_fv hZ) (ne_fv hT) (mq_mul e1) (mq_mul e2)
    (mq_mul e3) (mq_mul e4)
  unfold projC
  exact ⟨l1, l2, l3, fv_ne m3, eq_mul (fv_lt _) m1, eq_mul (fv_lt _) m2⟩

/-- `NRep`'s second coordinate, `(y + p - x) Z`, modulo `p`. -/
theorem mq_ymx {r y x Z : Nat} (hx : x < Ed25519.p) (h : r = (y + Ed25519.p - x) * Z % Ed25519.p) :
    MEq Ed25519.p r (((y : Int) - x) * Z) := by
  have m := mq h
  rw [Int.natCast_mul, (show ((y + Ed25519.p - x : Nat) : Int) = y + 𝔭 - x by omega)] at m
  exact sm (by ring_mod [(ms m) * 1, p_sub * (Z : Int)])

/-- `NRep`'s fourth coordinate, `2 d x y Z`, modulo `p`. -/
theorem mq_dxy {r x y Z : Nat} (h : r = 2 * Ed25519.d * x % Ed25519.p * y % Ed25519.p * Z % Ed25519.p) :
    MEq Ed25519.p r (2 * 𝔡 * x * y * Z) := by
  rw [mod_mul_mod'' (2 * Ed25519.d * x) y, mod_mul_mod'' (2 * Ed25519.d * x * y) Z] at h
  have m := mq h
  push_cast at m
  exact m

theorem edNiels_ok (hp : IsPrime Ed25519.p) : EdNielsOK := by
  rintro d2 ⟨X, Y, Z, T⟩ ⟨x, y⟩ ld hd hP ⟨lX, lY, lZ, lT, hZ, hX, hY, hXY⟩
  dsimp only at lX lY lZ lT hZ hX hY hXY hP ⊢
  obtain ⟨l1, e1⟩ := addL_ok lY lX (by decide)
  obtain ⟨l2, e2⟩ := subL_ok (lY.mono (by decide)) (lX.mono (by decide))
  obtain ⟨l4, e4⟩ := mulL_ok (lT.mono (by decide)) (ld.mono (by decide))
  have hD : MEq Ed25519.p (fv d2) (2 * 𝔡) := by
    have m := mq hd
    push_cast at m
    exact m
  obtain ⟨m1, m2, m4⟩ := niels_alg hp (mq_mul hX) (mq_mul hY) (mq_xy hXY) (ne_fv hZ) hD (mq_add e1)
    (mq_sub (fv_lt _) e2) (mq_mul e4)
  unfold nielsL
  refine ⟨l1.mono (by decide), l2.mono (by decide), lZ.mono (by decide), l4.mono (by decide), hZ,
    eq_of_mq (fv_lt _) (by push_cast; exact m1), eq_of_mq (fv_lt _) ?_, ?_⟩
  · have hx : x < Ed25519.p := hP.1
    rw [Int.natCast_mul, (show ((y + Ed25519.p - x : Nat) : Int) = y + 𝔭 - x by omega)]
    exact sm (by ring_mod [(ms m2) * 1, p_sub * (-((fv Z : Nat) : Int))])
  · rw [mod_mul_mod'' (2 * Ed25519.d * x) y, mod_mul_mod'' (2 * Ed25519.d * x * y) (fv Z)]
    exact eq_of_mq (fv_lt _) (by push_cast; exact m4)

theorem edAddN_ok (hp : IsPrime Ed25519.p) : EdAddNOK := by
  rintro ⟨X₁, Y₁, Z₁, T₁⟩ ⟨N₁, N₂, Z₂, N₄⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hP hQ ⟨lX, lY, lZ, lT, hZ, hX, hY, hXY⟩
    ⟨lN₁, lN₂, lZ₂, lN₄, hZ₂, hN₁, hN₂, hN₄⟩
  obtain ⟨hu, hv, n1, n2⟩ := add_char hp (x₁, y₁) (x₂, y₂) hP hQ
  dsimp only at hu hv n1 n2 lX lY lZ lT hZ hX hY hXY lN₁ lN₂ lZ₂ lN₄ hZ₂ hN₁ hN₂ hN₄ hQ ⊢
  obtain ⟨la, ea⟩ := addL_ok lY lX (by decide)
  obtain ⟨ls, es⟩ := subL_ok (lY.mono (by decide)) (lX.mono (by decide))
  obtain ⟨lPP, ePP⟩ := mulL_ok (la.mono (by decide)) lN₁
  obtain ⟨lMM, eMM⟩ := mulL_ok (ls.mono (by decide)) lN₂
  obtain ⟨lTT, eTT⟩ := mulL_ok (lT.mono (by decide)) lN₄
  obtain ⟨lZZ, eZZ⟩ := mulL_ok (lZ.mono (by decide)) lZ₂
  obtain ⟨lz, ez⟩ := addL_ok lZZ lZZ (by decide)
  obtain ⟨lXc, eXc⟩ := subL_ok (lPP.mono (by decide)) (lMM.mono (by decide))
  obtain ⟨lYc, eYc⟩ := addL_ok lPP lMM (by decide)
  obtain ⟨lZc, eZc⟩ := addL_ok lz lTT (by decide)
  obtain ⟨lTc, eTc⟩ := subL_ok (lz.mono (by decide)) (lTT.mono (by decide))
  have hT₁ := t_of_rep hp (mq_mul hX) (mq_mul hY) (mq_xy hXY) (ne_fv hZ)
  have mN₁ : MEq Ed25519.p (fv N₁) (((y₂ : Int) + x₂) * fv Z₂) := by
    have m := mq hN₁
    push_cast at m
    exact m
  obtain ⟨m1, m2, m3, m4⟩ := addN_alg hp hu hv n1 n2 (mq_mul hX) (mq_mul hY) hT₁ (ne_fv hZ) mN₁
    (mq_ymx hQ.1 hN₂) (mq_dxy hN₄) (ne_fv hZ₂) (mq_add ea) (mq_sub (fv_lt _) es) (mq_mul ePP) (mq_mul eMM)
    (mq_mul eTT) (mq_mul eZZ) (mq_add ez) (mq_sub (fv_lt _) eXc) (mq_add eYc) (mq_add eZc)
    (mq_sub (fv_lt _) eTc)
  unfold addNL
  exact ⟨lXc.mono (by decide), lYc.mono (by decide), lZc.mono (by decide), lTc.mono (by decide), fv_ne m3,
    fv_ne m4, eq_mul (fv_lt _) m1, eq_mul (fv_lt _) m2⟩

theorem edSubN_ok (hp : IsPrime Ed25519.p) : EdSubNOK := by
  rintro ⟨X₁, Y₁, Z₁, T₁⟩ ⟨N₁, N₂, Z₂, N₄⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hP hQ ⟨lX, lY, lZ, lT, hZ, hX, hY, hXY⟩
    ⟨lN₁, lN₂, lZ₂, lN₄, hZ₂, hN₁, hN₂, hN₄⟩
  obtain ⟨hu, hv, n1, n2⟩ := add_char hp (x₁, y₁) (neg (x₂, y₂)) hP (onCurve_neg _ hQ)
  have hneg : ((((Ed25519.p - x₂) % Ed25519.p : Nat) : Int) + x₂) % 𝔭 = 0 := by
    rw [Int.natCast_emod, Int.natCast_sub (Nat.le_of_lt hQ.1)]
    ring_mod [(emod_sub (𝔭 - (x₂ : Int))) * 1, p_sub * 1]
  unfold neg at hu hv n1 n2 ⊢
  dsimp only at hu hv n1 n2 lX lY lZ lT hZ hX hY hXY lN₁ lN₂ lZ₂ lN₄ hZ₂ hN₁ hN₂ hN₄ hQ ⊢
  obtain ⟨la, ea⟩ := addL_ok lY lX (by decide)
  obtain ⟨ls, es⟩ := subL_ok (lY.mono (by decide)) (lX.mono (by decide))
  obtain ⟨lPP, ePP⟩ := mulL_ok (la.mono (by decide)) lN₂
  obtain ⟨lMM, eMM⟩ := mulL_ok (ls.mono (by decide)) lN₁
  obtain ⟨lTT, eTT⟩ := mulL_ok (lT.mono (by decide)) lN₄
  obtain ⟨lZZ, eZZ⟩ := mulL_ok (lZ.mono (by decide)) lZ₂
  obtain ⟨lz, ez⟩ := addL_ok lZZ lZZ (by decide)
  obtain ⟨lXc, eXc⟩ := subL_ok (lPP.mono (by decide)) (lMM.mono (by decide))
  obtain ⟨lYc, eYc⟩ := addL_ok lPP lMM (by decide)
  obtain ⟨lZc, eZc⟩ := subL_ok (lz.mono (by decide)) (lTT.mono (by decide))
  obtain ⟨lTc, eTc⟩ := addL_ok lz lTT (by decide)
  have hT₁ := t_of_rep hp (mq_mul hX) (mq_mul hY) (mq_xy hXY) (ne_fv hZ)
  have mN₁ : MEq Ed25519.p (fv N₁) (((y₂ : Int) + x₂) * fv Z₂) := by
    have m := mq hN₁
    push_cast at m
    exact m
  have mN₂ := mq_ymx hQ.1 hN₂
  have mN₄ := mq_dxy hN₄
  have mTT := mq_mul eTT
  have mZc := mq_sub (fv_lt _) eZc
  have mTc := mq_add eTc
  generalize (((Ed25519.p - x₂) % Ed25519.p : Nat) : Int) = x₂' at hu hv n1 n2 hneg
  have hN₁' : MEq Ed25519.p (fv N₂) (((y₂ : Int) + x₂') * fv Z₂) :=
    sm (by ring_mod [(ms mN₂) * 1, hneg * (-((fv Z₂ : Nat) : Int))])
  have hN₂' : MEq Ed25519.p (fv N₁) (((y₂ : Int) - x₂') * fv Z₂) :=
    sm (by ring_mod [(ms mN₁) * 1, hneg * ((fv Z₂ : Nat) : Int)])
  have hN₄' : MEq Ed25519.p (-((fv N₄ : Nat) : Int)) (2 * 𝔡 * x₂' * y₂ * fv Z₂) :=
    sm (by ring_mod [(ms mN₄) * (-1), hneg * (-(2 * 𝔡 * y₂ * fv Z₂))])
  have hTT' : MEq Ed25519.p (-((fv (mulL T₁ N₄) : Nat) : Int)) (fv T₁ * -((fv N₄ : Nat) : Int)) :=
    sm (by ring_mod [(ms mTT) * (-1)])
  have hZc' : MEq Ed25519.p (fv (subL (addL (mulL Z₁ Z₂) (mulL Z₁ Z₂)) (mulL T₁ N₄)))
      (fv (addL (mulL Z₁ Z₂) (mulL Z₁ Z₂)) + -((fv (mulL T₁ N₄) : Nat) : Int)) :=
    sm (by ring_mod [(ms mZc) * 1])
  have hTc' : MEq Ed25519.p (fv (addL (addL (mulL Z₁ Z₂) (mulL Z₁ Z₂)) (mulL T₁ N₄)))
      (fv (addL (mulL Z₁ Z₂) (mulL Z₁ Z₂)) - -((fv (mulL T₁ N₄) : Nat) : Int)) :=
    sm (by ring_mod [(ms mTc) * 1])
  obtain ⟨m1, m2, m3, m4⟩ := addN_alg hp hu hv n1 n2 (mq_mul hX) (mq_mul hY) hT₁ (ne_fv hZ) hN₁' hN₂' hN₄'
    (ne_fv hZ₂) (mq_add ea) (mq_sub (fv_lt _) es) (mq_mul ePP) (mq_mul eMM) hTT' (mq_mul eZZ) (mq_add ez)
    (mq_sub (fv_lt _) eXc) (mq_add eYc) hZc' hTc'
  unfold subNL
  exact ⟨lXc.mono (by decide), lYc.mono (by decide), lZc.mono (by decide), lTc.mono (by decide), fv_ne m3,
    fv_ne m4, eq_mul (fv_lt _) m1, eq_mul (fv_lt _) m2⟩

/-- **`EdFormulas` from the primality of `p`.** -/
theorem edFormulas (hp : IsPrime Ed25519.p) : EdFormulas :=
  ⟨edDbl_ok hp, edExt_ok hp, edProj_ok hp, edAddN_ok hp, edSubN_ok hp, edNiels_ok hp⟩

end C3.RV32.EdM
