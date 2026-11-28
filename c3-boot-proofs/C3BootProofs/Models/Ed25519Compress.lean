import C3BootProofs.Models.Ed25519Model
import C3BootProofs.Models.Ed25519Formulas
import C3BootProofs.Models.Ed25519Fermat
import C3BootProofs.Models.Ed25519Bytes2

/-!
# `compress` encodes the point, from the primality of `p`

`compress` of a projective point `(X : Y : Z)` inverts `Z²` as
`(Z²)^(2^255 - 21) = (Z²)^(p - 2)`: `pow22501` gives `t19 = a^(2^250 - 1)`
and `t3 = a^11` for `a = Z²`, and five squarings and a product give
`a^((2^250 - 1) 2^5 + 11)`. By Fermat's little theorem `Y Z (Z²)^(p - 2)` is
`y` and `X Z (Z²)^(p - 2)` is `x`, and `bytesL_eq` and `leBytes32_sign`
turn them into the encoding.
-/

namespace C3.RV32.EdM

open C3.Models

local notation "𝔭" => ((Ed25519.p : Nat) : Int)

/-- Limbs below 2^26 that hold `a^e` modulo `p`. -/
def FP (l : List Nat) (a e : Nat) : Prop := Lim (2 ^ 26) l ∧ fv l = a ^ e % Ed25519.p

theorem fp_mul {l m : List Nat} {a e f g : Nat} (hl : FP l a e) (hm : FP m a f) (h : e + f = g) :
    FP (mulL l m) a g := by
  obtain ⟨l1, e1⟩ := mulL_ok (hl.1.mono (by decide)) (hm.1.mono (by decide))
  refine ⟨l1, ?_⟩
  rw [e1, hl.2, hm.2, ← Nat.mul_mod, ← Nat.pow_add, h]

theorem fp_sq {l : List Nat} {a e g : Nat} (hl : FP l a e) (h : e + e = g) : FP (sqL l) a g := by
  obtain ⟨l1, e1⟩ := sqL_ok (hl.1.mono (by decide))
  refine ⟨l1, ?_⟩
  rw [e1, hl.2, ← Nat.mul_mod, ← Nat.pow_add, h]

theorem fp_sqIter {l : List Nat} {a e : Nat} (hl : FP l a e) : ∀ k, FP (sqIter k l) a (e * 2 ^ k)
  | 0 => by rw [Nat.pow_zero, Nat.mul_one]; exact hl
  | k + 1 => fp_sq (fp_sqIter hl k) (by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two])

theorem wl_sqL (l : List Nat) : wl (sqL l) = sqL l := wl_red ..

theorem sqL_ofW (x : Nat → Word) :
    sqL (ofW x) = feSquareSpec (x 0).toNat (x 1).toNat (x 2).toNat (x 3).toNat (x 4).toNat (x 5).toNat
      (x 6).toNat (x 7).toNat (x 8).toNat (x 9).toNat := by
  simp only [sqL, getElem!_getD', ofW, List.getD_cons_succ, List.getD_cons_zero]

theorem ofW_sqW (x : Nat → Word) : ofW (feSqW x) = sqL (ofW x) := by
  rw [← wl_sqL, sqL_ofW]; rfl

theorem wfp_sq {x : Nat → Word} {a e g : Nat} (hx : FP (ofW x) a e) (h : e + e = g) : FP (ofW (feSqW x)) a g := by
  rw [ofW_sqW]; exact fp_sq hx h

theorem wfp_mul {x y : Nat → Word} {a e f g : Nat} (hx : FP (ofW x) a e) (hy : FP (ofW y) a f) (h : e + f = g) :
    FP (ofW (feMulW x y)) a g := by
  rw [ofW_mulW]; exact fp_mul hx hy h

theorem wfp_pow {x : Nat → Word} {a e g : Nat} (k : Nat) (hx : FP (ofW x) a e) (h : e * 2 ^ (k + 1) = g) :
    FP (ofW (pow2kW (k + 1) x)) a g := by
  show FP (wl (sqL (sqIter k (ofW x)))) a g
  rw [wl_sqL, ← h]
  exact fp_sqIter hx (k + 1)

/-- **`pow22501`**: `t19 = a^(2^250 - 1)` and `t3 = a^11`. -/
theorem fp_pow22501 {x : Nat → Word} {a : Nat} (hb : FP (ofW x) a 1) :
    FP (ofW (pwT19 x)) a (2 ^ 250 - 1) ∧ FP (ofW (pwT3 x)) a 11 := by
  have t0 : FP (ofW (pwT0 x)) a 2 := wfp_sq hb rfl
  have t0s : FP (ofW (pwT0s x)) a 4 := wfp_sq t0 rfl
  have t1 : FP (ofW (pwT1 x)) a 8 := wfp_sq t0s rfl
  have t2 : FP (ofW (pwT2 x)) a 9 := wfp_mul hb t1 rfl
  have t3 : FP (ofW (pwT3 x)) a 11 := wfp_mul t0 t2 rfl
  have t4 : FP (ofW (pwT4 x)) a 22 := wfp_sq t3 rfl
  have t5 : FP (ofW (pwT5 x)) a 31 := wfp_mul t2 t4 rfl
  have t6 : FP (ofW (pwT6 x)) a (31 * 2 ^ 5) := wfp_pow 4 t5 rfl
  have t7 : FP (ofW (pwT7 x)) a (2 ^ 10 - 1) := wfp_mul t6 t5 (by decide)
  have t8 : FP (ofW (pwT8 x)) a ((2 ^ 10 - 1) * 2 ^ 10) := wfp_pow 9 t7 rfl
  have t9 : FP (ofW (pwT9 x)) a (2 ^ 20 - 1) := wfp_mul t8 t7 (by decide)
  have t10 : FP (ofW (pwT10 x)) a ((2 ^ 20 - 1) * 2 ^ 20) := wfp_pow 19 t9 rfl
  have t11 : FP (ofW (pwT11 x)) a (2 ^ 40 - 1) := wfp_mul t10 t9 (by decide)
  have t12 : FP (ofW (pwT12 x)) a ((2 ^ 40 - 1) * 2 ^ 10) := wfp_pow 9 t11 rfl
  have t13 : FP (ofW (pwT13 x)) a (2 ^ 50 - 1) := wfp_mul t12 t7 (by decide)
  have t14 : FP (ofW (pwT14 x)) a ((2 ^ 50 - 1) * 2 ^ 50) := wfp_pow 49 t13 rfl
  have t15 : FP (ofW (pwT15 x)) a (2 ^ 100 - 1) := wfp_mul t14 t13 (by decide)
  have t16 : FP (ofW (pwT16 x)) a ((2 ^ 100 - 1) * 2 ^ 100) := wfp_pow 99 t15 rfl
  have t17 : FP (ofW (pwT17 x)) a (2 ^ 200 - 1) := wfp_mul t16 t15 (by decide)
  have t18 : FP (ofW (pwT18 x)) a ((2 ^ 200 - 1) * 2 ^ 50) := wfp_pow 49 t17 rfl
  exact ⟨wfp_mul t18 t13 (by decide), t3⟩

/-- **`invert`** of `Z²` in `compress`: `(Z²)^(p - 2)`. -/
theorem fp_recip {Z : List Nat} (hZ : Lim (2 ^ 26) Z) :
    FP (mulL (sqIter 5 (pw19L (sqL Z))) (pw3L (sqL Z))) (fv (sqL Z)) (Ed25519.p - 2) := by
  have l2 := (sqL_ok (hZ.mono (by decide))).1
  have hb : FP (ofW (limbF (sqL Z))) (fv (sqL Z)) 1 := by
    show FP (wl (sqL Z)) _ _
    rw [wl_sqL, FP, Nat.pow_one, Nat.mod_eq_of_lt (fv_lt _)]
    exact ⟨l2, rfl⟩
  obtain ⟨h19, h3⟩ := fp_pow22501 hb
  exact fp_mul (fp_sqIter h19 5) h3 (by decide)

/-- `X Z (Z²)^(p - 2)` is `x` when `X = x Z` and `Z ≠ 0`. -/
theorem recip_coord (hp : IsPrime Ed25519.p) {X Z R : List Nat} {x : Nat} (lX : Lim (2 ^ 26) X)
    (lZ : Lim (2 ^ 26) Z) (hZ : fv Z ≠ 0) (hX : fv X = x * fv Z % Ed25519.p) (hx : x < Ed25519.p)
    (hR : FP R (fv (sqL Z)) (Ed25519.p - 2)) :
    Lim (2 ^ 26) (mulL (mulL X Z) R) ∧ fv (mulL (mulL X Z) R) = x := by
  obtain ⟨l2, e2⟩ := sqL_ok (lZ.mono (by decide))
  obtain ⟨lXZ, eXZ⟩ := mulL_ok (lX.mono (by decide)) (lZ.mono (by decide))
  obtain ⟨lc, ec⟩ := mulL_ok (lXZ.mono (by decide)) (hR.1.mono (by decide))
  refine ⟨lc, ?_⟩
  have nZ := ne_fv hZ
  have na : ¬ MEq Ed25519.p (fv (sqL Z)) 0 := by
    intro h
    exact hp.meq_mul_ne nZ nZ (Eq.trans (Eq.symm (mq_mul e2)) h)
  have hf : fv (sqL Z) ^ (Ed25519.p - 2) * fv (sqL Z) % Ed25519.p = 1 := by
    have h := fermat hp (fv (sqL Z)) (fun h => na (mq_nat (h.trans (Nat.zero_mod _).symm)))
    rwa [show Ed25519.p - 1 = Ed25519.p - 2 + 1 by decide, Nat.pow_succ] at h
  have hR2 := hR.2
  generalize fv (sqL Z) ^ (Ed25519.p - 2) = A at hf hR2
  have m6 : MEq Ed25519.p ((A * fv (sqL Z) : Nat) : Int) ((1 : Nat) : Int) :=
    mq_nat (hf.trans (Nat.mod_eq_of_lt one_lt_p).symm)
  push_cast at m6
  have h1 := ms (mq_mul ec)
  have h2 := ms (mq_mul eXZ)
  have h3 := ms (mq_mul hX)
  have h4 := ms (mq_mul e2)
  have h5 := ms (mq hR2)
  have h6 := ms m6
  refine meq_eq (sm ?_) (fv_lt _) hx
  ring_mod [h1 * 1, h2 * (fv R : Int), h3 * ((fv R : Int) * fv Z), h4 * (-((x : Int) * fv R)),
    h5 * ((x : Int) * fv (sqL Z)), h6 * (x : Int)]

/-- **`compress` encodes the point** it represents, given that `p` is prime. -/
theorem compress_ok (hp : IsPrime Ed25519.p) : CompressOK := by
  rintro ⟨X, Y, Z⟩ ⟨x, y⟩ hP ⟨lX, lY, lZ, hZ, hX, hY⟩
  dsimp only at lX lY lZ hZ hX hY
  have hR := fp_recip lZ
  obtain ⟨lx, ex⟩ := recip_coord hp lX lZ hZ hX hP.1 hR
  obtain ⟨ly, ey⟩ := recip_coord hp lY lZ hZ hY hP.2.1 hR
  have hy : y < 2 ^ 255 := Nat.lt_trans hP.2.1 (by decide)
  unfold evCompress
  dsimp only
  rw [bytesL_eq ly, bytesL_eq lx, ey, ex]
  exact leBytes32_sign y x hy

end C3.RV32.EdM
