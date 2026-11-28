import C3BootProofs.Models.EcdsaLoop

/-!
# Projective triples, Montgomery form, and decoded keys, for any curve

`PRep p P a` says the projective triple `P` represents the affine point `a`
modulo `p`. Montgomery form scales all three coordinates by the same factor,
so it doesn't change what a triple represents. The Montgomery lemmas take
`R` and an inverse `Ri` of it modulo `p`, so P-256 and P-384 share them.
-/

namespace C3.Models

/-- The triple `P` represents `a` modulo `p`: every coordinate is below
`p`, the point at infinity is `(0 : Y : 0)` with `Y ≠ 0`, and `(x, y)` is
`(x Z : y Z : Z)` with `Z ≠ 0`. -/
def PRep (p : Nat) (P : Nat × Nat × Nat) : ECPoint → Prop
  | none => P.1 < p ∧ P.2.1 < p ∧ P.2.2 < p ∧ P.1 = 0 ∧ P.2.1 ≠ 0 ∧ P.2.2 = 0
  | some (x, y) => P.1 < p ∧ P.2.1 < p ∧ P.2.2 < p ∧ x < p ∧ y < p ∧ P.2.2 ≠ 0 ∧
      MEq p P.1 ((x : Int) * P.2.2) ∧ MEq p P.2.1 ((y : Int) * P.2.2)

theorem modInv_lt {a m : Nat} (hm : 0 < m) : modInv a m < m := by
  unfold modInv
  generalize modInv.go m (a % m) 0 1 (2 * m.log2 + 4) = g
  have h1 := Int.emod_nonneg g (show (m : Int) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos g (show (0 : Int) < m by omega)
  omega

/-- An inverse below `m` is the one `modInv` computes. -/
theorem modInv_unique {a w m : Nat} (hm : 1 < m) (hw : w < m) (h : MEq m ((w : Int) * a) 1) : modInv a m = w := by
  have hn : w * a % m = 1 := by
    have := MEq.natCast.mp (show MEq m ((w * a : Nat) : Int) ((1 : Nat) : Int) by rw [Int.natCast_mul]; exact h)
    rwa [Nat.mod_eq_of_lt hm] at this
  have hc : Nat.Coprime a m := by
    have d1 : Nat.gcd a m ∣ w * a := Nat.dvd_trans (Nat.gcd_dvd_left a m) (Nat.dvd_mul_left a w)
    have d2 : Nat.gcd a m ∣ w * a % m := (Nat.dvd_mod_iff (Nat.gcd_dvd_right a m)).mpr d1
    rw [hn] at d2
    exact Nat.dvd_one.mp d2
  have hs := modInv_spec hm hc
  have hv := modInv_lt (a := a) (Nat.lt_trans Nat.zero_lt_one hm)
  have e : w % m = modInv a m % m := by
    calc w % m = w * (a * modInv a m % m) % m := by rw [hs, Nat.mul_one]
      _ = w * a * modInv a m % m := by rw [Nat.mul_mod_mod, Nat.mul_assoc]
      _ = w * a % m * modInv a m % m := by rw [Nat.mod_mul_mod]
      _ = modInv a m % m := by rw [hn, Nat.one_mul]
  rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hv] at e
  exact e.symm

/-! ## Montgomery form -/

/-- The Montgomery product of `a`'s and `b`'s Montgomery forms is `ab`'s. -/
theorem mont_mul {p R Ri A B a b : Nat} (hR : R * Ri % p = 1) (hA : A % p = a * R % p)
    (hB : B % p = b * R % p) : A * B * Ri % p = a * b * R % p := by
  calc A * B * Ri % p = A % p * (B * Ri) % p := by rw [Nat.mod_mul_mod, Nat.mul_assoc]
    _ = a * R % p * (B * Ri) % p := by rw [hA]
    _ = B * (a * R * Ri) % p := by
      rw [Nat.mod_mul_mod]; simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ = B % p * (a * R * Ri) % p := by rw [Nat.mod_mul_mod]
    _ = b * R % p * (a * R * Ri) % p := by rw [hB]
    _ = a * b * R * (R * Ri) % p := by
      rw [Nat.mod_mul_mod]; simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ = a * b * R * (R * Ri % p) % p := by rw [Nat.mul_mod_mod]
    _ = a * b * R % p := by rw [hR, Nat.mul_one]

/-- Cancels `R` from both sides. -/
theorem mont_cancel {p R Ri u v : Nat} (hR : R * Ri % p = 1) (h : u * R % p = v * R % p) : u % p = v % p := by
  have e : ∀ w, w % p = w * R % p * Ri % p := fun w => by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod, hR, Nat.mul_one]
  rw [e u, e v, h]

/-- Taking a value out of Montgomery form: `(a R mod p) Ri ≡ a`. -/
theorem mont_out {p R Ri a : Nat} (hR : R * Ri % p = 1) : a * R % p * Ri % p = a % p := by
  rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod, hR, Nat.mul_one]

/-- An affine point in Montgomery form, with `Z` the Montgomery 1. -/
theorem mont_rep {p R x y : Nat} (hx : x < p) (hy : y < p) (hR : R % p ≠ 0) :
    PRep p (x * R % p, y * R % p, R % p) (some (x, y)) := by
  have hp : 0 < p := by omega
  refine ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp, hx, hy, hR, ?_, ?_⟩ <;>
  · show MEq _ ((_ % p : Nat) : Int) (_ * ((R % p : Nat) : Int))
    refine (natMod _ _).trans (MEq.trans ?_ ((MEq.refl _).mul (natMod _ _)).symm)
    rw [Int.natCast_mul]
    exact MEq.refl _

/-- **The affine `x`**: with `zinv Z ≡ R²`, the Montgomery product of `X`
and `zinv`, taken out of Montgomery form, is `x`. -/
theorem mont_affine_x {p R Ri X Y Z x y zinv : Nat} (hR : R * Ri % p = 1) (h : PRep p (X, Y, Z) (some (x, y)))
    (hz : MEq p ((zinv : Int) * Z) ((R * R % p : Nat) : Int)) :
    X * zinv * Ri % p * 1 * Ri % p = x := by
  obtain ⟨-, -, -, hx, -, -, eX, -⟩ := h
  have hp : 0 < p := by omega
  have hp1 : 1 < p := by
    rcases Nat.lt_or_ge 1 p with h1 | h1
    · exact h1
    · rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
      · exact absurd hx (Nat.not_lt_zero _)
      · rw [Nat.mod_one] at hR; exact absurd hR (by decide)
  have hRI : MEq p ((R : Int) * (Ri : Int)) 1 := by
    rw [← Int.natCast_mul]
    exact MEq.natCast.mpr (by rw [hR, Nat.mod_eq_of_lt hp1])
  rw [Nat.mul_one]
  apply EC.eq_of_meq (Nat.mod_lt _ hp) hx
  refine (natMod _ _).trans ?_
  rw [Int.natCast_mul]
  refine ((natMod _ _).mul (MEq.refl _)).trans ?_
  rw [Int.natCast_mul, Int.natCast_mul]
  have e1 : MEq p ((X : Int) * zinv) ((x : Int) * ((R : Int) * (R : Int))) := by
    refine (eX.mul (MEq.refl _)).trans ?_
    rw [Int.mul_assoc, Int.mul_comm (Z : Int)]
    refine (MEq.refl _).mul (hz.trans ((natMod _ _).trans ?_))
    rw [Int.natCast_mul]; exact MEq.refl _
  refine ((e1.mul (MEq.refl _)).mul (MEq.refl _)).trans ?_
  have e2 : (x : Int) * ((R : Int) * (R : Int)) * Ri * Ri = x * (((R : Int) * (Ri : Int)) * ((R : Int) * (Ri : Int))) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e2]
  refine ((MEq.refl _).mul (hRI.mul hRI)).trans ?_
  rw [Int.mul_one, Int.mul_one]
  exact MEq.refl _

/-- Negating `Y` modulo `p` represents the negated point. -/
theorem neg_rep {c : Curve} {X Y Z Y' : Nat} {a : ECPoint} (hp : 0 < c.p) (hY' : Y < c.p → Y' = (c.p - Y) % c.p)
    (h : PRep c.p (X, Y, Z) a) : PRep c.p (X, Y', Z) (EC.neg c a) := by
  rcases a with _ | ⟨x, y⟩
  · dsimp only [PRep] at h ⊢
    obtain ⟨hX, hY, hZ, eX, eY, eZ⟩ := h
    rw [hY' hY]
    refine ⟨hX, Nat.mod_lt _ hp, hZ, eX, ?_, eZ⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · dsimp only [PRep] at h ⊢
    obtain ⟨hX, hY, hZ, hx, hy, hZ0, eX, eY⟩ := h
    rw [hY' hY]
    refine ⟨hX, Nat.mod_lt _ hp, hZ, hx, Nat.mod_lt _ hp, hZ0, eX, ?_⟩
    show MEq c.p (((c.p - Y) % c.p : Nat) : Int) ((((c.p - y) % c.p : Nat) : Int) * Z)
    refine (natMod _ _).trans (MEq.trans ?_ ((natMod _ _).mul (MEq.refl _)).symm)
    have e1 : (((c.p - Y : Nat) : Int)) = -(Y : Int) + (c.p : Int) * 1 := by omega
    have e2 : (((c.p - y : Nat) : Int)) * Z = -((y : Int) * Z) + (c.p : Int) * Z := by
      rw [show (((c.p - y : Nat) : Int)) = (c.p : Int) - y by omega, Int.sub_mul, Int.sub_eq_add_neg, Int.add_comm]
    rw [e1, e2]
    exact (MEq.add_mul_self 1).trans ((eY.neg).trans (MEq.add_mul_self _).symm)

/-! ## Decoded keys -/

/-- The curve equation, as `decodePoint` checks it, puts the point on the
curve. -/
theorem onC_of_eq {c : Curve} {x y : Nat} (hx : x < c.p) (hy : y < c.p)
    (he : y * y % c.p = (x * x % c.p * x + c.a * x + c.b) % c.p) : EC.OnC c (some (x, y)) := by
  refine ⟨hx, hy, ?_⟩
  have e : y * y % c.p = (x * x * x + c.a * x + c.b) % c.p := by
    have h1 : x * x % c.p * x % c.p = x * x * x % c.p := Nat.mod_mul_mod _ _ _
    have h2 : (x * x % c.p * x + c.a * x) % c.p = (x * x * x + c.a * x) % c.p := by
      rw [Nat.add_mod, h1, ← Nat.add_mod]
    rw [he, Nat.add_mod, h2, ← Nat.add_mod]
  have := MEq.natCast.mpr e
  rw [Int.natCast_mul, Int.natCast_add, Int.natCast_add, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul] at this
  exact this

/-- `decodePoint` accepts an uncompressed point whose coordinates are below
`p` and satisfy the curve equation. -/
theorem decode_some {c : Curve} {b : Bytes} {x y : Nat} (hlen : b.length = 1 + 2 * c.size)
    (hh : b.head? = some 4) (hx' : beNat ((b.drop 1).take c.size) = x) (hy' : beNat (b.drop (1 + c.size)) = y)
    (hx : x < c.p) (hy : y < c.p) (he : y * y % c.p = (x * x % c.p * x + c.a * x + c.b) % c.p) :
    c.decodePoint b = some (x, y) := by
  have hr : require true = some () := rfl
  have hb : ∀ n : Nat, (n == n) = true := fun n => by unfold BEq.beq; exact decide_eq_true rfl
  unfold Curve.decodePoint
  simp only [Option.bind_eq_bind]
  rw [hlen, hh, hb, show ((some 4 : Option Nat) == some 4) = true from rfl, Bool.and_self, hr, Option.bind_some,
    hx', hy', decide_eq_true hx, decide_eq_true hy, he, hb, Bool.and_self, Bool.and_self, hr]
  rfl

end C3.Models
