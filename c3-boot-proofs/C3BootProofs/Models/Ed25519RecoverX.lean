import C3BootProofs.Models.Ed25519Model
import C3BootProofs.Models.Ed25519Laws

/-!
# `recoverX` finds each point's `x`, from the primality of `p`

For `(x, y)` on the curve, `u = y² - 1` and `v = d y² + 1` satisfy
`v x² = u`, and `v ≠ 0` because `d` is not a square. RFC 8032's candidate
`u v³ (u v⁷)^((p - 5) / 8)` is then `x^((p + 3) / 4)` by Fermat's little
theorem, its square times `v` is `u x^((p - 1) / 2) = ±u`, and either it or
its product with `sqrt(-1)` squares to `x²`, so it is `±x`. The sign bit
picks `x`.

The proof generalizes `sqrtM1` and the exponent before it reduces
`recoverX`, so the kernel never evaluates `powMod` on them.
-/

namespace C3.RV32.EdM

open C3.Models

local notation "𝔭" => ((Ed25519.p : Nat) : Int)
local notation "𝔡" => ((Ed25519.d : Nat) : Int)

theorem meq_pow {a b : Int} (h : MEq Ed25519.p a b) : ∀ n : Nat, MEq Ed25519.p (a ^ n) (b ^ n)
  | 0 => by rw [Int.pow_zero, Int.pow_zero]; exact MEq.refl _
  | n + 1 => by rw [Int.pow_succ, Int.pow_succ]; exact (meq_pow h n).mul h

theorem fermat_nat (hp : IsPrime Ed25519.p) {a : Nat} (ha : ¬ MEq Ed25519.p a 0) :
    MEq Ed25519.p ((a : Int) ^ (Ed25519.p - 1)) 1 := by
  have h0 : a % Ed25519.p ≠ 0 := fun h => ha (MEq.natCast.mpr (by rw [h]; rfl))
  have h := fermat hp a h0
  have m : MEq Ed25519.p ((a ^ (Ed25519.p - 1) : Nat) : Int) ((1 : Nat) : Int) :=
    MEq.natCast.mpr (by rw [h, Nat.mod_eq_of_lt one_lt_p])
  rw [Int.natCast_pow] at m
  exact m

/-- `v = d y² + 1` is not zero, because `-1` is a square and `d` is not. -/
theorem v_ne (hp : IsPrime Ed25519.p) {i y V : Int} (hi : (i * i + 1) % 𝔭 = 0) (hV : MEq Ed25519.p V (𝔡 * y * y + 1)) :
    ¬ MEq Ed25519.p V 0 := fun h0 =>
  d_nonsq_int hp (i * 𝔡 * y) (sm (by ring_mod [hi * (𝔡 * 𝔡 * y * y), (ms hV) * 𝔡, (ms h0) * (-𝔡)]))

/-- The candidate is `x² (x^K)²` for `K = (p - 5) / 8`. -/
theorem cand_eq {X U V C B : Int} {K : Nat} (hvx : MEq Ed25519.p (V * X * X) U)
    (hF : MEq Ed25519.p ((V ^ K) ^ 8 * V ^ 4) 1) (hC : MEq Ed25519.p C (U * V ^ 3 * B))
    (hB : MEq Ed25519.p B ((V ^ K) ^ 8 * (X ^ K) ^ 2)) : MEq Ed25519.p C (X * X * (X ^ K) * (X ^ K)) :=
  sm (by ring_mod [(ms hC) * 1, (ms hB) * (U * V ^ 3), (ms hvx) * (-(V ^ 3 * (V ^ K) ^ 8 * (X ^ K) ^ 2)),
    (ms hF) * (X * X * (X ^ K) * (X ^ K))])

/-- `±1`: a number whose square is `1` modulo a prime. -/
theorem pm_one (hp : IsPrime Ed25519.p) {e : Int} (h : MEq Ed25519.p (e * e) 1) :
    MEq Ed25519.p e 1 ∨ MEq Ed25519.p e (-1) := by
  rcases hp.meq_mul_zero (sm (by ring_mod [(ms h) * 1]) : MEq Ed25519.p ((e - 1) * (e + 1)) 0) with h1 | h1
  · exact Or.inl (sm (by ring_mod [(ms h1) * 1]))
  · exact Or.inr (sm (by ring_mod [(ms h1) * 1]))

/-- `±x`: from `v c² = v x²` with `v ≠ 0`. -/
theorem pm_x (hp : IsPrime Ed25519.p) {V C X : Int} (hV : ¬ MEq Ed25519.p V 0)
    (h : MEq Ed25519.p (V * C * C) (V * X * X)) : MEq Ed25519.p C X ∨ MEq Ed25519.p C (-X) := by
  have h2 : MEq Ed25519.p ((C - X) * (C + X)) 0 :=
    hp.meq_cancel hV (sm (by ring_mod [(ms h) * 1]) : MEq Ed25519.p ((C - X) * (C + X) * V) (0 * V))
  rcases hp.meq_mul_zero h2 with h1 | h1
  · exact Or.inl (sm (by ring_mod [(ms h1) * 1]))
  · exact Or.inr (sm (by ring_mod [(ms h1) * 1]))

theorem nat_of_meq {a b : Nat} (ha : a < Ed25519.p) (hb : b < Ed25519.p) (h : MEq Ed25519.p a b) : a = b :=
  meq_eq h ha hb

/-- The sign step: from `c = ±x` with `0 < x < p`, choosing by `x`'s low bit
gives `x`. -/
theorem sign_pick {x c : Nat} (hx : x < Ed25519.p) (hc : c < Ed25519.p) (hx0 : x ≠ 0)
    (h : MEq Ed25519.p c x ∨ MEq Ed25519.p c (-(x : Int))) :
    (do
      let c' ← some c
      require !(c' == 0 && x % 2 == 1)
      pure (if (c' % 2 == x % 2) = true then c' else Ed25519.p - c') : Option Nat) = some x := by
  have hodd : Ed25519.p % 2 = 1 := by decide
  rcases h with h | h
  · have e := nat_of_meq hc hx h
    subst e
    simp [require, hx0]
  · have hs : (c + x) % Ed25519.p = 0 := by
      have m : MEq Ed25519.p ((c + x : Nat) : Int) ((0 : Nat) : Int) := by
        push_cast
        exact sm (by ring_mod [(ms h) * 1])
      have m' := MEq.natCast.mp m
      rwa [Nat.zero_mod] at m'
    have hcx : c + x = Ed25519.p := by
      by_cases hlt : c + x < Ed25519.p
      · rw [Nat.mod_eq_of_lt hlt] at hs; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hs; omega
    have hc0 : c ≠ 0 := by omega
    have h2 : ¬ c % 2 = x % 2 := by omega
    simp [require, hc0, h2]
    omega

theorem recoverX_ok (hp : IsPrime Ed25519.p) : RecoverXOK := by
  intro x y hP
  have hx : x < Ed25519.p := hP.1
  have hy : y < Ed25519.p := hP.2.1
  have cv := curveI_of hP
  dsimp only at cv
  have hK : 8 * ((Ed25519.p - 5) / 8) + 4 = Ed25519.p - 1 := by decide
  have hi := sqrtM1_int
  unfold Ed25519.recoverX
  dsimp only
  generalize hu : (y * y + Ed25519.p - 1) % Ed25519.p = u
  generalize hv : (Ed25519.d * y % Ed25519.p * y + 1) % Ed25519.p = v
  generalize (Ed25519.p - 5) / 8 = K at hK ⊢
  generalize hc : u * powMod v 3 Ed25519.p % Ed25519.p *
    powMod (u * powMod v 7 Ed25519.p % Ed25519.p) K Ed25519.p % Ed25519.p = c
  generalize Ed25519.sqrtM1 = i at hi ⊢
  have hu' : MEq Ed25519.p u ((y : Int) * y - 1) := by
    rw [← hu]
    refine (natMod _ _).trans ?_
    have h1 : 1 ≤ y * y + Ed25519.p := by have := one_lt_p; omega
    rw [Int.natCast_sub h1, Int.natCast_add, Int.natCast_mul, Int.natCast_one]
    exact sm (by ring_mod [p_sub * 1])
  have hv' : MEq Ed25519.p v (𝔡 * y * y + 1) := by
    rw [← hv]
    refine (natMod _ _).trans ?_
    push_cast
    exact sm (by ring_mod [(emod_sub (𝔡 * y)) * (y : Int)])
  have hvx : MEq Ed25519.p ((v : Int) * x * x) u :=
    sm (by ring_mod [(ms hv') * ((x : Int) * x), (ms hu') * (-1), cv * (-1)])
  have hv0 := v_ne hp hi hv'
  have hu_lt : u < Ed25519.p := by rw [← hu]; exact Nat.mod_lt _ p_pos
  have hc_lt : c < Ed25519.p := by rw [← hc]; exact Nat.mod_lt _ p_pos
  have hF : MEq Ed25519.p (((v : Int) ^ K) ^ 8 * (v : Int) ^ 4) 1 := by
    have m := fermat_nat hp hv0
    rw [← hK, Int.pow_add, Nat.mul_comm, Int.pow_mul] at m
    exact m
  have hC : MEq Ed25519.p c (u * (v : Int) ^ 3 * ((u : Int) * (v : Int) ^ 7) ^ K) := by
    rw [← hc, powMod_eq, powMod_eq, powMod_eq]
    refine (natMod _ _).trans ?_
    rw [Int.natCast_mul]
    refine MEq.mul ?_ ?_
    · refine (natMod _ _).trans ?_
      rw [Int.natCast_mul]
      refine MEq.mul (MEq.refl _) ?_
      refine (natMod _ _).trans ?_
      rw [Int.natCast_pow]
      exact MEq.refl _
    · refine (natMod _ _).trans ?_
      rw [Int.natCast_pow]
      refine meq_pow ?_ K
      refine (natMod _ _).trans ?_
      rw [Int.natCast_mul]
      refine MEq.mul (MEq.refl _) ?_
      refine (natMod _ _).trans ?_
      rw [Int.natCast_pow]
      exact MEq.refl _
  have hB : MEq Ed25519.p (((u : Int) * (v : Int) ^ 7) ^ K) (((v : Int) ^ K) ^ 8 * ((x : Int) ^ K) ^ 2) := by
    refine (meq_pow (sm (by ring_mod [(ms hvx) * (-((v : Int) ^ 7))]) :
      MEq Ed25519.p ((u : Int) * (v : Int) ^ 7) ((v : Int) ^ 8 * (x : Int) ^ 2)) K).trans ?_
    rw [Int.mul_pow, ← Int.pow_mul, ← Int.pow_mul, Nat.mul_comm 8, Nat.mul_comm 2, Int.pow_mul, Int.pow_mul]
    exact MEq.refl _
  have hcx := cand_eq hvx hF hC hB
  by_cases hx0 : x = 0
  · subst hx0
    have u0 : u = 0 := nat_of_meq hu_lt p_pos (sm (by ring_mod [(ms hvx) * (-1)]))
    have c0 : c = 0 := nat_of_meq hc_lt p_pos (sm (by ring_mod [(ms hcx) * 1]))
    subst u0 c0
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [Nat.mul_zero, Nat.zero_mod]; rfl))]
    rfl
  have hxn : ¬ MEq Ed25519.p (x : Int) 0 := fun h => hx0 (nat_of_meq hx p_pos h)
  have hFx : MEq Ed25519.p (((x : Int) ^ K) ^ 4 * (x : Int) ^ 2 * (((x : Int) ^ K) ^ 4 * (x : Int) ^ 2)) 1 := by
    have m := fermat_nat hp hxn
    rw [← hK, Int.pow_add, Nat.mul_comm, Int.pow_mul] at m
    exact sm (by ring_mod [(ms m) * 1])
  have hvc : MEq Ed25519.p ((v : Int) * c * c) (u * (((x : Int) ^ K) ^ 4 * (x : Int) ^ 2)) :=
    sm (by ring_mod [(ms hcx) * ((v : Int) * (c + (x : Int) * x * (x : Int) ^ K * (x : Int) ^ K)),
      (ms hvx) * (((x : Int) ^ K) ^ 4 * (x : Int) ^ 2)])
  have hvcN : MEq Ed25519.p ((v * c % Ed25519.p * c % Ed25519.p : Nat) : Int) ((v : Int) * c * c) := by
    refine (natMod _ _).trans ?_
    push_cast
    exact sm (by ring_mod [(emod_sub ((v : Int) * c)) * (c : Int)])
  have hlt : v * c % Ed25519.p * c % Ed25519.p < Ed25519.p := Nat.mod_lt _ p_pos
  rcases pm_one hp hFx with he | he
  · have h1 : v * c % Ed25519.p * c % Ed25519.p = u :=
      nat_of_meq hlt hu_lt (hvcN.trans (sm (by ring_mod [(ms hvc) * 1, (ms he) * (u : Int)])))
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [h1]; exact decide_eq_true rfl))]
    exact sign_pick hx hc_lt hx0 (pm_x hp hv0 (sm (by ring_mod [(ms hvc) * 1, (ms he) * (u : Int),
      (ms hvx) * (-1)])))
  · have hn1 : ¬ (v * c % Ed25519.p * c % Ed25519.p = u) := by
      intro h1
      have m : MEq Ed25519.p (2 * (u : Int)) 0 := by
        have m1 := hvcN
        rw [h1] at m1
        exact sm (by ring_mod [(ms m1) * 1, (ms hvc) * 1, (ms he) * (u : Int)])
      rcases hp.meq_mul_zero m with m | m
      · exact two_ne m
      · exact hxn (by
          rcases hp.meq_mul_zero (sm (by ring_mod [(ms hvx) * 1, (ms m) * 1]) :
            MEq Ed25519.p ((v : Int) * x * x) 0) with m' | m'
          · rcases hp.meq_mul_zero m' with m'' | m''
            · exact absurd m'' hv0
            · exact m''
          · exact m')
    have hpu : ((Ed25519.p - u) % Ed25519.p : Nat) < Ed25519.p := Nat.mod_lt _ p_pos
    have h2 : v * c % Ed25519.p * c % Ed25519.p = (Ed25519.p - u) % Ed25519.p := by
      refine nat_of_meq hlt hpu (hvcN.trans ?_)
      refine (?_ : MEq Ed25519.p ((v : Int) * c * c) (-(u : Int))).trans ?_
      · exact sm (by ring_mod [(ms hvc) * 1, (ms he) * (u : Int)])
      · refine MEq.symm ((natMod _ _).trans ?_)
        rw [Int.natCast_sub (Nat.le_of_lt hu_lt)]
        exact sm (by ring_mod [p_sub * 1])
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [beq_eq_false_iff_ne.mpr hn1]; exact Bool.false_ne_true)),
      ite_eq_left_of_eq_true _ _ (eq_true (by rw [h2]; exact decide_eq_true rfl))]
    have hci : MEq Ed25519.p ((c * i % Ed25519.p : Nat) : Int) ((c : Int) * i) := by
      refine (natMod _ _).trans ?_
      push_cast
      exact MEq.refl _
    exact sign_pick hx (Nat.mod_lt _ p_pos) hx0 (pm_x hp hv0 (sm (by
      ring_mod [(ms hci) * ((v : Int) * (((c * i % Ed25519.p : Nat) : Int)) + (v : Int) * c * i),
        (ms hvc) * ((i : Int) * i), (ms he) * ((u : Int) * i * i), hi * (-(u : Int)), (ms hvx) * (-1)])))

end C3.RV32.EdM
