import C3BootProofs.Models.WeierstrassRcb
import C3BootProofs.Models.WeierstrassFermat

/-!
`NoRoot` from a certificate. A root `r` of `x³ + a x + b` satisfies `r ^ p = r`, so
`x ^ p - x` vanishes at `r`. The certificate is an inverse of `x ^ p - x` modulo the
cubic, which the kernel checks by computing `x ^ p` with square-and-multiply on
residues `u₀ + u₁ x + u₂ x²`.
-/

namespace C3.Models.EC

/-- A residue `u₀ + u₁ x + u₂ x²` modulo a monic cubic. -/
abbrev Quad := Nat × Nat × Nat

/-- The value of `u` at `r`. -/
def Quad.ev (r : Int) (u : Quad) : Int := u.1 + u.2.1 * r + u.2.2 * r ^ 2

/-- The product modulo `p` and `x³ = A x + B`. -/
def Quad.mul (p A B : Nat) (u v : Quad) : Quad :=
  ((u.1 * v.1 + B * (u.2.1 * v.2.2 + u.2.2 * v.2.1)) % p,
    (u.1 * v.2.1 + u.2.1 * v.1 + A * (u.2.1 * v.2.2 + u.2.2 * v.2.1) + B * (u.2.2 * v.2.2)) % p,
    (u.1 * v.2.2 + u.2.1 * v.2.1 + u.2.2 * v.1 + A * (u.2.2 * v.2.2)) % p)

/-- `u ^ n` for `n < 2 ^ fuel`. -/
noncomputable def Quad.pow (p A B : Nat) (u : Quad) (fuel : Nat) : Nat → Quad :=
  Nat.rec (motive := fun _ => Nat → Quad) (fun _ => (1, 0, 0))
    (fun _ ih n => Bool.rec (motive := fun _ => Quad) (Quad.mul p A B (ih (n / 2)) (ih (n / 2)))
      (Quad.mul p A B (Quad.mul p A B (ih (n / 2)) (ih (n / 2))) u) (n % 2 == 1)) fuel

/-- `u - x`. -/
def Quad.subX (p : Nat) (u : Quad) : Quad := (u.1, (u.2.1 + p - 1) % p, u.2.2)

theorem quad_mod (p a b c : Nat) (r : Int) :
    MEq p (Quad.ev r (a % p, b % p, c % p)) (Quad.ev r (a, b, c)) :=
  ((natMod a p).add ((natMod b p).mul (MEq.refl _))).add
    ((natMod c p).mul (MEq.refl _))

theorem quad_mul {p A B : Nat} {r : Int} (h : MEq p (r ^ 3) (A * r + B)) (u v : Quad) :
    MEq p (Quad.ev r (Quad.mul p A B u v)) (Quad.ev r u * Quad.ev r v) := by
  obtain ⟨u0, u1, u2⟩ := u
  obtain ⟨v0, v1, v2⟩ := v
  refine (quad_mod _ _ _ _ _).trans ?_
  simp only [Quad.ev]
  curve_mod [h] []

theorem ipow_add (x : Int) (m : Nat) : ∀ n : Nat, x ^ (m + n) = x ^ m * x ^ n
  | 0 => by rw [Nat.add_zero, Int.pow_zero, Int.mul_one]
  | n + 1 => by rw [← Nat.add_assoc, Int.pow_succ, ipow_add x m n, Int.pow_succ, Int.mul_assoc]

theorem quad_pow {p A B : Nat} {r : Int} (h : MEq p (r ^ 3) (A * r + B)) (u : Quad) :
    ∀ fuel n, n < 2 ^ fuel → MEq p (Quad.ev r (Quad.pow p A B u fuel n)) (Quad.ev r u ^ n)
  | 0, n, hn => by
    obtain rfl : n = 0 := by rw [Nat.pow_zero] at hn; omega
    show MEq p (Quad.ev r (1, 0, 0)) (Quad.ev r u ^ 0)
    exact MEq.of_eq (by
      simp only [Quad.ev, Int.natCast_one, Int.natCast_zero, Int.zero_mul, Int.add_zero, Int.pow_zero])
  | fuel + 1, n, hn => by
    have ih := quad_pow h u fuel (n / 2) (by rw [Nat.pow_succ] at hn; omega)
    have hsq := (quad_mul h _ _).trans (ih.mul ih)
    show MEq p (Quad.ev r (Bool.rec _ _ (n % 2 == 1))) _
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
    · rw [h2]
      refine hsq.trans (MEq.of_eq ?_)
      rw [← ipow_add]
      congr 1
      omega
    · rw [h2]
      refine ((quad_mul h _ _).trans (hsq.mul (MEq.refl _))).trans (MEq.of_eq ?_)
      rw [← ipow_add, ← Int.pow_succ]
      congr 1
      omega

theorem quad_subX {p : Nat} (hp : 0 < p) (r : Int) (u : Quad) :
    MEq p (Quad.ev r (Quad.subX p u)) (Quad.ev r u - r) := by
  obtain ⟨u0, u1, u2⟩ := u
  have hp0 : MEq p (p : Int) 0 := MEq.zero_iff.mpr (Int.dvd_refl _)
  have e : MEq p (((u1 + p - 1) % p : Nat) : Int) (u1 - 1) := by
    refine (natMod _ _).trans ?_
    rw [Int.natCast_sub (by omega), Int.natCast_add]
    curve_mod [] [hp0 * 1]
  have e' := MEq.iff_sub.mp e
  simp only [Quad.subX, Quad.ev]
  curve_mod [] [e' * r]

theorem negMod_meq {p : Nat} (hp : 0 < p) (a : Nat) :
    MEq p (((p - a % p) % p : Nat) : Int) (-(a : Int)) := by
  refine (natMod _ _).trans ?_
  rw [Int.natCast_sub (Nat.le_of_lt (Nat.mod_lt _ hp))]
  have e := MEq.iff_sub.mp (natMod a p)
  have hp0 : MEq p (p : Int) 0 := MEq.zero_iff.mpr (Int.dvd_refl _)
  curve_mod [] [e * (-1), hp0 * 1]

/-- `NoRoot c` from an inverse `u` of `x ^ p - x` modulo `x³ + a x + b`. -/
theorem noRoot_of_cert {c : Curve} (hp : IsPrime c.p) (fuel : Nat) (hf : c.p < 2 ^ fuel)
    (u : Quad)
    (h : Quad.mul c.p ((c.p - c.a % c.p) % c.p) ((c.p - c.b % c.p) % c.p) u
        (Quad.subX c.p (Quad.pow c.p ((c.p - c.a % c.p) % c.p) ((c.p - c.b % c.p) % c.p)
          (0, 1, 0) fuel c.p)) = (1, 0, 0)) :
    NoRoot c := by
  intro x hx
  have hA := negMod_meq hp.pos c.a
  have hB := negMod_meq hp.pos c.b
  have hA' := MEq.iff_sub.mp hA
  have hB' := MEq.iff_sub.mp hB
  have h3 : MEq c.p ((x : Int) ^ 3)
      (((c.p - c.a % c.p) % c.p : Nat) * (x : Int) + ((c.p - c.b % c.p) % c.p : Nat)) := by
    curve_mod [] [hx * 1, hA' * (-(x : Int)), hB' * (-1)]
  have hg := (quad_pow h3 (0, 1, 0) fuel c.p hf)
  have e1 : Quad.ev (x : Int) (0, 1, 0) = x := by
    simp only [Quad.ev, Int.natCast_zero, Int.natCast_one, Int.zero_add, Int.one_mul,
      Int.zero_mul, Int.add_zero]
  rw [e1] at hg
  have hs := (quad_subX hp.pos (x : Int) _).trans ((hg.trans (fermat hp x)).sub (MEq.refl _))
  have hm := (quad_mul h3 u _).trans ((MEq.refl _).mul hs)
  rw [h] at hm
  refine one_ne hp ((MEq.of_eq ?_).trans (hm.trans (MEq.of_eq ?_)))
  · simp only [Quad.ev, Int.natCast_zero, Int.natCast_one, Int.zero_mul, Int.add_zero]
  · rw [Int.sub_self, Int.mul_zero]

end C3.Models.EC
