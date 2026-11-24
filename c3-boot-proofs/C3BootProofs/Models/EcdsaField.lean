import C3BootProofs.Spec.Ecdsa

/-!
# Arithmetic modulo a prime for the ECDSA models

Congruences of integers, the inverse `modInv` computes, and the facts a
prime modulus gives: no zero divisors, and an inverse for every nonzero
residue. Primality is the hypothesis `IsPrime p`; nothing here proves that
the curves' moduli are prime.
-/

namespace C3.Models

/-- `p` is prime: at least 2, and divisible only by 1 and itself. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- Congruence modulo `p` of integers. -/
def MEq (p : Nat) (a b : Int) : Prop := a % (p : Int) = b % (p : Int)

namespace MEq

variable {p : Nat} {a b c d : Int}

theorem refl (a : Int) : MEq p a a := rfl

theorem symm (h : MEq p a b) : MEq p b a := Eq.symm h

theorem trans (h1 : MEq p a b) (h2 : MEq p b c) : MEq p a c := Eq.trans h1 h2

theorem add (h1 : MEq p a b) (h2 : MEq p c d) : MEq p (a + c) (b + d) := by
  unfold MEq at *; rw [Int.add_emod, h1, h2, ← Int.add_emod]

theorem sub (h1 : MEq p a b) (h2 : MEq p c d) : MEq p (a - c) (b - d) := by
  unfold MEq at *; rw [Int.sub_emod, h1, h2, ← Int.sub_emod]

theorem mul (h1 : MEq p a b) (h2 : MEq p c d) : MEq p (a * c) (b * d) := by
  unfold MEq at *; rw [Int.mul_emod, h1, h2, ← Int.mul_emod]

theorem neg (h : MEq p a b) : MEq p (-a) (-b) := by
  have := (refl (p := p) 0).sub h; simpa using this

theorem emod (a : Int) : MEq p (a % (p : Int)) a := Int.emod_emod _ _

theorem of_eq (h : a = b) : MEq p a b := h ▸ refl a

theorem zero_iff : MEq p a 0 ↔ (p : Int) ∣ a := by
  unfold MEq; rw [Int.zero_emod, Int.dvd_iff_emod_eq_zero]

theorem iff_sub : MEq p a b ↔ MEq p (a - b) 0 := by
  unfold MEq; rw [Int.zero_emod]; exact Int.emod_eq_emod_iff_emod_sub_eq_zero

theorem add_mul_self (k : Int) : MEq p (a + p * k) a := by
  unfold MEq; rw [Int.add_mul_emod_self_left]

theorem natCast {x y : Nat} : MEq p x y ↔ x % p = y % p := by
  unfold MEq
  constructor
  · intro h
    exact Int.ofNat.inj (show ((x % p : Nat) : Int) = ((y % p : Nat) : Int) by
      rw [Int.natCast_emod, Int.natCast_emod]; exact h)
  · intro h; rw [← Int.natCast_emod, ← Int.natCast_emod, h]

end MEq

/-- A natural number modulo `p` is congruent to itself. -/
theorem natMod (x p : Nat) : MEq p ((x % p : Nat) : Int) x := by
  rw [Int.natCast_emod]; exact MEq.emod _

/-! ## Prime moduli -/

theorem IsPrime.pos {p : Nat} (hp : IsPrime p) : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1

theorem IsPrime.coprime {p a : Nat} (hp : IsPrime p) (ha : a % p ≠ 0) : Nat.Coprime a p := by
  rcases hp.2 _ (Nat.gcd_dvd_right a p) with h | h
  · exact h
  · exact absurd (Nat.mod_eq_zero_of_dvd (h ▸ Nat.gcd_dvd_left a p)) ha

/-- Euclid's lemma for natural numbers. -/
theorem IsPrime.dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : a % p = 0
  · exact .inl (Nat.dvd_of_mod_eq_zero ha)
  · exact .inr ((Nat.Coprime.symm (hp.coprime ha)).dvd_of_dvd_mul_left h)

/-- Euclid's lemma for integers. -/
theorem IsPrime.int_dvd_mul {p : Nat} (hp : IsPrime p) {a b : Int} (h : (p : Int) ∣ a * b) :
    (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  have h' : p ∣ a.natAbs * b.natAbs := by
    rw [← Int.natAbs_mul]; exact Int.natAbs_dvd_natAbs.mpr h |> fun h => by simpa using h
  rcases hp.dvd_mul h' with h1 | h1
  · exact .inl (Int.natAbs_dvd_natAbs.mp (by simpa using h1))
  · exact .inr (Int.natAbs_dvd_natAbs.mp (by simpa using h1))

/-- No zero divisors modulo a prime. -/
theorem IsPrime.meq_mul_zero {p : Nat} (hp : IsPrime p) {a b : Int} (h : MEq p (a * b) 0) :
    MEq p a 0 ∨ MEq p b 0 := by
  rw [MEq.zero_iff, MEq.zero_iff]; exact hp.int_dvd_mul (MEq.zero_iff.mp h)

theorem IsPrime.meq_mul_ne {p : Nat} (hp : IsPrime p) {a b : Int} (ha : ¬ MEq p a 0) (hb : ¬ MEq p b 0) :
    ¬ MEq p (a * b) 0 := fun h => (hp.meq_mul_zero h).elim ha hb

/-- Cancelling a nonzero factor modulo a prime. -/
theorem IsPrime.meq_cancel {p : Nat} (hp : IsPrime p) {a b c : Int} (hc : ¬ MEq p c 0)
    (h : MEq p (a * c) (b * c)) : MEq p a b := by
  rw [MEq.iff_sub] at h ⊢
  rcases hp.meq_mul_zero (show MEq p ((a - b) * c) 0 by rw [Int.sub_mul]; exact h) with h1 | h1
  · exact h1
  · exact absurd h1 hc

/-! ## `modInv` -/

/-- What `modInv.go` keeps: each remainder is congruent to its coefficient
times `a`, and their greatest common divisor is 1. -/
def GoInv (m a r0 r1 : Nat) (s0 s1 : Int) : Prop :=
  MEq m r0 (s0 * a) ∧ MEq m r1 (s1 * a) ∧ Nat.gcd r0 r1 = 1

theorem mod_lt_half {r0 r1 : Nat} (h0 : 0 < r1) (h : r1 < r0) : 2 * (r0 % r1) < r0 := by
  by_cases hh : 2 * r1 ≤ r0
  · have := Nat.mod_lt r0 h0; omega
  · have e : r0 % r1 = r0 - r1 := by
      rw [Nat.mod_eq_sub_mod (Nat.le_of_lt h), Nat.mod_eq_of_lt (by omega)]
    omega

theorem goInv_step {m a r0 r1 : Nat} {s0 s1 : Int} (h : GoInv m a r0 r1 s0 s1) :
    GoInv m a r1 (r0 % r1) s1 (s0 - ((r0 / r1 : Nat) : Int) * s1) := by
  obtain ⟨h0, h1, hg⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · have e : ((r0 % r1 : Nat) : Int) = (r0 : Int) - ((r0 / r1 : Nat) : Int) * (r1 : Int) := by
      have h := congrArg (fun x : Nat => (x : Int)) (Nat.mod_add_div r0 r1)
      simp only [Int.natCast_add, Int.natCast_mul] at h
      rw [Int.mul_comm]; omega
    rw [e, Int.sub_mul, Int.mul_assoc]
    exact h0.sub ((MEq.refl _).mul h1)
  · rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact hg

theorem go_spec {m a : Nat} :
    ∀ k fuel r0 r1 (s0 s1 : Int), r1 < r0 → r0 < 2 ^ k → 2 * k + 1 ≤ fuel → GoInv m a r0 r1 s0 s1 →
      MEq m (modInv.go r0 r1 s0 s1 fuel * a) 1 := by
  intro k
  induction k with
  | zero => intro fuel r0 r1 s0 s1 h1 h2; exact absurd h2 (by rw [Nat.pow_zero]; omega)
  | succ k ih =>
    intro fuel r0 r1 s0 s1 hr hk hf hI
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [modInv.go]
    by_cases h1 : r1 = 0
    · rw [ite_eq_left h1]
      subst h1
      obtain ⟨h0, -, hg⟩ := hI
      rw [Nat.gcd_zero_right] at hg
      subst hg
      exact h0.symm
    rw [ite_eq_right h1]
    have hI1 := goInv_step hI
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [modInv.go]
    by_cases h2 : r0 % r1 = 0
    · rw [ite_eq_left h2]
      obtain ⟨h0, -, hg⟩ := hI1
      rw [h2, Nat.gcd_zero_right] at hg
      subst hg
      exact h0.symm
    rw [ite_eq_right h2]
    have hI2 := goInv_step hI1
    have hh := mod_lt_half (Nat.pos_of_ne_zero h1) hr
    exact ih g _ _ _ _ (Nat.mod_lt _ (Nat.pos_of_ne_zero h2)) (by rw [Nat.pow_succ] at hk; omega) (by omega) hI2

/-- `modInv a m` is an inverse of `a` modulo `m` when they are coprime. -/
theorem modInv_spec {a m : Nat} (hm : 1 < m) (hc : Nat.Coprime a m) : a * modInv a m % m = 1 := by
  have hI : GoInv m a m (a % m) 0 1 := by
    refine ⟨?_, ?_, ?_⟩
    · show (m : Int) % m = (0 * (a : Int)) % m; rw [Int.zero_mul, Int.emod_self, Int.zero_emod]
    · rw [Int.one_mul]; exact natMod a m
    · rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact hc
  have hs := go_spec (m := m) (a := a) (m.log2 + 1) (2 * m.log2 + 4) m (a % m) 0 1
    (Nat.mod_lt _ (by omega)) Nat.lt_log2_self (by omega) hI
  have hm0 : (0 : Int) < m := by omega
  unfold modInv
  generalize modInv.go m (a % m) 0 1 (2 * m.log2 + 4) = s at hs
  have hnn : 0 ≤ s % (m : Int) := Int.emod_nonneg _ (by omega)
  have e : (((s % (m : Int)).toNat : Nat) : Int) = s % m := Int.toNat_of_nonneg hnn
  have h1 : (1 : Int) % m = 1 := Int.emod_eq_of_lt (by decide) (by omega)
  have hh : MEq m ((a : Int) * (s % m)) 1 := ((MEq.refl (a : Int)).mul (MEq.emod s)).trans (by
    rw [Int.mul_comm]; exact hs)
  apply Int.ofNat.inj
  show ((a * (s % (m : Int)).toNat % m : Nat) : Int) = ((1 : Nat) : Int)
  rw [Int.natCast_emod, Int.natCast_mul, e]
  show _ = (1 : Int); rw [← h1]; exact hh

/-- `modInv a p` is the inverse of a nonzero residue modulo a prime. -/
theorem modInv_prime {a p : Nat} (hp : IsPrime p) (ha : a % p ≠ 0) :
    MEq p ((a : Int) * (modInv a p : Int)) 1 := by
  have h := modInv_spec (Nat.lt_of_lt_of_le (by decide) hp.1) (hp.coprime ha)
  have h' : MEq p ((a * modInv a p : Nat) : Int) ((1 : Nat) : Int) :=
    MEq.natCast.mpr (by rw [h, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide) hp.1)])
  rw [Int.natCast_mul] at h'; exact h'

end C3.Models
