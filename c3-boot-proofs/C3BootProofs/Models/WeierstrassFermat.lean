import C3BootProofs.Models.EcdsaField

/-!
Fermat's little theorem, `a ^ p ≡ a (mod p)` for prime `p`, from Pascal's
binomial coefficients.
-/

namespace C3.Models

/-- Pascal's binomial coefficients. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

theorem binom_succ_succ (n k : Nat) : binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by cases n <;> rfl

theorem binom_eq_zero : ∀ {n k : Nat}, n < k → binom n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | _ + 1, _ + 1, h => by
    rw [binom_succ_succ, binom_eq_zero (by omega), binom_eq_zero (by omega)]

theorem binom_self : ∀ n : Nat, binom n n = 1
  | 0 => rfl
  | n + 1 => by rw [binom_succ_succ, binom_self n, binom_eq_zero (Nat.lt_succ_self n)]

theorem binom_one_right : ∀ n : Nat, binom n 1 = n
  | 0 => rfl
  | n + 1 => by rw [binom_succ_succ, binom_zero_right, binom_one_right n, Nat.add_comm]

/-- `(k + 1) C(n + 1, k + 1) = (n + 1) C(n, k)`. -/
theorem succ_mul_binom : ∀ n k : Nat, (k + 1) * binom (n + 1) (k + 1) = (n + 1) * binom n k
  | 0, 0 => rfl
  | 0, k + 1 => by
    rw [binom_eq_zero (by omega : 0 + 1 < k + 1 + 1), binom_eq_zero (by omega : 0 < k + 1), Nat.mul_zero,
      Nat.mul_zero]
  | n + 1, 0 => by rw [binom_one_right, binom_zero_right, Nat.one_mul, Nat.mul_one]
  | n + 1, k + 1 => by
    have h1 := succ_mul_binom n k
    have h2 := succ_mul_binom n (k + 1)
    have h3 := binom_succ_succ n k
    have h4 : n * binom (n + 1) (k + 1) = n * binom n k + n * binom n (k + 1) := by
      rw [h3, Nat.mul_add]
    rw [binom_succ_succ (n + 1) (k + 1)]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul] at h1 h2 h3 ⊢
    omega

theorem binom_prime {p k : Nat} (hp : IsPrime p) (hk0 : 0 < k) (hkp : k < p) :
    binom p k % p = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h : MEq (n + 1) (((j + 1 : Nat) : Int) * (binom (n + 1) (j + 1) : Nat)) 0 := by
    rw [← Int.natCast_mul, succ_mul_binom, Int.natCast_mul]
    exact MEq.zero_iff.mpr (Int.dvd_mul_right _ _)
  rcases hp.meq_mul_zero h with h | h
  · have := MEq.natCast.mp h
    rw [Nat.zero_mod, Nat.mod_eq_of_lt hkp] at this
    omega
  · have := MEq.natCast.mp h
    rwa [Nat.zero_mod] at this

/-- The first `m` terms of the binomial expansion of `(a + 1) ^ n`. -/
def bsum (n a : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => bsum n a m + binom n m * a ^ m

theorem bsum_succ (n a m : Nat) : bsum (n + 1) a (m + 1) = bsum n a (m + 1) + a * bsum n a m := by
  induction m with
  | zero => simp only [bsum, binom_zero_right, Nat.mul_zero, Nat.add_zero]
  | succ m ih =>
    have e : a * (binom n m * a ^ m) = binom n m * a ^ (m + 1) := by
      rw [Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm a]
    show bsum (n + 1) a (m + 1) + binom (n + 1) (m + 1) * a ^ (m + 1) =
      (bsum n a (m + 1) + binom n (m + 1) * a ^ (m + 1)) + a * (bsum n a m + binom n m * a ^ m)
    rw [ih, binom_succ_succ, Nat.mul_add a, e, Nat.add_mul]
    omega

theorem pow_eq_bsum (n a : Nat) : (a + 1) ^ n = bsum n a (n + 1) := by
  induction n with
  | zero => simp only [bsum, binom_zero_right, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  | succ n ih =>
    rw [bsum_succ, bsum, binom_eq_zero (Nat.lt_succ_self n), Nat.zero_mul, Nat.add_zero,
      Nat.pow_succ, ih, Nat.mul_add, Nat.mul_one, Nat.mul_comm, Nat.add_comm]
    omega

theorem bsum_prime {p : Nat} (hp : IsPrime p) (a : Nat) :
    ∀ m, 1 ≤ m → m ≤ p → bsum p a m % p = 1 % p
  | 0, h, _ => absurd h (by decide)
  | m + 1, _, hm => by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · simp only [bsum, binom_zero_right, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    · rw [bsum, Nat.add_mod, Nat.mul_mod, binom_prime hp h0 (by omega), Nat.zero_mul,
        Nat.zero_mod, Nat.add_zero, Nat.mod_mod, bsum_prime hp a m h0 (by omega)]

/-- Fermat's little theorem. -/
theorem fermat_nat {p : Nat} (hp : IsPrime p) : ∀ a : Nat, a ^ p % p = a % p
  | 0 => by rw [Nat.zero_pow hp.pos]
  | a + 1 => by
    rw [pow_eq_bsum, bsum, binom_self, Nat.one_mul, Nat.add_mod, fermat_nat hp a,
      bsum_prime hp a p (Nat.succ_le_of_lt hp.pos) (Nat.le_refl _), ← Nat.add_mod, Nat.add_comm]

theorem fermat {p : Nat} (hp : IsPrime p) (a : Nat) : MEq p ((a : Int) ^ p) a := by
  have := MEq.natCast.mpr (fermat_nat hp a)
  rwa [Int.natCast_pow] at this

end C3.Models
