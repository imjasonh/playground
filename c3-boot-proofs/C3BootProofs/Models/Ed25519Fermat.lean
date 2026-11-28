import C3BootProofs.Ring.Tactic
import C3BootProofs.Models.EcdsaField
import C3BootProofs.Models.Ed25519Field

/-!
# Fermat's little theorem, and `d` is not a square modulo `p`

`powMod` computes `a ^ e % m`. Fermat's little theorem follows from the
binomial theorem for `(a + 1) ^ p`, with binomial coefficients defined here
by Pascal's rule. With it, the kernel's evaluation of
`d ^ ((p - 1) / 2) % p = p - 1` (Euler's criterion) shows that `d` has no
square root modulo a prime `p`.
-/

namespace C3.RV32.EdM

open C3.Models

theorem powModF_eq : ∀ f a e m, e < 2 ^ f → powModF f a e m = a ^ e % m
  | 0, a, e, m, h => by
    have : e = 0 := by omega
    subst this; rfl
  | f + 1, a, e, m, h => by
    have h2 : e / 2 < 2 ^ f := by
      have : 2 ^ (f + 1) = 2 ^ f * 2 := Nat.pow_succ _ _
      omega
    have hr := powModF_eq f (a * a % m) (e / 2) m h2
    have hsq : (a * a) ^ (e / 2) = a ^ (2 * (e / 2)) := by rw [← Nat.pow_two, ← Nat.pow_mul]
    rw [← Nat.pow_mod, hsq] at hr
    by_cases he : e = 0
    · subst he; simp only [powModF, ↓reduceIte, Nat.pow_zero]
    · simp only [powModF, he, ↓reduceIte]
      by_cases ho : e % 2 = 1
      · simp only [ho, ↓reduceIte]
        rw [hr, Nat.mod_mul_mod, ← Nat.pow_succ]
        congr 2; omega
      · simp only [ho, ↓reduceIte]
        rw [hr]
        congr 2; omega

theorem powMod_eq (a e m : Nat) : powMod a e m = a ^ e % m := by
  rw [powMod_F e a e m Nat.lt_two_pow_self, powModF_eq e a e m Nat.lt_two_pow_self]

/-- Binomial coefficients by Pascal's rule. -/
def ch : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => ch n k + ch n (k + 1)

theorem ch_zero_right (n : Nat) : ch n 0 = 1 := by cases n <;> rfl

theorem ch_zero_succ (k : Nat) : ch 0 (k + 1) = 0 := rfl

theorem ch_succ_succ (n k : Nat) : ch (n + 1) (k + 1) = ch n k + ch n (k + 1) := rfl

theorem ch_eq_zero : ∀ n k, n < k → ch n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [ch_succ_succ, ch_eq_zero n k (by omega), ch_eq_zero n (k + 1) (by omega)]

theorem ch_self : ∀ n, ch n n = 1
  | 0 => rfl
  | n + 1 => by rw [ch_succ_succ, ch_self n, ch_eq_zero n (n + 1) (by omega)]

theorem ch_one : ∀ n, ch n 1 = n
  | 0 => rfl
  | n + 1 => by rw [ch_succ_succ, ch_one n, ch_zero_right]; omega

theorem ch_absorb : ∀ n k, ch (n + 1) (k + 1) * (k + 1) = (n + 1) * ch n k
  | 0, 0 => rfl
  | 0, k + 1 => by rw [ch_succ_succ, ch_zero_succ, ch_zero_succ]; simp only [Nat.zero_add, Nat.zero_mul, Nat.mul_zero]
  | n + 1, 0 => by
    rw [ch_succ_succ, ch_one, ch_zero_right]; omega
  | n + 1, j + 1 => by
    have h1 := ch_absorb n j
    have h2 := ch_absorb n (j + 1)
    have hC := ch_succ_succ n j
    rw [ch_succ_succ (n + 1) (j + 1)]
    calc (ch (n + 1) (j + 1) + ch (n + 1) (j + 1 + 1)) * (j + 1 + 1)
        = ch (n + 1) (j + 1) * (j + 1) + ch (n + 1) (j + 1) + ch (n + 1) (j + 1 + 1) * (j + 1 + 1) := by
          ring_eq
      _ = (n + 1) * ch n j + (ch n j + ch n (j + 1)) + (n + 1) * ch n (j + 1) := by rw [h1, h2, ← hC]
      _ = (n + 1 + 1) * (ch n j + ch n (j + 1)) := by ring_eq
      _ = (n + 1 + 1) * ch (n + 1) (j + 1) := by rw [hC]

/-- `bs f n` is `f 0 + … + f (n - 1)`. -/
def bs (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bs f n + f n

theorem bs_shift (f : Nat → Nat) : ∀ n, bs f (n + 1) = f 0 + bs (fun k => f (k + 1)) n
  | 0 => by simp only [bs, Nat.add_zero, Nat.zero_add]
  | n + 1 => by
    rw [bs, bs_shift f n, bs, Nat.add_assoc]

theorem bs_add (f g : Nat → Nat) : ∀ n, bs (fun k => f k + g k) n = bs f n + bs g n
  | 0 => rfl
  | n + 1 => by
    simp only [bs, bs_add f g n]; omega

theorem bs_mul (c : Nat) (f : Nat → Nat) : ∀ n, bs (fun k => c * f k) n = c * bs f n
  | 0 => rfl
  | n + 1 => by simp only [bs, bs_mul c f n, Nat.mul_add]

theorem bs_congr {f g : Nat → Nat} : ∀ n, (∀ k, k < n → f k = g k) → bs f n = bs g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [bs]; rw [bs_congr n (fun k hk => h k (by omega)), h n (by omega)]

theorem bs_dvd (q : Nat) {f : Nat → Nat} : ∀ n, (∀ k, k < n → q ∣ f k) → q ∣ bs f n
  | 0, _ => Nat.dvd_zero q
  | n + 1, h => Nat.dvd_add (bs_dvd q n (fun k hk => h k (by omega))) (h n (by omega))

theorem binom (a : Nat) : ∀ n, (a + 1) ^ n = bs (fun k => ch n k * a ^ k) (n + 1)
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, binom a n, bs_shift (fun k => ch (n + 1) k * a ^ k) (n + 1)]
    have e1 : bs (fun k => ch (n + 1) (k + 1) * a ^ (k + 1)) (n + 1) =
        bs (fun k => a * (ch n k * a ^ k)) (n + 1) + bs (fun k => ch n (k + 1) * a ^ (k + 1)) (n + 1) := by
      rw [← bs_add]
      apply bs_congr; intro k _
      rw [ch_succ_succ, Nat.pow_succ]; ring_eq
    have e2 : 1 + bs (fun k => ch n (k + 1) * a ^ (k + 1)) (n + 1) = bs (fun k => ch n k * a ^ k) (n + 1 + 1) := by
      rw [bs_shift (fun k => ch n k * a ^ k) (n + 1), ch_zero_right, Nat.pow_zero]
    have e3 : bs (fun k => ch n k * a ^ k) (n + 1 + 1) = bs (fun k => ch n k * a ^ k) (n + 1) := by
      rw [bs, ch_eq_zero n (n + 1) (by omega), Nat.zero_mul, Nat.add_zero]
    show bs (fun k => ch n k * a ^ k) (n + 1) * (a + 1) =
      ch (n + 1) 0 * a ^ 0 + bs (fun k => ch (n + 1) (k + 1) * a ^ (k + 1)) (n + 1)
    rw [e1, bs_mul]
    rw [ch_zero_right, Nat.pow_zero]
    have e4 := e2.trans e3
    have e5 : bs (fun k => ch n k * a ^ k) (n + 1) * (a + 1) =
        a * bs (fun k => ch n k * a ^ k) (n + 1) + bs (fun k => ch n k * a ^ k) (n + 1) := by ring_eq
    omega

theorem prime_dvd_ch {q : Nat} (hq : IsPrime q) (k : Nat) (h0 : 0 < k) (hk : k < q) : q ∣ ch q k := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by have := hq.1; omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hd : n + 1 ∣ ch (n + 1) (j + 1) * (j + 1) := by rw [ch_absorb]; exact Nat.dvd_mul_right _ _
  rcases hq.dvd_mul hd with h | h
  · exact h
  · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

theorem bs_ends (f : Nat → Nat) (n : Nat) : bs f (n + 2) = f 0 + bs (fun k => f (k + 1)) n + f (n + 1) := by
  rw [show n + 2 = n + 1 + 1 from rfl, bs, bs_shift]

theorem frob {q : Nat} (hq : IsPrime q) (a : Nat) : (a + 1) ^ q % q = (a ^ q + 1) % q := by
  have h2 := hq.1
  rw [binom a q, show q + 1 = q - 1 + 2 by omega, bs_ends]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ q), ch_self, ch_zero_right]
  have hm : q ∣ bs (fun k => ch q (k + 1) * a ^ (k + 1)) (q - 1) := by
    apply bs_dvd; intro k hk
    exact Nat.dvd_trans (prime_dvd_ch hq (k + 1) (by omega) (by omega)) (Nat.dvd_mul_right _ _)
  obtain ⟨c, hc⟩ := hm
  rw [hc]
  have : 1 * a ^ 0 + q * c + 1 * a ^ q = (a ^ q + 1) + q * c := by rw [Nat.pow_zero]; ring_eq
  rw [this, Nat.add_mul_mod_self_left]

theorem fermat_pow {q : Nat} (hq : IsPrime q) : ∀ a, a ^ q % q = a % q
  | 0 => by rw [Nat.zero_pow (by have := hq.1; omega)]
  | a + 1 => by rw [frob hq, Nat.add_mod, fermat_pow hq a, ← Nat.add_mod]

theorem fermat {q : Nat} (hq : IsPrime q) (a : Nat) (ha : a % q ≠ 0) : a ^ (q - 1) % q = 1 := by
  have h1 : MEq q (((a ^ (q - 1) : Nat) : Int) * (a : Int)) (1 * (a : Int)) := by
    rw [Int.mul_comm, Int.mul_comm 1]
    have : q - 1 + 1 = q := by have := hq.1; omega
    rw [Int.mul_one, ← Int.natCast_mul, MEq.natCast, ← Nat.pow_succ', Nat.succ_eq_add_one, this, fermat_pow hq]
  have hne : ¬ MEq q (a : Int) 0 := by
    intro h; rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, MEq.natCast] at h; exact ha h
  have h2 := hq.meq_cancel hne h1
  rw [show (1 : Int) = ((1 : Nat) : Int) from rfl, MEq.natCast] at h2
  rw [h2]; exact Nat.mod_eq_of_lt (by have := hq.1; omega)

theorem d_eq : Ed25519.d = 37095705934669439343138083508754565189542113879843219016388785533085940283555 := by decide

theorem d_lt : Ed25519.d < Ed25519.p := by rw [d_eq]; decide

theorem euler_d : Ed25519.d ^ ((Ed25519.p - 1) / 2) % Ed25519.p = Ed25519.p - 1 := by
  rw [← powMod_eq, powMod_F 256 _ _ _ (by decide), d_eq]
  decide +kernel

/-- `d` has no square root modulo `p`. -/
theorem d_nonsq (hp : IsPrime Ed25519.p) (z : Nat) : z * z % Ed25519.p ≠ Ed25519.d := by
  intro h
  have hz : z % Ed25519.p ≠ 0 := by
    intro h0
    rw [Nat.mul_mod, h0, Nat.zero_mul, Nat.zero_mod, d_eq] at h
    exact absurd h (by decide)
  have hf := fermat hp z hz
  have e : (z * z) ^ ((Ed25519.p - 1) / 2) = z ^ (Ed25519.p - 1) := by
    rw [← Nat.pow_two, ← Nat.pow_mul]; rfl
  have := euler_d
  rw [← h, ← Nat.pow_mod, e, hf] at this
  exact absurd this (by decide)

/-- `d` has no square root modulo `p`, over `Int`. -/
theorem d_nonsq_int (hp : IsPrime Ed25519.p) (z : Int) : ¬ MEq Ed25519.p (z * z) (Ed25519.d : Int) := by
  intro h
  have hp0 : (0 : Int) < (Ed25519.p : Int) := by decide
  have hz : z % (Ed25519.p : Int) = (((z % (Ed25519.p : Int)).toNat : Nat) : Int) :=
    (Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hp0))).symm
  have h1 : MEq Ed25519.p (z * z) (((z % (Ed25519.p : Int)).toNat * (z % (Ed25519.p : Int)).toNat : Nat) : Int) := by
    rw [Int.natCast_mul, ← hz]; exact (MEq.mul (MEq.emod z) (MEq.emod z)).symm
  have h2 := (h1.symm.trans h)
  rw [MEq.natCast, Nat.mod_eq_of_lt d_lt] at h2
  exact d_nonsq hp _ h2

end C3.RV32.EdM
