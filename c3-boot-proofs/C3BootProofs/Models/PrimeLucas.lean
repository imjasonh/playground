import C3BootProofs.Models.EcdsaField

/-!
# Lucas's primality test

`p` is prime when some `a` has `a ^ (p - 1) ≡ 1 (mod p)` and
`a ^ ((p - 1) / q) ≢ 1 (mod p)` for every prime `q` dividing `p - 1`: then
`a` has order `p - 1`, so its powers are `p - 1` distinct residues, none
sharing a factor with `p`, which leaves no room for a proper divisor.

`checkLucas` decides the test's arithmetic for a given factorization of
`p - 1`, with `powModS`, modular exponentiation by structural recursion
that the kernel evaluates. A Pratt certificate is that check plus a
certificate for each prime of the factorization.
-/

namespace C3.Models

/-! ## Pigeonhole -/

/-- `n` values below `m`, pairwise distinct, need `n ≤ m`. -/
theorem pigeonhole : ∀ (n m : Nat) (f : Nat → Nat), (∀ k, k < n → f k < m) →
    (∀ i j, i < n → j < n → f i = f j → i = j) → n ≤ m
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, m, f, hr, hi => by
    have hv := hr n (Nat.lt_succ_self n)
    have hne : ∀ k, k < n → f k ≠ f n := fun k hk h =>
      Nat.ne_of_lt hk (hi k n (Nat.lt_succ_of_lt hk) (Nat.lt_succ_self n) h)
    have h := pigeonhole n (m - 1) (fun k => if f k < f n then f k else f k - 1)
      (fun k hk => by
        have h1 := hr k (Nat.lt_succ_of_lt hk)
        have h2 := hne k hk
        show (if f k < f n then f k else f k - 1) < m - 1
        split <;> omega)
      (fun i j hi' hj' h => by
        have h1 := hne i hi'
        have h2 := hne j hj'
        apply hi i j (Nat.lt_succ_of_lt hi') (Nat.lt_succ_of_lt hj')
        revert h
        show (if f i < f n then f i else f i - 1) = (if f j < f n then f j else f j - 1) → f i = f j
        split <;> split <;> omega)
    omega

/-! ## Modular exponentiation -/

/-- `r * b ^ e % m` when `e ≤ fuel` and `r < m`: square-and-multiply on the
bits of `e`, structurally recursive on `fuel`. -/
def powModAux : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, r => r
  | fuel + 1, b, e, m, r =>
    if e = 0 then r
    else powModAux fuel (b * b % m) (e / 2) m (if e % 2 = 1 then r * b % m else r)

/-- `a ^ e % m`. -/
def powModS (a e m : Nat) : Nat := powModAux e a e m (1 % m)

theorem mul_mod_congr_left {x y m : Nat} (z : Nat) (h : x % m = y % m) : x * z % m = y * z % m := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

theorem powModAux_spec (m : Nat) : ∀ fuel b e r, e ≤ fuel → r % m = r →
    powModAux fuel b e m r = r * b ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e r he hr
    rw [Nat.le_zero.mp he, Nat.pow_zero, Nat.mul_one, hr]; rfl
  | succ fuel ih =>
    intro b e r he hr
    simp only [powModAux]
    by_cases h0 : e = 0
    · rw [ite_eq_left h0, h0, Nat.pow_zero, Nat.mul_one, hr]
    rw [ite_eq_right h0]
    have hb : (b * b % m) ^ (e / 2) % m = (b * b) ^ (e / 2) % m := (Nat.pow_mod _ _ _).symm
    have hsq : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
      rw [Nat.pow_mul, Nat.pow_two]
    by_cases h1 : e % 2 = 1
    · rw [ite_eq_left h1, ih _ _ _ (by omega) (Nat.mod_mod _ _)]
      have he2 : e = 2 * (e / 2) + 1 := by omega
      calc r * b % m * (b * b % m) ^ (e / 2) % m
          = r * b % m * ((b * b % m) ^ (e / 2) % m) % m := by rw [Nat.mul_mod_mod]
        _ = r * b % m * ((b * b) ^ (e / 2) % m) % m := by rw [hb]
        _ = r * b * (b * b) ^ (e / 2) % m := by rw [Nat.mul_mod_mod, Nat.mod_mul_mod]
        _ = r * b ^ e % m := by
          have hbe : b ^ e = (b * b) ^ (e / 2) * b := by
            rw [hsq, ← Nat.pow_succ]; exact congrArg _ he2
          rw [hbe, Nat.mul_assoc, Nat.mul_comm b]
    · rw [ite_eq_right h1, ih _ _ _ (by omega) hr]
      have he2 : e = 2 * (e / 2) := by omega
      calc r * (b * b % m) ^ (e / 2) % m
          = r * ((b * b % m) ^ (e / 2) % m) % m := by rw [Nat.mul_mod_mod]
        _ = r * ((b * b) ^ (e / 2) % m) % m := by rw [hb]
        _ = r * b ^ e % m := by rw [Nat.mul_mod_mod, hsq, ← he2]

theorem powModS_eq (a e m : Nat) : powModS a e m = a ^ e % m := by
  unfold powModS
  rw [powModAux_spec m e a e (1 % m) (Nat.le_refl e) (Nat.mod_mod _ _), ← Nat.mod_mul_mod, Nat.mod_mod,
    Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.one_mul]

/-! ## Powers congruent to 1 -/

section Powers

variable {a p : Nat}

theorem mul_mod_of_mod_one {x y : Nat} (h : x % p = 1) : x * y % p = y % p := by
  rw [Nat.mul_mod, h, Nat.one_mul, Nat.mod_mod]

theorem pow_mul_mod_one (hp : 2 ≤ p) {x : Nat} (k : Nat) (h : a ^ x % p = 1) : a ^ (x * k) % p = 1 := by
  rw [Nat.pow_mul, Nat.pow_mod, h, Nat.one_pow, Nat.mod_eq_of_lt hp]

theorem pow_mod_mod_one (hp : 2 ≤ p) {x y : Nat} (hx : a ^ x % p = 1) (hy : a ^ y % p = 1) :
    a ^ (x % y) % p = 1 := by
  have e : a ^ x = a ^ (y * (x / y)) * a ^ (x % y) := by rw [← Nat.pow_add, Nat.div_add_mod]
  rw [e, mul_mod_of_mod_one (pow_mul_mod_one hp _ hy)] at hx
  exact hx

theorem pow_gcd_mod_one (hp : 2 ≤ p) (x y : Nat) :
    a ^ x % p = 1 → a ^ y % p = 1 → a ^ Nat.gcd x y % p = 1 :=
  Nat.gcd.induction (P := fun x y => a ^ x % p = 1 → a ^ y % p = 1 → a ^ Nat.gcd x y % p = 1) x y
    (fun n _ hn => by rw [Nat.gcd_zero_left]; exact hn)
    (fun m n _ ih hm hn => by rw [Nat.gcd_rec]; exact ih (pow_mod_mod_one hp hn hm) hm)

end Powers

/-! ## Factorizations -/

/-- The number a factorization `[(q₁, e₁), …]` stands for: `q₁ ^ e₁ * …`. -/
def fprod : List (Nat × Nat) → Nat
  | [] => 1
  | (q, e) :: r => q ^ e * fprod r

/-- Every base of a factorization is prime. -/
def AllPrime : List (Nat × Nat) → Prop
  | [] => True
  | (q, _) :: r => IsPrime q ∧ AllPrime r

/-- A divisor above 1 of a product of primes shares one of them. -/
theorem exists_base_dvd : ∀ (fs : List (Nat × Nat)) (m : Nat), AllPrime fs → m ∣ fprod fs → 2 ≤ m →
    ∃ q e, (q, e) ∈ fs ∧ q ∣ m
  | [], m, _, hd, hm => absurd (Nat.le_of_dvd Nat.one_pos hd) (by omega)
  | (q, e) :: r, m, ⟨hq, hr⟩, hd, hm => by
    by_cases h : m % q = 0
    · exact ⟨q, e, List.Mem.head _, Nat.dvd_of_mod_eq_zero h⟩
    · have hc : Nat.Coprime m (q ^ e) := Nat.Coprime.pow_right e (hq.coprime h)
      obtain ⟨q', e', hm', hd'⟩ := exists_base_dvd r m hr (hc.dvd_of_dvd_mul_left hd) hm
      exact ⟨q', e', List.Mem.tail _ hm', hd'⟩

/-! ## Lucas's theorem -/

/-- No power of `a` from 1 through `p - 2` is 1 modulo `p`. -/
theorem pow_ne_one_of_lucas {p a : Nat} (fs : List (Nat × Nat)) (hp : 2 ≤ p) (hall : AllPrime fs)
    (hprod : fprod fs = p - 1) (hf : a ^ (p - 1) % p = 1)
    (hq : ∀ q e, (q, e) ∈ fs → a ^ ((p - 1) / q) % p ≠ 1) :
    ∀ k, 0 < k → k < p - 1 → a ^ k % p ≠ 1 := by
  intro k hk0 hk h
  have hg := pow_gcd_mod_one hp k (p - 1) h hf
  have hgk : Nat.gcd k (p - 1) ≤ k := Nat.le_of_dvd hk0 (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd k (p - 1) := Nat.gcd_pos_of_pos_left _ hk0
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right k (p - 1)
  generalize Nat.gcd k (p - 1) = g at hg hgk hg0 hm
  have hm2 : 2 ≤ m := by
    by_cases h1 : m ≤ 1
    · have : g * m ≤ g * 1 := Nat.mul_le_mul_left g h1
      omega
    · omega
  obtain ⟨q, e, hmem, t, ht⟩ := exists_base_dvd fs m hall ⟨g, by rw [hprod, hm, Nat.mul_comm]⟩ hm2
  have hq0 : 0 < q := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.zero_mul] at ht; omega)
  have hdiv : (p - 1) / q = g * t := by
    rw [hm, ht, Nat.mul_left_comm, Nat.mul_div_cancel_left _ hq0]
  exact hq q e hmem (by rw [hdiv]; exact pow_mul_mod_one hp t hg)

/-- Lucas's test: `a` has order `p - 1` modulo `p`, so `p` is prime. -/
theorem isPrime_of_lucas {p a : Nat} (fs : List (Nat × Nat)) (hp : 2 ≤ p) (hall : AllPrime fs)
    (hprod : fprod fs = p - 1) (hf : a ^ (p - 1) % p = 1)
    (hq : ∀ q e, (q, e) ∈ fs → a ^ ((p - 1) / q) % p ≠ 1) : IsPrime p := by
  have hne := pow_ne_one_of_lucas fs hp hall hprod hf hq
  have hinj : ∀ i j, i < p - 1 → j < p - 1 → a ^ i % p = a ^ j % p → i = j := by
    have key : ∀ i j, i < j → j < p - 1 → a ^ i % p = a ^ j % p → False := by
      intro i j hij hj h
      have h1 : a ^ (p - 1 - j + i) % p = 1 := by
        rw [Nat.pow_add, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.pow_add,
          show p - 1 - j + j = p - 1 by omega, hf]
      have h2 : a ^ (j - i) % p = 1 := by
        rw [← mul_mod_of_mod_one h1, ← Nat.pow_add, show p - 1 - j + i + (j - i) = p - 1 by omega, hf]
      exact hne (j - i) (by omega) (by omega) h2
    intro i j hi hj h
    rcases Nat.lt_or_ge i j with hij | hij
    · exact (key i j hij hj h).elim
    rcases Nat.lt_or_ge j i with hji | hji
    · exact (key j i hji hi h.symm).elim
    exact Nat.le_antisymm hji hij
  refine ⟨hp, fun d hd => ?_⟩
  have hdp : d ≤ p := Nat.le_of_dvd (by omega) hd
  have hd0 : d ≠ 0 := fun h0 => by rw [h0, Nat.zero_dvd] at hd; omega
  by_cases h1 : d = 1
  · exact .inl h1
  by_cases h2 : d = p
  · exact .inr h2
  exfalso
  -- `d` divides no power of `a` below `p - 1`, so those powers avoid 0 and `d`.
  have hnd : ∀ k, k < p - 1 → ¬ d ∣ a ^ k % p := by
    intro k hk hdk
    have hda : d ∣ a ^ k := by
      have := Nat.dvd_add (Nat.dvd_trans hd (Nat.dvd_mul_right p (a ^ k / p))) hdk
      rwa [Nat.div_add_mod] at this
    have hda' : d ∣ a ^ (p - 1) := by
      rw [show p - 1 = k + (p - 1 - k) by omega, Nat.pow_add]; exact Nat.dvd_mul_right_of_dvd hda _
    have : d ∣ 1 := by
      have e := Nat.div_add_mod (a ^ (p - 1)) p
      rw [hf] at e
      exact (Nat.dvd_add_right (Nat.dvd_trans hd (Nat.dvd_mul_right _ _))).mp (e ▸ hda')
    exact h1 (Nat.eq_one_of_dvd_one this)
  have hv0 : ∀ k, k < p - 1 → a ^ k % p ≠ 0 := fun k hk h0 => hnd k hk (h0 ▸ Nat.dvd_zero d)
  have hvd : ∀ k, k < p - 1 → a ^ k % p ≠ d := fun k hk h0 => hnd k hk (h0 ▸ Nat.dvd_refl d)
  have hlt : ∀ k, a ^ k % p < p := fun k => Nat.mod_lt _ (by omega)
  have := pigeonhole (p - 1) (p - 2)
    (fun k => if a ^ k % p < d then a ^ k % p - 1 else a ^ k % p - 2)
    (fun k hk => by
      have := hv0 k hk; have := hvd k hk; have := hlt k
      show (if a ^ k % p < d then a ^ k % p - 1 else a ^ k % p - 2) < p - 2
      split <;> omega)
    (fun i j hi hj h => by
      apply hinj i j hi hj
      have := hv0 i hi; have := hvd i hi; have := hv0 j hj; have := hvd j hj
      revert h
      show (if a ^ i % p < d then a ^ i % p - 1 else a ^ i % p - 2) =
        (if a ^ j % p < d then a ^ j % p - 1 else a ^ j % p - 2) → a ^ i % p = a ^ j % p
      split <;> split <;> omega)
  omega

/-! ## The check the kernel evaluates -/

/-- `a ^ (n / q) % p ≠ 1` for each base `q`. -/
def allNe (a p n : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (q, _) :: r => decide (powModS a (n / q) p ≠ 1) && allNe a p n r

/-- Lucas's test for `p` with witness `a` and the factorization `fs` of
`p - 1`. -/
def checkLucas (p a : Nat) (fs : List (Nat × Nat)) : Bool :=
  decide (2 ≤ p) && decide (fprod fs = p - 1) && decide (powModS a (p - 1) p = 1) && allNe a p (p - 1) fs

theorem allNe_spec {a p n : Nat} : ∀ fs, allNe a p n fs = true → ∀ q e, (q, e) ∈ fs → a ^ (n / q) % p ≠ 1
  | [], _, _, _, h => nomatch h
  | (q', e') :: r, h, q, e, hm => by
    simp only [allNe, Bool.and_eq_true, decide_eq_true_eq] at h
    cases hm with
    | head => rw [← powModS_eq]; exact h.1
    | tail _ hm => exact allNe_spec r h.2 q e hm

/-- A Pratt certificate step: the check plus primality of the bases. -/
theorem isPrime_of_checkLucas (p a : Nat) (fs : List (Nat × Nat)) (h : checkLucas p a fs = true)
    (hall : AllPrime fs) : IsPrime p := by
  simp only [checkLucas, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, hprod⟩, hf⟩, hq⟩ := h
  exact isPrime_of_lucas fs hp hall hprod (by rw [← powModS_eq]; exact hf) (allNe_spec fs hq)

end C3.Models
