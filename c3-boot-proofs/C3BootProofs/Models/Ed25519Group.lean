import C3BootProofs.Spec.Ed25519

/-!
# Scalar multiplication on the Ed25519 curve, from the group laws

`EdGroupLaws` states three facts about the specification's affine addition
`Ed25519.add` on points of the curve: it stays on the curve, it is
associative, and `P + (-P)` is the neutral element. The proofs here take
them as a hypothesis. Commutativity, the neutral element, and the
negation's curve membership are proved outright. From these, the file
proves that `Ed25519.mul` is repeated addition (`mul_eq_nsmul`) and that
multiplication by an integer, `zs`, is additive in the scalar (`zs_add`).
-/

namespace C3.RV32.EdM

/-- The negation of a point, `(-x, y)`. -/
def neg (q : Nat × Nat) : Nat × Nat := ((Ed25519.p - q.1) % Ed25519.p, q.2)

/-- A point of the curve `-x² + y² = 1 + d x² y²`, with coordinates below `p`. -/
def OnCurve (q : Nat × Nat) : Prop :=
  q.1 < Ed25519.p ∧ q.2 < Ed25519.p ∧
    q.2 * q.2 % Ed25519.p = (1 + Ed25519.d * (q.1 * q.1) % Ed25519.p * (q.2 * q.2) + q.1 * q.1) % Ed25519.p

/-- **The group-law facts the Ed25519 proofs assume** about the affine
addition `Ed25519.add` on the curve. Each is a polynomial identity over
`ZMod p` once the denominators `1 ± d x₁ x₂ y₁ y₂` are known to be nonzero,
which holds on the curve because `d` is not a square modulo `p`:
- `closed`: the sum of two points of the curve is on the curve;
- `assoc`: `(P + Q) + R = P + (Q + R)` for points of the curve;
- `add_neg`: `P + (-P) = (0, 1)` for a point of the curve, which needs
  `(1 + d x² y²) * inv (1 + d x² y²) ≡ 1 (mod p)`. -/
structure EdGroupLaws : Prop where
  closed : ∀ P Q, OnCurve P → OnCurve Q → OnCurve (Ed25519.add P Q)
  assoc : ∀ P Q R, OnCurve P → OnCurve Q → OnCurve R →
    Ed25519.add (Ed25519.add P Q) R = Ed25519.add P (Ed25519.add Q R)
  add_neg : ∀ P, OnCurve P → Ed25519.add P (neg P) = Ed25519.zero

theorem p_pos : 0 < Ed25519.p := by decide

theorem one_lt_p : 1 < Ed25519.p := by decide

theorem mod4 (d a b c e n : Nat) : d * a % n * b % n * c % n * e % n = d * a * b * c * e % n := by
  simp only [Nat.mod_mul_mod]

theorem add_comm' (a b : Nat × Nat) : Ed25519.add a b = Ed25519.add b a := by
  obtain ⟨x1, y1⟩ := a
  obtain ⟨x2, y2⟩ := b
  simp only [Ed25519.add, mod4]
  rw [show Ed25519.d * x2 * x1 * y2 * y1 = Ed25519.d * x1 * x2 * y1 * y2 by
      simp only [Nat.mul_comm, Nat.mul_left_comm],
    show x2 * y1 + y2 * x1 = x1 * y2 + y1 * x2 by rw [Nat.add_comm, Nat.mul_comm x2, Nat.mul_comm y2],
    show y2 * y1 + x2 * x1 = y1 * y2 + x1 * x2 by rw [Nat.mul_comm y2, Nat.mul_comm x2]]

theorem modInv_go_one (s1 : Int) (f : Nat) (r0 : Nat) : modInv.go r0 1 0 s1 (f + 2) = s1 := by
  simp only [modInv.go, Nat.one_ne_zero, ↓reduceIte, Nat.mod_one]

theorem inv_one : Ed25519.inv 1 = 1 := by
  unfold Ed25519.inv modInv
  rw [Nat.mod_eq_of_lt one_lt_p, show 2 * Ed25519.p.log2 + 4 = (2 * Ed25519.p.log2 + 2) + 2 by omega,
    modInv_go_one 1]
  decide

theorem add_zero' (P : Nat × Nat) (h : OnCurve P) : Ed25519.add P Ed25519.zero = P := by
  obtain ⟨x, y⟩ := P
  obtain ⟨hx, hy, -⟩ := h
  simp only [Ed25519.add, Ed25519.zero, Nat.mul_zero, Nat.zero_mod, Nat.mul_one, Nat.add_zero,
    Nat.sub_zero, Nat.zero_mul, Nat.add_mod_right, Nat.mod_eq_of_lt one_lt_p, inv_one, Nat.mod_mod]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem zero_add' (P : Nat × Nat) (h : OnCurve P) : Ed25519.add Ed25519.zero P = P := by
  rw [add_comm']; exact add_zero' P h

theorem onCurve_zero : OnCurve Ed25519.zero := by
  refine ⟨p_pos, one_lt_p, ?_⟩
  simp only [Ed25519.zero, Nat.mul_zero, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]

theorem sq_neg_mod (x : Nat) (hx : x < Ed25519.p) :
    (Ed25519.p - x) % Ed25519.p * ((Ed25519.p - x) % Ed25519.p) % Ed25519.p = x * x % Ed25519.p := by
  by_cases h0 : x = 0
  · subst h0; simp only [Nat.sub_zero, Nat.mod_self, Nat.zero_mod, Nat.mul_zero]
  rw [Nat.mod_eq_of_lt (show Ed25519.p - x < Ed25519.p by omega)]
  have e : (Ed25519.p - x) * (Ed25519.p - x) + x * Ed25519.p = (Ed25519.p - x) * Ed25519.p + x * x := by
    have : Ed25519.p = (Ed25519.p - x) + x := by omega
    generalize Ed25519.p - x = a at this ⊢
    rw [this]
    simp only [Nat.mul_add, Nat.mul_comm x a]
    omega
  rw [← Nat.add_mul_mod_self_right ((Ed25519.p - x) * (Ed25519.p - x)) x, e, Nat.add_comm,
    Nat.add_mul_mod_self_right]

theorem onCurve_neg (P : Nat × Nat) (h : OnCurve P) : OnCurve (neg P) := by
  obtain ⟨x, y⟩ := P
  obtain ⟨hx, hy, he⟩ := h
  refine ⟨Nat.mod_lt _ p_pos, hy, ?_⟩
  simp only [neg] at he ⊢
  rw [he, Nat.add_mod (1 + _), Nat.add_mod (1 + _) ((Ed25519.p - x) % Ed25519.p * _), sq_neg_mod x hx,
    Nat.add_mod 1 (Ed25519.d * (x * x) % Ed25519.p * (y * y)), Nat.add_mod 1 (Ed25519.d * _ % Ed25519.p * (y * y)),
    Nat.mul_mod (Ed25519.d * (x * x) % Ed25519.p), Nat.mul_mod (Ed25519.d * _ % Ed25519.p) (y * y), Nat.mod_mod,
    Nat.mod_mod, Nat.mul_mod Ed25519.d (x * x), Nat.mul_mod Ed25519.d ((Ed25519.p - x) % Ed25519.p * _), sq_neg_mod x hx]

theorem neg_neg' (P : Nat × Nat) (h : OnCurve P) : neg (neg P) = P := by
  obtain ⟨x, y⟩ := P
  obtain ⟨hx, -, -⟩ := h
  simp only [neg, Prod.mk.injEq, and_true]
  by_cases h0 : x = 0
  · subst h0; simp only [Nat.sub_zero, Nat.mod_self]
  rw [Nat.mod_eq_of_lt (show Ed25519.p - x < Ed25519.p by omega), show Ed25519.p - (Ed25519.p - x) = x by omega,
    Nat.mod_eq_of_lt hx]

theorem neg_zero' : neg Ed25519.zero = Ed25519.zero := by
  simp only [neg, Ed25519.zero, Nat.sub_zero, Nat.mod_self]

section
variable (G : EdGroupLaws)
include G

theorem neg_add' (P : Nat × Nat) (h : OnCurve P) : Ed25519.add (neg P) P = Ed25519.zero := by
  rw [add_comm']; exact G.add_neg P h

/-- Inverses are unique. -/
theorem eq_neg_of_add (X Y : Nat × Nat) (hX : OnCurve X) (hY : OnCurve Y) (h : Ed25519.add X Y = Ed25519.zero) :
    Y = neg X := by
  have hn := onCurve_neg X hX
  calc Y = Ed25519.add (Ed25519.add (neg X) X) Y := by rw [neg_add' G X hX, zero_add' Y hY]
    _ = Ed25519.add (neg X) (Ed25519.add X Y) := G.assoc _ _ _ hn hX hY
    _ = neg X := by rw [h, add_zero' _ hn]

theorem neg_add_distrib (P Q : Nat × Nat) (hP : OnCurve P) (hQ : OnCurve Q) :
    neg (Ed25519.add P Q) = Ed25519.add (neg P) (neg Q) := by
  have hnP := onCurve_neg P hP
  have hnQ := onCurve_neg Q hQ
  have hPQ := G.closed P Q hP hQ
  refine (eq_neg_of_add G _ _ hPQ (G.closed _ _ hnP hnQ) ?_).symm
  rw [G.assoc _ _ _ hP hQ (G.closed _ _ hnP hnQ), add_comm' (neg P) (neg Q),
    ← G.assoc _ _ _ hQ hnQ hnP, G.add_neg Q hQ, zero_add' _ hnP, G.add_neg P hP]

/-- `n` times a point, by repeated addition. -/
def nsmul : Nat → Nat × Nat → Nat × Nat
  | 0, _ => Ed25519.zero
  | n + 1, q => Ed25519.add (nsmul n q) q

omit G in
theorem nsmul_zero (q : Nat × Nat) : nsmul 0 q = Ed25519.zero := rfl

omit G in
theorem nsmul_succ (n : Nat) (q : Nat × Nat) : nsmul (n + 1) q = Ed25519.add (nsmul n q) q := rfl

theorem nsmul_on (q : Nat × Nat) (hq : OnCurve q) : ∀ n, OnCurve (nsmul n q)
  | 0 => onCurve_zero
  | n + 1 => G.closed _ _ (nsmul_on q hq n) hq

omit G in
theorem nsmul_one (q : Nat × Nat) (hq : OnCurve q) : nsmul 1 q = q := zero_add' q hq

theorem nsmul_add (q : Nat × Nat) (hq : OnCurve q) (m : Nat) :
    ∀ n, nsmul (m + n) q = Ed25519.add (nsmul m q) (nsmul n q)
  | 0 => (add_zero' _ (nsmul_on G q hq m)).symm
  | n + 1 => by
    rw [← Nat.add_assoc, nsmul_succ, nsmul_add q hq m n, nsmul_succ,
      G.assoc _ _ _ (nsmul_on G q hq m) (nsmul_on G q hq n) hq]

/-- **`Ed25519.mul` is repeated addition.** -/
theorem mul_eq_nsmul (q : Nat × Nat) (hq : OnCurve q) : ∀ k, Ed25519.mul k q = nsmul k q := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rw [Ed25519.mul]
    by_cases h0 : k = 0
    · subst h0; rfl
    simp only [h0, ↓reduceIte]
    rw [ih (k / 2) (by omega), ← nsmul_add G q hq]
    split
    · rw [← nsmul_succ]; congr 1; omega
    · congr 1; omega

theorem mul_on (q : Nat × Nat) (hq : OnCurve q) (k : Nat) : OnCurve (Ed25519.mul k q) := by
  rw [mul_eq_nsmul G q hq]; exact nsmul_on G q hq k

theorem nsmul_neg (q : Nat × Nat) (hq : OnCurve q) : ∀ n, nsmul n (neg q) = neg (nsmul n q)
  | 0 => neg_zero'.symm
  | n + 1 => by
    rw [nsmul_succ, nsmul_succ, nsmul_neg q hq n, neg_add_distrib G _ _ (nsmul_on G q hq n) hq]

/-- An integer times a point. -/
def zs (z : Int) (q : Nat × Nat) : Nat × Nat :=
  match z with
  | .ofNat n => nsmul n q
  | .negSucc n => neg (nsmul (n + 1) q)

omit G in
theorem zs_ofNat (n : Nat) (q : Nat × Nat) : zs (n : Int) q = nsmul n q := rfl

theorem zs_on (q : Nat × Nat) (hq : OnCurve q) : ∀ z, OnCurve (zs z q)
  | .ofNat n => nsmul_on G q hq n
  | .negSucc n => onCurve_neg _ (nsmul_on G q hq (n + 1))

theorem zs_succ (q : Nat × Nat) (hq : OnCurve q) (z : Int) : zs (z + 1) q = Ed25519.add (zs z q) q := by
  cases z with
  | ofNat n => rfl
  | negSucc n =>
    cases n with
    | zero =>
      rw [show Int.negSucc 0 + 1 = Int.ofNat 0 by decide]
      show nsmul 0 q = Ed25519.add (neg (nsmul 1 q)) q
      rw [nsmul_one q hq, neg_add' G q hq]; rfl
    | succ m =>
      rw [show Int.negSucc (m + 1) + 1 = Int.negSucc m by omega]
      show neg (nsmul (m + 1) q) = Ed25519.add (neg (nsmul (m + 1 + 1) q)) q
      have h1 := nsmul_on G q hq (m + 1)
      rw [nsmul_succ (m + 1) q, neg_add_distrib G _ _ h1 hq,
        G.assoc _ _ _ (onCurve_neg _ h1) (onCurve_neg _ hq) hq, neg_add' G q hq, add_zero' _ (onCurve_neg _ h1)]

theorem zs_pred (q : Nat × Nat) (hq : OnCurve q) (z : Int) : zs (z - 1) q = Ed25519.add (zs z q) (neg q) := by
  cases z with
  | ofNat n =>
    cases n with
    | zero =>
      rw [show Int.ofNat 0 - 1 = Int.negSucc 0 by decide]
      show neg (nsmul (0 + 1) q) = Ed25519.add (nsmul 0 q) (neg q)
      rw [nsmul_one q hq, nsmul_zero, zero_add' _ (onCurve_neg q hq)]
    | succ n =>
      rw [show Int.ofNat (n + 1) - 1 = Int.ofNat n by simp only [Int.ofNat_eq_natCast]; omega]
      show nsmul n q = Ed25519.add (nsmul (n + 1) q) (neg q)
      rw [nsmul_succ, G.assoc _ _ _ (nsmul_on G q hq n) hq (onCurve_neg q hq), G.add_neg q hq,
        add_zero' _ (nsmul_on G q hq n)]
  | negSucc n =>
    rw [show Int.negSucc n - 1 = Int.negSucc (n + 1) by omega]
    show neg (nsmul (n + 1 + 1) q) = Ed25519.add (neg (nsmul (n + 1) q)) (neg q)
    rw [nsmul_succ (n + 1) q, neg_add_distrib G _ _ (nsmul_on G q hq (n + 1)) hq]

theorem zs_add_nat (q : Nat × Nat) (hq : OnCurve q) (a : Int) :
    ∀ n : Nat, zs (a + n) q = Ed25519.add (zs a q) (zs n q)
  | 0 => by
    show zs (a + 0) q = Ed25519.add (zs a q) Ed25519.zero
    rw [Int.add_zero, add_zero' _ (zs_on G q hq a)]
  | n + 1 => by
    rw [show a + ((n + 1 : Nat) : Int) = (a + n) + 1 by omega, zs_succ G q hq, zs_add_nat q hq a n,
      show ((n + 1 : Nat) : Int) = (n : Int) + 1 by omega, zs_succ G q hq,
      G.assoc _ _ _ (zs_on G q hq a) (zs_on G q hq _) hq]

theorem zs_add_neg (q : Nat × Nat) (hq : OnCurve q) (a : Int) :
    ∀ n : Nat, zs (a + Int.negSucc n) q = Ed25519.add (zs a q) (zs (Int.negSucc n) q)
  | 0 => by
    rw [show a + Int.negSucc 0 = a - 1 by omega, zs_pred G q hq]
    show _ = Ed25519.add (zs a q) (neg (nsmul (0 + 1) q))
    rw [nsmul_one q hq]
  | n + 1 => by
    rw [show a + Int.negSucc (n + 1) = (a + Int.negSucc n) - 1 by omega, zs_pred G q hq, zs_add_neg q hq a n,
      show Int.negSucc (n + 1) = Int.negSucc n - 1 by omega, zs_pred G q hq,
      G.assoc _ _ _ (zs_on G q hq a) (zs_on G q hq _) (onCurve_neg q hq)]

/-- **Integer multiplication is additive in the scalar.** -/
theorem zs_add (q : Nat × Nat) (hq : OnCurve q) (a b : Int) : zs (a + b) q = Ed25519.add (zs a q) (zs b q) := by
  cases b with
  | ofNat n => exact zs_add_nat G q hq a n
  | negSucc n => exact zs_add_neg G q hq a n

omit G in
theorem zs_neg_one (q : Nat × Nat) (hq : OnCurve q) : zs (-1) q = neg q := by
  show neg (nsmul 1 q) = neg q
  rw [nsmul_one q hq]

omit G in
theorem zs_negPt (q : Nat × Nat) (n : Nat) : zs (-(n : Int)) q = neg (nsmul n q) := by
  cases n with
  | zero => show nsmul 0 q = neg (nsmul 0 q); rw [nsmul_zero, neg_zero']
  | succ n => rfl

/-- The verification equation, rearranged: if `[s]B + [k](-A) = R`, then
`[s]B = R + [k]A`. -/
theorem verify_rearrange (A Bp R : Nat × Nat) (hA : OnCurve A) (hB : OnCurve Bp) (k s : Nat)
    (h : Ed25519.add (nsmul k (neg A)) (nsmul s Bp) = R) :
    Ed25519.mul s Bp = Ed25519.add R (Ed25519.mul k A) := by
  rw [mul_eq_nsmul G _ hB, mul_eq_nsmul G _ hA, ← h, nsmul_neg G A hA]
  have hk := nsmul_on G A hA k
  have hs := nsmul_on G Bp hB s
  rw [add_comm' (neg _), G.assoc _ _ _ hs (onCurve_neg _ hk) hk, neg_add' G _ hk, add_zero' _ hs]

end

end C3.RV32.EdM
