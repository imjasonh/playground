import C3BootProofs.Proofs.ScalarMont
import C3BootProofs.Spec.Ed25519
import C3BootProofs.Ring.Tactic

/-! # The value of `Scalar29::montgomery_mul`'s body

`scripts/gen-ed25519-kmont.py` writes this file from the definitions in
`ScalarMontBody.lean`. For limbs below 2^29, `smm_val` gives the value of
`smmRed a b`, the nine limbs `montgomery_reduce(mul_internal(a, b))`
returns before the final `sub`. -/

namespace C3.RV32.EdK

open C3.RV32

/-- Nine 29-bit limbs' value. -/
def sv9 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 29 * f 1 + 2 ^ 58 * f 2 + 2 ^ 87 * f 3 + 2 ^ 116 * f 4 + 2 ^ 145 * f 5 + 2 ^ 174 * f 6 + 2 ^ 203 * f 7 + 2 ^ 232 * f 8

theorem mont0 (S : Nat) : (S + (S % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 * 485872621) % 2 ^ 29 = 0 := by
  omega

theorem aa0 {a : Nat → Nat} (b : Nat → Nat) (ha : ∀ i, i < 9 → a i < 2 ^ 29) : smvAA0 a b = a 0 + a 5 :=
  Nat.mod_eq_of_lt (by have := ha 0 (by decide); have := ha 5 (by decide); omega)

theorem bb0 (a : Nat → Nat) {b : Nat → Nat} (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvBB0 a b = b 0 + b 5 :=
  Nat.mod_eq_of_lt (by have := hb 0 (by decide); have := hb 5 (by decide); omega)

theorem aa1 {a : Nat → Nat} (b : Nat → Nat) (ha : ∀ i, i < 9 → a i < 2 ^ 29) : smvAA1 a b = a 1 + a 6 :=
  Nat.mod_eq_of_lt (by have := ha 1 (by decide); have := ha 6 (by decide); omega)

theorem bb1 (a : Nat → Nat) {b : Nat → Nat} (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvBB1 a b = b 1 + b 6 :=
  Nat.mod_eq_of_lt (by have := hb 1 (by decide); have := hb 6 (by decide); omega)

theorem aa2 {a : Nat → Nat} (b : Nat → Nat) (ha : ∀ i, i < 9 → a i < 2 ^ 29) : smvAA2 a b = a 2 + a 7 :=
  Nat.mod_eq_of_lt (by have := ha 2 (by decide); have := ha 7 (by decide); omega)

theorem bb2 (a : Nat → Nat) {b : Nat → Nat} (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvBB2 a b = b 2 + b 7 :=
  Nat.mod_eq_of_lt (by have := hb 2 (by decide); have := hb 7 (by decide); omega)

theorem aa3 {a : Nat → Nat} (b : Nat → Nat) (ha : ∀ i, i < 9 → a i < 2 ^ 29) : smvAA3 a b = a 3 + a 8 :=
  Nat.mod_eq_of_lt (by have := ha 3 (by decide); have := ha 8 (by decide); omega)

theorem bb3 (a : Nat → Nat) {b : Nat → Nat} (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvBB3 a b = b 3 + b 8 :=
  Nat.mod_eq_of_lt (by have := hb 3 (by decide); have := hb 8 (by decide); omega)

section

variable {a b : Nat → Nat}

theorem kz0 : smvPA0B0 a b = a 0 * b 0 := rfl

theorem kz1 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ1 a b = a 0 * b 1 + a 1 * b 0 := by
  have p01 : a 0 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p10 : a 1 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  simp only [smvZ1, smvPA1B0, smvPA0B1]
  omega

theorem kz2 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ2 a b = a 0 * b 2 + a 1 * b 1 + a 2 * b 0 := by
  have p02 : a 0 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p11 : a 1 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p20 : a 2 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  simp only [smvZ2, smvPA2B0, smvPA1B1, smvPA0B2]
  omega

theorem kz3 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ3 a b = a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 := by
  have p03 : a 0 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p12 : a 1 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p21 : a 2 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p30 : a 3 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  simp only [smvZ3, smvPA3B0, smvPA2B1, smvPA1B2, smvPA0B3]
  omega

theorem kz4 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ4 a b = a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0 := by
  have p04 : a 0 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p13 : a 1 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p22 : a 2 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p31 : a 3 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p40 : a 4 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  simp only [smvZ4, smvPA4B0, smvPA3B1, smvPA2B2, smvPA1B3, smvPA0B4]
  omega

theorem kz5 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ5 a b = a 0 * b 5 + a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1 + a 5 * b 0 := by
  have p00 : a 0 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  have p05 : a 0 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p14 : a 1 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p23 : a 2 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p32 : a 3 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p41 : a 4 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p50 : a 5 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  have p55 : a 5 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  simp only [smvZ5, smvZ5b, smvPA0B0, smvZ10a, smvPA5B5, smvZ5a, smvPA4B1, smvPA3B2, smvPA2B3, smvPA1B4, smvPAA0BB0, aa0 b ha, bb0 a hb, Nat.add_mul, Nat.mul_add]
  omega

theorem kz6 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ6 a b = a 0 * b 6 + a 1 * b 5 + a 2 * b 4 + a 3 * b 3 + a 4 * b 2 + a 5 * b 1 + a 6 * b 0 := by
  have p01 : a 0 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p06 : a 0 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p10 : a 1 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  have p15 : a 1 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p24 : a 2 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p33 : a 3 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p42 : a 4 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p51 : a 5 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p56 : a 5 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p60 : a 6 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  have p65 : a 6 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  simp only [smvZ6, smvZ6b, smvZ1, smvPA1B0, smvPA0B1, smvZ11a, smvQ11, smvPA6B5, smvPA5B6, smvZ6a, smvPA4B2, smvPA3B3, smvPA2B4, smvK6, smvPAA1BB0, smvPAA0BB1, aa0 b ha, aa1 b ha, bb0 a hb, bb1 a hb, Nat.add_mul, Nat.mul_add]
  omega

theorem kz7 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ7 a b = a 0 * b 7 + a 1 * b 6 + a 2 * b 5 + a 3 * b 4 + a 4 * b 3 + a 5 * b 2 + a 6 * b 1 + a 7 * b 0 := by
  have p02 : a 0 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p07 : a 0 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p11 : a 1 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p16 : a 1 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p20 : a 2 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  have p25 : a 2 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p34 : a 3 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p43 : a 4 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p52 : a 5 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p57 : a 5 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p61 : a 6 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p66 : a 6 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p70 : a 7 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  have p75 : a 7 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  simp only [smvZ7, smvZ7b, smvZ2, smvPA2B0, smvPA1B1, smvPA0B2, smvZ12a, smvQ12, smvPA7B5, smvPA6B6, smvPA5B7, smvZ7a, smvPA4B3, smvPA3B4, smvK7, smvPAA2BB0, smvPAA1BB1, smvPAA0BB2, aa0 b ha, aa1 b ha, aa2 b ha, bb0 a hb, bb1 a hb, bb2 a hb, Nat.add_mul, Nat.mul_add]
  omega

theorem kz8 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ8 a b = a 0 * b 8 + a 1 * b 7 + a 2 * b 6 + a 3 * b 5 + a 4 * b 4 + a 5 * b 3 + a 6 * b 2 + a 7 * b 1 + a 8 * b 0 := by
  have p03 : a 0 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p08 : a 0 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p12 : a 1 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p17 : a 1 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p21 : a 2 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p26 : a 2 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p30 : a 3 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  have p35 : a 3 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p44 : a 4 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p53 : a 5 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p58 : a 5 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p62 : a 6 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p67 : a 6 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p71 : a 7 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p76 : a 7 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p80 : a 8 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  have p85 : a 8 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  simp only [smvZ8, smvZ8b, smvZ13, smvPA8B5, smvPA7B6, smvPA6B7, smvPA5B8, smvZ8a, smvZ3, smvPA3B0, smvPA2B1, smvPA1B2, smvPA0B3, smvPA4B4, smvK8, smvPAA3BB0, smvPAA2BB1, smvPAA1BB2, smvPAA0BB3, aa0 b ha, aa1 b ha, aa2 b ha, aa3 b ha, bb0 a hb, bb1 a hb, bb2 a hb, bb3 a hb, Nat.add_mul, Nat.mul_add]
  omega

theorem kz9 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ9 a b = a 1 * b 8 + a 2 * b 7 + a 3 * b 6 + a 4 * b 5 + a 5 * b 4 + a 6 * b 3 + a 7 * b 2 + a 8 * b 1 := by
  have p04 : a 0 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p13 : a 1 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p18 : a 1 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p22 : a 2 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p27 : a 2 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p31 : a 3 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p36 : a 3 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p40 : a 4 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  have p45 : a 4 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p54 : a 5 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p63 : a 6 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p68 : a 6 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p72 : a 7 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p77 : a 7 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p81 : a 8 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p86 : a 8 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  simp only [smvZ9, smvZ9a, smvZ4, smvPA4B0, smvPA3B1, smvPA2B2, smvPA1B3, smvPA0B4, smvZ14, smvPA8B6, smvPA7B7, smvPA6B8, smvK9, smvPA4BB0, smvPAA3BB1, smvPAA2BB2, smvPAA1BB3, smvPAA0B4, aa0 b ha, aa1 b ha, aa2 b ha, aa3 b ha, bb0 a hb, bb1 a hb, bb2 a hb, bb3 a hb, Nat.add_mul, Nat.mul_add]
  omega

theorem kz10 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ10 a b = a 2 * b 8 + a 3 * b 7 + a 4 * b 6 + a 5 * b 5 + a 6 * b 4 + a 7 * b 3 + a 8 * b 2 := by
  have p14 : a 1 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p23 : a 2 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p28 : a 2 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p32 : a 3 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p37 : a 3 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p41 : a 4 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p46 : a 4 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p55 : a 5 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p64 : a 6 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p73 : a 7 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p78 : a 7 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p82 : a 8 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p87 : a 8 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  simp only [smvZ10, smvZ10b, smvZ10a, smvPA5B5, smvZ5a, smvPA4B1, smvPA3B2, smvPA2B3, smvPA1B4, smvZ15, smvPA8B7, smvPA7B8, smvK10, smvPA4BB1, smvPAA3BB2, smvPAA2BB3, smvPAA1B4, aa1 b ha, aa2 b ha, aa3 b ha, bb1 a hb, bb2 a hb, bb3 a hb, Nat.add_mul, Nat.mul_add]
  omega

theorem kz11 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ11 a b = a 3 * b 8 + a 4 * b 7 + a 5 * b 6 + a 6 * b 5 + a 7 * b 4 + a 8 * b 3 := by
  have p24 : a 2 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p33 : a 3 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p38 : a 3 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p42 : a 4 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p47 : a 4 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p56 : a 5 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p65 : a 6 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p74 : a 7 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p83 : a 8 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p88 : a 8 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  simp only [smvZ11, smvZ11b, smvZ11a, smvQ11, smvPA6B5, smvPA5B6, smvZ6a, smvPA4B2, smvPA3B3, smvPA2B4, smvPA8B8, smvK11, smvPA4BB2, smvPAA3BB3, smvPAA2B4, aa2 b ha, aa3 b ha, bb2 a hb, bb3 a hb, Nat.add_mul, Nat.mul_add]
  omega

theorem kz12 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ12 a b = a 4 * b 8 + a 5 * b 7 + a 6 * b 6 + a 7 * b 5 + a 8 * b 4 := by
  have p34 : a 3 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p43 : a 4 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p48 : a 4 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p57 : a 5 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p66 : a 6 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p75 : a 7 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p84 : a 8 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  simp only [smvZ12, smvZ12a, smvQ12, smvPA7B5, smvPA6B6, smvPA5B7, smvZ7a, smvPA4B3, smvPA3B4, smvK12, smvPA4BB3, smvPAA3B4, aa3 b ha, bb3 a hb, Nat.add_mul, Nat.mul_add]
  omega

theorem kz13 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ13 a b = a 5 * b 8 + a 6 * b 7 + a 7 * b 6 + a 8 * b 5 := by
  have p58 : a 5 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p67 : a 6 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p76 : a 7 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p85 : a 8 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  simp only [smvZ13, smvPA8B5, smvPA7B6, smvPA6B7, smvPA5B8]
  omega

theorem kz14 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ14 a b = a 6 * b 8 + a 7 * b 7 + a 8 * b 6 := by
  have p68 : a 6 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p77 : a 7 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p86 : a 8 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  simp only [smvZ14, smvPA8B6, smvPA7B7, smvPA6B8]
  omega

theorem kz15 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ15 a b = a 7 * b 8 + a 8 * b 7 := by
  have p78 : a 7 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p87 : a 8 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  simp only [smvZ15, smvPA8B7, smvPA7B8]
  omega

theorem kz16 : smvPA8B8 a b = a 8 * b 8 := rfl

theorem kzb0 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvPA0B0 a b ≤ 1 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz0]
  have p00 : a 0 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  omega

theorem kzb1 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ1 a b ≤ 2 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz1 ha hb]
  have p01 : a 0 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p10 : a 1 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  omega

theorem kzb2 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ2 a b ≤ 3 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz2 ha hb]
  have p02 : a 0 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p11 : a 1 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p20 : a 2 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  omega

theorem kzb3 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ3 a b ≤ 4 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz3 ha hb]
  have p03 : a 0 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p12 : a 1 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p21 : a 2 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p30 : a 3 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  omega

theorem kzb4 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ4 a b ≤ 5 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz4 ha hb]
  have p04 : a 0 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p13 : a 1 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p22 : a 2 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p31 : a 3 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p40 : a 4 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  omega

theorem kzb5 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ5 a b ≤ 6 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz5 ha hb]
  have p05 : a 0 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p14 : a 1 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p23 : a 2 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p32 : a 3 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p41 : a 4 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p50 : a 5 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  omega

theorem kzb6 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ6 a b ≤ 7 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz6 ha hb]
  have p06 : a 0 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p15 : a 1 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p24 : a 2 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p33 : a 3 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p42 : a 4 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p51 : a 5 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p60 : a 6 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  omega

theorem kzb7 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ7 a b ≤ 8 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz7 ha hb]
  have p07 : a 0 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p16 : a 1 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p25 : a 2 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p34 : a 3 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p43 : a 4 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p52 : a 5 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p61 : a 6 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p70 : a 7 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  omega

theorem kzb8 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ8 a b ≤ 9 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz8 ha hb]
  have p08 : a 0 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 0 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p17 : a 1 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p26 : a 2 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p35 : a 3 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p44 : a 4 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p53 : a 5 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p62 : a 6 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p71 : a 7 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  have p80 : a 8 * b 0 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 0 (by decide)))
  omega

theorem kzb9 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ9 a b ≤ 8 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz9 ha hb]
  have p18 : a 1 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 1 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p27 : a 2 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p36 : a 3 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p45 : a 4 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p54 : a 5 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p63 : a 6 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p72 : a 7 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  have p81 : a 8 * b 1 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 1 (by decide)))
  omega

theorem kzb10 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ10 a b ≤ 7 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz10 ha hb]
  have p28 : a 2 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 2 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p37 : a 3 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p46 : a 4 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p55 : a 5 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p64 : a 6 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p73 : a 7 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  have p82 : a 8 * b 2 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 2 (by decide)))
  omega

theorem kzb11 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ11 a b ≤ 6 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz11 ha hb]
  have p38 : a 3 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 3 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p47 : a 4 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p56 : a 5 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p65 : a 6 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p74 : a 7 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  have p83 : a 8 * b 3 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 3 (by decide)))
  omega

theorem kzb12 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ12 a b ≤ 5 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz12 ha hb]
  have p48 : a 4 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 4 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p57 : a 5 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p66 : a 6 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p75 : a 7 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  have p84 : a 8 * b 4 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 4 (by decide)))
  omega

theorem kzb13 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ13 a b ≤ 4 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz13 ha hb]
  have p58 : a 5 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 5 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p67 : a 6 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p76 : a 7 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  have p85 : a 8 * b 5 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 5 (by decide)))
  omega

theorem kzb14 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ14 a b ≤ 3 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz14 ha hb]
  have p68 : a 6 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 6 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p77 : a 7 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  have p86 : a 8 * b 6 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 6 (by decide)))
  omega

theorem kzb15 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvZ15 a b ≤ 2 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz15 ha hb]
  have p78 : a 7 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 7 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  have p87 : a 8 * b 7 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 7 (by decide)))
  omega

theorem kzb16 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvPA8B8 a b ≤ 1 * ((2 ^ 29 - 1) * (2 ^ 29 - 1)) := by
  rw [kz16]
  have p88 : a 8 * b 8 ≤ (2 ^ 29 - 1) * (2 ^ 29 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt (ha 8 (by decide))) (Nat.le_pred_of_lt (hb 8 (by decide)))
  omega

theorem kn0 (a b : Nat → Nat) : smvN0 a b < 2 ^ 29 := by
  unfold smvN0; omega

theorem kn1 (a b : Nat → Nat) : smvN1 a b < 2 ^ 29 := by
  unfold smvN1; omega

theorem kn2 (a b : Nat → Nat) : smvN2 a b < 2 ^ 29 := by
  unfold smvN2; omega

theorem kn3 (a b : Nat → Nat) : smvN3 a b < 2 ^ 29 := by
  unfold smvN3; omega

theorem kn4 (a b : Nat → Nat) : smvN4 a b < 2 ^ 29 := by
  unfold smvN4; omega

theorem kn5 (a b : Nat → Nat) : smvN5 a b < 2 ^ 29 := by
  unfold smvN5; omega

theorem kn6 (a b : Nat → Nat) : smvN6 a b < 2 ^ 29 := by
  unfold smvN6; omega

theorem kn7 (a b : Nat → Nat) : smvN7 a b < 2 ^ 29 := by
  unfold smvN7; omega

theorem kn8 (a b : Nat → Nat) : smvN8 a b < 2 ^ 29 := by
  unfold smvN8; omega

theorem kc0 (a b : Nat → Nat) : smvC0 a b < 2 ^ 35 := by
  unfold smvC0 smvT0; omega

theorem kc1 (a b : Nat → Nat) : smvC1 a b < 2 ^ 35 := by
  unfold smvC1 smvT1; omega

theorem kc2 (a b : Nat → Nat) : smvC2 a b < 2 ^ 35 := by
  unfold smvC2 smvT2; omega

theorem kc3 (a b : Nat → Nat) : smvC3 a b < 2 ^ 35 := by
  unfold smvC3 smvT3; omega

theorem kc4 (a b : Nat → Nat) : smvC4 a b < 2 ^ 35 := by
  unfold smvC4 smvT4; omega

theorem kc5 (a b : Nat → Nat) : smvC5 a b < 2 ^ 35 := by
  unfold smvC5 smvT5; omega

theorem kc6 (a b : Nat → Nat) : smvC6 a b < 2 ^ 35 := by
  unfold smvC6 smvT6; omega

theorem kc7 (a b : Nat → Nat) : smvC7 a b < 2 ^ 35 := by
  unfold smvC7 smvT7; omega

theorem kc8 (a b : Nat → Nat) : smvC8 a b < 2 ^ 35 := by
  unfold smvC8 smvT8; omega

theorem kc9 (a b : Nat → Nat) : smvC9 a b < 2 ^ 35 := by
  unfold smvC9 smvS9; omega

theorem kc10 (a b : Nat → Nat) : smvC10 a b < 2 ^ 35 := by
  unfold smvC10 smvS10; omega

theorem kc11 (a b : Nat → Nat) : smvC11 a b < 2 ^ 35 := by
  unfold smvC11 smvS11; omega

theorem kc12 (a b : Nat → Nat) : smvC12 a b < 2 ^ 35 := by
  unfold smvC12 smvS12; omega

theorem kc13 (a b : Nat → Nat) : smvC13 a b < 2 ^ 35 := by
  unfold smvC13 smvS13; omega

theorem kc14 (a b : Nat → Nat) : smvC14 a b < 2 ^ 35 := by
  unfold smvC14 smvS14; omega

theorem kc15 (a b : Nat → Nat) : smvC15 a b < 2 ^ 35 := by
  unfold smvC15 smvS15; omega

theorem kc16 (a b : Nat → Nat) : smvC16 a b < 2 ^ 35 := by
  unfold smvC16 smvS16; omega

theorem ks1 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS1 a b = smvC0 a b + smvZ1 a b + smvN0 a b * 9640146 := by
  have := kc0 a b
  have := kzb1 ha hb
  have := kn0 a b
  unfold smvS1 smvPN0L1
  omega

theorem ks2 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS2 a b = smvC1 a b + smvZ2 a b + smvN0 a b * 501691798 + smvN1 a b * 9640146 := by
  have := kc1 a b
  have := kzb2 ha hb
  have := kn0 a b
  have := kn1 a b
  unfold smvS2 smvPN0L2 smvPN1L1
  omega

theorem ks3 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS3 a b = smvC2 a b + smvZ3 a b + smvN0 a b * 502512965 + smvN1 a b * 501691798 + smvN2 a b * 9640146 := by
  have := kc2 a b
  have := kzb3 ha hb
  have := kn0 a b
  have := kn1 a b
  have := kn2 a b
  unfold smvS3 smvPN0L3 smvPN1L2 smvPN2L1
  omega

theorem ks4 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS4 a b = smvC3 a b + smvZ4 a b + smvN0 a b * 333 + smvN1 a b * 502512965 + smvN2 a b * 501691798 + smvN3 a b * 9640146 := by
  have := kc3 a b
  have := kzb4 ha hb
  have := kn0 a b
  have := kn1 a b
  have := kn2 a b
  have := kn3 a b
  unfold smvS4 smvPN0L4 smvPN1L3 smvPN2L2 smvPN3L1
  omega

theorem ks5 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS5 a b = smvC4 a b + smvZ5 a b + smvN1 a b * 333 + smvN2 a b * 502512965 + smvN3 a b * 501691798 + smvN4 a b * 9640146 := by
  have := kc4 a b
  have := kzb5 ha hb
  have := kn1 a b
  have := kn2 a b
  have := kn3 a b
  have := kn4 a b
  unfold smvS5 smvPN1L4 smvPN2L3 smvPN3L2 smvPN4L1
  omega

theorem ks6 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS6 a b = smvC5 a b + smvZ6 a b + smvN2 a b * 333 + smvN3 a b * 502512965 + smvN4 a b * 501691798 + smvN5 a b * 9640146 := by
  have := kc5 a b
  have := kzb6 ha hb
  have := kn2 a b
  have := kn3 a b
  have := kn4 a b
  have := kn5 a b
  unfold smvS6 smvPN2L4 smvPN3L3 smvPN4L2 smvPN5L1
  omega

theorem ks7 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS7 a b = smvC6 a b + smvZ7 a b + smvN3 a b * 333 + smvN4 a b * 502512965 + smvN5 a b * 501691798 + smvN6 a b * 9640146 := by
  have := kc6 a b
  have := kzb7 ha hb
  have := kn3 a b
  have := kn4 a b
  have := kn5 a b
  have := kn6 a b
  unfold smvS7 smvPN3L4 smvPN4L3 smvPN5L2 smvPN6L1
  omega

theorem ks8 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS8 a b = smvC7 a b + smvZ8 a b + smvN0 a b * 1048576 + smvN4 a b * 333 + smvN5 a b * 502512965 + smvN6 a b * 501691798 + smvN7 a b * 9640146 := by
  have := kc7 a b
  have := kzb8 ha hb
  have := kn0 a b
  have := kn4 a b
  have := kn5 a b
  have := kn6 a b
  have := kn7 a b
  unfold smvS8 smvPN0L8 smvPN4L4 smvPN5L3 smvPN6L2 smvPN7L1
  omega

theorem ks9 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS9 a b = smvC8 a b + smvZ9 a b + smvN1 a b * 1048576 + smvN5 a b * 333 + smvN6 a b * 502512965 + smvN7 a b * 501691798 + smvN8 a b * 9640146 := by
  have := kc8 a b
  have := kzb9 ha hb
  have := kn1 a b
  have := kn5 a b
  have := kn6 a b
  have := kn7 a b
  have := kn8 a b
  unfold smvS9 smvPN1L8 smvPN5L4 smvPN6L3 smvPN7L2 smvPN8L1
  omega

theorem ks10 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS10 a b = smvC9 a b + smvZ10 a b + smvN2 a b * 1048576 + smvN6 a b * 333 + smvN7 a b * 502512965 + smvN8 a b * 501691798 := by
  have := kc9 a b
  have := kzb10 ha hb
  have := kn2 a b
  have := kn6 a b
  have := kn7 a b
  have := kn8 a b
  unfold smvS10 smvPN2L8 smvPN6L4 smvPN7L3 smvPN8L2
  omega

theorem ks11 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS11 a b = smvC10 a b + smvZ11 a b + smvN3 a b * 1048576 + smvN7 a b * 333 + smvN8 a b * 502512965 := by
  have := kc10 a b
  have := kzb11 ha hb
  have := kn3 a b
  have := kn7 a b
  have := kn8 a b
  unfold smvS11 smvPN3L8 smvPN7L4 smvPN8L3
  omega

theorem ks12 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS12 a b = smvC11 a b + smvZ12 a b + smvN4 a b * 1048576 + smvN8 a b * 333 := by
  have := kc11 a b
  have := kzb12 ha hb
  have := kn4 a b
  have := kn8 a b
  unfold smvS12 smvPN4L8 smvPN8L4
  omega

theorem ks13 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS13 a b = smvC12 a b + smvZ13 a b + smvN5 a b * 1048576 := by
  have := kc12 a b
  have := kzb13 ha hb
  have := kn5 a b
  unfold smvS13 smvPN5L8
  omega

theorem ks14 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS14 a b = smvC13 a b + smvZ14 a b + smvN6 a b * 1048576 := by
  have := kc13 a b
  have := kzb14 ha hb
  have := kn6 a b
  unfold smvS14 smvPN6L8
  omega

theorem ks15 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS15 a b = smvC14 a b + smvZ15 a b + smvN7 a b * 1048576 := by
  have := kc14 a b
  have := kzb15 ha hb
  have := kn7 a b
  unfold smvS15 smvPN7L8
  omega

theorem ks16 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : smvS16 a b = smvC15 a b + smvPA8B8 a b + smvN8 a b * 1048576 := by
  have := kc15 a b
  have := kzb16 ha hb
  have := kn8 a b
  unfold smvS16 smvPN8L8
  omega

theorem kt0 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : 2 ^ 29 * smvC0 a b = smvPA0B0 a b + smvN0 a b * 485872621 := by
  have hs : smvPA0B0 a b < 2 ^ 63 := by have := kzb0 ha hb; omega
  have hn := kn0 a b
  have hm := mont0 (smvPA0B0 a b)
  have e : smvN0 a b = smvPA0B0 a b % 2 ^ 32 * 307527195 % 2 ^ 32 % 2 ^ 29 := rfl
  rw [← e] at hm
  unfold smvC0 smvT0 smvPN0L0
  omega

theorem kt1 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : 2 ^ 29 * smvC1 a b = smvS1 a b + smvN1 a b * 485872621 := by
  have hs : smvS1 a b < 2 ^ 63 := by
    rw [ks1 ha hb]
    have := kc0 a b
    have := kzb1 ha hb
    have := kn0 a b
    omega
  have hn := kn1 a b
  have hm := mont0 (smvS1 a b)
  have e : smvN1 a b = smvS1 a b % 2 ^ 32 * 307527195 % 2 ^ 32 % 2 ^ 29 := rfl
  rw [← e] at hm
  unfold smvC1 smvT1 smvPN1L0
  omega

theorem kt2 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : 2 ^ 29 * smvC2 a b = smvS2 a b + smvN2 a b * 485872621 := by
  have hs : smvS2 a b < 2 ^ 63 := by
    rw [ks2 ha hb]
    have := kc1 a b
    have := kzb2 ha hb
    have := kn0 a b
    have := kn1 a b
    omega
  have hn := kn2 a b
  have hm := mont0 (smvS2 a b)
  have e : smvN2 a b = smvS2 a b % 2 ^ 32 * 307527195 % 2 ^ 32 % 2 ^ 29 := rfl
  rw [← e] at hm
  unfold smvC2 smvT2 smvPN2L0
  omega

theorem kt3 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : 2 ^ 29 * smvC3 a b = smvS3 a b + smvN3 a b * 485872621 := by
  have hs : smvS3 a b < 2 ^ 63 := by
    rw [ks3 ha hb]
    have := kc2 a b
    have := kzb3 ha hb
    have := kn0 a b
    have := kn1 a b
    have := kn2 a b
    omega
  have hn := kn3 a b
  have hm := mont0 (smvS3 a b)
  have e : smvN3 a b = smvS3 a b % 2 ^ 32 * 307527195 % 2 ^ 32 % 2 ^ 29 := rfl
  rw [← e] at hm
  unfold smvC3 smvT3 smvPN3L0
  omega

theorem kt4 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : 2 ^ 29 * smvC4 a b = smvS4 a b + smvN4 a b * 485872621 := by
  have hs : smvS4 a b < 2 ^ 63 := by
    rw [ks4 ha hb]
    have := kc3 a b
    have := kzb4 ha hb
    have := kn0 a b
    have := kn1 a b
    have := kn2 a b
    have := kn3 a b
    omega
  have hn := kn4 a b
  have hm := mont0 (smvS4 a b)
  have e : smvN4 a b = smvS4 a b % 2 ^ 32 * 307527195 % 2 ^ 32 % 2 ^ 29 := rfl
  rw [← e] at hm
  unfold smvC4 smvT4 smvPN4L0
  omega

theorem kt5 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : 2 ^ 29 * smvC5 a b = smvS5 a b + smvN5 a b * 485872621 := by
  have hs : smvS5 a b < 2 ^ 63 := by
    rw [ks5 ha hb]
    have := kc4 a b
    have := kzb5 ha hb
    have := kn1 a b
    have := kn2 a b
    have := kn3 a b
    have := kn4 a b
    omega
  have hn := kn5 a b
  have hm := mont0 (smvS5 a b)
  have e : smvN5 a b = smvS5 a b % 2 ^ 32 * 307527195 % 2 ^ 32 % 2 ^ 29 := rfl
  rw [← e] at hm
  unfold smvC5 smvT5 smvPN5L0
  omega

theorem kt6 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : 2 ^ 29 * smvC6 a b = smvS6 a b + smvN6 a b * 485872621 := by
  have hs : smvS6 a b < 2 ^ 63 := by
    rw [ks6 ha hb]
    have := kc5 a b
    have := kzb6 ha hb
    have := kn2 a b
    have := kn3 a b
    have := kn4 a b
    have := kn5 a b
    omega
  have hn := kn6 a b
  have hm := mont0 (smvS6 a b)
  have e : smvN6 a b = smvS6 a b % 2 ^ 32 * 307527195 % 2 ^ 32 % 2 ^ 29 := rfl
  rw [← e] at hm
  unfold smvC6 smvT6 smvPN6L0
  omega

theorem kt7 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : 2 ^ 29 * smvC7 a b = smvS7 a b + smvN7 a b * 485872621 := by
  have hs : smvS7 a b < 2 ^ 63 := by
    rw [ks7 ha hb]
    have := kc6 a b
    have := kzb7 ha hb
    have := kn3 a b
    have := kn4 a b
    have := kn5 a b
    have := kn6 a b
    omega
  have hn := kn7 a b
  have hm := mont0 (smvS7 a b)
  have e : smvN7 a b = smvS7 a b % 2 ^ 32 * 307527195 % 2 ^ 32 % 2 ^ 29 := rfl
  rw [← e] at hm
  unfold smvC7 smvT7 smvPN7L0
  omega

theorem kt8 (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) : 2 ^ 29 * smvC8 a b = smvS8 a b + smvN8 a b * 485872621 := by
  have hs : smvS8 a b < 2 ^ 63 := by
    rw [ks8 ha hb]
    have := kc7 a b
    have := kzb8 ha hb
    have := kn0 a b
    have := kn4 a b
    have := kn5 a b
    have := kn6 a b
    have := kn7 a b
    omega
  have hn := kn8 a b
  have hm := mont0 (smvS8 a b)
  have e : smvN8 a b = smvS8 a b % 2 ^ 32 * 307527195 % 2 ^ 32 % 2 ^ 29 := rfl
  rw [← e] at hm
  unfold smvC8 smvT8 smvPN8L0
  omega

theorem kmont_id (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) :
    2 ^ 261 * (smvR0 a b + 2 ^ 29 * smvR1 a b + 2 ^ 58 * smvR2 a b + 2 ^ 87 * smvR3 a b + 2 ^ 116 * smvR4 a b + 2 ^ 145 * smvR5 a b + 2 ^ 174 * smvR6 a b + 2 ^ 203 * smvR7 a b + 2 ^ 232 * smvC16 a b) =
      smvPA0B0 a b + 2 ^ 29 * smvZ1 a b + 2 ^ 58 * smvZ2 a b + 2 ^ 87 * smvZ3 a b + 2 ^ 116 * smvZ4 a b + 2 ^ 145 * smvZ5 a b + 2 ^ 174 * smvZ6 a b + 2 ^ 203 * smvZ7 a b + 2 ^ 232 * smvZ8 a b + 2 ^ 261 * smvZ9 a b + 2 ^ 290 * smvZ10 a b + 2 ^ 319 * smvZ11 a b + 2 ^ 348 * smvZ12 a b + 2 ^ 377 * smvZ13 a b + 2 ^ 406 * smvZ14 a b + 2 ^ 435 * smvZ15 a b + 2 ^ 464 * smvPA8B8 a b + (smvN0 a b + 2 ^ 29 * smvN1 a b + 2 ^ 58 * smvN2 a b + 2 ^ 87 * smvN3 a b + 2 ^ 116 * smvN4 a b + 2 ^ 145 * smvN5 a b + 2 ^ 174 * smvN6 a b + 2 ^ 203 * smvN7 a b + 2 ^ 232 * smvN8 a b) * 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
  have := kt0 ha hb
  have := kt1 ha hb
  have := kt2 ha hb
  have := kt3 ha hb
  have := kt4 ha hb
  have := kt5 ha hb
  have := kt6 ha hb
  have := kt7 ha hb
  have := kt8 ha hb
  have := ks1 ha hb
  have := ks2 ha hb
  have := ks3 ha hb
  have := ks4 ha hb
  have := ks5 ha hb
  have := ks6 ha hb
  have := ks7 ha hb
  have := ks8 ha hb
  have := ks9 ha hb
  have := ks10 ha hb
  have := ks11 ha hb
  have := ks12 ha hb
  have := ks13 ha hb
  have := ks14 ha hb
  have := ks15 ha hb
  have := ks16 ha hb
  have : smvR0 a b = smvS9 a b % 2 ^ 29 := rfl
  have : smvR1 a b = smvS10 a b % 2 ^ 29 := rfl
  have : smvR2 a b = smvS11 a b % 2 ^ 29 := rfl
  have : smvR3 a b = smvS12 a b % 2 ^ 29 := rfl
  have : smvR4 a b = smvS13 a b % 2 ^ 29 := rfl
  have : smvR5 a b = smvS14 a b % 2 ^ 29 := rfl
  have : smvR6 a b = smvS15 a b % 2 ^ 29 := rfl
  have : smvR7 a b = smvS16 a b % 2 ^ 29 := rfl
  have : smvC9 a b = smvS9 a b / 2 ^ 29 := rfl
  have : smvC10 a b = smvS10 a b / 2 ^ 29 := rfl
  have : smvC11 a b = smvS11 a b / 2 ^ 29 := rfl
  have : smvC12 a b = smvS12 a b / 2 ^ 29 := rfl
  have : smvC13 a b = smvS13 a b / 2 ^ 29 := rfl
  have : smvC14 a b = smvS14 a b / 2 ^ 29 := rfl
  have : smvC15 a b = smvS15 a b / 2 ^ 29 := rfl
  have : smvC16 a b = smvS16 a b / 2 ^ 29 := rfl
  omega

set_option exponentiation.threshold 600 in
theorem kab (a b : Nat → Nat) : sv9 a * sv9 b = (a 0 * b 0) + 2 ^ 29 * (a 0 * b 1 + a 1 * b 0) + 2 ^ 58 * (a 0 * b 2 + a 1 * b 1 + a 2 * b 0) + 2 ^ 87 * (a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0) + 2 ^ 116 * (a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0) + 2 ^ 145 * (a 0 * b 5 + a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1 + a 5 * b 0) + 2 ^ 174 * (a 0 * b 6 + a 1 * b 5 + a 2 * b 4 + a 3 * b 3 + a 4 * b 2 + a 5 * b 1 + a 6 * b 0) + 2 ^ 203 * (a 0 * b 7 + a 1 * b 6 + a 2 * b 5 + a 3 * b 4 + a 4 * b 3 + a 5 * b 2 + a 6 * b 1 + a 7 * b 0) + 2 ^ 232 * (a 0 * b 8 + a 1 * b 7 + a 2 * b 6 + a 3 * b 5 + a 4 * b 4 + a 5 * b 3 + a 6 * b 2 + a 7 * b 1 + a 8 * b 0) + 2 ^ 261 * (a 1 * b 8 + a 2 * b 7 + a 3 * b 6 + a 4 * b 5 + a 5 * b 4 + a 6 * b 3 + a 7 * b 2 + a 8 * b 1) + 2 ^ 290 * (a 2 * b 8 + a 3 * b 7 + a 4 * b 6 + a 5 * b 5 + a 6 * b 4 + a 7 * b 3 + a 8 * b 2) + 2 ^ 319 * (a 3 * b 8 + a 4 * b 7 + a 5 * b 6 + a 6 * b 5 + a 7 * b 4 + a 8 * b 3) + 2 ^ 348 * (a 4 * b 8 + a 5 * b 7 + a 6 * b 6 + a 7 * b 5 + a 8 * b 4) + 2 ^ 377 * (a 5 * b 8 + a 6 * b 7 + a 7 * b 6 + a 8 * b 5) + 2 ^ 406 * (a 6 * b 8 + a 7 * b 7 + a 8 * b 6) + 2 ^ 435 * (a 7 * b 8 + a 8 * b 7) + 2 ^ 464 * (a 8 * b 8) := by
  unfold sv9; ring_eq

theorem kmont_val (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) :
    2 ^ 261 * (smvR0 a b + 2 ^ 29 * smvR1 a b + 2 ^ 58 * smvR2 a b + 2 ^ 87 * smvR3 a b + 2 ^ 116 * smvR4 a b + 2 ^ 145 * smvR5 a b + 2 ^ 174 * smvR6 a b + 2 ^ 203 * smvR7 a b + 2 ^ 232 * smvC16 a b) = sv9 a * sv9 b + (smvN0 a b + 2 ^ 29 * smvN1 a b + 2 ^ 58 * smvN2 a b + 2 ^ 87 * smvN3 a b + 2 ^ 116 * smvN4 a b + 2 ^ 145 * smvN5 a b + 2 ^ 174 * smvN6 a b + 2 ^ 203 * smvN7 a b + 2 ^ 232 * smvN8 a b) * 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
  have := kmont_id ha hb
  have := kab a b
  have := kz0 (a := a) (b := b)
  have := kz1 ha hb
  have := kz2 ha hb
  have := kz3 ha hb
  have := kz4 ha hb
  have := kz5 ha hb
  have := kz6 ha hb
  have := kz7 ha hb
  have := kz8 ha hb
  have := kz9 ha hb
  have := kz10 ha hb
  have := kz11 ha hb
  have := kz12 ha hb
  have := kz13 ha hb
  have := kz14 ha hb
  have := kz15 ha hb
  have := kz16 (a := a) (b := b)
  omega

set_option exponentiation.threshold 600 in
theorem smm_val (ha : ∀ i, i < 9 → a i < 2 ^ 29) (hb : ∀ i, i < 9 → b i < 2 ^ 29) (hbL : sv9 b < Ed25519.L) :
    (∀ i, i < 9 → smmRed a b i < 2 ^ 29) ∧ sv9 (smmRed a b) < 2 * Ed25519.L ∧
      ∃ N, 2 ^ 261 * sv9 (smmRed a b) = sv9 a * sv9 b + N * Ed25519.L := by
  have hv := kmont_val ha hb
  have hA : sv9 a ≤ 2 ^ 261 - 1 := by
    unfold sv9
    have := ha 0 (by decide)
    have := ha 1 (by decide)
    have := ha 2 (by decide)
    have := ha 3 (by decide)
    have := ha 4 (by decide)
    have := ha 5 (by decide)
    have := ha 6 (by decide)
    have := ha 7 (by decide)
    have := ha 8 (by decide)
    omega
  have hB : sv9 b ≤ Ed25519.L - 1 := by omega
  have hAB : sv9 a * sv9 b ≤ (2 ^ 261 - 1) * (Ed25519.L - 1) := Nat.mul_le_mul hA hB
  have := kn0 a b
  have := kn1 a b
  have := kn2 a b
  have := kn3 a b
  have := kn4 a b
  have := kn5 a b
  have := kn6 a b
  have := kn7 a b
  have := kn8 a b
  have e : sv9 (smmRed a b) = smvR0 a b + 2 ^ 29 * smvR1 a b + 2 ^ 58 * smvR2 a b + 2 ^ 87 * smvR3 a b + 2 ^ 116 * smvR4 a b + 2 ^ 145 * smvR5 a b + 2 ^ 174 * smvR6 a b + 2 ^ 203 * smvR7 a b + 2 ^ 232 * smvR8 a b := rfl
  have e8 : smvR8 a b = smvC16 a b % 2 ^ 32 := rfl
  have hr : smvR0 a b + 2 ^ 29 * smvR1 a b + 2 ^ 58 * smvR2 a b + 2 ^ 87 * smvR3 a b + 2 ^ 116 * smvR4 a b + 2 ^ 145 * smvR5 a b + 2 ^ 174 * smvR6 a b + 2 ^ 203 * smvR7 a b + 2 ^ 232 * smvC16 a b < 2 * Ed25519.L := by
    unfold Ed25519.L at hAB ⊢
    omega
  have h16 : smvC16 a b < 2 ^ 32 := by unfold Ed25519.L at hr; omega
  rw [Nat.mod_eq_of_lt h16] at e8
  refine ⟨fun i hi => ?_, by rw [e, e8]; exact hr, ⟨smvN0 a b + 2 ^ 29 * smvN1 a b + 2 ^ 58 * smvN2 a b + 2 ^ 87 * smvN3 a b + 2 ^ 116 * smvN4 a b + 2 ^ 145 * smvN5 a b + 2 ^ 174 * smvN6 a b + 2 ^ 203 * smvN7 a b + 2 ^ 232 * smvN8 a b, ?_⟩⟩
  · match i, hi with
    | 0, _ => show smvS9 a b % 2 ^ 29 < 2 ^ 29; omega
    | 1, _ => show smvS10 a b % 2 ^ 29 < 2 ^ 29; omega
    | 2, _ => show smvS11 a b % 2 ^ 29 < 2 ^ 29; omega
    | 3, _ => show smvS12 a b % 2 ^ 29 < 2 ^ 29; omega
    | 4, _ => show smvS13 a b % 2 ^ 29 < 2 ^ 29; omega
    | 5, _ => show smvS14 a b % 2 ^ 29 < 2 ^ 29; omega
    | 6, _ => show smvS15 a b % 2 ^ 29 < 2 ^ 29; omega
    | 7, _ => show smvS16 a b % 2 ^ 29 < 2 ^ 29; omega
    | 8, _ => show smvR8 a b < 2 ^ 29; unfold Ed25519.L at hr; omega
    | _ + 9, h => exact absurd h (by omega)
  · rw [e, e8, hv]; rfl

end

end C3.RV32.EdK
