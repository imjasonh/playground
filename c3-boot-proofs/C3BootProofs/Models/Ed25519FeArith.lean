import C3BootProofs.Ring.Tactic
import C3BootProofs.Models.Ed25519Field
import C3BootProofs.Proofs.Fe25519

/-!
# Field arithmetic on radix-2^25.5 limbs

`reduce` keeps the value of ten `u64` sums below 3 · 2^62 modulo `p` and
leaves each limb below 2^26 (`feReduce_ok`). `mul`'s ten sums equal their
unwrapped polynomials when the operands' limbs are below 3 · 2^26
(`feMulZ_eq`), and `square_inner`'s when they are below 2^27 (`feSqZ_eq`);
`ring_mod` checks that those polynomials compute the product modulo `p`.
-/

namespace C3.RV32.EdM

theorem mod_of_eq {S P M : Nat} (h : S = P) (hb : P < M) : S % M = P := by rw [h]; exact Nat.mod_eq_of_lt hb

theorem two_sq_mod (A : Nat) : 2 * (A % Ed25519.p * (A % Ed25519.p)) % Ed25519.p = 2 * (A * A) % Ed25519.p :=
  calc 2 * (A % Ed25519.p * (A % Ed25519.p)) % Ed25519.p
      = 2 * (A % Ed25519.p * (A % Ed25519.p) % Ed25519.p) % Ed25519.p := (mod_mul_mod' _ _).symm
    _ = 2 * (A * A % Ed25519.p) % Ed25519.p := by rw [mod_mul_mod' (A % Ed25519.p) A, mod_mul_mod'' A A]
    _ = 2 * (A * A) % Ed25519.p := mod_mul_mod' _ _

set_option maxHeartbeats 4000000 in
/-- **`FieldElement2625::reduce` keeps the value modulo `p`** and leaves each
limb below 2^26. -/
theorem feReduce_ok (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : Nat) (h0 : z0 < 3 * 2 ^ 62) (h1 : z1 < 3 * 2 ^ 62)
    (h2 : z2 < 3 * 2 ^ 62) (h3 : z3 < 3 * 2 ^ 62) (h4 : z4 < 3 * 2 ^ 62) (h5 : z5 < 3 * 2 ^ 62) (h6 : z6 < 3 * 2 ^ 62)
    (h7 : z7 < 3 * 2 ^ 62) (h8 : z8 < 3 * 2 ^ 62) (h9 : z9 < 3 * 2 ^ 62) :
    Lim (2 ^ 26) (feReduceSpec z0 z1 z2 z3 z4 z5 z6 z7 z8 z9) ∧
    fv (feReduceSpec z0 z1 z2 z3 z4 z5 z6 z7 z8 z9) = (z0 + 2 ^ 26 * z1 + 2 ^ 51 * z2 + 2 ^ 77 * z3 + 2 ^ 102 * z4 +
      2 ^ 128 * z5 + 2 ^ 153 * z6 + 2 ^ 179 * z7 + 2 ^ 204 * z8 + 2 ^ 230 * z9) % Ed25519.p := by
  simp only [feReduceSpec, fv, Lim]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_succ, List.getD_cons_zero] <;> omega
  · unfold Ed25519.p
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

theorem mul_bounds (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Nat) (hx0 : x0 < 3 * 2 ^ 26) (hx1 : x1 < 3 * 2 ^ 26) (hx2 : x2 < 3 * 2 ^ 26) (hx3 : x3 < 3 * 2 ^ 26) (hx4 : x4 < 3 * 2 ^ 26) (hx5 : x5 < 3 * 2 ^ 26) (hx6 : x6 < 3 * 2 ^ 26) (hx7 : x7 < 3 * 2 ^ 26) (hx8 : x8 < 3 * 2 ^ 26) (hx9 : x9 < 3 * 2 ^ 26)
    (hy0 : y0 < 3 * 2 ^ 26) (hy1 : y1 < 3 * 2 ^ 26) (hy2 : y2 < 3 * 2 ^ 26) (hy3 : y3 < 3 * 2 ^ 26) (hy4 : y4 < 3 * 2 ^ 26) (hy5 : y5 < 3 * 2 ^ 26) (hy6 : y6 < 3 * 2 ^ 26) (hy7 : y7 < 3 * 2 ^ 26) (hy8 : y8 < 3 * 2 ^ 26) (hy9 : y9 < 3 * 2 ^ 26) :
    (x0 * y0 + 38 * (x1 * y9) + 19 * (x2 * y8) + 38 * (x3 * y7) + 19 * (x4 * y6) + 38 * (x5 * y5) + 19 * (x6 * y4) + 38 * (x7 * y3) + 19 * (x8 * y2) + 38 * (x9 * y1)) < 3 * 2 ^ 62 ∧
    (x0 * y1 + x1 * y0 + 19 * (x2 * y9) + 19 * (x3 * y8) + 19 * (x4 * y7) + 19 * (x5 * y6) + 19 * (x6 * y5) + 19 * (x7 * y4) + 19 * (x8 * y3) + 19 * (x9 * y2)) < 3 * 2 ^ 62 ∧
    (x0 * y2 + 2 * (x1 * y1) + x2 * y0 + 38 * (x3 * y9) + 19 * (x4 * y8) + 38 * (x5 * y7) + 19 * (x6 * y6) + 38 * (x7 * y5) + 19 * (x8 * y4) + 38 * (x9 * y3)) < 3 * 2 ^ 62 ∧
    (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 + 19 * (x4 * y9) + 19 * (x5 * y8) + 19 * (x6 * y7) + 19 * (x7 * y6) + 19 * (x8 * y5) + 19 * (x9 * y4)) < 3 * 2 ^ 62 ∧
    (x0 * y4 + 2 * (x1 * y3) + x2 * y2 + 2 * (x3 * y1) + x4 * y0 + 38 * (x5 * y9) + 19 * (x6 * y8) + 38 * (x7 * y7) + 19 * (x8 * y6) + 38 * (x9 * y5)) < 3 * 2 ^ 62 ∧
    (x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0 + 19 * (x6 * y9) + 19 * (x7 * y8) + 19 * (x8 * y7) + 19 * (x9 * y6)) < 3 * 2 ^ 62 ∧
    (x0 * y6 + 2 * (x1 * y5) + x2 * y4 + 2 * (x3 * y3) + x4 * y2 + 2 * (x5 * y1) + x6 * y0 + 38 * (x7 * y9) + 19 * (x8 * y8) + 38 * (x9 * y7)) < 3 * 2 ^ 62 ∧
    (x0 * y7 + x1 * y6 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2 + x6 * y1 + x7 * y0 + 19 * (x8 * y9) + 19 * (x9 * y8)) < 3 * 2 ^ 62 ∧
    (x0 * y8 + 2 * (x1 * y7) + x2 * y6 + 2 * (x3 * y5) + x4 * y4 + 2 * (x5 * y3) + x6 * y2 + 2 * (x7 * y1) + x8 * y0 + 38 * (x9 * y9)) < 3 * 2 ^ 62 ∧
    (x0 * y9 + x1 * y8 + x2 * y7 + x3 * y6 + x4 * y5 + x5 * y4 + x6 * y3 + x7 * y2 + x8 * y1 + x9 * y0) < 3 * 2 ^ 62 := by
  have p0_0 : x0 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy0)) (by decide)
  have p0_1 : x0 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy1)) (by decide)
  have p0_2 : x0 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy2)) (by decide)
  have p0_3 : x0 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy3)) (by decide)
  have p0_4 : x0 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy4)) (by decide)
  have p0_5 : x0 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy5)) (by decide)
  have p0_6 : x0 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy6)) (by decide)
  have p0_7 : x0 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy7)) (by decide)
  have p0_8 : x0 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy8)) (by decide)
  have p0_9 : x0 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hy9)) (by decide)
  have p1_0 : x1 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy0)) (by decide)
  have p1_1 : x1 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy1)) (by decide)
  have p1_2 : x1 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy2)) (by decide)
  have p1_3 : x1 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy3)) (by decide)
  have p1_4 : x1 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy4)) (by decide)
  have p1_5 : x1 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy5)) (by decide)
  have p1_6 : x1 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy6)) (by decide)
  have p1_7 : x1 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy7)) (by decide)
  have p1_8 : x1 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy8)) (by decide)
  have p1_9 : x1 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hy9)) (by decide)
  have p2_0 : x2 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy0)) (by decide)
  have p2_1 : x2 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy1)) (by decide)
  have p2_2 : x2 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy2)) (by decide)
  have p2_3 : x2 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy3)) (by decide)
  have p2_4 : x2 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy4)) (by decide)
  have p2_5 : x2 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy5)) (by decide)
  have p2_6 : x2 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy6)) (by decide)
  have p2_7 : x2 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy7)) (by decide)
  have p2_8 : x2 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy8)) (by decide)
  have p2_9 : x2 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hy9)) (by decide)
  have p3_0 : x3 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy0)) (by decide)
  have p3_1 : x3 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy1)) (by decide)
  have p3_2 : x3 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy2)) (by decide)
  have p3_3 : x3 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy3)) (by decide)
  have p3_4 : x3 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy4)) (by decide)
  have p3_5 : x3 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy5)) (by decide)
  have p3_6 : x3 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy6)) (by decide)
  have p3_7 : x3 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy7)) (by decide)
  have p3_8 : x3 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy8)) (by decide)
  have p3_9 : x3 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hy9)) (by decide)
  have p4_0 : x4 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy0)) (by decide)
  have p4_1 : x4 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy1)) (by decide)
  have p4_2 : x4 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy2)) (by decide)
  have p4_3 : x4 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy3)) (by decide)
  have p4_4 : x4 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy4)) (by decide)
  have p4_5 : x4 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy5)) (by decide)
  have p4_6 : x4 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy6)) (by decide)
  have p4_7 : x4 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy7)) (by decide)
  have p4_8 : x4 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy8)) (by decide)
  have p4_9 : x4 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hy9)) (by decide)
  have p5_0 : x5 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy0)) (by decide)
  have p5_1 : x5 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy1)) (by decide)
  have p5_2 : x5 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy2)) (by decide)
  have p5_3 : x5 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy3)) (by decide)
  have p5_4 : x5 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy4)) (by decide)
  have p5_5 : x5 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy5)) (by decide)
  have p5_6 : x5 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy6)) (by decide)
  have p5_7 : x5 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy7)) (by decide)
  have p5_8 : x5 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy8)) (by decide)
  have p5_9 : x5 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hy9)) (by decide)
  have p6_0 : x6 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy0)) (by decide)
  have p6_1 : x6 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy1)) (by decide)
  have p6_2 : x6 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy2)) (by decide)
  have p6_3 : x6 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy3)) (by decide)
  have p6_4 : x6 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy4)) (by decide)
  have p6_5 : x6 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy5)) (by decide)
  have p6_6 : x6 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy6)) (by decide)
  have p6_7 : x6 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy7)) (by decide)
  have p6_8 : x6 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy8)) (by decide)
  have p6_9 : x6 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hy9)) (by decide)
  have p7_0 : x7 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy0)) (by decide)
  have p7_1 : x7 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy1)) (by decide)
  have p7_2 : x7 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy2)) (by decide)
  have p7_3 : x7 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy3)) (by decide)
  have p7_4 : x7 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy4)) (by decide)
  have p7_5 : x7 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy5)) (by decide)
  have p7_6 : x7 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy6)) (by decide)
  have p7_7 : x7 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy7)) (by decide)
  have p7_8 : x7 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy8)) (by decide)
  have p7_9 : x7 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hy9)) (by decide)
  have p8_0 : x8 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy0)) (by decide)
  have p8_1 : x8 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy1)) (by decide)
  have p8_2 : x8 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy2)) (by decide)
  have p8_3 : x8 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy3)) (by decide)
  have p8_4 : x8 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy4)) (by decide)
  have p8_5 : x8 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy5)) (by decide)
  have p8_6 : x8 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy6)) (by decide)
  have p8_7 : x8 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy7)) (by decide)
  have p8_8 : x8 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy8)) (by decide)
  have p8_9 : x8 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hy9)) (by decide)
  have p9_0 : x9 * y0 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy0)) (by decide)
  have p9_1 : x9 * y1 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy1)) (by decide)
  have p9_2 : x9 * y2 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy2)) (by decide)
  have p9_3 : x9 * y3 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy3)) (by decide)
  have p9_4 : x9 * y4 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy4)) (by decide)
  have p9_5 : x9 * y5 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy5)) (by decide)
  have p9_6 : x9 * y6 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy6)) (by decide)
  have p9_7 : x9 * y7 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy7)) (by decide)
  have p9_8 : x9 * y8 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy8)) (by decide)
  have p9_9 : x9 * y9 ≤ 40532396243681281 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hy9)) (by decide)
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem feMulZ_eq (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Nat) (hx0 : x0 < 3 * 2 ^ 26) (hx1 : x1 < 3 * 2 ^ 26) (hx2 : x2 < 3 * 2 ^ 26) (hx3 : x3 < 3 * 2 ^ 26) (hx4 : x4 < 3 * 2 ^ 26) (hx5 : x5 < 3 * 2 ^ 26) (hx6 : x6 < 3 * 2 ^ 26) (hx7 : x7 < 3 * 2 ^ 26) (hx8 : x8 < 3 * 2 ^ 26) (hx9 : x9 < 3 * 2 ^ 26)
    (hy0 : y0 < 3 * 2 ^ 26) (hy1 : y1 < 3 * 2 ^ 26) (hy2 : y2 < 3 * 2 ^ 26) (hy3 : y3 < 3 * 2 ^ 26) (hy4 : y4 < 3 * 2 ^ 26) (hy5 : y5 < 3 * 2 ^ 26) (hy6 : y6 < 3 * 2 ^ 26) (hy7 : y7 < 3 * 2 ^ 26) (hy8 : y8 < 3 * 2 ^ 26) (hy9 : y9 < 3 * 2 ^ 26) :
    feMulZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 =
      [x0 * y0 + 38 * (x1 * y9) + 19 * (x2 * y8) + 38 * (x3 * y7) + 19 * (x4 * y6) + 38 * (x5 * y5) + 19 * (x6 * y4) + 38 * (x7 * y3) + 19 * (x8 * y2) + 38 * (x9 * y1),
        x0 * y1 + x1 * y0 + 19 * (x2 * y9) + 19 * (x3 * y8) + 19 * (x4 * y7) + 19 * (x5 * y6) + 19 * (x6 * y5) + 19 * (x7 * y4) + 19 * (x8 * y3) + 19 * (x9 * y2),
        x0 * y2 + 2 * (x1 * y1) + x2 * y0 + 38 * (x3 * y9) + 19 * (x4 * y8) + 38 * (x5 * y7) + 19 * (x6 * y6) + 38 * (x7 * y5) + 19 * (x8 * y4) + 38 * (x9 * y3),
        x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 + 19 * (x4 * y9) + 19 * (x5 * y8) + 19 * (x6 * y7) + 19 * (x7 * y6) + 19 * (x8 * y5) + 19 * (x9 * y4),
        x0 * y4 + 2 * (x1 * y3) + x2 * y2 + 2 * (x3 * y1) + x4 * y0 + 38 * (x5 * y9) + 19 * (x6 * y8) + 38 * (x7 * y7) + 19 * (x8 * y6) + 38 * (x9 * y5),
        x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0 + 19 * (x6 * y9) + 19 * (x7 * y8) + 19 * (x8 * y7) + 19 * (x9 * y6),
        x0 * y6 + 2 * (x1 * y5) + x2 * y4 + 2 * (x3 * y3) + x4 * y2 + 2 * (x5 * y1) + x6 * y0 + 38 * (x7 * y9) + 19 * (x8 * y8) + 38 * (x9 * y7),
        x0 * y7 + x1 * y6 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2 + x6 * y1 + x7 * y0 + 19 * (x8 * y9) + 19 * (x9 * y8),
        x0 * y8 + 2 * (x1 * y7) + x2 * y6 + 2 * (x3 * y5) + x4 * y4 + 2 * (x5 * y3) + x6 * y2 + 2 * (x7 * y1) + x8 * y0 + 38 * (x9 * y9),
        x0 * y9 + x1 * y8 + x2 * y7 + x3 * y6 + x4 * y5 + x5 * y4 + x6 * y3 + x7 * y2 + x8 * y1 + x9 * y0] := by
  simp only [feMulZ]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  have hb := mul_bounds x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hy0 hy1 hy2 hy3 hy4 hy5 hy6 hy7 hy8 hy9
  simp only [List.cons.injEq, and_true]
  exact ⟨mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega)⟩

theorem mul_canon (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Nat) :
    ((x0 * y0 + 38 * (x1 * y9) + 19 * (x2 * y8) + 38 * (x3 * y7) + 19 * (x4 * y6) + 38 * (x5 * y5) + 19 * (x6 * y4) + 38 * (x7 * y3) + 19 * (x8 * y2) + 38 * (x9 * y1)) + 2 ^ 26 * (x0 * y1 + x1 * y0 + 19 * (x2 * y9) + 19 * (x3 * y8) + 19 * (x4 * y7) + 19 * (x5 * y6) + 19 * (x6 * y5) + 19 * (x7 * y4) + 19 * (x8 * y3) + 19 * (x9 * y2)) + 2 ^ 51 * (x0 * y2 + 2 * (x1 * y1) + x2 * y0 + 38 * (x3 * y9) + 19 * (x4 * y8) + 38 * (x5 * y7) + 19 * (x6 * y6) + 38 * (x7 * y5) + 19 * (x8 * y4) + 38 * (x9 * y3)) + 2 ^ 77 * (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 + 19 * (x4 * y9) + 19 * (x5 * y8) + 19 * (x6 * y7) + 19 * (x7 * y6) + 19 * (x8 * y5) + 19 * (x9 * y4)) + 2 ^ 102 * (x0 * y4 + 2 * (x1 * y3) + x2 * y2 + 2 * (x3 * y1) + x4 * y0 + 38 * (x5 * y9) + 19 * (x6 * y8) + 38 * (x7 * y7) + 19 * (x8 * y6) + 38 * (x9 * y5)) + 2 ^ 128 * (x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0 + 19 * (x6 * y9) + 19 * (x7 * y8) + 19 * (x8 * y7) + 19 * (x9 * y6)) + 2 ^ 153 * (x0 * y6 + 2 * (x1 * y5) + x2 * y4 + 2 * (x3 * y3) + x4 * y2 + 2 * (x5 * y1) + x6 * y0 + 38 * (x7 * y9) + 19 * (x8 * y8) + 38 * (x9 * y7)) + 2 ^ 179 * (x0 * y7 + x1 * y6 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2 + x6 * y1 + x7 * y0 + 19 * (x8 * y9) + 19 * (x9 * y8)) + 2 ^ 204 * (x0 * y8 + 2 * (x1 * y7) + x2 * y6 + 2 * (x3 * y5) + x4 * y4 + 2 * (x5 * y3) + x6 * y2 + 2 * (x7 * y1) + x8 * y0 + 38 * (x9 * y9)) + 2 ^ 230 * (x0 * y9 + x1 * y8 + x2 * y7 + x3 * y6 + x4 * y5 + x5 * y4 + x6 * y3 + x7 * y2 + x8 * y1 + x9 * y0)) % Ed25519.p =
      ((x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9) * (y0 + 2 ^ 26 * y1 + 2 ^ 51 * y2 + 2 ^ 77 * y3 + 2 ^ 102 * y4 + 2 ^ 128 * y5 + 2 ^ 153 * y6 + 2 ^ 179 * y7 + 2 ^ 204 * y8 + 2 ^ 230 * y9)) % Ed25519.p := by
  ring_mod

theorem sq_bounds27 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hx0 : x0 < 2 ^ 27) (hx1 : x1 < 2 ^ 27) (hx2 : x2 < 2 ^ 27) (hx3 : x3 < 2 ^ 27) (hx4 : x4 < 2 ^ 27) (hx5 : x5 < 2 ^ 27) (hx6 : x6 < 2 ^ 27) (hx7 : x7 < 2 ^ 27) (hx8 : x8 < 2 ^ 27) (hx9 : x9 < 2 ^ 27) :
    (x0 * x0 + 76 * (x1 * x9) + 38 * (x2 * x8) + 76 * (x3 * x7) + 38 * (x4 * x6) + 38 * (x5 * x5)) < 3 * 2 ^ 62 ∧
    (2 * (x0 * x1) + 38 * (x2 * x9) + 38 * (x3 * x8) + 38 * (x4 * x7) + 38 * (x5 * x6)) < 3 * 2 ^ 62 ∧
    (2 * (x0 * x2) + 2 * (x1 * x1) + 76 * (x3 * x9) + 38 * (x4 * x8) + 76 * (x5 * x7) + 19 * (x6 * x6)) < 3 * 2 ^ 62 ∧
    (2 * (x0 * x3) + 2 * (x1 * x2) + 38 * (x4 * x9) + 38 * (x5 * x8) + 38 * (x6 * x7)) < 3 * 2 ^ 62 ∧
    (2 * (x0 * x4) + 4 * (x1 * x3) + x2 * x2 + 76 * (x5 * x9) + 38 * (x6 * x8) + 38 * (x7 * x7)) < 3 * 2 ^ 62 ∧
    (2 * (x0 * x5) + 2 * (x1 * x4) + 2 * (x2 * x3) + 38 * (x6 * x9) + 38 * (x7 * x8)) < 3 * 2 ^ 62 ∧
    (2 * (x0 * x6) + 4 * (x1 * x5) + 2 * (x2 * x4) + 2 * (x3 * x3) + 76 * (x7 * x9) + 19 * (x8 * x8)) < 3 * 2 ^ 62 ∧
    (2 * (x0 * x7) + 2 * (x1 * x6) + 2 * (x2 * x5) + 2 * (x3 * x4) + 38 * (x8 * x9)) < 3 * 2 ^ 62 ∧
    (2 * (x0 * x8) + 4 * (x1 * x7) + 2 * (x2 * x6) + 4 * (x3 * x5) + x4 * x4 + 38 * (x9 * x9)) < 3 * 2 ^ 62 ∧
    (2 * (x0 * x9) + 2 * (x1 * x8) + 2 * (x2 * x7) + 2 * (x3 * x6) + 2 * (x4 * x5)) < 3 * 2 ^ 62 := by
  have p0_0 : x0 * x0 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx0)) (by decide)
  have p0_1 : x0 * x1 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx1)) (by decide)
  have p0_2 : x0 * x2 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx2)) (by decide)
  have p0_3 : x0 * x3 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx3)) (by decide)
  have p0_4 : x0 * x4 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx4)) (by decide)
  have p0_5 : x0 * x5 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx5)) (by decide)
  have p0_6 : x0 * x6 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx6)) (by decide)
  have p0_7 : x0 * x7 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx7)) (by decide)
  have p0_8 : x0 * x8 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx8)) (by decide)
  have p0_9 : x0 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx9)) (by decide)
  have p1_1 : x1 * x1 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx1)) (by decide)
  have p1_2 : x1 * x2 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx2)) (by decide)
  have p1_3 : x1 * x3 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx3)) (by decide)
  have p1_4 : x1 * x4 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx4)) (by decide)
  have p1_5 : x1 * x5 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx5)) (by decide)
  have p1_6 : x1 * x6 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx6)) (by decide)
  have p1_7 : x1 * x7 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx7)) (by decide)
  have p1_8 : x1 * x8 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx8)) (by decide)
  have p1_9 : x1 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx9)) (by decide)
  have p2_2 : x2 * x2 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx2)) (by decide)
  have p2_3 : x2 * x3 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx3)) (by decide)
  have p2_4 : x2 * x4 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx4)) (by decide)
  have p2_5 : x2 * x5 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx5)) (by decide)
  have p2_6 : x2 * x6 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx6)) (by decide)
  have p2_7 : x2 * x7 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx7)) (by decide)
  have p2_8 : x2 * x8 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx8)) (by decide)
  have p2_9 : x2 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx9)) (by decide)
  have p3_3 : x3 * x3 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx3)) (by decide)
  have p3_4 : x3 * x4 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx4)) (by decide)
  have p3_5 : x3 * x5 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx5)) (by decide)
  have p3_6 : x3 * x6 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx6)) (by decide)
  have p3_7 : x3 * x7 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx7)) (by decide)
  have p3_8 : x3 * x8 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx8)) (by decide)
  have p3_9 : x3 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx9)) (by decide)
  have p4_4 : x4 * x4 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx4)) (by decide)
  have p4_5 : x4 * x5 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx5)) (by decide)
  have p4_6 : x4 * x6 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx6)) (by decide)
  have p4_7 : x4 * x7 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx7)) (by decide)
  have p4_8 : x4 * x8 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx8)) (by decide)
  have p4_9 : x4 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx9)) (by decide)
  have p5_5 : x5 * x5 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx5)) (by decide)
  have p5_6 : x5 * x6 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx6)) (by decide)
  have p5_7 : x5 * x7 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx7)) (by decide)
  have p5_8 : x5 * x8 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx8)) (by decide)
  have p5_9 : x5 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx9)) (by decide)
  have p6_6 : x6 * x6 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hx6)) (by decide)
  have p6_7 : x6 * x7 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hx7)) (by decide)
  have p6_8 : x6 * x8 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hx8)) (by decide)
  have p6_9 : x6 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hx9)) (by decide)
  have p7_7 : x7 * x7 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hx7)) (by decide)
  have p7_8 : x7 * x8 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hx8)) (by decide)
  have p7_9 : x7 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hx9)) (by decide)
  have p8_8 : x8 * x8 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hx8)) (by decide)
  have p8_9 : x8 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hx9)) (by decide)
  have p9_9 : x9 * x9 ≤ 18014398241046529 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hx9)) (by decide)
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem sq_bounds26 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hx0 : x0 < 2 ^ 26) (hx1 : x1 < 2 ^ 26) (hx2 : x2 < 2 ^ 26) (hx3 : x3 < 2 ^ 26) (hx4 : x4 < 2 ^ 26) (hx5 : x5 < 2 ^ 26) (hx6 : x6 < 2 ^ 26) (hx7 : x7 < 2 ^ 26) (hx8 : x8 < 2 ^ 26) (hx9 : x9 < 2 ^ 26) :
    (x0 * x0 + 76 * (x1 * x9) + 38 * (x2 * x8) + 76 * (x3 * x7) + 38 * (x4 * x6) + 38 * (x5 * x5)) < 2 ^ 61 ∧
    (2 * (x0 * x1) + 38 * (x2 * x9) + 38 * (x3 * x8) + 38 * (x4 * x7) + 38 * (x5 * x6)) < 2 ^ 61 ∧
    (2 * (x0 * x2) + 2 * (x1 * x1) + 76 * (x3 * x9) + 38 * (x4 * x8) + 76 * (x5 * x7) + 19 * (x6 * x6)) < 2 ^ 61 ∧
    (2 * (x0 * x3) + 2 * (x1 * x2) + 38 * (x4 * x9) + 38 * (x5 * x8) + 38 * (x6 * x7)) < 2 ^ 61 ∧
    (2 * (x0 * x4) + 4 * (x1 * x3) + x2 * x2 + 76 * (x5 * x9) + 38 * (x6 * x8) + 38 * (x7 * x7)) < 2 ^ 61 ∧
    (2 * (x0 * x5) + 2 * (x1 * x4) + 2 * (x2 * x3) + 38 * (x6 * x9) + 38 * (x7 * x8)) < 2 ^ 61 ∧
    (2 * (x0 * x6) + 4 * (x1 * x5) + 2 * (x2 * x4) + 2 * (x3 * x3) + 76 * (x7 * x9) + 19 * (x8 * x8)) < 2 ^ 61 ∧
    (2 * (x0 * x7) + 2 * (x1 * x6) + 2 * (x2 * x5) + 2 * (x3 * x4) + 38 * (x8 * x9)) < 2 ^ 61 ∧
    (2 * (x0 * x8) + 4 * (x1 * x7) + 2 * (x2 * x6) + 4 * (x3 * x5) + x4 * x4 + 38 * (x9 * x9)) < 2 ^ 61 ∧
    (2 * (x0 * x9) + 2 * (x1 * x8) + 2 * (x2 * x7) + 2 * (x3 * x6) + 2 * (x4 * x5)) < 2 ^ 61 := by
  have p0_0 : x0 * x0 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx0)) (by decide)
  have p0_1 : x0 * x1 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx1)) (by decide)
  have p0_2 : x0 * x2 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx2)) (by decide)
  have p0_3 : x0 * x3 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx3)) (by decide)
  have p0_4 : x0 * x4 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx4)) (by decide)
  have p0_5 : x0 * x5 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx5)) (by decide)
  have p0_6 : x0 * x6 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx6)) (by decide)
  have p0_7 : x0 * x7 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx7)) (by decide)
  have p0_8 : x0 * x8 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx8)) (by decide)
  have p0_9 : x0 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx0) (Nat.le_pred_of_lt hx9)) (by decide)
  have p1_1 : x1 * x1 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx1)) (by decide)
  have p1_2 : x1 * x2 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx2)) (by decide)
  have p1_3 : x1 * x3 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx3)) (by decide)
  have p1_4 : x1 * x4 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx4)) (by decide)
  have p1_5 : x1 * x5 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx5)) (by decide)
  have p1_6 : x1 * x6 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx6)) (by decide)
  have p1_7 : x1 * x7 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx7)) (by decide)
  have p1_8 : x1 * x8 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx8)) (by decide)
  have p1_9 : x1 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx1) (Nat.le_pred_of_lt hx9)) (by decide)
  have p2_2 : x2 * x2 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx2)) (by decide)
  have p2_3 : x2 * x3 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx3)) (by decide)
  have p2_4 : x2 * x4 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx4)) (by decide)
  have p2_5 : x2 * x5 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx5)) (by decide)
  have p2_6 : x2 * x6 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx6)) (by decide)
  have p2_7 : x2 * x7 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx7)) (by decide)
  have p2_8 : x2 * x8 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx8)) (by decide)
  have p2_9 : x2 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx2) (Nat.le_pred_of_lt hx9)) (by decide)
  have p3_3 : x3 * x3 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx3)) (by decide)
  have p3_4 : x3 * x4 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx4)) (by decide)
  have p3_5 : x3 * x5 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx5)) (by decide)
  have p3_6 : x3 * x6 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx6)) (by decide)
  have p3_7 : x3 * x7 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx7)) (by decide)
  have p3_8 : x3 * x8 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx8)) (by decide)
  have p3_9 : x3 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx3) (Nat.le_pred_of_lt hx9)) (by decide)
  have p4_4 : x4 * x4 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx4)) (by decide)
  have p4_5 : x4 * x5 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx5)) (by decide)
  have p4_6 : x4 * x6 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx6)) (by decide)
  have p4_7 : x4 * x7 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx7)) (by decide)
  have p4_8 : x4 * x8 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx8)) (by decide)
  have p4_9 : x4 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx4) (Nat.le_pred_of_lt hx9)) (by decide)
  have p5_5 : x5 * x5 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx5)) (by decide)
  have p5_6 : x5 * x6 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx6)) (by decide)
  have p5_7 : x5 * x7 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx7)) (by decide)
  have p5_8 : x5 * x8 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx8)) (by decide)
  have p5_9 : x5 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx5) (Nat.le_pred_of_lt hx9)) (by decide)
  have p6_6 : x6 * x6 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hx6)) (by decide)
  have p6_7 : x6 * x7 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hx7)) (by decide)
  have p6_8 : x6 * x8 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hx8)) (by decide)
  have p6_9 : x6 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx6) (Nat.le_pred_of_lt hx9)) (by decide)
  have p7_7 : x7 * x7 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hx7)) (by decide)
  have p7_8 : x7 * x8 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hx8)) (by decide)
  have p7_9 : x7 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx7) (Nat.le_pred_of_lt hx9)) (by decide)
  have p8_8 : x8 * x8 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hx8)) (by decide)
  have p8_9 : x8 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx8) (Nat.le_pred_of_lt hx9)) (by decide)
  have p9_9 : x9 * x9 ≤ 4503599493152769 := Nat.le_trans (Nat.mul_le_mul (Nat.le_pred_of_lt hx9) (Nat.le_pred_of_lt hx9)) (by decide)
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem feSqZ_eq (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hx0 : x0 < 2 ^ 27) (hx1 : x1 < 2 ^ 27) (hx2 : x2 < 2 ^ 27) (hx3 : x3 < 2 ^ 27) (hx4 : x4 < 2 ^ 27) (hx5 : x5 < 2 ^ 27) (hx6 : x6 < 2 ^ 27) (hx7 : x7 < 2 ^ 27) (hx8 : x8 < 2 ^ 27) (hx9 : x9 < 2 ^ 27) :
    feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      [x0 * x0 + 76 * (x1 * x9) + 38 * (x2 * x8) + 76 * (x3 * x7) + 38 * (x4 * x6) + 38 * (x5 * x5),
        2 * (x0 * x1) + 38 * (x2 * x9) + 38 * (x3 * x8) + 38 * (x4 * x7) + 38 * (x5 * x6),
        2 * (x0 * x2) + 2 * (x1 * x1) + 76 * (x3 * x9) + 38 * (x4 * x8) + 76 * (x5 * x7) + 19 * (x6 * x6),
        2 * (x0 * x3) + 2 * (x1 * x2) + 38 * (x4 * x9) + 38 * (x5 * x8) + 38 * (x6 * x7),
        2 * (x0 * x4) + 4 * (x1 * x3) + x2 * x2 + 76 * (x5 * x9) + 38 * (x6 * x8) + 38 * (x7 * x7),
        2 * (x0 * x5) + 2 * (x1 * x4) + 2 * (x2 * x3) + 38 * (x6 * x9) + 38 * (x7 * x8),
        2 * (x0 * x6) + 4 * (x1 * x5) + 2 * (x2 * x4) + 2 * (x3 * x3) + 76 * (x7 * x9) + 19 * (x8 * x8),
        2 * (x0 * x7) + 2 * (x1 * x6) + 2 * (x2 * x5) + 2 * (x3 * x4) + 38 * (x8 * x9),
        2 * (x0 * x8) + 4 * (x1 * x7) + 2 * (x2 * x6) + 4 * (x3 * x5) + x4 * x4 + 38 * (x9 * x9),
        2 * (x0 * x9) + 2 * (x1 * x8) + 2 * (x2 * x7) + 2 * (x3 * x6) + 2 * (x4 * x5)] := by
  simp only [feSqZ]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  have hb := sq_bounds27 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9
  simp only [List.cons.injEq, and_true]
  exact ⟨mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega), mod_of_eq (by ring_eq) (by omega)⟩

theorem sq_canon (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) :
    ((x0 * x0 + 76 * (x1 * x9) + 38 * (x2 * x8) + 76 * (x3 * x7) + 38 * (x4 * x6) + 38 * (x5 * x5)) + 2 ^ 26 * (2 * (x0 * x1) + 38 * (x2 * x9) + 38 * (x3 * x8) + 38 * (x4 * x7) + 38 * (x5 * x6)) + 2 ^ 51 * (2 * (x0 * x2) + 2 * (x1 * x1) + 76 * (x3 * x9) + 38 * (x4 * x8) + 76 * (x5 * x7) + 19 * (x6 * x6)) + 2 ^ 77 * (2 * (x0 * x3) + 2 * (x1 * x2) + 38 * (x4 * x9) + 38 * (x5 * x8) + 38 * (x6 * x7)) + 2 ^ 102 * (2 * (x0 * x4) + 4 * (x1 * x3) + x2 * x2 + 76 * (x5 * x9) + 38 * (x6 * x8) + 38 * (x7 * x7)) + 2 ^ 128 * (2 * (x0 * x5) + 2 * (x1 * x4) + 2 * (x2 * x3) + 38 * (x6 * x9) + 38 * (x7 * x8)) + 2 ^ 153 * (2 * (x0 * x6) + 4 * (x1 * x5) + 2 * (x2 * x4) + 2 * (x3 * x3) + 76 * (x7 * x9) + 19 * (x8 * x8)) + 2 ^ 179 * (2 * (x0 * x7) + 2 * (x1 * x6) + 2 * (x2 * x5) + 2 * (x3 * x4) + 38 * (x8 * x9)) + 2 ^ 204 * (2 * (x0 * x8) + 4 * (x1 * x7) + 2 * (x2 * x6) + 4 * (x3 * x5) + x4 * x4 + 38 * (x9 * x9)) + 2 ^ 230 * (2 * (x0 * x9) + 2 * (x1 * x8) + 2 * (x2 * x7) + 2 * (x3 * x6) + 2 * (x4 * x5))) % Ed25519.p =
      ((x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9) * (x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9)) % Ed25519.p := by
  ring_mod

theorem sq2_canon (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) :
    ((2 * (x0 * x0 + 76 * (x1 * x9) + 38 * (x2 * x8) + 76 * (x3 * x7) + 38 * (x4 * x6) + 38 * (x5 * x5))) + 2 ^ 26 * (2 * (2 * (x0 * x1) + 38 * (x2 * x9) + 38 * (x3 * x8) + 38 * (x4 * x7) + 38 * (x5 * x6))) + 2 ^ 51 * (2 * (2 * (x0 * x2) + 2 * (x1 * x1) + 76 * (x3 * x9) + 38 * (x4 * x8) + 76 * (x5 * x7) + 19 * (x6 * x6))) + 2 ^ 77 * (2 * (2 * (x0 * x3) + 2 * (x1 * x2) + 38 * (x4 * x9) + 38 * (x5 * x8) + 38 * (x6 * x7))) + 2 ^ 102 * (2 * (2 * (x0 * x4) + 4 * (x1 * x3) + x2 * x2 + 76 * (x5 * x9) + 38 * (x6 * x8) + 38 * (x7 * x7))) + 2 ^ 128 * (2 * (2 * (x0 * x5) + 2 * (x1 * x4) + 2 * (x2 * x3) + 38 * (x6 * x9) + 38 * (x7 * x8))) + 2 ^ 153 * (2 * (2 * (x0 * x6) + 4 * (x1 * x5) + 2 * (x2 * x4) + 2 * (x3 * x3) + 76 * (x7 * x9) + 19 * (x8 * x8))) + 2 ^ 179 * (2 * (2 * (x0 * x7) + 2 * (x1 * x6) + 2 * (x2 * x5) + 2 * (x3 * x4) + 38 * (x8 * x9))) + 2 ^ 204 * (2 * (2 * (x0 * x8) + 4 * (x1 * x7) + 2 * (x2 * x6) + 4 * (x3 * x5) + x4 * x4 + 38 * (x9 * x9))) + 2 ^ 230 * (2 * (2 * (x0 * x9) + 2 * (x1 * x8) + 2 * (x2 * x7) + 2 * (x3 * x6) + 2 * (x4 * x5)))) % Ed25519.p =
      (2 * ((x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9) * (x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9))) % Ed25519.p := by
  ring_mod
theorem feMulSpec_ok (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Nat) (hx0 : x0 < 3 * 2 ^ 26) (hx1 : x1 < 3 * 2 ^ 26) (hx2 : x2 < 3 * 2 ^ 26) (hx3 : x3 < 3 * 2 ^ 26) (hx4 : x4 < 3 * 2 ^ 26) (hx5 : x5 < 3 * 2 ^ 26) (hx6 : x6 < 3 * 2 ^ 26) (hx7 : x7 < 3 * 2 ^ 26) (hx8 : x8 < 3 * 2 ^ 26) (hx9 : x9 < 3 * 2 ^ 26)
    (hy0 : y0 < 3 * 2 ^ 26) (hy1 : y1 < 3 * 2 ^ 26) (hy2 : y2 < 3 * 2 ^ 26) (hy3 : y3 < 3 * 2 ^ 26) (hy4 : y4 < 3 * 2 ^ 26) (hy5 : y5 < 3 * 2 ^ 26) (hy6 : y6 < 3 * 2 ^ 26) (hy7 : y7 < 3 * 2 ^ 26) (hy8 : y8 < 3 * 2 ^ 26) (hy9 : y9 < 3 * 2 ^ 26) :
    Lim (2 ^ 26) (feMulSpec x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) ∧
      fv (feMulSpec x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) =
        (x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9) % Ed25519.p * ((y0 + 2 ^ 26 * y1 + 2 ^ 51 * y2 + 2 ^ 77 * y3 + 2 ^ 102 * y4 + 2 ^ 128 * y5 + 2 ^ 153 * y6 + 2 ^ 179 * y7 + 2 ^ 204 * y8 + 2 ^ 230 * y9) % Ed25519.p) % Ed25519.p := by
  have hb := mul_bounds x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hy0 hy1 hy2 hy3 hy4 hy5 hy6 hy7 hy8 hy9
  have e : feMulSpec x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 = feReduceSpec (x0 * y0 + 38 * (x1 * y9) + 19 * (x2 * y8) + 38 * (x3 * y7) + 19 * (x4 * y6) + 38 * (x5 * y5) + 19 * (x6 * y4) + 38 * (x7 * y3) + 19 * (x8 * y2) + 38 * (x9 * y1)) (x0 * y1 + x1 * y0 + 19 * (x2 * y9) + 19 * (x3 * y8) + 19 * (x4 * y7) + 19 * (x5 * y6) + 19 * (x6 * y5) + 19 * (x7 * y4) + 19 * (x8 * y3) + 19 * (x9 * y2)) (x0 * y2 + 2 * (x1 * y1) + x2 * y0 + 38 * (x3 * y9) + 19 * (x4 * y8) + 38 * (x5 * y7) + 19 * (x6 * y6) + 38 * (x7 * y5) + 19 * (x8 * y4) + 38 * (x9 * y3)) (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 + 19 * (x4 * y9) + 19 * (x5 * y8) + 19 * (x6 * y7) + 19 * (x7 * y6) + 19 * (x8 * y5) + 19 * (x9 * y4)) (x0 * y4 + 2 * (x1 * y3) + x2 * y2 + 2 * (x3 * y1) + x4 * y0 + 38 * (x5 * y9) + 19 * (x6 * y8) + 38 * (x7 * y7) + 19 * (x8 * y6) + 38 * (x9 * y5)) (x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0 + 19 * (x6 * y9) + 19 * (x7 * y8) + 19 * (x8 * y7) + 19 * (x9 * y6)) (x0 * y6 + 2 * (x1 * y5) + x2 * y4 + 2 * (x3 * y3) + x4 * y2 + 2 * (x5 * y1) + x6 * y0 + 38 * (x7 * y9) + 19 * (x8 * y8) + 38 * (x9 * y7)) (x0 * y7 + x1 * y6 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2 + x6 * y1 + x7 * y0 + 19 * (x8 * y9) + 19 * (x9 * y8)) (x0 * y8 + 2 * (x1 * y7) + x2 * y6 + 2 * (x3 * y5) + x4 * y4 + 2 * (x5 * y3) + x6 * y2 + 2 * (x7 * y1) + x8 * y0 + 38 * (x9 * y9)) (x0 * y9 + x1 * y8 + x2 * y7 + x3 * y6 + x4 * y5 + x5 * y4 + x6 * y3 + x7 * y2 + x8 * y1 + x9 * y0) := by
    unfold feMulSpec; rw [feMulZ_eq x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hy0 hy1 hy2 hy3 hy4 hy5 hy6 hy7 hy8 hy9]; rfl
  rw [e]
  obtain ⟨hL, hv⟩ := feReduce_ok _ _ _ _ _ _ _ _ _ _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2
  exact ⟨hL, by rw [hv, mul_canon, Nat.mul_mod]⟩

theorem feSq_ok (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hx0 : x0 < 2 ^ 27) (hx1 : x1 < 2 ^ 27) (hx2 : x2 < 2 ^ 27) (hx3 : x3 < 2 ^ 27) (hx4 : x4 < 2 ^ 27) (hx5 : x5 < 2 ^ 27) (hx6 : x6 < 2 ^ 27) (hx7 : x7 < 2 ^ 27) (hx8 : x8 < 2 ^ 27) (hx9 : x9 < 2 ^ 27) :
    Lim (2 ^ 26) (feReduceSpec (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[0]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[1]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[2]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[3]!
      (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[4]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[5]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[6]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[7]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[8]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[9]!) ∧
    fv (feReduceSpec (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[0]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[1]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[2]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[3]!
      (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[4]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[5]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[6]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[7]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[8]! (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[9]!) =
        (x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9) % Ed25519.p * ((x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9) % Ed25519.p) % Ed25519.p := by
  have hb := sq_bounds27 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9
  rw [feSqZ_eq x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
  obtain ⟨hL, hv⟩ := feReduce_ok _ _ _ _ _ _ _ _ _ _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2
  exact ⟨hL, by rw [hv, sq_canon, Nat.mul_mod]⟩

theorem feSq2_ok (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) (hx0 : x0 < 2 ^ 26) (hx1 : x1 < 2 ^ 26) (hx2 : x2 < 2 ^ 26) (hx3 : x3 < 2 ^ 26) (hx4 : x4 < 2 ^ 26) (hx5 : x5 < 2 ^ 26) (hx6 : x6 < 2 ^ 26) (hx7 : x7 < 2 ^ 26) (hx8 : x8 < 2 ^ 26) (hx9 : x9 < 2 ^ 26) :
    Lim (2 ^ 26) (feReduceSpec (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[0]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[1]! % 2 ^ 64)
      (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[2]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[3]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[4]! % 2 ^ 64)
      (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[5]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[6]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[7]! % 2 ^ 64)
      (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[8]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[9]! % 2 ^ 64)) ∧
    fv (feReduceSpec (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[0]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[1]! % 2 ^ 64)
      (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[2]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[3]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[4]! % 2 ^ 64)
      (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[5]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[6]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[7]! % 2 ^ 64)
      (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[8]! % 2 ^ 64) (2 * (feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)[9]! % 2 ^ 64)) =
        2 * ((x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9) % Ed25519.p * ((x0 + 2 ^ 26 * x1 + 2 ^ 51 * x2 + 2 ^ 77 * x3 + 2 ^ 102 * x4 + 2 ^ 128 * x5 + 2 ^ 153 * x6 + 2 ^ 179 * x7 + 2 ^ 204 * x8 + 2 ^ 230 * x9) % Ed25519.p)) % Ed25519.p := by
  have hb := sq_bounds26 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9
  rw [feSqZ_eq x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  obtain ⟨hL, hv⟩ := feReduce_ok (2 * (x0 * x0 + 76 * (x1 * x9) + 38 * (x2 * x8) + 76 * (x3 * x7) + 38 * (x4 * x6) + 38 * (x5 * x5))) (2 * (2 * (x0 * x1) + 38 * (x2 * x9) + 38 * (x3 * x8) + 38 * (x4 * x7) + 38 * (x5 * x6))) (2 * (2 * (x0 * x2) + 2 * (x1 * x1) + 76 * (x3 * x9) + 38 * (x4 * x8) + 76 * (x5 * x7) + 19 * (x6 * x6))) (2 * (2 * (x0 * x3) + 2 * (x1 * x2) + 38 * (x4 * x9) + 38 * (x5 * x8) + 38 * (x6 * x7))) (2 * (2 * (x0 * x4) + 4 * (x1 * x3) + x2 * x2 + 76 * (x5 * x9) + 38 * (x6 * x8) + 38 * (x7 * x7))) (2 * (2 * (x0 * x5) + 2 * (x1 * x4) + 2 * (x2 * x3) + 38 * (x6 * x9) + 38 * (x7 * x8))) (2 * (2 * (x0 * x6) + 4 * (x1 * x5) + 2 * (x2 * x4) + 2 * (x3 * x3) + 76 * (x7 * x9) + 19 * (x8 * x8))) (2 * (2 * (x0 * x7) + 2 * (x1 * x6) + 2 * (x2 * x5) + 2 * (x3 * x4) + 38 * (x8 * x9))) (2 * (2 * (x0 * x8) + 4 * (x1 * x7) + 2 * (x2 * x6) + 4 * (x3 * x5) + x4 * x4 + 38 * (x9 * x9))) (2 * (2 * (x0 * x9) + 2 * (x1 * x8) + 2 * (x2 * x7) + 2 * (x3 * x6) + 2 * (x4 * x5)))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact ⟨hL, by rw [hv, sq2_canon, two_sq_mod]⟩

theorem feAdd_ok {a b : List Nat} {A B : Nat} (ha : Lim A a) (hb : Lim B b) (hAB : A + B ≤ 2 ^ 32) :
    Lim (A + B) [(a.getD 0 0 + b.getD 0 0) % 2 ^ 32,
      (a.getD 1 0 + b.getD 1 0) % 2 ^ 32,
      (a.getD 2 0 + b.getD 2 0) % 2 ^ 32,
      (a.getD 3 0 + b.getD 3 0) % 2 ^ 32,
      (a.getD 4 0 + b.getD 4 0) % 2 ^ 32,
      (a.getD 5 0 + b.getD 5 0) % 2 ^ 32,
      (a.getD 6 0 + b.getD 6 0) % 2 ^ 32,
      (a.getD 7 0 + b.getD 7 0) % 2 ^ 32,
      (a.getD 8 0 + b.getD 8 0) % 2 ^ 32,
      (a.getD 9 0 + b.getD 9 0) % 2 ^ 32] ∧
    fv [(a.getD 0 0 + b.getD 0 0) % 2 ^ 32,
      (a.getD 1 0 + b.getD 1 0) % 2 ^ 32,
      (a.getD 2 0 + b.getD 2 0) % 2 ^ 32,
      (a.getD 3 0 + b.getD 3 0) % 2 ^ 32,
      (a.getD 4 0 + b.getD 4 0) % 2 ^ 32,
      (a.getD 5 0 + b.getD 5 0) % 2 ^ 32,
      (a.getD 6 0 + b.getD 6 0) % 2 ^ 32,
      (a.getD 7 0 + b.getD 7 0) % 2 ^ 32,
      (a.getD 8 0 + b.getD 8 0) % 2 ^ 32,
      (a.getD 9 0 + b.getD 9 0) % 2 ^ 32] = (fv a + fv b) % Ed25519.p := by
  obtain ⟨-, ha⟩ := ha
  obtain ⟨-, hb⟩ := hb
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  have a5 := ha 5 (by decide)
  have a6 := ha 6 (by decide)
  have a7 := ha 7 (by decide)
  have a8 := ha 8 (by decide)
  have a9 := ha 9 (by decide)
  have b0 := hb 0 (by decide)
  have b1 := hb 1 (by decide)
  have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide)
  have b4 := hb 4 (by decide)
  have b5 := hb 5 (by decide)
  have b6 := hb 6 (by decide)
  have b7 := hb 7 (by decide)
  have b8 := hb 8 (by decide)
  have b9 := hb 9 (by decide)
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_succ, List.getD_cons_zero] <;> omega
  · unfold fv
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← Nat.add_mod]
    congr 1
    ring_eq

theorem bv_sub_toNat (a c b : Nat) (ha : a < 2 ^ 28) (hc : c < 2 ^ 31) (hb : b ≤ c) :
    (BitVec.ofNat 32 a + BitVec.ofNat 32 c - BitVec.ofNat 32 b).toNat = a + c - b := by
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 4000000 in
theorem feSub_ok {x y : List Nat} (hx : Lim (2 ^ 27) x) (hy : Lim (2 ^ 27) y) :
    Lim (2 ^ 26) (feReduceSpec (BitVec.ofNat 32 (x.getD 0 0) + 0x3FFFFED0 - BitVec.ofNat 32 (y.getD 0 0)).toNat
      (BitVec.ofNat 32 (x.getD 1 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 1 0)).toNat
      (BitVec.ofNat 32 (x.getD 2 0) + 0x3FFFFFF0 - BitVec.ofNat 32 (y.getD 2 0)).toNat
      (BitVec.ofNat 32 (x.getD 3 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 3 0)).toNat
      (BitVec.ofNat 32 (x.getD 4 0) + 0x3FFFFFF0 - BitVec.ofNat 32 (y.getD 4 0)).toNat
      (BitVec.ofNat 32 (x.getD 5 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 5 0)).toNat
      (BitVec.ofNat 32 (x.getD 6 0) + 0x3FFFFFF0 - BitVec.ofNat 32 (y.getD 6 0)).toNat
      (BitVec.ofNat 32 (x.getD 7 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 7 0)).toNat
      (BitVec.ofNat 32 (x.getD 8 0) + 0x3FFFFFF0 - BitVec.ofNat 32 (y.getD 8 0)).toNat
      (BitVec.ofNat 32 (x.getD 9 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 9 0)).toNat) ∧
    fv (feReduceSpec (BitVec.ofNat 32 (x.getD 0 0) + 0x3FFFFED0 - BitVec.ofNat 32 (y.getD 0 0)).toNat
      (BitVec.ofNat 32 (x.getD 1 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 1 0)).toNat
      (BitVec.ofNat 32 (x.getD 2 0) + 0x3FFFFFF0 - BitVec.ofNat 32 (y.getD 2 0)).toNat
      (BitVec.ofNat 32 (x.getD 3 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 3 0)).toNat
      (BitVec.ofNat 32 (x.getD 4 0) + 0x3FFFFFF0 - BitVec.ofNat 32 (y.getD 4 0)).toNat
      (BitVec.ofNat 32 (x.getD 5 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 5 0)).toNat
      (BitVec.ofNat 32 (x.getD 6 0) + 0x3FFFFFF0 - BitVec.ofNat 32 (y.getD 6 0)).toNat
      (BitVec.ofNat 32 (x.getD 7 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 7 0)).toNat
      (BitVec.ofNat 32 (x.getD 8 0) + 0x3FFFFFF0 - BitVec.ofNat 32 (y.getD 8 0)).toNat
      (BitVec.ofNat 32 (x.getD 9 0) + 0x1FFFFFF0 - BitVec.ofNat 32 (y.getD 9 0)).toNat) = (fv x + Ed25519.p - fv y) % Ed25519.p := by
  obtain ⟨-, hx⟩ := hx
  obtain ⟨-, hy⟩ := hy
  have a0 := hx 0 (by decide)
  have a1 := hx 1 (by decide)
  have a2 := hx 2 (by decide)
  have a3 := hx 3 (by decide)
  have a4 := hx 4 (by decide)
  have a5 := hx 5 (by decide)
  have a6 := hx 6 (by decide)
  have a7 := hx 7 (by decide)
  have a8 := hx 8 (by decide)
  have a9 := hx 9 (by decide)
  have b0 := hy 0 (by decide)
  have b1 := hy 1 (by decide)
  have b2 := hy 2 (by decide)
  have b3 := hy 3 (by decide)
  have b4 := hy 4 (by decide)
  have b5 := hy 5 (by decide)
  have b6 := hy 6 (by decide)
  have b7 := hy 7 (by decide)
  have b8 := hy 8 (by decide)
  have b9 := hy 9 (by decide)
  simp only [BitVec.ofNat_eq_ofNat]
  simp (disch := omega) only [bv_sub_toNat]
  obtain ⟨hL, hv⟩ := feReduce_ok (x.getD 0 0 + 1073741520 - y.getD 0 0) (x.getD 1 0 + 536870896 - y.getD 1 0) (x.getD 2 0 + 1073741808 - y.getD 2 0) (x.getD 3 0 + 536870896 - y.getD 3 0) (x.getD 4 0 + 1073741808 - y.getD 4 0) (x.getD 5 0 + 536870896 - y.getD 5 0) (x.getD 6 0 + 1073741808 - y.getD 6 0) (x.getD 7 0 + 536870896 - y.getD 7 0) (x.getD 8 0 + 1073741808 - y.getD 8 0) (x.getD 9 0 + 536870896 - y.getD 9 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨hL, ?_⟩
  rw [hv]
  unfold fv Ed25519.p
  omega
end C3.RV32.EdM
