import C3BootProofs.Models.Ed25519Field
import C3BootProofs.Proofs.FeToBytesSpec

/-!
# Canonical bytes of a field element

`reduce` returns limbs below 2^26, except limbs 3, 7, and 9, which are below
2^25, whatever its input (`feReduce_redB`).
`to_bytes` of such limbs spells their value modulo `p` (`feToBytes_val`),
because that value is below `2p`.
-/

namespace C3.RV32.EdM

/-- The little-endian number that 32 byte values spell. -/
def leB32 (b : List Nat) : Nat :=
  b.getD 0 0 + 2 ^ 8 * b.getD 1 0 + 2 ^ 16 * b.getD 2 0 + 2 ^ 24 * b.getD 3 0 + 2 ^ 32 * b.getD 4 0 +
    2 ^ 40 * b.getD 5 0 + 2 ^ 48 * b.getD 6 0 + 2 ^ 56 * b.getD 7 0 + 2 ^ 64 * b.getD 8 0 + 2 ^ 72 * b.getD 9 0 +
    2 ^ 80 * b.getD 10 0 + 2 ^ 88 * b.getD 11 0 + 2 ^ 96 * b.getD 12 0 + 2 ^ 104 * b.getD 13 0 +
    2 ^ 112 * b.getD 14 0 + 2 ^ 120 * b.getD 15 0 + 2 ^ 128 * b.getD 16 0 + 2 ^ 136 * b.getD 17 0 +
    2 ^ 144 * b.getD 18 0 + 2 ^ 152 * b.getD 19 0 + 2 ^ 160 * b.getD 20 0 + 2 ^ 168 * b.getD 21 0 +
    2 ^ 176 * b.getD 22 0 + 2 ^ 184 * b.getD 23 0 + 2 ^ 192 * b.getD 24 0 + 2 ^ 200 * b.getD 25 0 +
    2 ^ 208 * b.getD 26 0 + 2 ^ 216 * b.getD 27 0 + 2 ^ 224 * b.getD 28 0 + 2 ^ 232 * b.getD 29 0 +
    2 ^ 240 * b.getD 30 0 + 2 ^ 248 * b.getD 31 0

/-- The limb bounds that `reduce` leaves. -/
structure RedB (l : List Nat) : Prop where
  len : l.length = 10
  b0 : l.getD 0 0 < 2 ^ 26
  b1 : l.getD 1 0 < 2 ^ 26
  b2 : l.getD 2 0 < 2 ^ 26
  b3 : l.getD 3 0 < 2 ^ 25
  b4 : l.getD 4 0 < 2 ^ 26
  b5 : l.getD 5 0 < 2 ^ 26
  b6 : l.getD 6 0 < 2 ^ 26
  b7 : l.getD 7 0 < 2 ^ 25
  b8 : l.getD 8 0 < 2 ^ 26
  b9 : l.getD 9 0 < 2 ^ 25

theorem red_lt (a b c : Nat) (hc : c < 2 ^ 44) :
    (a % 2 ^ 25 + (b % 2 ^ 26 + c) % 2 ^ 64 / 2 ^ 26) % 2 ^ 64 % 2 ^ 32 < 2 ^ 26 := by
  have ha := Nat.mod_lt a (show 0 < 2 ^ 25 by decide)
  have hb := Nat.mod_lt b (show 0 < 2 ^ 26 by decide)
  generalize a % 2 ^ 25 = A at *
  generalize b % 2 ^ 26 = B at *
  omega

theorem c_lt (y : Nat) : 19 * (y % 2 ^ 64 / 2 ^ 25) % 2 ^ 64 < 2 ^ 44 := by
  have h := Nat.mod_lt y (show 0 < 2 ^ 64 by decide)
  generalize y % 2 ^ 64 = Y at *
  have h2 : Y / 2 ^ 25 < 2 ^ 39 := by omega
  generalize Y / 2 ^ 25 = Z at *
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem c_lt' (y : Nat) : y % 2 ^ 64 / 2 ^ 25 < 2 ^ 44 := by
  have h := Nat.mod_lt y (show 0 < 2 ^ 64 by decide)
  generalize y % 2 ^ 64 = Y at *
  omega

set_option maxHeartbeats 4000000 in
theorem feReduce_redB (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : Nat) :
    RedB (feReduceSpec z0 z1 z2 z3 z4 z5 z6 z7 z8 z9) := by
  refine ⟨?_, ?_, red_lt _ _ _ (c_lt _), ?_, ?_, ?_, red_lt _ _ _ (c_lt' _), ?_, ?_, ?_, ?_⟩ <;>
    simp only [feReduceSpec, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil] <;> omega

theorem RedB.lim {l : List Nat} (h : RedB l) : Lim (2 ^ 26) l := by
  refine ⟨h.len, fun i hi => ?_⟩
  have := h.b0; have := h.b1; have := h.b2; have := h.b3; have := h.b4; have := h.b5; have := h.b6
  have := h.b7; have := h.b8; have := h.b9
  match i, hi with
  | 0, _ => omega | 1, _ => omega | 2, _ => omega | 3, _ => omega | 4, _ => omega
  | 5, _ => omega | 6, _ => omega | 7, _ => omega | 8, _ => omega | 9, _ => omega

set_option maxHeartbeats 4000000 in
/-- The packed bytes of ten carried limbs spell their radix-2^25.5 value. -/
theorem pack_val (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Nat) (b0 : c0 < 2 ^ 26) (b1 : c1 < 2 ^ 25)
    (b2 : c2 < 2 ^ 26) (b3 : c3 < 2 ^ 25) (b4 : c4 < 2 ^ 26) (b5 : c5 < 2 ^ 25) (b6 : c6 < 2 ^ 26)
    (b7 : c7 < 2 ^ 25) (b8 : c8 < 2 ^ 26) (b9 : c9 < 2 ^ 25) :
    leB32 [c0 % 2 ^ 8, c0 / 2 ^ 8 % 2 ^ 8, c0 / 2 ^ 16 % 2 ^ 8, (c0 / 2 ^ 24 + c1 * 2 ^ 2 % 2 ^ 32) % 2 ^ 8,
       c1 / 2 ^ 6 % 2 ^ 8, c1 / 2 ^ 14 % 2 ^ 8, (c1 / 2 ^ 22 + c2 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8,
       c2 / 2 ^ 5 % 2 ^ 8, c2 / 2 ^ 13 % 2 ^ 8, (c2 / 2 ^ 21 + c3 * 2 ^ 5 % 2 ^ 32) % 2 ^ 8,
       c3 / 2 ^ 3 % 2 ^ 8, c3 / 2 ^ 11 % 2 ^ 8, (c3 / 2 ^ 19 + c4 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8,
       c4 / 2 ^ 2 % 2 ^ 8, c4 / 2 ^ 10 % 2 ^ 8, c4 / 2 ^ 18 % 2 ^ 8,
       c5 % 2 ^ 8, c5 / 2 ^ 8 % 2 ^ 8, c5 / 2 ^ 16 % 2 ^ 8, (c5 / 2 ^ 24 + c6 * 2 ^ 1 % 2 ^ 32) % 2 ^ 8,
       c6 / 2 ^ 7 % 2 ^ 8, c6 / 2 ^ 15 % 2 ^ 8, (c6 / 2 ^ 23 + c7 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8,
       c7 / 2 ^ 5 % 2 ^ 8, c7 / 2 ^ 13 % 2 ^ 8, (c7 / 2 ^ 21 + c8 * 2 ^ 4 % 2 ^ 32) % 2 ^ 8,
       c8 / 2 ^ 4 % 2 ^ 8, c8 / 2 ^ 12 % 2 ^ 8, (c8 / 2 ^ 20 + c9 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8,
       c9 / 2 ^ 2 % 2 ^ 8, c9 / 2 ^ 10 % 2 ^ 8, c9 / 2 ^ 18 % 2 ^ 8] =
      c0 + 2 ^ 26 * c1 + 2 ^ 51 * c2 + 2 ^ 77 * c3 + 2 ^ 102 * c4 + 2 ^ 128 * c5 + 2 ^ 153 * c6 +
        2 ^ 179 * c7 + 2 ^ 204 * c8 + 2 ^ 230 * c9 := by
  have j3 : (c0 / 2 ^ 24 + c1 * 2 ^ 2 % 2 ^ 32) % 2 ^ 8 = c0 / 2 ^ 24 + c1 % 2 ^ 6 * 2 ^ 2 := by omega
  have j6 : (c1 / 2 ^ 22 + c2 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8 = c1 / 2 ^ 22 + c2 % 2 ^ 5 * 2 ^ 3 := by omega
  have j9 : (c2 / 2 ^ 21 + c3 * 2 ^ 5 % 2 ^ 32) % 2 ^ 8 = c2 / 2 ^ 21 + c3 % 2 ^ 3 * 2 ^ 5 := by omega
  have j12 : (c3 / 2 ^ 19 + c4 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8 = c3 / 2 ^ 19 + c4 % 2 ^ 2 * 2 ^ 6 := by omega
  have j19 : (c5 / 2 ^ 24 + c6 * 2 ^ 1 % 2 ^ 32) % 2 ^ 8 = c5 / 2 ^ 24 + c6 % 2 ^ 7 * 2 ^ 1 := by omega
  have j22 : (c6 / 2 ^ 23 + c7 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8 = c6 / 2 ^ 23 + c7 % 2 ^ 5 * 2 ^ 3 := by omega
  have j25 : (c7 / 2 ^ 21 + c8 * 2 ^ 4 % 2 ^ 32) % 2 ^ 8 = c7 / 2 ^ 21 + c8 % 2 ^ 4 * 2 ^ 4 := by omega
  have j28 : (c8 / 2 ^ 20 + c9 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8 = c8 / 2 ^ 20 + c9 % 2 ^ 2 * 2 ^ 6 := by omega
  rw [j3, j6, j9, j12, j19, j22, j25, j28]
  have d0 : c0 = c0 % 2 ^ 8 + 2 ^ 8 * (c0 / 2 ^ 8 % 2 ^ 8) + 2 ^ 16 * (c0 / 2 ^ 16 % 2 ^ 8) +
    2 ^ 24 * (c0 / 2 ^ 24) := by omega
  have d1 : c1 = c1 % 2 ^ 6 + 2 ^ 6 * (c1 / 2 ^ 6 % 2 ^ 8) + 2 ^ 14 * (c1 / 2 ^ 14 % 2 ^ 8) +
    2 ^ 22 * (c1 / 2 ^ 22) := by omega
  have d2 : c2 = c2 % 2 ^ 5 + 2 ^ 5 * (c2 / 2 ^ 5 % 2 ^ 8) + 2 ^ 13 * (c2 / 2 ^ 13 % 2 ^ 8) +
    2 ^ 21 * (c2 / 2 ^ 21) := by omega
  have d3 : c3 = c3 % 2 ^ 3 + 2 ^ 3 * (c3 / 2 ^ 3 % 2 ^ 8) + 2 ^ 11 * (c3 / 2 ^ 11 % 2 ^ 8) +
    2 ^ 19 * (c3 / 2 ^ 19) := by omega
  have d4 : c4 = c4 % 2 ^ 2 + 2 ^ 2 * (c4 / 2 ^ 2 % 2 ^ 8) + 2 ^ 10 * (c4 / 2 ^ 10 % 2 ^ 8) +
    2 ^ 18 * (c4 / 2 ^ 18 % 2 ^ 8) := by omega
  have d5 : c5 = c5 % 2 ^ 8 + 2 ^ 8 * (c5 / 2 ^ 8 % 2 ^ 8) + 2 ^ 16 * (c5 / 2 ^ 16 % 2 ^ 8) +
    2 ^ 24 * (c5 / 2 ^ 24) := by omega
  have d6 : c6 = c6 % 2 ^ 7 + 2 ^ 7 * (c6 / 2 ^ 7 % 2 ^ 8) + 2 ^ 15 * (c6 / 2 ^ 15 % 2 ^ 8) +
    2 ^ 23 * (c6 / 2 ^ 23) := by omega
  have d7 : c7 = c7 % 2 ^ 5 + 2 ^ 5 * (c7 / 2 ^ 5 % 2 ^ 8) + 2 ^ 13 * (c7 / 2 ^ 13 % 2 ^ 8) +
    2 ^ 21 * (c7 / 2 ^ 21) := by omega
  have d8 : c8 = c8 % 2 ^ 4 + 2 ^ 4 * (c8 / 2 ^ 4 % 2 ^ 8) + 2 ^ 12 * (c8 / 2 ^ 12 % 2 ^ 8) +
    2 ^ 20 * (c8 / 2 ^ 20) := by omega
  have d9 : c9 = c9 % 2 ^ 2 + 2 ^ 2 * (c9 / 2 ^ 2 % 2 ^ 8) + 2 ^ 10 * (c9 / 2 ^ 10 % 2 ^ 8) +
    2 ^ 18 * (c9 / 2 ^ 18 % 2 ^ 8) := by omega
  generalize c0 % 2 ^ 8 = e00 at d0 ⊢
  generalize c0 / 2 ^ 8 % 2 ^ 8 = e01 at d0 ⊢
  generalize c0 / 2 ^ 16 % 2 ^ 8 = e02 at d0 ⊢
  generalize c0 / 2 ^ 24 = e03 at d0 ⊢
  generalize c1 % 2 ^ 6 = e10 at d1 ⊢
  generalize c1 / 2 ^ 6 % 2 ^ 8 = e11 at d1 ⊢
  generalize c1 / 2 ^ 14 % 2 ^ 8 = e12 at d1 ⊢
  generalize c1 / 2 ^ 22 = e13 at d1 ⊢
  generalize c2 % 2 ^ 5 = e20 at d2 ⊢
  generalize c2 / 2 ^ 5 % 2 ^ 8 = e21 at d2 ⊢
  generalize c2 / 2 ^ 13 % 2 ^ 8 = e22 at d2 ⊢
  generalize c2 / 2 ^ 21 = e23 at d2 ⊢
  generalize c3 % 2 ^ 3 = e30 at d3 ⊢
  generalize c3 / 2 ^ 3 % 2 ^ 8 = e31 at d3 ⊢
  generalize c3 / 2 ^ 11 % 2 ^ 8 = e32 at d3 ⊢
  generalize c3 / 2 ^ 19 = e33 at d3 ⊢
  generalize c4 % 2 ^ 2 = e40 at d4 ⊢
  generalize c4 / 2 ^ 2 % 2 ^ 8 = e41 at d4 ⊢
  generalize c4 / 2 ^ 10 % 2 ^ 8 = e42 at d4 ⊢
  generalize c4 / 2 ^ 18 % 2 ^ 8 = e43 at d4 ⊢
  generalize c5 % 2 ^ 8 = e50 at d5 ⊢
  generalize c5 / 2 ^ 8 % 2 ^ 8 = e51 at d5 ⊢
  generalize c5 / 2 ^ 16 % 2 ^ 8 = e52 at d5 ⊢
  generalize c5 / 2 ^ 24 = e53 at d5 ⊢
  generalize c6 % 2 ^ 7 = e60 at d6 ⊢
  generalize c6 / 2 ^ 7 % 2 ^ 8 = e61 at d6 ⊢
  generalize c6 / 2 ^ 15 % 2 ^ 8 = e62 at d6 ⊢
  generalize c6 / 2 ^ 23 = e63 at d6 ⊢
  generalize c7 % 2 ^ 5 = e70 at d7 ⊢
  generalize c7 / 2 ^ 5 % 2 ^ 8 = e71 at d7 ⊢
  generalize c7 / 2 ^ 13 % 2 ^ 8 = e72 at d7 ⊢
  generalize c7 / 2 ^ 21 = e73 at d7 ⊢
  generalize c8 % 2 ^ 4 = e80 at d8 ⊢
  generalize c8 / 2 ^ 4 % 2 ^ 8 = e81 at d8 ⊢
  generalize c8 / 2 ^ 12 % 2 ^ 8 = e82 at d8 ⊢
  generalize c8 / 2 ^ 20 = e83 at d8 ⊢
  generalize c9 % 2 ^ 2 = e90 at d9 ⊢
  generalize c9 / 2 ^ 2 % 2 ^ 8 = e91 at d9 ⊢
  generalize c9 / 2 ^ 10 % 2 ^ 8 = e92 at d9 ⊢
  generalize c9 / 2 ^ 18 % 2 ^ 8 = e93 at d9 ⊢
  simp only [leB32, List.getD_cons_succ, List.getD_cons_zero]
  omega

theorem qstep {A h Q k m n : Nat} (hq : Q = A / 2 ^ k) (hlt : h + Q < 2 ^ 32) (hn : k + m = n) :
    (h + Q) % 2 ^ 32 / 2 ^ m = (A + 2 ^ k * h) / 2 ^ n := by
  subst hq hn
  rw [Nat.mod_eq_of_lt hlt, Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
    Nat.add_comm]

theorem carry_fin {H V K Q : Nat} (hH : H < 2 ^ 255 + 2 ^ 154) (hV : V < 2 ^ 255) (hq : Q = (H + 19) / 2 ^ 255)
    (hv : V + 2 ^ 255 * K = H + 19 * Q) : V = H % Ed25519.p := by
  have hp : Ed25519.p = 2 ^ 255 - 19 := rfl
  rcases Nat.lt_or_ge (H + 19) (2 ^ 255) with h | h
  · have q0 : Q = 0 := by rw [hq]; exact Nat.div_eq_of_lt h
    subst q0
    rw [Nat.mod_eq_of_lt (by rw [hp]; omega)]
    omega
  · have q1 : Q = 1 := by rw [hq]; omega
    subst q1
    rw [Nat.mod_eq_sub_mod (by rw [hp]; omega), Nat.mod_eq_of_lt (by rw [hp]; omega)]
    rw [hp]
    omega

set_option maxHeartbeats 4000000 in
/-- The quotient and carry chains of `to_bytes`: the carried limbs spell the
value modulo `p`. -/
theorem carry_val {h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10
    C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 : Nat} (b0 : h0 < 2 ^ 26) (b1 : h1 < 2 ^ 26)
    (b2 : h2 < 2 ^ 26) (b3 : h3 < 2 ^ 25) (b4 : h4 < 2 ^ 26) (b5 : h5 < 2 ^ 26) (b6 : h6 < 2 ^ 26)
    (b7 : h7 < 2 ^ 25) (b8 : h8 < 2 ^ 26) (b9 : h9 < 2 ^ 25)
    (hQ1 : (h0 + 19) % 2 ^ 32 / 2 ^ 26 = Q1)
    (hQ2 : (h1 + Q1) % 2 ^ 32 / 2 ^ 25 = Q2)
    (hQ3 : (h2 + Q2) % 2 ^ 32 / 2 ^ 26 = Q3)
    (hQ4 : (h3 + Q3) % 2 ^ 32 / 2 ^ 25 = Q4)
    (hQ5 : (h4 + Q4) % 2 ^ 32 / 2 ^ 26 = Q5)
    (hQ6 : (h5 + Q5) % 2 ^ 32 / 2 ^ 25 = Q6)
    (hQ7 : (h6 + Q6) % 2 ^ 32 / 2 ^ 26 = Q7)
    (hQ8 : (h7 + Q7) % 2 ^ 32 / 2 ^ 25 = Q8)
    (hQ9 : (h8 + Q8) % 2 ^ 32 / 2 ^ 26 = Q9)
    (hQ10 : (h9 + Q9) % 2 ^ 32 / 2 ^ 25 = Q10)
    (hC0 : (h0 + 19 * Q10 % 2 ^ 32) % 2 ^ 32 = C0)
    (hC1 : (h1 + C0 / 2 ^ 26) % 2 ^ 32 = C1)
    (hC2 : (h2 + C1 / 2 ^ 25) % 2 ^ 32 = C2)
    (hC3 : (h3 + C2 / 2 ^ 26) % 2 ^ 32 = C3)
    (hC4 : (h4 + C3 / 2 ^ 25) % 2 ^ 32 = C4)
    (hC5 : (h5 + C4 / 2 ^ 26) % 2 ^ 32 = C5)
    (hC6 : (h6 + C5 / 2 ^ 25) % 2 ^ 32 = C6)
    (hC7 : (h7 + C6 / 2 ^ 26) % 2 ^ 32 = C7)
    (hC8 : (h8 + C7 / 2 ^ 25) % 2 ^ 32 = C8)
    (hC9 : (h9 + C8 / 2 ^ 26) % 2 ^ 32 = C9) :
    C0 % 2 ^ 26 + 2 ^ 26 * (C1 % 2 ^ 25) + 2 ^ 51 * (C2 % 2 ^ 26) + 2 ^ 77 * (C3 % 2 ^ 25) +
      2 ^ 102 * (C4 % 2 ^ 26) + 2 ^ 128 * (C5 % 2 ^ 25) + 2 ^ 153 * (C6 % 2 ^ 26) + 2 ^ 179 * (C7 % 2 ^ 25) +
      2 ^ 204 * (C8 % 2 ^ 26) + 2 ^ 230 * (C9 % 2 ^ 25) =
    (h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 +
      2 ^ 179 * h7 + 2 ^ 204 * h8 + 2 ^ 230 * h9) % Ed25519.p := by
  have q1 : Q1 = (h0 + 19) / 2 ^ 26 := by omega
  have q2 : Q2 = (h0 + 19 + 2 ^ 26 * h1) / 2 ^ 51 := by
    rw [← hQ2]; exact qstep q1 (by omega) rfl
  have q3 : Q3 = (h0 + 19 + 2 ^ 26 * h1 + 2 ^ 51 * h2) / 2 ^ 77 := by
    rw [← hQ3]; exact qstep q2 (by omega) rfl
  have q4 : Q4 = (h0 + 19 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3) / 2 ^ 102 := by
    rw [← hQ4]; exact qstep q3 (by omega) rfl
  have q5 : Q5 = (h0 + 19 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4) / 2 ^ 128 := by
    rw [← hQ5]; exact qstep q4 (by omega) rfl
  have q6 : Q6 = (h0 + 19 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5) / 2 ^ 153 := by
    rw [← hQ6]; exact qstep q5 (by omega) rfl
  have q7 : Q7 = (h0 + 19 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6) / 2 ^ 179 := by
    rw [← hQ7]; exact qstep q6 (by omega) rfl
  have q8 : Q8 = (h0 + 19 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 + 2 ^ 179 * h7) / 2 ^ 204 := by
    rw [← hQ8]; exact qstep q7 (by omega) rfl
  have q9 : Q9 = (h0 + 19 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 + 2 ^ 179 * h7 + 2 ^ 204 * h8) / 2 ^ 230 := by
    rw [← hQ9]; exact qstep q8 (by omega) rfl
  have q10 : Q10 = (h0 + 19 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 + 2 ^ 179 * h7 + 2 ^ 204 * h8 + 2 ^ 230 * h9) / 2 ^ 255 := by
    rw [← hQ10]; exact qstep q9 (by omega) rfl
  clear q1 q2 q3 q4 q5 q6 q7 q8 q9 hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hQ7 hQ8 hQ9 hQ10
  generalize hH : h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 +
    2 ^ 179 * h7 + 2 ^ 204 * h8 + 2 ^ 230 * h9 = H
  have hHlt : H < 2 ^ 255 + 2 ^ 154 := by omega
  have q10' : Q10 = (H + 19) / 2 ^ 255 := by rw [q10]; congr 1; omega
  clear q10
  have c0 : C0 = h0 + 19 * Q10 := by omega
  have c1 : C1 = h1 + C0 / 2 ^ 26 := by omega
  have c2 : C2 = h2 + C1 / 2 ^ 25 := by omega
  have c3 : C3 = h3 + C2 / 2 ^ 26 := by omega
  have c4 : C4 = h4 + C3 / 2 ^ 25 := by omega
  have c5 : C5 = h5 + C4 / 2 ^ 26 := by omega
  have c6 : C6 = h6 + C5 / 2 ^ 25 := by omega
  have c7 : C7 = h7 + C6 / 2 ^ 26 := by omega
  have c8 : C8 = h8 + C7 / 2 ^ 25 := by omega
  have c9 : C9 = h9 + C8 / 2 ^ 26 := by omega
  clear hC0 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9
  have hVlt : C0 % 2 ^ 26 + 2 ^ 26 * (C1 % 2 ^ 25) + 2 ^ 51 * (C2 % 2 ^ 26) + 2 ^ 77 * (C3 % 2 ^ 25) +
      2 ^ 102 * (C4 % 2 ^ 26) + 2 ^ 128 * (C5 % 2 ^ 25) + 2 ^ 153 * (C6 % 2 ^ 26) + 2 ^ 179 * (C7 % 2 ^ 25) +
      2 ^ 204 * (C8 % 2 ^ 26) + 2 ^ 230 * (C9 % 2 ^ 25) < 2 ^ 255 := by omega
  have hv : C0 % 2 ^ 26 + 2 ^ 26 * (C1 % 2 ^ 25) + 2 ^ 51 * (C2 % 2 ^ 26) + 2 ^ 77 * (C3 % 2 ^ 25) +
      2 ^ 102 * (C4 % 2 ^ 26) + 2 ^ 128 * (C5 % 2 ^ 25) + 2 ^ 153 * (C6 % 2 ^ 26) + 2 ^ 179 * (C7 % 2 ^ 25) +
      2 ^ 204 * (C8 % 2 ^ 26) + 2 ^ 230 * (C9 % 2 ^ 25) + 2 ^ 255 * (C9 / 2 ^ 25) = H + 19 * Q10 := by
    omega
  generalize C0 % 2 ^ 26 + 2 ^ 26 * (C1 % 2 ^ 25) + 2 ^ 51 * (C2 % 2 ^ 26) + 2 ^ 77 * (C3 % 2 ^ 25) +
      2 ^ 102 * (C4 % 2 ^ 26) + 2 ^ 128 * (C5 % 2 ^ 25) + 2 ^ 153 * (C6 % 2 ^ 26) + 2 ^ 179 * (C7 % 2 ^ 25) +
      2 ^ 204 * (C8 % 2 ^ 26) + 2 ^ 230 * (C9 % 2 ^ 25) = V at hv hVlt ⊢
  exact carry_fin hHlt hVlt q10' hv

set_option maxHeartbeats 4000000 in
/-- **`to_bytes` encodes the value modulo `p`** of limbs that `reduce`
returns. -/
theorem feToBytes_val {h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : Nat} (b0 : h0 < 2 ^ 26) (b1 : h1 < 2 ^ 26)
    (b2 : h2 < 2 ^ 26) (b3 : h3 < 2 ^ 25) (b4 : h4 < 2 ^ 26) (b5 : h5 < 2 ^ 26) (b6 : h6 < 2 ^ 26)
    (b7 : h7 < 2 ^ 25) (b8 : h8 < 2 ^ 26) (b9 : h9 < 2 ^ 25) :
    leB32 (feToBytesSpec h0 h1 h2 h3 h4 h5 h6 h7 h8 h9) = (h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 +
      2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 + 2 ^ 179 * h7 + 2 ^ 204 * h8 + 2 ^ 230 * h9) % Ed25519.p := by
  obtain ⟨Q1, hQ1⟩ : ∃ q, (h0 + 19) % 2 ^ 32 / 2 ^ 26 = q := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2⟩ : ∃ q, (h1 + Q1) % 2 ^ 32 / 2 ^ 25 = q := ⟨_, rfl⟩
  obtain ⟨Q3, hQ3⟩ : ∃ q, (h2 + Q2) % 2 ^ 32 / 2 ^ 26 = q := ⟨_, rfl⟩
  obtain ⟨Q4, hQ4⟩ : ∃ q, (h3 + Q3) % 2 ^ 32 / 2 ^ 25 = q := ⟨_, rfl⟩
  obtain ⟨Q5, hQ5⟩ : ∃ q, (h4 + Q4) % 2 ^ 32 / 2 ^ 26 = q := ⟨_, rfl⟩
  obtain ⟨Q6, hQ6⟩ : ∃ q, (h5 + Q5) % 2 ^ 32 / 2 ^ 25 = q := ⟨_, rfl⟩
  obtain ⟨Q7, hQ7⟩ : ∃ q, (h6 + Q6) % 2 ^ 32 / 2 ^ 26 = q := ⟨_, rfl⟩
  obtain ⟨Q8, hQ8⟩ : ∃ q, (h7 + Q7) % 2 ^ 32 / 2 ^ 25 = q := ⟨_, rfl⟩
  obtain ⟨Q9, hQ9⟩ : ∃ q, (h8 + Q8) % 2 ^ 32 / 2 ^ 26 = q := ⟨_, rfl⟩
  obtain ⟨Q10, hQ10⟩ : ∃ q, (h9 + Q9) % 2 ^ 32 / 2 ^ 25 = q := ⟨_, rfl⟩
  obtain ⟨C0, hC0⟩ : ∃ c, (h0 + 19 * Q10 % 2 ^ 32) % 2 ^ 32 = c := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ c, (h1 + C0 / 2 ^ 26) % 2 ^ 32 = c := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ c, (h2 + C1 / 2 ^ 25) % 2 ^ 32 = c := ⟨_, rfl⟩
  obtain ⟨C3, hC3⟩ : ∃ c, (h3 + C2 / 2 ^ 26) % 2 ^ 32 = c := ⟨_, rfl⟩
  obtain ⟨C4, hC4⟩ : ∃ c, (h4 + C3 / 2 ^ 25) % 2 ^ 32 = c := ⟨_, rfl⟩
  obtain ⟨C5, hC5⟩ : ∃ c, (h5 + C4 / 2 ^ 26) % 2 ^ 32 = c := ⟨_, rfl⟩
  obtain ⟨C6, hC6⟩ : ∃ c, (h6 + C5 / 2 ^ 25) % 2 ^ 32 = c := ⟨_, rfl⟩
  obtain ⟨C7, hC7⟩ : ∃ c, (h7 + C6 / 2 ^ 26) % 2 ^ 32 = c := ⟨_, rfl⟩
  obtain ⟨C8, hC8⟩ : ∃ c, (h8 + C7 / 2 ^ 25) % 2 ^ 32 = c := ⟨_, rfl⟩
  obtain ⟨C9, hC9⟩ : ∃ c, (h9 + C8 / 2 ^ 26) % 2 ^ 32 = c := ⟨_, rfl⟩
  rw [feToBytesSpec_of hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hQ7 hQ8 hQ9 hQ10 hC0 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9,
    pack_val (C0 % 2 ^ 26) (C1 % 2 ^ 25) (C2 % 2 ^ 26) (C3 % 2 ^ 25) (C4 % 2 ^ 26) (C5 % 2 ^ 25)
      (C6 % 2 ^ 26) (C7 % 2 ^ 25) (C8 % 2 ^ 26) (C9 % 2 ^ 25) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide))]
  exact carry_val b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hQ7 hQ8 hQ9 hQ10 hC0 hC1 hC2 hC3 hC4
    hC5 hC6 hC7 hC8 hC9

/-- `to_bytes` after `reduce` spells the value modulo `p`. -/
theorem feToBytes_reduce (l : List Nat) (h : RedB l) :
    leB32 (feToBytesSpec (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) (l.getD 4 0) (l.getD 5 0)
      (l.getD 6 0) (l.getD 7 0) (l.getD 8 0) (l.getD 9 0)) = fv l :=
  feToBytes_val h.b0 h.b1 h.b2 h.b3 h.b4 h.b5 h.b6 h.b7 h.b8 h.b9

end C3.RV32.EdM
