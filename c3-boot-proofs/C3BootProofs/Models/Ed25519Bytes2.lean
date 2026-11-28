import C3BootProofs.Proofs.EdCall
import C3BootProofs.Proofs.FeToBytesSpec
import C3BootProofs.Models.Ed25519FeArith

/-!
# `to_bytes` gives the canonical encoding

`feToBytesSpec_val`: on limbs that `reduce` returns (each below 2^26, the
last below 2^25), `to_bytes` returns the 32 little-endian bytes of the value
modulo `p`. The quotient chain computes `q = ⌊(v + 19) / 2^255⌋`, which is 0
or 1 because `v < 2p`, and the carry chain computes `v + 19 q` with the bit
at 2^255 dropped, which is `v - q p`. `bytesL_eq` composes it with
`reduce`: `bytesL l` is the bytes of `fv l`.
-/

namespace C3.RV32.EdM

/-- The 32 little-endian bytes of `n`. -/
def leBytes32 (n : Nat) : List Nat := (List.range 32).map fun i => n / 256 ^ i % 256

theorem leBytes32_eq (n : Nat) :
    leBytes32 n =
      [n / 256 ^ 0 % 256, n / 256 ^ 1 % 256, n / 256 ^ 2 % 256, n / 256 ^ 3 % 256, n / 256 ^ 4 % 256,
        n / 256 ^ 5 % 256, n / 256 ^ 6 % 256, n / 256 ^ 7 % 256, n / 256 ^ 8 % 256, n / 256 ^ 9 % 256,
        n / 256 ^ 10 % 256, n / 256 ^ 11 % 256, n / 256 ^ 12 % 256, n / 256 ^ 13 % 256, n / 256 ^ 14 % 256,
        n / 256 ^ 15 % 256, n / 256 ^ 16 % 256, n / 256 ^ 17 % 256, n / 256 ^ 18 % 256, n / 256 ^ 19 % 256,
        n / 256 ^ 20 % 256, n / 256 ^ 21 % 256, n / 256 ^ 22 % 256, n / 256 ^ 23 % 256, n / 256 ^ 24 % 256,
        n / 256 ^ 25 % 256, n / 256 ^ 26 % 256, n / 256 ^ 27 % 256, n / 256 ^ 28 % 256, n / 256 ^ 29 % 256,
        n / 256 ^ 30 % 256, n / 256 ^ 31 % 256] := rfl

set_option maxHeartbeats 8000000 in
/-- The bytes `to_bytes` packs from the carried limbs. -/
theorem bytes_of_limbs (C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 : Nat) :
    [C0 % 2 ^ 26 % 2 ^ 8,
       C0 % 2 ^ 26 / 2 ^ 8 % 2 ^ 8,
       C0 % 2 ^ 26 / 2 ^ 16 % 2 ^ 8,
       (C0 % 2 ^ 26 / 2 ^ 24 + C1 % 2 ^ 25 * 2 ^ 2 % 2 ^ 32) % 2 ^ 8,
       C1 % 2 ^ 25 / 2 ^ 6 % 2 ^ 8,
       C1 % 2 ^ 25 / 2 ^ 14 % 2 ^ 8,
       (C1 % 2 ^ 25 / 2 ^ 22 + C2 % 2 ^ 26 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8,
       C2 % 2 ^ 26 / 2 ^ 5 % 2 ^ 8,
       C2 % 2 ^ 26 / 2 ^ 13 % 2 ^ 8,
       (C2 % 2 ^ 26 / 2 ^ 21 + C3 % 2 ^ 25 * 2 ^ 5 % 2 ^ 32) % 2 ^ 8,
       C3 % 2 ^ 25 / 2 ^ 3 % 2 ^ 8,
       C3 % 2 ^ 25 / 2 ^ 11 % 2 ^ 8,
       (C3 % 2 ^ 25 / 2 ^ 19 + C4 % 2 ^ 26 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8,
       C4 % 2 ^ 26 / 2 ^ 2 % 2 ^ 8,
       C4 % 2 ^ 26 / 2 ^ 10 % 2 ^ 8,
       C4 % 2 ^ 26 / 2 ^ 18 % 2 ^ 8,
       C5 % 2 ^ 25 % 2 ^ 8,
       C5 % 2 ^ 25 / 2 ^ 8 % 2 ^ 8,
       C5 % 2 ^ 25 / 2 ^ 16 % 2 ^ 8,
       (C5 % 2 ^ 25 / 2 ^ 24 + C6 % 2 ^ 26 * 2 ^ 1 % 2 ^ 32) % 2 ^ 8,
       C6 % 2 ^ 26 / 2 ^ 7 % 2 ^ 8,
       C6 % 2 ^ 26 / 2 ^ 15 % 2 ^ 8,
       (C6 % 2 ^ 26 / 2 ^ 23 + C7 % 2 ^ 25 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8,
       C7 % 2 ^ 25 / 2 ^ 5 % 2 ^ 8,
       C7 % 2 ^ 25 / 2 ^ 13 % 2 ^ 8,
       (C7 % 2 ^ 25 / 2 ^ 21 + C8 % 2 ^ 26 * 2 ^ 4 % 2 ^ 32) % 2 ^ 8,
       C8 % 2 ^ 26 / 2 ^ 4 % 2 ^ 8,
       C8 % 2 ^ 26 / 2 ^ 12 % 2 ^ 8,
       (C8 % 2 ^ 26 / 2 ^ 20 + C9 % 2 ^ 25 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8,
       C9 % 2 ^ 25 / 2 ^ 2 % 2 ^ 8,
       C9 % 2 ^ 25 / 2 ^ 10 % 2 ^ 8,
       C9 % 2 ^ 25 / 2 ^ 18 % 2 ^ 8] =
      leBytes32 (C0 % 2 ^ 26 + 2 ^ 26 * (C1 % 2 ^ 25) + 2 ^ 51 * (C2 % 2 ^ 26) + 2 ^ 77 * (C3 % 2 ^ 25) +
        2 ^ 102 * (C4 % 2 ^ 26) + 2 ^ 128 * (C5 % 2 ^ 25) + 2 ^ 153 * (C6 % 2 ^ 26) + 2 ^ 179 * (C7 % 2 ^ 25) +
        2 ^ 204 * (C8 % 2 ^ 26) + 2 ^ 230 * (C9 % 2 ^ 25)) := by
  rw [leBytes32_eq]
  simp only [List.cons.injEq, and_true]
  and_intros
  all_goals omega

private theorem tb_div_step {A h a w b : Nat} (hab : a + w = b) : (h + A / 2 ^ a) / 2 ^ w = (A + 2 ^ a * h) / 2 ^ b := by
  subst hab
  have e : (A + 2 ^ a * h) / 2 ^ a = h + A / 2 ^ a := by rw [Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos a)]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, e]

private theorem qE {h q Q : Nat} (hh : h < 2 ^ 26) (hq : q ≤ 19) (e : (h + q) % 2 ^ 32 / 2 ^ 26 = Q) :
    (h + q) / 2 ^ 26 = Q := by
  rw [← e, Nat.mod_eq_of_lt (by omega)]

private theorem qE_le {h q Q : Nat} (hh : h < 2 ^ 26) (hq : q ≤ 19) (e : (h + q) / 2 ^ 26 = Q) : Q ≤ 1 := by omega

private theorem qO {h q Q : Nat} (hh : h < 2 ^ 26) (hq : q ≤ 1) (e : (h + q) % 2 ^ 32 / 2 ^ 25 = Q) :
    (h + q) / 2 ^ 25 = Q := by
  rw [← e, Nat.mod_eq_of_lt (by omega)]

private theorem qO_le {h q Q : Nat} (hh : h < 2 ^ 26) (hq : q ≤ 1) (e : (h + q) / 2 ^ 25 = Q) : Q ≤ 2 := by omega

private theorem q9_le {h q Q : Nat} (hh : h < 2 ^ 25) (hq : q ≤ 1) (e : (h + q) / 2 ^ 25 = Q) : Q ≤ 1 := by omega

private theorem cE {h c C : Nat} (hh : h < 2 ^ 26) (hc : c ≤ 19) (e : (h + c) % 2 ^ 32 = C) : h + c = C := by
  rw [← e, Nat.mod_eq_of_lt (by omega)]

private theorem cE_le {h c C : Nat} (hh : h < 2 ^ 26) (hc : c ≤ 19) (e : h + c = C) : C / 2 ^ 26 ≤ 1 := by omega

private theorem cO_le {h c C : Nat} (hh : h < 2 ^ 26) (hc : c ≤ 1) (e : h + c = C) : C / 2 ^ 25 ≤ 2 := by omega

private theorem c0_eq {h Q C : Nat} (hh : h < 2 ^ 26) (hQ : Q ≤ 1) (e : (h + 19 * Q % 2 ^ 32) % 2 ^ 32 = C) :
    h + 19 * Q = C := by
  rw [← e, Nat.mod_eq_of_lt (by omega : 19 * Q < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]

private theorem chain_tele {h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 Q C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 : Nat}
    (f0 : h0 + 19 * Q = C0) (f1 : h1 + C0 / 2 ^ 26 = C1) (f2 : h2 + C1 / 2 ^ 25 = C2)
    (f3 : h3 + C2 / 2 ^ 26 = C3) (f4 : h4 + C3 / 2 ^ 25 = C4) (f5 : h5 + C4 / 2 ^ 26 = C5)
    (f6 : h6 + C5 / 2 ^ 25 = C6) (f7 : h7 + C6 / 2 ^ 26 = C7) (f8 : h8 + C7 / 2 ^ 25 = C8)
    (f9 : h9 + C8 / 2 ^ 26 = C9) :
    C0 % 2 ^ 26 + 2 ^ 26 * (C1 % 2 ^ 25) + 2 ^ 51 * (C2 % 2 ^ 26) + 2 ^ 77 * (C3 % 2 ^ 25) +
        2 ^ 102 * (C4 % 2 ^ 26) + 2 ^ 128 * (C5 % 2 ^ 25) + 2 ^ 153 * (C6 % 2 ^ 26) + 2 ^ 179 * (C7 % 2 ^ 25) +
        2 ^ 204 * (C8 % 2 ^ 26) + 2 ^ 230 * (C9 % 2 ^ 25) + 2 ^ 255 * (C9 / 2 ^ 25) =
      h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 + 2 ^ 179 * h7 +
        2 ^ 204 * h8 + 2 ^ 230 * h9 + 19 * Q := by
  have g0 := Nat.div_add_mod C0 (2 ^ 26)
  have g1 := Nat.div_add_mod C1 (2 ^ 25)
  have g2 := Nat.div_add_mod C2 (2 ^ 26)
  have g3 := Nat.div_add_mod C3 (2 ^ 25)
  have g4 := Nat.div_add_mod C4 (2 ^ 26)
  have g5 := Nat.div_add_mod C5 (2 ^ 25)
  have g6 := Nat.div_add_mod C6 (2 ^ 26)
  have g7 := Nat.div_add_mod C7 (2 ^ 25)
  have g8 := Nat.div_add_mod C8 (2 ^ 26)
  have g9 := Nat.div_add_mod C9 (2 ^ 25)
  generalize C0 / 2 ^ 26 = d0 at *
  generalize C1 / 2 ^ 25 = d1 at *
  generalize C2 / 2 ^ 26 = d2 at *
  generalize C3 / 2 ^ 25 = d3 at *
  generalize C4 / 2 ^ 26 = d4 at *
  generalize C5 / 2 ^ 25 = d5 at *
  generalize C6 / 2 ^ 26 = d6 at *
  generalize C7 / 2 ^ 25 = d7 at *
  generalize C8 / 2 ^ 26 = d8 at *
  generalize C9 / 2 ^ 25 = d9 at *
  generalize C0 % 2 ^ 26 = c0 at *
  generalize C1 % 2 ^ 25 = c1 at *
  generalize C2 % 2 ^ 26 = c2 at *
  generalize C3 % 2 ^ 25 = c3 at *
  generalize C4 % 2 ^ 26 = c4 at *
  generalize C5 % 2 ^ 25 = c5 at *
  generalize C6 % 2 ^ 26 = c6 at *
  generalize C7 % 2 ^ 25 = c7 at *
  generalize C8 % 2 ^ 26 = c8 at *
  generalize C9 % 2 ^ 25 = c9 at *
  omega

private theorem n_lt (C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 : Nat) :
    C0 % 2 ^ 26 + 2 ^ 26 * (C1 % 2 ^ 25) + 2 ^ 51 * (C2 % 2 ^ 26) + 2 ^ 77 * (C3 % 2 ^ 25) +
        2 ^ 102 * (C4 % 2 ^ 26) + 2 ^ 128 * (C5 % 2 ^ 25) + 2 ^ 153 * (C6 % 2 ^ 26) + 2 ^ 179 * (C7 % 2 ^ 25) +
        2 ^ 204 * (C8 % 2 ^ 26) + 2 ^ 230 * (C9 % 2 ^ 25) < 2 ^ 255 := by
  omega

private theorem v_lt {h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : Nat}
    (b0 : h0 < 2 ^ 26) (b1 : h1 < 2 ^ 26) (b2 : h2 < 2 ^ 26) (b3 : h3 < 2 ^ 26) (b4 : h4 < 2 ^ 26)
    (b5 : h5 < 2 ^ 26) (b6 : h6 < 2 ^ 26) (b7 : h7 < 2 ^ 26) (b8 : h8 < 2 ^ 26) (b9 : h9 < 2 ^ 25) :
    h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 + 2 ^ 179 * h7 +
        2 ^ 204 * h8 + 2 ^ 230 * h9 < 2 ^ 255 + 2 ^ 231 := by
  omega

private theorem chain_final {h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 N Q d : Nat}
    (hQ : (h0 + 19 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 +
      2 ^ 179 * h7 + 2 ^ 204 * h8 + 2 ^ 230 * h9) / 2 ^ 255 = Q) (hN : N < 2 ^ 255)
    (hV : h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 + 2 ^ 179 * h7 +
        2 ^ 204 * h8 + 2 ^ 230 * h9 < 2 ^ 255 + 2 ^ 231)
    (hs : N + 2 ^ 255 * d = h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 +
      2 ^ 153 * h6 + 2 ^ 179 * h7 + 2 ^ 204 * h8 + 2 ^ 230 * h9 + 19 * Q) (hq : Q ≤ 1) :
    N = (h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 + 2 ^ 179 * h7 +
        2 ^ 204 * h8 + 2 ^ 230 * h9) % (2 ^ 255 - 19) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl
  · omega
  · omega

/-- The carried limbs hold the value modulo `p`. -/
theorem chain_val {h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10
    C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 : Nat}
    (b0 : h0 < 2 ^ 26) (b1 : h1 < 2 ^ 26) (b2 : h2 < 2 ^ 26) (b3 : h3 < 2 ^ 26) (b4 : h4 < 2 ^ 26)
    (b5 : h5 < 2 ^ 26) (b6 : h6 < 2 ^ 26) (b7 : h7 < 2 ^ 26) (b8 : h8 < 2 ^ 26) (b9 : h9 < 2 ^ 25)
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
      (h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 + 2 ^ 179 * h7 +
        2 ^ 204 * h8 + 2 ^ 230 * h9) % (2 ^ 255 - 19) := by
  have e1 := qE b0 (Nat.le_refl _) hQ1
  have q1 := qE_le b0 (Nat.le_refl _) e1
  have e2 := qO b1 q1 hQ2
  have q2 := qO_le b1 q1 e2
  have e3 := qE b2 (Nat.le_trans q2 (by decide)) hQ3
  have q3 := qE_le b2 (Nat.le_trans q2 (by decide)) e3
  have e4 := qO b3 q3 hQ4
  have q4 := qO_le b3 q3 e4
  have e5 := qE b4 (Nat.le_trans q4 (by decide)) hQ5
  have q5 := qE_le b4 (Nat.le_trans q4 (by decide)) e5
  have e6 := qO b5 q5 hQ6
  have q6 := qO_le b5 q5 e6
  have e7 := qE b6 (Nat.le_trans q6 (by decide)) hQ7
  have q7 := qE_le b6 (Nat.le_trans q6 (by decide)) e7
  have e8 := qO b7 q7 hQ8
  have q8 := qO_le b7 q7 e8
  have e9 := qE b8 (Nat.le_trans q8 (by decide)) hQ9
  have q9 := qE_le b8 (Nat.le_trans q8 (by decide)) e9
  have e10 := qO (Nat.lt_trans b9 (by decide)) q9 hQ10
  have q10 := q9_le b9 q9 e10
  have f0 := c0_eq b0 q10 hC0
  have k0 := cE_le b0 (Nat.mul_le_mul_left 19 q10 : 19 * Q10 ≤ 19) f0
  have f1 := cE b1 (Nat.le_trans k0 (by decide)) hC1
  have k1 := cO_le b1 k0 f1
  have f2 := cE b2 (Nat.le_trans k1 (by decide)) hC2
  have k2 := cE_le b2 (Nat.le_trans k1 (by decide)) f2
  have f3 := cE b3 (Nat.le_trans k2 (by decide)) hC3
  have k3 := cO_le b3 k2 f3
  have f4 := cE b4 (Nat.le_trans k3 (by decide)) hC4
  have k4 := cE_le b4 (Nat.le_trans k3 (by decide)) f4
  have f5 := cE b5 (Nat.le_trans k4 (by decide)) hC5
  have k5 := cO_le b5 k4 f5
  have f6 := cE b6 (Nat.le_trans k5 (by decide)) hC6
  have k6 := cE_le b6 (Nat.le_trans k5 (by decide)) f6
  have f7 := cE b7 (Nat.le_trans k6 (by decide)) hC7
  have k7 := cO_le b7 k6 f7
  have f8 := cE b8 (Nat.le_trans k7 (by decide)) hC8
  have k8 := cE_le b8 (Nat.le_trans k7 (by decide)) f8
  have f9 := cE (Nat.lt_trans b9 (by decide)) (Nat.le_trans k8 (by decide)) hC9
  rw [← e1, tb_div_step (b := 51) rfl] at e2
  rw [← e2, tb_div_step (b := 77) rfl] at e3
  rw [← e3, tb_div_step (b := 102) rfl] at e4
  rw [← e4, tb_div_step (b := 128) rfl] at e5
  rw [← e5, tb_div_step (b := 153) rfl] at e6
  rw [← e6, tb_div_step (b := 179) rfl] at e7
  rw [← e7, tb_div_step (b := 204) rfl] at e8
  rw [← e8, tb_div_step (b := 230) rfl] at e9
  rw [← e9, tb_div_step (b := 255) rfl] at e10
  exact chain_final e10 (n_lt _ _ _ _ _ _ _ _ _ _) (v_lt b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)
    (chain_tele f0 f1 f2 f3 f4 f5 f6 f7 f8 f9) q10

/-- **`to_bytes` of reduced limbs**: the little-endian bytes of the value
modulo `p`. -/
theorem feToBytesSpec_val {h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : Nat}
    (b0 : h0 < 2 ^ 26) (b1 : h1 < 2 ^ 26) (b2 : h2 < 2 ^ 26) (b3 : h3 < 2 ^ 26) (b4 : h4 < 2 ^ 26)
    (b5 : h5 < 2 ^ 26) (b6 : h6 < 2 ^ 26) (b7 : h7 < 2 ^ 26) (b8 : h8 < 2 ^ 26) (b9 : h9 < 2 ^ 25) :
    feToBytesSpec h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =
      leBytes32 ((h0 + 2 ^ 26 * h1 + 2 ^ 51 * h2 + 2 ^ 77 * h3 + 2 ^ 102 * h4 + 2 ^ 128 * h5 + 2 ^ 153 * h6 +
        2 ^ 179 * h7 + 2 ^ 204 * h8 + 2 ^ 230 * h9) % Ed25519.p) := by
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
    bytes_of_limbs]
  exact congrArg leBytes32 (chain_val b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hQ7 hQ8 hQ9 hQ10
    hC0 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9)

theorem feReduce_lim9 (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : Nat) :
    (feReduceSpec z0 z1 z2 z3 z4 z5 z6 z7 z8 z9).getD 9 0 < 2 ^ 25 :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))

/-- **The canonical bytes of a field element**: `bytesL l` is the 32
little-endian bytes of `fv l`. -/
theorem bytesL_eq {l : List Nat} (hl : Lim (2 ^ 26) l) : bytesL l = leBytes32 (fv l) := by
  have b : ∀ i, i < 10 → l.getD i 0 < 3 * 2 ^ 62 := fun i hi => Nat.lt_trans (hl.2 i hi) (by decide)
  obtain ⟨hr, hv⟩ := feReduce_ok _ _ _ _ _ _ _ _ _ _ (b 0 (by decide)) (b 1 (by decide)) (b 2 (by decide))
    (b 3 (by decide)) (b 4 (by decide)) (b 5 (by decide)) (b 6 (by decide)) (b 7 (by decide)) (b 8 (by decide))
    (b 9 (by decide))
  unfold bytesL feToBytesOf
  rw [feToBytesSpec_val (hr.2 0 (by decide)) (hr.2 1 (by decide)) (hr.2 2 (by decide)) (hr.2 3 (by decide))
    (hr.2 4 (by decide)) (hr.2 5 (by decide)) (hr.2 6 (by decide)) (hr.2 7 (by decide)) (hr.2 8 (by decide))
    (feReduce_lim9 _ _ _ _ _ _ _ _ _ _)]
  exact congrArg leBytes32 hv

private theorem xor_128 {u b : Nat} (hu : u < 128) (hb : b < 2) : u ^^^ 128 * b = u + 128 * b := by
  rcases b with _ | _ | b
  · rw [Nat.mul_zero, Nat.xor_zero, Nat.add_zero]
  · have h : ∀ u, u < 128 → u ^^^ 128 = u + 128 := by decide
    exact h u hu
  · omega

/-- Bit 255 of the encoding, set the way `compress` sets it: the sign of `x` in
byte 31 of the bytes of `y`. -/
theorem leBytes32_sign (y x : Nat) (hy : y < 2 ^ 255) :
    (leBytes32 y).set 31 ((leBytes32 y).getD 31 0 ^^^ 128 * ((leBytes32 x).getD 0 0 % 2)) =
      leBytes32 (y + 2 ^ 255 * (x % 2)) := by
  have hb : (leBytes32 x).getD 0 0 % 2 = x % 2 := by
    rw [leBytes32_eq]; show x / 256 ^ 0 % 256 % 2 = x % 2; omega
  have h31 : (leBytes32 y).getD 31 0 = y / 256 ^ 31 % 256 := by rw [leBytes32_eq]; rfl
  rw [hb, h31, xor_128 (by omega) (Nat.mod_lt x (by decide)), leBytes32_eq, leBytes32_eq]
  simp only [List.set_cons_succ, List.set_cons_zero, List.cons.injEq, and_true]
  and_intros
  all_goals omega

end C3.RV32.EdM
