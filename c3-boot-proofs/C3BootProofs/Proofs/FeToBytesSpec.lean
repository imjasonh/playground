import C3BootProofs.Proofs.Fe25519

/-!
# `FieldElement2625::to_bytes`'s arithmetic

`feToBytesSpec` is the Rust source of `to_bytes` after its call to `reduce`,
on naturals: each `u32` `+` modulo 2^32, `>> k` as division by `2^k`,
`<< k` as multiplication by `2^k` modulo 2^32, `& LOW_k_BITS` modulo `2^k`,
and `as u8` modulo 2^8.
-/

namespace C3.RV32

/-- `to_bytes` from the ten limbs that `reduce` returns: the quotient `q` of
the value by `p = 2^255 - 19`, the value plus `19 q` carried through the
limbs with the top carry dropped, and the limbs packed into 32 little-endian
bytes. -/
def feToBytesSpec (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : Nat) : List Nat :=
  let q := (h0 + 19) % 2 ^ 32 / 2 ^ 26
  let q := (h1 + q) % 2 ^ 32 / 2 ^ 25
  let q := (h2 + q) % 2 ^ 32 / 2 ^ 26
  let q := (h3 + q) % 2 ^ 32 / 2 ^ 25
  let q := (h4 + q) % 2 ^ 32 / 2 ^ 26
  let q := (h5 + q) % 2 ^ 32 / 2 ^ 25
  let q := (h6 + q) % 2 ^ 32 / 2 ^ 26
  let q := (h7 + q) % 2 ^ 32 / 2 ^ 25
  let q := (h8 + q) % 2 ^ 32 / 2 ^ 26
  let q := (h9 + q) % 2 ^ 32 / 2 ^ 25
  let h0 := (h0 + 19 * q % 2 ^ 32) % 2 ^ 32
  let h1 := (h1 + h0 / 2 ^ 26) % 2 ^ 32
  let h0 := h0 % 2 ^ 26
  let h2 := (h2 + h1 / 2 ^ 25) % 2 ^ 32
  let h1 := h1 % 2 ^ 25
  let h3 := (h3 + h2 / 2 ^ 26) % 2 ^ 32
  let h2 := h2 % 2 ^ 26
  let h4 := (h4 + h3 / 2 ^ 25) % 2 ^ 32
  let h3 := h3 % 2 ^ 25
  let h5 := (h5 + h4 / 2 ^ 26) % 2 ^ 32
  let h4 := h4 % 2 ^ 26
  let h6 := (h6 + h5 / 2 ^ 25) % 2 ^ 32
  let h5 := h5 % 2 ^ 25
  let h7 := (h7 + h6 / 2 ^ 26) % 2 ^ 32
  let h6 := h6 % 2 ^ 26
  let h8 := (h8 + h7 / 2 ^ 25) % 2 ^ 32
  let h7 := h7 % 2 ^ 25
  let h9 := (h9 + h8 / 2 ^ 26) % 2 ^ 32
  let h8 := h8 % 2 ^ 26
  let h9 := h9 % 2 ^ 25
  [h0 % 2 ^ 8, h0 / 2 ^ 8 % 2 ^ 8, h0 / 2 ^ 16 % 2 ^ 8, (h0 / 2 ^ 24 ||| h1 * 2 ^ 2 % 2 ^ 32) % 2 ^ 8,
   h1 / 2 ^ 6 % 2 ^ 8, h1 / 2 ^ 14 % 2 ^ 8, (h1 / 2 ^ 22 ||| h2 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8,
   h2 / 2 ^ 5 % 2 ^ 8, h2 / 2 ^ 13 % 2 ^ 8, (h2 / 2 ^ 21 ||| h3 * 2 ^ 5 % 2 ^ 32) % 2 ^ 8,
   h3 / 2 ^ 3 % 2 ^ 8, h3 / 2 ^ 11 % 2 ^ 8, (h3 / 2 ^ 19 ||| h4 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8,
   h4 / 2 ^ 2 % 2 ^ 8, h4 / 2 ^ 10 % 2 ^ 8, h4 / 2 ^ 18 % 2 ^ 8,
   h5 % 2 ^ 8, h5 / 2 ^ 8 % 2 ^ 8, h5 / 2 ^ 16 % 2 ^ 8, (h5 / 2 ^ 24 ||| h6 * 2 ^ 1 % 2 ^ 32) % 2 ^ 8,
   h6 / 2 ^ 7 % 2 ^ 8, h6 / 2 ^ 15 % 2 ^ 8, (h6 / 2 ^ 23 ||| h7 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8,
   h7 / 2 ^ 5 % 2 ^ 8, h7 / 2 ^ 13 % 2 ^ 8, (h7 / 2 ^ 21 ||| h8 * 2 ^ 4 % 2 ^ 32) % 2 ^ 8,
   h8 / 2 ^ 4 % 2 ^ 8, h8 / 2 ^ 12 % 2 ^ 8, (h8 / 2 ^ 20 ||| h9 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8,
   h9 / 2 ^ 2 % 2 ^ 8, h9 / 2 ^ 10 % 2 ^ 8, h9 / 2 ^ 18 % 2 ^ 8]

/-- An `or` of a value below `2^k` and a multiple of `2^k` is their sum. -/
theorem nat_or_add {x y k : Nat} (hx : x < 2 ^ k) (hy : y % 2 ^ k = 0) : (x ||| y) = x + y := by
  have e : y = 2 ^ k * (y / 2 ^ k) := by have := Nat.div_add_mod y (2 ^ k); omega
  rw [Nat.or_comm, e, ← Nat.two_pow_add_eq_or_of_lt hx, Nat.add_comm]

/-- The `or`s of `feToBytesSpec`: the high bits of one limb, below `2^k`,
and the next limb shifted left `k` bits. -/
theorem spec_or {h l j k : Nat} (hk : j + k = 26 ∨ j + k = 25) (hh : h < 2 ^ (j + k)) :
    (h / 2 ^ j ||| l * 2 ^ k % 2 ^ 32) = h / 2 ^ j + l * 2 ^ k % 2 ^ 32 := by
  apply nat_or_add (k := k)
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j), ← Nat.pow_add, Nat.add_comm]; exact hh
  · have hk32 : k ≤ 32 := by omega
    have e : 2 ^ 32 = 2 ^ k * 2 ^ (32 - k) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, Nat.mod_mul_right_mod, Nat.mul_mod_left]

set_option simprocs false in
/-- `feToBytesSpec` with its intermediate values named: `Q1` to `Q10` the
quotient's steps and `C0` to `C9` the carried limbs before their masks, and
each `or` a sum. -/
theorem feToBytesSpec_of {h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10
    C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 : Nat}
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
    feToBytesSpec h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =
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
       C9 % 2 ^ 25 / 2 ^ 18 % 2 ^ 8] := by
  simp only [feToBytesSpec, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6, hQ7, hQ8, hQ9, hQ10, hC0, hC1, hC2, hC3, hC4, hC5,
    hC6, hC7, hC8, hC9]
  rw [spec_or (h := C0 % 2 ^ 26) (l := C1 % 2 ^ 25) (j := 24) (k := 2) (by decide) (Nat.mod_lt _ (by decide)),
    spec_or (h := C1 % 2 ^ 25) (l := C2 % 2 ^ 26) (j := 22) (k := 3) (by decide) (Nat.mod_lt _ (by decide)),
    spec_or (h := C2 % 2 ^ 26) (l := C3 % 2 ^ 25) (j := 21) (k := 5) (by decide) (Nat.mod_lt _ (by decide)),
    spec_or (h := C3 % 2 ^ 25) (l := C4 % 2 ^ 26) (j := 19) (k := 6) (by decide) (Nat.mod_lt _ (by decide)),
    spec_or (h := C5 % 2 ^ 25) (l := C6 % 2 ^ 26) (j := 24) (k := 1) (by decide) (Nat.mod_lt _ (by decide)),
    spec_or (h := C6 % 2 ^ 26) (l := C7 % 2 ^ 25) (j := 23) (k := 3) (by decide) (Nat.mod_lt _ (by decide)),
    spec_or (h := C7 % 2 ^ 25) (l := C8 % 2 ^ 26) (j := 21) (k := 4) (by decide) (Nat.mod_lt _ (by decide)),
    spec_or (h := C8 % 2 ^ 26) (l := C9 % 2 ^ 25) (j := 20) (k := 6) (by decide) (Nat.mod_lt _ (by decide))]

end C3.RV32
