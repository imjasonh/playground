import C3BootProofs.Models.Ed25519KMont
import C3BootProofs.Proofs.Ed25519VerifyP3
import C3BootProofs.Proofs.Ed25519VerifyB

/-!
# The bytes of `Scalar29::as_bytes`

`as_bytes` of nine limbs below 2^29, the top one below 2^24, spells their
value (`pack9`).
-/

namespace C3.RV32.EdK

open C3.RV32

/-- An `or` of a value below `2^k` and a multiple of `2^k` is their sum. -/
theorem or_add {x y k : Nat} (hx : x < 2 ^ k) (hy : y % 2 ^ k = 0) : (x ||| y) = x + y := by
  have e : y = 2 ^ k * (y / 2 ^ k) := by have := Nat.div_add_mod y (2 ^ k); omega
  rw [Nat.or_comm, e, ← Nat.two_pow_add_eq_or_of_lt hx, Nat.add_comm]

theorem bv_lo (x s : Nat) (hx : x < 2 ^ 32) :
    ((BitVec.ofNat 32 x >>> s).extractLsb' 0 8).toNat = x / 2 ^ s % 2 ^ 8 := by
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hx, Nat.pow_zero, Nat.div_one]

theorem bv_lo0 (x : Nat) (hx : x < 2 ^ 32) : ((BitVec.ofNat 32 x).extractLsb' 0 8).toNat = x % 2 ^ 8 := by
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_zero]

theorem bv_or (x y s k : Nat) (hx : x < 2 ^ (s + k)) (hx32 : x < 2 ^ 32) (hy : y < 2 ^ 32) (hk : k ≤ 32) :
    (((BitVec.ofNat 32 x >>> s) ||| (BitVec.ofNat 32 y <<< k)).extractLsb' 0 8).toNat =
      (x / 2 ^ s + y * 2 ^ k % 2 ^ 32) % 2 ^ 8 := by
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hx32,
    Nat.pow_zero, Nat.div_one]
  rw [or_add (k := k)]
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), ← Nat.pow_add, Nat.add_comm]; exact hx
  · have e : 2 ^ 32 = 2 ^ k * 2 ^ (32 - k) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, Nat.mod_mul_right_mod, Nat.mul_mod_left]

set_option maxHeartbeats 4000000 in
theorem pack9 {l : Nat → Nat} (hl : ∀ i, i < 9 → l i < 2 ^ 29) (h8 : l 8 < 2 ^ 24) :
    leL ((List.range 32).map fun j => (s29PackByte (fun i => BitVec.ofNat 32 (l i)) j).toNat) 0 32 = sv9 l := by
  have b0 := hl 0 (by decide)
  have b1 := hl 1 (by decide)
  have b2 := hl 2 (by decide)
  have b3 := hl 3 (by decide)
  have b4 := hl 4 (by decide)
  have b5 := hl 5 (by decide)
  have b6 := hl 6 (by decide)
  have b7 := hl 7 (by decide)
  have b8 := hl 8 (by decide)
  have e : leL ((List.range 32).map fun j => (s29PackByte (fun i => BitVec.ofNat 32 (l i)) j).toNat) 0 32 =
      0 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 0).toNat * 256 ^ 0 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 1).toNat * 256 ^ 1 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 2).toNat * 256 ^ 2 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 3).toNat * 256 ^ 3 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 4).toNat * 256 ^ 4 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 5).toNat * 256 ^ 5 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 6).toNat * 256 ^ 6 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 7).toNat * 256 ^ 7 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 8).toNat * 256 ^ 8 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 9).toNat * 256 ^ 9 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 10).toNat * 256 ^ 10 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 11).toNat * 256 ^ 11 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 12).toNat * 256 ^ 12 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 13).toNat * 256 ^ 13 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 14).toNat * 256 ^ 14 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 15).toNat * 256 ^ 15 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 16).toNat * 256 ^ 16 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 17).toNat * 256 ^ 17 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 18).toNat * 256 ^ 18 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 19).toNat * 256 ^ 19 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 20).toNat * 256 ^ 20 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 21).toNat * 256 ^ 21 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 22).toNat * 256 ^ 22 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 23).toNat * 256 ^ 23 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 24).toNat * 256 ^ 24 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 25).toNat * 256 ^ 25 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 26).toNat * 256 ^ 26 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 27).toNat * 256 ^ 27 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 28).toNat * 256 ^ 28 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 29).toNat * 256 ^ 29 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 30).toNat * 256 ^ 30 +
        (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 31).toNat * 256 ^ 31 := rfl
  have y0 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 0).toNat = l 0 % 2 ^ 8 := bv_lo0 _ (by omega)
  have y1 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 1).toNat = l 0 / 2 ^ 8 % 2 ^ 8 := bv_lo _ 8 (by omega)
  have y2 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 2).toNat = l 0 / 2 ^ 16 % 2 ^ 8 := bv_lo _ 16 (by omega)
  have y3 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 3).toNat = (l 0 / 2 ^ 24 + l 1 * 2 ^ 5 % 2 ^ 32) % 2 ^ 8 :=
    bv_or _ _ 24 5 (by omega) (by omega) (by omega) (by decide)
  have y4 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 4).toNat = l 1 / 2 ^ 3 % 2 ^ 8 := bv_lo _ 3 (by omega)
  have y5 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 5).toNat = l 1 / 2 ^ 11 % 2 ^ 8 := bv_lo _ 11 (by omega)
  have y6 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 6).toNat = l 1 / 2 ^ 19 % 2 ^ 8 := bv_lo _ 19 (by omega)
  have y7 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 7).toNat = (l 1 / 2 ^ 27 + l 2 * 2 ^ 2 % 2 ^ 32) % 2 ^ 8 :=
    bv_or _ _ 27 2 (by omega) (by omega) (by omega) (by decide)
  have y8 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 8).toNat = l 2 / 2 ^ 6 % 2 ^ 8 := bv_lo _ 6 (by omega)
  have y9 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 9).toNat = l 2 / 2 ^ 14 % 2 ^ 8 := bv_lo _ 14 (by omega)
  have y10 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 10).toNat = (l 2 / 2 ^ 22 + l 3 * 2 ^ 7 % 2 ^ 32) % 2 ^ 8 :=
    bv_or _ _ 22 7 (by omega) (by omega) (by omega) (by decide)
  have y11 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 11).toNat = l 3 / 2 ^ 1 % 2 ^ 8 := bv_lo _ 1 (by omega)
  have y12 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 12).toNat = l 3 / 2 ^ 9 % 2 ^ 8 := bv_lo _ 9 (by omega)
  have y13 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 13).toNat = l 3 / 2 ^ 17 % 2 ^ 8 := bv_lo _ 17 (by omega)
  have y14 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 14).toNat = (l 3 / 2 ^ 25 + l 4 * 2 ^ 4 % 2 ^ 32) % 2 ^ 8 :=
    bv_or _ _ 25 4 (by omega) (by omega) (by omega) (by decide)
  have y15 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 15).toNat = l 4 / 2 ^ 4 % 2 ^ 8 := bv_lo _ 4 (by omega)
  have y16 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 16).toNat = l 4 / 2 ^ 12 % 2 ^ 8 := bv_lo _ 12 (by omega)
  have y17 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 17).toNat = l 4 / 2 ^ 20 % 2 ^ 8 := bv_lo _ 20 (by omega)
  have y18 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 18).toNat = (l 4 / 2 ^ 28 + l 5 * 2 ^ 1 % 2 ^ 32) % 2 ^ 8 :=
    bv_or _ _ 28 1 (by omega) (by omega) (by omega) (by decide)
  have y19 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 19).toNat = l 5 / 2 ^ 7 % 2 ^ 8 := bv_lo _ 7 (by omega)
  have y20 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 20).toNat = l 5 / 2 ^ 15 % 2 ^ 8 := bv_lo _ 15 (by omega)
  have y21 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 21).toNat = (l 5 / 2 ^ 23 + l 6 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8 :=
    bv_or _ _ 23 6 (by omega) (by omega) (by omega) (by decide)
  have y22 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 22).toNat = l 6 / 2 ^ 2 % 2 ^ 8 := bv_lo _ 2 (by omega)
  have y23 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 23).toNat = l 6 / 2 ^ 10 % 2 ^ 8 := bv_lo _ 10 (by omega)
  have y24 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 24).toNat = l 6 / 2 ^ 18 % 2 ^ 8 := bv_lo _ 18 (by omega)
  have y25 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 25).toNat = (l 6 / 2 ^ 26 + l 7 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8 :=
    bv_or _ _ 26 3 (by omega) (by omega) (by omega) (by decide)
  have y26 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 26).toNat = l 7 / 2 ^ 5 % 2 ^ 8 := bv_lo _ 5 (by omega)
  have y27 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 27).toNat = l 7 / 2 ^ 13 % 2 ^ 8 := bv_lo _ 13 (by omega)
  have y28 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 28).toNat = l 7 / 2 ^ 21 % 2 ^ 8 := bv_lo _ 21 (by omega)
  have y29 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 29).toNat = l 8 % 2 ^ 8 := bv_lo0 _ (by omega)
  have y30 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 30).toNat = l 8 / 2 ^ 8 % 2 ^ 8 := bv_lo _ 8 (by omega)
  have y31 : (s29PackByte (fun i => BitVec.ofNat 32 (l i)) 31).toNat = l 8 / 2 ^ 16 % 2 ^ 8 := bv_lo _ 16 (by omega)
  rw [e, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31]
  have j3 : (l 0 / 2 ^ 24 + l 1 * 2 ^ 5 % 2 ^ 32) % 2 ^ 8 = l 0 / 2 ^ 24 + l 1 % 2 ^ 3 * 2 ^ 5 := by omega
  have j7 : (l 1 / 2 ^ 27 + l 2 * 2 ^ 2 % 2 ^ 32) % 2 ^ 8 = l 1 / 2 ^ 27 + l 2 % 2 ^ 6 * 2 ^ 2 := by omega
  have j10 : (l 2 / 2 ^ 22 + l 3 * 2 ^ 7 % 2 ^ 32) % 2 ^ 8 = l 2 / 2 ^ 22 + l 3 % 2 ^ 1 * 2 ^ 7 := by omega
  have j14 : (l 3 / 2 ^ 25 + l 4 * 2 ^ 4 % 2 ^ 32) % 2 ^ 8 = l 3 / 2 ^ 25 + l 4 % 2 ^ 4 * 2 ^ 4 := by omega
  have j18 : (l 4 / 2 ^ 28 + l 5 * 2 ^ 1 % 2 ^ 32) % 2 ^ 8 = l 4 / 2 ^ 28 + l 5 % 2 ^ 7 * 2 ^ 1 := by omega
  have j21 : (l 5 / 2 ^ 23 + l 6 * 2 ^ 6 % 2 ^ 32) % 2 ^ 8 = l 5 / 2 ^ 23 + l 6 % 2 ^ 2 * 2 ^ 6 := by omega
  have j25 : (l 6 / 2 ^ 26 + l 7 * 2 ^ 3 % 2 ^ 32) % 2 ^ 8 = l 6 / 2 ^ 26 + l 7 % 2 ^ 5 * 2 ^ 3 := by omega
  rw [j3, j7, j10, j14, j18, j21, j25]
  have d0 : l 0 = l 0 % 2 ^ 8 + 2 ^ 8 * (l 0 / 2 ^ 8 % 2 ^ 8) + 2 ^ 16 * (l 0 / 2 ^ 16 % 2 ^ 8) + 2 ^ 24 * (l 0 / 2 ^ 24) := by omega
  have d1 : l 1 = l 1 % 2 ^ 3 + 2 ^ 3 * (l 1 / 2 ^ 3 % 2 ^ 8) + 2 ^ 11 * (l 1 / 2 ^ 11 % 2 ^ 8) + 2 ^ 19 * (l 1 / 2 ^ 19 % 2 ^ 8) + 2 ^ 27 * (l 1 / 2 ^ 27) := by omega
  have d2 : l 2 = l 2 % 2 ^ 6 + 2 ^ 6 * (l 2 / 2 ^ 6 % 2 ^ 8) + 2 ^ 14 * (l 2 / 2 ^ 14 % 2 ^ 8) + 2 ^ 22 * (l 2 / 2 ^ 22) := by omega
  have d3 : l 3 = l 3 % 2 ^ 1 + 2 ^ 1 * (l 3 / 2 ^ 1 % 2 ^ 8) + 2 ^ 9 * (l 3 / 2 ^ 9 % 2 ^ 8) + 2 ^ 17 * (l 3 / 2 ^ 17 % 2 ^ 8) + 2 ^ 25 * (l 3 / 2 ^ 25) := by omega
  have d4 : l 4 = l 4 % 2 ^ 4 + 2 ^ 4 * (l 4 / 2 ^ 4 % 2 ^ 8) + 2 ^ 12 * (l 4 / 2 ^ 12 % 2 ^ 8) + 2 ^ 20 * (l 4 / 2 ^ 20 % 2 ^ 8) + 2 ^ 28 * (l 4 / 2 ^ 28) := by omega
  have d5 : l 5 = l 5 % 2 ^ 7 + 2 ^ 7 * (l 5 / 2 ^ 7 % 2 ^ 8) + 2 ^ 15 * (l 5 / 2 ^ 15 % 2 ^ 8) + 2 ^ 23 * (l 5 / 2 ^ 23) := by omega
  have d6 : l 6 = l 6 % 2 ^ 2 + 2 ^ 2 * (l 6 / 2 ^ 2 % 2 ^ 8) + 2 ^ 10 * (l 6 / 2 ^ 10 % 2 ^ 8) + 2 ^ 18 * (l 6 / 2 ^ 18 % 2 ^ 8) + 2 ^ 26 * (l 6 / 2 ^ 26) := by omega
  have d7 : l 7 = l 7 % 2 ^ 5 + 2 ^ 5 * (l 7 / 2 ^ 5 % 2 ^ 8) + 2 ^ 13 * (l 7 / 2 ^ 13 % 2 ^ 8) + 2 ^ 21 * (l 7 / 2 ^ 21 % 2 ^ 8) := by omega
  have d8 : l 8 = l 8 % 2 ^ 8 + 2 ^ 8 * (l 8 / 2 ^ 8 % 2 ^ 8) + 2 ^ 16 * (l 8 / 2 ^ 16 % 2 ^ 8) := by omega
  generalize l 0 % 2 ^ 8 = e0 at d0 ⊢
  generalize l 0 / 2 ^ 8 % 2 ^ 8 = e1 at d0 ⊢
  generalize l 0 / 2 ^ 16 % 2 ^ 8 = e2 at d0 ⊢
  generalize l 0 / 2 ^ 24 = e3 at d0 ⊢
  generalize l 1 % 2 ^ 3 = e4 at d1 ⊢
  generalize l 1 / 2 ^ 3 % 2 ^ 8 = e5 at d1 ⊢
  generalize l 1 / 2 ^ 11 % 2 ^ 8 = e6 at d1 ⊢
  generalize l 1 / 2 ^ 19 % 2 ^ 8 = e7 at d1 ⊢
  generalize l 1 / 2 ^ 27 = e8 at d1 ⊢
  generalize l 2 % 2 ^ 6 = e9 at d2 ⊢
  generalize l 2 / 2 ^ 6 % 2 ^ 8 = e10 at d2 ⊢
  generalize l 2 / 2 ^ 14 % 2 ^ 8 = e11 at d2 ⊢
  generalize l 2 / 2 ^ 22 = e12 at d2 ⊢
  generalize l 3 % 2 ^ 1 = e13 at d3 ⊢
  generalize l 3 / 2 ^ 1 % 2 ^ 8 = e14 at d3 ⊢
  generalize l 3 / 2 ^ 9 % 2 ^ 8 = e15 at d3 ⊢
  generalize l 3 / 2 ^ 17 % 2 ^ 8 = e16 at d3 ⊢
  generalize l 3 / 2 ^ 25 = e17 at d3 ⊢
  generalize l 4 % 2 ^ 4 = e18 at d4 ⊢
  generalize l 4 / 2 ^ 4 % 2 ^ 8 = e19 at d4 ⊢
  generalize l 4 / 2 ^ 12 % 2 ^ 8 = e20 at d4 ⊢
  generalize l 4 / 2 ^ 20 % 2 ^ 8 = e21 at d4 ⊢
  generalize l 4 / 2 ^ 28 = e22 at d4 ⊢
  generalize l 5 % 2 ^ 7 = e23 at d5 ⊢
  generalize l 5 / 2 ^ 7 % 2 ^ 8 = e24 at d5 ⊢
  generalize l 5 / 2 ^ 15 % 2 ^ 8 = e25 at d5 ⊢
  generalize l 5 / 2 ^ 23 = e26 at d5 ⊢
  generalize l 6 % 2 ^ 2 = e27 at d6 ⊢
  generalize l 6 / 2 ^ 2 % 2 ^ 8 = e28 at d6 ⊢
  generalize l 6 / 2 ^ 10 % 2 ^ 8 = e29 at d6 ⊢
  generalize l 6 / 2 ^ 18 % 2 ^ 8 = e30 at d6 ⊢
  generalize l 6 / 2 ^ 26 = e31 at d6 ⊢
  generalize l 7 % 2 ^ 5 = e32 at d7 ⊢
  generalize l 7 / 2 ^ 5 % 2 ^ 8 = e33 at d7 ⊢
  generalize l 7 / 2 ^ 13 % 2 ^ 8 = e34 at d7 ⊢
  generalize l 7 / 2 ^ 21 % 2 ^ 8 = e35 at d7 ⊢
  generalize l 8 % 2 ^ 8 = e36 at d8 ⊢
  generalize l 8 / 2 ^ 8 % 2 ^ 8 = e37 at d8 ⊢
  generalize l 8 / 2 ^ 16 % 2 ^ 8 = e38 at d8 ⊢
  unfold sv9
  omega

end C3.RV32.EdK
