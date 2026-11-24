import C3BootProofs.Models.Ed25519KMont
import C3BootProofs.Models.Ed25519Model

/-!
# SHA-512 digests, as `from_bytes_wide` splits them

A digest is 64 bytes (`sha512_length`, `sha512_byt`). Its value is the sum of
its sixteen little-endian words (`leNum64`), and `lo9` and `hi9` split those
words into eighteen 29-bit limbs with the same value (`split16`).
-/

namespace C3.RV32.EdK

open C3.RV32 C3.RV32.EdM

theorem round_length (w : Array Sha512.W64) (v : List Sha512.W64) (t : Nat) :
    (Sha512.round w v t).length = v.length := by
  unfold Sha512.round
  split <;> rfl

theorem foldl_round_length (w : Array Sha512.W64) :
    ∀ (l : List Nat) (v : List Sha512.W64), (l.foldl (Sha512.round w) v).length = v.length
  | [], _ => rfl
  | t :: l, v => by rw [List.foldl_cons, foldl_round_length w l, round_length]

theorem compress_length (hv : List Sha512.W64) (b : Bytes) : (Sha512.compress hv b).length = hv.length := by
  unfold Sha512.compress
  rw [List.length_zipWith, foldl_round_length, Nat.min_self]

theorem foldl_compress_length :
    ∀ (l : List Bytes) (hv : List Sha512.W64), (l.foldl Sha512.compress hv).length = hv.length
  | [], _ => rfl
  | b :: l, hv => by rw [List.foldl_cons, foldl_compress_length l, compress_length]

theorem wordBytes_length (x : Sha512.W64) : (Sha512.wordBytes x).length = 8 := by
  unfold Sha512.wordBytes
  rw [List.length_map, List.length_reverse, List.length_range]

theorem flatMap_wordBytes_length : ∀ l : List Sha512.W64, (l.flatMap Sha512.wordBytes).length = 8 * l.length
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, wordBytes_length, flatMap_wordBytes_length l, List.length_cons]
    omega

theorem sha512_length (m : Bytes) : (sha512 m).length = 64 := by
  unfold sha512
  rw [flatMap_wordBytes_length, foldl_compress_length]
  rfl

theorem byt_of_lt {l : List Nat} (h : ∀ x ∈ l, x < 256) : Byt l := fun i => by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => decide
  | some v => exact h v (List.mem_of_getElem? hi)

theorem sha512_byt (m : Bytes) : Byt (sha512 m) := byt_of_lt fun x hx => by
  unfold sha512 at hx
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.1 hx
  unfold Sha512.wordBytes at ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
  exact Nat.mod_lt _ (by decide)

theorem leL4_lt {d : List Nat} (hd : Byt d) (b : Nat) : leL d b 4 < 2 ^ 32 := by
  have h0 := hd (b + 0)
  have h1 := hd (b + 1)
  have h2 := hd (b + 2)
  have h3 := hd (b + 3)
  simp only [leL]
  omega

theorem lv_add4 (d : List Nat) (k : Nat) : lv (k + 4) d = lv k d + 256 ^ k * leL d k 4 := by
  simp only [lv, leL, Nat.add_zero, Nat.pow_succ, Nat.pow_zero]
  generalize 256 ^ k = P
  ring_eq

theorem leNum64 {d : List Nat} (hl : d.length = 64) :
    Ed25519.leNum d = leL d 0 4 + 256 ^ 4 * leL d 4 4 + 256 ^ 8 * leL d 8 4 + 256 ^ 12 * leL d 12 4 + 256 ^ 16 * leL d 16 4 + 256 ^ 20 * leL d 20 4 + 256 ^ 24 * leL d 24 4 + 256 ^ 28 * leL d 28 4 + 256 ^ 32 * leL d 32 4 + 256 ^ 36 * leL d 36 4 + 256 ^ 40 * leL d 40 4 + 256 ^ 44 * leL d 44 4 + 256 ^ 48 * leL d 48 4 + 256 ^ 52 * leL d 52 4 + 256 ^ 56 * leL d 56 4 + 256 ^ 60 * leL d 60 4 := by
  rw [leNum_lv, hl]
  rw [show lv 64 d = lv 60 d + 256 ^ 60 * leL d 60 4 from lv_add4 d 60]
  rw [show lv 60 d = lv 56 d + 256 ^ 56 * leL d 56 4 from lv_add4 d 56]
  rw [show lv 56 d = lv 52 d + 256 ^ 52 * leL d 52 4 from lv_add4 d 52]
  rw [show lv 52 d = lv 48 d + 256 ^ 48 * leL d 48 4 from lv_add4 d 48]
  rw [show lv 48 d = lv 44 d + 256 ^ 44 * leL d 44 4 from lv_add4 d 44]
  rw [show lv 44 d = lv 40 d + 256 ^ 40 * leL d 40 4 from lv_add4 d 40]
  rw [show lv 40 d = lv 36 d + 256 ^ 36 * leL d 36 4 from lv_add4 d 36]
  rw [show lv 36 d = lv 32 d + 256 ^ 32 * leL d 32 4 from lv_add4 d 32]
  rw [show lv 32 d = lv 28 d + 256 ^ 28 * leL d 28 4 from lv_add4 d 28]
  rw [show lv 28 d = lv 24 d + 256 ^ 24 * leL d 24 4 from lv_add4 d 24]
  rw [show lv 24 d = lv 20 d + 256 ^ 20 * leL d 20 4 from lv_add4 d 20]
  rw [show lv 20 d = lv 16 d + 256 ^ 16 * leL d 16 4 from lv_add4 d 16]
  rw [show lv 16 d = lv 12 d + 256 ^ 12 * leL d 12 4 from lv_add4 d 12]
  rw [show lv 12 d = lv 8 d + 256 ^ 8 * leL d 8 4 from lv_add4 d 8]
  rw [show lv 8 d = lv 4 d + 256 ^ 4 * leL d 4 4 from lv_add4 d 4]
  rw [show lv 4 d = lv 0 d + 256 ^ 0 * leL d 0 4 from lv_add4 d 0]
  rw [show lv 0 d = 0 from rfl, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

theorem split_lt {w : Nat → Nat} (hw : w 15 < 2 ^ 32) :
    (∀ i, i < 9 → lo9 w i < 2 ^ 29) ∧ (∀ i, i < 9 → hi9 w i < 2 ^ 29) := by
  have l0 : lo9 w 0 = w 0 % 2 ^ 29 := by simp only [lo9, ↓reduceIte]
  have l1 : lo9 w 1 = (w 0 / 2 ^ 29 + w 1 * 2 ^ 3) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l2 : lo9 w 2 = (w 1 / 2 ^ 26 + w 2 * 2 ^ 6) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l3 : lo9 w 3 = (w 2 / 2 ^ 23 + w 3 * 2 ^ 9) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l4 : lo9 w 4 = (w 3 / 2 ^ 20 + w 4 * 2 ^ 12) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l5 : lo9 w 5 = (w 4 / 2 ^ 17 + w 5 * 2 ^ 15) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l6 : lo9 w 6 = (w 5 / 2 ^ 14 + w 6 * 2 ^ 18) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l7 : lo9 w 7 = (w 6 / 2 ^ 11 + w 7 * 2 ^ 21) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l8 : lo9 w 8 = (w 7 / 2 ^ 8 + w 8 * 2 ^ 24) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have h0 : hi9 w 0 = (w 8 / 2 ^ 5 + w 9 * 2 ^ 27) % 2 ^ 29 := by simp only [hi9, ↓reduceIte]
  have h1 : hi9 w 1 = w 9 / 2 ^ 2 % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h2 : hi9 w 2 = (w 9 / 2 ^ 31 + w 10 * 2 ^ 1) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h3 : hi9 w 3 = (w 10 / 2 ^ 28 + w 11 * 2 ^ 4) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h4 : hi9 w 4 = (w 11 / 2 ^ 25 + w 12 * 2 ^ 7) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h5 : hi9 w 5 = (w 12 / 2 ^ 22 + w 13 * 2 ^ 10) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h6 : hi9 w 6 = (w 13 / 2 ^ 19 + w 14 * 2 ^ 13) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h7 : hi9 w 7 = (w 14 / 2 ^ 16 + w 15 * 2 ^ 16) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h8 : hi9 w 8 = w 15 / 2 ^ 13 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  refine ⟨nat9 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, nat9 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · show lo9 w 0 < 2 ^ 29; rw [l0]; exact Nat.mod_lt _ (by decide)
  · show lo9 w 1 < 2 ^ 29; rw [l1]; exact Nat.mod_lt _ (by decide)
  · show lo9 w 2 < 2 ^ 29; rw [l2]; exact Nat.mod_lt _ (by decide)
  · show lo9 w 3 < 2 ^ 29; rw [l3]; exact Nat.mod_lt _ (by decide)
  · show lo9 w 4 < 2 ^ 29; rw [l4]; exact Nat.mod_lt _ (by decide)
  · show lo9 w 5 < 2 ^ 29; rw [l5]; exact Nat.mod_lt _ (by decide)
  · show lo9 w 6 < 2 ^ 29; rw [l6]; exact Nat.mod_lt _ (by decide)
  · show lo9 w 7 < 2 ^ 29; rw [l7]; exact Nat.mod_lt _ (by decide)
  · show lo9 w 8 < 2 ^ 29; rw [l8]; exact Nat.mod_lt _ (by decide)
  · show hi9 w 0 < 2 ^ 29; rw [h0]; exact Nat.mod_lt _ (by decide)
  · show hi9 w 1 < 2 ^ 29; rw [h1]; exact Nat.mod_lt _ (by decide)
  · show hi9 w 2 < 2 ^ 29; rw [h2]; exact Nat.mod_lt _ (by decide)
  · show hi9 w 3 < 2 ^ 29; rw [h3]; exact Nat.mod_lt _ (by decide)
  · show hi9 w 4 < 2 ^ 29; rw [h4]; exact Nat.mod_lt _ (by decide)
  · show hi9 w 5 < 2 ^ 29; rw [h5]; exact Nat.mod_lt _ (by decide)
  · show hi9 w 6 < 2 ^ 29; rw [h6]; exact Nat.mod_lt _ (by decide)
  · show hi9 w 7 < 2 ^ 29; rw [h7]; exact Nat.mod_lt _ (by decide)
  · show hi9 w 8 < 2 ^ 29; rw [h8]; omega

set_option exponentiation.threshold 600 in
set_option maxHeartbeats 4000000 in
theorem split_val {w : Nat → Nat} (hw : ∀ t, t < 16 → w t < 2 ^ 32) :
    sv9 (lo9 w) + 2 ^ 261 * sv9 (hi9 w) = w 0 + 256 ^ 4 * w 1 + 256 ^ 8 * w 2 + 256 ^ 12 * w 3 + 256 ^ 16 * w 4 + 256 ^ 20 * w 5 + 256 ^ 24 * w 6 + 256 ^ 28 * w 7 + 256 ^ 32 * w 8 + 256 ^ 36 * w 9 + 256 ^ 40 * w 10 + 256 ^ 44 * w 11 + 256 ^ 48 * w 12 + 256 ^ 52 * w 13 + 256 ^ 56 * w 14 + 256 ^ 60 * w 15 := by
  have w0 := hw 0 (by decide)
  have w1 := hw 1 (by decide)
  have w2 := hw 2 (by decide)
  have w3 := hw 3 (by decide)
  have w4 := hw 4 (by decide)
  have w5 := hw 5 (by decide)
  have w6 := hw 6 (by decide)
  have w7 := hw 7 (by decide)
  have w8 := hw 8 (by decide)
  have w9 := hw 9 (by decide)
  have w10 := hw 10 (by decide)
  have w11 := hw 11 (by decide)
  have w12 := hw 12 (by decide)
  have w13 := hw 13 (by decide)
  have w14 := hw 14 (by decide)
  have w15 := hw 15 (by decide)
  have l0 : lo9 w 0 = w 0 % 2 ^ 29 := by simp only [lo9, ↓reduceIte]
  have l1 : lo9 w 1 = (w 0 / 2 ^ 29 + w 1 * 2 ^ 3) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l2 : lo9 w 2 = (w 1 / 2 ^ 26 + w 2 * 2 ^ 6) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l3 : lo9 w 3 = (w 2 / 2 ^ 23 + w 3 * 2 ^ 9) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l4 : lo9 w 4 = (w 3 / 2 ^ 20 + w 4 * 2 ^ 12) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l5 : lo9 w 5 = (w 4 / 2 ^ 17 + w 5 * 2 ^ 15) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l6 : lo9 w 6 = (w 5 / 2 ^ 14 + w 6 * 2 ^ 18) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l7 : lo9 w 7 = (w 6 / 2 ^ 11 + w 7 * 2 ^ 21) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have l8 : lo9 w 8 = (w 7 / 2 ^ 8 + w 8 * 2 ^ 24) % 2 ^ 29 := by simp only [lo9, Nat.reduceEqDiff, ↓reduceIte]
  have h0 : hi9 w 0 = (w 8 / 2 ^ 5 + w 9 * 2 ^ 27) % 2 ^ 29 := by simp only [hi9, ↓reduceIte]
  have h1 : hi9 w 1 = w 9 / 2 ^ 2 % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h2 : hi9 w 2 = (w 9 / 2 ^ 31 + w 10 * 2 ^ 1) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h3 : hi9 w 3 = (w 10 / 2 ^ 28 + w 11 * 2 ^ 4) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h4 : hi9 w 4 = (w 11 / 2 ^ 25 + w 12 * 2 ^ 7) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h5 : hi9 w 5 = (w 12 / 2 ^ 22 + w 13 * 2 ^ 10) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h6 : hi9 w 6 = (w 13 / 2 ^ 19 + w 14 * 2 ^ 13) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h7 : hi9 w 7 = (w 14 / 2 ^ 16 + w 15 * 2 ^ 16) % 2 ^ 29 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  have h8 : hi9 w 8 = w 15 / 2 ^ 13 := by simp only [hi9, Nat.reduceEqDiff, ↓reduceIte]
  unfold sv9
  rw [l0, l1, l2, l3, l4, l5, l6, l7, l8, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have j0 : (w 0 / 2 ^ 29 + w 1 * 2 ^ 3) % 2 ^ 29 = w 0 / 2 ^ 29 + w 1 % 2 ^ 26 * 2 ^ 3 := by omega
  have j1 : (w 1 / 2 ^ 26 + w 2 * 2 ^ 6) % 2 ^ 29 = w 1 / 2 ^ 26 + w 2 % 2 ^ 23 * 2 ^ 6 := by omega
  have j2 : (w 2 / 2 ^ 23 + w 3 * 2 ^ 9) % 2 ^ 29 = w 2 / 2 ^ 23 + w 3 % 2 ^ 20 * 2 ^ 9 := by omega
  have j3 : (w 3 / 2 ^ 20 + w 4 * 2 ^ 12) % 2 ^ 29 = w 3 / 2 ^ 20 + w 4 % 2 ^ 17 * 2 ^ 12 := by omega
  have j4 : (w 4 / 2 ^ 17 + w 5 * 2 ^ 15) % 2 ^ 29 = w 4 / 2 ^ 17 + w 5 % 2 ^ 14 * 2 ^ 15 := by omega
  have j5 : (w 5 / 2 ^ 14 + w 6 * 2 ^ 18) % 2 ^ 29 = w 5 / 2 ^ 14 + w 6 % 2 ^ 11 * 2 ^ 18 := by omega
  have j6 : (w 6 / 2 ^ 11 + w 7 * 2 ^ 21) % 2 ^ 29 = w 6 / 2 ^ 11 + w 7 % 2 ^ 8 * 2 ^ 21 := by omega
  have j7 : (w 7 / 2 ^ 8 + w 8 * 2 ^ 24) % 2 ^ 29 = w 7 / 2 ^ 8 + w 8 % 2 ^ 5 * 2 ^ 24 := by omega
  have j8 : (w 8 / 2 ^ 5 + w 9 * 2 ^ 27) % 2 ^ 29 = w 8 / 2 ^ 5 + w 9 % 2 ^ 2 * 2 ^ 27 := by omega
  have j9 : (w 9 / 2 ^ 31 + w 10 * 2 ^ 1) % 2 ^ 29 = w 9 / 2 ^ 31 + w 10 % 2 ^ 28 * 2 ^ 1 := by omega
  have j10 : (w 10 / 2 ^ 28 + w 11 * 2 ^ 4) % 2 ^ 29 = w 10 / 2 ^ 28 + w 11 % 2 ^ 25 * 2 ^ 4 := by omega
  have j11 : (w 11 / 2 ^ 25 + w 12 * 2 ^ 7) % 2 ^ 29 = w 11 / 2 ^ 25 + w 12 % 2 ^ 22 * 2 ^ 7 := by omega
  have j12 : (w 12 / 2 ^ 22 + w 13 * 2 ^ 10) % 2 ^ 29 = w 12 / 2 ^ 22 + w 13 % 2 ^ 19 * 2 ^ 10 := by omega
  have j13 : (w 13 / 2 ^ 19 + w 14 * 2 ^ 13) % 2 ^ 29 = w 13 / 2 ^ 19 + w 14 % 2 ^ 16 * 2 ^ 13 := by omega
  have j14 : (w 14 / 2 ^ 16 + w 15 * 2 ^ 16) % 2 ^ 29 = w 14 / 2 ^ 16 + w 15 % 2 ^ 13 * 2 ^ 16 := by omega
  rw [j0, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14]
  have d0 : w 0 = w 0 % 2 ^ 29 + 2 ^ 29 * (w 0 / 2 ^ 29) := by omega
  have d1 : w 1 = w 1 % 2 ^ 26 + 2 ^ 26 * (w 1 / 2 ^ 26) := by omega
  have d2 : w 2 = w 2 % 2 ^ 23 + 2 ^ 23 * (w 2 / 2 ^ 23) := by omega
  have d3 : w 3 = w 3 % 2 ^ 20 + 2 ^ 20 * (w 3 / 2 ^ 20) := by omega
  have d4 : w 4 = w 4 % 2 ^ 17 + 2 ^ 17 * (w 4 / 2 ^ 17) := by omega
  have d5 : w 5 = w 5 % 2 ^ 14 + 2 ^ 14 * (w 5 / 2 ^ 14) := by omega
  have d6 : w 6 = w 6 % 2 ^ 11 + 2 ^ 11 * (w 6 / 2 ^ 11) := by omega
  have d7 : w 7 = w 7 % 2 ^ 8 + 2 ^ 8 * (w 7 / 2 ^ 8) := by omega
  have d8 : w 8 = w 8 % 2 ^ 5 + 2 ^ 5 * (w 8 / 2 ^ 5) := by omega
  have d9 : w 9 = w 9 % 2 ^ 2 + 2 ^ 2 * (w 9 / 2 ^ 2 % 2 ^ 29) + 2 ^ 31 * (w 9 / 2 ^ 31) := by omega
  have d10 : w 10 = w 10 % 2 ^ 28 + 2 ^ 28 * (w 10 / 2 ^ 28) := by omega
  have d11 : w 11 = w 11 % 2 ^ 25 + 2 ^ 25 * (w 11 / 2 ^ 25) := by omega
  have d12 : w 12 = w 12 % 2 ^ 22 + 2 ^ 22 * (w 12 / 2 ^ 22) := by omega
  have d13 : w 13 = w 13 % 2 ^ 19 + 2 ^ 19 * (w 13 / 2 ^ 19) := by omega
  have d14 : w 14 = w 14 % 2 ^ 16 + 2 ^ 16 * (w 14 / 2 ^ 16) := by omega
  have d15 : w 15 = w 15 % 2 ^ 13 + 2 ^ 13 * (w 15 / 2 ^ 13) := by omega
  generalize w 0 % 2 ^ 29 = e0 at d0 ⊢
  generalize w 0 / 2 ^ 29 = e1 at d0 ⊢
  generalize w 1 % 2 ^ 26 = e2 at d1 ⊢
  generalize w 1 / 2 ^ 26 = e3 at d1 ⊢
  generalize w 2 % 2 ^ 23 = e4 at d2 ⊢
  generalize w 2 / 2 ^ 23 = e5 at d2 ⊢
  generalize w 3 % 2 ^ 20 = e6 at d3 ⊢
  generalize w 3 / 2 ^ 20 = e7 at d3 ⊢
  generalize w 4 % 2 ^ 17 = e8 at d4 ⊢
  generalize w 4 / 2 ^ 17 = e9 at d4 ⊢
  generalize w 5 % 2 ^ 14 = e10 at d5 ⊢
  generalize w 5 / 2 ^ 14 = e11 at d5 ⊢
  generalize w 6 % 2 ^ 11 = e12 at d6 ⊢
  generalize w 6 / 2 ^ 11 = e13 at d6 ⊢
  generalize w 7 % 2 ^ 8 = e14 at d7 ⊢
  generalize w 7 / 2 ^ 8 = e15 at d7 ⊢
  generalize w 8 % 2 ^ 5 = e16 at d8 ⊢
  generalize w 8 / 2 ^ 5 = e17 at d8 ⊢
  generalize w 9 % 2 ^ 2 = e18 at d9 ⊢
  generalize w 9 / 2 ^ 2 % 2 ^ 29 = e19 at d9 ⊢
  generalize w 9 / 2 ^ 31 = e20 at d9 ⊢
  generalize w 10 % 2 ^ 28 = e21 at d10 ⊢
  generalize w 10 / 2 ^ 28 = e22 at d10 ⊢
  generalize w 11 % 2 ^ 25 = e23 at d11 ⊢
  generalize w 11 / 2 ^ 25 = e24 at d11 ⊢
  generalize w 12 % 2 ^ 22 = e25 at d12 ⊢
  generalize w 12 / 2 ^ 22 = e26 at d12 ⊢
  generalize w 13 % 2 ^ 19 = e27 at d13 ⊢
  generalize w 13 / 2 ^ 19 = e28 at d13 ⊢
  generalize w 14 % 2 ^ 16 = e29 at d14 ⊢
  generalize w 14 / 2 ^ 16 = e30 at d14 ⊢
  generalize w 15 % 2 ^ 13 = e31 at d15 ⊢
  generalize w 15 / 2 ^ 13 = e32 at d15 ⊢
  rw [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15]
  ring_eq

end C3.RV32.EdK
