import C3BootProofs.Proofs.ShaStream5

/-!
# SHA-512's padding as a stream

`ShaStream.lean`'s `sha256_stream`, `padTail_short`, and `padTail_long` for
SHA-512: the digest is the hash of the full 128-byte blocks, then of the one
or two blocks that `finalize` builds from the buffer, the 0x80 byte, zeros,
and the 16-byte length in bits.
-/

namespace C3

open Sha512

theorem be128_length (n : Nat) : (be128 n).length = 16 := by simp [be128]

/-- The number of padding zeros. -/
def padZeros5 (len : Nat) : Nat := (239 - len % 128) % 128

/-- The buffer after `finalize` pads it: the tail, 0x80, zeros, and the
length in bits. -/
def padTail5 (msg : Bytes) : Bytes :=
  tailBytes5 msg ++ [0x80] ++ List.replicate (padZeros5 msg.length) 0 ++ be128 (8 * msg.length)

theorem padTail5_length (msg : Bytes) :
    (padTail5 msg).length = msg.length % 128 + 17 + padZeros5 msg.length := by
  simp only [padTail5, List.length_append, List.length_replicate, be128_length, tailBytes5_length,
    List.length_singleton]
  omega

/-- FIPS 180-4's digest: the hash of the full blocks, then of the padded
buffer's one or two blocks. -/
theorem sha512_stream (msg : Bytes) :
    sha512 msg = ((fullBlocks5 msg ++ blocks ((padTail5 msg).length / 128) (padTail5 msg)).foldl compress h0).flatMap
      wordBytes := by
  have hpad : pad msg = msg.take (128 * (msg.length / 128)) ++ padTail5 msg := by
    unfold pad padTail5 tailBytes5 padZeros5
    simp only [← List.append_assoc, List.take_append_drop]
  have hA := take_full5_length msg
  have hT := padTail5_length msg
  have hP : (pad msg).length = 128 * (msg.length / 128 + (padTail5 msg).length / 128) := by
    rw [hpad, List.length_append, hA, hT]; unfold padZeros5; omega
  have hm : (padTail5 msg).length = 128 * ((padTail5 msg).length / 128) := by rw [hT]; unfold padZeros5; omega
  unfold sha512
  simp only
  rw [blocks5_fuel _ _ _ hP (by omega), hpad, blocks5_append _ _ _ _ hA, ← blocks5_take]
  rfl

/-- A buffer of fewer than 112 bytes pads to one block. -/
theorem padTail5_short (msg : Bytes) (h : msg.length % 128 < 112) :
    blocks ((padTail5 msg).length / 128) (padTail5 msg) = [padTail5 msg] := by
  have hl : (padTail5 msg).length = 128 := by rw [padTail5_length]; unfold padZeros5; omega
  rw [hl, show 128 / 128 = 0 + 1 from rfl, blocks5_succ]
  have hne : (padTail5 msg).isEmpty = false := by
    cases hc : padTail5 msg with
    | nil => rw [hc] at hl; cases hl
    | cons _ _ => rfl
  rw [hne, ite_eq_right Bool.false_ne_true, List.take_of_length_le (by omega)]
  rfl

/-- A buffer of 112 bytes or more pads to two blocks: the tail, 0x80, and
zeros, then 112 zeros and the length in bits. -/
theorem padTail5_long (msg : Bytes) (h : 112 ≤ msg.length % 128) :
    blocks ((padTail5 msg).length / 128) (padTail5 msg) =
      [tailBytes5 msg ++ [0x80] ++ List.replicate (127 - msg.length % 128) 0,
       List.replicate 112 0 ++ be128 (8 * msg.length)] := by
  have hz : padZeros5 msg.length = (127 - msg.length % 128) + 112 := by unfold padZeros5; omega
  have hl : (padTail5 msg).length = 256 := by rw [padTail5_length]; unfold padZeros5; omega
  have hsplit : padTail5 msg = (tailBytes5 msg ++ [0x80] ++ List.replicate (127 - msg.length % 128) 0) ++
      (List.replicate 112 0 ++ be128 (8 * msg.length)) := by
    unfold padTail5
    rw [hz, ← List.replicate_append_replicate]
    simp only [List.append_assoc]
  have h1 : (tailBytes5 msg ++ [0x80] ++ List.replicate (127 - msg.length % 128) 0).length = 128 := by
    simp only [List.length_append, tailBytes5_length, List.length_singleton, List.length_replicate]; omega
  have h2 : (List.replicate 112 0 ++ be128 (8 * msg.length)).length = 128 := by
    simp only [List.length_append, List.length_replicate, be128_length]
  rw [hl, show 256 / 128 = 1 + 1 from rfl, hsplit, blocks5_append 1 1 _ _ h1]
  rw [show (1 : Nat) = 0 + 1 from rfl, blocks5_succ, blocks5_succ]
  have ne1 : (tailBytes5 msg ++ [0x80] ++ List.replicate (127 - msg.length % 128) 0).isEmpty = false := by
    cases hc : (tailBytes5 msg ++ [0x80] ++ List.replicate (127 - msg.length % 128) 0) with
    | nil => rw [hc] at h1; cases h1
    | cons _ _ => rfl
  have ne2 : (List.replicate 112 0 ++ be128 (8 * msg.length)).isEmpty = false := by
    cases hc : (List.replicate 112 0 ++ be128 (8 * msg.length)) with
    | nil => rw [hc] at h2; cases h2
    | cons _ _ => rfl
  rw [ne1, ne2, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
    List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  rfl

end C3
