import C3BootProofs.Proofs.Sha256Data

/-!
# SHA-256 as a stream

The compiled hasher keeps a message as its full 64-byte blocks, already
compressed into the hash value, and the bytes after them in a buffer.
`fullBlocks` and `tailBytes` split a message that way. `fullBlocks_append`
says how appending bytes moves the split, which covers every case of
`update`, and `sha256_stream` rewrites FIPS 180-4's padded digest as the
full blocks followed by the one or two blocks that `finalize` builds from
the buffer.
-/

namespace C3

open Sha256

/-- The 64-byte blocks of `msg`'s first `64 * (msg.length / 64)` bytes. -/
def fullBlocks (msg : Bytes) : List Bytes := blocks (msg.length / 64) msg

/-- The bytes of `msg` after its full blocks: fewer than 64. -/
def tailBytes (msg : Bytes) : Bytes := msg.drop (64 * (msg.length / 64))

theorem tailBytes_length (msg : Bytes) : (tailBytes msg).length = msg.length % 64 := by
  unfold tailBytes; rw [List.length_drop]; omega

theorem blocks_succ (n : Nat) (b : Bytes) :
    blocks (n + 1) b = if b.isEmpty then [] else b.take 64 :: blocks n (b.drop 64) := rfl

/-- `List.drop_take` without `Classical.choice`, which the library's uses. -/
theorem drop_take' {α : Type} : ∀ (i j : Nat) (l : List α), (l.take j).drop i = (l.drop i).take (j - i)
  | 0, j, l => by rw [List.drop_zero, List.drop_zero, Nat.sub_zero]
  | i + 1, 0, l => by rw [List.take_zero, List.drop_nil, Nat.zero_sub, List.take_zero]
  | i + 1, j + 1, [] => by rw [List.take_nil, List.drop_nil, List.take_nil]
  | i + 1, j + 1, x :: xs => by
    rw [List.take_succ_cons, List.drop_succ_cons, List.drop_succ_cons, Nat.add_sub_add_right]
    exact drop_take' i j xs

/-- `blocks` reads only the first `64 * fuel` bytes. -/
theorem blocks_take : ∀ (k : Nat) (b : Bytes), blocks k b = blocks k (b.take (64 * k))
  | 0, _ => rfl
  | k + 1, b => by
    unfold blocks
    by_cases hb : b.isEmpty
    · have : b = [] := List.isEmpty_iff.mp hb
      subst this; rfl
    · have hb' : (b.take (64 * (k + 1))).isEmpty = false := by
        cases b with
        | nil => exact absurd rfl hb
        | cons x xs => rfl
      rw [ite_eq_right hb, hb', ite_eq_right Bool.false_ne_true, List.take_take, show min 64 (64 * (k + 1)) = 64 by omega,
        blocks_take k (b.drop 64), blocks_take k ((b.take (64 * (k + 1))).drop 64), drop_take',
        List.take_take, show 64 * (k + 1) - 64 = 64 * k by omega, Nat.min_self]

/-- `blocks` splits after a whole number of blocks. -/
theorem blocks_append : ∀ (j k : Nat) (a b : Bytes), a.length = 64 * j →
    blocks (j + k) (a ++ b) = blocks j a ++ blocks k b
  | 0, k, a, b, h => by
    have : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [blocks]
  | j + 1, k, a, b, h => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    have hne : a ≠ [] := fun e => by subst e; simp at h
    have hab : (a ++ b).isEmpty = false := by
      cases a with
      | nil => exact absurd rfl hne
      | cons x xs => rfl
    have ha : a.isEmpty = false := by
      cases a with
      | nil => exact absurd rfl hne
      | cons x xs => rfl
    rw [blocks_succ (j + k), blocks_succ j, hab, ha, ite_eq_right Bool.false_ne_true,
      ite_eq_right Bool.false_ne_true, List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega), blocks_append j k (a.drop 64) b (by rw [List.length_drop]; omega)]
    rfl

/-- With enough fuel, `blocks` of a whole number of blocks is that many. -/
theorem blocks_fuel : ∀ (m fuel : Nat) (b : Bytes), b.length = 64 * m → m ≤ fuel → blocks fuel b = blocks m b
  | 0, fuel, b, h, _ => by
    have : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases fuel <;> rfl
  | m + 1, 0, b, _, h => absurd h (by omega)
  | m + 1, fuel + 1, b, h, hf => by
    have hb : b.isEmpty = false := by
      cases b with
      | nil => simp at h
      | cons x xs => rfl
    unfold blocks
    rw [hb, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
      blocks_fuel m fuel (b.drop 64) (by rw [List.length_drop]; omega) (by omega)]

theorem msg_split (msg : Bytes) : msg = msg.take (64 * (msg.length / 64)) ++ tailBytes msg :=
  (List.take_append_drop _ _).symm

theorem take_full_length (msg : Bytes) :
    (msg.take (64 * (msg.length / 64))).length = 64 * (msg.length / 64) := by
  rw [List.length_take]; omega

theorem fullBlocks_eq (msg : Bytes) :
    fullBlocks msg = blocks (msg.length / 64) (msg.take (64 * (msg.length / 64))) := by
  unfold fullBlocks; exact blocks_take _ _

/-- Appending `d` adds the full blocks of the old buffer followed by `d`, and
leaves the rest in the buffer. -/
theorem fullBlocks_append (msg d : Bytes) :
    fullBlocks (msg ++ d) = fullBlocks msg ++
      blocks (((tailBytes msg).length + d.length) / 64) (tailBytes msg ++ d) ∧
    tailBytes (msg ++ d) =
      (tailBytes msg ++ d).drop (64 * (((tailBytes msg).length + d.length) / 64)) := by
  have hA := take_full_length msg
  have hr := tailBytes_length msg
  have hsplit : msg ++ d = msg.take (64 * (msg.length / 64)) ++ (tailBytes msg ++ d) := by
    rw [← List.append_assoc, ← msg_split]
  have hq : (msg ++ d).length / 64 = msg.length / 64 + ((tailBytes msg).length + d.length) / 64 := by
    rw [List.length_append, hr]; omega
  constructor
  · unfold fullBlocks
    rw [hq, hsplit, blocks_append _ _ _ (tailBytes msg ++ d) hA, ← blocks_take]
  · show (msg ++ d).drop (64 * ((msg ++ d).length / 64)) = _
    rw [hq, hsplit, show 64 * (msg.length / 64 + ((tailBytes msg).length + d.length) / 64) =
      (msg.take (64 * (msg.length / 64))).length + 64 * (((tailBytes msg).length + d.length) / 64) by
        rw [hA]; omega, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      Nat.add_sub_cancel_left]

theorem be64_length (n : Nat) : (be64 n).length = 8 := by simp [be64]

/-- The number of padding zeros. -/
def padZeros (len : Nat) : Nat := (119 - len % 64) % 64

/-- The buffer after `finalize` pads it: the tail, 0x80, zeros, and the
length in bits. -/
def padTail (msg : Bytes) : Bytes :=
  tailBytes msg ++ [0x80] ++ List.replicate (padZeros msg.length) 0 ++ be64 (8 * msg.length)

theorem padTail_length (msg : Bytes) :
    (padTail msg).length = msg.length % 64 + 9 + padZeros msg.length := by
  simp only [padTail, List.length_append, List.length_replicate, be64_length, tailBytes_length,
    List.length_singleton]
  omega

/-- FIPS 180-4's digest: the hash of the full blocks, then of the padded
buffer's one or two blocks. -/
theorem sha256_stream (msg : Bytes) :
    sha256 msg = ((fullBlocks msg ++ blocks ((padTail msg).length / 64) (padTail msg)).foldl compress h0).flatMap
      wordBytes := by
  have hpad : pad msg = msg.take (64 * (msg.length / 64)) ++ padTail msg := by
    unfold pad padTail tailBytes padZeros
    simp only [← List.append_assoc, List.take_append_drop]
  have hA := take_full_length msg
  have hT := padTail_length msg
  have hP : (pad msg).length = 64 * (msg.length / 64 + (padTail msg).length / 64) := by
    rw [hpad, List.length_append, hA, hT]; unfold padZeros; omega
  have hm : (padTail msg).length = 64 * ((padTail msg).length / 64) := by rw [hT]; unfold padZeros; omega
  unfold sha256
  simp only
  rw [blocks_fuel _ _ _ hP (by omega), hpad, blocks_append _ _ _ _ hA, ← blocks_take]
  rfl

/-- A buffer of fewer than 56 bytes pads to one block. -/
theorem padTail_short (msg : Bytes) (h : msg.length % 64 < 56) :
    blocks ((padTail msg).length / 64) (padTail msg) = [padTail msg] := by
  have hl : (padTail msg).length = 64 := by rw [padTail_length]; unfold padZeros; omega
  rw [hl, show 64 / 64 = 0 + 1 from rfl, blocks_succ]
  have hne : (padTail msg).isEmpty = false := by
    cases hc : padTail msg with
    | nil => rw [hc] at hl; cases hl
    | cons _ _ => rfl
  rw [hne, ite_eq_right Bool.false_ne_true, List.take_of_length_le (by omega)]
  rfl

/-- A buffer of 56 bytes or more pads to two blocks: the tail, 0x80, and
zeros, then 56 zeros and the length in bits. -/
theorem padTail_long (msg : Bytes) (h : 56 ≤ msg.length % 64) :
    blocks ((padTail msg).length / 64) (padTail msg) =
      [tailBytes msg ++ [0x80] ++ List.replicate (63 - msg.length % 64) 0,
       List.replicate 56 0 ++ be64 (8 * msg.length)] := by
  have hz : padZeros msg.length = (63 - msg.length % 64) + 56 := by unfold padZeros; omega
  have hl : (padTail msg).length = 128 := by rw [padTail_length]; unfold padZeros; omega
  have hsplit : padTail msg = (tailBytes msg ++ [0x80] ++ List.replicate (63 - msg.length % 64) 0) ++
      (List.replicate 56 0 ++ be64 (8 * msg.length)) := by
    unfold padTail
    rw [hz, ← List.replicate_append_replicate]
    simp only [List.append_assoc]
  have h1 : (tailBytes msg ++ [0x80] ++ List.replicate (63 - msg.length % 64) 0).length = 64 := by
    simp only [List.length_append, tailBytes_length, List.length_singleton, List.length_replicate]; omega
  have h2 : (List.replicate 56 0 ++ be64 (8 * msg.length)).length = 64 := by
    simp only [List.length_append, List.length_replicate, be64_length]
  rw [hl, show 128 / 64 = 1 + 1 from rfl, hsplit, blocks_append 1 1 _ _ h1]
  rw [show (1 : Nat) = 0 + 1 from rfl, blocks_succ, blocks_succ]
  have ne1 : (tailBytes msg ++ [0x80] ++ List.replicate (63 - msg.length % 64) 0).isEmpty = false := by
    cases hc : (tailBytes msg ++ [0x80] ++ List.replicate (63 - msg.length % 64) 0) with
    | nil => rw [hc] at h1; cases h1
    | cons _ _ => rfl
  have ne2 : (List.replicate 56 0 ++ be64 (8 * msg.length)).isEmpty = false := by
    cases hc : (List.replicate 56 0 ++ be64 (8 * msg.length)) with
    | nil => rw [hc] at h2; cases h2
    | cons _ _ => rfl
  rw [ne1, ne2, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
    List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  rfl

end C3
