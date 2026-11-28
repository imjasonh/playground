import C3BootProofs.Proofs.ShaStream
import C3BootProofs.Spec.Sha512

/-!
# SHA-512 as a stream

`ShaStream.lean` for SHA-512's 128-byte blocks: the compiled hasher keeps a
message as its full blocks, already compressed into the hash value, and the
bytes after them in a buffer. `fullBlocks5_append` says how appending bytes
moves the split, which covers every case of `update`.
-/

namespace C3

open Sha512

/-- The 128-byte blocks of `msg`'s first `128 * (msg.length / 128)` bytes. -/
def fullBlocks5 (msg : Bytes) : List Bytes := Sha512.blocks (msg.length / 128) msg

/-- The bytes of `msg` after its full blocks: fewer than 128. -/
def tailBytes5 (msg : Bytes) : Bytes := msg.drop (128 * (msg.length / 128))

theorem tailBytes5_length (msg : Bytes) : (tailBytes5 msg).length = msg.length % 128 := by
  unfold tailBytes5; rw [List.length_drop]; omega

theorem blocks5_succ (n : Nat) (b : Bytes) :
    Sha512.blocks (n + 1) b = if b.isEmpty then [] else b.take 128 :: Sha512.blocks n (b.drop 128) := rfl

/-- `blocks` reads only the first `128 * fuel` bytes. -/
theorem blocks5_take : ∀ (k : Nat) (b : Bytes), Sha512.blocks k b = Sha512.blocks k (b.take (128 * k))
  | 0, _ => rfl
  | k + 1, b => by
    unfold Sha512.blocks
    by_cases hb : b.isEmpty
    · have : b = [] := List.isEmpty_iff.mp hb
      subst this; rfl
    · have hb' : (b.take (128 * (k + 1))).isEmpty = false := by
        cases b with
        | nil => exact absurd rfl hb
        | cons x xs => rfl
      rw [ite_eq_right hb, hb', ite_eq_right Bool.false_ne_true, List.take_take, show min 128 (128 * (k + 1)) = 128 by omega,
        blocks5_take k (b.drop 128), blocks5_take k ((b.take (128 * (k + 1))).drop 128), drop_take',
        List.take_take, show 128 * (k + 1) - 128 = 128 * k by omega, Nat.min_self]

/-- `blocks` splits after a whole number of blocks. -/
theorem blocks5_append : ∀ (j k : Nat) (a b : Bytes), a.length = 128 * j →
    Sha512.blocks (j + k) (a ++ b) = Sha512.blocks j a ++ Sha512.blocks k b
  | 0, k, a, b, h => by
    have : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [Sha512.blocks]
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
    rw [blocks5_succ (j + k), blocks5_succ j, hab, ha, ite_eq_right Bool.false_ne_true,
      ite_eq_right Bool.false_ne_true, List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega), blocks5_append j k (a.drop 128) b (by rw [List.length_drop]; omega)]
    rfl

/-- With enough fuel, `blocks` of a whole number of blocks is that many. -/
theorem blocks5_fuel : ∀ (m fuel : Nat) (b : Bytes), b.length = 128 * m → m ≤ fuel → Sha512.blocks fuel b = Sha512.blocks m b
  | 0, fuel, b, h, _ => by
    have : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases fuel <;> rfl
  | m + 1, 0, b, _, h => absurd h (by omega)
  | m + 1, fuel + 1, b, h, hf => by
    have hb : b.isEmpty = false := by
      cases b with
      | nil => simp at h
      | cons x xs => rfl
    unfold Sha512.blocks
    rw [hb, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
      blocks5_fuel m fuel (b.drop 128) (by rw [List.length_drop]; omega) (by omega)]

theorem msg5_split (msg : Bytes) : msg = msg.take (128 * (msg.length / 128)) ++ tailBytes5 msg :=
  (List.take_append_drop _ _).symm

theorem take_full5_length (msg : Bytes) :
    (msg.take (128 * (msg.length / 128))).length = 128 * (msg.length / 128) := by
  rw [List.length_take]; omega

/-- Appending `d` adds the full blocks of the old buffer followed by `d`, and
leaves the rest in the buffer. -/
theorem fullBlocks5_append (msg d : Bytes) :
    fullBlocks5 (msg ++ d) = fullBlocks5 msg ++
      Sha512.blocks (((tailBytes5 msg).length + d.length) / 128) (tailBytes5 msg ++ d) ∧
    tailBytes5 (msg ++ d) =
      (tailBytes5 msg ++ d).drop (128 * (((tailBytes5 msg).length + d.length) / 128)) := by
  have hA := take_full5_length msg
  have hr := tailBytes5_length msg
  have hsplit : msg ++ d = msg.take (128 * (msg.length / 128)) ++ (tailBytes5 msg ++ d) := by
    rw [← List.append_assoc, ← msg5_split]
  have hq : (msg ++ d).length / 128 = msg.length / 128 + ((tailBytes5 msg).length + d.length) / 128 := by
    rw [List.length_append, hr]; omega
  constructor
  · unfold fullBlocks5
    rw [hq, hsplit, blocks5_append _ _ _ (tailBytes5 msg ++ d) hA, ← blocks5_take]
  · show (msg ++ d).drop (128 * ((msg ++ d).length / 128)) = _
    rw [hq, hsplit, show 128 * (msg.length / 128 + ((tailBytes5 msg).length + d.length) / 128) =
      (msg.take (128 * (msg.length / 128))).length + 128 * (((tailBytes5 msg).length + d.length) / 128) by
        rw [hA]; omega, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      Nat.add_sub_cancel_left]

/-- Appending at least the `r` bytes that fill the buffer adds the full
blocks of the old message, then the filled buffer, then the full blocks of
the rest of `d`. This is `update` with a partly full buffer. -/
theorem fullBlocks5_fill (msg d : Bytes) {r : Nat} (hr : (tailBytes5 msg).length + r = 128)
    (hd : r ≤ d.length) :
    fullBlocks5 (msg ++ d) = fullBlocks5 msg ++ (tailBytes5 msg ++ d.take r) ::
      Sha512.blocks ((d.length - r) / 128) (d.drop r) ∧
    tailBytes5 (msg ++ d) = (d.drop r).drop (128 * ((d.length - r) / 128)) := by
  obtain ⟨hf, ht⟩ := fullBlocks5_append msg d
  have hq : ((tailBytes5 msg).length + d.length) / 128 = (d.length - r) / 128 + 1 := by
    rw [show (tailBytes5 msg).length + d.length = 128 + (d.length - r) by omega]; omega
  have hne : (tailBytes5 msg ++ d).isEmpty = false := by
    cases h : tailBytes5 msg ++ d with
    | nil => have := congrArg List.length h; rw [List.length_append, List.length_nil] at this; omega
    | cons x xs => rfl
  have hdrop : (tailBytes5 msg ++ d).drop 128 = d.drop r := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, show 128 - (tailBytes5 msg).length = r by omega]
  refine ⟨?_, ?_⟩
  · rw [hf, hq, blocks5_succ, hne, ite_eq_right Bool.false_ne_true, List.take_append,
      List.take_of_length_le (by omega), show 128 - (tailBytes5 msg).length = r by omega, hdrop]
  · rw [ht, hq, show 128 * ((d.length - r) / 128 + 1) = 128 + 128 * ((d.length - r) / 128) by omega, ← List.drop_drop, hdrop]

/-- `blocks` of at least `128 * k` bytes has `k` blocks. -/
theorem blocks5_length : ∀ (k : Nat) (b : Bytes), 128 * k ≤ b.length → (Sha512.blocks k b).length = k
  | 0, _, _ => rfl
  | k + 1, b, h => by
    have hb : b.isEmpty = false := by
      cases b with
      | nil => simp at h
      | cons x xs => rfl
    rw [blocks5_succ, hb, ite_eq_right Bool.false_ne_true, List.length_cons,
      blocks5_length k (b.drop 128) (by rw [List.length_drop]; omega)]

theorem fullBlocks5_length (msg : Bytes) : (fullBlocks5 msg).length = msg.length / 128 :=
  blocks5_length _ _ (by omega)

end C3
