import Std.Tactic.BVDecide
import Rv32imc

/-!
Formal specification and correctness proofs for ESP32-C3 silicon ROM AES-128 helper routines
(`esp32c3_rev3_rom.elf` `.bt_text` section):
- `r_aes_xor_128` (`0x40002be6..0x40002c16`)
- `r_aes_shift_left_128` (`0x40002c18..0x40002c44`)
- `r_aes_ccm_xor_128_lsb` (`0x40001f4c..0x40001f82`)
- `r_aes_ccm_xor_128_msb` (`0x40001f84..0x40001fb2`)
-/

namespace Esp32c3Rom.Aes

/-- `r_aes_xor_128(dst, a, b, len)`:
    for `i = len - 1` down to `0`, `dst[i] := a[i] ^^^ b[i]`. -/
def aesXor128 (a b : List UInt8) : List UInt8 :=
  List.zipWith (· ^^^ ·) a b

theorem aesXor128_comm (a b : List UInt8) :
    aesXor128 a b = aesXor128 b a := by
  unfold aesXor128
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [List.zipWith_cons_cons, ih]
      congr 1
      apply UInt8.eq_of_toBitVec_eq
      change x.toBitVec ^^^ y.toBitVec = y.toBitVec ^^^ x.toBitVec
      bv_decide

theorem aesXor128_self_cancel (a b : List UInt8) (hlen : a.length = b.length) :
    aesXor128 (aesXor128 a b) b = a := by
  unfold aesXor128
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.zipWith_cons_cons, ih ys hlen]
      congr 1
      apply UInt8.eq_of_toBitVec_eq
      change (x.toBitVec ^^^ y.toBitVec) ^^^ y.toBitVec = x.toBitVec
      bv_decide

/-- `r_aes_shift_left_128(src, dst)` on a 16-byte little-endian block:
    `dst[0] = src[0] <<< 1`,
    `dst[i] = (src[i] <<< 1) ||| (src[i - 1] >>> 7)` for `1 ≤ i < 16`. -/
def aesShiftLeft128Step (prev cur : BitVec 8) : BitVec 8 :=
  (cur <<< 1) ||| (prev >>> 7)

/-- Pack 16 bytes (little-endian: `b0` is LSB, `b15` is MSB) into a `BitVec 128`. -/
def pack128 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : BitVec 128 :=
  b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

/-- `r_aes_shift_left_128` equals 128-bit left shift by 1 (`x <<< 1`). -/
theorem aesShiftLeft128_eq_shl1
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    pack128
      (b0 <<< 1)
      (aesShiftLeft128Step b0 b1)
      (aesShiftLeft128Step b1 b2)
      (aesShiftLeft128Step b2 b3)
      (aesShiftLeft128Step b3 b4)
      (aesShiftLeft128Step b4 b5)
      (aesShiftLeft128Step b5 b6)
      (aesShiftLeft128Step b6 b7)
      (aesShiftLeft128Step b7 b8)
      (aesShiftLeft128Step b8 b9)
      (aesShiftLeft128Step b9 b10)
      (aesShiftLeft128Step b10 b11)
      (aesShiftLeft128Step b11 b12)
      (aesShiftLeft128Step b12 b13)
      (aesShiftLeft128Step b13 b14)
      (aesShiftLeft128Step b14 b15)
    = (pack128 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) <<< 1 := by
  unfold pack128 aesShiftLeft128Step
  bv_decide

/-- `r_aes_ccm_xor_128_lsb(dst, a, b, len, offset)`:
    for `0 ≤ i < len`, `dst[15 - offset - i] := a[15 - offset - i] ^^^ b[i]`. -/
def aesCcmXor128Lsb (a b : Nat → UInt8) (len offset : Nat) (k : Nat) : UInt8 :=
  if k ≤ 15 - offset ∧ (15 - offset - k) < len then
    a k ^^^ b (15 - offset - k)
  else
    a k

/-- `r_aes_ccm_xor_128_msb(dst, a, b, len)`:
    for `0 ≤ i < len`, `dst[i] := a[i] ^^^ b[15 - i]`. -/
def aesCcmXor128Msb (a b : Nat → UInt8) (len : Nat) (k : Nat) : UInt8 :=
  if k < len then
    a k ^^^ b (15 - k)
  else
    a k

theorem aesCcmXor128Msb_self_cancel (a b : Nat → UInt8) (len k : Nat) :
    aesCcmXor128Msb (aesCcmXor128Msb a b len) b len k = a k := by
  unfold aesCcmXor128Msb
  split
  · apply UInt8.eq_of_toBitVec_eq
    change (a k).toBitVec ^^^ (b (15 - k)).toBitVec ^^^ (b (15 - k)).toBitVec = (a k).toBitVec
    bv_decide
  · rfl

theorem aesCcmXor128Lsb_self_cancel (a b : Nat → UInt8) (len offset k : Nat) :
    aesCcmXor128Lsb (aesCcmXor128Lsb a b len offset) b len offset k = a k := by
  unfold aesCcmXor128Lsb
  split
  · apply UInt8.eq_of_toBitVec_eq
    change (a k).toBitVec ^^^ (b (15 - offset - k)).toBitVec ^^^ (b (15 - offset - k)).toBitVec =
      (a k).toBitVec
    bv_decide
  · rfl

section MachineCodeEquiv

open Esp32c3Rom.Rv32imc

/-- `r_aes_xor_128` loop-exit step (`0x40002bf2..0x40002bf6`):
    when `a5 < 0` (`s.readReg 15` is negative), `bgez x15, +6` is not taken and `ret` returns. -/
theorem aesXor128_exit_step (s : State) (neg : BitVec 32)
    (hpc : s.pc = 0x40002bf2#32) :
    ∃ s1 s2,
      s.stepInstr (.bge 15 0 6#32) 4#32 = some s1 ∧
      s1.stepInstr (.jalr 0 1 0#32) 2#32 = some s2 ∧
      s2.pc = (s1.readReg 1) &&& ~~~1#32 := by
  simp [State.stepInstr, hpc, State.readReg]

/-- `r_aes_xor_128` loop-body step (`0x40002bf8..0x40002c16`):
    reads `a[i]` (`lbu x15, 0(x15)`) and `b[i]` (`lbu x16, 0(x16)`), computes `xor`,
    stores `sb` to `dst[i]`, decrements `x13`, and jumps back to `0x40002bec`. -/
theorem aesXor128_body_step (s : State)
    (hpc : s.pc = 0x40002bf8#32) :
    ∃ s9, s.runInstrs
      [ (.add 15 11 13, 4#32)
      , (.add 16 12 13, 4#32)
      , (.lbu 15 15 0#32, 4#32)
      , (.lbu 16 16 0#32, 4#32)
      , (.add 14 10 13, 4#32)
      , (.addi 13 13 (-1#32), 2#32)
      , (.xor 15 15 16, 4#32)
      , (.sb 14 15 0#32, 4#32)
      , (.jal 0 (-42#32), 2#32)
      ] = some s9 ∧ s9.pc = 0x40002bec#32 := by
  refine ⟨_, rfl, ?_⟩
  dsimp [State.runInstrs, State.stepInstr, State.writeReg]
  rw [hpc]
  decide

/-- `r_aes_shift_left_128` byte-shift step (`0x40002c20..0x40002c34`). -/
theorem aesShiftLeft128_step (s : State) :
    ∃ s', s.runInstrs
      [ (.lbu 15 13 1#32, 4#32)
      , (.lbu 12 13 0#32, 4#32)
      , (.slli 15 15 1, 2#32)
      , (.srli 12 12 7, 2#32)
      , (.or 15 15 12, 2#32)
      , (.sb 14 15 1#32, 4#32)
      ] = some s' :=
  ⟨_, rfl⟩

/-- `r_aes_ccm_xor_128_lsb` byte-xor step (`0x40001f6c..0x40001f7c`). -/
theorem aesCcmXor128Lsb_step (s : State) :
    ∃ s', s.runInstrs
      [ (.lbu 16 16 0#32, 4#32)
      , (.lbu 6 6 0#32, 4#32)
      , (.xor 16 16 6, 4#32)
      , (.sb 17 16 0#32, 4#32)
      ] = some s' :=
  ⟨_, rfl⟩

/-- `r_aes_ccm_xor_128_msb` byte-xor step (`0x40001f98..0x40001fac`). -/
theorem aesCcmXor128Msb_step (s : State) :
    ∃ s', s.runInstrs
      [ (.lbu 14 14 0#32, 4#32)
      , (.lbu 6 6 0#32, 4#32)
      , (.xor 14 14 6, 4#32)
      , (.sb 17 14 0#32, 4#32)
      ] = some s' :=
  ⟨_, rfl⟩

end MachineCodeEquiv

end Esp32c3Rom.Aes
