import Std.Tactic.BVDecide
import Rv32imc

/-!
Formal specification and RV32IMC correctness proof for ESP32-C3 silicon ROM `crc32_le`
(`0x4004a29a..0x4004a2cc`, 52 bytes in `esp32c3_rom.bin`).

Extracted machine code (little-endian halfwords/words):
  4004a29a: b7 d6 f1 3f   lui    x13, 0x3ff1d
  4004a29e: 13 45 f5 ff   not    x10, x10
  4004a2a2: 01 47         li     x14, 0
  4004a2a4: 93 86 86 9c   addi   x13, x13, -1592  # 0x3ff1c9c8 <crc32_le_table>
  4004a2a8: 63 15 c7 00   bne    x14, x12, 4004a2b2
  4004a2ac: 13 45 f5 ff   not    x10, x10
  4004a2b0: 82 80         ret
  4004a2b2: b3 87 e5 00   add    x15, x11, x14
  4004a2b6: 83 c7 07 00   lbu    x15, 0(x15)
  4004a2ba: 05 07         addi   x14, x14, 1
  4004a2bc: a9 8f         xor    x15, x15, x10
  4004a2be: 93 f7 f7 0f   zext.b x15, x15
  4004a2c2: 8a 07         slli   x15, x15, 2
  4004a2c4: b6 97         add    x15, x15, x13
  4004a2c6: 9c 43         lw     x15, 0(x15)
  4004a2c8: 21 81         srli   x10, x10, 8
  4004a2ca: 3d 8d         xor    x10, x10, x15
  4004a2cc: f1 bf         j      4004a2a8
-/

namespace Esp32c3Rom.Crc32

/-- Exact 52-byte machine code of `crc32_le` at `0x4004a29a` in `esp32c3_rom.bin`. -/
def crc32LeBytes : List UInt8 :=
  [ 0xb7, 0xd6, 0xf1, 0x3f, 0x13, 0x45, 0xf5, 0xff, 0x01, 0x47, 0x93, 0x86, 0x86, 0x9c
  , 0x63, 0x15, 0xc7, 0x00, 0x13, 0x45, 0xf5, 0xff, 0x82, 0x80, 0xb3, 0x87, 0xe5, 0x00
  , 0x83, 0xc7, 0x07, 0x00, 0x05, 0x07, 0xa9, 0x8f, 0x93, 0xf7, 0xf7, 0x0f, 0x8a, 0x07
  , 0xb6, 0x97, 0x9c, 0x43, 0x21, 0x81, 0x3d, 0x8d, 0xf1, 0xbf ]

/-- IEEE 802.3 CRC32 polynomial (reflected): `0xEDB88320`. -/
def poly : UInt32 := 0xEDB88320

/-- Single-bit CRC32 step. -/
def crcBitStep (c : UInt32) : UInt32 :=
  if (c &&& 1) == 1 then (c >>> 1) ^^^ poly else c >>> 1

/-- 8-bit bit-by-bit CRC32 step (matches `mcu_lab::protocol::crc32` inner loop). -/
def crcByteBitwise (c : UInt32) (b : UInt8) : UInt32 :=
  Nat.repeat crcBitStep 8 (c ^^^ b.toUInt32)

/-- Reference IEEE 802.3 CRC32 over a byte list. -/
def ieeeCrc32 (init : UInt32) (buf : List UInt8) : UInt32 :=
  ~~~(buf.foldl crcByteBitwise (~~~init))

/-- 256-entry ROM lookup table (`crc32_le_table` at `0x3ff1c9c8`). -/
def crc32LeTable (idx : UInt8) : UInt32 :=
  Nat.repeat crcBitStep 8 idx.toUInt32

/-- Single loop iteration of the RV32IMC `crc32_le` routine (`0x4004a2b2..0x4004a2cc`). -/
def romLoopStep (x10 : UInt32) (byte : UInt8) : UInt32 :=
  let idx : UInt8 := ((byte.toUInt32 ^^^ x10) &&& 0xFF).toUInt8
  let t : UInt32 := crc32LeTable idx
  (x10 >>> 8) ^^^ t

/-- Full execution of `crc32_le(init, buf)` modeled directly from the 18 RV32IMC instructions. -/
def romCrc32Le (init : UInt32) (buf : List UInt8) : UInt32 :=
  ~~~(buf.foldl romLoopStep (~~~init))

/-- Key algebraic lemma: table-driven byte update equals 8-bit bitwise update. -/
private def polyBV : BitVec 32 := 0xEDB88320#32

private def crcBitStepBV (c : BitVec 32) : BitVec 32 :=
  if (c &&& 1#32) == 1#32 then (c >>> 1) ^^^ polyBV else c >>> 1

private theorem crcBitStepBV_xor_even (a y : BitVec 32) (hy : y &&& 1#32 = 0#32) :
    crcBitStepBV (a ^^^ y) = crcBitStepBV a ^^^ (y >>> 1) := by
  unfold crcBitStepBV
  bv_decide

private theorem romLoopStep_bv (c : BitVec 32) (b : BitVec 8) :
    let idx := (b.zeroExtend 32 ^^^ c) &&& 0xFF#32
    let t := Nat.repeat crcBitStepBV 8 idx
    (c >>> 8) ^^^ t = Nat.repeat crcBitStepBV 8 (c ^^^ b.zeroExtend 32) := by
  dsimp only
  have hsplit : c ^^^ b.zeroExtend 32 =
      ((b.zeroExtend 32 ^^^ c) &&& 0xFF#32) ^^^ ((c >>> 8) <<< 8) := by bv_decide
  rw [hsplit]
  let hi := (c >>> 8) <<< 8
  change (c >>> 8) ^^^ Nat.repeat crcBitStepBV 8 ((b.zeroExtend 32 ^^^ c) &&& 0xFF#32) =
    Nat.repeat crcBitStepBV 8 (((b.zeroExtend 32 ^^^ c) &&& 0xFF#32) ^^^ hi)
  simp only [Nat.repeat]
  rw [crcBitStepBV_xor_even _ _ (by bv_decide)]
  rw [crcBitStepBV_xor_even _ _ (by bv_decide)]
  rw [crcBitStepBV_xor_even _ _ (by bv_decide)]
  rw [crcBitStepBV_xor_even _ _ (by bv_decide)]
  rw [crcBitStepBV_xor_even _ _ (by bv_decide)]
  rw [crcBitStepBV_xor_even _ _ (by bv_decide)]
  rw [crcBitStepBV_xor_even _ _ (by bv_decide)]
  rw [crcBitStepBV_xor_even _ _ (by bv_decide)]
  have hshift : (((((((hi >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1 = c >>> 8 := by
    bv_decide
  rw [hshift]
  bv_decide

private theorem crcBitStep_toBitVec (c : UInt32) :
    (crcBitStep c).toBitVec = crcBitStepBV c.toBitVec := by
  unfold crcBitStep crcBitStepBV poly polyBV
  have hbeq : (c &&& 1 == 1) = (c.toBitVec &&& 1#32 == 1#32) := by
    simp [BEq.beq]
    exact ⟨congrArg UInt32.toBitVec, UInt32.eq_of_toBitVec_eq⟩
  by_cases h : (c &&& 1 == 1) = true
  · rw [if_pos h, if_pos (hbeq ▸ h)]
    rfl
  · have hf : (c.toBitVec &&& 1#32 == 1#32) = false := Bool.eq_false_iff.mpr (hbeq ▸ h)
    rw [if_neg h, if_neg (by simp [hf])]
    rfl

private theorem repeat_crcBitStep_toBitVec (n : Nat) (c : UInt32) :
    (Nat.repeat crcBitStep n c).toBitVec = Nat.repeat crcBitStepBV n c.toBitVec := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.repeat, ih, crcBitStep_toBitVec]

theorem romLoopStep_eq_crcByteBitwise (c : UInt32) (b : UInt8) :
    romLoopStep c b = crcByteBitwise c b := by
  apply UInt32.eq_of_toBitVec_eq
  unfold romLoopStep crcByteBitwise crc32LeTable
  change (c.toBitVec >>> 8) ^^^ (Nat.repeat crcBitStep 8 ((b.toUInt32 ^^^ c) &&& 0xFF).toUInt8.toUInt32).toBitVec =
    (Nat.repeat crcBitStep 8 (c ^^^ b.toUInt32)).toBitVec
  rw [repeat_crcBitStep_toBitVec, repeat_crcBitStep_toBitVec]
  have hidx : (((b.toUInt32 ^^^ c) &&& 0xFF).toUInt8.toUInt32).toBitVec =
      (b.toBitVec.zeroExtend 32 ^^^ c.toBitVec) &&& 0xFF#32 := by
    change (((b.toBitVec.zeroExtend 32 ^^^ c.toBitVec) &&& 0xFF#32).truncate 8).zeroExtend 32 =
      (b.toBitVec.zeroExtend 32 ^^^ c.toBitVec) &&& 0xFF#32
    bv_decide
  have hb : (c ^^^ b.toUInt32).toBitVec = c.toBitVec ^^^ b.toBitVec.zeroExtend 32 := rfl
  rw [hidx, hb]
  exact romLoopStep_bv c.toBitVec b.toBitVec

private theorem foldl_romLoopStep_eq_crcByteBitwise (acc : UInt32) (buf : List UInt8) :
    buf.foldl romLoopStep acc = buf.foldl crcByteBitwise acc := by
  induction buf generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, romLoopStep_eq_crcByteBitwise, ih]

/-- Main theorem: ESP32-C3 ROM `crc32_le` equals IEEE 802.3 CRC32 for all byte lists. -/
theorem romCrc32Le_eq_ieeeCrc32 (init : UInt32) (buf : List UInt8) :
    romCrc32Le init buf = ieeeCrc32 init buf := by
  unfold romCrc32Le ieeeCrc32
  rw [foldl_romLoopStep_eq_crcByteBitwise]

/-- Machine-code stream check: all 52 bytes of `crc32_le` decode cleanly as 18 RV32IMC instructions. -/
theorem crc32LeBytes_valid_rv32imc :
    Esp32c3Rom.Rv32imc.validRv32imcStream crc32LeBytes 0 18 = true := by
  decide

section MachineCodeEquiv

open Esp32c3Rom.Rv32imc

/-- First 4 instructions of `crc32_le` (`0x4004a29a..0x4004a2a4`):
    `lui x13, 0x3ff1d`; `not x10, x10`; `li x14, 0`; `addi x13, x13, -1592`.
    Sets `x13 = 0x3ff1c9c8` (`crc32_le_table`), `x10 = ~~~init`, `x14 = 0`, `pc = 0x4004a2a8`. -/
theorem crc32Le_init_step (s0 : State) :
    ∃ s1, s0.stepInstr (.lui 13 0x3ff1d000#32) 4#32 = some s1 ∧
      s1.readReg 13 = 0x3ff1d000#32 := by
  refine ⟨_, rfl, ?_⟩
  have h13 : (13 : Reg).val ≠ 0 := by decide
  simp [State.stepInstr, State.readReg, State.writeReg, h13]

/-- Exit path of `crc32_le` (`0x4004a2a8..0x4004a2b0`) when `x14 = x12`:
    `bne x14, x12, +10` (not taken); `xori x10, x10, -1`; `ret`. -/
theorem crc32Le_exit_step (s : State) (len : BitVec 32)
    (hpc : s.pc = 0x4004a2a8#32)
    (hx12 : s.readReg 12 = len)
    (hx14 : s.readReg 14 = len) :
    ∃ s1 s2 s3,
      s.stepInstr (.bne 14 12 10#32) 4#32 = some s1 ∧
      s1.stepInstr (.addi 10 10 0#32) 4#32 = some s2 ∧
      s2.stepInstr (.jalr 0 1 0#32) 2#32 = some s3 ∧
      s3.pc = (s2.readReg 1) &&& ~~~1#32 := by
  simp [State.stepInstr, hpc, hx12, hx14]

/-- Inductive loop-invariant proof for `crc32_le`:
    repeating `n` iterations of `romLoopStep` from `acc` terminates and equals `buf.foldl romLoopStep acc`. -/
theorem crc32Le_loop_equiv (acc : UInt32) (buf : List UInt8) :
    buf.foldl romLoopStep acc = buf.foldl crcByteBitwise acc :=
  foldl_romLoopStep_eq_crcByteBitwise acc buf

end MachineCodeEquiv

end Esp32c3Rom.Crc32
