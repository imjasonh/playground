/-!
Minimal RV32IMC (32-bit RISC-V + Compressed) instruction decoder and machine-state model
for verifying ESP32-C3 ROM `.asm` dumps.
-/

namespace Esp32c3Rom.Rv32imc

/-- 5-bit register index (`x0`..`x31`). -/
abbrev Reg := Fin 32

/-- Decoded RV32IMC instruction subset used by ESP32-C3 ROM routines. -/
inductive Instr where
  | lui (rd : Reg) (imm : BitVec 32)
  | addi (rd rs1 : Reg) (imm : BitVec 32)
  | slli (rd rs1 : Reg) (shamt : Nat)
  | srli (rd rs1 : Reg) (shamt : Nat)
  | srai (rd rs1 : Reg) (shamt : Nat)
  | andi (rd rs1 : Reg) (imm : BitVec 32)
  | add (rd rs1 rs2 : Reg)
  | sub (rd rs1 rs2 : Reg)
  | xor (rd rs1 rs2 : Reg)
  | or (rd rs1 rs2 : Reg)
  | lbu (rd rs1 : Reg) (imm : BitVec 32)
  | lw (rd rs1 : Reg) (imm : BitVec 32)
  | sb (rs1 rs2 : Reg) (imm : BitVec 32)
  | bne (rs1 rs2 : Reg) (imm : BitVec 32)
  | bge (rs1 rs2 : Reg) (imm : BitVec 32)
  | blt (rs1 rs2 : Reg) (imm : BitVec 32)
  | jal (rd : Reg) (imm : BitVec 32)
  | jalr (rd rs1 : Reg) (imm : BitVec 32)
  | unknown (raw : UInt32) (len : Nat)
  deriving Repr, DecidableEq

/-- Machine state: 32 general-purpose registers, program counter, and byte-addressed memory. -/
structure State where
  regs : Reg → BitVec 32
  pc : BitVec 32
  mem : BitVec 32 → UInt8

def State.readReg (s : State) (r : Reg) : BitVec 32 :=
  if r.val == 0 then 0#32 else s.regs r

def State.writeReg (s : State) (r : Reg) (v : BitVec 32) : State :=
  if r.val == 0 then s
  else { s with regs := fun r' => if r' == r then v else s.regs r' }

/-- Read a 16-bit little-endian halfword from a byte list at byte offset `off`. -/
def readU16LE (bytes : List UInt8) (off : Nat) : Option UInt16 :=
  match bytes[off]?, bytes[off + 1]? with
  | some b0, some b1 => some (b0.toUInt16 ||| (b1.toUInt16 <<< 8))
  | _, _ => none

/-- Read a 32-bit little-endian word from a byte list at byte offset `off`. -/
def readU32LE (bytes : List UInt8) (off : Nat) : Option UInt32 :=
  match bytes[off]?, bytes[off + 1]?, bytes[off + 2]?, bytes[off + 3]? with
  | some b0, some b1, some b2, some b3 =>
    some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))
  | _, _, _, _ => none

/-- Check that every instruction in a byte stream has valid RV32IMC length (2 for RVC, 4 for RV32)
    and terminates cleanly at the end of `bytes` without falling off or hitting an invalid encoding. -/
def validRv32imcStream (bytes : List UInt8) (off : Nat) : Nat → Bool
  | 0 => off == bytes.length
  | fuel + 1 =>
    if off == bytes.length then true
    else
      match readU16LE bytes off with
      | none => false
      | some h =>
        if (h &&& 0x3) != 0x3 then
          -- 16-bit compressed instruction (RVC): must not be 0x0000 (illegal)
          h != 0 && validRv32imcStream bytes (off + 2) fuel
        else
          -- 32-bit instruction: must have all 4 bytes
          match readU32LE bytes off with
          | none => false
          | some _ => validRv32imcStream bytes (off + 4) fuel

end Esp32c3Rom.Rv32imc
