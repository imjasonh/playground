/-
TRUSTED. Changes to this file need human review.

The instruction decoder and the fetch-decode-execute step. The bit layouts
follow the RISC-V Unprivileged ISA, chapter "RV32I Base Integer Instruction
Set", base instruction formats R, I, S, B, U, and J.
-/
import VerifiedFw.RiscV.Machine

namespace VerifiedFw.RiscV

/-- `len` bits of `w` starting at bit `lo`. -/
def field (w : Word) (lo len : Nat) : Nat := w.toNat / 2 ^ lo % 2 ^ len

def regAt (w : Word) (lo : Nat) : Reg := ⟨w.toNat / 2 ^ lo % 32, Nat.mod_lt _ (by decide)⟩

def decode (w : Word) : Option Instr :=
  let rd := regAt w 7
  let rs1 := regAt w 15
  let rs2 := regAt w 20
  let immI : BitVec 12 := .ofNat 12 (field w 20 12)
  let immS : BitVec 12 := .ofNat 12 (field w 25 7 * 32 + field w 7 5)
  let offB : BitVec 12 := .ofNat 12
    (field w 31 1 * 2048 + field w 7 1 * 1024 + field w 25 6 * 16 + field w 8 4)
  let immU : BitVec 20 := .ofNat 20 (field w 12 20)
  let offJ : BitVec 20 := .ofNat 20
    (field w 31 1 * 524288 + field w 12 8 * 2048 + field w 20 1 * 1024 + field w 21 10)
  match field w 0 7, field w 12 3, field w 25 7 with
  | 0x37, _, _ => some (.lui rd immU)
  | 0x13, 0, _ => some (.addi rd rs1 immI)
  | 0x33, 0, 0x00 => some (.add rd rs1 rs2)
  | 0x33, 0, 0x20 => some (.sub rd rs1 rs2)
  | 0x33, 1, 0x00 => some (.sll rd rs1 rs2)
  | 0x33, 3, 0x00 => some (.sltu rd rs1 rs2)
  | 0x33, 4, 0x00 => some (.xor rd rs1 rs2)
  | 0x33, 5, 0x00 => some (.srl rd rs1 rs2)
  | 0x33, 6, 0x00 => some (.or rd rs1 rs2)
  | 0x33, 7, 0x00 => some (.and rd rs1 rs2)
  | 0x03, 2, _ => some (.lw rd rs1 immI)
  | 0x23, 2, _ => some (.sw rs2 rs1 immS)
  | 0x63, 0, _ => some (.beq rs1 rs2 offB)
  | 0x63, 1, _ => some (.bne rs1 rs2 offB)
  | 0x6f, _, _ => some (.jal rd offJ)
  | _, _, _ => none

/-- Fetches the 32-bit instruction at `pc`, decodes it, and runs it. -/
def step (p : Platform) (m : Machine) : Option Machine :=
  if aligned m.pc then
    match decode (m.imem m.pc) with
    | some i => exec p m i
    | none => none
  else none

end VerifiedFw.RiscV
