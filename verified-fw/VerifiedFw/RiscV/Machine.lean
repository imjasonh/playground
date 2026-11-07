/-
TRUSTED. Changes to this file need human review.

A model of the RV32I subset that the compiler emits, running in machine mode
on one hart with interrupts disabled.

The model is conservative: it faults (`step` returns `none`) on anything it
doesn't describe, such as a misaligned access or a load from a device. A proof
that the model never faults therefore says nothing about those cases, and the
hardware only has to agree with the model on the cases it describes.
-/

namespace VerifiedFw.RiscV

abbrev Word := BitVec 32

/-- An integer register, `x0` through `x31`. -/
abbrev Reg := Fin 32

/-- The RV32I instructions the compiler uses.

Branch and jump offsets are stored the way the hardware stores them: in units
of two bytes, so the byte offset is twice the sign-extended field. -/
inductive Instr where
  | lui (rd : Reg) (imm : BitVec 20)
  | addi (rd rs1 : Reg) (imm : BitVec 12)
  | add (rd rs1 rs2 : Reg)
  | sub (rd rs1 rs2 : Reg)
  | and (rd rs1 rs2 : Reg)
  | or (rd rs1 rs2 : Reg)
  | xor (rd rs1 rs2 : Reg)
  | sll (rd rs1 rs2 : Reg)
  | srl (rd rs1 rs2 : Reg)
  | sltu (rd rs1 rs2 : Reg)
  | lw (rd rs1 : Reg) (imm : BitVec 12)
  | sw (rs2 rs1 : Reg) (imm : BitVec 12)
  | beq (rs1 rs2 : Reg) (off : BitVec 12)
  | bne (rs1 rs2 : Reg) (off : BitVec 12)
  | jal (rd : Reg) (off : BitVec 20)
  deriving DecidableEq, Repr

/-- An observable store to a device register: address and value. -/
structure Event where
  addr : Word
  val : Word
  deriving DecidableEq, Repr

/-- What the model needs to know about a chip's address map. -/
structure Platform where
  /-- Addresses where a store reaches a device instead of RAM. -/
  isMmio : Word → Bool

structure Machine where
  pc : Word
  regs : Reg → Word
  /-- Instruction memory, by word-aligned address. Execution never writes it. -/
  imem : Word → Word
  /-- Data RAM, by word-aligned address. -/
  dmem : Word → Word
  /-- Device stores so far, oldest first. -/
  trace : List Event

namespace Machine

def reg (m : Machine) (r : Reg) : Word :=
  if r = 0 then 0 else m.regs r

/-- Writes to `x0` are discarded. -/
def setReg (m : Machine) (r : Reg) (v : Word) : Machine :=
  if r = 0 then m else { m with regs := fun x => if x = r then v else m.regs x }

def next (m : Machine) : Machine :=
  { m with pc := m.pc + 4 }

end Machine

/-- A RISC-V I-type or S-type immediate, sign-extended. -/
def sext12 (imm : BitVec 12) : Word := imm.signExtend 32

/-- The byte offset of a branch: twice the sign-extended field. -/
def branchOffset (off : BitVec 12) : Word := (off.signExtend 32) <<< 1

/-- The byte offset of `jal`: twice the sign-extended field. -/
def jumpOffset (off : BitVec 20) : Word := (off.signExtend 32) <<< 1

def aligned (a : Word) : Prop := a.toNat % 4 = 0

instance (a : Word) : Decidable (aligned a) := by
  unfold aligned; infer_instance

/-- Runs one already-decoded instruction. -/
def exec (p : Platform) (m : Machine) : Instr → Option Machine
  | .lui rd imm => some ((m.setReg rd ((imm.setWidth 32) <<< 12)).next)
  | .addi rd rs1 imm => some ((m.setReg rd (m.reg rs1 + sext12 imm)).next)
  | .add rd rs1 rs2 => some ((m.setReg rd (m.reg rs1 + m.reg rs2)).next)
  | .sub rd rs1 rs2 => some ((m.setReg rd (m.reg rs1 - m.reg rs2)).next)
  | .and rd rs1 rs2 => some ((m.setReg rd (m.reg rs1 &&& m.reg rs2)).next)
  | .or rd rs1 rs2 => some ((m.setReg rd (m.reg rs1 ||| m.reg rs2)).next)
  | .xor rd rs1 rs2 => some ((m.setReg rd (m.reg rs1 ^^^ m.reg rs2)).next)
  | .sll rd rs1 rs2 =>
    some ((m.setReg rd (m.reg rs1 <<< ((m.reg rs2).toNat % 32))).next)
  | .srl rd rs1 rs2 =>
    some ((m.setReg rd (m.reg rs1 >>> ((m.reg rs2).toNat % 32))).next)
  | .sltu rd rs1 rs2 =>
    some ((m.setReg rd (if m.reg rs1 < m.reg rs2 then 1 else 0)).next)
  | .lw rd rs1 imm =>
    let a := m.reg rs1 + sext12 imm
    if aligned a ∧ p.isMmio a = false then
      some ((m.setReg rd (m.dmem a)).next)
    else none
  | .sw rs2 rs1 imm =>
    let a := m.reg rs1 + sext12 imm
    let v := m.reg rs2
    if aligned a then
      if p.isMmio a then
        some { m.next with trace := m.trace ++ [⟨a, v⟩] }
      else
        some { m.next with dmem := fun x => if x = a then v else m.dmem x }
    else none
  | .beq rs1 rs2 off =>
    if m.reg rs1 = m.reg rs2 then some { m with pc := m.pc + branchOffset off }
    else some m.next
  | .bne rs1 rs2 off =>
    if m.reg rs1 ≠ m.reg rs2 then some { m with pc := m.pc + branchOffset off }
    else some m.next
  | .jal rd off =>
    some { m.setReg rd (m.pc + 4) with pc := m.pc + jumpOffset off }

end VerifiedFw.RiscV
