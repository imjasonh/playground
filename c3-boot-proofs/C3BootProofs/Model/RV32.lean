/-!
# RV32IMC

An executable model of the RV32I base, the M extension, and the C
extension's 16-bit forms, at machine level with no traps: an instruction
that would trap, such as a reserved encoding or a misaligned load or store,
makes `step` return `none`. With the C extension, instructions need only
16-bit alignment, so a 32-bit instruction may start at an address that is 2
modulo 4. Encodings that the C extension lists as HINTs, such as `C.LI`,
`C.LUI`, or `C.SLLI` with `rd = x0`, run as the instruction they stand for,
which writes `x0` and so changes nothing.
The ESP32-C3 implements RV32IMC. This is the compact semantics the plan
proves equivalent to the Sail model, and `rv-check` tests it against
Espressif's QEMU. It doesn't model CSRs, interrupts, or the system
instructions yet; those decode as `none`.
-/

namespace C3.RV32

abbrev Word := BitVec 32

/-- The state operations `step` needs: raw register access, the program
counter, and byte-addressed memory. `step` applies the `x0` rule itself, so
an instance stores whatever it's given. `Machine` is the instance the
proofs use; other instances, such as `boot-sim`'s, are for testing. -/
class Arch (σ : Type) where
  getReg : σ → Fin 32 → Word
  setReg : σ → Fin 32 → Word → σ
  getPc : σ → Word
  setPc : σ → Word → σ
  read8 : σ → Word → BitVec 8
  write8 : σ → Word → BitVec 8 → σ

section Ops

variable {σ : Type} [Arch σ]

/-- A register's value; `x0` reads as zero. -/
def reg (s : σ) (r : Fin 32) : Word := if r.val = 0 then 0 else Arch.getReg s r

/-- Sets a register; writes to `x0` are discarded. -/
def writeReg (s : σ) (r : Fin 32) (v : Word) : σ := if r.val = 0 then s else Arch.setReg s r v

def load8 (s : σ) (a : Word) : BitVec 8 := Arch.read8 s a

def load16 (s : σ) (a : Word) : BitVec 16 := load8 s (a + 1) ++ load8 s a

def load32 (s : σ) (a : Word) : Word :=
  load8 s (a + 3) ++ load8 s (a + 2) ++ load8 s (a + 1) ++ load8 s a

def store8 (s : σ) (a : Word) (v : BitVec 8) : σ := Arch.write8 s a v

def store16 (s : σ) (a : Word) (v : BitVec 16) : σ :=
  store8 (store8 s a (v.extractLsb' 0 8)) (a + 1) (v.extractLsb' 8 8)

def store32 (s : σ) (a : Word) (v : Word) : σ :=
  store8 (store8 (store8 (store8 s a (v.extractLsb' 0 8)) (a + 1) (v.extractLsb' 8 8)) (a + 2)
    (v.extractLsb' 16 8)) (a + 3) (v.extractLsb' 24 8)

end Ops

/-- Registers, the program counter, and byte-addressed memory, as
functions: the state the proofs use. -/
structure Machine where
  regs : Fin 32 → Word
  pc : Word
  mem : Word → BitVec 8

instance : Arch Machine where
  getReg m r := m.regs r
  setReg m r v := { m with regs := fun i => if i = r then v else m.regs i }
  getPc m := m.pc
  setPc m v := { m with pc := v }
  read8 m a := m.mem a
  write8 m a v := { m with mem := fun x => if x = a then v else m.mem x }

inductive BranchOp | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, Repr

inductive LoadOp | lb | lh | lw | lbu | lhu
  deriving DecidableEq, Repr

inductive StoreOp | sb | sh | sw
  deriving DecidableEq, Repr

inductive AluOp
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  deriving DecidableEq, Repr

/-- A decoded instruction. Immediates are already sign- or zero-extended to
32 bits, and compressed forms are expanded to the base instruction they
stand for. -/
inductive Instr
  | lui (rd : Fin 32) (imm : Word)
  | auipc (rd : Fin 32) (imm : Word)
  | jal (rd : Fin 32) (off : Word)
  | jalr (rd rs1 : Fin 32) (off : Word)
  | branch (op : BranchOp) (rs1 rs2 : Fin 32) (off : Word)
  | load (op : LoadOp) (rd rs1 : Fin 32) (off : Word)
  | store (op : StoreOp) (rs1 rs2 : Fin 32) (off : Word)
  | aluImm (op : AluOp) (rd rs1 : Fin 32) (imm : Word)
  | alu (op : AluOp) (rd rs1 rs2 : Fin 32)
  | fence
  deriving DecidableEq, Repr

/-- Bits `hi` down to `lo` of `w`, as a natural number. -/
def bits (w : Nat) (hi lo : Nat) : Nat := (w >>> lo) % 2 ^ (hi + 1 - lo)

def regOf (n : Nat) : Fin 32 := ⟨n % 32, Nat.mod_lt _ (by decide)⟩

/-- Sign-extends the low `n` bits of `v` to 32 bits. -/
def sext (n : Nat) (v : Nat) : Word := (BitVec.ofNat n v).signExtend 32

def zext (v : Nat) : Word := BitVec.ofNat 32 v

/-- Decodes a 32-bit instruction. -/
def decode32 (w : Nat) : Option Instr :=
  let opcode := bits w 6 0
  let rd := regOf (bits w 11 7)
  let f3 := bits w 14 12
  let rs1 := regOf (bits w 19 15)
  let rs2 := regOf (bits w 24 20)
  let f7 := bits w 31 25
  let immI := sext 12 (bits w 31 20)
  let immS := sext 12 (bits w 31 25 * 32 + bits w 11 7)
  let immB := sext 13 (bits w 31 31 * 4096 + bits w 7 7 * 2048 + bits w 30 25 * 32 +
    bits w 11 8 * 2)
  let immU := zext (bits w 31 12 * 4096)
  let immJ := sext 21 (bits w 31 31 * 1048576 + bits w 19 12 * 4096 + bits w 20 20 * 2048 +
    bits w 30 21 * 2)
  match opcode with
  | 0x37 => some (.lui rd immU)
  | 0x17 => some (.auipc rd immU)
  | 0x6F => some (.jal rd immJ)
  | 0x67 => if f3 == 0 then some (.jalr rd rs1 immI) else none
  | 0x63 =>
    let op? : Option BranchOp := match f3 with
      | 0 => some .beq | 1 => some .bne | 4 => some .blt | 5 => some .bge
      | 6 => some .bltu | 7 => some .bgeu | _ => none
    op?.map fun op => .branch op rs1 rs2 immB
  | 0x03 =>
    let op? : Option LoadOp := match f3 with
      | 0 => some .lb | 1 => some .lh | 2 => some .lw | 4 => some .lbu | 5 => some .lhu
      | _ => none
    op?.map fun op => .load op rd rs1 immI
  | 0x23 =>
    let op? : Option StoreOp := match f3 with
      | 0 => some .sb | 1 => some .sh | 2 => some .sw | _ => none
    op?.map fun op => .store op rs1 rs2 immS
  | 0x13 =>
    match f3 with
    | 0 => some (.aluImm .add rd rs1 immI)
    | 2 => some (.aluImm .slt rd rs1 immI)
    | 3 => some (.aluImm .sltu rd rs1 immI)
    | 4 => some (.aluImm .xor rd rs1 immI)
    | 6 => some (.aluImm .or rd rs1 immI)
    | 7 => some (.aluImm .and rd rs1 immI)
    | 1 => if f7 == 0 then some (.aluImm .sll rd rs1 (zext (bits w 24 20))) else none
    | 5 =>
      if f7 == 0 then some (.aluImm .srl rd rs1 (zext (bits w 24 20)))
      else if f7 == 0x20 then some (.aluImm .sra rd rs1 (zext (bits w 24 20)))
      else none
    | _ => none
  | 0x33 =>
    let op? : Option AluOp := match f7, f3 with
      | 0, 0 => some .add | 0x20, 0 => some .sub | 0, 1 => some .sll | 0, 2 => some .slt
      | 0, 3 => some .sltu | 0, 4 => some .xor | 0, 5 => some .srl | 0x20, 5 => some .sra
      | 0, 6 => some .or | 0, 7 => some .and
      | 1, 0 => some .mul | 1, 1 => some .mulh | 1, 2 => some .mulhsu | 1, 3 => some .mulhu
      | 1, 4 => some .div | 1, 5 => some .divu | 1, 6 => some .rem | 1, 7 => some .remu
      | _, _ => none
    op?.map fun op => .alu op rd rs1 rs2
  | 0x0F =>
    -- The base ISA says to ignore FENCE's unused fields, but compilers zero
    -- them, so the model accepts only that form and FENCE.TSO, as LLVM does.
    if f3 == 0 && bits w 11 7 == 0 && bits w 19 15 == 0 &&
        (bits w 31 28 == 0 || w == 0x8330000F) then some .fence else none
  | _ => none

/-- The register `x8 + n`, for the compressed forms' 3-bit register fields. -/
def creg (n : Nat) : Fin 32 := regOf (8 + n % 8)

/-- Decodes and expands a 16-bit instruction. -/
def decode16 (h : Nat) : Option Instr :=
  let op := bits h 1 0
  let f3 := bits h 15 13
  let rd := regOf (bits h 11 7)
  let rs2 := regOf (bits h 6 2)
  let rdp := creg (bits h 4 2)
  let rs1p := creg (bits h 9 7)
  let ciImm := bits h 12 12 * 32 + bits h 6 2
  let cjOff := sext 12 (bits h 12 12 * 2048 + bits h 8 8 * 1024 + bits h 10 9 * 256 +
    bits h 6 6 * 128 + bits h 7 7 * 64 + bits h 2 2 * 32 + bits h 11 11 * 16 + bits h 5 3 * 2)
  let cbOff := sext 9 (bits h 12 12 * 256 + bits h 6 5 * 64 + bits h 2 2 * 32 +
    bits h 11 10 * 8 + bits h 4 3 * 2)
  let x0 : Fin 32 := regOf 0
  let x1 : Fin 32 := regOf 1
  let x2 : Fin 32 := regOf 2
  match op, f3 with
  | 0, 0 =>
    let imm := bits h 10 7 * 64 + bits h 12 11 * 16 + bits h 5 5 * 8 + bits h 6 6 * 4
    if imm == 0 then none else some (.aluImm .add rdp x2 (zext imm))
  | 0, 2 =>
    let off := bits h 5 5 * 64 + bits h 12 10 * 8 + bits h 6 6 * 4
    some (.load .lw rdp rs1p (zext off))
  | 0, 6 =>
    let off := bits h 5 5 * 64 + bits h 12 10 * 8 + bits h 6 6 * 4
    some (.store .sw rs1p rdp (zext off))
  | 1, 0 => some (.aluImm .add rd rd (sext 6 ciImm))
  | 1, 1 => some (.jal x1 cjOff)
  | 1, 2 => some (.aluImm .add rd x0 (sext 6 ciImm))
  | 1, 3 =>
    if rd.val == 2 then
      let imm := bits h 12 12 * 512 + bits h 4 3 * 128 + bits h 5 5 * 64 + bits h 2 2 * 32 +
        bits h 6 6 * 16
      if imm == 0 then none else some (.aluImm .add x2 x2 (sext 10 imm))
    else if ciImm == 0 then none
    else some (.lui rd (sext 18 (ciImm * 4096)))
  | 1, 4 =>
    match bits h 11 10 with
    | 0 => if bits h 12 12 == 1 then none else some (.aluImm .srl rs1p rs1p (zext (bits h 6 2)))
    | 1 => if bits h 12 12 == 1 then none else some (.aluImm .sra rs1p rs1p (zext (bits h 6 2)))
    | 2 => some (.aluImm .and rs1p rs1p (sext 6 ciImm))
    | _ =>
      if bits h 12 12 == 1 then none
      else
        let rs2p := creg (bits h 4 2)
        match bits h 6 5 with
        | 0 => some (.alu .sub rs1p rs1p rs2p)
        | 1 => some (.alu .xor rs1p rs1p rs2p)
        | 2 => some (.alu .or rs1p rs1p rs2p)
        | _ => some (.alu .and rs1p rs1p rs2p)
  | 1, 5 => some (.jal x0 cjOff)
  | 1, 6 => some (.branch .beq rs1p x0 cbOff)
  | 1, 7 => some (.branch .bne rs1p x0 cbOff)
  | 2, 0 => if bits h 12 12 == 1 then none else some (.aluImm .sll rd rd (zext (bits h 6 2)))
  | 2, 2 =>
    if rd.val == 0 then none
    else
      let off := bits h 3 2 * 64 + bits h 12 12 * 32 + bits h 6 4 * 4
      some (.load .lw rd x2 (zext off))
  | 2, 4 =>
    if bits h 12 12 == 0 then
      if rs2.val == 0 then (if rd.val == 0 then none else some (.jalr x0 rd 0))
      else some (.alu .add rd x0 rs2)
    else
      if rs2.val == 0 then (if rd.val == 0 then none else some (.jalr x1 rd 0))
      else some (.alu .add rd rd rs2)
  | 2, 6 =>
    let off := bits h 8 7 * 64 + bits h 12 9 * 4
    some (.store .sw x2 rs2 (zext off))
  | _, _ => none

/-- The arithmetic of one ALU operation, with RISC-V's rules for division by
zero and signed overflow. -/
def aluEval (op : AluOp) (a b : Word) : Word :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b.toNat % 32)
  | .slt => if a.slt b then 1 else 0
  | .sltu => if a.ult b then 1 else 0
  | .xor => a ^^^ b
  | .srl => a >>> (b.toNat % 32)
  | .sra => a.sshiftRight (b.toNat % 32)
  | .or => a ||| b
  | .and => a &&& b
  | .mul => a * b
  | .mulh => BitVec.ofInt 32 ((a.toInt * b.toInt) / 2 ^ 32)
  | .mulhsu => BitVec.ofInt 32 ((a.toInt * (b.toNat : Int)) / 2 ^ 32)
  | .mulhu => BitVec.ofNat 32 ((a.toNat * b.toNat) / 2 ^ 32)
  | .div =>
    if b = 0 then BitVec.allOnes 32
    else if a = BitVec.intMin 32 ∧ b = BitVec.allOnes 32 then a
    else BitVec.ofInt 32 (a.toInt.tdiv b.toInt)
  | .divu => if b = 0 then BitVec.allOnes 32 else BitVec.ofNat 32 (a.toNat / b.toNat)
  | .rem =>
    if b = 0 then a
    else if a = BitVec.intMin 32 ∧ b = BitVec.allOnes 32 then 0
    else BitVec.ofInt 32 (a.toInt.tmod b.toInt)
  | .remu => if b = 0 then a else BitVec.ofNat 32 (a.toNat % b.toNat)

def branchTaken (op : BranchOp) (a b : Word) : Bool :=
  match op with
  | .beq => a == b
  | .bne => a != b
  | .blt => a.slt b
  | .bge => !a.slt b
  | .bltu => a.ult b
  | .bgeu => !a.ult b

def loadSize : LoadOp → Nat
  | .lb | .lbu => 1
  | .lh | .lhu => 2
  | .lw => 4

def storeSize : StoreOp → Nat
  | .sb => 1
  | .sh => 2
  | .sw => 4

/-- Whether `a` is a multiple of `size`. A misaligned load or store traps:
the model doesn't let one succeed, so a proof must show none happens. -/
def aligned (size : Nat) (a : Word) : Bool := a.toNat % size == 0

/-- Fetches the instruction at `pc`: 16 bits if its low two bits aren't
`11`, and 32 bits otherwise. -/
def fetch {σ : Type} [Arch σ] (s : σ) : Option (Instr × Word) :=
  let pc := Arch.getPc s
  let lo := (load16 s pc).toNat
  if lo % 4 == 3 then
    (decode32 (load32 s pc).toNat).map (·, 4)
  else (decode16 lo).map (·, 2)

/-- Runs the decoded instruction `i`, `len` bytes long, at the program
counter, or returns `none` if it would trap. -/
def exec {σ : Type} [Arch σ] (s : σ) (i : Instr) (len : Word) : Option σ := do
  let pc := Arch.getPc s
  let next := pc + len
  match i with
  | .lui rd imm => pure (Arch.setPc (writeReg s rd imm) next)
  | .auipc rd imm => pure (Arch.setPc (writeReg s rd (pc + imm)) next)
  | .jal rd off =>
    let target := pc + off
    if target.getLsbD 0 then none
    pure (Arch.setPc (writeReg s rd next) target)
  | .jalr rd rs1 off =>
    let target := (reg s rs1 + off) &&& ~~~1
    pure (Arch.setPc (writeReg s rd next) target)
  | .branch op rs1 rs2 off =>
    pure (Arch.setPc s (if branchTaken op (reg s rs1) (reg s rs2) then pc + off else next))
  | .load op rd rs1 off =>
    let a := reg s rs1 + off
    if !aligned (loadSize op) a then none
    let v : Word := match op with
      | .lb => (load8 s a).signExtend 32
      | .lh => (load16 s a).signExtend 32
      | .lw => load32 s a
      | .lbu => (load8 s a).zeroExtend 32
      | .lhu => (load16 s a).zeroExtend 32
    pure (Arch.setPc (writeReg s rd v) next)
  | .store op rs1 rs2 off =>
    let a := reg s rs1 + off
    if !aligned (storeSize op) a then none
    let v := reg s rs2
    let s' := match op with
      | .sb => store8 s a (v.extractLsb' 0 8)
      | .sh => store16 s a (v.extractLsb' 0 16)
      | .sw => store32 s a v
    pure (Arch.setPc s' next)
  | .aluImm op rd rs1 imm => pure (Arch.setPc (writeReg s rd (aluEval op (reg s rs1) imm)) next)
  | .alu op rd rs1 rs2 =>
    pure (Arch.setPc (writeReg s rd (aluEval op (reg s rs1) (reg s rs2))) next)
  | .fence => pure (Arch.setPc s next)

/-- Runs one instruction, or returns `none` if it would trap. -/
def step {σ : Type} [Arch σ] (s : σ) : Option σ := do
  let (i, len) ← fetch s
  exec s i len

/-- Runs until the program counter reaches `stop`, for at most `fuel`
instructions. -/
def runTo {σ : Type} [Arch σ] (stop : Word) : Nat → σ → Option σ
  | 0, _ => none
  | fuel + 1, s => if Arch.getPc s = stop then some s else (step s).bind (runTo stop fuel)

end C3.RV32
