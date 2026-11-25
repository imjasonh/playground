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

/-- Sign-extend a `BitVec w` to `BitVec 32`. -/
def sext32 {w : Nat} (x : BitVec w) : BitVec 32 := x.signExtend 32

/-- Decode a 16-bit compressed (RVC) instruction. -/
def decodeRVC (h : UInt16) : Instr :=
  let v : BitVec 16 := h.toBitVec
  let op := (v &&& 0x3#16).toNat
  let funct3 := ((v >>> 13) &&& 0x7#16).toNat
  let rdFull : Reg := ⟨((v >>> 7) &&& 0x1F#16).toNat % 32, Nat.mod_lt _ (by decide)⟩
  let rdPrime : Reg := ⟨(8 + ((v >>> 7) &&& 0x7#16).toNat) % 32, Nat.mod_lt _ (by decide)⟩
  let rs2Prime : Reg := ⟨(8 + ((v >>> 2) &&& 0x7#16).toNat) % 32, Nat.mod_lt _ (by decide)⟩
  let rs2Full : Reg := ⟨((v >>> 2) &&& 0x1F#16).toNat % 32, Nat.mod_lt _ (by decide)⟩
  match op, funct3 with
  | 0, 2 => -- c.lw rd', offset(rs1')
    let u5_3 := (v >>> 10) &&& 0x7#16
    let u2 := (v >>> 6) &&& 0x1#16
    let u6 := (v >>> 5) &&& 0x1#16
    let imm := (u6 <<< 6) ||| (u5_3 <<< 3) ||| (u2 <<< 2)
    Instr.lw rs2Prime rdPrime imm.toNat
  | 1, 0 => -- c.addi rd, nzimm
    let i5 := (v >>> 12) &&& 0x1#16
    let i4_0 := (v >>> 2) &&& 0x1F#16
    let imm6 : BitVec 6 := BitVec.ofNat 6 ((i5.toNat <<< 5) ||| i4_0.toNat)
    Instr.addi rdFull rdFull (sext32 imm6)
  | 1, 2 => -- c.li rd, imm
    let i5 := (v >>> 12) &&& 0x1#16
    let i4_0 := (v >>> 2) &&& 0x1F#16
    let imm6 : BitVec 6 := BitVec.ofNat 6 ((i5.toNat <<< 5) ||| i4_0.toNat)
    Instr.addi rdFull ⟨0, by omega⟩ (sext32 imm6)
  | 1, 4 => -- c.srli / c.srai / c.andi / c.sub / c.xor / c.or
    let funct2 := ((v >>> 10) &&& 0x3#16).toNat
    let shamt := (((v >>> 12) &&& 0x1#16).toNat <<< 5) ||| ((v >>> 2) &&& 0x1F#16).toNat
    match funct2 with
    | 0 => Instr.srli rdPrime rdPrime shamt
    | 1 => Instr.srai rdPrime rdPrime shamt
    | 2 =>
      let imm6 : BitVec 6 := BitVec.ofNat 6 shamt
      Instr.andi rdPrime rdPrime (sext32 imm6)
    | 3 =>
      let funct2b := ((v >>> 5) &&& 0x3#16).toNat
      match funct2b with
      | 0 => Instr.sub rdPrime rdPrime rs2Prime
      | 1 => Instr.xor rdPrime rdPrime rs2Prime
      | 2 => Instr.or rdPrime rdPrime rs2Prime
      | _ => Instr.unknown h.toUInt32 2
    | _ => Instr.unknown h.toUInt32 2
  | 1, 5 => -- c.j offset
    let b11 := ((v >>> 12) &&& 0x1#16).toNat
    let b4 := ((v >>> 11) &&& 0x1#16).toNat
    let b9_8 := ((v >>> 9) &&& 0x3#16).toNat
    let b10 := ((v >>> 8) &&& 0x1#16).toNat
    let b6 := ((v >>> 7) &&& 0x1#16).toNat
    let b7 := ((v >>> 6) &&& 0x1#16).toNat
    let b3_1 := ((v >>> 3) &&& 0x7#16).toNat
    let b5 := ((v >>> 2) &&& 0x1#16).toNat
    let imm12 : BitVec 12 := BitVec.ofNat 12
      ((b11 <<< 11) ||| (b10 <<< 10) ||| (b9_8 <<< 8) ||| (b7 <<< 7) |||
       (b6 <<< 6) ||| (b5 <<< 5) ||| (b4 <<< 4) ||| (b3_1 <<< 1))
    Instr.jal ⟨0, by omega⟩ (sext32 imm12)
  | 2, 0 => -- c.slli rd, shamt
    let shamt := (((v >>> 12) &&& 0x1#16).toNat <<< 5) ||| ((v >>> 2) &&& 0x1F#16).toNat
    Instr.slli rdFull rdFull shamt
  | 2, 4 => -- c.jr / c.mv / c.add
    let bit12 := ((v >>> 12) &&& 0x1#16).toNat
    if bit12 == 0 && rs2Full.val == 0 && rdFull.val != 0 then
      Instr.jalr ⟨0, by omega⟩ rdFull 0#32
    else if bit12 == 0 && rs2Full.val != 0 && rdFull.val != 0 then
      Instr.add rdFull ⟨0, by omega⟩ rs2Full
    else if bit12 == 1 && rs2Full.val != 0 && rdFull.val != 0 then
      Instr.add rdFull rdFull rs2Full
    else
      Instr.unknown h.toUInt32 2
  | _, _ => Instr.unknown h.toUInt32 2

/-- Decode a 32-bit RV32I instruction. -/
def decodeRV32 (w : UInt32) : Instr :=
  let v : BitVec 32 := w.toBitVec
  let opcode := (v &&& 0x7F#32).toNat
  let rd : Reg := ⟨((v >>> 7) &&& 0x1F#32).toNat % 32, Nat.mod_lt _ (by decide)⟩
  let funct3 := ((v >>> 12) &&& 0x7#32).toNat
  let rs1 : Reg := ⟨((v >>> 15) &&& 0x1F#32).toNat % 32, Nat.mod_lt _ (by decide)⟩
  let rs2 : Reg := ⟨((v >>> 20) &&& 0x1F#32).toNat % 32, Nat.mod_lt _ (by decide)⟩
  let funct7 := ((v >>> 25) &&& 0x7F#32).toNat
  match opcode with
  | 0x37 => -- lui
    Instr.lui rd (v &&& 0xFFFFF000#32)
  | 0x13 => -- op-imm
    let imm12 : BitVec 12 := BitVec.ofNat 12 ((v >>> 20).toNat)
    match funct3 with
    | 0 => Instr.addi rd rs1 (sext32 imm12)
    | 1 => Instr.slli rd rs1 rs2.val
    | 5 => if funct7 == 0 then Instr.srli rd rs1 rs2.val else Instr.srai rd rs1 rs2.val
    | 7 => Instr.andi rd rs1 (sext32 imm12)
    | _ => Instr.unknown w 4
  | 0x33 => -- op
    match funct3, funct7 with
    | 0, 0x00 => Instr.add rd rs1 rs2
    | 0, 0x20 => Instr.sub rd rs1 rs2
    | 4, 0x00 => Instr.xor rd rs1 rs2
    | 6, 0x00 => Instr.or rd rs1 rs2
    | _, _ => Instr.unknown w 4
  | 0x03 => -- load
    let imm12 : BitVec 12 := BitVec.ofNat 12 ((v >>> 20).toNat)
    match funct3 with
    | 2 => Instr.lw rd rs1 (sext32 imm12)
    | 4 => Instr.lbu rd rs1 (sext32 imm12)
    | _ => Instr.unknown w 4
  | 0x23 => -- store
    let imm12 : BitVec 12 := BitVec.ofNat 12
      ((((v >>> 25) &&& 0x7F#32).toNat <<< 5) ||| ((v >>> 7) &&& 0x1F#32).toNat)
    match funct3 with
    | 0 => Instr.sb rs1 rs2 (sext32 imm12)
    | _ => Instr.unknown w 4
  | 0x63 => -- branch
    let b12 := ((v >>> 31) &&& 0x1#32).toNat
    let b10_5 := ((v >>> 25) &&& 0x3F#32).toNat
    let b4_1 := ((v >>> 8) &&& 0xF#32).toNat
    let b11 := ((v >>> 7) &&& 0x1#32).toNat
    let imm13 : BitVec 13 := BitVec.ofNat 13
      ((b12 <<< 12) ||| (b11 <<< 11) ||| (b10_5 <<< 5) ||| (b4_1 <<< 1))
    match funct3 with
    | 1 => Instr.bne rs1 rs2 (sext32 imm13)
    | 4 => Instr.blt rs1 rs2 (sext32 imm13)
    | 5 => Instr.bge rs1 rs2 (sext32 imm13)
    | _ => Instr.unknown w 4
  | _ => Instr.unknown w 4

/-- Execute one decoded instruction of length `ilen` (2 or 4 bytes).
    Returns `none` on `unknown` instruction or unaligned `lw`. -/
def State.stepInstr (s : State) (instr : Instr) (ilen : BitVec 32) : Option State :=
  let nextPc := s.pc + ilen
  match instr with
  | .lui rd imm => some { s.writeReg rd imm with pc := nextPc }
  | .addi rd rs1 imm => some { s.writeReg rd (s.readReg rs1 + imm) with pc := nextPc }
  | .slli rd rs1 shamt => some { s.writeReg rd (s.readReg rs1 <<< (shamt % 32)) with pc := nextPc }
  | .srli rd rs1 shamt => some { s.writeReg rd (s.readReg rs1 >>> (shamt % 32)) with pc := nextPc }
  | .srai rd rs1 shamt => some { s.writeReg rd (BitVec.sshiftRight (s.readReg rs1) (shamt % 32)) with pc := nextPc }
  | .andi rd rs1 imm => some { s.writeReg rd (s.readReg rs1 &&& imm) with pc := nextPc }
  | .add rd rs1 rs2 => some { s.writeReg rd (s.readReg rs1 + s.readReg rs2) with pc := nextPc }
  | .sub rd rs1 rs2 => some { s.writeReg rd (s.readReg rs1 - s.readReg rs2) with pc := nextPc }
  | .xor rd rs1 rs2 => some { s.writeReg rd (s.readReg rs1 ^^^ s.readReg rs2) with pc := nextPc }
  | .or rd rs1 rs2 => some { s.writeReg rd (s.readReg rs1 ||| s.readReg rs2) with pc := nextPc }
  | .lbu rd rs1 imm =>
    let addr := s.readReg rs1 + imm
    some { s.writeReg rd ((s.mem addr).toBitVec.zeroExtend 32) with pc := nextPc }
  | .lw rd rs1 imm =>
    let addr := s.readReg rs1 + imm
    if (addr &&& 0x3#32) != 0#32 then none
    else
      let b0 := (s.mem addr).toBitVec.zeroExtend 32
      let b1 := (s.mem (addr + 1#32)).toBitVec.zeroExtend 32
      let b2 := (s.mem (addr + 2#32)).toBitVec.zeroExtend 32
      let b3 := (s.mem (addr + 3#32)).toBitVec.zeroExtend 32
      let w := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
      some { s.writeReg rd w with pc := nextPc }
  | .sb rs1 rs2 imm =>
    let addr := s.readReg rs1 + imm
    let byte : UInt8 := UInt8.ofNat ((s.readReg rs2 &&& 0xFF#32).toNat)
    some { s with pc := nextPc, mem := fun a => if a == addr then byte else s.mem a }
  | .bne rs1 rs2 imm =>
    let pc' := if s.readReg rs1 != s.readReg rs2 then s.pc + imm else nextPc
    some { s with pc := pc' }
  | .bge rs1 rs2 imm =>
    let pc' := if BitVec.sle (s.readReg rs2) (s.readReg rs1) then s.pc + imm else nextPc
    some { s with pc := pc' }
  | .blt rs1 rs2 imm =>
    let pc' := if BitVec.slt (s.readReg rs1) (s.readReg rs2) then s.pc + imm else nextPc
    some { s with pc := pc' }
  | .jal rd imm =>
    some { s.writeReg rd nextPc with pc := s.pc + imm }
  | .jalr rd rs1 imm =>
    let target := (s.readReg rs1 + imm) &&& ~~~1#32
    some { s.writeReg rd nextPc with pc := target }
  | .unknown _ _ => none

/-- Decode an entire byte stream into a list of `(Instr, byteLen)` pairs.
    Returns `none` if any instruction is `unknown` or the stream is truncated. -/
def decodeAll (bytes : List UInt8) (off : Nat) : Nat → Option (List (Instr × Nat))
  | 0 => if off == bytes.length then some [] else none
  | fuel + 1 =>
    if off == bytes.length then some []
    else
      match readU16LE bytes off with
      | none => none
      | some h =>
        if (h &&& 0x3) != 0x3 then
          let instr := decodeRVC h
          match instr with
          | .unknown _ _ => none
          | _ =>
            match decodeAll bytes (off + 2) fuel with
            | none => none
            | some rest => some ((instr, 2) :: rest)
        else
          match readU32LE bytes off with
          | none => none
          | some w =>
            let instr := decodeRV32 w
            match instr with
            | .unknown _ _ => none
            | _ =>
              match decodeAll bytes (off + 4) fuel with
              | none => none
              | some rest => some ((instr, 4) :: rest)

end Esp32c3Rom.Rv32imc
