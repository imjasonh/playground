import C3BootProofs.Proofs.MontMul12Main
import C3BootProofs.Proofs.Sha256LoopFrame

/-!
# `ConstMontyForm<p384::FieldParams, 12>::add`

P-384's field addition as compiled: a 12-limb add with carry into a buffer,
a 12-limb `borrowing_sub` of the modulus into a second buffer, and a
constant-time select of the sum when it is below the modulus, else the
difference.
-/

namespace C3.RV32

open C3.Image

set_option exponentiation.threshold 400

section
set_option maxRecDepth 20000

theorem pa3_at_0 : fetchRel p384AddCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF50, 2) := by decide
theorem pa3_at_2 : fetchRel p384AddCode 0x2 = some (.store .sw sp ra 0xAC, 2) := by decide
theorem pa3_at_4 : fetchRel p384AddCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xA8, 2) := by decide
theorem pa3_at_6 : fetchRel p384AddCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xA4, 2) := by decide
theorem pa3_at_8 : fetchRel p384AddCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xA0, 2) := by decide
theorem pa3_at_a : fetchRel p384AddCode 0xA = some (.store .sw sp (19 : Fin 32) 0x9C, 2) := by decide
theorem pa3_at_c : fetchRel p384AddCode 0xC = some (.store .sw sp (20 : Fin 32) 0x98, 2) := by decide
theorem pa3_at_e : fetchRel p384AddCode 0xE = some (.store .sw sp (21 : Fin 32) 0x94, 2) := by decide
theorem pa3_at_10 : fetchRel p384AddCode 0x10 = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem pa3_at_12 : fetchRel p384AddCode 0x12 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem pa3_at_14 : fetchRel p384AddCode 0x14 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem pa3_at_16 : fetchRel p384AddCode 0x16 = some (.alu .add a0 x0 sp, 2) := by decide
theorem pa3_at_18 : fetchRel p384AddCode 0x18 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pa3_at_1c : fetchRel p384AddCode 0x1C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pa3_at_1e : fetchRel p384AddCode 0x1E = some (.alu .add (8 : Fin 32) x0 sp, 2) := by decide
theorem pa3_at_20 : fetchRel p384AddCode 0x20 = some (.auipc ra 0x12000, 4) := by decide
theorem pa3_at_24 : fetchRel p384AddCode 0x24 = some (.jalr ra ra 0x692, 4) := by decide
theorem pa3_at_28 : fetchRel p384AddCode 0x28 = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem pa3_at_2a : fetchRel p384AddCode 0x2A = some (.aluImm .add a0 x0 0xC, 2) := by decide
theorem pa3_at_2c : fetchRel p384AddCode 0x2C = some (.branch .beq a0 x0 0x22, 2) := by decide
theorem pa3_at_2e : fetchRel p384AddCode 0x2E = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem pa3_at_30 : fetchRel p384AddCode 0x30 = some (.load .lw a2 (20 : Fin 32) 0x0, 4) := by decide
theorem pa3_at_34 : fetchRel p384AddCode 0x34 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem pa3_at_36 : fetchRel p384AddCode 0x36 = some (.alu .add (19 : Fin 32) (19 : Fin 32) a1, 2) := by decide
theorem pa3_at_38 : fetchRel p384AddCode 0x38 = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem pa3_at_3a : fetchRel p384AddCode 0x3A = some (.alu .add a2 a2 (19 : Fin 32), 2) := by decide
theorem pa3_at_3c : fetchRel p384AddCode 0x3C = some (.alu .sltu a1 (19 : Fin 32) a1, 4) := by decide
theorem pa3_at_40 : fetchRel p384AddCode 0x40 = some (.alu .sltu (19 : Fin 32) a2 (19 : Fin 32), 4) := by decide
theorem pa3_at_44 : fetchRel p384AddCode 0x44 = some (.store .sw (8 : Fin 32) a2 0x0, 2) := by decide
theorem pa3_at_46 : fetchRel p384AddCode 0x46 = some (.alu .add (19 : Fin 32) (19 : Fin 32) a1, 2) := by decide
theorem pa3_at_48 : fetchRel p384AddCode 0x48 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem pa3_at_4a : fetchRel p384AddCode 0x4A = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem pa3_at_4c : fetchRel p384AddCode 0x4C = some (.branch .bne a0 x0 0xFFFFFFE2, 2) := by decide
theorem pa3_at_4e : fetchRel p384AddCode 0x4E = some (.aluImm .add a0 sp 0x30, 2) := by decide
theorem pa3_at_50 : fetchRel p384AddCode 0x50 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pa3_at_54 : fetchRel p384AddCode 0x54 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pa3_at_56 : fetchRel p384AddCode 0x56 = some (.aluImm .add (20 : Fin 32) sp 0x30, 4) := by decide
theorem pa3_at_5a : fetchRel p384AddCode 0x5A = some (.auipc ra 0x12000, 4) := by decide
theorem pa3_at_5e : fetchRel p384AddCode 0x5E = some (.jalr ra ra 0x658, 4) := by decide
theorem pa3_at_62 : fetchRel p384AddCode 0x62 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem pa3_at_64 : fetchRel p384AddCode 0x64 = some (.alu .add (21 : Fin 32) x0 sp, 2) := by decide
theorem pa3_at_66 : fetchRel p384AddCode 0x66 = some (.lui (8 : Fin 32) 0x3FCC5000, 4) := by decide
theorem pa3_at_6a : fetchRel p384AddCode 0x6A = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFC8C, 4) := by decide
theorem pa3_at_6e : fetchRel p384AddCode 0x6E = some (.aluImm .add (9 : Fin 32) x0 0xC, 2) := by decide
theorem pa3_at_70 : fetchRel p384AddCode 0x70 = some (.branch .beq (9 : Fin 32) x0 0x20, 2) := by decide
theorem pa3_at_72 : fetchRel p384AddCode 0x72 = some (.load .lw a0 (21 : Fin 32) 0x0, 4) := by decide
theorem pa3_at_76 : fetchRel p384AddCode 0x76 = some (.load .lw a1 (8 : Fin 32) 0x0, 2) := by decide
theorem pa3_at_78 : fetchRel p384AddCode 0x78 = some (.auipc ra 0x0, 4) := by decide
theorem pa3_at_7c : fetchRel p384AddCode 0x7C = some (.jalr ra ra 0x174, 4) := by decide
theorem pa3_at_80 : fetchRel p384AddCode 0x80 = some (.alu .add a2 x0 a1, 2) := by decide
theorem pa3_at_82 : fetchRel p384AddCode 0x82 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem pa3_at_84 : fetchRel p384AddCode 0x84 = some (.store .sw (20 : Fin 32) a0 0x0, 4) := by decide
theorem pa3_at_88 : fetchRel p384AddCode 0x88 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem pa3_at_8a : fetchRel p384AddCode 0x8A = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem pa3_at_8c : fetchRel p384AddCode 0x8C = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem pa3_at_8e : fetchRel p384AddCode 0x8E = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem pa3_at_90 : fetchRel p384AddCode 0x90 = some (.store .sw sp (19 : Fin 32) 0x60, 2) := by decide
theorem pa3_at_92 : fetchRel p384AddCode 0x92 = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem pa3_at_94 : fetchRel p384AddCode 0x94 = some (.load .lw a0 sp 0x60, 2) := by decide
theorem pa3_at_96 : fetchRel p384AddCode 0x96 = some (.aluImm .sltu (8 : Fin 32) a0 0x1, 4) := by decide
theorem pa3_at_9a : fetchRel p384AddCode 0x9A = some (.alu .and (8 : Fin 32) (8 : Fin 32) a2, 2) := by decide
theorem pa3_at_9c : fetchRel p384AddCode 0x9C = some (.store .sb sp (8 : Fin 32) 0x60, 4) := by decide
theorem pa3_at_a0 : fetchRel p384AddCode 0xA0 = some (.aluImm .add (9 : Fin 32) sp 0x60, 2) := by decide
theorem pa3_at_a2 : fetchRel p384AddCode 0xA2 = some (.load .lbu a0 sp 0x60, 4) := by decide
theorem pa3_at_a6 : fetchRel p384AddCode 0xA6 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem pa3_at_a8 : fetchRel p384AddCode 0xA8 = some (.alu .and a2 a2 a0, 2) := by decide
theorem pa3_at_aa : fetchRel p384AddCode 0xAA = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem pa3_at_ac : fetchRel p384AddCode 0xAC = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pa3_at_ae : fetchRel p384AddCode 0xAE = some (.auipc ra 0x0, 4) := by decide
theorem pa3_at_b2 : fetchRel p384AddCode 0xB2 = some (.jalr ra ra 0x13E, 4) := by decide
theorem pa3_at_b6 : fetchRel p384AddCode 0xB6 = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem pa3_at_b8 : fetchRel p384AddCode 0xB8 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pa3_at_bc : fetchRel p384AddCode 0xBC = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pa3_at_be : fetchRel p384AddCode 0xBE = some (.auipc ra 0x12000, 4) := by decide
theorem pa3_at_c2 : fetchRel p384AddCode 0xC2 = some (.jalr ra ra 0x5F4, 4) := by decide
theorem pa3_at_c6 : fetchRel p384AddCode 0xC6 = some (.aluImm .add a0 sp 0x30, 2) := by decide
theorem pa3_at_c8 : fetchRel p384AddCode 0xC8 = some (.alu .add a1 x0 sp, 2) := by decide
theorem pa3_at_ca : fetchRel p384AddCode 0xCA = some (.aluImm .add a2 x0 0xC, 2) := by decide
theorem pa3_at_cc : fetchRel p384AddCode 0xCC = some (.aluImm .add a6 sp 0x93, 4) := by decide
theorem pa3_at_d0 : fetchRel p384AddCode 0xD0 = some (.branch .beq a2 x0 0x24, 2) := by decide
theorem pa3_at_d2 : fetchRel p384AddCode 0xD2 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem pa3_at_d4 : fetchRel p384AddCode 0xD4 = some (.store .sb sp (8 : Fin 32) 0x93, 4) := by decide
theorem pa3_at_d8 : fetchRel p384AddCode 0xD8 = some (.load .lw a5 a1 0x0, 2) := by decide
theorem pa3_at_da : fetchRel p384AddCode 0xDA = some (.load .lbu a3 sp 0x93, 4) := by decide
theorem pa3_at_de : fetchRel p384AddCode 0xDE = some (.alu .xor a5 a5 a4, 2) := by decide
theorem pa3_at_e0 : fetchRel p384AddCode 0xE0 = some (.alu .sub a3 x0 a3, 4) := by decide
theorem pa3_at_e4 : fetchRel p384AddCode 0xE4 = some (.alu .and a3 a3 a5, 2) := by decide
theorem pa3_at_e6 : fetchRel p384AddCode 0xE6 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem pa3_at_e8 : fetchRel p384AddCode 0xE8 = some (.alu .xor a3 a3 a4, 2) := by decide
theorem pa3_at_ea : fetchRel p384AddCode 0xEA = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem pa3_at_ec : fetchRel p384AddCode 0xEC = some (.store .sw (9 : Fin 32) a3 0x0, 2) := by decide
theorem pa3_at_ee : fetchRel p384AddCode 0xEE = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem pa3_at_f0 : fetchRel p384AddCode 0xF0 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem pa3_at_f2 : fetchRel p384AddCode 0xF2 = some (.branch .bne a2 x0 0xFFFFFFE0, 2) := by decide
theorem pa3_at_f4 : fetchRel p384AddCode 0xF4 = some (.aluImm .add a1 sp 0x60, 2) := by decide
theorem pa3_at_f6 : fetchRel p384AddCode 0xF6 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pa3_at_fa : fetchRel p384AddCode 0xFA = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem pa3_at_fc : fetchRel p384AddCode 0xFC = some (.auipc ra 0x12000, 4) := by decide
theorem pa3_at_100 : fetchRel p384AddCode 0x100 = some (.jalr ra ra 0x61E, 4) := by decide
theorem pa3_at_104 : fetchRel p384AddCode 0x104 = some (.load .lw ra sp 0xAC, 2) := by decide
theorem pa3_at_106 : fetchRel p384AddCode 0x106 = some (.load .lw (8 : Fin 32) sp 0xA8, 2) := by decide
theorem pa3_at_108 : fetchRel p384AddCode 0x108 = some (.load .lw (9 : Fin 32) sp 0xA4, 2) := by decide
theorem pa3_at_10a : fetchRel p384AddCode 0x10A = some (.load .lw (18 : Fin 32) sp 0xA0, 2) := by decide
theorem pa3_at_10c : fetchRel p384AddCode 0x10C = some (.load .lw (19 : Fin 32) sp 0x9C, 2) := by decide
theorem pa3_at_10e : fetchRel p384AddCode 0x10E = some (.load .lw (20 : Fin 32) sp 0x98, 2) := by decide
theorem pa3_at_110 : fetchRel p384AddCode 0x110 = some (.load .lw (21 : Fin 32) sp 0x94, 2) := by decide
theorem pa3_at_112 : fetchRel p384AddCode 0x112 = some (.aluImm .add sp sp 0xB0, 2) := by decide
theorem pa3_at_114 : fetchRel p384AddCode 0x114 = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- The P-384 modulus. -/
def p384 : Nat := 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1

/-- Where the image stores the modulus. -/
abbrev p3M : Word := BitVec.ofNat 32 p384ModulusAddress

/-- What `add` stores: the sum when it is below `p`, else the sum less `p`
modulo 2^384. -/
def p3AddRes (A B : Nat) : Nat := if A + B < p384 then A + B else (A + B - p384) % 2 ^ 384

theorem p3AddRes_mod {A B : Nat} (hA : A < p384) (hB : B < p384) : p3AddRes A B = (A + B) % p384 := by
  have hp : p384 < 2 ^ 384 := by unfold p384; decide
  unfold p3AddRes
  generalize p384 = p at *
  generalize (2 : Nat) ^ 384 = K at *
  split
  · rw [Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The prologue's argument moves, from 0x10 to 0x20. -/
def p3Pro : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a2, .alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 sp,
   .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0, .alu .add (8 : Fin 32) x0 sp]

def p3AddInit : List BInstr := [.aluImm .add (19 : Fin 32) x0 0x0, .aluImm .add a0 x0 0xC]

/-- One limb of the sum, from 0x2E to 0x4C. -/
def p3AddBody : List BInstr :=
  [.lw a1 (9 : Fin 32) 0x0, .lw a2 (20 : Fin 32) 0x0, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4,
   .alu .add (19 : Fin 32) (19 : Fin 32) a1, .aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4,
   .alu .add a2 a2 (19 : Fin 32), .alu .sltu a1 (19 : Fin 32) a1, .alu .sltu (19 : Fin 32) a2 (19 : Fin 32),
   .sw (8 : Fin 32) a2 0x0, .alu .add (19 : Fin 32) (19 : Fin 32) a1, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4,
   .aluImm .add a0 a0 0xFFFFFFFF]

def p3Mid : List BInstr :=
  [.aluImm .add a0 sp 0x30, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0, .aluImm .add (20 : Fin 32) sp 0x30]

def p3SubInit : List BInstr :=
  [.aluImm .add a2 x0 0x0, .alu .add (21 : Fin 32) x0 sp, .lui (8 : Fin 32) 0x3FCC5000,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFC8C, .aluImm .add (9 : Fin 32) x0 0xC]

def p3SubHead : List BInstr := [.lw a0 (21 : Fin 32) 0x0, .lw a1 (8 : Fin 32) 0x0]

/-- The end of one limb of the difference, from 0x80 to 0x8E. -/
def p3SubTail : List BInstr :=
  [.alu .add a2 x0 a1, .aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, .sw (20 : Fin 32) a0 0x0,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, .aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]

/-- The choice, from 0x90 to 0xAE: 1 when there was no carry and the
subtraction borrowed. -/
def p3Tail : List BInstr :=
  [.sw sp (19 : Fin 32) 0x60, .aluImm .add a0 sp 0x60, .lw a0 sp 0x60, .aluImm .sltu (8 : Fin 32) a0 0x1,
   .alu .and (8 : Fin 32) (8 : Fin 32) a2, .sb sp (8 : Fin 32) 0x60, .aluImm .add (9 : Fin 32) sp 0x60,
   .lbu a0 sp 0x60, .aluImm .add a0 a0 0xFFFFFFFF, .alu .and a2 a2 a0, .alu .add a0 x0 (19 : Fin 32),
   .aluImm .add a1 x0 0x0]

def p3MsetArgs : List BInstr := [.aluImm .add a0 sp 0x60, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0]

def p3SelInit : List BInstr :=
  [.aluImm .add a0 sp 0x30, .alu .add a1 x0 sp, .aluImm .add a2 x0 0xC, .aluImm .add a6 sp 0x93]

/-- One limb of the select, from 0xD2 to 0xF2. -/
def p3SelBody : List BInstr :=
  [.lw a4 a0 0x0, .sb sp (8 : Fin 32) 0x93, .lw a5 a1 0x0, .lbu a3 sp 0x93, .alu .xor a5 a5 a4, .alu .sub a3 x0 a3,
   .alu .and a3 a3 a5, .aluImm .add a0 a0 0x4, .alu .xor a3 a3 a4, .aluImm .add a1 a1 0x4, .sw (9 : Fin 32) a3 0x0,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, .aluImm .add a2 a2 0xFFFFFFFF]

def p3CpyArgs : List BInstr := [.aluImm .add a1 sp 0x60, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (18 : Fin 32)]

/-- The registers `add` saves, at offsets from its `sp`. -/
abbrev p3Ps : List (Fin 32 × Word) :=
  [(ra, 0xAC), ((8 : Fin 32), 0xA8), ((9 : Fin 32), 0xA4), ((18 : Fin 32), 0xA0), ((19 : Fin 32), 0x9C),
   ((20 : Fin 32), 0x98), ((21 : Fin 32), 0x94)]

section
set_option maxRecDepth 20000
theorem p3Save_end : blockEnd p384AddCode 2 (saveBlock p3Ps) = some 0x10 := by decide
theorem p3Pro_end : blockEnd p384AddCode 0x10 p3Pro = some 0x20 := by decide
theorem p3AddInit_end : blockEnd p384AddCode 0x28 p3AddInit = some 0x2C := by decide
theorem p3AddBody_end : blockEnd p384AddCode 0x2E p3AddBody = some 0x4C := by decide
theorem p3Mid_end : blockEnd p384AddCode 0x4E p3Mid = some 0x5A := by decide
theorem p3SubInit_end : blockEnd p384AddCode 0x62 p3SubInit = some 0x70 := by decide
theorem p3SubHead_end : blockEnd p384AddCode 0x72 p3SubHead = some 0x78 := by decide
theorem p3SubTail_end : blockEnd p384AddCode 0x80 p3SubTail = some 0x8E := by decide
theorem p3Tail_end : blockEnd p384AddCode 0x90 p3Tail = some 0xAE := by decide
theorem p3MsetArgs_end : blockEnd p384AddCode 0xB6 p3MsetArgs = some 0xBE := by decide
theorem p3SelInit_end : blockEnd p384AddCode 0xC6 p3SelInit = some 0xD0 := by decide
theorem p3SelBody_end : blockEnd p384AddCode 0xD2 p3SelBody = some 0xF2 := by decide
theorem p3CpyArgs_end : blockEnd p384AddCode 0xF4 p3CpyArgs = some 0xFC := by decide
theorem p3Restore_end : blockEnd p384AddCode 0x104 (restoreBlock p3Ps) = some 0x112 := by decide
end

/-- The registers one limb of the sum leaves alone. -/
def p3AddKeep (q : Fin 32) : Bool := q.val ∉ [0, 8, 9, 10, 11, 12, 19, 20]

set_option maxRecDepth 20000 in
theorem p3AddBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock p3AddBody (M, f)).1 = memStore32 M (f 8 + 0)
      (aluEval .add (memLoad32 M (f 20 + 0)) (aluEval .add (f 19) (memLoad32 M (f 9 + 0)))) ∧
    (runBlock p3AddBody (M, f)).2 19 =
      aluEval .add (aluEval .sltu (aluEval .add (memLoad32 M (f 20 + 0)) (aluEval .add (f 19) (memLoad32 M (f 9 + 0))))
        (aluEval .add (f 19) (memLoad32 M (f 9 + 0))))
        (aluEval .sltu (aluEval .add (f 19) (memLoad32 M (f 9 + 0))) (memLoad32 M (f 9 + 0))) ∧
    (runBlock p3AddBody (M, f)).2 9 = f 9 + 4 ∧ (runBlock p3AddBody (M, f)).2 20 = f 20 + 4 ∧
    (runBlock p3AddBody (M, f)).2 8 = f 8 + 4 ∧ (runBlock p3AddBody (M, f)).2 a0 = f a0 + 0xFFFFFFFF ∧
    ∀ q, p3AddKeep q = true → (runBlock p3AddBody (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, p3AddBody, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 6
  have h0 : q.val ≠ 0 := fun e => absurd (show p3AddKeep q = false by unfold p3AddKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a0) hq rfl,
    pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := 19) hq rfl, pkeep_ne (r := 20) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem p3AddBody_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h9 : (f 9 + 0).toNat % 4 = 0) (h20 : (f 20 + 0).toNat % 4 = 0) (h8 : (f 8 + 0).toNat % 4 = 0)
    (hs : Sep (f 8 + 0) 4 base len) : BlockOk base len p3AddBody (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, p3AddBody, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h9, h20, h8, hs⟩

/-- `c + l` then `r +` that, with the two carries the code adds: the limb and
its carry out. -/
theorem adc_val (l r c : Word) (hc : c.toNat ≤ 1) :
    (aluEval .add r (aluEval .add c l)).toNat +
        2 ^ 32 * (aluEval .add (aluEval .sltu (aluEval .add r (aluEval .add c l)) (aluEval .add c l))
          (aluEval .sltu (aluEval .add c l) l)).toNat = l.toNat + r.toNat + c.toNat ∧
    (aluEval .add (aluEval .sltu (aluEval .add r (aluEval .add c l)) (aluEval .add c l))
      (aluEval .sltu (aluEval .add c l) l)).toNat ≤ 1 := by
  have e1 := add_carry c l
  have e2 := add_carry r (aluEval .add c l)
  have s1 := sltu_le1 (aluEval .add c l) l
  have s2 := sltu_le1 (aluEval .add r (aluEval .add c l)) (aluEval .add c l)
  have hl := l.isLt; have hr := r.isLt
  rw [add_small s2 s1]
  constructor <;> omega

theorem adc_arith {Acc L R X s c c' l r : Nat} (h1 : Acc + X * c = L + R) (h2 : s + 2 ^ 32 * c' = l + r + c) :
    Acc + s * X + X * 2 ^ 32 * c' = L + l * X + (R + r * X) := by
  have e : (s + 2 ^ 32 * c') * X = (l + r + c) * X := by rw [h2]
  simp only [Nat.add_mul] at e
  simp only [Nat.mul_comm, Nat.mul_left_comm] at h1 e ⊢
  omega

/-- **One limb of the sum**, from 0x2E: add limb `i` of both operands and the
carry, and store the limb at `F + 4 i`. -/
theorem p3_add_iter {M : Word → BitVec 8} {P F lp rp c : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x2E (reg n)) (hc : CodeIn M P p384AddCode) (hi : i < 12)
    (hF : F.toNat % 4 = 0) (hlp : lp.toNat % 4 = 0) (hrp : rp.toNat % 4 = 0)
    (sC : Sep (F + BitVec.ofNat 32 (4 * i)) 4 P p384AddCode.length)
    (r9 : reg n 9 = lp + BitVec.ofNat 32 (4 * i)) (r20 : reg n 20 = rp + BitVec.ofNat 32 (4 * i))
    (r8 : reg n 8 = F + BitVec.ofNat 32 (4 * i)) (ra0 : reg n a0 = BitVec.ofNat 32 (12 - i)) (r19 : reg n 19 = c) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (F + BitVec.ofNat 32 (4 * i)) (aluEval .add (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))))))
        P n' (if i + 1 < 12 then 0x2E else 0x4E) (reg n') ∧
      reg n' 19 = aluEval .add (aluEval .sltu (aluEval .add (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))))
        (aluEval .sltu (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))))
          (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))) ∧
      reg n' 9 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 20 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' 8 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, p3AddKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E19, E9, E20, E8, Ea0, Ek⟩ := p3AddBody_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block p3AddBody s hc p3AddBody_end
    (p3AddBody_ok (by rw [r9, add_lit_zero]; exact aligned_add hlp (by omega))
      (by rw [r20, add_lit_zero]; exact aligned_add hrp (by omega))
      (by rw [r8, add_lit_zero]; exact aligned_add hF (by omega)) (by rw [r8, add_lit_zero]; exact sC))
  rw [E1, r8, r9, r20, r19, add_lit_zero, add_lit_zero, add_lit_zero] at u1
  rw [r9, r20, r19, add_lit_zero, add_lit_zero] at E19
  have hc1 := CodeIn.store32 (v := aluEval .add (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
    (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))))) hc sC
  have ea0 : reg n1 a0 = BitVec.ofNat 32 (12 - (i + 1)) := by rw [u1.regs, Ea0, ra0, cnt12_dec i hi]
  have hb : branchTaken .bne (reg n1 a0) (reg n1 x0) = decide (i + 1 < 12) := by
    rw [ea0, u1.self.zero]; exact cnt12_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 19 = aluEval .add (aluEval .sltu (aluEval .add (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))))
        (aluEval .sltu (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))))
          (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))) ∧
      reg n2 9 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 20 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 8 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, p3AddKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E19], by rw [h2, u1.regs, E9, r9, ptr4], by rw [h2, u1.regs, E20, r20, ptr4],
      by rw [h2, u1.regs, E8, r8, ptr4], by rw [h2, ea0], fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 12
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x2E pa3_at_4c (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x4E pa3_at_4c (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The sum**, from limb `i` to the loop's exit at 0x4E: the buffer at `F`
and the carry in `s3` hold the two operands' sum. -/
theorem p3_add_loop {P F lp rp : Word} {M1 : Word → BitVec 8} (hF : F.toNat % 4 = 0)
    (hFw : F.toNat + 0x30 ≤ 2 ^ 32) (hlp : lp.toNat % 4 = 0) (hrp : rp.toNat % 4 = 0)
    (sL : Sep F 0x30 lp 48) (sR : Sep F 0x30 rp 48) (sC : Sep F 0x30 P p384AddCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {c : Word},
      St M P n 0x2E (reg n) → CodeIn M P p384AddCode → (∀ x, Sep F 0x30 x 1 → M x = M1 x) → c.toNat ≤ 1 →
      accV M F i + 2 ^ (32 * i) * c.toNat = accV M1 lp i + accV M1 rp i →
      reg n 9 = lp + BitVec.ofNat 32 (4 * i) → reg n 20 = rp + BitVec.ofNat 32 (4 * i) →
      reg n 8 = F + BitVec.ofNat 32 (4 * i) → reg n a0 = BitVec.ofNat 32 (12 - i) → reg n 19 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x4E (reg n') ∧ CodeIn M' P p384AddCode ∧
        (∀ x, Sep F 0x30 x 1 → M' x = M1 x) ∧ (reg n' 19).toNat ≤ 1 ∧
        accV M' F 12 + 2 ^ (32 * 12) * (reg n' 19).toNat = accV M1 lp 12 + accV M1 rp 12 ∧
        ∀ q, p3AddKeep q = true → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {c : Word},
      St M P n 0x2E (reg n) → CodeIn M P p384AddCode → (∀ x, Sep F 0x30 x 1 → M x = M1 x) → c.toNat ≤ 1 →
      accV M F i + 2 ^ (32 * i) * c.toNat = accV M1 lp i + accV M1 rp i →
      reg n 9 = lp + BitVec.ofNat 32 (4 * i) → reg n 20 = rp + BitVec.ofNat 32 (4 * i) →
      reg n 8 = F + BitVec.ofNat 32 (4 * i) → reg n a0 = BitVec.ofNat 32 (12 - i) → reg n 19 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x2E else 0x4E) (reg n') ∧
        CodeIn M' P p384AddCode ∧ (∀ x, Sep F 0x30 x 1 → M' x = M1 x) ∧ (reg n' 19).toNat ≤ 1 ∧
        accV M' F (i + 1) + 2 ^ (32 * (i + 1)) * (reg n' 19).toNat = accV M1 lp (i + 1) + accV M1 rp (i + 1) ∧
        reg n' 9 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 20 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' 8 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, p3AddKeep q = true → reg n' q = reg n q := by
    intro i hi M n c s hc hfr hcb hv r9 r20 r8 ra0 r19
    have sCi : Sep (F + BitVec.ofNat 32 (4 * i)) 4 P p384AddCode.length := sC.sub (by omega)
    obtain ⟨n1, c1, u1, e19, e9, e20, e8, ea0, fr⟩ := p3_add_iter s hc hi hF hlp hrp sCi r9 r20 r8 ra0 r19
    have eL : memLoad32 M (lp + BitVec.ofNat 32 (4 * i)) = memLoad32 M1 (lp + BitVec.ofNat 32 (4 * i)) :=
      load_frame hfr (sL.subR (by omega))
    have eR : memLoad32 M (rp + BitVec.ofNat 32 (4 * i)) = memLoad32 M1 (rp + BitVec.ofNat 32 (4 * i)) :=
      load_frame hfr (sR.subR (by omega))
    rw [eL, eR] at u1 e19
    obtain ⟨hv1, hc1⟩ := adc_val (memLoad32 M1 (lp + BitVec.ofNat 32 (4 * i)))
      (memLoad32 M1 (rp + BitVec.ofNat 32 (4 * i))) c hcb
    refine ⟨n1, _, c1, u1, hc.store32 sCi, fun x hx => ?_, by rw [e19]; exact hc1, ?_, e9, e20, e8, ea0, fr⟩
    · rw [memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), hfr x hx]
    · rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same, accV_succ1,
        accV_succ1, pow32_succ, e19]
      exact adc_arith hv hv1
  intro m
  induction m with
  | zero =>
    intro i hi M n c s hc hfr hcb hv r9 r20 r8 ra0 r19
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, _, _, _, _, fr⟩ := step 11 (by decide) s hc hfr hcb hv r9 r20 r8 ra0 r19
    exact ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, fr⟩
  | succ m ih =>
    intro i hi M n c s hc hfr hcb hv r9 r20 r8 ra0 r19
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, e9, e20, e8, ea0, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hfr hcb hv r9 r20 r8 ra0 r19
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M'', c', u', hc', hf', hb', hv', fr'⟩ := ih (i + 1) (sel_succ hi) u1 hc1 hf1 hb1 hv1 e9 e20 e8 ea0 rfl
    exact ⟨n', M'', c1.trans c', u', hc', hf', hb', hv', fun q hq => by rw [fr' q hq, fr q hq]⟩


/-- `borrowing_sub`'s offset from `add`. -/
abbrev p3Bsub (P : Word) : Word := P + 0x1EC

set_option maxRecDepth 20000 in
theorem p3SubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock p3SubTail (M, f)).1 = memStore32 M (f (20 : Fin 32) + 0) (f a0) ∧
    (runBlock p3SubTail (M, f)).2 a2 = f a1 ∧
    (runBlock p3SubTail (M, f)).2 (21 : Fin 32) = f (21 : Fin 32) + 4 ∧
    (runBlock p3SubTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 4 ∧
    (runBlock p3SubTail (M, f)).2 (20 : Fin 32) = f (20 : Fin 32) + 4 ∧
    (runBlock p3SubTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) →
      (runBlock p3SubTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, p3SubTail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q2 q9 q23 q19 q8 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q9, q23, q19, q8]

theorem p3SubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (20 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (20 : Fin 32) + 0) 4 base len) :
    BlockOk base len p3SubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, p3SubTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One round of the final subtraction**, from 0x72: subtract limb `i` of
the modulus and the borrow from limb `i` of the accumulator, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem p3_sub_iter {M : Word → BitVec 8} {P F acc np D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x72 (reg n)) (hc : CodeIn M P p384AddCode) (hb : CodeIn M (p3Bsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 12) (hF : F.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (p3Bsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P p384AddCode.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P p384AddCode.length)
    (rsp : reg n sp = F) (r9 : reg n (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * i))
    (r23 : reg n (8 : Fin 32) = np + BitVec.ofNat 32 (4 * i)) (r19 : reg n (20 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (r8 : reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 12 then 0x72 else 0x90) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (20 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
        q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc pa3_at_72 (off' := 0x76) (by decide)
    (by rw [r9, add_lit_zero]; exact aligned_add hacc (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc pa3_at_76 (off' := 0x78) (by decide)
    (by rw [upd_ne (by decide) (by decide), r23, add_lit_zero]; exact aligned_add hnp (by omega))
  rw [r9, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (8 : Fin 32) + 0)) a0 =
      memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (8 : Fin 32) + 0)) a1 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [r23, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0x1EC (by decide))
    pa3_at_78 pa3_at_7c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x78 + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P p384AddCode := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have e19 : reg n3 (20 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block p3SubTail u3 hc3 p3SubTail_end
    (p3SubTail_ok (by rw [e19]; exact aligned_add hD (by omega)) (by rw [e19]; exact sDC))
  obtain ⟨em4, t2, t9, t23, t19, t8, tk⟩ := p3SubTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, e19, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock p3SubTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have e8 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) := by
    rw [g4, t8, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, cnt12_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (9 : Fin 32)) (reg n4 x0) = decide (i + 1 < 12) := by
    rw [e8, u4'.zero]; exact cnt12_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (20 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
        q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, e8], fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => ?_⟩
    · rw [h5, g4, t9, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9, ptr4]
    · rw [h5, g4, t23, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r23, ptr4]
    · rw [h5, g4, t19, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, ptr4]
    · rw [h5, g4, tk q q2 q9 q23 q19 q8, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x72 pa3_at_8e (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x90 pa3_at_8e (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The final subtraction**, from round `i` to its end at 0x90: the
buffer at `D` gets the accumulator minus the modulus, and `a2` the borrow
out as a mask. -/
theorem p3_sub_loop {P F acc np D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hacc : acc.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 48 ≤ 2 ^ 32)
    (sFA : Sep (F + 0xFFFFFFFC) 4 acc 48) (sFN : Sep (F + 0xFFFFFFFC) 4 np 48) (sFD : Sep (F + 0xFFFFFFFC) 4 D 48)
    (sDA : Sep D 48 acc 48) (sDN : Sep D 48 np 48)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (p3Bsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P p384AddCode.length)
    (sDB : Sep D 48 (p3Bsub P) borrowingSubCode.length) (sDC : Sep D 48 P p384AddCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x72 (reg n) → CodeIn M P p384AddCode → CodeIn M (p3Bsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (20 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x90 (reg n') ∧ CodeIn M' P p384AddCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc 12 + 2 ^ (32 * 12) * maskBit (reg n' a2) = accV M0 np 12 + accV M' D 12 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
          q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x72 (reg n) → CodeIn M P p384AddCode → CodeIn M (p3Bsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (20 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x72 else 0x90) (reg n') ∧
        CodeIn M' P p384AddCode ∧ CodeIn M' (p3Bsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 np (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (21 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (20 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
          q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, e9, e23, e19, e8, fr⟩ := p3_sub_iter (i := i) s hc hb hP hi hF hacc hnp hD
      sFB sFC (sDC.sub (by omega)) rsp r9 r23 r19 r8 ra2
    have eA : memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFA.subR (by omega)) (sDA.subR (by omega))
    have eN : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (p3Bsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P p384AddCode := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, e9, e23, e19, e8, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e2]
      exact sub_arith hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, e9, e23, e19, e8, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 e9 e23 e19 e8 rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => by
      rw [fr' q q0 q1 q2 q3 q4 qr q9 q23 q19 q8, fr q q0 q1 q2 q3 q4 qr q9 q23 q19 q8]⟩


/-- The registers one limb of the select leaves alone. -/
def p3SelKeep (q : Fin 32) : Bool := q.val ∉ [0, 9, 10, 11, 12, 13, 14, 15]

set_option maxRecDepth 20000 in
theorem p3SelBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock p3SelBody (M, f)).1 = memStore32 (memStore8 M (f sp + 0x93) ((f 8).extractLsb' 0 8)) (f 9 + 0)
      (aluEval .xor (aluEval .and (aluEval .sub 0
          ((memStore8 M (f sp + 0x93) ((f 8).extractLsb' 0 8) (f sp + 0x93)).zeroExtend 32))
        (aluEval .xor (memLoad32 (memStore8 M (f sp + 0x93) ((f 8).extractLsb' 0 8)) (f a1 + 0))
          (memLoad32 M (f a0 + 0)))) (memLoad32 M (f a0 + 0))) ∧
    (runBlock p3SelBody (M, f)).2 a0 = f a0 + 4 ∧ (runBlock p3SelBody (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock p3SelBody (M, f)).2 9 = f 9 + 4 ∧ (runBlock p3SelBody (M, f)).2 a2 = f a2 + 0xFFFFFFFF ∧
    ∀ q, p3SelKeep q = true → (runBlock p3SelBody (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, p3SelBody, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 5
  have h0 : q.val ≠ 0 := fun e => absurd (show p3SelKeep q = false by unfold p3SelKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
    pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl, pkeep_ne (r := a4) hq rfl, pkeep_ne (r := a5) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem p3SelBody_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (ha0 : (f a0 + 0).toNat % 4 = 0) (ha1 : (f a1 + 0).toNat % 4 = 0) (h9 : (f 9 + 0).toNat % 4 = 0)
    (hb : Sep (f sp + 0x93) 1 base len) (hs : Sep (f 9 + 0) 4 base len) : BlockOk base len p3SelBody (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, p3SelBody, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨ha0, hb, ha1, h9, hs⟩

theorem p3sel_eq (d s c : Word) (hc : c = 0 ∨ c = 1) :
    aluEval .xor (aluEval .and (aluEval .sub 0 c) (aluEval .xor s d)) d = if c = 1 then s else d := by
  rw [← selWord_eq d s c hc]
  unfold selWord
  show (0 - c) &&& (s ^^^ d) ^^^ d = d ^^^ ((s ^^^ d) &&& (0 - c))
  rw [BitVec.xor_comm, BitVec.and_comm]

theorem slot93 (F : Word) : F + 0x60 + BitVec.ofNat 32 0x33 = F + 0x93 := by rw [BitVec.add_assoc]; rfl

/-- **One limb of the select**, from 0xD2: store limb `i` of the sum or of
the difference to the buffer at `F + 0x60`. -/
theorem p3_sel_iter {M : Word → BitVec 8} {P F c : Word} {n : Machine} {i : Nat}
    (s : St M P n 0xD2 (reg n)) (hc : CodeIn M P p384AddCode) (hi : i < 12) (hcc : c = 0 ∨ c = 1)
    (hF : F.toNat % 4 = 0)
    (sC1 : Sep (F + 0x93) 1 P p384AddCode.length)
    (sC2 : Sep (F + 0x60 + BitVec.ofNat 32 (4 * i)) 4 P p384AddCode.length)
    (rsp : reg n sp = F) (ra0 : reg n a0 = F + 0x30 + BitVec.ofNat 32 (4 * i))
    (ra1 : reg n a1 = F + BitVec.ofNat 32 (4 * i)) (r9 : reg n 9 = F + 0x60 + BitVec.ofNat 32 (4 * i))
    (ra2 : reg n a2 = BitVec.ofNat 32 (12 - i)) (r8 : reg n 8 = c) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore8 M (F + 0x93) (c.extractLsb' 0 8)) (F + 0x60 + BitVec.ofNat 32 (4 * i))
          (if c = 1 then memLoad32 M (F + BitVec.ofNat 32 (4 * i))
            else memLoad32 M (F + 0x30 + BitVec.ofNat 32 (4 * i))))
        P n' (if i + 1 < 12 then 0xD2 else 0xF4) (reg n') ∧
      reg n' a0 = F + 0x30 + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a1 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' 9 = F + 0x60 + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, p3SelKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨E1, Ea0, Ea1, E9, Ea2, Ek⟩ := p3SelBody_run (M := M) (f := reg n)
  have hF30 : (F + 0x30).toNat % 4 = 0 := aligned_add hF (k := 0x30) (by decide)
  have hF60 : (F + 0x60).toNat % 4 = 0 := aligned_add hF (k := 0x60) (by decide)
  obtain ⟨n1, c1, u1⟩ := St.block p3SelBody s hc p3SelBody_end
    (p3SelBody_ok (by rw [ra0, add_lit_zero]; exact aligned_add hF30 (by omega))
      (by rw [ra1, add_lit_zero]; exact aligned_add hF (by omega))
      (by rw [r9, add_lit_zero]; exact aligned_add hF60 (by omega)) (by rw [rsp]; exact sC1)
      (by rw [r9, add_lit_zero]; exact sC2))
  have sb : Sep (F + 0x93) 1 (F + BitVec.ofNat 32 (4 * i)) 4 :=
    sep_offsets (c := 0x93) (n := 1) (d := 4 * i) (k := 4) F (.inr (by omega)) (by decide) (by omega)
  rw [E1, rsp, r8, r9, ra0, ra1, add_lit_zero, add_lit_zero, add_lit_zero, choice_byte M _ c hcc,
    memLoad32_store8_sep sb, p3sel_eq _ _ c hcc] at u1
  have hc1 := CodeIn.store32 (v := if c = 1 then memLoad32 M (F + BitVec.ofNat 32 (4 * i))
    else memLoad32 M (F + 0x30 + BitVec.ofNat 32 (4 * i))) (CodeIn.store8 (v := c.extractLsb' 0 8) hc sC1) sC2
  have ea2 : reg n1 a2 = BitVec.ofNat 32 (12 - (i + 1)) := by rw [u1.regs, Ea2, ra2, cnt12_dec i hi]
  have hb : branchTaken .bne (reg n1 a2) (reg n1 x0) = decide (i + 1 < 12) := by
    rw [ea2, u1.self.zero]; exact cnt12_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a0 = F + 0x30 + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a1 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 9 = F + 0x60 + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a2 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, p3SelKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, Ea0, ra0, ptr4], by rw [h2, u1.regs, Ea1, ra1, ptr4],
      by rw [h2, u1.regs, E9, r9, ptr4], by rw [h2, ea2], fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 12
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0xD2 pa3_at_f2 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0xF4 pa3_at_f2 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- What one limb of the select does to memory. -/
theorem p3_sel_mem {M MB : Word → BitVec 8} {F c : Word} {v : BitVec 8} {i : Nat} (hi : i < 12)
    (hw : F.toNat + 0xB0 ≤ 2 ^ 32)
    (hfr : ∀ x, Sep (F + 0x60) 0x34 x 1 → M x = MB x)
    (hwd : ∀ j, j < i → memLoad32 M (F + 0x60 + BitVec.ofNat 32 (4 * j)) =
      if c = 1 then memLoad32 MB (F + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (F + 0x30 + BitVec.ofNat 32 (4 * j))) :
    (∀ x, Sep (F + 0x60) 0x34 x 1 → memStore32 (memStore8 M (F + 0x93) v) (F + 0x60 + BitVec.ofNat 32 (4 * i))
      (if c = 1 then memLoad32 M (F + BitVec.ofNat 32 (4 * i)) else memLoad32 M (F + 0x30 + BitVec.ofNat 32 (4 * i))) x =
        MB x) ∧
    ∀ j, j < i + 1 → memLoad32 (memStore32 (memStore8 M (F + 0x93) v) (F + 0x60 + BitVec.ofNat 32 (4 * i))
      (if c = 1 then memLoad32 M (F + BitVec.ofNat 32 (4 * i)) else memLoad32 M (F + 0x30 + BitVec.ofNat 32 (4 * i))))
        (F + 0x60 + BitVec.ofNat 32 (4 * j)) =
      if c = 1 then memLoad32 MB (F + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (F + 0x30 + BitVec.ofNat 32 (4 * j)) := by
  have h60 : (F + 0x60).toNat + 0x34 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (0x60 : Word).toNat = 0x60 := rfl; rw [this]; omega
  have sS : ∀ j, j < 12 → Sep (F + 0x60) 0x34 (F + BitVec.ofNat 32 (4 * j)) 4 := fun j hj => by
    have := sep_offsets F (c := 0x60) (n := 0x34) (d := 4 * j) (k := 4) (.inr (by omega)) (by omega) (by omega)
    exact this
  have sD : ∀ j, j < 12 → Sep (F + 0x60) 0x34 (F + 0x30 + BitVec.ofNat 32 (4 * j)) 4 := fun j hj => by
    have := sep_offsets F (c := 0x60) (n := 0x34) (d := 0x30 + 4 * j) (k := 4) (.inr (by omega)) (by omega) (by omega)
    rwa [← add_ofNat_assoc] at this
  refine ⟨fun x hx => ?_, fun j hj => ?_⟩
  · have h8 : x ≠ F + 0x93 := fun e => by
      have := hx.point (i := 0x33) (j := 0) (by decide) (by decide)
      rw [slot93, add_ofNat_zero] at this; exact this e.symm
    rw [memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), memStore8_ne h8, hfr x hx]
  · by_cases hji : j = i
    · subst hji
      rw [memLoad32_store32_same, load_frame hfr (sS j hi), load_frame hfr (sD j hi)]
    · rw [memLoad32_store32_sep (sep_offsets (F + 0x60) (c := 4 * i) (n := 4) (d := 4 * j) (k := 4) (by omega)
          (by omega) (by omega)), memLoad32_store8_sep (by
          rw [← slot93]; exact sep_offsets (F + 0x60) (c := 0x33) (n := 1) (d := 4 * j) (k := 4) (.inr (by omega))
            (by omega) (by omega)), hwd j (by omega)]

/-- **The select loop**, from limb `i` to its exit at 0xF4. -/
theorem p3_sel_loop {P F c : Word} {MB : Word → BitVec 8} (hcc : c = 0 ∨ c = 1) (hF : F.toNat % 4 = 0)
    (hw : F.toNat + 0xB0 ≤ 2 ^ 32) (sC : Sep (F + 0x60) 0x34 P p384AddCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M P n 0xD2 (reg n) → CodeIn M P p384AddCode →
      (∀ x, Sep (F + 0x60) 0x34 x 1 → M x = MB x) →
      (∀ j, j < i → memLoad32 M (F + 0x60 + BitVec.ofNat 32 (4 * j)) =
        if c = 1 then memLoad32 MB (F + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (F + 0x30 + BitVec.ofNat 32 (4 * j))) →
      reg n sp = F → reg n a0 = F + 0x30 + BitVec.ofNat 32 (4 * i) → reg n a1 = F + BitVec.ofNat 32 (4 * i) →
      reg n 9 = F + 0x60 + BitVec.ofNat 32 (4 * i) → reg n a2 = BitVec.ofNat 32 (12 - i) → reg n 8 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' 0xF4 (reg n') ∧ CodeIn M' P p384AddCode ∧
        (∀ x, Sep (F + 0x60) 0x34 x 1 → M' x = MB x) ∧
        (∀ j, j < 12 → memLoad32 M' (F + 0x60 + BitVec.ofNat 32 (4 * j)) =
          if c = 1 then memLoad32 MB (F + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (F + 0x30 + BitVec.ofNat 32 (4 * j))) ∧
        ∀ q, p3SelKeep q = true → reg n' q = reg n q := by
  have h60 : (F + 0x60).toNat + 0x34 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (0x60 : Word).toNat = 0x60 := rfl; rw [this]; omega
  have hb93 : ∀ {b : Word} {len : Nat}, Sep (F + 0x60) 0x34 b len → Sep (F + 0x93) 1 b len := fun h => by
    rw [← slot93]; exact h.sub (by decide)
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M P n 0xD2 (reg n) → CodeIn M P p384AddCode →
      (∀ x, Sep (F + 0x60) 0x34 x 1 → M x = MB x) →
      (∀ j, j < i → memLoad32 M (F + 0x60 + BitVec.ofNat 32 (4 * j)) =
        if c = 1 then memLoad32 MB (F + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (F + 0x30 + BitVec.ofNat 32 (4 * j))) →
      reg n sp = F → reg n a0 = F + 0x30 + BitVec.ofNat 32 (4 * i) → reg n a1 = F + BitVec.ofNat 32 (4 * i) →
      reg n 9 = F + 0x60 + BitVec.ofNat 32 (4 * i) → reg n a2 = BitVec.ofNat 32 (12 - i) → reg n 8 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0xD2 else 0xF4) (reg n') ∧ CodeIn M' P p384AddCode ∧
        (∀ x, Sep (F + 0x60) 0x34 x 1 → M' x = MB x) ∧
        (∀ j, j < i + 1 → memLoad32 M' (F + 0x60 + BitVec.ofNat 32 (4 * j)) =
          if c = 1 then memLoad32 MB (F + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (F + 0x30 + BitVec.ofNat 32 (4 * j))) ∧
        reg n' a0 = F + 0x30 + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a1 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' 9 = F + 0x60 + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, p3SelKeep q = true → reg n' q = reg n q := by
    intro i hi M n s hc hfr hwd rsp ra0 ra1 r9 ra2 r8
    obtain ⟨n1, c1, u1, ea0, ea1, e9, ea2, fr⟩ := p3_sel_iter (i := i) s hc hi hcc hF (hb93 sC)
      (sC.sub (by omega)) rsp ra0 ra1 r9 ra2 r8
    obtain ⟨m1, m2⟩ := p3_sel_mem (v := c.extractLsb' 0 8) hi hw hfr hwd
    exact ⟨n1, _, c1, u1, CodeIn.store32 (CodeIn.store8 hc (hb93 sC)) (sC.sub (by omega)), m1, m2, ea0, ea1, e9,
      ea2, fr⟩
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hwd rsp ra0 ra1 r9 ra2 r8
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hf1, hw1, _, _, _, _, fr⟩ := step 11 (by decide) s hc hfr hwd rsp ra0 ra1 r9 ra2 r8
    exact ⟨n1, M1, c1, u1, hc1, hf1, hw1, fr⟩
  | succ m ih =>
    intro i hi M n s hc hfr hwd rsp ra0 ra1 r9 ra2 r8
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, hw1, ea0, ea1, e9, ea2, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hfr hwd rsp ra0 ra1 r9 ra2 r8
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hw', fr'⟩ := ih (i + 1) (sel_succ hi) u1 hc1 hf1 hw1
      (by rw [fr sp rfl, rsp]) ea0 ea1 e9 ea2 (by rw [fr 8 rfl, r8])
    exact ⟨n', M', c1.trans c', u', hc', hf', hw', fun q hq => by rw [fr' q hq, fr q hq]⟩

set_option maxRecDepth 20000 in
/-- The modulus the image stores is `p384`. -/
theorem p3M_val {M : Word → BitVec 8} (h : CodeIn M p3M p384ModulusData) : accV M p3M 12 = p384 := by
  have he : ∀ i : Fin 12, (byteAt p384ModulusData (4 * i.val + 3) ++ byteAt p384ModulusData (4 * i.val + 2) ++
      byteAt p384ModulusData (4 * i.val + 1) ++ byteAt p384ModulusData (4 * i.val)) =
      BitVec.ofNat 32 ((p384 / 2 ^ (32 * i.val)) % 2 ^ 32) := by decide +kernel
  have hw : ∀ i, i < 12 → memLoad32 M (p3M + BitVec.ofNat 32 (4 * i)) =
      BitVec.ofNat 32 ((p384 / 2 ^ (32 * i)) % 2 ^ 32) := fun i hi => by
    rw [← he ⟨i, hi⟩]
    unfold memLoad32
    have hl : p384ModulusData.length = 48 := rfl
    have b0 := h (4 * i) (by omega)
    have b1 : M (p3M + BitVec.ofNat 32 (4 * i) + 1) = byteAt p384ModulusData (4 * i + 1) := by
      rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    have b2 : M (p3M + BitVec.ofNat 32 (4 * i) + 2) = byteAt p384ModulusData (4 * i + 2) := by
      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    have b3 : M (p3M + BitVec.ofNat 32 (4 * i) + 3) = byteAt p384ModulusData (4 * i + 3) := by
      rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    rw [b3, b2, b1, b0]
  simp only [accV]
  rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide),
    hw 6 (by decide), hw 7 (by decide), hw 8 (by decide), hw 9 (by decide), hw 10 (by decide), hw 11 (by decide)]
  decide

/-- The words a select stores add up to the chosen buffer's value. -/
theorem accV_sel {Mo MS MD : Word → BitVec 8} {o s d c : Word}
    (h : ∀ j, j < 12 → memLoad32 Mo (o + BitVec.ofNat 32 (4 * j)) =
      if c = 1 then memLoad32 MS (s + BitVec.ofNat 32 (4 * j)) else memLoad32 MD (d + BitVec.ofNat 32 (4 * j))) :
    accV Mo o 12 = if c = 1 then accV MS s 12 else accV MD d 12 := by
  by_cases hc : c = 1
  · rw [ite_eq_left hc]; exact accV_congr2 12 fun j hj => by rw [h j hj, ite_eq_left hc]
  · rw [ite_eq_right hc]; exact accV_congr2 12 fun j hj => by rw [h j hj, ite_eq_right hc]

/-- The select's outcome is `p3AddRes`: the sum when there was no carry and
the subtraction of `p` borrowed, else the difference. -/
theorem p3_final {S D A B c mb : Nat} (hD : D < 2 ^ 384) (hc : c ≤ 1) (hmb : mb ≤ 1)
    (hsum : S + 2 ^ 384 * c = A + B) (hsub : S + 2 ^ 384 * mb = p384 + D) :
    (if c = 0 ∧ mb = 1 then S else D) = p3AddRes A B := by
  have hp : p384 < 2 ^ 384 := by unfold p384; decide
  unfold p3AddRes
  generalize p384 = p at *
  generalize (2 : Nat) ^ 384 = K at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hmb with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero] at hsum hsub
    rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hsum hsub
    rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left (by omega)]; omega
  · simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hsum hsub
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [show A + B - p = D + K by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hD]
  · simp only [Nat.mul_one] at hsum hsub
    rw [ite_eq_right (by omega), ite_eq_right (by omega), show A + B - p = D by omega, Nat.mod_eq_of_lt hD]

/-- Where `add` runs: its code and its callees' at their offsets from an even
`P`, the modulus where the image keeps it, the 0xB4 bytes of stack below
`sp0` that it and `borrowing_sub` use, the 12-word result at `out`, and the
operands at `lp` and `rp`, all apart where they must be. -/
structure P3Env (M : Word → BitVec 8) (P sp0 out lp rp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384AddCode
  mset : CodeIn M (P + 0x126B2) memsetCode
  bsub : CodeIn M (p3Bsub P) borrowingSubCode
  stub : CodeIn M (P + 0x1271A) memcpyStubCode
  body : CodeIn M (P + 0x12722) memcpyBodyCode
  pmod : CodeIn M p3M p384ModulusData
  hsp : sp0.toNat % 4 = 0
  hS : 0xB4 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hlp : lp.toNat % 4 = 0
  hrp : rp.toNat % 4 = 0
  hwo : out.toNat + 48 < 2 ^ 32
  sSC : Sep (sp0 + 0xFFFFFF4C) 0xB4 P p384AddCode.length
  sSM : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0x126B2) memsetCode.length
  sSB : Sep (sp0 + 0xFFFFFF4C) 0xB4 (p3Bsub P) borrowingSubCode.length
  sSU : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0x1271A) memcpyStubCode.length
  sSY : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0x12722) memcpyBodyCode.length
  sSP : Sep (sp0 + 0xFFFFFF4C) 0xB4 p3M 48
  sOC : Sep out 48 P p384AddCode.length
  sOY : Sep out 48 (P + 0x12722) memcpyBodyCode.length
  sOS : Sep out 48 (sp0 + 0xFFFFFF4C) 0xB4
  sLS : Sep lp 48 (sp0 + 0xFFFFFF4C) 0xB4
  sRS : Sep rp 48 (sp0 + 0xFFFFFF4C) 0xB4

/-- The registers `add` never writes. -/
def p3Keep (q : Fin 32) : Bool := q.val ∈ [3, 4, 7, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

theorem p3G_F (sp0 : Word) : sp0 + 0xFFFFFF4C + BitVec.ofNat 32 4 = sp0 + 0xFFFFFF50 := by
  rw [BitVec.add_assoc]; rfl

theorem p3F_G (sp0 : Word) : sp0 + 0xFFFFFF50 + 0xFFFFFFFC = sp0 + 0xFFFFFF4C := by
  rw [BitVec.add_assoc]; rfl

theorem p3G_w (sp0 : Word) (h : 0xB4 ≤ sp0.toNat) : (sp0 + 0xFFFFFF4C).toNat + 0xB4 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFF4C : Word).toNat = 4294967116 := rfl
  have := sp0.isLt
  omega

/-- A range in the frame `F = G + 4` is in the region at `G`. -/
theorem p3inF {sp0 x : Word} {c l : Nat} (h : c + l ≤ 0xB0) (hx : Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1) :
    Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) l x 1 := by
  rw [← p3G_F, add_ofNat_assoc]; exact hx.sub (by omega)

theorem p3inF' {sp0 b : Word} {c l k : Nat} (h : c + l ≤ 0xB0) (hx : Sep (sp0 + 0xFFFFFF4C) 0xB4 b k) :
    Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) l b k := by
  rw [← p3G_F, add_ofNat_assoc]; exact hx.sub (by omega)

set_option maxRecDepth 20000 in
theorem p3Ps_range : ∀ p ∈ p3Ps, p.2.toNat % 4 = 0 ∧ 0x94 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0xB0 := by decide

set_option maxRecDepth 20000 in
theorem p3Ps_sp : ∀ p ∈ p3Ps, p.1 ≠ sp := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `add`'s prologue, from entry to the sum loop at 0x2E. -/
theorem p3_pro (m : Machine) {P sp0 out lp rp : Word} (env : P3Env m.mem P sp0 out lp rp) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = lp) (ha2 : reg m a2 = rp) (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x2E (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ p3Ps → memLoad32 M (sp0 + 0xFFFFFF50 + o) = reg m r) ∧
      reg n sp = sp0 + 0xFFFFFF50 ∧ reg n 9 = lp + BitVec.ofNat 32 (4 * 0) ∧
      reg n 20 = rp + BitVec.ofNat 32 (4 * 0) ∧ reg n 8 = sp0 + 0xFFFFFF50 + BitVec.ofNat 32 (4 * 0) ∧
      reg n a0 = BitVec.ofNat 32 (12 - 0) ∧ reg n 19 = 0 ∧ reg n 18 = out ∧
      ∀ q, p3Keep q = true → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGw := p3G_w sp0 env.hS
  have hFa : (sp0 + 0xFFFFFF50).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF50) (by decide)
  have hFw : (sp0 + 0xFFFFFF50).toNat + 0xB0 ≤ 2 ^ 32 := by
    rw [← p3G_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sFC : Sep (sp0 + 0xFFFFFF50) 0xB0 P p384AddCode.length := by
    have := p3inF' (c := 0) (l := 0xB0) (by decide) env.sSC; rwa [add_ofNat_zero] at this
  have fF : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep (sp0 + 0xFFFFFF50) 0xB0 x 1 := fun x hx => by
    have := p3inF (c := 0) (l := 0xB0) (by decide) hx; rwa [add_ofNat_zero] at this
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code pa3_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF50) sp = sp0 + 0xFFFFFF50 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock p3Ps) u1 env.code p3Save_end (saveBlock_ok _ p3Ps _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (p3Ps_range p hp).1, frm_sep' sFC (by have := p3Ps_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (sp0 + 0xFFFFFF50)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF50)) p3Ps = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside p3Ps fun p hp => frm_sep' (fF x hx) (by have := p3Ps_range p hp; omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF4C) 0xB4 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have k2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q hq => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, hq]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFF50 := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block p3Pro u2.self (cIn env.code env.sSC frSv) p3Pro_end
    (by simp [BlockOk, BInstr.ok, p3Pro])
  simp only [runBlock, BInstr.run, p3Pro] at u3
  have g3 : ∀ q, reg m3 q = _ := u3.regs
  obtain ⟨m4, c4, u4, a04, k4⟩ := St.memsetW (B := P + 0x126B2) (w := 12) (dst := sp0 + 0xFFFFFF50)
    (even_at P env.hP 0x126B2 (by decide)) u3.self (cIn env.code env.sSC frSv) (cIn env.mset env.sSM frSv)
    pa3_at_20 pa3_at_24 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x20 + 8) (by decide))
    (by decide) (by omega) (by decide) hFa
    (by have := p3inF' (c := 0) (l := 4 * 12) (by decide) env.sSM; rwa [add_ofNat_zero] at this)
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact BitVec.zero_add _)
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval])
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords Msv (sp0 + 0xFFFFFF50) 0 12 = Mz := ⟨_, rfl⟩
  rw [hMz] at u4
  have frZ : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Mz x = m.mem x := fun x hx => by
    have h48 : Sep (sp0 + 0xFFFFFF50) (4 * 12) x 1 := by
      have := p3inF (c := 0) (l := 4 * 12) (by decide) hx; rwa [add_ofNat_zero] at this
    rw [← hMz, fillWords_outside 12 h48, frSv x hx]
  have cZ := cIn env.code env.sSC frZ
  obtain ⟨m5, c5, u5⟩ := St.block p3AddInit u4 cZ p3AddInit_end (by simp [BlockOk, BInstr.ok, p3AddInit])
  simp only [runBlock, BInstr.run, p3AddInit] at u5
  have x10 : reg m5 a0 = 0xC := by rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨m6, d6, u6⟩ := u5.self.notTaken cZ 0x2E pa3_at_2c (by decide) (by rw [x10, u5.self.zero]; decide)
  have k5 : ∀ q, q ≠ a0 → q ≠ (19 : Fin 32) → reg m6 q = reg m4 q := fun q h1 h2 => by
    rw [u6.regs, u5.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, u4.zero]
    · simp [upd, h0, h1, h2]
  have k3 : ∀ q, q.val ≠ 0 → q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ a0 → q ≠ a2 →
      q ≠ a1 → q ≠ (8 : Fin 32) → reg m3 q = reg m2 q := fun q h0 h20 h9 h18 h10 h12 h11 h8 => by
    rw [g3]; simp only [upd_app, h0, h20, h9, h18, h10, h12, h11, h8, ite_false]
  refine ⟨m6, Mz, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.single d6))))), u6.self, frZ, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro r o h
    obtain ⟨_, ho1, ho2⟩ := p3Ps_range (r, o) h
    dsimp only at ho1 ho2
    have hs : Sep (sp0 + 0xFFFFFF50) (4 * 12) (sp0 + 0xFFFFFF50 + o) 4 := by
      have := sep_offsets (sp0 + 0xFFFFFF50) (c := 0) (n := 4 * 12) (d := o.toNat) (k := 4) (.inl (by omega))
        (by decide) (by omega)
      rwa [add_ofNat_zero, ofNat_toNat_self] at this
    rw [← hMz, fillWords_load_sep hs, ← hMsv]
    simp only [p3Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  · rw [k5 sp (by decide) (by decide), k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a1 (by decide), ha1]; exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a2 (by decide), ha2]; exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [sp2]; exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [u6.regs, x10]; rfl
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [u4.zero]; rfl
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a0 (by decide), ha0]; exact BitVec.zero_add _
  · intro q hq
    have k := fun r (hr : p3Keep r = false) => pkeep_ne hq hr
    rw [k5 q (k a0 rfl) (k 19 rfl), k4 q (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k ra rfl),
      k3 q (fun e => k 0 rfl (Fin.ext e)) (k 20 rfl) (k 9 rfl) (k 18 rfl) (k a0 rfl) (k a2 rfl) (k a1 rfl) (k 8 rfl),
      k2 q (k sp rfl)]

/-- The registers from the sum loop's exit to the subtraction loop leave alone. -/
def p3MidKeep (q : Fin 32) : Bool := q.val ∉ [0, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 21]

theorem p3M_lit : (0x3FCC5000 : Word) + 0xFFFFFC8C = p3M := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the sum loop's exit at 0x4E to the subtraction loop at 0x72: zero the
difference buffer at `F + 0x30` and point at the sum and the modulus. -/
theorem p3_mid {M : Word → BitVec 8} {P F : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x4E (reg n)) (hc : CodeIn M P p384AddCode) (hms : CodeIn M (P + 0x126B2) memsetCode)
    (hF : F.toNat % 4 = 0) (hFw : F.toNat + 0xB0 ≤ 2 ^ 32)
    (sM : Sep (F + BitVec.ofNat 32 0x30) (4 * 12) (P + 0x126B2) memsetCode.length)
    (sC : Sep (F + BitVec.ofNat 32 0x30) (4 * 12) P p384AddCode.length) (rsp : reg n sp = F) :
    ∃ n', Steps n n' ∧ St (fillWords M (F + BitVec.ofNat 32 0x30) 0 12) P n' 0x72 (reg n') ∧
      reg n' sp = F ∧ reg n' 21 = F + BitVec.ofNat 32 (4 * 0) ∧ reg n' 8 = p3M + BitVec.ofNat 32 (4 * 0) ∧
      reg n' 20 = F + BitVec.ofNat 32 0x30 + BitVec.ofNat 32 (4 * 0) ∧ reg n' 9 = BitVec.ofNat 32 (12 - 0) ∧
      reg n' a2 = 0 ∧
      ∀ q, p3MidKeep q = true → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block p3Mid s hc p3Mid_end (by simp [BlockOk, BInstr.ok, p3Mid])
  simp only [runBlock, BInstr.run, p3Mid] at u1
  obtain ⟨n2, c2, u2, a02, k2⟩ := St.memsetW (B := P + 0x126B2) (w := 12) (dst := F + BitVec.ofNat 32 0x30)
    (even_at P hP 0x126B2 (by decide)) u1.self hc hms pa3_at_5a pa3_at_5e
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x5A + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (aligned_add hF (by decide)) sM
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  have hc2 : CodeIn (fillWords M (F + BitVec.ofNat 32 0x30) 0 12) P p384AddCode := fun i hi => by
    rw [fillWords_outside 12 (sC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  obtain ⟨n3, c3, u3⟩ := St.block p3SubInit u2 hc2 p3SubInit_end (by simp [BlockOk, BInstr.ok, p3SubInit])
  simp only [runBlock, BInstr.run, p3SubInit] at u3
  have z2 : reg n2 0 = 0 := u2.zero
  have x9 : reg n3 9 = 0xC := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc2 0x72 pa3_at_70 (by decide) (by rw [x9, u3.self.zero]; decide)
  have k1 : ∀ q, p3MidKeep q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl]
  have k3 : ∀ q, p3MidKeep q = true → reg n4 q = reg n2 q := fun q hq => by
    rw [u4.regs, u3.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl,
      upd_kp hq rfl rfl]
  have sp2 : reg n2 sp = F := by
    rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k1 sp rfl, rsp]
  refine ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), u4.self, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [k3 sp rfl, sp2]
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]
    exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u1.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; exact (add_ofNat_zero _).symm
  · rw [u4.regs, x9]; rfl
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [z2]; rfl
  · rw [k3 q hq, k2 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl), k1 q hq]

/-- The choice the code makes from the top carry `c` and the borrow mask `b`. -/
theorem p3_choice (c b : Word) (hc : c.toNat ≤ 1) (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    aluEval .and (aluEval .sltu c 1) b = (if c.toNat = 0 ∧ maskBit b = 1 then 1 else 0) := by
  have hc' : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  rcases hc' with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem p3_choice01 (c b : Word) (hc : c.toNat ≤ 1) (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    aluEval .and (aluEval .sltu c 1) b = 0 ∨ aluEval .and (aluEval .sltu c 1) b = 1 := by
  rw [p3_choice c b hc hb]; split <;> simp

/-- The registers from the subtraction loop's exit to the select loop leave alone. -/
def p3TailKeep (q : Fin 32) : Bool := q.val ∉ [0, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the subtraction loop's exit at 0x90 to the select loop at 0xD2: the
choice through a byte of the frame, a `borrowing_sub` whose result goes
unused, and the zeroed output buffer at `F + 0x60`. -/
theorem p3_tail {M : Word → BitVec 8} {P F c b : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x90 (reg n)) (hc : CodeIn M P p384AddCode) (hms : CodeIn M (P + 0x126B2) memsetCode)
    (hbs : CodeIn M (p3Bsub P) borrowingSubCode)
    (hF : F.toNat % 4 = 0) (hFw : F.toNat + 0xB0 ≤ 2 ^ 32)
    (sC : Sep (F + 0xFFFFFFFC) 0xB4 P p384AddCode.length)
    (sM : Sep (F + 0xFFFFFFFC) 0xB4 (P + 0x126B2) memsetCode.length)
    (sB : Sep (F + 0xFFFFFFFC) 0xB4 (p3Bsub P) borrowingSubCode.length)
    (rsp : reg n sp = F) (r19 : reg n 19 = c) (ra2 : reg n a2 = b) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0xD2 (reg n') ∧
      (∀ x, Sep (F + BitVec.ofNat 32 0x60) 0x34 x 1 → Sep (F + 0xFFFFFFFC) 4 x 1 → M' x = M x) ∧
      reg n' sp = F ∧ reg n' a0 = F + BitVec.ofNat 32 0x30 + BitVec.ofNat 32 (4 * 0) ∧
      reg n' a1 = F + BitVec.ofNat 32 (4 * 0) ∧ reg n' 9 = F + BitVec.ofNat 32 0x60 + BitVec.ofNat 32 (4 * 0) ∧
      reg n' a2 = BitVec.ofNat 32 (12 - 0) ∧ reg n' 8 = aluEval .and (aluEval .sltu c 1) b ∧
      ∀ q, p3TailKeep q = true → reg n' q = reg n q := by
  have frm4 : F + 0xFFFFFFFC + BitVec.ofNat 32 4 = F := by
    rw [BitVec.add_assoc, show (0xFFFFFFFC : Word) + BitVec.ofNat 32 4 = 0 from rfl]; exact add_lit_zero F
  have sCF : Sep F 0xB0 P p384AddCode.length := by
    have := sC.sub (c := 4) (l := 0xB0) (by decide); rwa [frm4] at this
  have a60 : (F + 0x60).toNat % 4 = 0 := fr_al hF (by decide)
  have s60 : Sep (F + 0x60) 4 P p384AddCode.length := frm_sep sCF (by decide)
  have s60' : Sep (F + 0x60) 1 P p384AddCode.length := by
    have := s60.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨n1, c1, u1⟩ := St.block p3Tail s hc p3Tail_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, p3Tail, upd_app, ↓reduceIte, and_true, true_and]
    rw [rsp]; exact ⟨⟨a60, s60⟩, a60, s60'⟩)
  simp +decide only [runBlock, BInstr.run, p3Tail, upd_app, ↓reduceIte] at u1
  rw [rsp, r19, memLoad32_store32_same, ra2] at u1
  obtain ⟨Mt0, hMt0⟩ : ∃ Mt0, memStore8 (memStore32 M (F + 96) c) (F + 96)
      (BitVec.extractLsb' 0 8 (aluEval AluOp.and (aluEval AluOp.sltu c 1) b)) = Mt0 := ⟨_, rfl⟩
  rw [hMt0] at u1
  have s1of4 : ∀ {a b : Word} {k : Nat}, Sep a 4 b k → Sep a 1 b k := fun h => by
    have := h.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  have code0 : ∀ {base : Word} {code : List Nat}, CodeIn M base code → Sep (F + 0x60) 4 base code.length →
      CodeIn Mt0 base code := fun h hs => by
    rw [← hMt0]; exact (h.store32 hs).store8 (s1of4 hs)
  have frm4' : ∀ {b : Word} {k : Nat}, Sep (F + 0xFFFFFFFC) 0xB4 b k → Sep (F + 0x60) 4 b k := fun h => by
    have := h.sub (c := 0x64) (l := 4) (by decide)
    rwa [BitVec.add_assoc, show (0xFFFFFFFC : Word) + BitVec.ofNat 32 0x64 = 0x60 from rfl] at this
  have hb1 : CodeIn Mt0 (p3Bsub P) borrowingSubCode := code0 hbs (frm4' sB)
  have hc1 : CodeIn Mt0 P p384AddCode := code0 hc (frm4' sC)
  have hm1 : CodeIn Mt0 (P + 0x126B2) memsetCode := code0 hms (frm4' sM)
  have r1 : ∀ q, p3TailKeep q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; repeat rw [upd_kp hq rfl rfl]
  have sp1 : reg n1 sp = F := (r1 sp rfl).trans rsp
  have x8 : reg n1 8 = aluEval .and (aluEval .sltu c 1) b := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
  have x9 : reg n1 9 = F + BitVec.ofNat 32 0x60 := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rfl
  obtain ⟨n2, c2, u2, _, _, sp2, fr2, mem2⟩ := u1.self.bsubCall hc1 hb1 (even_at P hP 0x1EC (by decide))
    pa3_at_ae pa3_at_b2 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0xAE + 8) (by decide))
    sp1 hF (by have := sB.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  have inG4 : ∀ (b : Word) (code : List Nat), CodeIn Mt0 b code → Sep (F + 0xFFFFFFFC) 0xB4 b code.length →
      CodeIn n2.mem b code := fun b code h hs i hi => by
    have h4 : Sep (F + 0xFFFFFFFC) 4 b code.length := by
      have := hs.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [mem2 _ (h4.subR (c := i) (l := 1) (by omega))]; exact h i hi
  have hc2 := inG4 _ _ hc1 sC
  obtain ⟨n3, c3, u3⟩ := St.block p3MsetArgs u2 hc2 p3MsetArgs_end (by simp [BlockOk, BInstr.ok, p3MsetArgs])
  simp only [runBlock, BInstr.run, p3MsetArgs] at u3
  have s60M : Sep (F + BitVec.ofNat 32 0x60) (4 * 12) (P + 0x126B2) memsetCode.length := by
    have := sM.sub (c := 0x64) (l := 4 * 12) (by decide)
    rwa [BitVec.add_assoc, show (0xFFFFFFFC : Word) + BitVec.ofNat 32 0x64 = BitVec.ofNat 32 0x60 from rfl] at this
  have s60C : Sep (F + BitVec.ofNat 32 0x60) (4 * 12) P p384AddCode.length := by
    have := sC.sub (c := 0x64) (l := 4 * 12) (by decide)
    rwa [BitVec.add_assoc, show (0xFFFFFFFC : Word) + BitVec.ofNat 32 0x64 = BitVec.ofNat 32 0x60 from rfl] at this
  obtain ⟨n4, c4, u4, a04, k4⟩ := St.memsetW (B := P + 0x126B2) (w := 12) (dst := F + BitVec.ofNat 32 0x60)
    (even_at P hP 0x126B2 (by decide)) u3.self hc2 (inG4 _ _ hm1 sM) pa3_at_be pa3_at_c2
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0xBE + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (aligned_add hF (by decide)) s60M
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  have hc4 : CodeIn (fillWords n2.mem (F + BitVec.ofNat 32 0x60) 0 12) P p384AddCode := fun i hi => by
    rw [fillWords_outside 12 (s60C.subR (c := i) (l := 1) (by omega))]; exact hc2 i hi
  obtain ⟨n5, c5, u5⟩ := St.block p3SelInit u4 hc4 p3SelInit_end (by simp [BlockOk, BInstr.ok, p3SelInit])
  simp only [runBlock, BInstr.run, p3SelInit] at u5
  have x12 : reg n5 a2 = 0xC := by rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc4 0xD2 pa3_at_d0 (by decide) (by rw [x12, u5.self.zero]; decide)
  have k3 : ∀ q, p3TailKeep q = true → reg n3 q = reg n2 q := fun q hq => by
    rw [u3.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl]
  have k2' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n2 q = reg n1 q := fr2
  have sp4 : reg n4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k3 sp rfl, sp2]
  refine ⟨n6, _, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (.single d6))))), u6.self, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x hx hG
    have h48 : Sep (F + BitVec.ofNat 32 0x60) (4 * 12) x 1 := by
      have := hx.sub (c := 0) (l := 4 * 12) (by decide); rwa [add_ofNat_zero] at this
    have h4 : Sep (F + 96) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have hne : x ≠ F + 96 := fun e => by
      have := hx.point (i := 0) (j := 0) (by decide) (by decide)
      rw [add_ofNat_zero, add_ofNat_zero] at this; exact this e.symm
    rw [fillWords_outside 12 h48, mem2 x hG, ← hMt0, memStore8_ne hne, memStore32_get_sep h4]
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp4
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp4]
    exact (add_ofNat_zero _).symm
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp4]
    exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]
    rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x9]
    exact (add_ofNat_zero _).symm
  · rw [u6.regs, x12]; rfl
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]
    rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x8]
  · intro q hq
    rw [u6.regs, u5.regs]
    repeat rw [upd_kp hq rfl rfl]
    rw [k4 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl), k3 q hq, fr2 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl) (pkeep_ne hq rfl), r1 q hq]

theorem p3G_60 (sp0 : Word) : sp0 + 0xFFFFFF4C + BitVec.ofNat 32 0x64 = sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x60 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `add`'s epilogue, from 0xF4: copy the result out, restore the saved
registers, and return. -/
theorem p3_epi {P sp0 out lp rp : Word} {M0 Mx : Word → BitVec 8} {n : Machine} {v : Fin 32 → Word}
    (env : P3Env M0 P sp0 out lp rp) (s : St Mx P n 0xF4 (reg n))
    (hfr : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Mx x = M0 x)
    (hsl : ∀ r o, (r, o) ∈ p3Ps → memLoad32 Mx (sp0 + 0xFFFFFF50 + o) = v r)
    (rsp : reg n sp = sp0 + 0xFFFFFF50) (r18 : reg n 18 = out) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧
      n'.mem = copyWords Mx out (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x60) 12 ∧
      reg n' sp = sp0 ∧ (∀ r o, (r, o) ∈ p3Ps → reg n' r = v r) ∧
      ∀ q, p3Keep q = true → reg n' q = reg n q := by
  have hGw := p3G_w sp0 env.hS
  have hFa : (sp0 + 0xFFFFFF50).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF50) (by decide)
  have cX : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → Sep (sp0 + 0xFFFFFF4C) 0xB4 b code.length →
      CodeIn Mx b code := fun hc hs i hi => by
    rw [hfr _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hc := cX env.code env.sSC
  obtain ⟨n1, c1, u1⟩ := St.block p3CpyArgs s hc p3CpyArgs_end (by simp [BlockOk, BInstr.ok, p3CpyArgs])
  simp only [runBlock, BInstr.run, p3CpyArgs] at u1
  have e8 : P + 0x1271A + 8 = P + 0x12722 := by rw [BitVec.add_assoc]; rfl
  have sO60 : Sep out 48 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x60) 48 := by
    have := env.sOS.subR (c := 0x64) (l := 48) (by decide); rwa [p3G_60] at this
  obtain ⟨n2, c2, u2, a02, k2⟩ := St.memcpyW (B := P + 0x1271A) (w := 12) (dst := out)
    (src := sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x60) (even_at P env.hP 0x1271A (by decide)) u1.self hc
    (cX env.stub env.sSU) (by rw [e8]; exact cX env.body env.sSY) pa3_at_fc pa3_at_100
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0xFC + 8) (by decide))
    (by decide) env.hwo (by decide) env.hout (aligned_add hFa (by decide)) sO60 (by rw [e8]; exact env.sOY)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r18]; exact BitVec.zero_add _)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  obtain ⟨Mc, hMc⟩ : ∃ Mc, copyWords Mx out (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x60) 12 = Mc := ⟨_, rfl⟩
  rw [hMc] at u2
  have hc2 : CodeIn Mc P p384AddCode := fun i hi => by
    rw [← hMc, copyWords_outside 12 (env.sOC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have k1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n1 q = reg n q := fun q h0 h1 h2 => by
    rw [u1.regs]
    by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, s.zero]
    · simp [upd, hq, h0, h1, h2]
  have sp2 : reg n2 sp = sp0 + 0xFFFFFF50 := by
    rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k1 sp (by decide) (by decide) (by decide), rsp]
  obtain ⟨n3, c3, u3⟩ := St.block (restoreBlock p3Ps) u2 hc2 p3Restore_end
    (restoreBlock_ok Mc _ p3Ps (reg n2) sp2 p3Ps_sp fun p hp => fr_al' hFa (p3Ps_range p hp).1)
  simp only [restoreBlock_run Mc _ p3Ps (reg n2) sp2 p3Ps_sp] at u3
  have slot : ∀ r o, (r, o) ∈ p3Ps → memLoad32 Mc (sp0 + 0xFFFFFF50 + o) = v r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := p3Ps_range (r, o) h
    dsimp only at ho1 ho2
    have hs : Sep out 48 (sp0 + 0xFFFFFF50 + o) 4 := by
      have := env.sOS.subR (c := 4 + o.toNat) (l := 4) (by omega)
      rwa [← add_ofNat_assoc, p3G_F, ofNat_toNat_self] at this
    rw [← hMc, copyWords_load_sep (k := 12) hs, hsl r o h]
  have rsp3 : restoreRegs Mc (sp0 + 0xFFFFFF50) (reg n2) p3Ps sp = sp0 + 0xFFFFFF50 := by
    rw [restoreRegs_sp _ _ _ _ p3Ps_sp]; exact sp2
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc2 pa3_at_112 (off' := 0x114) (by decide)
  obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.jalr hc2 pa3_at_114
  refine ⟨n5, c1.trans (c2.trans (c3.trans (.cons d4 (.single d5)))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc5]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, slot ra 0xAC (by decide)]
  · rw [mem5, ← hMc]
  · rw [regs5]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp3, BitVec.add_assoc]
    exact BitVec.add_zero _
  · intro r o h
    rw [regs5]
    simp only [p3Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slot _ _ (by decide)
  · intro q hq
    rw [regs5, upd_kp hq rfl rfl]
    simp only [restoreRegs]
    repeat rw [upd_kp hq rfl rfl]
    rw [k2 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl),
      k1 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)]

theorem p3Keep_add : ∀ q, p3Keep q = true → p3AddKeep q = true := by decide
theorem p3Keep_mid : ∀ q, p3Keep q = true → p3MidKeep q = true := by decide
theorem p3Keep_tail : ∀ q, p3Keep q = true → p3TailKeep q = true := by decide
theorem p3Keep_sel : ∀ q, p3Keep q = true → p3SelKeep q = true := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `ConstMontyForm<p384::FieldParams, 12>::add`**, called with
the result at `out` and 12-limb operands `A` at `lp` and `B` at `rp`. It
stores `p3AddRes A B`, which is `(A + B) mod p` for operands below `p`
(`p3AddRes_mod`). It returns with `sp` and every register but `a0` through
`a7`, `t0`, and `t1` as they were, and changes no memory outside the 0xB4
bytes of stack below `sp` and the result. -/
theorem p384Add_correct (m : Machine) {P sp0 out lp rp retAddr : Word}
    (env : P3Env m.mem P sp0 out lp rp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = lp)
    (ha2 : reg m a2 = rp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem out 12) = p3AddRes (limbVal (wordsAt m.mem lp 12)) (limbVal (wordsAt m.mem rp 12)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  have hGw := p3G_w sp0 env.hS
  have hFa : (sp0 + 0xFFFFFF50).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF50) (by decide)
  have hFw : (sp0 + 0xFFFFFF50).toNat + 0xB0 ≤ 2 ^ 32 := by
    rw [← p3G_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have toF : ∀ {b : Word} {k : Nat} {c l : Nat}, c + l ≤ 0xB0 → Sep (sp0 + 0xFFFFFF4C) 0xB4 b k →
      Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) l b k := fun h hs => p3inF' h hs
  have toF0 : ∀ (b : Word) (k l : Nat), l ≤ 0xB0 → Sep (sp0 + 0xFFFFFF4C) 0xB4 b k →
      Sep (sp0 + 0xFFFFFF50) l b k := fun b k l h hs => by
    have := p3inF' (c := 0) (l := l) (by omega) hs; rwa [add_ofNat_zero] at this
  have toG : ∀ {b : Word} {k : Nat}, Sep (sp0 + 0xFFFFFF4C) 0xB4 b k → Sep (sp0 + 0xFFFFFF50 + 0xFFFFFFFC) 0xB4 b k :=
    fun h => by rw [p3F_G]; exact h
  have toG4 : ∀ {b : Word} {k : Nat}, Sep (sp0 + 0xFFFFFF4C) 0xB4 b k → Sep (sp0 + 0xFFFFFF50 + 0xFFFFFFFC) 4 b k :=
    fun h => by
      rw [p3F_G]; have := h.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have cOf : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF4C) 0xB4 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  -- the prologue
  obtain ⟨n1, M1, c1, s1, fr1, hsl, sp1, r9, r20, r8, ra0, r19, r18, k1⟩ := p3_pro m env hpc ha0 ha1 ha2 hsp
  -- the sum
  obtain ⟨n2, M2, c2, s2, cM2, fr2, hc2, hv2, k2⟩ := p3_add_loop (M1 := M1) hFa (by omega) env.hlp env.hrp
    (toF0 _ _ _ (by decide) env.sLS.symm) (toF0 _ _ _ (by decide) env.sRS.symm) (toF0 _ _ _ (by decide) env.sSC) 11 0 rfl (M := M1) (n := n1) (c := 0) s1
    (cOf env.code env.sSC fr1) (fun _ _ => rfl) (Nat.zero_le 1) (by simp [accV]) r9 r20 r8 ra0 r19
  have frM2 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M2 x = m.mem x := fun x hx => by
    rw [fr2 x (toF0 _ _ _ (by decide) hx), fr1 x hx]
  have sp2 : reg n2 sp = sp0 + 0xFFFFFF50 := by rw [k2 sp rfl, sp1]
  -- zero the difference buffer
  obtain ⟨n3, c3, s3, sp3, r21_3, r8_3, r20_3, r9_3, ra2_3, k3⟩ := p3_mid env.hP s2 cM2
    (cOf env.mset env.sSM frM2) hFa hFw (toF (by decide) env.sSM) (toF (by decide) env.sSC) sp2
  obtain ⟨M3, hM3⟩ : ∃ M3, fillWords M2 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x30) 0 12 = M3 := ⟨_, rfl⟩
  rw [hM3] at s3
  have frM3 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, fillWords_outside 12 (p3inF (by decide) hx), frM2 x hx]
  -- the difference
  have hD : (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x30).toNat % 4 = 0 := aligned_add hFa (by decide)
  have sDF : Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x30) 48 (sp0 + 0xFFFFFF50) 48 := by
    have := sep_offsets (sp0 + 0xFFFFFF50) (c := 0x30) (n := 48) (d := 0) (k := 48) (.inr (by decide)) (by decide)
      (by decide)
    rwa [add_ofNat_zero] at this
  obtain ⟨n4, M4, c4, s4, cM4, fr4, hb4, hv4, sp4, k4⟩ := p3_sub_loop (M0 := M3) env.hP hFa hFa
    (show p3M.toNat % 4 = 0 by decide) hD (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by rw [p3F_G]; have := sep_offsets (sp0 + 0xFFFFFF4C) (c := 0) (n := 4) (d := 4) (k := 48) (.inl (by decide))
          (by decide) (by decide)
        rwa [add_ofNat_zero, p3G_F] at this)
    (toG4 env.sSP)
    (by rw [p3F_G]; have := sep_offsets (sp0 + 0xFFFFFF4C) (c := 0) (n := 4) (d := 0x34) (k := 48) (.inl (by decide))
          (by decide) (by decide)
        rwa [add_ofNat_zero, show sp0 + 0xFFFFFF4C + BitVec.ofNat 32 0x34 = sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x30 by
          rw [BitVec.add_assoc, BitVec.add_assoc]; rfl] at this)
    sDF (toF (by decide) env.sSP) (toG4 env.sSB) (toG4 env.sSC) (toF (by decide) env.sSB) (toF (by decide) env.sSC)
    11 0 rfl s3 (cOf env.code env.sSC frM3) (cOf env.bsub env.sSB frM3) (fun _ _ _ => rfl) (.inl rfl)
    (by simp [accV, maskBit]) sp3 r21_3 r8_3 r20_3 r9_3 ra2_3
  have inD : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x30) 48 x 1 :=
    fun x hx => p3inF (by decide) hx
  have inG4x : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep (sp0 + 0xFFFFFF50 + 0xFFFFFFFC) 4 x 1 :=
    fun x hx => toG4 hx
  have frM4 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M4 x = m.mem x := fun x hx => by
    rw [fr4 x (inG4x x hx) (inD x hx), frM3 x hx]
  have r19_4 : reg n4 19 = reg n2 19 := by
    rw [k4 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k3 19 rfl]
  -- the choice and the zeroed output buffer
  obtain ⟨n5, M5, c5, s5, fr5, sp5, ra0_5, ra1_5, r9_5, ra2_5, r8_5, k5⟩ := p3_tail (c := reg n2 19)
    (b := reg n4 a2) env.hP s4 cM4 (cOf env.mset env.sSM frM4) (cOf env.bsub env.sSB frM4) hFa hFw (toG env.sSC)
    (toG env.sSM) (toG env.sSB) sp4 r19_4 rfl
  have in60 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x60) 0x34 x 1 :=
    fun x hx => p3inF (by decide) hx
  have frM5 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M5 x = m.mem x := fun x hx => by
    rw [fr5 x (in60 x hx) (inG4x x hx), frM4 x hx]
  have hcc := p3_choice01 (reg n2 19) (reg n4 a2) hc2 hb4
  -- the select
  obtain ⟨n6, M6, c6, s6, cM6, fr6, hw6, k6⟩ := p3_sel_loop (MB := M5) hcc hFa hFw (toF (by decide) env.sSC)
    11 0 rfl s5 (cOf env.code env.sSC frM5) (fun _ _ => rfl) (fun j hj => absurd hj (Nat.not_lt_zero _)) sp5
    ra0_5 ra1_5 r9_5 ra2_5 r8_5
  have frM6 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M6 x = m.mem x := fun x hx => by
    rw [fr6 x (in60 x hx), frM5 x hx]
  -- the saved registers are where the prologue put them
  have hsl6 : ∀ r o, (r, o) ∈ p3Ps → memLoad32 M6 (sp0 + 0xFFFFFF50 + o) = reg m r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := p3Ps_range (r, o) h
    dsimp only at ho1 ho2
    have e : sp0 + 0xFFFFFF50 + o = sp0 + 0xFFFFFF50 + BitVec.ofNat 32 o.toNat := by rw [ofNat_toNat_self]
    have sF : ∀ c l, c + l ≤ o.toNat → Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) l (sp0 + 0xFFFFFF50 + o) 4 :=
      fun c l hcl => by rw [e]; exact sep_offsets _ (.inl hcl) (by omega) (by omega)
    have sG : Sep (sp0 + 0xFFFFFF50 + 0xFFFFFFFC) 4 (sp0 + 0xFFFFFF50 + o) 4 := by
      rw [p3F_G, e, ← p3G_F, add_ofNat_assoc]
      have := sep_offsets (sp0 + 0xFFFFFF4C) (c := 0) (n := 4) (d := 4 + o.toNat) (k := 4) (.inl (by omega))
        (by decide) (by omega)
      rwa [add_ofNat_zero] at this
    have s0F : Sep (sp0 + 0xFFFFFF50) 0x30 (sp0 + 0xFFFFFF50 + o) 4 := by
      have := sF 0 0x30 (by omega); rwa [add_ofNat_zero] at this
    rw [load_frame fr6 (sF 0x60 0x34 (by omega)), load_frame2 fr5 (sF 0x60 0x34 (by omega)) sG,
      load_frame2 fr4 sG (sF 0x30 48 (by omega)), ← hM3,
      fillWords_load_sep (sF 0x30 (4 * 12) (by omega)), load_frame fr2 s0F, hsl r o h]
  have r18_6 : reg n6 18 = out := by
    rw [k6 18 rfl, k5 18 rfl, k4 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), k3 18 rfl, k2 18 rfl, r18]
  have sp6 : reg n6 sp = sp0 + 0xFFFFFF50 := by rw [k6 sp rfl, sp5]
  -- the epilogue
  obtain ⟨n7, c7, pc7, mem7, sp7, sv7, k7⟩ := p3_epi (v := reg m) env s6 frM6 hsl6 sp6 r18_6
  refine ⟨n7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))), by rw [pc7, hra, hret], sp7, ?_,
    ?_, ?_⟩
  · intro q q10 q11 q12 q13 q14 q15 q16 q17 q5 q6
    have cat := (by decide : ∀ q : Fin 32, q = 0 ∨ q = sp ∨ q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
      q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ p3Keep q = true ∨
      q = a0 ∨ q = a1 ∨ q = a2 ∨ q = a3 ∨ q = a4 ∨ q = a5 ∨ q = a6 ∨ q = a7 ∨ q = t0 ∨ q = t1) q
    rcases cat with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; rfl
    · subst h; rw [sp7, hsp]
    · subst h; exact sv7 _ 0xAC (by decide)
    · subst h; exact sv7 _ 0xA8 (by decide)
    · subst h; exact sv7 _ 0xA4 (by decide)
    · subst h; exact sv7 _ 0xA0 (by decide)
    · subst h; exact sv7 _ 0x9C (by decide)
    · subst h; exact sv7 _ 0x98 (by decide)
    · subst h; exact sv7 _ 0x94 (by decide)
    · have kq := fun r (hr : p3Keep r = false) => pkeep_ne h hr
      rw [k7 q h, k6 q (p3Keep_sel q h), k5 q (p3Keep_tail q h), k4 q (kq a0 rfl) (kq a1 rfl) (kq a2 rfl)
        (kq a3 rfl) (kq a4 rfl) (kq ra rfl) (kq 21 rfl) (kq 8 rfl) (kq 20 rfl) (kq 9 rfl), k3 q (p3Keep_mid q h),
        k2 q (p3Keep_add q h), k1 q h]
    · exact absurd h q10
    · exact absurd h q11
    · exact absurd h q12
    · exact absurd h q13
    · exact absurd h q14
    · exact absurd h q15
    · exact absurd h q16
    · exact absurd h q17
    · exact absurd h q5
    · exact absurd h q6
  · have hwo := env.hwo
    have eOut : limbVal (wordsAt n7.mem out 12) = accV M6 (sp0 + 0xFFFFFF50 + 0x60) 12 := by
      rw [limbVal_wordsAt, mem7]
      exact accV_congr2 12 fun j hj => copyWords_load 12 j hj (by omega)
    have sGw : ∀ c, c + 4 ≤ 0xB0 → Sep (sp0 + 0xFFFFFF50 + 0xFFFFFFFC) 4 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) 4 :=
      fun c hc => by
        rw [p3F_G, ← p3G_F, add_ofNat_assoc]
        have := sep_offsets (sp0 + 0xFFFFFF4C) (c := 0) (n := 4) (d := 4 + c) (k := 4) (.inl (by omega))
          (by decide) (by omega)
        rwa [add_ofNat_zero] at this
    have sFw : ∀ a n c, a + n ≤ 0xB0 → c + 4 ≤ 0xB0 → (a + n ≤ c ∨ c + 4 ≤ a) →
        Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 a) n (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) 4 :=
      fun a n c h1 h2 h3 => sep_offsets _ h3 (by omega) (by omega)
    have agS : accV M5 (sp0 + 0xFFFFFF50) 12 = accV M2 (sp0 + 0xFFFFFF50) 12 := accV_congr 12 fun j hj => by
      rw [load_frame2 fr5 (sFw 0x60 0x34 (4 * j) (by decide) (by omega) (.inr (by omega))) (sGw (4 * j) (by omega)),
        load_frame2 fr4 (sGw (4 * j) (by omega)) (sFw 0x30 48 (4 * j) (by decide) (by omega) (.inr (by omega))),
        ← hM3, fillWords_load_sep (sFw 0x30 (4 * 12) (4 * j) (by decide) (by omega) (.inr (by omega)))]
    have agD : accV M5 (sp0 + 0xFFFFFF50 + 0x30) 12 = accV M4 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x30) 12 :=
      accV_congr2 12 fun j hj => by
        have e : sp0 + 0xFFFFFF50 + 0x30 + BitVec.ofNat 32 (4 * j) =
            sp0 + 0xFFFFFF50 + BitVec.ofNat 32 (0x30 + 4 * j) := add_ofNat_assoc _ 0x30 (4 * j)
        rw [e, load_frame2 fr5 (sFw 0x60 0x34 (0x30 + 4 * j) (by decide) (by omega) (.inr (by omega)))
          (sGw (0x30 + 4 * j) (by omega)), add_ofNat_assoc]
    have hS3 : accV M3 (sp0 + 0xFFFFFF50) 12 = accV M2 (sp0 + 0xFFFFFF50) 12 := accV_congr 12 fun j hj => by
      rw [← hM3, fillWords_load_sep (sFw 0x30 (4 * 12) (4 * j) (by decide) (by omega) (.inr (by omega)))]
    have hP3 : accV M3 p3M 12 = p384 := p3M_val (cOf env.pmod env.sSP frM3)
    have hA : accV M1 lp 12 = accV m.mem lp 12 := accV_congr 12 fun j hj =>
      load_frame fr1 (env.sLS.symm.subR (c := 4 * j) (l := 4) (by omega))
    have hB : accV M1 rp 12 = accV m.mem rp 12 := accV_congr 12 fun j hj =>
      load_frame fr1 (env.sRS.symm.subR (c := 4 * j) (l := 4) (by omega))
    rw [eOut, accV_sel hw6, p3_choice _ _ hc2 hb4, agS, agD, limbVal_wordsAt, limbVal_wordsAt]
    have hif : ∀ (Q : Prop) [Decidable Q] (X Y : Nat), (if (if Q then (1 : Word) else 0) = 1 then X else Y) =
        if Q then X else Y := fun Q _ X Y => by by_cases hq : Q <;> simp [hq]
    rw [hif]
    have e384 : (2 : Nat) ^ (32 * 12) = 2 ^ 384 := rfl
    refine p3_final (accV_lt _ _ 12) hc2 (mb_le1 _) ?_ ?_
    · rw [← hA, ← hB, ← e384]; exact hv2
    · rw [← hS3, ← hP3, ← e384]; exact hv4
  · intro x hx ho
    rw [mem7, copyWords_outside 12 ho, frM6 x hx]

end C3.RV32
