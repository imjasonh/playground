import C3BootProofs.Proofs.EdCall
import C3BootProofs.Proofs.EdNiels
import C3BootProofs.Proofs.CtInto

/-!
# `EdwardsPoint::is_small_order`, as compiled

`is_small_order` multiplies the point by the cofactor 8 with three
doublings (`mul_by_cofactor`, each a `ProjectivePoint::double` followed by
`as_projective`, the last by `as_extended`) and compares the result with the
identity through `EdwardsPoint::ct_eq`: `X · 1 = 0 · Z` and `Y · 1 = 1 · Z`,
each side through `mul` and the comparison through `FieldElement::ct_eq`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem iso_at_0 : fetchRel isSmallOrderCode 0x0 = some (.aluImm .add sp sp 0xFFFFFD40, 4) := by decide
theorem iso_at_4 : fetchRel isSmallOrderCode 0x4 = some (.aluImm .add a1 sp 0x280, 2) := by decide
theorem iso_at_6 : fetchRel isSmallOrderCode 0x6 = some (.store .sw a1 ra 0x3C, 4) := by decide
theorem iso_at_a : fetchRel isSmallOrderCode 0xA = some (.store .sw a1 (8 : Fin 32) 0x38, 2) := by decide
theorem iso_at_c : fetchRel isSmallOrderCode 0xC = some (.store .sw a1 (9 : Fin 32) 0x34, 2) := by decide
theorem iso_at_e : fetchRel isSmallOrderCode 0xE = some (.store .sw a1 (18 : Fin 32) 0x30, 4) := by decide
theorem iso_at_12 : fetchRel isSmallOrderCode 0x12 = some (.store .sw a1 (19 : Fin 32) 0x2C, 4) := by decide
theorem iso_at_16 : fetchRel isSmallOrderCode 0x16 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem iso_at_18 : fetchRel isSmallOrderCode 0x18 = some (.aluImm .add a0 sp 0x16C, 2) := by decide
theorem iso_at_1a : fetchRel isSmallOrderCode 0x1A = some (.aluImm .add a1 (8 : Fin 32) 0x28, 4) := by decide
theorem iso_at_1e : fetchRel isSmallOrderCode 0x1E = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem iso_at_22 : fetchRel isSmallOrderCode 0x22 = some (.auipc ra 0x4000, 4) := by decide
theorem iso_at_26 : fetchRel isSmallOrderCode 0x26 = some (.jalr ra ra 0xFFFFFF2E, 4) := by decide
theorem iso_at_2a : fetchRel isSmallOrderCode 0x2A = some (.aluImm .add a1 (8 : Fin 32) 0x50, 4) := by decide
theorem iso_at_2e : fetchRel isSmallOrderCode 0x2E = some (.aluImm .add a0 sp 0x194, 2) := by decide
theorem iso_at_30 : fetchRel isSmallOrderCode 0x30 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem iso_at_34 : fetchRel isSmallOrderCode 0x34 = some (.auipc ra 0x4000, 4) := by decide
theorem iso_at_38 : fetchRel isSmallOrderCode 0x38 = some (.jalr ra ra 0xFFFFFF1C, 4) := by decide
theorem iso_at_3c : fetchRel isSmallOrderCode 0x3C = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem iso_at_3e : fetchRel isSmallOrderCode 0x3E = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem iso_at_42 : fetchRel isSmallOrderCode 0x42 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem iso_at_44 : fetchRel isSmallOrderCode 0x44 = some (.auipc ra 0x4000, 4) := by decide
theorem iso_at_48 : fetchRel isSmallOrderCode 0x48 = some (.jalr ra ra 0xFFFFFF0C, 4) := by decide
theorem iso_at_4c : fetchRel isSmallOrderCode 0x4C = some (.aluImm .add (8 : Fin 32) x0 0x2, 2) := by decide
theorem iso_at_4e : fetchRel isSmallOrderCode 0x4E = some (.branch .beq (8 : Fin 32) x0 0x1E, 2) := by decide
theorem iso_at_50 : fetchRel isSmallOrderCode 0x50 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem iso_at_52 : fetchRel isSmallOrderCode 0x52 = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem iso_at_54 : fetchRel isSmallOrderCode 0x54 = some (.auipc ra 0x0, 4) := by decide
theorem iso_at_58 : fetchRel isSmallOrderCode 0x58 = some (.jalr ra ra 0xFFFFFB00, 4) := by decide
theorem iso_at_5c : fetchRel isSmallOrderCode 0x5C = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem iso_at_5e : fetchRel isSmallOrderCode 0x5E = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem iso_at_60 : fetchRel isSmallOrderCode 0x60 = some (.auipc ra 0x0, 4) := by decide
theorem iso_at_64 : fetchRel isSmallOrderCode 0x64 = some (.jalr ra ra 0xFFFFFAA8, 4) := by decide
theorem iso_at_68 : fetchRel isSmallOrderCode 0x68 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem iso_at_6a : fetchRel isSmallOrderCode 0x6A = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE6, 2) := by decide
theorem iso_at_6c : fetchRel isSmallOrderCode 0x6C = some (.aluImm .add a0 sp 0x1BC, 2) := by decide
theorem iso_at_6e : fetchRel isSmallOrderCode 0x6E = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem iso_at_70 : fetchRel isSmallOrderCode 0x70 = some (.auipc ra 0x0, 4) := by decide
theorem iso_at_74 : fetchRel isSmallOrderCode 0x74 = some (.jalr ra ra 0xFFFFFAE4, 4) := by decide
theorem iso_at_78 : fetchRel isSmallOrderCode 0x78 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem iso_at_7a : fetchRel isSmallOrderCode 0x7A = some (.aluImm .add a1 sp 0x1BC, 2) := by decide
theorem iso_at_7c : fetchRel isSmallOrderCode 0x7C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem iso_at_80 : fetchRel isSmallOrderCode 0x80 = some (.jalr ra ra 0x4F2, 4) := by decide
theorem iso_at_84 : fetchRel isSmallOrderCode 0x84 = some (.aluImm .add a0 sp 0x1BC, 2) := by decide
theorem iso_at_86 : fetchRel isSmallOrderCode 0x86 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem iso_at_8a : fetchRel isSmallOrderCode 0x8A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem iso_at_8c : fetchRel isSmallOrderCode 0x8C = some (.auipc ra 0x4000, 4) := by decide
theorem iso_at_90 : fetchRel isSmallOrderCode 0x90 = some (.jalr ra ra 0xFFFFFE5C, 4) := by decide
theorem iso_at_94 : fetchRel isSmallOrderCode 0x94 = some (.aluImm .add (18 : Fin 32) sp 0x1E4, 4) := by decide
theorem iso_at_98 : fetchRel isSmallOrderCode 0x98 = some (.lui (9 : Fin 32) 0x3FCC5000, 4) := by decide
theorem iso_at_9c : fetchRel isSmallOrderCode 0x9C = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFF948, 4) := by decide
theorem iso_at_a0 : fetchRel isSmallOrderCode 0xA0 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem iso_at_a4 : fetchRel isSmallOrderCode 0xA4 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem iso_at_a6 : fetchRel isSmallOrderCode 0xA6 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem iso_at_a8 : fetchRel isSmallOrderCode 0xA8 = some (.auipc ra 0x4000, 4) := by decide
theorem iso_at_ac : fetchRel isSmallOrderCode 0xAC = some (.jalr ra ra 0xFFFFFEA8, 4) := by decide
theorem iso_at_b0 : fetchRel isSmallOrderCode 0xB0 = some (.aluImm .add (19 : Fin 32) sp 0x20C, 4) := by decide
theorem iso_at_b4 : fetchRel isSmallOrderCode 0xB4 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem iso_at_b8 : fetchRel isSmallOrderCode 0xB8 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem iso_at_ba : fetchRel isSmallOrderCode 0xBA = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem iso_at_bc : fetchRel isSmallOrderCode 0xBC = some (.auipc ra 0x4000, 4) := by decide
theorem iso_at_c0 : fetchRel isSmallOrderCode 0xC0 = some (.jalr ra ra 0xFFFFFE94, 4) := by decide
theorem iso_at_c4 : fetchRel isSmallOrderCode 0xC4 = some (.aluImm .add a0 sp 0x234, 2) := by decide
theorem iso_at_c6 : fetchRel isSmallOrderCode 0xC6 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem iso_at_ca : fetchRel isSmallOrderCode 0xCA = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem iso_at_cc : fetchRel isSmallOrderCode 0xCC = some (.auipc ra 0x4000, 4) := by decide
theorem iso_at_d0 : fetchRel isSmallOrderCode 0xD0 = some (.jalr ra ra 0xFFFFFE1C, 4) := by decide
theorem iso_at_d4 : fetchRel isSmallOrderCode 0xD4 = some (.aluImm .add a0 sp 0x25C, 2) := by decide
theorem iso_at_d6 : fetchRel isSmallOrderCode 0xD6 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem iso_at_d8 : fetchRel isSmallOrderCode 0xD8 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem iso_at_da : fetchRel isSmallOrderCode 0xDA = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem iso_at_de : fetchRel isSmallOrderCode 0xDE = some (.jalr ra ra 0xFFFFFD7A, 4) := by decide
theorem iso_at_e2 : fetchRel isSmallOrderCode 0xE2 = some (.aluImm .add (9 : Fin 32) sp 0x54, 2) := by decide
theorem iso_at_e4 : fetchRel isSmallOrderCode 0xE4 = some (.aluImm .add a0 sp 0x284, 2) := by decide
theorem iso_at_e6 : fetchRel isSmallOrderCode 0xE6 = some (.aluImm .add a1 sp 0x1BC, 2) := by decide
theorem iso_at_e8 : fetchRel isSmallOrderCode 0xE8 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem iso_at_ea : fetchRel isSmallOrderCode 0xEA = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem iso_at_ee : fetchRel isSmallOrderCode 0xEE = some (.jalr ra ra 0xFFFFFD6A, 4) := by decide
theorem iso_at_f2 : fetchRel isSmallOrderCode 0xF2 = some (.aluImm .add a0 sp 0x25C, 2) := by decide
theorem iso_at_f4 : fetchRel isSmallOrderCode 0xF4 = some (.aluImm .add a1 sp 0x284, 2) := by decide
theorem iso_at_f6 : fetchRel isSmallOrderCode 0xF6 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem iso_at_fa : fetchRel isSmallOrderCode 0xFA = some (.jalr ra ra 0x5A8, 4) := by decide
theorem iso_at_fe : fetchRel isSmallOrderCode 0xFE = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem iso_at_100 : fetchRel isSmallOrderCode 0x100 = some (.aluImm .add a1 sp 0x2C, 2) := by decide
theorem iso_at_102 : fetchRel isSmallOrderCode 0x102 = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem iso_at_104 : fetchRel isSmallOrderCode 0x104 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem iso_at_106 : fetchRel isSmallOrderCode 0x106 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem iso_at_10a : fetchRel isSmallOrderCode 0x10A = some (.jalr ra ra 0xFFFFFD4E, 4) := by decide
theorem iso_at_10e : fetchRel isSmallOrderCode 0x10E = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem iso_at_110 : fetchRel isSmallOrderCode 0x110 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem iso_at_112 : fetchRel isSmallOrderCode 0x112 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem iso_at_114 : fetchRel isSmallOrderCode 0x114 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem iso_at_118 : fetchRel isSmallOrderCode 0x118 = some (.jalr ra ra 0xFFFFFD40, 4) := by decide
theorem iso_at_11c : fetchRel isSmallOrderCode 0x11C = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem iso_at_11e : fetchRel isSmallOrderCode 0x11E = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem iso_at_120 : fetchRel isSmallOrderCode 0x120 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem iso_at_124 : fetchRel isSmallOrderCode 0x124 = some (.jalr ra ra 0x57E, 4) := by decide
theorem iso_at_128 : fetchRel isSmallOrderCode 0x128 = some (.alu .and a0 a0 (8 : Fin 32), 2) := by decide
theorem iso_at_12a : fetchRel isSmallOrderCode 0x12A = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem iso_at_12e : fetchRel isSmallOrderCode 0x12E = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem iso_at_132 : fetchRel isSmallOrderCode 0x132 = some (.jalr ra ra 0xFFFFFD18, 4) := by decide
theorem iso_at_136 : fetchRel isSmallOrderCode 0x136 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem iso_at_13a : fetchRel isSmallOrderCode 0x13A = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem iso_at_13e : fetchRel isSmallOrderCode 0x13E = some (.aluImm .add a1 sp 0x280, 2) := by decide
theorem iso_at_140 : fetchRel isSmallOrderCode 0x140 = some (.load .lw ra a1 0x3C, 4) := by decide
theorem iso_at_144 : fetchRel isSmallOrderCode 0x144 = some (.load .lw (8 : Fin 32) a1 0x38, 2) := by decide
theorem iso_at_146 : fetchRel isSmallOrderCode 0x146 = some (.load .lw (9 : Fin 32) a1 0x34, 2) := by decide
theorem iso_at_148 : fetchRel isSmallOrderCode 0x148 = some (.load .lw (18 : Fin 32) a1 0x30, 4) := by decide
theorem iso_at_14c : fetchRel isSmallOrderCode 0x14C = some (.load .lw (19 : Fin 32) a1 0x2C, 4) := by decide
theorem iso_at_150 : fetchRel isSmallOrderCode 0x150 = some (.aluImm .add sp sp 0x2C0, 4) := by decide
theorem iso_at_154 : fetchRel isSmallOrderCode 0x154 = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev ISO : Word := BitVec.ofNat 32 isSmallOrderAddress

/-- A doubling followed by `as_projective`, on limb lists: one step of
`mul_by_pow_2`. -/
def isoStep (X Y Z : List Nat) : List Nat × List Nat × List Nat :=
  let c := edDoubleSpec X Y Z
  (mulL c.1 c.2.2.2, mulL c.2.1 c.2.2.1, mulL c.2.2.1 c.2.2.2)

/-- The cofactor multiple's extended coordinates. -/
def isoTimes8 (X Y Z : List Nat) : List Nat × List Nat × List Nat :=
  let p1 := isoStep X Y Z
  let p2 := isoStep p1.1 p1.2.1 p1.2.2
  let c := edDoubleSpec p2.1 p2.2.1 p2.2.2
  (mulL c.1 c.2.2.2, mulL c.2.1 c.2.2.1, mulL c.2.2.1 c.2.2.2)

def feZeroL : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def feOneL : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- What `is_small_order` decides for the point with projective coordinates
`X`, `Y`, `Z`: whether 8 times it equals the identity, as `ct_eq` compares. -/
def isoSpec (X Y Z : List Nat) : Bool :=
  let e := isoTimes8 X Y Z
  decide (bytesL (mulL e.1 feOneL) = bytesL (mulL feZeroL e.2.2)) &&
    decide (bytesL (mulL e.2.1 feOneL) = bytesL (mulL feOneL e.2.2))

/-- The code `is_small_order` runs and its callees', and the field element
`ONE` it copies. -/
structure ISOEnv (M : Word → BitVec 8) : Prop where
  cod : CodeIn M ISO isSmallOrderCode
  mcs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  mcb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  mset : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  dbl : CodeIn M (BitVec.ofNat 32 edDoubleAddress) edDoubleCode
  sq : CodeIn M (BitVec.ofNat 32 feSquareAddress) feSquareCode
  sqi : CodeIn M (BitVec.ofNat 32 feSquareInnerAddress) feSquareInnerCode
  red : CodeIn M (BitVec.ofNat 32 feReduceAddress) feReduceCode
  add : CodeIn M (BitVec.ofNat 32 feAddAddress) feAddCode
  sub : CodeIn M (BitVec.ofNat 32 feSubAddress) feSubCode
  ap : CodeIn M (BitVec.ofNat 32 asProjectiveAddress) asProjectiveCode
  ax : CodeIn M (BitVec.ofNat 32 asExtendedAddress) asExtendedCode
  mul : CodeIn M (BitVec.ofNat 32 feMulAddress) feMulCode
  ce : CodeIn M (BitVec.ofNat 32 feCtEqAddress) feCtEqCode
  tb : CodeIn M (BitVec.ofNat 32 feToBytesAddress) feToBytesCode
  cs : CodeIn M (BitVec.ofNat 32 ctEqSliceAddress) ctEqSliceCode
  cu : CodeIn M (BitVec.ofNat 32 ctEqU8Address) ctEqU8Code
  bb : CodeIn M (BitVec.ofNat 32 blackBoxU8Address) blackBoxU8Code
  one : feW M (BitVec.ofNat 32 edOneAddress) = feOneL

theorem feW_copyW {M : Word → BitVec 8} {d s : Word} (h : d.toNat + 40 ≤ 2 ^ 32) :
    feW (copyWords M d s 10) d = feW M s := by
  unfold feW limbAt
  rw [copyWords_load 10 0 (by decide) h, copyWords_load 10 1 (by decide) h, copyWords_load 10 2 (by decide) h,
    copyWords_load 10 3 (by decide) h, copyWords_load 10 4 (by decide) h, copyWords_load 10 5 (by decide) h,
    copyWords_load 10 6 (by decide) h, copyWords_load 10 7 (by decide) h, copyWords_load 10 8 (by decide) h,
    copyWords_load 10 9 (by decide) h]

theorem feW_fill0 {M : Word → BitVec 8} {d : Word} (h : d.toNat + 40 ≤ 2 ^ 32) :
    feW (fillWords M d 0 10) d = feZeroL := by
  unfold feW limbAt
  rw [fillWords_load 10 0 (by decide) h, fillWords_load 10 1 (by decide) h, fillWords_load 10 2 (by decide) h,
    fillWords_load 10 3 (by decide) h, fillWords_load 10 4 (by decide) h, fillWords_load 10 5 (by decide) h,
    fillWords_load 10 6 (by decide) h, fillWords_load 10 7 (by decide) h, fillWords_load 10 8 (by decide) h,
    fillWords_load 10 9 (by decide) h]
  rfl

abbrev isoPs : List (Fin 32 × Word) :=
  [(ra, 0x3C), ((8 : Fin 32), 0x38), ((9 : Fin 32), 0x34), ((18 : Fin 32), 0x30), ((19 : Fin 32), 0x2C)]

def isoA : List BInstr := [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 0x16C, .aluImm .add a1 (8 : Fin 32) 0x28,
  .aluImm .add a2 x0 0x28]
def isoB : List BInstr := [.aluImm .add a1 (8 : Fin 32) 0x50, .aluImm .add a0 sp 0x194, .aluImm .add a2 x0 0x28]
def isoC : List BInstr := [.aluImm .add a0 sp 0x144, .aluImm .add a2 x0 0x28, .alu .add a1 x0 (8 : Fin 32)]
def isoD1 : List BInstr := [.aluImm .add a0 sp 0xA4, .aluImm .add a1 sp 0x144]
def isoD2 : List BInstr := [.aluImm .add a0 sp 0x144, .aluImm .add a1 sp 0xA4]
def isoE1 : List BInstr := [.aluImm .add a0 sp 0x1BC, .aluImm .add a1 sp 0x144]
def isoE2 : List BInstr := [.aluImm .add a0 sp 0x4, .aluImm .add a1 sp 0x1BC]

section
set_option maxRecDepth 20000
theorem isoSave_end : blockEnd isSmallOrderCode 0x6 (saveBlockR a1 isoPs) = some 0x16 := by decide
theorem isoA_end : blockEnd isSmallOrderCode 0x16 isoA = some 0x22 := by decide
theorem isoB_end : blockEnd isSmallOrderCode 0x2A isoB = some 0x34 := by decide
theorem isoC_end : blockEnd isSmallOrderCode 0x3C isoC = some 0x44 := by decide
theorem isoD1_end : blockEnd isSmallOrderCode 0x50 isoD1 = some 0x54 := by decide
theorem isoD2_end : blockEnd isSmallOrderCode 0x5C isoD2 = some 0x60 := by decide
theorem isoE1_end : blockEnd isSmallOrderCode 0x6C isoE1 = some 0x70 := by decide
theorem isoE2_end : blockEnd isSmallOrderCode 0x78 isoE2 = some 0x7C := by decide
theorem isoRestore_end : blockEnd isSmallOrderCode 0x140 (restoreBlockR a1 isoPs) = some 0x150 := by decide
end

def isoF1 : List BInstr := [.aluImm .add a0 sp 0x1BC, .aluImm .add a2 x0 0x28, .aluImm .add a1 x0 0x0]
def isoF2 : List BInstr := [.aluImm .add (18 : Fin 32) sp 0x1E4, .lui (9 : Fin 32) 0x3FCC5000,
  .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFF948, .aluImm .add a2 x0 0x28, .alu .add a0 x0 (18 : Fin 32),
  .alu .add a1 x0 (9 : Fin 32)]
def isoF3 : List BInstr := [.aluImm .add (19 : Fin 32) sp 0x20C, .aluImm .add a2 x0 0x28, .alu .add a0 x0 (19 : Fin 32),
  .alu .add a1 x0 (9 : Fin 32)]
def isoF4 : List BInstr := [.aluImm .add a0 sp 0x234, .aluImm .add a2 x0 0x28, .aluImm .add a1 x0 0x0]
def isoG1 : List BInstr := [.aluImm .add a0 sp 0x25C, .aluImm .add a1 sp 0x4, .alu .add a2 x0 (19 : Fin 32)]
def isoG2 : List BInstr := [.aluImm .add (9 : Fin 32) sp 0x54, .aluImm .add a0 sp 0x284, .aluImm .add a1 sp 0x1BC,
  .alu .add a2 x0 (9 : Fin 32)]
def isoG3 : List BInstr := [.aluImm .add a0 sp 0x25C, .aluImm .add a1 sp 0x284]
def isoG4 : List BInstr := [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a1 sp 0x2C, .aluImm .add a0 sp 0x144,
  .alu .add a2 x0 (19 : Fin 32)]
def isoG5 : List BInstr := [.aluImm .add a0 sp 0xA4, .alu .add a1 x0 (18 : Fin 32), .alu .add a2 x0 (9 : Fin 32)]
def isoG6 : List BInstr := [.aluImm .add a0 sp 0x144, .aluImm .add a1 sp 0xA4]
def isoG7 : List BInstr := [.alu .and a0 a0 (8 : Fin 32), .aluImm .and a0 a0 0xFF]
def isoG8 : List BInstr := [.aluImm .and a0 a0 0xFF, .alu .sltu a0 x0 a0, .aluImm .add a1 sp 0x280]

section
set_option maxRecDepth 20000
theorem isoF1_end : blockEnd isSmallOrderCode 0x84 isoF1 = some 0x8C := by decide
theorem isoF2_end : blockEnd isSmallOrderCode 0x94 isoF2 = some 0xA8 := by decide
theorem isoF3_end : blockEnd isSmallOrderCode 0xB0 isoF3 = some 0xBC := by decide
theorem isoF4_end : blockEnd isSmallOrderCode 0xC4 isoF4 = some 0xCC := by decide
theorem isoG1_end : blockEnd isSmallOrderCode 0xD4 isoG1 = some 0xDA := by decide
theorem isoG2_end : blockEnd isSmallOrderCode 0xE2 isoG2 = some 0xEA := by decide
theorem isoG3_end : blockEnd isSmallOrderCode 0xF2 isoG3 = some 0xF6 := by decide
theorem isoG4_end : blockEnd isSmallOrderCode 0xFE isoG4 = some 0x106 := by decide
theorem isoG5_end : blockEnd isSmallOrderCode 0x10E isoG5 = some 0x114 := by decide
theorem isoG6_end : blockEnd isSmallOrderCode 0x11C isoG6 = some 0x120 := by decide
theorem isoG7_end : blockEnd isSmallOrderCode 0x128 isoG7 = some 0x12E := by decide
theorem isoG8_end : blockEnd isSmallOrderCode 0x136 isoG8 = some 0x140 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `EdwardsPoint::is_small_order`**: for the point at `p`,
it returns 1 when 8 times it is the identity, as `isoSpec` computes from
the point's projective coordinates' limbs, and 0 otherwise. It returns with
`sp` and the callee-saved registers restored and writes only the 0x4D0
bytes of stack below `sp`. -/
theorem isSmallOrder_correct (m : Machine) {sp0 p retAddr : Word} (E : ISOEnv m.mem)
    (hpc : m.pc = ISO) (ha0 : reg m a0 = p) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0) (hsl : 0x4D0 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (hpa : p.toNat % 4 = 0) (sPG : Sep p 120 (sp0 + 0xFFFFFB30) 0x4D0)
    (sOG : Sep (BitVec.ofNat 32 edOneAddress) 40 (sp0 + 0xFFFFFB30) 0x4D0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      reg m' a0 = (if isoSpec (feW m.mem p) (feW m.mem (p + 0x28)) (feW m.mem (p + 0x50)) then 1 else 0) ∧
      ∀ x, Sep (sp0 + 0xFFFFFB30) 0x4D0 x 1 → m'.mem x = m.mem x := by
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFFB30 = R := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFD40 = F := ⟨_, rfl⟩
  rw [hR] at sPG sOG ⊢
  have hRn : R.toNat = sp0.toNat - 0x4D0 := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFB30 : Word).toNat = 2 ^ 32 - 0x4D0 from rfl]; have := sp0.isLt; omega
  have hRF : R + BitVec.ofNat 32 0x210 = F := by rw [← hR, ← hF, BitVec.add_assoc]; rfl
  have hRc : ∀ c, c ≤ 0x4D0 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFn : F.toNat = R.toNat + 0x210 := by rw [← hRF]; exact hRc _ (by decide)
  have hFa : F.toNat % 4 = 0 := by omega
  have eFk : ∀ k, F + BitVec.ofNat 32 k = R + BitVec.ofNat 32 (0x210 + k) := fun k => by rw [← hRF, add_ofNat_assoc]
  have eFS : F + 0x2C0 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x4D0 → d + k ≤ 0x4D0 →
      Sep (R + BitVec.ofNat 32 c) n (R + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets R h (by omega) (by omega)
  have inR : ∀ {c l : Nat} {x : Word}, Sep R 0x4D0 x 1 → c + l ≤ 0x4D0 → Sep (R + BitVec.ofNat 32 c) l x 1 :=
    fun hx h => (hx.symm.subR h).symm
  have hiR : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep R 0x4D0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hiC : ∀ {c l : Nat} {a : Word} {len : Nat}, c + l ≤ 0x4D0 → 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l a len := fun h h1 h2 => sep_of_le (by rw [hRc _ (by omega)]; omega) h2
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep R 0x4D0 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by rw [hM _ (hiR _ (code_hi h1 h2 hi'))]; exact hc i hi'
  -- a field element at `F + k` and the regions a call writes
  have fA : ∀ k, k % 4 = 0 → (F + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k h => aligned_add hFa h
  have fW : ∀ k, k + 40 ≤ 0x2C0 → (F + BitVec.ofNat 32 k).toNat + 40 < 2 ^ 32 := fun k h => by
    rw [eFk, hRc _ (by omega)]; omega
  have pers : ∀ {M M' : Word → BitVec 8} {a W V : Word} {wl vl : Nat}, (∀ z, Sep W wl z 1 → Sep V vl z 1 → M' z = M z) →
      Sep a 40 W wl → Sep a 40 V vl → feW M' a = feW M a :=
    fun hM h1 h2 => feW_frame fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact hM _ (h1.sub (c := 4 * i + j) (l := 1) (by omega)).symm (h2.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  have hISn : ISO.toNat = (img% isSmallOrderAddress) := by decide
  have hc := E.cod
  have st0 : St m.mem ISO m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc iso_at_0 (off' := 4) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.self.aluImm hc iso_at_4 (off' := 6) (by decide)
  have sp2 : reg m2 sp = F := by
    rw [u2.regs, upd_ne (by decide) (by decide), u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hF
  have a12 : reg m2 a1 = F + 0x280 := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, ev_add]; rw [hsp, hF]
  have slotC : ∀ o : Word, 0x2AC ≤ o.toNat → o.toNat + 4 ≤ 0x2C0 →
      Sep (F + o) 4 ISO isSmallOrderCode.length := fun o h1 h2 =>
    sep_of_le (by rw [BitVec.toNat_add, hISn]; have := Nat.mod_le (F.toNat + o.toNat) (2 ^ 32); omega)
      (by rw [hISn]; decide)
  have eA1 : ∀ o : Word, F + 0x280 + o = F + (0x280 + o) := fun o => BitVec.add_assoc _ _ _
  obtain ⟨m3, c3, u3⟩ := St.block (saveBlockR a1 isoPs) u2.self hc isoSave_end (saveBlockR_ok a1 _ isoPs _ fun q hq => by
      rw [a12]
      simp only [isoPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by rw [eA1]; exact fA _ (by decide), by rw [eA1]; exact slotC _ (by decide) (by decide)⟩)
  rw [saveBlockR_run, a12] at u3
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem (F + 0x280) (reg m2) isoPs = Ms := ⟨_, rfl⟩
  have u3' : St Ms ISO m3 0x16 (reg m3) := ⟨u3.pc, by rw [u3.mem, ← hMs], fun _ => rfl⟩
  have R3 : ∀ q, reg m3 q = reg m2 q := u3.regs
  have IMs : ∀ x, Sep R 0x4D0 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside isoPs fun q hq => by
      simp only [isoPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        (rw [eA1, show (0x280 : Word) + _ = BitVec.ofNat 32 _ from rfl, eFk]; exact inR hx (by decide))
  have r2 : ∀ q, q ≠ sp → q ≠ a1 → reg m2 q = reg m q := fun q h1 h2 => by
    rw [u2.regs, updz u1.self.zero h2, u1.regs, updz hz h1]
  have slots : ∀ r o, (r, o) ∈ isoPs → memLoad32 Ms (F + 0x280 + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp ∧ r ≠ a1 := by
      simp only [isoPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot isoPs _ hm (by
      simp only [isoPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), r2 r hr.1 hr.2]
  have hc3 : CodeIn Ms ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IMs
  -- code facts in a memory that agrees with the entry memory outside the stack region
  have hMSn : (BitVec.ofNat 32 memsetAddress : Word).toNat = memsetAddress := by decide
  have hMCn : (BitVec.ofNat 32 memcpyStubAddress : Word).toNat = memcpyStubAddress := by decide
  have hMCb : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = memcpyStubAddress + 8 := by decide
  have sPk : ∀ k, k + 40 ≤ 120 → Sep (p + BitVec.ofNat 32 k) 40 R 0x4D0 := fun k h => sPG.sub h
  have fk : ∀ k, k + 40 ≤ 0x2C0 → ∀ c l, c + l ≤ 0x4D0 → 0x210 + k + 40 ≤ c ∨ c + l ≤ 0x210 + k →
      Sep (F + BitVec.ofNat 32 k) 40 (R + BitVec.ofNat 32 c) l := fun k h c l hl hd => by
    rw [eFk]; exact offs (by omega) (by omega) (by omega)
  have fkC : ∀ k, k + 40 ≤ 0x2C0 → ∀ {a : Word} {len : Nat}, 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (F + BitVec.ofNat 32 k) 40 a len := fun k h a len h1 h2 => by rw [eFk]; exact hiC (by omega) h1 h2
  have fkP : ∀ k, k + 40 ≤ 0x2C0 → ∀ j, j + 40 ≤ 120 → Sep (F + BitVec.ofNat 32 k) 40 (p + BitVec.ofNat 32 j) 40 :=
    fun k h j hj => by rw [eFk]; exact ((sPk j hj).subR (c := 0x210 + k) (l := 40) (by omega)).symm
  have fkI : ∀ k, k + 40 ≤ 0x2C0 → ∀ {x : Word}, Sep R 0x4D0 x 1 → Sep (F + BitVec.ofNat 32 k) 40 x 1 :=
    fun k h x hx => by rw [eFk]; exact inR hx (by omega)
  obtain ⟨m4, c4, u4⟩ := St.block isoA u3' hc3 isoA_end (by simp only [BlockOk, BInstr.ok, isoA, and_self])
  have R4 : ∀ q, reg m4 q = (runBlock isoA (Ms, reg m3)).2 q := u4.regs
  have u4' : St Ms ISO m4 0x22 (reg m4) := ⟨u4.pc, by rw [u4.mem]; rfl, fun _ => rfl⟩
  have sp3 : reg m3 sp = F := by rw [R3, sp2]
  have v4 : reg m4 (8 : Fin 32) = p ∧ reg m4 a0 = F + BitVec.ofNat 32 0x16C ∧ reg m4 a1 = p + BitVec.ofNat 32 0x28 ∧
      reg m4 a2 = BitVec.ofNat 32 (4 * 10) := by
    simp +decide only [R4, runBlock, BInstr.run, isoA, upd_app, ↓reduceIte, ev_add]
    rw [u3'.zero, R3 a0, r2 a0 (by decide) (by decide), ha0, sp3]; exact ⟨zw _, rfl, by rw [zw]; rfl, trivial⟩
  obtain ⟨m5, c5, u5, _, k5⟩ := u4'.memcpyW (B := BitVec.ofNat 32 memcpyStubAddress) (w := 10)
    (dst := F + BitVec.ofNat 32 0x16C) (src := p + BitVec.ofNat 32 0x28) (by decide) hc3
    (cd E.mcs (by rw [hMCn]; decide) (by rw [hMCn]; decide) IMs) (cd E.mcb (by rw [hMCb]; decide) (by rw [hMCb]; decide) IMs)
    iso_at_22 iso_at_26 (by decide) (by decide) (by decide) (fW 0x16C (by decide)) (by decide)
    (fA _ (by decide)) (aligned_add hpa (by decide)) (fkP _ (by decide) _ (by decide))
    (fkC _ (by decide) (by rw [hMCb]; decide) (by rw [hMCb]; decide)) v4.2.1 v4.2.2.1 v4.2.2.2
  obtain ⟨M5, hM5⟩ : ∃ M5, copyWords Ms (F + BitVec.ofNat 32 0x16C) (p + BitVec.ofNat 32 0x28) 10 = M5 := ⟨_, rfl⟩
  rw [hM5] at u5
  have IM5 : ∀ x, Sep R 0x4D0 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5, copyWords_outside 10 (fkI _ (by decide) hx), IMs x hx]
  have hc5 : CodeIn M5 ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM5
  have Kl5 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m q := fun q hq => by
    rw [k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), R4, runBlock_reg _ _ _ q u3'.zero (by
        simp only [isoA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        intro h; revert h hq; revert q; decide), R3, r2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have v5 : reg m5 (8 : Fin 32) = p ∧ reg m5 sp = F := by
    rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), k5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), v4.1, R4, runBlock_reg _ _ _ sp u3'.zero (by decide), sp3]
    exact ⟨rfl, rfl⟩
  -- the second copy: `Z`
  obtain ⟨m6, c6, u6⟩ := St.block isoB u5 hc5 isoB_end (by simp only [BlockOk, BInstr.ok, isoB, and_self])
  have R6 : ∀ q, reg m6 q = (runBlock isoB (M5, reg m5)).2 q := u6.regs
  have u6' : St M5 ISO m6 0x34 (reg m6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
  have K6 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m6 q = reg m5 q := fun q h0 h1 h2 => by
    rw [R6]; refine runBlock_reg _ _ _ q u5.zero ?_
    simp only [isoB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2]
  have v6 : reg m6 a1 = p + BitVec.ofNat 32 0x50 ∧ reg m6 a0 = F + BitVec.ofNat 32 0x194 ∧
      reg m6 a2 = BitVec.ofNat 32 (4 * 10) := by
    simp +decide only [R6, runBlock, BInstr.run, isoB, upd_app, ↓reduceIte, ev_add]
    rw [v5.1, v5.2]; exact ⟨rfl, rfl, trivial⟩
  obtain ⟨m7, c7, u7, _, k7⟩ := u6'.memcpyW (B := BitVec.ofNat 32 memcpyStubAddress) (w := 10)
    (dst := F + BitVec.ofNat 32 0x194) (src := p + BitVec.ofNat 32 0x50) (by decide) hc5
    (cd E.mcs (by rw [hMCn]; decide) (by rw [hMCn]; decide) IM5) (cd E.mcb (by rw [hMCb]; decide) (by rw [hMCb]; decide) IM5)
    iso_at_34 iso_at_38 (by decide) (by decide) (by decide) (fW 0x194 (by decide)) (by decide)
    (fA _ (by decide)) (aligned_add hpa (by decide)) (fkP _ (by decide) _ (by decide))
    (fkC _ (by decide) (by rw [hMCb]; decide) (by rw [hMCb]; decide)) v6.2.1 v6.1 v6.2.2
  obtain ⟨M7, hM7⟩ : ∃ M7, copyWords M5 (F + BitVec.ofNat 32 0x194) (p + BitVec.ofNat 32 0x50) 10 = M7 := ⟨_, rfl⟩
  rw [hM7] at u7
  have IM7 : ∀ x, Sep R 0x4D0 x 1 → M7 x = m.mem x := fun x hx => by
    rw [← hM7, copyWords_outside 10 (fkI _ (by decide) hx), IM5 x hx]
  have hc7 : CodeIn M7 ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM7
  have v7 : reg m7 (8 : Fin 32) = p ∧ reg m7 sp = F := by
    rw [k7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), k7 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), K6 _ (by decide) (by decide) (by decide),
      K6 sp (by decide) (by decide) (by decide)]
    exact v5
  have Kl7 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m7 q = reg m q := fun q hq => by
    rw [k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), K6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), Kl5 q hq]
  -- the third copy: `X`
  obtain ⟨m8, c8, u8⟩ := St.block isoC u7 hc7 isoC_end (by simp only [BlockOk, BInstr.ok, isoC, and_self])
  have R8 : ∀ q, reg m8 q = (runBlock isoC (M7, reg m7)).2 q := u8.regs
  have u8' : St M7 ISO m8 0x44 (reg m8) := ⟨u8.pc, by rw [u8.mem]; rfl, fun _ => rfl⟩
  have K8 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m8 q = reg m7 q := fun q h0 h1 h2 => by
    rw [R8]; refine runBlock_reg _ _ _ q u7.zero ?_
    simp only [isoC, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2]
  have v8 : reg m8 a0 = F + BitVec.ofNat 32 0x144 ∧ reg m8 a2 = BitVec.ofNat 32 (4 * 10) ∧ reg m8 a1 = p := by
    simp +decide only [R8, runBlock, BInstr.run, isoC, upd_app, ↓reduceIte, ev_add]
    rw [v7.1, v7.2]; exact ⟨rfl, trivial, zw _⟩
  obtain ⟨m9, c9, u9, _, k9⟩ := u8'.memcpyW (B := BitVec.ofNat 32 memcpyStubAddress) (w := 10)
    (dst := F + BitVec.ofNat 32 0x144) (src := p) (by decide) hc7
    (cd E.mcs (by rw [hMCn]; decide) (by rw [hMCn]; decide) IM7) (cd E.mcb (by rw [hMCb]; decide) (by rw [hMCb]; decide) IM7)
    iso_at_44 iso_at_48 (by decide) (by decide) (by decide) (fW 0x144 (by decide)) (by decide)
    (fA _ (by decide)) hpa (by have := fkP 0x144 (by decide) 0 (by decide); rwa [add_ofNat_zero] at this)
    (fkC _ (by decide) (by rw [hMCb]; decide) (by rw [hMCb]; decide)) v8.1 v8.2.2 v8.2.1
  obtain ⟨M9, hM9⟩ : ∃ M9, copyWords M7 (F + BitVec.ofNat 32 0x144) p 10 = M9 := ⟨_, rfl⟩
  rw [hM9] at u9
  have IM9 : ∀ x, Sep R 0x4D0 x 1 → M9 x = m.mem x := fun x hx => by
    rw [← hM9, copyWords_outside 10 (fkI _ (by decide) hx), IM7 x hx]
  have hc9 : CodeIn M9 ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM9
  have v9 : reg m9 sp = F := by
    rw [k9 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), K8 sp (by decide) (by decide) (by decide), v7.2]
  have Kl9 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m9 q = reg m q := fun q hq => by
    rw [k9 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), K8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), Kl7 q hq]
  -- the copied coordinates
  have pX : feW m.mem p = feW M7 p := (pers (W := R) (V := R) (wl := 0x4D0) (vl := 0x4D0)
    (fun z h _ => IM7 z h) (by have := sPk 0 (by decide); rwa [add_ofNat_zero] at this)
    (by have := sPk 0 (by decide); rwa [add_ofNat_zero] at this)).symm
  have cX : feW M9 (F + BitVec.ofNat 32 0x144) = feW m.mem p := by rw [← hM9, feW_copyW (Nat.le_of_lt (fW _ (by decide))), pX]
  have cY : feW M9 (F + BitVec.ofNat 32 0x16C) = feW m.mem (p + 0x28) := by
    rw [← hM9, pers (W := F + BitVec.ofNat 32 0x144) (V := F + BitVec.ofNat 32 0x144) (wl := 40) (vl := 40)
      (fun z h _ => copyWords_outside 10 h) (by rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega))
      (by rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)), ← hM7,
      pers (W := F + BitVec.ofNat 32 0x194) (V := F + BitVec.ofNat 32 0x194) (wl := 40) (vl := 40)
      (fun z h _ => copyWords_outside 10 h) (by rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega))
      (by rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)), ← hM5,
      feW_copyW (Nat.le_of_lt (fW _ (by decide)))]
    exact pers (W := R) (V := R) (wl := 0x4D0) (vl := 0x4D0) (fun z h _ => IMs z h) (sPk _ (by decide)) (sPk _ (by decide))
  have cZ : feW M9 (F + BitVec.ofNat 32 0x194) = feW m.mem (p + 0x50) := by
    rw [← hM9, pers (W := F + BitVec.ofNat 32 0x144) (V := F + BitVec.ofNat 32 0x144) (wl := 40) (vl := 40)
      (fun z h _ => copyWords_outside 10 h) (by rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega))
      (by rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)), ← hM7,
      feW_copyW (Nat.le_of_lt (fW _ (by decide)))]
    exact pers (W := R) (V := R) (wl := 0x4D0) (vl := 0x4D0) (fun z h _ => IM5 z h) (sPk _ (by decide)) (sPk _ (by decide))
  -- the callees' environments, for any memory that agrees with the entry memory outside the stack region
  have hR4 : R.toNat % 4 = 0 := by omega
  have hiR0 : ∀ {a : Word} {len : Nat} {l : Nat}, l ≤ 0x4D0 → 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep R l a len := fun h h1 h2 => sep_of_le (by omega) h2
  have fkR : ∀ k n, k + n ≤ 0x2C0 → ∀ c l, c + l ≤ 0x210 → Sep (F + BitVec.ofNat 32 k) n (R + BitVec.ofNat 32 c) l :=
    fun k n h c l hl => by rw [eFk]; exact offs (by omega) (by omega) (by omega)
  have fkR0 : ∀ k n, k + n ≤ 0x2C0 → ∀ l, l ≤ 0x210 → Sep (F + BitVec.ofNat 32 k) n R l := fun k n h l hl => by
    have := fkR k n h 0 l (by omega); rwa [add_ofNat_zero] at this
  have fkF : ∀ k n j o, k + n ≤ 0x2C0 → j + o ≤ 0x2C0 → k + n ≤ j ∨ j + o ≤ k →
      Sep (F + BitVec.ofNat 32 k) n (F + BitVec.ofNat 32 j) o := fun k n j o h1 h2 h3 => by
    rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)
  have fkCn : ∀ k n, k + n ≤ 0x2C0 → ∀ {a : Word} {len : Nat}, 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (F + BitVec.ofNat 32 k) n a len := fun k n h a len h1 h2 => by rw [eFk]; exact hiC (by omega) h1 h2
  have fkW : ∀ k n, k + n ≤ 0x2C0 → (F + BitVec.ofNat 32 k).toNat + n < 2 ^ 32 := fun k n h => by
    rw [eFk, hRc _ (by omega)]; omega
  have eRF : F + 0xFFFFFDF0 = R := by rw [← hRF, BitVec.add_assoc]; exact BitVec.add_zero R
  have eAP : apR F = R + BitVec.ofNat 32 0xC0 := by
    show F + 0xFFFFFEB0 = _; rw [← hRF, BitVec.add_assoc]; rfl
  have eAX : axR F = R + BitVec.ofNat 32 0xB0 := by
    show F + 0xFFFFFEA0 = _; rw [← hRF, BitVec.add_assoc]; rfl
  have eMR : F + 0xFFFFFEC0 = R + BitVec.ofNat 32 0xD0 := by rw [← hRF, BitVec.add_assoc]; rfl
  have eCR : F + 0xFFFFFF00 = R + BitVec.ofNat 32 0x110 := by rw [← hRF, BitVec.add_assoc]; rfl
  have envD : ∀ {M : Word → BitVec 8}, (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) → ∀ k j, k % 4 = 0 → j % 4 = 0 →
      k + 160 ≤ 0x2C0 → j + 120 ≤ 0x2C0 →
      EdDblEnv M (BitVec.ofNat 32 edDoubleAddress) R (F + BitVec.ofNat 32 k) (F + BitVec.ofNat 32 j) :=
    fun IM k j hk hj h1 h2 => by
      refine ⟨by decide, cd E.dbl (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 edDoubleAddress + 0xFFFFE164 = BitVec.ofNat 32 feSquareAddress by decide]
           exact cd E.sq (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 edDoubleAddress + 0xFFFFE18A = BitVec.ofNat 32 feSquareInnerAddress by decide]
           exact cd E.sqi (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 edDoubleAddress + 0xFFFFDDF0 = BitVec.ofNat 32 feReduceAddress by decide]
           exact cd E.red (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 edDoubleAddress + 0xFFFFE674 = BitVec.ofNat 32 feAddAddress by decide]
           exact cd E.add (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 edDoubleAddress + 0xFFFFE6C2 = BitVec.ofNat 32 feSubAddress by decide]
           exact cd E.sub (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 edDoubleAddress + 0x43FC = BitVec.ofNat 32 memcpyStubAddress by decide]
           exact cd E.mcs (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 edDoubleAddress + 0x4404 = BitVec.ofNat 32 memcpyStubAddress + 8 by decide]
           exact cd E.mcb (by decide) (by decide) IM,
        hR4, by omega, fA k hk, fkW k 160 h1, fA j hj, fkW j 120 h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, fkR0 k 160 h1 _ (by decide), fkR0 j 120 h2 _ (by decide)⟩
      all_goals first
        | exact hiR0 (by decide) (by decide) (by decide)
        | exact fkCn _ _ (by omega) (by decide) (by decide)
  have envP : ∀ {M : Word → BitVec 8}, (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) → ∀ k j, k % 4 = 0 → j % 4 = 0 →
      k + 120 ≤ 0x2C0 → j + 160 ≤ 0x2C0 → (k + 120 ≤ j ∨ j + 160 ≤ k) →
      ApEnv M (BitVec.ofNat 32 asProjectiveAddress) F (F + BitVec.ofNat 32 k) (F + BitVec.ofNat 32 j) :=
    fun IM k j hk hj h1 h2 h3 => by
      refine ⟨by decide, cd E.ap (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 asProjectiveAddress + 0xFFFFD34C = BitVec.ofNat 32 feMulAddress by decide]
           exact cd E.mul (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 asProjectiveAddress + 0xFFFFDE3C = BitVec.ofNat 32 feReduceAddress by decide]
           exact cd E.red (by decide) (by decide) IM,
        hFa, by omega, fA k hk, fA j hj, ?_, ?_, ?_, by rw [eAP]; exact fkR k 120 h1 _ _ (by decide),
        by rw [eAP]; exact fkR j 160 h2 _ _ (by decide), fkF k 120 j 160 h1 h2 h3, ?_, ?_, ?_⟩
      all_goals first
        | (rw [eAP]; exact hiC (by decide) (by decide) (by decide))
        | exact fkCn _ _ (by omega) (by decide) (by decide)
  have envX : ∀ {M : Word → BitVec 8}, (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) → ∀ k j, k % 4 = 0 → j % 4 = 0 →
      k + 160 ≤ 0x2C0 → j + 160 ≤ 0x2C0 → (k + 160 ≤ j ∨ j + 160 ≤ k) →
      AxEnv M (BitVec.ofNat 32 asExtendedAddress) F (F + BitVec.ofNat 32 k) (F + BitVec.ofNat 32 j) :=
    fun IM k j hk hj h1 h2 h3 => by
      refine ⟨by decide, cd E.ax (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 asExtendedAddress + 0xFFFFD8E6 = BitVec.ofNat 32 feMulAddress by decide]
           exact cd E.mul (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 asExtendedAddress + 0xFFFFE3D6 = BitVec.ofNat 32 feReduceAddress by decide]
           exact cd E.red (by decide) (by decide) IM,
        hFa, by omega, fA k hk, fA j hj, ?_, ?_, ?_, by rw [eAX]; exact fkR k 160 h1 _ _ (by decide),
        by rw [eAX]; exact fkR j 160 h2 _ _ (by decide), fkF k 160 j 160 h1 h2 h3, ?_, ?_, ?_⟩
      all_goals first
        | (rw [eAX]; exact hiC (by decide) (by decide) (by decide))
        | exact fkCn _ _ (by omega) (by decide) (by decide)
  have envM : ∀ {M : Word → BitVec 8}, (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) → ∀ k i j, k % 4 = 0 → i % 4 = 0 →
      j % 4 = 0 → k + 40 ≤ 0x2C0 → i + 40 ≤ 0x2C0 → j + 40 ≤ 0x2C0 →
      FeMEnv M (BitVec.ofNat 32 feMulAddress) F (F + BitVec.ofNat 32 k) (F + BitVec.ofNat 32 i)
        (F + BitVec.ofNat 32 j) :=
    fun IM k i j hk hi hj h1 h2 h3 => by
      refine ⟨by decide, cd E.mul (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 feMulAddress + 0xAF0 = BitVec.ofNat 32 feReduceAddress by decide]
           exact cd E.red (by decide) (by decide) IM,
        hFa, by omega, fA k hk, fA i hi, fA j hj, ?_, ?_, ?_, ?_, by rw [eMR]; exact fkR k 40 h1 _ _ (by decide),
        by rw [eMR]; exact fkR i 40 h2 _ _ (by decide), by rw [eMR]; exact fkR j 40 h3 _ _ (by decide)⟩
      all_goals first
        | (rw [eMR]; exact hiC (by decide) (by decide) (by decide))
        | exact fkCn _ _ (by omega) (by decide) (by decide)
  have envC : ∀ {M : Word → BitVec 8}, (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) → ∀ i j, i % 4 = 0 → j % 4 = 0 →
      i + 40 ≤ 0x2C0 → j + 40 ≤ 0x2C0 →
      FCEEnv M (BitVec.ofNat 32 feCtEqAddress) F (F + BitVec.ofNat 32 i) (F + BitVec.ofNat 32 j) :=
    fun IM i j hi hj h1 h2 => by
      refine ⟨by decide, cd E.ce (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 feCtEqAddress + 0xFFFFE096 = BitVec.ofNat 32 feToBytesAddress by decide]
           exact cd E.tb (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 feCtEqAddress + 0xFFFFE096 + 0x210 = BitVec.ofNat 32 feReduceAddress by decide]
           exact cd E.red (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 feCtEqAddress + 0xFFFFEF72 = BitVec.ofNat 32 ctEqSliceAddress by decide]
           exact cd E.cs (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 feCtEqAddress + 0xFFFFEF72 + 0xFFFFFFE8 = BitVec.ofNat 32 ctEqU8Address by decide]
           exact cd E.cu (by decide) (by decide) IM,
        by rw [show BitVec.ofNat 32 feCtEqAddress + 0xFFFFEF72 + 0xFFFFE836 = BitVec.ofNat 32 blackBoxU8Address by decide]
           exact cd E.bb (by decide) (by decide) IM,
        hFa, by omega, fA i hi, fA j hj, ?_, ?_, ?_, ?_, ?_, ?_, by rw [eCR]; exact fkR i 40 h1 _ _ (by decide),
        by rw [eCR]; exact fkR j 40 h2 _ _ (by decide)⟩
      all_goals (rw [eCR]; exact hiC (by decide) (by decide) (by decide))
  have eFo : ∀ k o, F + BitVec.ofNat 32 k + BitVec.ofNat 32 o = F + BitVec.ofNat 32 (k + o) := fun k o =>
    add_ofNat_assoc F k o
  have l28 : ∀ k, F + BitVec.ofNat 32 k + 0x28 = F + BitVec.ofNat 32 (k + 0x28) := fun k => eFo k 0x28
  have l50 : ∀ k, F + BitVec.ofNat 32 k + 0x50 = F + BitVec.ofNat 32 (k + 0x50) := fun k => eFo k 0x50
  have l78 : ∀ k, F + BitVec.ofNat 32 k + 0x78 = F + BitVec.ofNat 32 (k + 0x78) := fun k => eFo k 0x78
  have frR : ∀ {M M' : Word → BitVec 8} {W : Word} {wl : Nat} k n, k + n ≤ 0x2C0 → wl ≤ 0x210 →
      (∀ x, Sep W wl x 1 → Sep (F + BitVec.ofNat 32 k) n x 1 → M' x = M x) → W = R →
      (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) → ∀ x, Sep R 0x4D0 x 1 → M' x = m.mem x :=
    fun {M M' W wl} k n h hw hM hW IM x hx => by
      rw [hM x (by rw [hW]; have := inR (c := 0) (l := wl) hx (by omega); rwa [add_ofNat_zero] at this)
        (by rw [eFk]; exact inR hx (by omega)), IM x hx]
  -- one round of the loop: double, then `as_projective`
  have iter : ∀ {M : Word → BitVec 8} {n : Machine} {X Y Z : List Nat} {c : Word},
      St M ISO n 0x50 (reg n) → (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) → reg n sp = F →
      reg n (8 : Fin 32) = c → (∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q) →
      feW M (F + BitVec.ofNat 32 0x144) = X → feW M (F + BitVec.ofNat 32 0x16C) = Y →
      feW M (F + BitVec.ofNat 32 0x194) = Z →
      ∃ n' M', Steps n n' ∧ St M' ISO n' 0x6A (reg n') ∧ (∀ x, Sep R 0x4D0 x 1 → M' x = m.mem x) ∧
        reg n' sp = F ∧ reg n' (8 : Fin 32) = c + 0xFFFFFFFF ∧
        (∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q) ∧
        feW M' (F + BitVec.ofNat 32 0x144) = (isoStep X Y Z).1 ∧
        feW M' (F + BitVec.ofNat 32 0x16C) = (isoStep X Y Z).2.1 ∧
        feW M' (F + BitVec.ofNat 32 0x194) = (isoStep X Y Z).2.2 ∧
        (∀ c, 0x4BC ≤ c → c < 0x4D0 → M' (R + BitVec.ofNat 32 c) = M (R + BitVec.ofNat 32 c)) := by
    intro M n X Y Z c s IM rsp r8 Kl fX fY fZ
    have hcM : CodeIn M ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM
    obtain ⟨n1, c1, u1⟩ := St.block isoD1 s hcM isoD1_end (by simp only [BlockOk, BInstr.ok, isoD1, and_self])
    have R1 : ∀ q, reg n1 q = (runBlock isoD1 (M, reg n)).2 q := u1.regs
    have u1' : St M ISO n1 0x54 (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
    have K1 : ∀ q, q ≠ a0 → q ≠ a1 → reg n1 q = reg n q := fun q h0 h1 => by
      rw [R1]; refine runBlock_reg _ _ _ q s.zero ?_
      simp only [isoD1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
    have v1 : reg n1 a0 = F + BitVec.ofNat 32 0xA4 ∧ reg n1 a1 = F + BitVec.ofNat 32 0x144 := by
      simp +decide only [R1, runBlock, BInstr.run, isoD1, upd_app, ↓reduceIte, ev_add]; rw [rsp]; exact ⟨rfl, rfl⟩
    have sp1 : reg n1 sp = F := by rw [K1 sp (by decide) (by decide), rsp]
    obtain ⟨n2, c2, u2, sp2, k2, dbl, fr2⟩ := u1'.callEdDouble hcM (cb := BitVec.ofNat 32 edDoubleAddress) iso_at_54 iso_at_58 (by decide) (by decide)
      (by rw [sp1, eRF, v1.1, v1.2]; exact envD IM 0xA4 0x144 (by decide) (by decide) (by decide) (by decide))
    rw [v1.1, v1.2, l28, l50, l28, l50, l78, fX] at dbl
    rw [show F + BitVec.ofNat 32 (0x144 + 0x28) = F + BitVec.ofNat 32 0x16C from rfl,
      show F + BitVec.ofNat 32 (0x144 + 0x50) = F + BitVec.ofNat 32 0x194 from rfl, fY, fZ] at dbl
    rw [sp1, eRF, v1.1] at fr2
    have IM2 := frR (M := M) 0xA4 160 (by decide) (Nat.le_refl _) fr2 rfl IM
    have hcM2 : CodeIn n2.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM2
    obtain ⟨n3, c3, u3⟩ := St.block isoD2 u2 hcM2 isoD2_end (by simp only [BlockOk, BInstr.ok, isoD2, and_self])
    have R3 : ∀ q, reg n3 q = (runBlock isoD2 (n2.mem, reg n2)).2 q := u3.regs
    have u3' : St n2.mem ISO n3 0x60 (reg n3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
    have K3 : ∀ q, q ≠ a0 → q ≠ a1 → reg n3 q = reg n2 q := fun q h0 h1 => by
      rw [R3]; refine runBlock_reg _ _ _ q u2.zero ?_
      simp only [isoD2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
    have sp2' : reg n2 sp = F := by rw [sp2, sp1]
    have v3 : reg n3 a0 = F + BitVec.ofNat 32 0x144 ∧ reg n3 a1 = F + BitVec.ofNat 32 0xA4 := by
      simp +decide only [R3, runBlock, BInstr.run, isoD2, upd_app, ↓reduceIte, ev_add]; rw [sp2']; exact ⟨rfl, rfl⟩
    have sp3 : reg n3 sp = F := by rw [K3 sp (by decide) (by decide), sp2']
    obtain ⟨n4, c4, u4, sp4, k4, w0, w1, w2, fr4⟩ := u3'.callAsProj hcM2 (cb := BitVec.ofNat 32 asProjectiveAddress) iso_at_60 iso_at_64 (by decide) (by decide)
      (by rw [sp3, v3.1, v3.2]; exact envP IM2 0x144 0xA4 (by decide) (by decide) (by decide) (by decide) (.inr (by decide)))
    rw [v3.1, v3.2, l78] at w0
    rw [v3.1, v3.2, l28, l28, l50] at w1
    rw [v3.1, v3.2, l50, l50, l78] at w2
    rw [sp3, v3.1, eAP] at fr4
    have IM4 : ∀ x, Sep R 0x4D0 x 1 → n4.mem x = m.mem x := fun x hx => by
      rw [fr4 x (inR hx (by decide)) (by rw [eFk]; exact inR hx (by decide)), IM2 x hx]
    have hcM4 : CodeIn n4.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM4
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hcM4 iso_at_68 (off' := 0x6A) (by decide)
    have K5 : ∀ q, q ≠ (8 : Fin 32) → reg n5 q = reg n4 q := fun q h => by rw [u5.regs, updz u4.zero h]
    have K4 : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ sp → reg n4 q = reg n q :=
      fun q hq hs => by
        rw [k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
          K3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
          k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
          K1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    refine ⟨n5, n4.mem, c1.trans (c2.trans (c3.trans (c4.trans (.single d5)))), u5.self, IM4, ?_, ?_, ?_, ?_, ?_, ?_,
      fun c h1 h2 => ?_⟩
    · rw [K5 sp (by decide), sp4, sp3]
    · rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [K4 _ (by decide) (by decide), r8]; rfl
    · intro q hq
      rw [K5 q (by revert hq; revert q; decide), K4 q (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), Kl q hq]
    · rw [w0]; show _ = mulL (edDoubleSpec X Y Z).1 (edDoubleSpec X Y Z).2.2.2; rw [dbl]
    · rw [w1]; show _ = mulL (edDoubleSpec X Y Z).2.1 (edDoubleSpec X Y Z).2.2.1; rw [dbl]
    · rw [w2]; show _ = mulL (edDoubleSpec X Y Z).2.2.1 (edDoubleSpec X Y Z).2.2.2; rw [dbl]
    · rw [fr4 _ (offs (by omega) (by omega) (by omega)) (by rw [eFk]; exact offs (by omega) (by omega) (by omega)),
        fr2 _ (by have := offs (c := 0) (n := 0x210) (d := c) (k := 1) (by omega) (by omega) (by omega)
                  rwa [add_ofNat_zero] at this) (by rw [eFk]; exact offs (by omega) (by omega) (by omega))]
  obtain ⟨m10, d10, u10⟩ := u9.aluImm hc9 iso_at_4c (off' := 0x4E) (by decide)
  have v10 : reg m10 (8 : Fin 32) = 2 := by rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u9.zero]; rfl
  have K10 : ∀ q, q ≠ (8 : Fin 32) → reg m10 q = reg m9 q := fun q h => by rw [u10.regs, updz u9.zero h]
  obtain ⟨m11, d11, u11⟩ := u10.self.notTaken hc9 0x50 iso_at_4e (by decide) (by
    simp only [branchTaken]; rw [v10, u10.self.zero]; decide)
  obtain ⟨n12, M12, c12, u12, IM12, sp12, s012, Kl12, x12, y12, z12, sl12⟩ := iter u11.self IM9
    (by rw [u11.regs, K10 sp (by decide), v9]) (by rw [u11.regs, v10])
    (fun q hq => by rw [u11.regs, K10 q (by revert hq; revert q; decide), Kl9 q hq]) cX cY cZ
  have hc12 : CodeIn M12 ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM12
  obtain ⟨m13, d13, u13⟩ := u12.taken hc12 0x50 iso_at_6a (by decide) (by
    simp only [branchTaken]; rw [s012, u12.zero]; decide)
  obtain ⟨n14, M14, c14, u14, IM14, sp14, s014, Kl14, x14, y14, z14, sl14⟩ := iter u13.self IM12
    (by rw [u13.regs, sp12]) (by rw [u13.regs, s012]) (fun q hq => by rw [u13.regs, Kl12 q hq]) x12 y12 z12
  have hc14 : CodeIn M14 ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM14
  obtain ⟨m15, d15, u15⟩ := u14.notTaken hc14 0x6C iso_at_6a (by decide) (by
    simp only [branchTaken]; rw [s014, u14.zero]; decide)
  -- the last doubling, then `as_extended`
  obtain ⟨m16, c16, u16⟩ := St.block isoE1 u15.self hc14 isoE1_end (by simp only [BlockOk, BInstr.ok, isoE1, and_self])
  have R16 : ∀ q, reg m16 q = (runBlock isoE1 (M14, reg m15)).2 q := u16.regs
  have u16' : St M14 ISO m16 0x70 (reg m16) := ⟨u16.pc, by rw [u16.mem]; rfl, fun _ => rfl⟩
  have K16 : ∀ q, q ≠ a0 → q ≠ a1 → reg m16 q = reg n14 q := fun q h0 h1 => by
    rw [R16, runBlock_reg _ _ _ q u15.self.zero (by
      simp only [isoE1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]), u15.regs]
  have v16 : reg m16 a0 = F + BitVec.ofNat 32 0x1BC ∧ reg m16 a1 = F + BitVec.ofNat 32 0x144 := by
    simp +decide only [R16, runBlock, BInstr.run, isoE1, upd_app, ↓reduceIte, ev_add]; rw [u15.regs, sp14]
    exact ⟨rfl, rfl⟩
  have sp16 : reg m16 sp = F := by rw [K16 sp (by decide) (by decide), sp14]
  obtain ⟨n17, c17, u17, sp17, k17, dbl, fr17⟩ := u16'.callEdDouble hc14 (cb := BitVec.ofNat 32 edDoubleAddress)
    iso_at_70 iso_at_74 (by decide) (by decide)
    (by rw [sp16, eRF, v16.1, v16.2]; exact envD IM14 0x1BC 0x144 (by decide) (by decide) (by decide) (by decide))
  rw [v16.1, v16.2, l28, l50, l28, l50, l78, x14] at dbl
  rw [show F + BitVec.ofNat 32 (0x144 + 0x28) = F + BitVec.ofNat 32 0x16C from rfl,
    show F + BitVec.ofNat 32 (0x144 + 0x50) = F + BitVec.ofNat 32 0x194 from rfl, y14, z14] at dbl
  rw [sp16, eRF, v16.1] at fr17
  have IM17 := frR (M := M14) 0x1BC 160 (by decide) (Nat.le_refl _) fr17 rfl IM14
  have hc17 : CodeIn n17.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM17
  obtain ⟨m18, c18, u18⟩ := St.block isoE2 u17 hc17 isoE2_end (by simp only [BlockOk, BInstr.ok, isoE2, and_self])
  have R18 : ∀ q, reg m18 q = (runBlock isoE2 (n17.mem, reg n17)).2 q := u18.regs
  have u18' : St n17.mem ISO m18 0x7C (reg m18) := ⟨u18.pc, by rw [u18.mem]; rfl, fun _ => rfl⟩
  have K18 : ∀ q, q ≠ a0 → q ≠ a1 → reg m18 q = reg n17 q := fun q h0 h1 => by
    rw [R18]; refine runBlock_reg _ _ _ q u17.zero ?_
    simp only [isoE2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
  have sp17' : reg n17 sp = F := by rw [sp17, sp16]
  have v18 : reg m18 a0 = F + BitVec.ofNat 32 0x4 ∧ reg m18 a1 = F + BitVec.ofNat 32 0x1BC := by
    simp +decide only [R18, runBlock, BInstr.run, isoE2, upd_app, ↓reduceIte, ev_add]; rw [sp17']; exact ⟨rfl, rfl⟩
  have sp18 : reg m18 sp = F := by rw [K18 sp (by decide) (by decide), sp17']
  obtain ⟨n19, c19, u19, sp19, k19, e0, e1, e2, e3, fr19⟩ := u18'.callAsExt hc17 (cb := BitVec.ofNat 32 asExtendedAddress)
    iso_at_7c iso_at_80 (by decide) (by decide)
    (by rw [sp18, v18.1, v18.2]; exact envX IM17 0x4 0x1BC (by decide) (by decide) (by decide) (by decide) (.inl (by decide)))
  rw [v18.1, v18.2, l78] at e0
  rw [v18.1, v18.2, l28, l28, l50] at e1
  rw [v18.1, v18.2, l50, l50, l78] at e2
  rw [sp18, v18.1, eAX] at fr19
  have IM19 : ∀ x, Sep R 0x4D0 x 1 → n19.mem x = m.mem x := fun x hx => by
    rw [fr19 x (inR hx (by decide)) (by rw [eFk]; exact inR hx (by decide)), IM17 x hx]
  have hc19 : CodeIn n19.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM19
  -- the cofactor multiple's coordinates
  obtain ⟨T8, hT8⟩ : ∃ T8, isoTimes8 (feW m.mem p) (feW m.mem (p + 0x28)) (feW m.mem (p + 0x50)) = T8 := ⟨_, rfl⟩
  have eX : feW n19.mem (F + BitVec.ofNat 32 0x4) = T8.1 := by
    rw [e0, ← hT8]; show _ = mulL (edDoubleSpec _ _ _).1 (edDoubleSpec _ _ _).2.2.2; rw [dbl]
  have eY : feW n19.mem (F + BitVec.ofNat 32 (0x4 + 0x28)) = T8.2.1 := by
    rw [e1, ← hT8]; show _ = mulL (edDoubleSpec _ _ _).2.1 (edDoubleSpec _ _ _).2.2.1; rw [dbl]
  have eZ : feW n19.mem (F + BitVec.ofNat 32 (0x4 + 0x50)) = T8.2.2 := by
    rw [e2, ← hT8]; show _ = mulL (edDoubleSpec _ _ _).2.2.1 (edDoubleSpec _ _ _).2.2.2; rw [dbl]
  have hONE : (BitVec.ofNat 32 edOneAddress : Word).toNat = edOneAddress := by decide
  have Kl19 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n19 q = reg m q := fun q hq => by
    rw [k19 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      K18 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      k17 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      K16 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), Kl14 q hq]
  have sp19' : reg n19 sp = F := by rw [sp19, sp18]
  -- the identity: `X = 0` at `F + 0x1BC`, `Y = Z = 1` at `F + 0x1E4` and `F + 0x20C`, `T = 0` at `F + 0x234`
  obtain ⟨m20, c20, u20⟩ := St.block isoF1 u19 hc19 isoF1_end (by simp only [BlockOk, BInstr.ok, isoF1, and_self])
  have R20 : ∀ q, reg m20 q = (runBlock isoF1 (n19.mem, reg n19)).2 q := u20.regs
  have u20' : St n19.mem ISO m20 0x8C (reg m20) := ⟨u20.pc, by rw [u20.mem]; rfl, fun _ => rfl⟩
  have K20 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m20 q = reg n19 q := fun q h0 h1 h2 => by
    rw [R20]; refine runBlock_reg _ _ _ q u19.zero ?_
    simp only [isoF1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2]
  have v20 : reg m20 a0 = F + BitVec.ofNat 32 0x1BC ∧ reg m20 a2 = BitVec.ofNat 32 (4 * 10) ∧ reg m20 a1 = 0 := by
    simp +decide only [R20, runBlock, BInstr.run, isoF1, upd_app, ↓reduceIte, ev_add]; rw [sp19']
    exact ⟨rfl, trivial⟩
  obtain ⟨m21, c21, u21, _, k21⟩ := u20'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 10)
    (dst := F + BitVec.ofNat 32 0x1BC) (by decide) hc19 (cd E.mset (by rw [hMSn]; decide) (by rw [hMSn]; decide) IM19)
    iso_at_8c iso_at_90 (by decide) (by decide) (by decide) (fW 0x1BC (by decide)) (by decide) (fA _ (by decide))
    (fkC _ (by decide) (by rw [hMSn]; decide) (by rw [hMSn]; decide)) v20.1 v20.2.2 v20.2.1
  obtain ⟨N21, hN21⟩ : ∃ N21, fillWords n19.mem (F + BitVec.ofNat 32 0x1BC) 0 10 = N21 := ⟨_, rfl⟩
  rw [hN21] at u21
  have IM21 : ∀ x, Sep R 0x4D0 x 1 → N21 x = m.mem x := fun x hx => by
    rw [← hN21, fillWords_outside 10 (fkI _ (by decide) hx), IM19 x hx]
  have hc21 : CodeIn N21 ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM21
  have sp21 : reg m21 sp = F := by
    rw [k21 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K20 sp (by decide) (by decide) (by decide), sp19']
  obtain ⟨m22, c22, u22⟩ := St.block isoF2 u21 hc21 isoF2_end (by simp only [BlockOk, BInstr.ok, isoF2, and_self])
  have R22 : ∀ q, reg m22 q = (runBlock isoF2 (N21, reg m21)).2 q := u22.regs
  have u22' : St N21 ISO m22 0xA8 (reg m22) := ⟨u22.pc, by rw [u22.mem]; rfl, fun _ => rfl⟩
  have K22 : ∀ q, q.val ∉ [9, 10, 11, 12, 18] → reg m22 q = reg m21 q := fun q hq => by
    rw [R22]; refine runBlock_reg _ _ _ q u21.zero ?_
    simp only [isoF2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v22 : reg m22 (18 : Fin 32) = F + BitVec.ofNat 32 0x1E4 ∧ reg m22 (9 : Fin 32) = BitVec.ofNat 32 edOneAddress ∧
      reg m22 a2 = BitVec.ofNat 32 (4 * 10) ∧ reg m22 a0 = F + BitVec.ofNat 32 0x1E4 ∧
      reg m22 a1 = BitVec.ofNat 32 edOneAddress := by
    simp +decide only [R22, runBlock, BInstr.run, isoF2, upd_app, ↓reduceIte, ev_add]; rw [sp21]
    exact ⟨rfl, trivial, trivial, zw _, trivial⟩
  obtain ⟨m23, c23, u23, _, k23⟩ := u22'.memcpyW (B := BitVec.ofNat 32 memcpyStubAddress) (w := 10)
    (dst := F + BitVec.ofNat 32 0x1E4) (src := BitVec.ofNat 32 edOneAddress) (by decide) hc21
    (cd E.mcs (by rw [hMCn]; decide) (by rw [hMCn]; decide) IM21) (cd E.mcb (by rw [hMCb]; decide) (by rw [hMCb]; decide) IM21)
    iso_at_a8 iso_at_ac (by decide) (by decide) (by decide) (fW 0x1E4 (by decide)) (by decide)
    (fA _ (by decide)) (by decide) (by rw [eFk]; exact (sOG.subR (c := 0x210 + 0x1E4) (l := 40) (by decide)).symm)
    (fkC _ (by decide) (by rw [hMCb]; decide) (by rw [hMCb]; decide)) v22.2.2.2.1 v22.2.2.2.2 v22.2.2.1
  obtain ⟨N23, hN23⟩ : ∃ N23, copyWords N21 (F + BitVec.ofNat 32 0x1E4) (BitVec.ofNat 32 edOneAddress) 10 = N23 :=
    ⟨_, rfl⟩
  rw [hN23] at u23
  have IM23 : ∀ x, Sep R 0x4D0 x 1 → N23 x = m.mem x := fun x hx => by
    rw [← hN23, copyWords_outside 10 (fkI _ (by decide) hx), IM21 x hx]
  have hc23 : CodeIn N23 ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM23
  have oneW : ∀ {M : Word → BitVec 8}, (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) →
      feW M (BitVec.ofNat 32 edOneAddress) = feOneL := fun IM => by
    rw [pers (W := R) (V := R) (wl := 0x4D0) (vl := 0x4D0) (fun z h _ => IM z h) sOG sOG]; exact E.one
  have K23 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ ra →
      reg m23 q = reg m22 q := fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => k23 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨m24, c24, u24⟩ := St.block isoF3 u23 hc23 isoF3_end (by simp only [BlockOk, BInstr.ok, isoF3, and_self])
  have R24 : ∀ q, reg m24 q = (runBlock isoF3 (N23, reg m23)).2 q := u24.regs
  have u24' : St N23 ISO m24 0xBC (reg m24) := ⟨u24.pc, by rw [u24.mem]; rfl, fun _ => rfl⟩
  have K24 : ∀ q, q.val ∉ [10, 11, 12, 19] → reg m24 q = reg m23 q := fun q hq => by
    rw [R24]; refine runBlock_reg _ _ _ q u23.zero ?_
    simp only [isoF3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have sp23 : reg m23 sp = F := by
    rw [K23 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), K22 sp (by decide), sp21]
  have r23_9 : reg m23 (9 : Fin 32) = BitVec.ofNat 32 edOneAddress := by
    rw [K23 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), v22.2.1]
  have v24 : reg m24 (19 : Fin 32) = F + BitVec.ofNat 32 0x20C ∧ reg m24 a2 = BitVec.ofNat 32 (4 * 10) ∧
      reg m24 a0 = F + BitVec.ofNat 32 0x20C ∧ reg m24 a1 = BitVec.ofNat 32 edOneAddress := by
    simp +decide only [R24, runBlock, BInstr.run, isoF3, upd_app, ↓reduceIte, ev_add]; rw [sp23, r23_9]
    exact ⟨rfl, trivial, zw _, zw _⟩
  obtain ⟨m25, c25, u25, _, k25⟩ := u24'.memcpyW (B := BitVec.ofNat 32 memcpyStubAddress) (w := 10)
    (dst := F + BitVec.ofNat 32 0x20C) (src := BitVec.ofNat 32 edOneAddress) (by decide) hc23
    (cd E.mcs (by rw [hMCn]; decide) (by rw [hMCn]; decide) IM23) (cd E.mcb (by rw [hMCb]; decide) (by rw [hMCb]; decide) IM23)
    iso_at_bc iso_at_c0 (by decide) (by decide) (by decide) (fW 0x20C (by decide)) (by decide)
    (fA _ (by decide)) (by decide) (by rw [eFk]; exact (sOG.subR (c := 0x210 + 0x20C) (l := 40) (by decide)).symm)
    (fkC _ (by decide) (by rw [hMCb]; decide) (by rw [hMCb]; decide)) v24.2.2.1 v24.2.2.2 v24.2.1
  obtain ⟨N25, hN25⟩ : ∃ N25, copyWords N23 (F + BitVec.ofNat 32 0x20C) (BitVec.ofNat 32 edOneAddress) 10 = N25 :=
    ⟨_, rfl⟩
  rw [hN25] at u25
  have IM25 : ∀ x, Sep R 0x4D0 x 1 → N25 x = m.mem x := fun x hx => by
    rw [← hN25, copyWords_outside 10 (fkI _ (by decide) hx), IM23 x hx]
  have hc25 : CodeIn N25 ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM25
  have K25 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ ra →
      reg m25 q = reg m24 q := fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => k25 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have sp25 : reg m25 sp = F := by
    rw [K25 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), K24 sp (by decide), sp23]
  obtain ⟨m26, c26, u26⟩ := St.block isoF4 u25 hc25 isoF4_end (by simp only [BlockOk, BInstr.ok, isoF4, and_self])
  have R26 : ∀ q, reg m26 q = (runBlock isoF4 (N25, reg m25)).2 q := u26.regs
  have u26' : St N25 ISO m26 0xCC (reg m26) := ⟨u26.pc, by rw [u26.mem]; rfl, fun _ => rfl⟩
  have K26 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m26 q = reg m25 q := fun q h0 h1 h2 => by
    rw [R26]; refine runBlock_reg _ _ _ q u25.zero ?_
    simp only [isoF4, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2]
  have v26 : reg m26 a0 = F + BitVec.ofNat 32 0x234 ∧ reg m26 a2 = BitVec.ofNat 32 (4 * 10) ∧ reg m26 a1 = 0 := by
    simp +decide only [R26, runBlock, BInstr.run, isoF4, upd_app, ↓reduceIte, ev_add]; rw [sp25]
    exact ⟨rfl, trivial⟩
  obtain ⟨m27, c27, u27, _, k27⟩ := u26'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 10)
    (dst := F + BitVec.ofNat 32 0x234) (by decide) hc25 (cd E.mset (by rw [hMSn]; decide) (by rw [hMSn]; decide) IM25)
    iso_at_cc iso_at_d0 (by decide) (by decide) (by decide) (fW 0x234 (by decide)) (by decide) (fA _ (by decide))
    (fkC _ (by decide) (by rw [hMSn]; decide) (by rw [hMSn]; decide)) v26.1 v26.2.2 v26.2.1
  obtain ⟨N27, hN27⟩ : ∃ N27, fillWords N25 (F + BitVec.ofNat 32 0x234) 0 10 = N27 := ⟨_, rfl⟩
  rw [hN27] at u27
  have IM27 : ∀ x, Sep R 0x4D0 x 1 → N27 x = m.mem x := fun x hx => by
    rw [← hN27, fillWords_outside 10 (fkI _ (by decide) hx), IM25 x hx]
  have hc27 : CodeIn N27 ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM27
  -- the field elements the products read, in `N27`
  have kF : ∀ {M M' : Word → BitVec 8} {d : Word}, (∀ z, Sep d 40 z 1 → M' z = M z) → ∀ k k', k + 40 ≤ 0x2C0 →
      k' + 40 ≤ 0x2C0 → (k + 40 ≤ k' ∨ k' + 40 ≤ k) → d = F + BitVec.ofNat 32 k' →
      feW M' (F + BitVec.ofNat 32 k) = feW M (F + BitVec.ofNat 32 k) := fun {M M' d} hM k k' h1 h2 h3 hd =>
    pers (W := d) (V := d) (wl := 40) (vl := 40) (fun z h _ => hM z h) (by rw [hd]; exact fkF k 40 k' 40 h1 h2 h3)
      (by rw [hd]; exact fkF k 40 k' 40 h1 h2 h3)
  have z27 : feW N27 (F + BitVec.ofNat 32 0x1BC) = feZeroL := by
    rw [← hN27, kF (fun z h => fillWords_outside 10 h) 0x1BC 0x234 (by decide) (by decide) (by decide) rfl, ← hN25,
      kF (fun z h => copyWords_outside 10 h) 0x1BC 0x20C (by decide) (by decide) (by decide) rfl, ← hN23,
      kF (fun z h => copyWords_outside 10 h) 0x1BC 0x1E4 (by decide) (by decide) (by decide) rfl, ← hN21,
      feW_fill0 (Nat.le_of_lt (fW _ (by decide)))]
  have oY27 : feW N27 (F + BitVec.ofNat 32 0x1E4) = feOneL := by
    rw [← hN27, kF (fun z h => fillWords_outside 10 h) 0x1E4 0x234 (by decide) (by decide) (by decide) rfl, ← hN25,
      kF (fun z h => copyWords_outside 10 h) 0x1E4 0x20C (by decide) (by decide) (by decide) rfl, ← hN23,
      feW_copyW (Nat.le_of_lt (fW _ (by decide))), oneW IM21]
  have oZ27 : feW N27 (F + BitVec.ofNat 32 0x20C) = feOneL := by
    rw [← hN27, kF (fun z h => fillWords_outside 10 h) 0x20C 0x234 (by decide) (by decide) (by decide) rfl, ← hN25,
      feW_copyW (Nat.le_of_lt (fW _ (by decide))), oneW IM23]
  have keep27 : ∀ k, k + 40 ≤ 0x1BC → feW N27 (F + BitVec.ofNat 32 k) = feW n19.mem (F + BitVec.ofNat 32 k) :=
    fun k hk => by
      rw [← hN27, kF (fun z h => fillWords_outside 10 h) k 0x234 (by omega) (by decide) (by omega) rfl, ← hN25,
        kF (fun z h => copyWords_outside 10 h) k 0x20C (by omega) (by decide) (by omega) rfl, ← hN23,
        kF (fun z h => copyWords_outside 10 h) k 0x1E4 (by omega) (by decide) (by omega) rfl, ← hN21,
        kF (fun z h => fillWords_outside 10 h) k 0x1BC (by omega) (by decide) (by omega) rfl]
  have eX27 : feW N27 (F + BitVec.ofNat 32 0x4) = T8.1 := by rw [keep27 _ (by decide), eX]
  have eY27 : feW N27 (F + BitVec.ofNat 32 0x2C) = T8.2.1 := by rw [keep27 _ (by decide)]; exact eY
  have eZ27 : feW N27 (F + BitVec.ofNat 32 0x54) = T8.2.2 := by rw [keep27 _ (by decide)]; exact eZ
  -- frames of the calls that follow, for field elements at `F + k`
  have keepM : ∀ {M M' : Word → BitVec 8} {o : Word} k ko, (∀ x, Sep (F + 0xFFFFFEC0) 0x140 x 1 → Sep o 40 x 1 →
      M' x = M x) → o = F + BitVec.ofNat 32 ko → k + 40 ≤ 0x2C0 → ko + 40 ≤ 0x2C0 → (k + 40 ≤ ko ∨ ko + 40 ≤ k) →
      feW M' (F + BitVec.ofNat 32 k) = feW M (F + BitVec.ofNat 32 k) := fun {M M' o} k ko hM ho h1 h2 h3 =>
    pers (W := F + 0xFFFFFEC0) (V := o) (wl := 0x140) (vl := 40) hM (by rw [eMR]; exact fkR k 40 h1 _ _ (by decide))
      (by rw [ho]; exact fkF k 40 ko 40 h1 h2 h3)
  have keepC : ∀ {M M' : Word → BitVec 8} k, (∀ x, Sep (F + 0xFFFFFF00) 0x100 x 1 → M' x = M x) → k + 40 ≤ 0x2C0 →
      feW M' (F + BitVec.ofNat 32 k) = feW M (F + BitVec.ofNat 32 k) := fun {M M'} k hM h1 =>
    pers (W := F + 0xFFFFFF00) (V := F + 0xFFFFFF00) (wl := 0x100) (vl := 0x100) (fun x h _ => hM x h)
      (by rw [eCR]; exact fkR k 40 h1 _ _ (by decide)) (by rw [eCR]; exact fkR k 40 h1 _ _ (by decide))
  have IMm : ∀ {M M' : Word → BitVec 8} {o : Word} ko, (∀ x, Sep (F + 0xFFFFFEC0) 0x140 x 1 → Sep o 40 x 1 →
      M' x = M x) → o = F + BitVec.ofNat 32 ko → ko + 40 ≤ 0x2C0 → (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) →
      ∀ x, Sep R 0x4D0 x 1 → M' x = m.mem x := fun {M M' o} ko hM ho h IM x hx => by
    rw [hM x (by rw [eMR]; exact inR hx (by decide)) (by rw [ho, eFk]; exact inR hx (by omega)), IM x hx]
  have IMc : ∀ {M M' : Word → BitVec 8}, (∀ x, Sep (F + 0xFFFFFF00) 0x100 x 1 → M' x = M x) →
      (∀ x, Sep R 0x4D0 x 1 → M x = m.mem x) → ∀ x, Sep R 0x4D0 x 1 → M' x = m.mem x := fun hM IM x hx => by
    rw [hM x (by rw [eCR]; exact inR hx (by decide)), IM x hx]
  have Kl21 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m21 q = reg n19 q := fun q hq => by
    rw [k21 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      K20 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have Kl27 : ∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg m27 q = reg m q := fun q hq => by
    rw [k27 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      K26 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      K25 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), K24 q (by intro h; revert h; revert hq; revert q; decide),
      K23 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), K22 q (by intro h; revert h; revert hq; revert q; decide),
      Kl21 q (by revert hq; revert q; decide), Kl19 q (by revert hq; revert q; decide)]
  have sp27 : reg m27 sp = F := by
    rw [k27 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K26 sp (by decide) (by decide) (by decide), sp25]
  have r27_19 : reg m27 (19 : Fin 32) = F + BitVec.ofNat 32 0x20C := by
    rw [k27 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K26 _ (by decide) (by decide) (by decide), K25 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), v24.1]
  have r27_18 : reg m27 (18 : Fin 32) = F + BitVec.ofNat 32 0x1E4 := by
    rw [k27 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K26 _ (by decide) (by decide) (by decide), K25 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), K24 _ (by decide),
      K23 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), v22.1]
  -- `X · 1` and `0 · Z`
  obtain ⟨m28, c28, u28⟩ := St.block isoG1 u27 hc27 isoG1_end (by simp only [BlockOk, BInstr.ok, isoG1, and_self])
  have R28 : ∀ q, reg m28 q = (runBlock isoG1 (N27, reg m27)).2 q := u28.regs
  have u28' : St N27 ISO m28 0xDA (reg m28) := ⟨u28.pc, by rw [u28.mem]; rfl, fun _ => rfl⟩
  have K28 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m28 q = reg m27 q := fun q h0 h1 h2 => by
    rw [R28]; refine runBlock_reg _ _ _ q u27.zero ?_
    simp only [isoG1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2]
  have v28 : reg m28 a0 = F + BitVec.ofNat 32 0x25C ∧ reg m28 a1 = F + BitVec.ofNat 32 0x4 ∧
      reg m28 a2 = F + BitVec.ofNat 32 0x20C := by
    simp +decide only [R28, runBlock, BInstr.run, isoG1, upd_app, ↓reduceIte, ev_add]; rw [sp27, r27_19]
    exact ⟨rfl, rfl, zw _⟩
  have sp28 : reg m28 sp = F := by rw [K28 sp (by decide) (by decide) (by decide), sp27]
  have em29 := envM IM27 0x25C 0x4 0x20C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨m29, c29, u29, sp29, k29, w29, f29⟩ := u28'.callFeMulL hc27 (cb := BitVec.ofNat 32 feMulAddress)
    iso_at_da iso_at_de (by decide) (by decide) (by rw [sp28, v28.1, v28.2.1, v28.2.2]; exact em29)
  rw [v28.1, v28.2.1, v28.2.2, eX27, oZ27] at w29
  rw [sp28, v28.1] at f29
  have IM29 := IMm (M := N27) 0x25C f29 rfl (by decide) IM27
  have hc29 : CodeIn m29.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM29
  have k29' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m29 q = reg m28 q := fun q hq => by
    rw [k29 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  obtain ⟨m30, c30, u30⟩ := St.block isoG2 u29 hc29 isoG2_end (by simp only [BlockOk, BInstr.ok, isoG2, and_self])
  have R30 : ∀ q, reg m30 q = (runBlock isoG2 (m29.mem, reg m29)).2 q := u30.regs
  have u30' : St m29.mem ISO m30 0xEA (reg m30) := ⟨u30.pc, by rw [u30.mem]; rfl, fun _ => rfl⟩
  have K30 : ∀ q, q.val ∉ [9, 10, 11, 12] → reg m30 q = reg m29 q := fun q hq => by
    rw [R30]; refine runBlock_reg _ _ _ q u29.zero ?_
    simp only [isoG2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have sp29' : reg m29 sp = F := by rw [sp29, sp28]
  have v30 : reg m30 (9 : Fin 32) = F + BitVec.ofNat 32 0x54 ∧ reg m30 a0 = F + BitVec.ofNat 32 0x284 ∧
      reg m30 a1 = F + BitVec.ofNat 32 0x1BC ∧ reg m30 a2 = F + BitVec.ofNat 32 0x54 := by
    simp +decide only [R30, runBlock, BInstr.run, isoG2, upd_app, ↓reduceIte, ev_add]; rw [sp29']
    exact ⟨rfl, rfl, rfl, zw _⟩
  have sp30 : reg m30 sp = F := by rw [K30 sp (by decide), sp29']
  have em31 := envM IM29 0x284 0x1BC 0x54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨m31, c31, u31, sp31, k31, w31, f31⟩ := u30'.callFeMulL hc29 (cb := BitVec.ofNat 32 feMulAddress)
    iso_at_ea iso_at_ee (by decide) (by decide) (by rw [sp30, v30.2.1, v30.2.2.1, v30.2.2.2]; exact em31)
  rw [v30.2.1, v30.2.2.1, v30.2.2.2, keepM 0x1BC 0x25C f29 rfl (by decide) (by decide) (by decide), z27,
    keepM 0x54 0x25C f29 rfl (by decide) (by decide) (by decide), eZ27] at w31
  rw [sp30, v30.2.1] at f31
  have IM31 := IMm (M := m29.mem) 0x284 f31 rfl (by decide) IM29
  have hc31 : CodeIn m31.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM31
  have k31' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m31 q = reg m30 q := fun q hq => by
    rw [k31 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  obtain ⟨m32, c32, u32⟩ := St.block isoG3 u31 hc31 isoG3_end (by simp only [BlockOk, BInstr.ok, isoG3, and_self])
  have R32 : ∀ q, reg m32 q = (runBlock isoG3 (m31.mem, reg m31)).2 q := u32.regs
  have u32' : St m31.mem ISO m32 0xF6 (reg m32) := ⟨u32.pc, by rw [u32.mem]; rfl, fun _ => rfl⟩
  have K32 : ∀ q, q ≠ a0 → q ≠ a1 → reg m32 q = reg m31 q := fun q h0 h1 => by
    rw [R32]; refine runBlock_reg _ _ _ q u31.zero ?_
    simp only [isoG3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
  have sp31' : reg m31 sp = F := by rw [sp31, sp30]
  have v32 : reg m32 a0 = F + BitVec.ofNat 32 0x25C ∧ reg m32 a1 = F + BitVec.ofNat 32 0x284 := by
    simp +decide only [R32, runBlock, BInstr.run, isoG3, upd_app, ↓reduceIte, ev_add]; rw [sp31']; exact ⟨rfl, rfl⟩
  have sp32 : reg m32 sp = F := by rw [K32 sp (by decide) (by decide), sp31']
  have ec33 := envC IM31 0x25C 0x284 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨m33, c33, u33, sp33, a033, k33, f33⟩ := u32'.callFeCtEq hc31 (cb := BitVec.ofNat 32 feCtEqAddress)
    iso_at_f6 iso_at_fa (by decide) (by decide) (by rw [sp32, v32.1, v32.2]; exact ec33)
  rw [v32.1, v32.2, keepM 0x25C 0x284 f31 rfl (by decide) (by decide) (by decide), w29, w31] at a033
  rw [sp32] at f33
  have IM33 := IMc f33 IM31
  have hc33 : CodeIn m33.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM33
  have k33' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m33 q = reg m32 q := fun q hq =>
    k33 q (by revert hq; revert q; decide)
  -- registers since `m27`
  have Kr33 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m33 q = reg m27 q := fun q hq => by
    rw [k33' q (by revert hq; revert q; decide), K32 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      k31' q (by revert hq; revert q; decide), K30 q (by intro h; revert h; revert hq; revert q; decide),
      k29' q (by revert hq; revert q; decide), K28 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)]
  have r33_9 : reg m33 (9 : Fin 32) = F + BitVec.ofNat 32 0x54 := by
    rw [k33' _ (by decide), K32 _ (by decide) (by decide), k31' _ (by decide), v30.1]
  have sp33' : reg m33 sp = F := by rw [sp33, sp32]
  -- `Y · 1` and `1 · Z`
  obtain ⟨m34, c34, u34⟩ := St.block isoG4 u33 hc33 isoG4_end (by simp only [BlockOk, BInstr.ok, isoG4, and_self])
  have R34 : ∀ q, reg m34 q = (runBlock isoG4 (m33.mem, reg m33)).2 q := u34.regs
  have u34' : St m33.mem ISO m34 0x106 (reg m34) := ⟨u34.pc, by rw [u34.mem]; rfl, fun _ => rfl⟩
  have K34 : ∀ q, q.val ∉ [8, 10, 11, 12] → reg m34 q = reg m33 q := fun q hq => by
    rw [R34]; refine runBlock_reg _ _ _ q u33.zero ?_
    simp only [isoG4, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v34 : reg m34 (8 : Fin 32) = reg m33 a0 ∧ reg m34 a1 = F + BitVec.ofNat 32 0x2C ∧
      reg m34 a0 = F + BitVec.ofNat 32 0x144 ∧ reg m34 a2 = F + BitVec.ofNat 32 0x20C := by
    simp +decide only [R34, runBlock, BInstr.run, isoG4, upd_app, ↓reduceIte, ev_add]
    rw [sp33', Kr33 19 (by decide), r27_19, u33.zero]; exact ⟨zw _, rfl, rfl, zw _⟩
  have sp34 : reg m34 sp = F := by rw [K34 sp (by decide), sp33']
  have em35 := envM IM33 0x144 0x2C 0x20C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨m35, c35, u35, sp35, k35, w35, f35⟩ := u34'.callFeMulL hc33 (cb := BitVec.ofNat 32 feMulAddress)
    iso_at_106 iso_at_10a (by decide) (by decide) (by rw [sp34, v34.2.2.1, v34.2.1, v34.2.2.2]; exact em35)
  rw [v34.2.2.1, v34.2.1, v34.2.2.2, keepC 0x2C f33 (by decide),
    keepM 0x2C 0x284 f31 rfl (by decide) (by decide) (by decide),
    keepM 0x2C 0x25C f29 rfl (by decide) (by decide) (by decide), eY27, keepC 0x20C f33 (by decide),
    keepM 0x20C 0x284 f31 rfl (by decide) (by decide) (by decide),
    keepM 0x20C 0x25C f29 rfl (by decide) (by decide) (by decide), oZ27] at w35
  rw [sp34, v34.2.2.1] at f35
  have IM35 := IMm (M := m33.mem) 0x144 f35 rfl (by decide) IM33
  have hc35 : CodeIn m35.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM35
  have k35' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m35 q = reg m34 q := fun q hq => by
    rw [k35 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  obtain ⟨m36, c36, u36⟩ := St.block isoG5 u35 hc35 isoG5_end (by simp only [BlockOk, BInstr.ok, isoG5, and_self])
  have R36 : ∀ q, reg m36 q = (runBlock isoG5 (m35.mem, reg m35)).2 q := u36.regs
  have u36' : St m35.mem ISO m36 0x114 (reg m36) := ⟨u36.pc, by rw [u36.mem]; rfl, fun _ => rfl⟩
  have K36 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m36 q = reg m35 q := fun q h0 h1 h2 => by
    rw [R36]; refine runBlock_reg _ _ _ q u35.zero ?_
    simp only [isoG5, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2]
  have sp35' : reg m35 sp = F := by rw [sp35, sp34]
  have v36 : reg m36 a0 = F + BitVec.ofNat 32 0xA4 ∧ reg m36 a1 = F + BitVec.ofNat 32 0x1E4 ∧
      reg m36 a2 = F + BitVec.ofNat 32 0x54 := by
    simp +decide only [R36, runBlock, BInstr.run, isoG5, upd_app, ↓reduceIte, ev_add]
    rw [sp35', k35' 18 (by decide), K34 18 (by decide), Kr33 18 (by decide), r27_18, k35' 9 (by decide),
      K34 9 (by decide), r33_9]
    exact ⟨rfl, zw _, zw _⟩
  have sp36 : reg m36 sp = F := by rw [K36 sp (by decide) (by decide) (by decide), sp35']
  have em37 := envM IM35 0xA4 0x1E4 0x54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨m37, c37, u37, sp37, k37, w37, f37⟩ := u36'.callFeMulL hc35 (cb := BitVec.ofNat 32 feMulAddress)
    iso_at_114 iso_at_118 (by decide) (by decide) (by rw [sp36, v36.1, v36.2.1, v36.2.2]; exact em37)
  rw [v36.1, v36.2.1, v36.2.2, keepM 0x1E4 0x144 f35 rfl (by decide) (by decide) (by decide), keepC 0x1E4 f33 (by decide),
    keepM 0x1E4 0x284 f31 rfl (by decide) (by decide) (by decide),
    keepM 0x1E4 0x25C f29 rfl (by decide) (by decide) (by decide), oY27,
    keepM 0x54 0x144 f35 rfl (by decide) (by decide) (by decide), keepC 0x54 f33 (by decide),
    keepM 0x54 0x284 f31 rfl (by decide) (by decide) (by decide),
    keepM 0x54 0x25C f29 rfl (by decide) (by decide) (by decide), eZ27] at w37
  rw [sp36, v36.1] at f37
  have IM37 := IMm (M := m35.mem) 0xA4 f37 rfl (by decide) IM35
  have hc37 : CodeIn m37.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM37
  have k37' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m37 q = reg m36 q := fun q hq => by
    rw [k37 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  obtain ⟨m38, c38, u38⟩ := St.block isoG6 u37 hc37 isoG6_end (by simp only [BlockOk, BInstr.ok, isoG6, and_self])
  have R38 : ∀ q, reg m38 q = (runBlock isoG6 (m37.mem, reg m37)).2 q := u38.regs
  have u38' : St m37.mem ISO m38 0x120 (reg m38) := ⟨u38.pc, by rw [u38.mem]; rfl, fun _ => rfl⟩
  have K38 : ∀ q, q ≠ a0 → q ≠ a1 → reg m38 q = reg m37 q := fun q h0 h1 => by
    rw [R38]; refine runBlock_reg _ _ _ q u37.zero ?_
    simp only [isoG6, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
  have sp37' : reg m37 sp = F := by rw [sp37, sp36]
  have v38 : reg m38 a0 = F + BitVec.ofNat 32 0x144 ∧ reg m38 a1 = F + BitVec.ofNat 32 0xA4 := by
    simp +decide only [R38, runBlock, BInstr.run, isoG6, upd_app, ↓reduceIte, ev_add]; rw [sp37']; exact ⟨rfl, rfl⟩
  have sp38 : reg m38 sp = F := by rw [K38 sp (by decide) (by decide), sp37']
  have ec39 := envC IM37 0x144 0xA4 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨m39, c39, u39, sp39, a039, k39, f39⟩ := u38'.callFeCtEq hc37 (cb := BitVec.ofNat 32 feCtEqAddress)
    iso_at_120 iso_at_124 (by decide) (by decide) (by rw [sp38, v38.1, v38.2]; exact ec39)
  rw [v38.1, v38.2, keepM 0x144 0xA4 f37 rfl (by decide) (by decide) (by decide), w35, w37] at a039
  rw [sp38] at f39
  have IM39 := IMc f39 IM37
  have hc39 : CodeIn m39.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM39
  have k39' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m39 q = reg m38 q := fun q hq =>
    k39 q (by revert hq; revert q; decide)
  have Kr39 : ∀ q, q.val ∈ [3, 4, 8, 20, 21, 22, 23, 24, 25, 26, 27] → reg m39 q = reg m34 q := fun q hq => by
    rw [k39' q (by revert hq; revert q; decide), K38 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      k37' q (by revert hq; revert q; decide), K36 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), k35' q (by revert hq; revert q; decide)]
  have sp39' : reg m39 sp = F := by rw [sp39, sp38]
  -- combine the two comparisons and pass them through `black_box`
  have s039 : reg m39 (8 : Fin 32) = if (bytesL (mulL T8.1 feOneL) = bytesL (mulL feZeroL T8.2.2)) then 1 else 0 := by
    rw [Kr39 _ (by decide), v34.1, a033]
  obtain ⟨m40, c40, u40⟩ := St.block isoG7 u39 hc39 isoG7_end (by simp only [BlockOk, BInstr.ok, isoG7, and_self])
  have R40 : ∀ q, reg m40 q = (runBlock isoG7 (m39.mem, reg m39)).2 q := u40.regs
  have u40' : St m39.mem ISO m40 0x12E (reg m40) := ⟨u40.pc, by rw [u40.mem]; rfl, fun _ => rfl⟩
  have K40 : ∀ q, q ≠ a0 → reg m40 q = reg m39 q := fun q h0 => by
    rw [R40]; refine runBlock_reg _ _ _ q u39.zero ?_
    simp only [isoG7, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0]
  have v40 : reg m40 a0 = if (bytesL (mulL T8.1 feOneL) = bytesL (mulL feZeroL T8.2.2)) ∧ (bytesL (mulL T8.2.1 feOneL) = bytesL (mulL feOneL T8.2.2)) then 1 else 0 := by
    simp +decide only [R40, runBlock, BInstr.run, isoG7, upd_app, ↓reduceIte]; rw [a039, s039]
    by_cases ha : (bytesL (mulL T8.1 feOneL) = bytesL (mulL feZeroL T8.2.2)) <;> by_cases hb : (bytesL (mulL T8.2.1 feOneL) = bytesL (mulL feOneL T8.2.2)) <;> simp only [ha, hb, ite_true, ite_false, and_self, and_false, false_and] <;> decide
  have hBBa : (BitVec.ofNat 32 blackBoxU8Address : Word).toNat = blackBoxU8Address := by decide
  obtain ⟨m41, c41, pc41, mem41, regs41⟩ := u40'.callRa hc39 iso_at_12e iso_at_132
    (cb := BitVec.ofNat 32 blackBoxU8Address) (by decide) (by decide)
  have r41 := PEnv.reg1 regs41 u40'.zero
  have sp40 : reg m40 sp = F := by rw [K40 sp (by decide), sp39']
  have eFm1 : F + 0xFFFFFFFF = R + BitVec.ofNat 32 0x20F := by rw [← hRF, BitVec.add_assoc]; rfl
  obtain ⟨m42, c42, pc42, a042, K42, fr42⟩ := blackBoxU8_correct m41 (base := BitVec.ofNat 32 blackBoxU8Address)
    (retAddr := ISO + BitVec.ofNat 32 (0x12E + 8))
    (by rw [mem41]; exact cd E.bb (by rw [hBBa]; decide) (by rw [hBBa]; decide) IM39) pc41
    (by rw [regs41]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at ISO (by decide) _ (by decide)))
    (by rw [r41 sp (by decide), sp40, eFm1]; exact hiC (by decide) (by rw [hBBa]; decide) (by rw [hBBa]; decide))
  rw [r41 a0 (by decide), v40] at a042
  rw [r41 sp (by decide), sp40, eFm1, mem41] at fr42
  have IM42 : ∀ x, Sep R 0x4D0 x 1 → m42.mem x = m.mem x := fun x hx => by rw [fr42 x (inR hx (by decide)), IM39 x hx]
  have hc42 : CodeIn m42.mem ISO isSmallOrderCode := cd hc (by rw [hISn]; decide) (by rw [hISn]; decide) IM42
  have u42 : St m42.mem ISO m42 0x136 (reg m42) := ⟨by rw [pc42], rfl, fun _ => rfl⟩
  have K42' : ∀ q, q ≠ a0 → q ≠ ra → reg m42 q = reg m40 q := fun q h0 hr => by rw [K42 q h0, r41 q hr]
  obtain ⟨m43, c43, u43⟩ := St.block isoG8 u42 hc42 isoG8_end (by simp only [BlockOk, BInstr.ok, isoG8, and_self])
  have R43 : ∀ q, reg m43 q = (runBlock isoG8 (m42.mem, reg m42)).2 q := u43.regs
  have u43' : St m42.mem ISO m43 0x140 (reg m43) := ⟨u43.pc, by rw [u43.mem]; rfl, fun _ => rfl⟩
  have K43 : ∀ q, q ≠ a0 → q ≠ a1 → reg m43 q = reg m42 q := fun q h0 h1 => by
    rw [R43]; refine runBlock_reg _ _ _ q u42.zero ?_
    simp only [isoG8, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
  have sp42 : reg m42 sp = F := by rw [K42' sp (by decide) (by decide), sp40]
  have v43 : reg m43 a0 = (if (bytesL (mulL T8.1 feOneL) = bytesL (mulL feZeroL T8.2.2)) ∧ (bytesL (mulL T8.2.1 feOneL) = bytesL (mulL feOneL T8.2.2)) then 1 else 0) ∧ reg m43 a1 = F + 0x280 := by
    simp +decide only [R43, runBlock, BInstr.run, isoG8, upd_app, ↓reduceIte, ev_add]; rw [sp42, a042]
    refine ⟨?_, rfl⟩
    by_cases h : (bytesL (mulL T8.1 feOneL) = bytesL (mulL feZeroL T8.2.2)) ∧ (bytesL (mulL T8.2.1 feOneL) = bytesL (mulL feOneL T8.2.2))
    · rw [ite_eq_left h]; decide
    · rw [ite_eq_right h]; decide
  -- the saved registers' slots are as the prologue left them
  have slS : ∀ {a l c : Nat}, a + l ≤ 0x4BC → 0x4BC ≤ c → c < 0x4D0 →
      Sep (R + BitVec.ofNat 32 a) l (R + BitVec.ofNat 32 c) 1 := fun h1 h2 h3 => offs (by omega) (by omega) (by omega)
  have slF : ∀ {k l c : Nat}, 0x210 + k + l ≤ 0x4BC → 0x4BC ≤ c → c < 0x4D0 →
      Sep (F + BitVec.ofNat 32 k) l (R + BitVec.ofNat 32 c) 1 := fun h1 h2 h3 => by rw [eFk]; exact slS h1 h2 h3
  have slR0 : ∀ {l c : Nat}, l ≤ 0x4BC → 0x4BC ≤ c → c < 0x4D0 → Sep R l (R + BitVec.ofNat 32 c) 1 :=
    fun {l c} h1 h2 h3 => by
      have := slS (a := 0) (l := l) (by omega) h2 h3; rwa [add_ofNat_zero] at this
  have slotM : ∀ c, 0x4BC ≤ c → c < 0x4D0 → m42.mem (R + BitVec.ofNat 32 c) = Ms (R + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      rw [fr42 _ (slS (by decide) h1 h2), f39 _ (by rw [eCR]; exact slS (by decide) h1 h2),
        f37 _ (by rw [eMR]; exact slS (by decide) h1 h2) (slF (by decide) h1 h2), f35 _ (by rw [eMR]; exact slS (by decide) h1 h2)
          (slF (by decide) h1 h2), f33 _ (by rw [eCR]; exact slS (by decide) h1 h2),
        f31 _ (by rw [eMR]; exact slS (by decide) h1 h2) (slF (by decide) h1 h2),
        f29 _ (by rw [eMR]; exact slS (by decide) h1 h2) (slF (by decide) h1 h2), ← hN27,
        fillWords_outside 10 (slF (by decide) h1 h2), ← hN25, copyWords_outside 10 (slF (by decide) h1 h2), ← hN23,
        copyWords_outside 10 (slF (by decide) h1 h2), ← hN21, fillWords_outside 10 (slF (by decide) h1 h2),
        fr19 _ (slS (by decide) h1 h2) (slF (by decide) h1 h2),
        fr17 _ (slR0 (by decide) h1 h2) (slF (by decide) h1 h2), sl14 c h1 h2, sl12 c h1 h2, ← hM9,
        copyWords_outside 10 (slF (by decide) h1 h2), ← hM7, copyWords_outside 10 (slF (by decide) h1 h2), ← hM5,
        copyWords_outside 10 (slF (by decide) h1 h2)]
  have hpsA : ∀ q ∈ isoPs, q.1 ≠ a1 := by decide
  obtain ⟨m44, c44, u44⟩ := St.block (restoreBlockR a1 isoPs) u43' hc42 isoRestore_end
    (restoreBlockR_ok m42.mem (F + 0x280) a1 (by decide) isoPs (reg m43) v43.2 hpsA fun q hq => by
      simp only [isoPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> (rw [eA1]; exact fA _ (by decide)))
  rw [restoreBlockR_run m42.mem (F + 0x280) a1 (by decide) isoPs (reg m43) v43.2 hpsA] at u44
  have hc44 : CodeIn m42.mem ISO isSmallOrderCode := hc42
  obtain ⟨m45, d45, u45⟩ := u44.aluImm hc44 iso_at_150 (off' := 0x154) (by decide)
  obtain ⟨m46, d46, pc46, mem46, regs46⟩ := u45.self.jalr hc44 iso_at_154
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs m42.mem (F + 0x280) f ps q = f q := by
    intro f ps q hq0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
  have slot : ∀ o : Word, 0x2C ≤ o.toNat → o.toNat + 4 ≤ 0x40 →
      memLoad32 m42.mem (F + 0x280 + o) = memLoad32 Ms (F + 0x280 + o) := fun o h1 h2 => by
    apply memLoad32_congr; intro j hj
    rw [eA1, show F + (0x280 + o) = F + BitVec.ofNat 32 ((0x280 : Word) + o).toNat by rw [ofNat_toNat_self],
      add_ofNat_assoc, eFk]
    have e : ((0x280 : Word) + o).toNat = 0x280 + o.toNat := by
      rw [BitVec.toNat_add, show (0x280 : Word).toNat = 0x280 from rfl]; omega
    rw [e]; exact slotM _ (by omega) (by omega)
  have hslot : ∀ r o, (r, o) ∈ isoPs → reg m46 r = reg m r := fun r o hm => by
    rw [regs46, u45.regs]
    simp only [isoPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      rw [slot _ (by decide) (by decide)]; exact slots _ _ (by decide)
  have sp43 : reg m43 sp = F := by rw [K43 sp (by decide) (by decide), sp42]
  refine ⟨m46, .cons d1 (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (.cons d10
    (.cons d11 (c12.trans (.cons d13 (c14.trans (.cons d15 (c16.trans (c17.trans (c18.trans (c19.trans (c20.trans
    (c21.trans (c22.trans (c23.trans (c24.trans (c25.trans (c26.trans (c27.trans (c28.trans (c29.trans (c30.trans
    (c31.trans (c32.trans (c33.trans (c34.trans (c35.trans (c36.trans (c37.trans (c38.trans (c39.trans (c40.trans
    (c41.trans (c42.trans (c43.trans (c44.trans (.cons d45 (.single d46))))))))))))))))))))))))))))))))))))))))))))),
    ?_, ?_, fun q hq => ?_, ?_, fun x hx => ?_⟩
  · rw [pc46, ← regs46, hslot ra 0x3C (by decide), hra, add_lit_zero, hret]
  · rw [regs46, u45.regs]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rr _ _ sp (by decide) (by decide), sp43, eFS]
  · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27]) q hq with rfl | rfl | rfl | rfl | rfl | hL
    · exact hslot _ 0x3C (by decide)
    · exact hslot _ 0x38 (by decide)
    · exact hslot _ 0x34 (by decide)
    · exact hslot _ 0x30 (by decide)
    · exact hslot _ 0x2C (by decide)
    · obtain ⟨hv, hs, hps, h0, h1, hr⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ isoPs, p.1 ≠ q) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ ra := by
        revert hL; revert q; decide
      rw [regs46, u45.regs, upd_ne hv hs]; dsimp only
      rw [rr _ _ q hv hps, K43 q h0 h1, K42' q h0 hr, K40 q h0,
        Kr39 q ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] →
          q.val ∈ [3, 4, 8, 20, 21, 22, 23, 24, 25, 26, 27]) q hL),
        K34 q ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → q.val ∉ [8, 10, 11, 12]) q hL),
        Kr33 q ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] →
          q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) q hL), Kl27 q hL]
  · have hspec : isoSpec (feW m.mem p) (feW m.mem (p + 0x28)) (feW m.mem (p + 0x50)) =
        (decide (bytesL (mulL T8.1 feOneL) = bytesL (mulL feZeroL T8.2.2)) &&
          decide (bytesL (mulL T8.2.1 feOneL) = bytesL (mulL feOneL T8.2.2))) := by
      unfold isoSpec; rw [hT8]
    rw [regs46, u45.regs, upd_ne (by decide) (by decide)]; dsimp only
    rw [rr _ _ a0 (by decide) (by decide), v43.1, hspec]
    by_cases ha : bytesL (mulL T8.1 feOneL) = bytesL (mulL feZeroL T8.2.2) <;>
      by_cases hb : bytesL (mulL T8.2.1 feOneL) = bytesL (mulL feOneL T8.2.2) <;>
      simp only [ha, hb, decide_true, decide_false, Bool.and_true, Bool.and_false, and_self,
        and_false, false_and, ite_true, ite_false] <;> decide
  · rw [mem46]; exact IM42 x hx

end C3.RV32
