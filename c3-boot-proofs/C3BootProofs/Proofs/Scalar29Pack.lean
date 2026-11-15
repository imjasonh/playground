import C3BootProofs.Proofs.FeCall

/-!
# `Scalar29::pack`, as compiled

`curve25519_dalek`'s `Scalar29::pack` writes the nine 29-bit limbs of a
scalar as 32 little-endian bytes, each byte a shift of one limb or the OR of
two, as the Rust source spells out byte by byte.
-/

namespace C3.RV32

open C3.Image

abbrev spkPs : List (Fin 32 × Word) :=
  [((8 : Fin 32), 0x1C), ((9 : Fin 32), 0x18), ((18 : Fin 32), 0x14), ((19 : Fin 32), 0x10), ((20 : Fin 32), 0xC)]

section
set_option maxRecDepth 20000
theorem spk_at_0 : fetchRel scalar29PackCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem spk_at_2 : fetchRel scalar29PackCode 0x2 = some (.store .sw sp (8 : Fin 32) 0x1C, 2) := by decide
theorem spk_at_4 : fetchRel scalar29PackCode 0x4 = some (.store .sw sp (9 : Fin 32) 0x18, 2) := by decide
theorem spk_at_6 : fetchRel scalar29PackCode 0x6 = some (.store .sw sp (18 : Fin 32) 0x14, 2) := by decide
theorem spk_at_8 : fetchRel scalar29PackCode 0x8 = some (.store .sw sp (19 : Fin 32) 0x10, 2) := by decide
theorem spk_at_a : fetchRel scalar29PackCode 0xA = some (.store .sw sp (20 : Fin 32) 0xC, 2) := by decide
theorem spk_at_c : fetchRel scalar29PackCode 0xC = some (.load .lw (17 : Fin 32) a1 0x0, 4) := by decide
theorem spk_at_10 : fetchRel scalar29PackCode 0x10 = some (.load .lw (18 : Fin 32) a1 0x4, 4) := by decide
theorem spk_at_14 : fetchRel scalar29PackCode 0x14 = some (.load .lw a6 a1 0x8, 4) := by decide
theorem spk_at_18 : fetchRel scalar29PackCode 0x18 = some (.load .lw (19 : Fin 32) a1 0xC, 4) := by decide
theorem spk_at_1c : fetchRel scalar29PackCode 0x1C = some (.aluImm .srl (5 : Fin 32) (17 : Fin 32) 0x18, 4) := by decide
theorem spk_at_20 : fetchRel scalar29PackCode 0x20 = some (.aluImm .sll a5 (18 : Fin 32) 0x5, 4) := by decide
theorem spk_at_24 : fetchRel scalar29PackCode 0x24 = some (.aluImm .srl (7 : Fin 32) (18 : Fin 32) 0x1B, 4) := by decide
theorem spk_at_28 : fetchRel scalar29PackCode 0x28 = some (.aluImm .sll (28 : Fin 32) a6 0x2, 4) := by decide
theorem spk_at_2c : fetchRel scalar29PackCode 0x2C = some (.aluImm .srl (29 : Fin 32) a6 0x16, 4) := by decide
theorem spk_at_30 : fetchRel scalar29PackCode 0x30 = some (.aluImm .sll (30 : Fin 32) (19 : Fin 32) 0x7, 4) := by decide
theorem spk_at_34 : fetchRel scalar29PackCode 0x34 = some (.load .lw (20 : Fin 32) a1 0x10, 4) := by decide
theorem spk_at_38 : fetchRel scalar29PackCode 0x38 = some (.alu .or (31 : Fin 32) a5 (5 : Fin 32), 4) := by decide
theorem spk_at_3c : fetchRel scalar29PackCode 0x3C = some (.load .lw (6 : Fin 32) a1 0x14, 4) := by decide
theorem spk_at_40 : fetchRel scalar29PackCode 0x40 = some (.alu .or (7 : Fin 32) (28 : Fin 32) (7 : Fin 32), 4) := by decide
theorem spk_at_44 : fetchRel scalar29PackCode 0x44 = some (.alu .or (28 : Fin 32) (30 : Fin 32) (29 : Fin 32), 4) := by decide
theorem spk_at_48 : fetchRel scalar29PackCode 0x48 = some (.aluImm .srl (29 : Fin 32) (19 : Fin 32) 0x19, 4) := by decide
theorem spk_at_4c : fetchRel scalar29PackCode 0x4C = some (.load .lw (9 : Fin 32) a1 0x18, 2) := by decide
theorem spk_at_4e : fetchRel scalar29PackCode 0x4E = some (.load .lw (5 : Fin 32) a1 0x1C, 4) := by decide
theorem spk_at_52 : fetchRel scalar29PackCode 0x52 = some (.aluImm .sll a4 (20 : Fin 32) 0x4, 4) := by decide
theorem spk_at_56 : fetchRel scalar29PackCode 0x56 = some (.aluImm .srl (8 : Fin 32) (20 : Fin 32) 0x1C, 4) := by decide
theorem spk_at_5a : fetchRel scalar29PackCode 0x5A = some (.aluImm .sll a2 (6 : Fin 32) 0x1, 4) := by decide
theorem spk_at_5e : fetchRel scalar29PackCode 0x5E = some (.alu .or a4 a4 (29 : Fin 32), 4) := by decide
theorem spk_at_62 : fetchRel scalar29PackCode 0x62 = some (.alu .or (29 : Fin 32) a2 (8 : Fin 32), 4) := by decide
theorem spk_at_66 : fetchRel scalar29PackCode 0x66 = some (.aluImm .srl (8 : Fin 32) (6 : Fin 32) 0x17, 4) := by decide
theorem spk_at_6a : fetchRel scalar29PackCode 0x6A = some (.aluImm .sll a5 (9 : Fin 32) 0x6, 4) := by decide
theorem spk_at_6e : fetchRel scalar29PackCode 0x6E = some (.aluImm .srl a3 (9 : Fin 32) 0x1A, 4) := by decide
theorem spk_at_72 : fetchRel scalar29PackCode 0x72 = some (.aluImm .sll a2 (5 : Fin 32) 0x3, 4) := by decide
theorem spk_at_76 : fetchRel scalar29PackCode 0x76 = some (.alu .or a5 a5 (8 : Fin 32), 2) := by decide
theorem spk_at_78 : fetchRel scalar29PackCode 0x78 = some (.alu .or a2 a2 a3, 2) := by decide
theorem spk_at_7a : fetchRel scalar29PackCode 0x7A = some (.aluImm .srl a3 (17 : Fin 32) 0x8, 4) := by decide
theorem spk_at_7e : fetchRel scalar29PackCode 0x7E = some (.store .sb a0 (17 : Fin 32) 0x0, 4) := by decide
theorem spk_at_82 : fetchRel scalar29PackCode 0x82 = some (.aluImm .srl (8 : Fin 32) (17 : Fin 32) 0x10, 4) := by decide
theorem spk_at_86 : fetchRel scalar29PackCode 0x86 = some (.store .sb a0 a3 0x1, 4) := by decide
theorem spk_at_8a : fetchRel scalar29PackCode 0x8A = some (.store .sb a0 (8 : Fin 32) 0x2, 4) := by decide
theorem spk_at_8e : fetchRel scalar29PackCode 0x8E = some (.aluImm .srl a3 (18 : Fin 32) 0x3, 4) := by decide
theorem spk_at_92 : fetchRel scalar29PackCode 0x92 = some (.store .sb a0 (31 : Fin 32) 0x3, 4) := by decide
theorem spk_at_96 : fetchRel scalar29PackCode 0x96 = some (.aluImm .srl (8 : Fin 32) (18 : Fin 32) 0xB, 4) := by decide
theorem spk_at_9a : fetchRel scalar29PackCode 0x9A = some (.store .sb a0 a3 0x4, 4) := by decide
theorem spk_at_9e : fetchRel scalar29PackCode 0x9E = some (.aluImm .srl a3 (18 : Fin 32) 0x13, 4) := by decide
theorem spk_at_a2 : fetchRel scalar29PackCode 0xA2 = some (.store .sb a0 (8 : Fin 32) 0x5, 4) := by decide
theorem spk_at_a6 : fetchRel scalar29PackCode 0xA6 = some (.store .sb a0 a3 0x6, 4) := by decide
theorem spk_at_aa : fetchRel scalar29PackCode 0xAA = some (.store .sb a0 (7 : Fin 32) 0x7, 4) := by decide
theorem spk_at_ae : fetchRel scalar29PackCode 0xAE = some (.aluImm .srl a3 a6 0x6, 4) := by decide
theorem spk_at_b2 : fetchRel scalar29PackCode 0xB2 = some (.aluImm .srl (8 : Fin 32) a6 0xE, 4) := by decide
theorem spk_at_b6 : fetchRel scalar29PackCode 0xB6 = some (.store .sb a0 a3 0x8, 4) := by decide
theorem spk_at_ba : fetchRel scalar29PackCode 0xBA = some (.store .sb a0 (8 : Fin 32) 0x9, 4) := by decide
theorem spk_at_be : fetchRel scalar29PackCode 0xBE = some (.aluImm .srl a3 (19 : Fin 32) 0x1, 4) := by decide
theorem spk_at_c2 : fetchRel scalar29PackCode 0xC2 = some (.store .sb a0 (28 : Fin 32) 0xA, 4) := by decide
theorem spk_at_c6 : fetchRel scalar29PackCode 0xC6 = some (.store .sb a0 a3 0xB, 4) := by decide
theorem spk_at_ca : fetchRel scalar29PackCode 0xCA = some (.aluImm .srl a3 (19 : Fin 32) 0x9, 4) := by decide
theorem spk_at_ce : fetchRel scalar29PackCode 0xCE = some (.aluImm .srl (8 : Fin 32) (19 : Fin 32) 0x11, 4) := by decide
theorem spk_at_d2 : fetchRel scalar29PackCode 0xD2 = some (.store .sb a0 a3 0xC, 4) := by decide
theorem spk_at_d6 : fetchRel scalar29PackCode 0xD6 = some (.store .sb a0 (8 : Fin 32) 0xD, 4) := by decide
theorem spk_at_da : fetchRel scalar29PackCode 0xDA = some (.aluImm .srl a3 (20 : Fin 32) 0x4, 4) := by decide
theorem spk_at_de : fetchRel scalar29PackCode 0xDE = some (.store .sb a0 a4 0xE, 4) := by decide
theorem spk_at_e2 : fetchRel scalar29PackCode 0xE2 = some (.store .sb a0 a3 0xF, 4) := by decide
theorem spk_at_e6 : fetchRel scalar29PackCode 0xE6 = some (.aluImm .srl a3 (20 : Fin 32) 0xC, 4) := by decide
theorem spk_at_ea : fetchRel scalar29PackCode 0xEA = some (.aluImm .srl a4 (20 : Fin 32) 0x14, 4) := by decide
theorem spk_at_ee : fetchRel scalar29PackCode 0xEE = some (.store .sb a0 a3 0x10, 4) := by decide
theorem spk_at_f2 : fetchRel scalar29PackCode 0xF2 = some (.store .sb a0 a4 0x11, 4) := by decide
theorem spk_at_f6 : fetchRel scalar29PackCode 0xF6 = some (.aluImm .srl a3 (6 : Fin 32) 0x7, 4) := by decide
theorem spk_at_fa : fetchRel scalar29PackCode 0xFA = some (.store .sb a0 (29 : Fin 32) 0x12, 4) := by decide
theorem spk_at_fe : fetchRel scalar29PackCode 0xFE = some (.aluImm .srl a4 (6 : Fin 32) 0xF, 4) := by decide
theorem spk_at_102 : fetchRel scalar29PackCode 0x102 = some (.store .sb a0 a3 0x13, 4) := by decide
theorem spk_at_106 : fetchRel scalar29PackCode 0x106 = some (.store .sb a0 a4 0x14, 4) := by decide
theorem spk_at_10a : fetchRel scalar29PackCode 0x10A = some (.aluImm .srl a3 (9 : Fin 32) 0x2, 4) := by decide
theorem spk_at_10e : fetchRel scalar29PackCode 0x10E = some (.store .sb a0 a5 0x15, 4) := by decide
theorem spk_at_112 : fetchRel scalar29PackCode 0x112 = some (.aluImm .srl a4 (9 : Fin 32) 0xA, 4) := by decide
theorem spk_at_116 : fetchRel scalar29PackCode 0x116 = some (.store .sb a0 a3 0x16, 4) := by decide
theorem spk_at_11a : fetchRel scalar29PackCode 0x11A = some (.store .sb a0 a4 0x17, 4) := by decide
theorem spk_at_11e : fetchRel scalar29PackCode 0x11E = some (.aluImm .srl (9 : Fin 32) (9 : Fin 32) 0x12, 2) := by decide
theorem spk_at_120 : fetchRel scalar29PackCode 0x120 = some (.load .lw a1 a1 0x20, 2) := by decide
theorem spk_at_122 : fetchRel scalar29PackCode 0x122 = some (.store .sb a0 (9 : Fin 32) 0x18, 4) := by decide
theorem spk_at_126 : fetchRel scalar29PackCode 0x126 = some (.aluImm .srl a3 (5 : Fin 32) 0x5, 4) := by decide
theorem spk_at_12a : fetchRel scalar29PackCode 0x12A = some (.store .sb a0 a2 0x19, 4) := by decide
theorem spk_at_12e : fetchRel scalar29PackCode 0x12E = some (.aluImm .srl a2 (5 : Fin 32) 0xD, 4) := by decide
theorem spk_at_132 : fetchRel scalar29PackCode 0x132 = some (.store .sb a0 a3 0x1A, 4) := by decide
theorem spk_at_136 : fetchRel scalar29PackCode 0x136 = some (.store .sb a0 a2 0x1B, 4) := by decide
theorem spk_at_13a : fetchRel scalar29PackCode 0x13A = some (.aluImm .srl a2 (5 : Fin 32) 0x15, 4) := by decide
theorem spk_at_13e : fetchRel scalar29PackCode 0x13E = some (.store .sb a0 a2 0x1C, 4) := by decide
theorem spk_at_142 : fetchRel scalar29PackCode 0x142 = some (.aluImm .srl a2 a1 0x8, 4) := by decide
theorem spk_at_146 : fetchRel scalar29PackCode 0x146 = some (.store .sb a0 a1 0x1D, 4) := by decide
theorem spk_at_14a : fetchRel scalar29PackCode 0x14A = some (.aluImm .srl a1 a1 0x10, 2) := by decide
theorem spk_at_14c : fetchRel scalar29PackCode 0x14C = some (.store .sb a0 a2 0x1E, 4) := by decide
theorem spk_at_150 : fetchRel scalar29PackCode 0x150 = some (.store .sb a0 a1 0x1F, 4) := by decide
theorem spk_at_154 : fetchRel scalar29PackCode 0x154 = some (.load .lw (8 : Fin 32) sp 0x1C, 2) := by decide
theorem spk_at_156 : fetchRel scalar29PackCode 0x156 = some (.load .lw (9 : Fin 32) sp 0x18, 2) := by decide
theorem spk_at_158 : fetchRel scalar29PackCode 0x158 = some (.load .lw (18 : Fin 32) sp 0x14, 2) := by decide
theorem spk_at_15a : fetchRel scalar29PackCode 0x15A = some (.load .lw (19 : Fin 32) sp 0x10, 2) := by decide
theorem spk_at_15c : fetchRel scalar29PackCode 0x15C = some (.load .lw (20 : Fin 32) sp 0xC, 2) := by decide
theorem spk_at_15e : fetchRel scalar29PackCode 0x15E = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem spk_at_160 : fetchRel scalar29PackCode 0x160 = some (.jalr x0 ra 0x0, 2) := by decide
theorem spkSave_end : blockEnd scalar29PackCode 2 (saveBlock spkPs) = some 0xC := by decide
theorem spkRestore_end : blockEnd scalar29PackCode 0x154 (restoreBlock spkPs) = some 0x15E := by decide

def spkC1 : List BInstr :=
  [.lw (17 : Fin 32) a1 0x0,
    .lw (18 : Fin 32) a1 0x4,
    .lw a6 a1 0x8,
    .lw (19 : Fin 32) a1 0xC,
    .aluImm .srl (5 : Fin 32) (17 : Fin 32) 0x18,
    .aluImm .sll a5 (18 : Fin 32) 0x5,
    .aluImm .srl (7 : Fin 32) (18 : Fin 32) 0x1B,
    .aluImm .sll (28 : Fin 32) a6 0x2,
    .aluImm .srl (29 : Fin 32) a6 0x16,
    .aluImm .sll (30 : Fin 32) (19 : Fin 32) 0x7,
    .lw (20 : Fin 32) a1 0x10]

theorem spkC1_end : blockEnd scalar29PackCode 0xC spkC1 = some 0x38 := by decide

def spkC2 : List BInstr :=
  [.alu .or (31 : Fin 32) a5 (5 : Fin 32),
    .lw (6 : Fin 32) a1 0x14,
    .alu .or (7 : Fin 32) (28 : Fin 32) (7 : Fin 32),
    .alu .or (28 : Fin 32) (30 : Fin 32) (29 : Fin 32),
    .aluImm .srl (29 : Fin 32) (19 : Fin 32) 0x19,
    .lw (9 : Fin 32) a1 0x18,
    .lw (5 : Fin 32) a1 0x1C]

theorem spkC2_end : blockEnd scalar29PackCode 0x38 spkC2 = some 0x52 := by decide

def spkC3 : List BInstr :=
  [.aluImm .sll a4 (20 : Fin 32) 0x4,
    .aluImm .srl (8 : Fin 32) (20 : Fin 32) 0x1C,
    .aluImm .sll a2 (6 : Fin 32) 0x1,
    .alu .or a4 a4 (29 : Fin 32),
    .alu .or (29 : Fin 32) a2 (8 : Fin 32),
    .aluImm .srl (8 : Fin 32) (6 : Fin 32) 0x17,
    .aluImm .sll a5 (9 : Fin 32) 0x6,
    .aluImm .srl a3 (9 : Fin 32) 0x1A,
    .aluImm .sll a2 (5 : Fin 32) 0x3,
    .alu .or a5 a5 (8 : Fin 32),
    .alu .or a2 a2 a3]

theorem spkC3_end : blockEnd scalar29PackCode 0x52 spkC3 = some 0x7A := by decide

def spkC4 : List BInstr :=
  [.aluImm .srl a3 (17 : Fin 32) 0x8,
    .sb a0 (17 : Fin 32) 0x0,
    .aluImm .srl (8 : Fin 32) (17 : Fin 32) 0x10,
    .sb a0 a3 0x1,
    .sb a0 (8 : Fin 32) 0x2,
    .aluImm .srl a3 (18 : Fin 32) 0x3,
    .sb a0 (31 : Fin 32) 0x3,
    .aluImm .srl (8 : Fin 32) (18 : Fin 32) 0xB,
    .sb a0 a3 0x4,
    .aluImm .srl a3 (18 : Fin 32) 0x13,
    .sb a0 (8 : Fin 32) 0x5,
    .sb a0 a3 0x6,
    .sb a0 (7 : Fin 32) 0x7]

theorem spkC4_end : blockEnd scalar29PackCode 0x7A spkC4 = some 0xAE := by decide

def spkC5 : List BInstr :=
  [.aluImm .srl a3 a6 0x6,
    .aluImm .srl (8 : Fin 32) a6 0xE,
    .sb a0 a3 0x8,
    .sb a0 (8 : Fin 32) 0x9,
    .aluImm .srl a3 (19 : Fin 32) 0x1,
    .sb a0 (28 : Fin 32) 0xA,
    .sb a0 a3 0xB,
    .aluImm .srl a3 (19 : Fin 32) 0x9,
    .aluImm .srl (8 : Fin 32) (19 : Fin 32) 0x11,
    .sb a0 a3 0xC,
    .sb a0 (8 : Fin 32) 0xD]

theorem spkC5_end : blockEnd scalar29PackCode 0xAE spkC5 = some 0xDA := by decide

def spkC6 : List BInstr :=
  [.aluImm .srl a3 (20 : Fin 32) 0x4,
    .sb a0 a4 0xE,
    .sb a0 a3 0xF,
    .aluImm .srl a3 (20 : Fin 32) 0xC,
    .aluImm .srl a4 (20 : Fin 32) 0x14,
    .sb a0 a3 0x10,
    .sb a0 a4 0x11,
    .aluImm .srl a3 (6 : Fin 32) 0x7,
    .sb a0 (29 : Fin 32) 0x12,
    .aluImm .srl a4 (6 : Fin 32) 0xF,
    .sb a0 a3 0x13,
    .sb a0 a4 0x14]

theorem spkC6_end : blockEnd scalar29PackCode 0xDA spkC6 = some 0x10A := by decide

def spkC7 : List BInstr :=
  [.aluImm .srl a3 (9 : Fin 32) 0x2,
    .sb a0 a5 0x15,
    .aluImm .srl a4 (9 : Fin 32) 0xA,
    .sb a0 a3 0x16,
    .sb a0 a4 0x17,
    .aluImm .srl (9 : Fin 32) (9 : Fin 32) 0x12]

theorem spkC7_end : blockEnd scalar29PackCode 0x10A spkC7 = some 0x120 := by decide

def spkB2 : List BInstr :=
  [.sb a0 (9 : Fin 32) 0x18,
    .aluImm .srl a3 (5 : Fin 32) 0x5,
    .sb a0 a2 0x19,
    .aluImm .srl a2 (5 : Fin 32) 0xD,
    .sb a0 a3 0x1A,
    .sb a0 a2 0x1B,
    .aluImm .srl a2 (5 : Fin 32) 0x15,
    .sb a0 a2 0x1C,
    .aluImm .srl a2 a1 0x8,
    .sb a0 a1 0x1D,
    .aluImm .srl a1 a1 0x10,
    .sb a0 a2 0x1E,
    .sb a0 a1 0x1F]

theorem spkB2_end : blockEnd scalar29PackCode 0x122 spkB2 = some 0x154 := by decide


def spkL8 : List BInstr :=
  [.lw a1 a1 0x20]

theorem spkL8_end : blockEnd scalar29PackCode 0x120 spkL8 = some 0x122 := by decide


end

/-- Byte `j` of `Scalar29::as_bytes`, from the Rust source, for limbs `l`. -/
def s29PackByte (l : Nat → Word) : Nat → BitVec 8
  | 0 => (l 0).extractLsb' 0 8
  | 1 => (l 0 >>> 8).extractLsb' 0 8
  | 2 => (l 0 >>> 16).extractLsb' 0 8
  | 3 => ((l 0 >>> 24) ||| (l 1 <<< 5)).extractLsb' 0 8
  | 4 => (l 1 >>> 3).extractLsb' 0 8
  | 5 => (l 1 >>> 11).extractLsb' 0 8
  | 6 => (l 1 >>> 19).extractLsb' 0 8
  | 7 => ((l 1 >>> 27) ||| (l 2 <<< 2)).extractLsb' 0 8
  | 8 => (l 2 >>> 6).extractLsb' 0 8
  | 9 => (l 2 >>> 14).extractLsb' 0 8
  | 10 => ((l 2 >>> 22) ||| (l 3 <<< 7)).extractLsb' 0 8
  | 11 => (l 3 >>> 1).extractLsb' 0 8
  | 12 => (l 3 >>> 9).extractLsb' 0 8
  | 13 => (l 3 >>> 17).extractLsb' 0 8
  | 14 => ((l 3 >>> 25) ||| (l 4 <<< 4)).extractLsb' 0 8
  | 15 => (l 4 >>> 4).extractLsb' 0 8
  | 16 => (l 4 >>> 12).extractLsb' 0 8
  | 17 => (l 4 >>> 20).extractLsb' 0 8
  | 18 => ((l 4 >>> 28) ||| (l 5 <<< 1)).extractLsb' 0 8
  | 19 => (l 5 >>> 7).extractLsb' 0 8
  | 20 => (l 5 >>> 15).extractLsb' 0 8
  | 21 => ((l 5 >>> 23) ||| (l 6 <<< 6)).extractLsb' 0 8
  | 22 => (l 6 >>> 2).extractLsb' 0 8
  | 23 => (l 6 >>> 10).extractLsb' 0 8
  | 24 => (l 6 >>> 18).extractLsb' 0 8
  | 25 => ((l 6 >>> 26) ||| (l 7 <<< 3)).extractLsb' 0 8
  | 26 => (l 7 >>> 5).extractLsb' 0 8
  | 27 => (l 7 >>> 13).extractLsb' 0 8
  | 28 => (l 7 >>> 21).extractLsb' 0 8
  | 29 => (l 8).extractLsb' 0 8
  | 30 => (l 8 >>> 8).extractLsb' 0 8
  | 31 => (l 8 >>> 16).extractLsb' 0 8
  | _ => 0

theorem outNe (out : Word) (j : Nat) (L : List Nat)
    (h : (L.all fun c => decide (c < 32 ∧ j < 32 ∧ j ≠ c)) = true) :
    ∀ c ∈ L, out + BitVec.ofNat 32 j ≠ out + BitVec.ofNat 32 c := fun c hc => by
  have := of_decide_eq_true (List.all_eq_true.1 h c hc)
  exact add_ofNat_ne out (by omega) (by omega) this.2.2

theorem outFr {out x : Word} (hx : Sep out 32 x 1) (L : List Nat) (h : (L.all fun c => decide (c < 32)) = true) :
    ∀ c ∈ L, x ≠ out + BitVec.ofNat 32 c := fun c hc e => by
  have := hx c (of_decide_eq_true (List.all_eq_true.1 h c hc)) 0 (by decide)
  rw [add_ofNat_zero] at this; exact this e.symm

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 400000 in
/-- **The compiled `Scalar29::pack`**: it writes `s29PackByte` of the nine
limbs at `ap` to the 32 bytes at `out`, and changes nothing else but its
0x20 bytes of stack. -/
theorem scalar29Pack_correct (m : Machine) {P sp0 out ap retAddr : Word} (hc : CodeIn m.mem P scalar29PackCode)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsa : sp0.toNat % 4 = 0) (hS : 0x20 ≤ sp0.toNat) (hap : ap.toNat % 4 = 0)
    (sGC : Sep (sp0 + 0xFFFFFFE0) 0x20 P scalar29PackCode.length) (sOC : Sep out 32 P scalar29PackCode.length)
    (sOG : Sep out 32 (sp0 + 0xFFFFFFE0) 0x20) (sAG : Sep ap 36 (sp0 + 0xFFFFFFE0) 0x20) (sOA : Sep out 32 ap 36) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ j, j < 32 → m'.mem (out + BitVec.ofNat 32 j) = s29PackByte (limbs m.mem ap) j) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  rw [hF] at sGC sOG sAG ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hsa (k := 0xFFFFFFE0) (by decide)
  have hFn : F.toNat + 0x20 = sp0.toNat := by
    rw [← hF, BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 4294967264 from rfl]
    have := sp0.isLt; omega
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have slotC : ∀ (o : Word), o.toNat + 4 ≤ 0x20 → ∀ {b : Word} {l : Nat}, Sep F 0x20 b l → Sep (F + o) 4 b l := by
    intro o h b l hs
    rw [← ofNat_toNat_self o]; exact hs.sub (c := o.toNat) (l := 4) (by omega)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm hc spk_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨ms, cs, us⟩ := St.block (saveBlock spkPs) u1 hc spkSave_end (saveBlock_ok _ spkPs _ fun p hp => by
    rw [sp1]
    simp only [spkPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨aligned_add hFa (by decide), slotC _ (by decide) sGC⟩)
  simp only [saveBlock_run] at us
  rw [sp1] at us
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) spkPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at us
  have frSv : ∀ x, Sep F 0x20 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside spkPs fun p hp => by
      simp only [spkPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact slotC _ (by decide) hx
  have hslv : ∀ r o, (r, o) ∈ spkPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [spkPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg ms q = reg m q := fun q h => by rw [us.regs, updz hz h]
  have sp2 : reg ms sp = F := by rw [us.regs]; exact sp1
  have hcS : CodeIn Msv P scalar29PackCode := fun i hi => by
    rw [frSv _ (sGC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have ldA : ∀ k, k + 4 ≤ 36 → memLoad32 Msv (ap + BitVec.ofNat 32 k) = memLoad32 m.mem (ap + BitVec.ofNat 32 k) :=
    fun k h => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact frSv _ (sAG.sub (c := k + j) (l := 1) (by omega)).symm
  obtain ⟨l, hl⟩ : ∃ l, limbs m.mem ap = l := ⟨_, rfl⟩
  have LA0 : memLoad32 Msv (ap + 0x0) = l 0 := (ldA 0x0 (by decide)).trans (by rw [← hl]; rfl)
  have LA1 : memLoad32 Msv (ap + 0x4) = l 1 := (ldA 0x4 (by decide)).trans (by rw [← hl]; rfl)
  have LA2 : memLoad32 Msv (ap + 0x8) = l 2 := (ldA 0x8 (by decide)).trans (by rw [← hl]; rfl)
  have LA3 : memLoad32 Msv (ap + 0xC) = l 3 := (ldA 0xC (by decide)).trans (by rw [← hl]; rfl)
  have LA4 : memLoad32 Msv (ap + 0x10) = l 4 := (ldA 0x10 (by decide)).trans (by rw [← hl]; rfl)
  have LA5 : memLoad32 Msv (ap + 0x14) = l 5 := (ldA 0x14 (by decide)).trans (by rw [← hl]; rfl)
  have LA6 : memLoad32 Msv (ap + 0x18) = l 6 := (ldA 0x18 (by decide)).trans (by rw [← hl]; rfl)
  have LA7 : memLoad32 Msv (ap + 0x1C) = l 7 := (ldA 0x1C (by decide)).trans (by rw [← hl]; rfl)
  have LA8 : memLoad32 Msv (ap + 0x20) = l 8 := (ldA 0x20 (by decide)).trans (by rw [← hl]; rfl)
  have A0s : reg ms a0 = out := by rw [r2 a0 (by decide), ha0]
  have A1s : reg ms a1 = ap := by rw [r2 a1 (by decide), ha1]
  obtain ⟨mC1, cC1, uC1⟩ := St.block spkC1 us.self hcS spkC1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, spkC1, upd_app, ↓reduceIte, and_true]
    all_goals try simp only [A0s, A1s]
    all_goals repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hap ?_; decide) | exact sOC.sub (by decide))
  simp only [runBlock, BInstr.run, spkC1] at uC1
  have kC1 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mC1 q = reg ms q := fun q hq => by
    obtain ⟨h0, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ : q.val ≠ 0 ∧ q ≠ (5 : Fin 32) ∧ q ≠ (7 : Fin 32) ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ (17 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧ q ≠ (20 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) := by revert hq; revert q; decide
    rw [uC1.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1, upd_ne h0 n2, upd_ne h0 n3, upd_ne h0 n4, upd_ne h0 n5, upd_ne h0 n6, upd_ne h0 n7, upd_ne h0 n8, upd_ne h0 n9, upd_ne h0 n10]
  have RC1_5 : reg mC1 (5 : Fin 32) = (l 0 >>> 24) := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_7 : reg mC1 (7 : Fin 32) = (l 1 >>> 27) := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_10 : reg mC1 a0 = out := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]; exact A0s
  have RC1_11 : reg mC1 a1 = ap := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]; exact A1s
  have RC1_15 : reg mC1 a5 = (l 1 <<< 5) := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_16 : reg mC1 a6 = l 2 := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_17 : reg mC1 (17 : Fin 32) = l 0 := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_18 : reg mC1 (18 : Fin 32) = l 1 := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_19 : reg mC1 (19 : Fin 32) = l 3 := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_20 : reg mC1 (20 : Fin 32) = l 4 := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_28 : reg mC1 (28 : Fin 32) = (l 2 <<< 2) := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_29 : reg mC1 (29 : Fin 32) = (l 2 >>> 22) := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC1_30 : reg mC1 (30 : Fin 32) = (l 3 <<< 7) := by
    rw [uC1.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [A1s, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  obtain ⟨mC2, cC2, uC2⟩ := St.block spkC2 uC1.self hcS spkC2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, spkC2, upd_app, ↓reduceIte, and_true]
    all_goals try simp only [RC1_10, RC1_11]
    all_goals repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hap ?_; decide) | exact sOC.sub (by decide))
  simp only [runBlock, BInstr.run, spkC2] at uC2
  have kC2 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mC2 q = reg mC1 q := fun q hq => by
    obtain ⟨h0, n0, n1, n2, n3, n4, n5, n6⟩ : q.val ≠ 0 ∧ q ≠ (5 : Fin 32) ∧ q ≠ (6 : Fin 32) ∧ q ≠ (7 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (31 : Fin 32) := by revert hq; revert q; decide
    rw [uC2.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1, upd_ne h0 n2, upd_ne h0 n3, upd_ne h0 n4, upd_ne h0 n5, upd_ne h0 n6]
  have RC2_5 : reg mC2 (5 : Fin 32) = l 7 := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC1_11, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC2_6 : reg mC2 (6 : Fin 32) = l 5 := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC1_11, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC2_7 : reg mC2 (7 : Fin 32) = ((l 2 <<< 2) ||| (l 1 >>> 27)) := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC1_7, RC1_28, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC2_9 : reg mC2 (9 : Fin 32) = l 6 := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC1_11, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC2_10 : reg mC2 a0 = out := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC1_10
  have RC2_11 : reg mC2 a1 = ap := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC1_11
  have RC2_16 : reg mC2 a6 = l 2 := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC1_16
  have RC2_17 : reg mC2 (17 : Fin 32) = l 0 := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC1_17
  have RC2_18 : reg mC2 (18 : Fin 32) = l 1 := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC1_18
  have RC2_19 : reg mC2 (19 : Fin 32) = l 3 := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC1_19
  have RC2_20 : reg mC2 (20 : Fin 32) = l 4 := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC1_20
  have RC2_28 : reg mC2 (28 : Fin 32) = ((l 3 <<< 7) ||| (l 2 >>> 22)) := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC1_29, RC1_30, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC2_29 : reg mC2 (29 : Fin 32) = (l 3 >>> 25) := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC1_19, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  have RC2_31 : reg mC2 (31 : Fin 32) = ((l 1 <<< 5) ||| (l 0 >>> 24)) := by
    rw [uC2.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC1_5, RC1_15, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8]) <;> rfl
  obtain ⟨mC3, cC3, uC3⟩ := St.block spkC3 uC2.self hcS spkC3_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, spkC3, upd_app, ↓reduceIte, and_true]
    all_goals try simp only [RC2_10, RC2_11]
    all_goals repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hap ?_; decide) | exact sOC.sub (by decide))
  simp only [runBlock, BInstr.run, spkC3] at uC3
  have kC3 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mC3 q = reg mC2 q := fun q hq => by
    obtain ⟨h0, n0, n1, n2, n3, n4, n5⟩ : q.val ≠ 0 ∧ q ≠ (8 : Fin 32) ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ (29 : Fin 32) := by revert hq; revert q; decide
    rw [uC3.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1, upd_ne h0 n2, upd_ne h0 n3, upd_ne h0 n4, upd_ne h0 n5]
  have RC3_5 : reg mC3 (5 : Fin 32) = l 7 := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_5
  have RC3_6 : reg mC3 (6 : Fin 32) = l 5 := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_6
  have RC3_7 : reg mC3 (7 : Fin 32) = ((l 2 <<< 2) ||| (l 1 >>> 27)) := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_7
  have RC3_9 : reg mC3 (9 : Fin 32) = l 6 := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_9
  have RC3_10 : reg mC3 a0 = out := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_10
  have RC3_11 : reg mC3 a1 = ap := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_11
  have RC3_12 : reg mC3 a2 = ((l 7 <<< 3) ||| (l 6 >>> 26)) := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC2_5, RC2_9]) <;> rfl
  have RC3_14 : reg mC3 a4 = ((l 4 <<< 4) ||| (l 3 >>> 25)) := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC2_20, RC2_29]) <;> rfl
  have RC3_15 : reg mC3 a5 = ((l 6 <<< 6) ||| (l 5 >>> 23)) := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC2_6, RC2_9]) <;> rfl
  have RC3_16 : reg mC3 a6 = l 2 := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_16
  have RC3_17 : reg mC3 (17 : Fin 32) = l 0 := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_17
  have RC3_18 : reg mC3 (18 : Fin 32) = l 1 := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_18
  have RC3_19 : reg mC3 (19 : Fin 32) = l 3 := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_19
  have RC3_20 : reg mC3 (20 : Fin 32) = l 4 := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_20
  have RC3_28 : reg mC3 (28 : Fin 32) = ((l 3 <<< 7) ||| (l 2 >>> 22)) := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_28
  have RC3_29 : reg mC3 (29 : Fin 32) = ((l 5 <<< 1) ||| (l 4 >>> 28)) := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC2_6, RC2_20]) <;> rfl
  have RC3_31 : reg mC3 (31 : Fin 32) = ((l 1 <<< 5) ||| (l 0 >>> 24)) := by
    rw [uC3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC2_31
  obtain ⟨mC4, cC4, uC4⟩ := St.block spkC4 uC3.self hcS spkC4_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, spkC4, upd_app, ↓reduceIte, and_true]
    all_goals try simp only [RC3_10, RC3_11]
    all_goals repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hap ?_; decide) | exact sOC.sub (by decide))
  simp only [runBlock, BInstr.run, spkC4] at uC4
  have kC4 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mC4 q = reg mC3 q := fun q hq => by
    obtain ⟨h0, n0, n1⟩ : q.val ≠ 0 ∧ q ≠ (8 : Fin 32) ∧ q ≠ a3 := by revert hq; revert q; decide
    rw [uC4.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1]
  have RC4_5 : reg mC4 (5 : Fin 32) = l 7 := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_5
  have RC4_6 : reg mC4 (6 : Fin 32) = l 5 := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_6
  have RC4_9 : reg mC4 (9 : Fin 32) = l 6 := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_9
  have RC4_10 : reg mC4 a0 = out := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_10
  have RC4_11 : reg mC4 a1 = ap := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_11
  have RC4_12 : reg mC4 a2 = ((l 7 <<< 3) ||| (l 6 >>> 26)) := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_12
  have RC4_14 : reg mC4 a4 = ((l 4 <<< 4) ||| (l 3 >>> 25)) := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_14
  have RC4_15 : reg mC4 a5 = ((l 6 <<< 6) ||| (l 5 >>> 23)) := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_15
  have RC4_16 : reg mC4 a6 = l 2 := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_16
  have RC4_19 : reg mC4 (19 : Fin 32) = l 3 := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_19
  have RC4_20 : reg mC4 (20 : Fin 32) = l 4 := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_20
  have RC4_28 : reg mC4 (28 : Fin 32) = ((l 3 <<< 7) ||| (l 2 >>> 22)) := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_28
  have RC4_29 : reg mC4 (29 : Fin 32) = ((l 5 <<< 1) ||| (l 4 >>> 28)) := by
    rw [uC4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC3_29
  have MC4 := uC4.mem
  simp +decide only [upd_app, ↓reduceIte] at MC4
  simp only [RC3_10, RC3_17, RC3_18, RC3_31, RC3_7] at MC4
  have fC4 : ∀ x, (∀ c ∈ [0, 1, 2, 3, 4, 5, 6, 7], x ≠ out + BitVec.ofNat 32 c) → mC4.mem x = Msv x := fun x h => by
    rw [MC4, memStore8_ne (a := out + 0x7) (h 7 (by decide)), memStore8_ne (a := out + 0x6) (h 6 (by decide)), memStore8_ne (a := out + 0x5) (h 5 (by decide)), memStore8_ne (a := out + 0x4) (h 4 (by decide)), memStore8_ne (a := out + 0x3) (h 3 (by decide)), memStore8_ne (a := out + 0x2) (h 2 (by decide)), memStore8_ne (a := out + 0x1) (h 1 (by decide)), memStore8_ne (a := out + 0x0) (h 0 (by decide))]
  have B0 : mC4.mem (out + 0x0) = s29PackByte l 0 := by
    rw [MC4, memStore8_ne (x := out + 0x0) (a := out + 0x7) (add_ofNat_ne out (c := 0) (d := 7) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x0) (a := out + 0x6) (add_ofNat_ne out (c := 0) (d := 6) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x0) (a := out + 0x5) (add_ofNat_ne out (c := 0) (d := 5) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x0) (a := out + 0x4) (add_ofNat_ne out (c := 0) (d := 4) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x0) (a := out + 0x3) (add_ofNat_ne out (c := 0) (d := 3) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x0) (a := out + 0x2) (add_ofNat_ne out (c := 0) (d := 2) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x0) (a := out + 0x1) (add_ofNat_ne out (c := 0) (d := 1) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B1 : mC4.mem (out + 0x1) = s29PackByte l 1 := by
    rw [MC4, memStore8_ne (x := out + 0x1) (a := out + 0x7) (add_ofNat_ne out (c := 1) (d := 7) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1) (a := out + 0x6) (add_ofNat_ne out (c := 1) (d := 6) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1) (a := out + 0x5) (add_ofNat_ne out (c := 1) (d := 5) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1) (a := out + 0x4) (add_ofNat_ne out (c := 1) (d := 4) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1) (a := out + 0x3) (add_ofNat_ne out (c := 1) (d := 3) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1) (a := out + 0x2) (add_ofNat_ne out (c := 1) (d := 2) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B2 : mC4.mem (out + 0x2) = s29PackByte l 2 := by
    rw [MC4, memStore8_ne (x := out + 0x2) (a := out + 0x7) (add_ofNat_ne out (c := 2) (d := 7) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x2) (a := out + 0x6) (add_ofNat_ne out (c := 2) (d := 6) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x2) (a := out + 0x5) (add_ofNat_ne out (c := 2) (d := 5) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x2) (a := out + 0x4) (add_ofNat_ne out (c := 2) (d := 4) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x2) (a := out + 0x3) (add_ofNat_ne out (c := 2) (d := 3) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B3 : mC4.mem (out + 0x3) = s29PackByte l 3 := by
    rw [MC4, memStore8_ne (x := out + 0x3) (a := out + 0x7) (add_ofNat_ne out (c := 3) (d := 7) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x3) (a := out + 0x6) (add_ofNat_ne out (c := 3) (d := 6) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x3) (a := out + 0x5) (add_ofNat_ne out (c := 3) (d := 5) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x3) (a := out + 0x4) (add_ofNat_ne out (c := 3) (d := 4) (by decide) (by decide) (by decide)), memStore8_same]
    exact congrArg (BitVec.extractLsb' 0 8) (BitVec.or_comm _ _)
  have B4 : mC4.mem (out + 0x4) = s29PackByte l 4 := by
    rw [MC4, memStore8_ne (x := out + 0x4) (a := out + 0x7) (add_ofNat_ne out (c := 4) (d := 7) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x4) (a := out + 0x6) (add_ofNat_ne out (c := 4) (d := 6) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x4) (a := out + 0x5) (add_ofNat_ne out (c := 4) (d := 5) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B5 : mC4.mem (out + 0x5) = s29PackByte l 5 := by
    rw [MC4, memStore8_ne (x := out + 0x5) (a := out + 0x7) (add_ofNat_ne out (c := 5) (d := 7) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x5) (a := out + 0x6) (add_ofNat_ne out (c := 5) (d := 6) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B6 : mC4.mem (out + 0x6) = s29PackByte l 6 := by
    rw [MC4, memStore8_ne (x := out + 0x6) (a := out + 0x7) (add_ofNat_ne out (c := 6) (d := 7) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B7 : mC4.mem (out + 0x7) = s29PackByte l 7 := by
    rw [MC4, memStore8_same]
    exact congrArg (BitVec.extractLsb' 0 8) (BitVec.or_comm _ _)
  have hcC4 : CodeIn mC4.mem P scalar29PackCode := by
    rw [MC4]; exact ((((((((hcS.store8 (sOC.sub (c := 0) (l := 1) (by decide))).store8 (sOC.sub (c := 1) (l := 1) (by decide))).store8 (sOC.sub (c := 2) (l := 1) (by decide))).store8 (sOC.sub (c := 3) (l := 1) (by decide))).store8 (sOC.sub (c := 4) (l := 1) (by decide))).store8 (sOC.sub (c := 5) (l := 1) (by decide))).store8 (sOC.sub (c := 6) (l := 1) (by decide))).store8 (sOC.sub (c := 7) (l := 1) (by decide)))
  have uC4' : St mC4.mem P mC4 0xAE (reg mC4) := ⟨uC4.pc, rfl, fun _ => rfl⟩
  obtain ⟨mC5, cC5, uC5⟩ := St.block spkC5 uC4' hcC4 spkC5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, spkC5, upd_app, ↓reduceIte, and_true]
    all_goals try simp only [RC4_10, RC4_11]
    all_goals repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hap ?_; decide) | exact sOC.sub (by decide))
  simp only [runBlock, BInstr.run, spkC5] at uC5
  have kC5 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mC5 q = reg mC4 q := fun q hq => by
    obtain ⟨h0, n0, n1⟩ : q.val ≠ 0 ∧ q ≠ (8 : Fin 32) ∧ q ≠ a3 := by revert hq; revert q; decide
    rw [uC5.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1]
  have RC5_5 : reg mC5 (5 : Fin 32) = l 7 := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_5
  have RC5_6 : reg mC5 (6 : Fin 32) = l 5 := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_6
  have RC5_9 : reg mC5 (9 : Fin 32) = l 6 := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_9
  have RC5_10 : reg mC5 a0 = out := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_10
  have RC5_11 : reg mC5 a1 = ap := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_11
  have RC5_12 : reg mC5 a2 = ((l 7 <<< 3) ||| (l 6 >>> 26)) := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_12
  have RC5_14 : reg mC5 a4 = ((l 4 <<< 4) ||| (l 3 >>> 25)) := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_14
  have RC5_15 : reg mC5 a5 = ((l 6 <<< 6) ||| (l 5 >>> 23)) := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_15
  have RC5_20 : reg mC5 (20 : Fin 32) = l 4 := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_20
  have RC5_29 : reg mC5 (29 : Fin 32) = ((l 5 <<< 1) ||| (l 4 >>> 28)) := by
    rw [uC5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC4_29
  have MC5 := uC5.mem
  simp +decide only [upd_app, ↓reduceIte] at MC5
  simp only [RC4_10, RC4_16, RC4_19, RC4_28] at MC5
  have fC5 : ∀ x, (∀ c ∈ [8, 9, 10, 11, 12, 13], x ≠ out + BitVec.ofNat 32 c) → mC5.mem x = mC4.mem x := fun x h => by
    rw [MC5, memStore8_ne (a := out + 0xD) (h 13 (by decide)), memStore8_ne (a := out + 0xC) (h 12 (by decide)), memStore8_ne (a := out + 0xB) (h 11 (by decide)), memStore8_ne (a := out + 0xA) (h 10 (by decide)), memStore8_ne (a := out + 0x9) (h 9 (by decide)), memStore8_ne (a := out + 0x8) (h 8 (by decide))]
  have B8 : mC5.mem (out + 0x8) = s29PackByte l 8 := by
    rw [MC5, memStore8_ne (x := out + 0x8) (a := out + 0xD) (add_ofNat_ne out (c := 8) (d := 13) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x8) (a := out + 0xC) (add_ofNat_ne out (c := 8) (d := 12) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x8) (a := out + 0xB) (add_ofNat_ne out (c := 8) (d := 11) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x8) (a := out + 0xA) (add_ofNat_ne out (c := 8) (d := 10) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x8) (a := out + 0x9) (add_ofNat_ne out (c := 8) (d := 9) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B9 : mC5.mem (out + 0x9) = s29PackByte l 9 := by
    rw [MC5, memStore8_ne (x := out + 0x9) (a := out + 0xD) (add_ofNat_ne out (c := 9) (d := 13) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x9) (a := out + 0xC) (add_ofNat_ne out (c := 9) (d := 12) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x9) (a := out + 0xB) (add_ofNat_ne out (c := 9) (d := 11) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x9) (a := out + 0xA) (add_ofNat_ne out (c := 9) (d := 10) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B10 : mC5.mem (out + 0xA) = s29PackByte l 10 := by
    rw [MC5, memStore8_ne (x := out + 0xA) (a := out + 0xD) (add_ofNat_ne out (c := 10) (d := 13) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xA) (a := out + 0xC) (add_ofNat_ne out (c := 10) (d := 12) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xA) (a := out + 0xB) (add_ofNat_ne out (c := 10) (d := 11) (by decide) (by decide) (by decide)), memStore8_same]
    exact congrArg (BitVec.extractLsb' 0 8) (BitVec.or_comm _ _)
  have B11 : mC5.mem (out + 0xB) = s29PackByte l 11 := by
    rw [MC5, memStore8_ne (x := out + 0xB) (a := out + 0xD) (add_ofNat_ne out (c := 11) (d := 13) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xB) (a := out + 0xC) (add_ofNat_ne out (c := 11) (d := 12) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B12 : mC5.mem (out + 0xC) = s29PackByte l 12 := by
    rw [MC5, memStore8_ne (x := out + 0xC) (a := out + 0xD) (add_ofNat_ne out (c := 12) (d := 13) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B13 : mC5.mem (out + 0xD) = s29PackByte l 13 := by
    rw [MC5, memStore8_same]
    rfl
  have hcC5 : CodeIn mC5.mem P scalar29PackCode := by
    rw [MC5]; exact ((((((hcC4.store8 (sOC.sub (c := 8) (l := 1) (by decide))).store8 (sOC.sub (c := 9) (l := 1) (by decide))).store8 (sOC.sub (c := 10) (l := 1) (by decide))).store8 (sOC.sub (c := 11) (l := 1) (by decide))).store8 (sOC.sub (c := 12) (l := 1) (by decide))).store8 (sOC.sub (c := 13) (l := 1) (by decide)))
  have uC5' : St mC5.mem P mC5 0xDA (reg mC5) := ⟨uC5.pc, rfl, fun _ => rfl⟩
  obtain ⟨mC6, cC6, uC6⟩ := St.block spkC6 uC5' hcC5 spkC6_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, spkC6, upd_app, ↓reduceIte, and_true]
    all_goals try simp only [RC5_10, RC5_11]
    all_goals repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hap ?_; decide) | exact sOC.sub (by decide))
  simp only [runBlock, BInstr.run, spkC6] at uC6
  have kC6 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mC6 q = reg mC5 q := fun q hq => by
    obtain ⟨h0, n0, n1⟩ : q.val ≠ 0 ∧ q ≠ a3 ∧ q ≠ a4 := by revert hq; revert q; decide
    rw [uC6.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1]
  have RC6_5 : reg mC6 (5 : Fin 32) = l 7 := by
    rw [uC6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC5_5
  have RC6_9 : reg mC6 (9 : Fin 32) = l 6 := by
    rw [uC6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC5_9
  have RC6_10 : reg mC6 a0 = out := by
    rw [uC6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC5_10
  have RC6_11 : reg mC6 a1 = ap := by
    rw [uC6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC5_11
  have RC6_12 : reg mC6 a2 = ((l 7 <<< 3) ||| (l 6 >>> 26)) := by
    rw [uC6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC5_12
  have RC6_15 : reg mC6 a5 = ((l 6 <<< 6) ||| (l 5 >>> 23)) := by
    rw [uC6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC5_15
  have MC6 := uC6.mem
  simp +decide only [upd_app, ↓reduceIte] at MC6
  simp only [RC5_10, RC5_14, RC5_20, RC5_29, RC5_6] at MC6
  have fC6 : ∀ x, (∀ c ∈ [14, 15, 16, 17, 18, 19, 20], x ≠ out + BitVec.ofNat 32 c) → mC6.mem x = mC5.mem x := fun x h => by
    rw [MC6, memStore8_ne (a := out + 0x14) (h 20 (by decide)), memStore8_ne (a := out + 0x13) (h 19 (by decide)), memStore8_ne (a := out + 0x12) (h 18 (by decide)), memStore8_ne (a := out + 0x11) (h 17 (by decide)), memStore8_ne (a := out + 0x10) (h 16 (by decide)), memStore8_ne (a := out + 0xF) (h 15 (by decide)), memStore8_ne (a := out + 0xE) (h 14 (by decide))]
  have B14 : mC6.mem (out + 0xE) = s29PackByte l 14 := by
    rw [MC6, memStore8_ne (x := out + 0xE) (a := out + 0x14) (add_ofNat_ne out (c := 14) (d := 20) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xE) (a := out + 0x13) (add_ofNat_ne out (c := 14) (d := 19) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xE) (a := out + 0x12) (add_ofNat_ne out (c := 14) (d := 18) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xE) (a := out + 0x11) (add_ofNat_ne out (c := 14) (d := 17) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xE) (a := out + 0x10) (add_ofNat_ne out (c := 14) (d := 16) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xE) (a := out + 0xF) (add_ofNat_ne out (c := 14) (d := 15) (by decide) (by decide) (by decide)), memStore8_same]
    exact congrArg (BitVec.extractLsb' 0 8) (BitVec.or_comm _ _)
  have B15 : mC6.mem (out + 0xF) = s29PackByte l 15 := by
    rw [MC6, memStore8_ne (x := out + 0xF) (a := out + 0x14) (add_ofNat_ne out (c := 15) (d := 20) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xF) (a := out + 0x13) (add_ofNat_ne out (c := 15) (d := 19) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xF) (a := out + 0x12) (add_ofNat_ne out (c := 15) (d := 18) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xF) (a := out + 0x11) (add_ofNat_ne out (c := 15) (d := 17) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0xF) (a := out + 0x10) (add_ofNat_ne out (c := 15) (d := 16) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B16 : mC6.mem (out + 0x10) = s29PackByte l 16 := by
    rw [MC6, memStore8_ne (x := out + 0x10) (a := out + 0x14) (add_ofNat_ne out (c := 16) (d := 20) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x10) (a := out + 0x13) (add_ofNat_ne out (c := 16) (d := 19) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x10) (a := out + 0x12) (add_ofNat_ne out (c := 16) (d := 18) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x10) (a := out + 0x11) (add_ofNat_ne out (c := 16) (d := 17) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B17 : mC6.mem (out + 0x11) = s29PackByte l 17 := by
    rw [MC6, memStore8_ne (x := out + 0x11) (a := out + 0x14) (add_ofNat_ne out (c := 17) (d := 20) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x11) (a := out + 0x13) (add_ofNat_ne out (c := 17) (d := 19) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x11) (a := out + 0x12) (add_ofNat_ne out (c := 17) (d := 18) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B18 : mC6.mem (out + 0x12) = s29PackByte l 18 := by
    rw [MC6, memStore8_ne (x := out + 0x12) (a := out + 0x14) (add_ofNat_ne out (c := 18) (d := 20) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x12) (a := out + 0x13) (add_ofNat_ne out (c := 18) (d := 19) (by decide) (by decide) (by decide)), memStore8_same]
    exact congrArg (BitVec.extractLsb' 0 8) (BitVec.or_comm _ _)
  have B19 : mC6.mem (out + 0x13) = s29PackByte l 19 := by
    rw [MC6, memStore8_ne (x := out + 0x13) (a := out + 0x14) (add_ofNat_ne out (c := 19) (d := 20) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B20 : mC6.mem (out + 0x14) = s29PackByte l 20 := by
    rw [MC6, memStore8_same]
    rfl
  have hcC6 : CodeIn mC6.mem P scalar29PackCode := by
    rw [MC6]; exact (((((((hcC5.store8 (sOC.sub (c := 14) (l := 1) (by decide))).store8 (sOC.sub (c := 15) (l := 1) (by decide))).store8 (sOC.sub (c := 16) (l := 1) (by decide))).store8 (sOC.sub (c := 17) (l := 1) (by decide))).store8 (sOC.sub (c := 18) (l := 1) (by decide))).store8 (sOC.sub (c := 19) (l := 1) (by decide))).store8 (sOC.sub (c := 20) (l := 1) (by decide)))
  have uC6' : St mC6.mem P mC6 0x10A (reg mC6) := ⟨uC6.pc, rfl, fun _ => rfl⟩
  obtain ⟨mC7, cC7, uC7⟩ := St.block spkC7 uC6' hcC6 spkC7_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, spkC7, upd_app, ↓reduceIte, and_true]
    all_goals try simp only [RC6_10, RC6_11]
    all_goals repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hap ?_; decide) | exact sOC.sub (by decide))
  simp only [runBlock, BInstr.run, spkC7] at uC7
  have kC7 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mC7 q = reg mC6 q := fun q hq => by
    obtain ⟨h0, n0, n1, n2⟩ : q.val ≠ 0 ∧ q ≠ (9 : Fin 32) ∧ q ≠ a3 ∧ q ≠ a4 := by revert hq; revert q; decide
    rw [uC7.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1, upd_ne h0 n2]
  have RC7_5 : reg mC7 (5 : Fin 32) = l 7 := by
    rw [uC7.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC6_5
  have RC7_9 : reg mC7 (9 : Fin 32) = (l 6 >>> 18) := by
    rw [uC7.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC6_9]) <;> rfl
  have RC7_10 : reg mC7 a0 = out := by
    rw [uC7.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC6_10
  have RC7_11 : reg mC7 a1 = ap := by
    rw [uC7.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC6_11
  have RC7_12 : reg mC7 a2 = ((l 7 <<< 3) ||| (l 6 >>> 26)) := by
    rw [uC7.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC6_12
  have MC7 := uC7.mem
  simp +decide only [upd_app, ↓reduceIte] at MC7
  simp only [RC6_10, RC6_15, RC6_9] at MC7
  have fC7 : ∀ x, (∀ c ∈ [21, 22, 23], x ≠ out + BitVec.ofNat 32 c) → mC7.mem x = mC6.mem x := fun x h => by
    rw [MC7, memStore8_ne (a := out + 0x17) (h 23 (by decide)), memStore8_ne (a := out + 0x16) (h 22 (by decide)), memStore8_ne (a := out + 0x15) (h 21 (by decide))]
  have B21 : mC7.mem (out + 0x15) = s29PackByte l 21 := by
    rw [MC7, memStore8_ne (x := out + 0x15) (a := out + 0x17) (add_ofNat_ne out (c := 21) (d := 23) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x15) (a := out + 0x16) (add_ofNat_ne out (c := 21) (d := 22) (by decide) (by decide) (by decide)), memStore8_same]
    exact congrArg (BitVec.extractLsb' 0 8) (BitVec.or_comm _ _)
  have B22 : mC7.mem (out + 0x16) = s29PackByte l 22 := by
    rw [MC7, memStore8_ne (x := out + 0x16) (a := out + 0x17) (add_ofNat_ne out (c := 22) (d := 23) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B23 : mC7.mem (out + 0x17) = s29PackByte l 23 := by
    rw [MC7, memStore8_same]
    rfl
  have hcC7 : CodeIn mC7.mem P scalar29PackCode := by
    rw [MC7]; exact (((hcC6.store8 (sOC.sub (c := 21) (l := 1) (by decide))).store8 (sOC.sub (c := 22) (l := 1) (by decide))).store8 (sOC.sub (c := 23) (l := 1) (by decide)))
  have uC7' : St mC7.mem P mC7 0x120 (reg mC7) := ⟨uC7.pc, rfl, fun _ => rfl⟩
  have fO7 : ∀ x, Sep out 32 x 1 → mC7.mem x = Msv x := fun x hx => by
    rw [fC7 x (outFr hx _ (by decide)), fC6 x (outFr hx _ (by decide)), fC5 x (outFr hx _ (by decide)), fC4 x (outFr hx _ (by decide))]
  have L8v : memLoad32 mC7.mem (ap + 0x20) = l 8 := by
    rw [← LA8]; show memLoad32 mC7.mem (ap + BitVec.ofNat 32 0x20) = memLoad32 Msv (ap + BitVec.ofNat 32 0x20)
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact fO7 _ (sOA.subR (c := 0x20 + j) (l := 1) (by omega))
  obtain ⟨mL8, cL8, uL8⟩ := St.block spkL8 uC7' hcC7 spkL8_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, spkL8, upd_app, ↓reduceIte, and_true]
    all_goals try simp only [RC7_10, RC7_11]
    all_goals repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hap ?_; decide) | exact sOC.sub (by decide))
  simp only [runBlock, BInstr.run, spkL8] at uL8
  have kL8 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mL8 q = reg mC7 q := fun q hq => by
    obtain ⟨h0, n0⟩ : q.val ≠ 0 ∧ q ≠ a1 := by revert hq; revert q; decide
    rw [uL8.regs]; simp only [upd_ne h0 n0]
  have RL8_5 : reg mL8 (5 : Fin 32) = l 7 := by
    rw [uL8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC7_5
  have RL8_9 : reg mL8 (9 : Fin 32) = (l 6 >>> 18) := by
    rw [uL8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC7_9
  have RL8_10 : reg mL8 a0 = out := by
    rw [uL8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC7_10
  have RL8_11 : reg mL8 a1 = l 8 := by
    rw [uL8.regs]; simp +decide only [upd_app, ↓reduceIte]
    (try simp only [RC7_11, L8v]) <;> rfl
  have RL8_12 : reg mL8 a2 = ((l 7 <<< 3) ||| (l 6 >>> 26)) := by
    rw [uL8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RC7_12
  obtain ⟨mB2, cB2, uB2⟩ := St.block spkB2 uL8.self hcC7 spkB2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, spkB2, upd_app, ↓reduceIte, and_true]
    all_goals try simp only [RL8_10, RL8_11]
    all_goals repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hap ?_; decide) | exact sOC.sub (by decide))
  simp only [runBlock, BInstr.run, spkB2] at uB2
  have kB2 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mB2 q = reg mL8 q := fun q hq => by
    obtain ⟨h0, n0, n1, n2⟩ : q.val ≠ 0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 := by revert hq; revert q; decide
    rw [uB2.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1, upd_ne h0 n2]
  have RB2_10 : reg mB2 a0 = out := by
    rw [uB2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RL8_10
  have MB2 := uB2.mem
  simp +decide only [upd_app, ↓reduceIte] at MB2
  simp only [RL8_10, RL8_11, RL8_12, RL8_5, RL8_9] at MB2
  have fB2 : ∀ x, (∀ c ∈ [24, 25, 26, 27, 28, 29, 30, 31], x ≠ out + BitVec.ofNat 32 c) → mB2.mem x = mC7.mem x := fun x h => by
    rw [MB2, memStore8_ne (a := out + 0x1F) (h 31 (by decide)), memStore8_ne (a := out + 0x1E) (h 30 (by decide)), memStore8_ne (a := out + 0x1D) (h 29 (by decide)), memStore8_ne (a := out + 0x1C) (h 28 (by decide)), memStore8_ne (a := out + 0x1B) (h 27 (by decide)), memStore8_ne (a := out + 0x1A) (h 26 (by decide)), memStore8_ne (a := out + 0x19) (h 25 (by decide)), memStore8_ne (a := out + 0x18) (h 24 (by decide))]
  have B24 : mB2.mem (out + 0x18) = s29PackByte l 24 := by
    rw [MB2, memStore8_ne (x := out + 0x18) (a := out + 0x1F) (add_ofNat_ne out (c := 24) (d := 31) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x18) (a := out + 0x1E) (add_ofNat_ne out (c := 24) (d := 30) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x18) (a := out + 0x1D) (add_ofNat_ne out (c := 24) (d := 29) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x18) (a := out + 0x1C) (add_ofNat_ne out (c := 24) (d := 28) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x18) (a := out + 0x1B) (add_ofNat_ne out (c := 24) (d := 27) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x18) (a := out + 0x1A) (add_ofNat_ne out (c := 24) (d := 26) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x18) (a := out + 0x19) (add_ofNat_ne out (c := 24) (d := 25) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B25 : mB2.mem (out + 0x19) = s29PackByte l 25 := by
    rw [MB2, memStore8_ne (x := out + 0x19) (a := out + 0x1F) (add_ofNat_ne out (c := 25) (d := 31) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x19) (a := out + 0x1E) (add_ofNat_ne out (c := 25) (d := 30) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x19) (a := out + 0x1D) (add_ofNat_ne out (c := 25) (d := 29) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x19) (a := out + 0x1C) (add_ofNat_ne out (c := 25) (d := 28) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x19) (a := out + 0x1B) (add_ofNat_ne out (c := 25) (d := 27) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x19) (a := out + 0x1A) (add_ofNat_ne out (c := 25) (d := 26) (by decide) (by decide) (by decide)), memStore8_same]
    exact congrArg (BitVec.extractLsb' 0 8) (BitVec.or_comm _ _)
  have B26 : mB2.mem (out + 0x1A) = s29PackByte l 26 := by
    rw [MB2, memStore8_ne (x := out + 0x1A) (a := out + 0x1F) (add_ofNat_ne out (c := 26) (d := 31) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1A) (a := out + 0x1E) (add_ofNat_ne out (c := 26) (d := 30) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1A) (a := out + 0x1D) (add_ofNat_ne out (c := 26) (d := 29) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1A) (a := out + 0x1C) (add_ofNat_ne out (c := 26) (d := 28) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1A) (a := out + 0x1B) (add_ofNat_ne out (c := 26) (d := 27) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B27 : mB2.mem (out + 0x1B) = s29PackByte l 27 := by
    rw [MB2, memStore8_ne (x := out + 0x1B) (a := out + 0x1F) (add_ofNat_ne out (c := 27) (d := 31) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1B) (a := out + 0x1E) (add_ofNat_ne out (c := 27) (d := 30) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1B) (a := out + 0x1D) (add_ofNat_ne out (c := 27) (d := 29) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1B) (a := out + 0x1C) (add_ofNat_ne out (c := 27) (d := 28) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B28 : mB2.mem (out + 0x1C) = s29PackByte l 28 := by
    rw [MB2, memStore8_ne (x := out + 0x1C) (a := out + 0x1F) (add_ofNat_ne out (c := 28) (d := 31) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1C) (a := out + 0x1E) (add_ofNat_ne out (c := 28) (d := 30) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1C) (a := out + 0x1D) (add_ofNat_ne out (c := 28) (d := 29) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B29 : mB2.mem (out + 0x1D) = s29PackByte l 29 := by
    rw [MB2, memStore8_ne (x := out + 0x1D) (a := out + 0x1F) (add_ofNat_ne out (c := 29) (d := 31) (by decide) (by decide) (by decide)), memStore8_ne (x := out + 0x1D) (a := out + 0x1E) (add_ofNat_ne out (c := 29) (d := 30) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B30 : mB2.mem (out + 0x1E) = s29PackByte l 30 := by
    rw [MB2, memStore8_ne (x := out + 0x1E) (a := out + 0x1F) (add_ofNat_ne out (c := 30) (d := 31) (by decide) (by decide) (by decide)), memStore8_same]
    rfl
  have B31 : mB2.mem (out + 0x1F) = s29PackByte l 31 := by
    rw [MB2, memStore8_same]
    rfl
  have hcB2 : CodeIn mB2.mem P scalar29PackCode := by
    rw [MB2]; exact ((((((((hcC7.store8 (sOC.sub (c := 24) (l := 1) (by decide))).store8 (sOC.sub (c := 25) (l := 1) (by decide))).store8 (sOC.sub (c := 26) (l := 1) (by decide))).store8 (sOC.sub (c := 27) (l := 1) (by decide))).store8 (sOC.sub (c := 28) (l := 1) (by decide))).store8 (sOC.sub (c := 29) (l := 1) (by decide))).store8 (sOC.sub (c := 30) (l := 1) (by decide))).store8 (sOC.sub (c := 31) (l := 1) (by decide)))
  have uB2' : St mB2.mem P mB2 0x154 (reg mB2) := ⟨uB2.pc, rfl, fun _ => rfl⟩
  have fOut : ∀ x, Sep out 32 x 1 → mB2.mem x = Msv x := fun x hx => by
    rw [fB2 x (outFr hx _ (by decide)), fO7 x hx]
  have bytes : ∀ j, j < 32 → mB2.mem (out + BitVec.ofNat 32 j) = s29PackByte (limbs m.mem ap) j := by
    intro j hj
    rw [hl]
    match j, hj with
    | 0, _ => rw [fB2 _ (outNe out 0 _ (by decide)), fC7 _ (outNe out 0 _ (by decide)), fC6 _ (outNe out 0 _ (by decide)), fC5 _ (outNe out 0 _ (by decide))]; exact B0
    | 1, _ => rw [fB2 _ (outNe out 1 _ (by decide)), fC7 _ (outNe out 1 _ (by decide)), fC6 _ (outNe out 1 _ (by decide)), fC5 _ (outNe out 1 _ (by decide))]; exact B1
    | 2, _ => rw [fB2 _ (outNe out 2 _ (by decide)), fC7 _ (outNe out 2 _ (by decide)), fC6 _ (outNe out 2 _ (by decide)), fC5 _ (outNe out 2 _ (by decide))]; exact B2
    | 3, _ => rw [fB2 _ (outNe out 3 _ (by decide)), fC7 _ (outNe out 3 _ (by decide)), fC6 _ (outNe out 3 _ (by decide)), fC5 _ (outNe out 3 _ (by decide))]; exact B3
    | 4, _ => rw [fB2 _ (outNe out 4 _ (by decide)), fC7 _ (outNe out 4 _ (by decide)), fC6 _ (outNe out 4 _ (by decide)), fC5 _ (outNe out 4 _ (by decide))]; exact B4
    | 5, _ => rw [fB2 _ (outNe out 5 _ (by decide)), fC7 _ (outNe out 5 _ (by decide)), fC6 _ (outNe out 5 _ (by decide)), fC5 _ (outNe out 5 _ (by decide))]; exact B5
    | 6, _ => rw [fB2 _ (outNe out 6 _ (by decide)), fC7 _ (outNe out 6 _ (by decide)), fC6 _ (outNe out 6 _ (by decide)), fC5 _ (outNe out 6 _ (by decide))]; exact B6
    | 7, _ => rw [fB2 _ (outNe out 7 _ (by decide)), fC7 _ (outNe out 7 _ (by decide)), fC6 _ (outNe out 7 _ (by decide)), fC5 _ (outNe out 7 _ (by decide))]; exact B7
    | 8, _ => rw [fB2 _ (outNe out 8 _ (by decide)), fC7 _ (outNe out 8 _ (by decide)), fC6 _ (outNe out 8 _ (by decide))]; exact B8
    | 9, _ => rw [fB2 _ (outNe out 9 _ (by decide)), fC7 _ (outNe out 9 _ (by decide)), fC6 _ (outNe out 9 _ (by decide))]; exact B9
    | 10, _ => rw [fB2 _ (outNe out 10 _ (by decide)), fC7 _ (outNe out 10 _ (by decide)), fC6 _ (outNe out 10 _ (by decide))]; exact B10
    | 11, _ => rw [fB2 _ (outNe out 11 _ (by decide)), fC7 _ (outNe out 11 _ (by decide)), fC6 _ (outNe out 11 _ (by decide))]; exact B11
    | 12, _ => rw [fB2 _ (outNe out 12 _ (by decide)), fC7 _ (outNe out 12 _ (by decide)), fC6 _ (outNe out 12 _ (by decide))]; exact B12
    | 13, _ => rw [fB2 _ (outNe out 13 _ (by decide)), fC7 _ (outNe out 13 _ (by decide)), fC6 _ (outNe out 13 _ (by decide))]; exact B13
    | 14, _ => rw [fB2 _ (outNe out 14 _ (by decide)), fC7 _ (outNe out 14 _ (by decide))]; exact B14
    | 15, _ => rw [fB2 _ (outNe out 15 _ (by decide)), fC7 _ (outNe out 15 _ (by decide))]; exact B15
    | 16, _ => rw [fB2 _ (outNe out 16 _ (by decide)), fC7 _ (outNe out 16 _ (by decide))]; exact B16
    | 17, _ => rw [fB2 _ (outNe out 17 _ (by decide)), fC7 _ (outNe out 17 _ (by decide))]; exact B17
    | 18, _ => rw [fB2 _ (outNe out 18 _ (by decide)), fC7 _ (outNe out 18 _ (by decide))]; exact B18
    | 19, _ => rw [fB2 _ (outNe out 19 _ (by decide)), fC7 _ (outNe out 19 _ (by decide))]; exact B19
    | 20, _ => rw [fB2 _ (outNe out 20 _ (by decide)), fC7 _ (outNe out 20 _ (by decide))]; exact B20
    | 21, _ => rw [fB2 _ (outNe out 21 _ (by decide))]; exact B21
    | 22, _ => rw [fB2 _ (outNe out 22 _ (by decide))]; exact B22
    | 23, _ => rw [fB2 _ (outNe out 23 _ (by decide))]; exact B23
    | 24, _ => exact B24
    | 25, _ => exact B25
    | 26, _ => exact B26
    | 27, _ => exact B27
    | 28, _ => exact B28
    | 29, _ => exact B29
    | 30, _ => exact B30
    | 31, _ => exact B31
    | _ + 32, h => exact absurd h (by omega)
  have keepB2 : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mB2 q = reg ms q := fun q hq => by
    rw [kB2 q hq, kL8 q hq, kC7 q hq, kC6 q hq, kC5 q hq, kC4 q hq, kC3 q hq, kC2 q hq, kC1 q hq]
  have hslB : ∀ r o, (r, o) ∈ spkPs → memLoad32 mB2.mem (F + o) = reg m r := fun r o h => by
    have ho : 0xC ≤ o.toNat ∧ o.toNat + 4 ≤ 0x20 := by
      simp only [spkPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, fOut _ (sOG.subR (c := o.toNat + j) (l := 1) (by omega))]
  have spY : reg mB2 sp = F := (keepB2 sp (by decide)).trans sp2
  have hpsp : ∀ p ∈ spkPs, p.1 ≠ sp := by decide
  obtain ⟨e1, ce1, ue1⟩ := St.block (restoreBlock spkPs) uB2' hcB2 spkRestore_end
    (restoreBlock_ok mB2.mem F spkPs _ spY hpsp fun q hq => by
      simp only [spkPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run mB2.mem F spkPs _ spY hpsp] at ue1
  obtain ⟨e2, de2, ue2⟩ := ue1.aluImm hcB2 spk_at_15e (off' := 0x160) (by decide)
  obtain ⟨e3, de3, pc3, mem3, regs3⟩ := ue2.jalr hcB2 spk_at_160
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs mB2.mem F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ spkPs → restoreRegs mB2.mem F (reg mB2) spkPs r = reg m r := fun r o hm => by
    simp only [spkPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hslB _ _ (by decide)
  have rsp : restoreRegs mB2.mem F (reg mB2) spkPs sp = F := by rw [rr _ _ sp (by decide) (by decide)]; exact spY
  have keepM : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg mB2 q = reg m q := fun q hq => by
    obtain ⟨h1, h2⟩ : q.val ∈ [1, 2, 3, 4, 21, 22, 23, 24, 25, 26, 27] ∧ q ≠ sp := by revert hq; revert q; decide
    exact (keepB2 q h1).trans (r2 q h2)
  have S : Steps m mB2 := .cons d1 (cs.trans (cC1.trans (cC2.trans (cC3.trans (cC4.trans (cC5.trans (cC6.trans
    (cC7.trans (cL8.trans cB2)))))))))
  refine ⟨e3, S.trans (ce1.trans (.cons de2 (.single de3))), ?_, ?_, fun q hq => ?_, fun j hj => ?_, fun x hx ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
    rw [rr _ _ ra (by decide) (by decide), keepM ra (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp, eS]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
          (q.val ∈ [1, 3, 4, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ spkPs, p.1 ≠ q)) := by decide
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x1C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x18 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x14 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x10 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xC (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact keepM q h1
  · rw [mem3]; exact bytes j hj
  · rw [mem3, fOut x ho, frSv x hx]

end C3.RV32
