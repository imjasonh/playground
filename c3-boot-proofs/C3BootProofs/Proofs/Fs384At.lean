import C3BootProofs.Proofs.P384Mont

/-! Fetch lemmas for `VerifyingKey<NistP384>::from_sec1_bytes` (`p384FromSec1Code`). -/

namespace C3.RV32.Fs

open C3.Image

/-- Where `from_sec1_bytes` is in the image. -/
abbrev FP : Word := BitVec.ofNat 32 p384FromSec1Address

set_option maxRecDepth 20000

theorem fs_at_0 : fetchRel p384FromSec1Code 0x0 = some (.aluImm .add sp sp 0xFFFFFBE0, 4) := by decide
theorem fs_at_4 : fetchRel p384FromSec1Code 0x4 = some (.aluImm .add a2 sp 0x400, 4) := by decide
theorem fs_at_8 : fetchRel p384FromSec1Code 0x8 = some (.store .sw a2 ra 0x1C, 4) := by decide
theorem fs_at_c : fetchRel p384FromSec1Code 0xC = some (.store .sw a2 (8 : Fin 32) 0x18, 2) := by decide
theorem fs_at_e : fetchRel p384FromSec1Code 0xE = some (.store .sw a2 (9 : Fin 32) 0x14, 2) := by decide
theorem fs_at_10 : fetchRel p384FromSec1Code 0x10 = some (.store .sw a2 (18 : Fin 32) 0x10, 4) := by decide
theorem fs_at_14 : fetchRel p384FromSec1Code 0x14 = some (.store .sw a2 (19 : Fin 32) 0xC, 4) := by decide
theorem fs_at_18 : fetchRel p384FromSec1Code 0x18 = some (.store .sw a2 (20 : Fin 32) 0x8, 4) := by decide
theorem fs_at_1c : fetchRel p384FromSec1Code 0x1C = some (.store .sw a2 (21 : Fin 32) 0x4, 4) := by decide
theorem fs_at_20 : fetchRel p384FromSec1Code 0x20 = some (.store .sw a2 (22 : Fin 32) 0x0, 4) := by decide
theorem fs_at_24 : fetchRel p384FromSec1Code 0x24 = some (.aluImm .add a2 sp 0x380, 2) := by decide
theorem fs_at_26 : fetchRel p384FromSec1Code 0x26 = some (.store .sw a2 (23 : Fin 32) 0x7C, 4) := by decide
theorem fs_at_2a : fetchRel p384FromSec1Code 0x2A = some (.store .sw a2 (24 : Fin 32) 0x78, 4) := by decide
theorem fs_at_2e : fetchRel p384FromSec1Code 0x2E = some (.store .sw a2 (25 : Fin 32) 0x74, 4) := by decide
theorem fs_at_32 : fetchRel p384FromSec1Code 0x32 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem fs_at_34 : fetchRel p384FromSec1Code 0x34 = some (.alu .add (24 : Fin 32) x0 a0, 2) := by decide
theorem fs_at_36 : fetchRel p384FromSec1Code 0x36 = some (.load .lbu a0 a1 0x0, 4) := by decide
theorem fs_at_3a : fetchRel p384FromSec1Code 0x3A = some (.aluImm .add (8 : Fin 32) x0 0xFFFFFFFF, 2) := by decide
theorem fs_at_3c : fetchRel p384FromSec1Code 0x3C = some (.store .sw sp (8 : Fin 32) 0x144, 4) := by decide
theorem fs_at_40 : fetchRel p384FromSec1Code 0x40 = some (.store .sb sp a0 0x148, 4) := by decide
theorem fs_at_44 : fetchRel p384FromSec1Code 0x44 = some (.aluImm .add a0 sp 0xDC, 2) := by decide
theorem fs_at_46 : fetchRel p384FromSec1Code 0x46 = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem fs_at_48 : fetchRel p384FromSec1Code 0x48 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem fs_at_4c : fetchRel p384FromSec1Code 0x4C = some (.jalr ra ra 0xF8, 4) := by decide
theorem fs_at_50 : fetchRel p384FromSec1Code 0x50 = some (.load .lw a0 sp 0xDC, 2) := by decide
theorem fs_at_52 : fetchRel p384FromSec1Code 0x52 = some (.branch .beq a0 (8 : Fin 32) 0x18, 4) := by decide
theorem fs_at_56 : fetchRel p384FromSec1Code 0x56 = some (.aluImm .add a1 sp 0xE1, 4) := by decide
theorem fs_at_5a : fetchRel p384FromSec1Code 0x5A = some (.aluImm .add a0 sp 0x210, 2) := by decide
theorem fs_at_5c : fetchRel p384FromSec1Code 0x5C = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem fs_at_60 : fetchRel p384FromSec1Code 0x60 = some (.auipc ra 0x10000, 4) := by decide
theorem fs_at_64 : fetchRel p384FromSec1Code 0x64 = some (.jalr ra ra 0xFFFFFA94, 4) := by decide
theorem fs_at_68 : fetchRel p384FromSec1Code 0x68 = some (.jal x0 0x3E2, 2) := by decide
theorem fs_at_6a : fetchRel p384FromSec1Code 0x6A = some (.load .lbu a0 sp 0xE0, 4) := by decide
theorem fs_at_6e : fetchRel p384FromSec1Code 0x6E = some (.aluImm .add a1 x0 0x30, 4) := by decide
theorem fs_at_72 : fetchRel p384FromSec1Code 0x72 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem fs_at_76 : fetchRel p384FromSec1Code 0x76 = some (.jalr ra ra 0xEE, 4) := by decide
theorem fs_at_7a : fetchRel p384FromSec1Code 0x7A = some (.aluImm .add a0 a0 0xFFFFFF9F, 4) := by decide
theorem fs_at_7e : fetchRel p384FromSec1Code 0x7E = some (.branch .bne a0 x0 0x3CC, 4) := by decide
theorem fs_at_82 : fetchRel p384FromSec1Code 0x82 = some (.aluImm .add (18 : Fin 32) sp 0x2A4, 4) := by decide
theorem fs_at_86 : fetchRel p384FromSec1Code 0x86 = some (.aluImm .add a0 x0 0x61, 4) := by decide
theorem fs_at_8a : fetchRel p384FromSec1Code 0x8A = some (.branch .beq a0 x0 0x6, 2) := by decide
theorem fs_at_8c : fetchRel p384FromSec1Code 0x8C = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem fs_at_8e : fetchRel p384FromSec1Code 0x8E = some (.branch .bne a0 x0 0xFFFFFFFE, 2) := by decide
theorem fs_at_90 : fetchRel p384FromSec1Code 0x90 = some (.load .lbu a0 (9 : Fin 32) 0x1, 4) := by decide
theorem fs_at_94 : fetchRel p384FromSec1Code 0x94 = some (.load .lbu a1 (9 : Fin 32) 0x0, 4) := by decide
theorem fs_at_98 : fetchRel p384FromSec1Code 0x98 = some (.load .lbu a2 (9 : Fin 32) 0x2, 4) := by decide
theorem fs_at_9c : fetchRel p384FromSec1Code 0x9C = some (.load .lbu (8 : Fin 32) (9 : Fin 32) 0x3, 4) := by decide
theorem fs_at_a0 : fetchRel p384FromSec1Code 0xA0 = some (.load .lbu (19 : Fin 32) (9 : Fin 32) 0x4, 4) := by decide
theorem fs_at_a4 : fetchRel p384FromSec1Code 0xA4 = some (.load .lbu (20 : Fin 32) (9 : Fin 32) 0x5, 4) := by decide
theorem fs_at_a8 : fetchRel p384FromSec1Code 0xA8 = some (.load .lbu (21 : Fin 32) (9 : Fin 32) 0x6, 4) := by decide
theorem fs_at_ac : fetchRel p384FromSec1Code 0xAC = some (.load .lbu (22 : Fin 32) (9 : Fin 32) 0x7, 4) := by decide
theorem fs_at_b0 : fetchRel p384FromSec1Code 0xB0 = some (.aluImm .sll a0 a0 0x8, 2) := by decide
theorem fs_at_b2 : fetchRel p384FromSec1Code 0xB2 = some (.alu .or a0 a0 a1, 2) := by decide
theorem fs_at_b4 : fetchRel p384FromSec1Code 0xB4 = some (.aluImm .add a1 (9 : Fin 32) 0x8, 4) := by decide
theorem fs_at_b8 : fetchRel p384FromSec1Code 0xB8 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x37, 4) := by decide
theorem fs_at_bc : fetchRel p384FromSec1Code 0xBC = some (.store .sh sp a0 0x394, 4) := by decide
theorem fs_at_c0 : fetchRel p384FromSec1Code 0xC0 = some (.store .sb sp a2 0x396, 4) := by decide
theorem fs_at_c4 : fetchRel p384FromSec1Code 0xC4 = some (.aluImm .add a0 sp 0x210, 2) := by decide
theorem fs_at_c6 : fetchRel p384FromSec1Code 0xC6 = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem fs_at_ca : fetchRel p384FromSec1Code 0xCA = some (.auipc ra 0x10000, 4) := by decide
theorem fs_at_ce : fetchRel p384FromSec1Code 0xCE = some (.jalr ra ra 0xFFFFFA2A, 4) := by decide
theorem fs_at_d2 : fetchRel p384FromSec1Code 0xD2 = some (.aluImm .add a0 sp 0x1AC, 2) := by decide
theorem fs_at_d4 : fetchRel p384FromSec1Code 0xD4 = some (.aluImm .add a2 x0 0x2A, 4) := by decide
theorem fs_at_d8 : fetchRel p384FromSec1Code 0xD8 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem fs_at_da : fetchRel p384FromSec1Code 0xDA = some (.auipc ra 0x10000, 4) := by decide
theorem fs_at_de : fetchRel p384FromSec1Code 0xDE = some (.jalr ra ra 0xFFFFFA1A, 4) := by decide
theorem fs_at_e2 : fetchRel p384FromSec1Code 0xE2 = some (.load .lh a0 sp 0x394, 4) := by decide
theorem fs_at_e6 : fetchRel p384FromSec1Code 0xE6 = some (.load .lbu a1 sp 0x396, 4) := by decide
theorem fs_at_ea : fetchRel p384FromSec1Code 0xEA = some (.store .sh sp a0 0x12, 4) := by decide
theorem fs_at_ee : fetchRel p384FromSec1Code 0xEE = some (.store .sb sp a1 0x14, 4) := by decide
theorem fs_at_f2 : fetchRel p384FromSec1Code 0xF2 = some (.store .sb sp (8 : Fin 32) 0x15, 4) := by decide
theorem fs_at_f6 : fetchRel p384FromSec1Code 0xF6 = some (.store .sb sp (19 : Fin 32) 0x16, 4) := by decide
theorem fs_at_fa : fetchRel p384FromSec1Code 0xFA = some (.store .sb sp (20 : Fin 32) 0x17, 4) := by decide
theorem fs_at_fe : fetchRel p384FromSec1Code 0xFE = some (.store .sb sp (21 : Fin 32) 0x18, 4) := by decide
theorem fs_at_102 : fetchRel p384FromSec1Code 0x102 = some (.store .sb sp (22 : Fin 32) 0x19, 4) := by decide
theorem fs_at_106 : fetchRel p384FromSec1Code 0x106 = some (.aluImm .add a0 sp 0x1A, 4) := by decide
theorem fs_at_10a : fetchRel p384FromSec1Code 0x10A = some (.aluImm .add a1 sp 0x210, 2) := by decide
theorem fs_at_10c : fetchRel p384FromSec1Code 0x10C = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem fs_at_110 : fetchRel p384FromSec1Code 0x110 = some (.auipc ra 0x10000, 4) := by decide
theorem fs_at_114 : fetchRel p384FromSec1Code 0x114 = some (.jalr ra ra 0xFFFFF9E4, 4) := by decide
theorem fs_at_118 : fetchRel p384FromSec1Code 0x118 = some (.aluImm .add a0 sp 0x49, 4) := by decide
theorem fs_at_11c : fetchRel p384FromSec1Code 0x11C = some (.aluImm .add a1 sp 0x1AC, 2) := by decide
theorem fs_at_11e : fetchRel p384FromSec1Code 0x11E = some (.aluImm .add a2 x0 0x2A, 4) := by decide
theorem fs_at_122 : fetchRel p384FromSec1Code 0x122 = some (.auipc ra 0x10000, 4) := by decide
theorem fs_at_126 : fetchRel p384FromSec1Code 0x126 = some (.jalr ra ra 0xFFFFF9D2, 4) := by decide
theorem fs_at_12a : fetchRel p384FromSec1Code 0x12A = some (.load .lbu (22 : Fin 32) sp 0x12, 4) := by decide
theorem fs_at_12e : fetchRel p384FromSec1Code 0x12E = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem fs_at_130 : fetchRel p384FromSec1Code 0x130 = some (.auipc ra 0x0, 4) := by decide
theorem fs_at_134 : fetchRel p384FromSec1Code 0x134 = some (.jalr ra ra 0x354, 4) := by decide
theorem fs_at_138 : fetchRel p384FromSec1Code 0x138 = some (.branch .beq a0 x0 0x20, 2) := by decide
theorem fs_at_13a : fetchRel p384FromSec1Code 0x13A = some (.lui a1 0x3FCC4000, 4) := by decide
theorem fs_at_13e : fetchRel p384FromSec1Code 0x13E = some (.aluImm .add a1 a1 0x3C8, 4) := by decide
theorem fs_at_142 : fetchRel p384FromSec1Code 0x142 = some (.aluImm .add a0 sp 0x74, 2) := by decide
theorem fs_at_144 : fetchRel p384FromSec1Code 0x144 = some (.aluImm .add a2 x0 0x64, 4) := by decide
theorem fs_at_148 : fetchRel p384FromSec1Code 0x148 = some (.auipc ra 0x10000, 4) := by decide
theorem fs_at_14c : fetchRel p384FromSec1Code 0x14C = some (.jalr ra ra 0xFFFFF9AC, 4) := by decide
theorem fs_at_150 : fetchRel p384FromSec1Code 0x150 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem fs_at_152 : fetchRel p384FromSec1Code 0x152 = some (.store .sb sp a0 0xD8, 4) := by decide
theorem fs_at_156 : fetchRel p384FromSec1Code 0x156 = some (.jal x0 0x2BE, 2) := by decide
theorem fs_at_158 : fetchRel p384FromSec1Code 0x158 = some (.aluImm .add (19 : Fin 32) sp 0x13, 4) := by decide
theorem fs_at_15c : fetchRel p384FromSec1Code 0x15C = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem fs_at_15e : fetchRel p384FromSec1Code 0x15E = some (.auipc ra 0x0, 4) := by decide
theorem fs_at_162 : fetchRel p384FromSec1Code 0x162 = some (.jalr ra ra 0x340, 4) := by decide
theorem fs_at_166 : fetchRel p384FromSec1Code 0x166 = some (.aluImm .and (8 : Fin 32) a0 0xFE, 4) := by decide
theorem fs_at_16a : fetchRel p384FromSec1Code 0x16A = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem fs_at_16c : fetchRel p384FromSec1Code 0x16C = some (.auipc ra 0x0, 4) := by decide
theorem fs_at_170 : fetchRel p384FromSec1Code 0x170 = some (.jalr ra ra 0x332, 4) := by decide
theorem fs_at_174 : fetchRel p384FromSec1Code 0x174 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem fs_at_176 : fetchRel p384FromSec1Code 0x176 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem fs_at_17a : fetchRel p384FromSec1Code 0x17A = some (.branch .bne (8 : Fin 32) a1 0x20, 4) := by decide
theorem fs_at_17e : fetchRel p384FromSec1Code 0x17E = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem fs_at_180 : fetchRel p384FromSec1Code 0x180 = some (.auipc ra 0x9000, 4) := by decide
theorem fs_at_184 : fetchRel p384FromSec1Code 0x184 = some (.jalr ra ra 0xFFFFF86A, 4) := by decide
theorem fs_at_188 : fetchRel p384FromSec1Code 0x188 = some (.aluImm .and a2 a0 0xFF, 4) := by decide
theorem fs_at_18c : fetchRel p384FromSec1Code 0x18C = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem fs_at_18e : fetchRel p384FromSec1Code 0x18E = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem fs_at_190 : fetchRel p384FromSec1Code 0x190 = some (.auipc ra 0x0, 4) := by decide
theorem fs_at_194 : fetchRel p384FromSec1Code 0x194 = some (.jalr ra ra 0x378, 4) := by decide
theorem fs_at_198 : fetchRel p384FromSec1Code 0x198 = some (.jal x0 0x270, 2) := by decide
theorem fs_at_19a : fetchRel p384FromSec1Code 0x19A = some (.aluImm .add a1 x0 0x5, 2) := by decide
theorem fs_at_19c : fetchRel p384FromSec1Code 0x19C = some (.branch .bne a0 a1 0x140, 4) := by decide
theorem fs_at_1a0 : fetchRel p384FromSec1Code 0x1A0 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem fs_at_1a2 : fetchRel p384FromSec1Code 0x1A2 = some (.auipc ra 0x9000, 4) := by decide
theorem fs_at_1a6 : fetchRel p384FromSec1Code 0x1A6 = some (.jalr ra ra 0xFFFFF848, 4) := by decide
theorem fs_at_1aa : fetchRel p384FromSec1Code 0x1AA = some (.aluImm .and a2 a0 0xFF, 4) := by decide
theorem fs_at_1ae : fetchRel p384FromSec1Code 0x1AE = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem fs_at_1b0 : fetchRel p384FromSec1Code 0x1B0 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem fs_at_1b2 : fetchRel p384FromSec1Code 0x1B2 = some (.auipc ra 0x0, 4) := by decide
theorem fs_at_1b6 : fetchRel p384FromSec1Code 0x1B6 = some (.jalr ra ra 0x356, 4) := by decide
theorem fs_at_1ba : fetchRel p384FromSec1Code 0x1BA = some (.load .lbu (19 : Fin 32) sp 0x1A8, 4) := by decide
theorem fs_at_1be : fetchRel p384FromSec1Code 0x1BE = some (.lui (9 : Fin 32) 0x3FCC4000, 4) := by decide
theorem fs_at_1c2 : fetchRel p384FromSec1Code 0x1C2 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x3C8, 4) := by decide
theorem fs_at_1c6 : fetchRel p384FromSec1Code 0x1C6 = some (.aluImm .add a0 sp 0x274, 2) := by decide
theorem fs_at_1c8 : fetchRel p384FromSec1Code 0x1C8 = some (.aluImm .add a2 sp 0x144, 2) := by decide
theorem fs_at_1ca : fetchRel p384FromSec1Code 0x1CA = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem fs_at_1cc : fetchRel p384FromSec1Code 0x1CC = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem fs_at_1ce : fetchRel p384FromSec1Code 0x1CE = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_1d2 : fetchRel p384FromSec1Code 0x1D2 = some (.jalr ra ra 0xFFFFF90C, 4) := by decide
theorem fs_at_1d6 : fetchRel p384FromSec1Code 0x1D6 = some (.aluImm .add a2 sp 0x174, 2) := by decide
theorem fs_at_1d8 : fetchRel p384FromSec1Code 0x1D8 = some (.aluImm .add a0 sp 0x2A4, 2) := by decide
theorem fs_at_1da : fetchRel p384FromSec1Code 0x1DA = some (.aluImm .add a1 (9 : Fin 32) 0x30, 4) := by decide
theorem fs_at_1de : fetchRel p384FromSec1Code 0x1DE = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem fs_at_1e0 : fetchRel p384FromSec1Code 0x1E0 = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_1e4 : fetchRel p384FromSec1Code 0x1E4 = some (.jalr ra ra 0xFFFFF8FA, 4) := by decide
theorem fs_at_1e8 : fetchRel p384FromSec1Code 0x1E8 = some (.load .lbu a0 sp 0x1A4, 4) := by decide
theorem fs_at_1ec : fetchRel p384FromSec1Code 0x1EC = some (.alu .sub a1 x0 (19 : Fin 32), 4) := by decide
theorem fs_at_1f0 : fetchRel p384FromSec1Code 0x1F0 = some (.aluImm .xor a0 a0 0x1, 4) := by decide
theorem fs_at_1f4 : fetchRel p384FromSec1Code 0x1F4 = some (.alu .and a0 a0 a1, 2) := by decide
theorem fs_at_1f6 : fetchRel p384FromSec1Code 0x1F6 = some (.aluImm .xor (23 : Fin 32) a0 0x1, 4) := by decide
theorem fs_at_1fa : fetchRel p384FromSec1Code 0x1FA = some (.aluImm .add a0 sp 0x1AC, 2) := by decide
theorem fs_at_1fc : fetchRel p384FromSec1Code 0x1FC = some (.aluImm .add a1 sp 0x274, 2) := by decide
theorem fs_at_1fe : fetchRel p384FromSec1Code 0x1FE = some (.aluImm .add a2 x0 0x60, 4) := by decide
theorem fs_at_202 : fetchRel p384FromSec1Code 0x202 = some (.auipc ra 0x10000, 4) := by decide
theorem fs_at_206 : fetchRel p384FromSec1Code 0x206 = some (.jalr ra ra 0xFFFFF8F2, 4) := by decide
theorem fs_at_20a : fetchRel p384FromSec1Code 0x20A = some (.store .sb sp (23 : Fin 32) 0x20C, 4) := by decide
theorem fs_at_20e : fetchRel p384FromSec1Code 0x20E = some (.aluImm .add (20 : Fin 32) sp 0x1DC, 4) := by decide
theorem fs_at_212 : fetchRel p384FromSec1Code 0x212 = some (.aluImm .add (21 : Fin 32) sp 0x240, 4) := by decide
theorem fs_at_216 : fetchRel p384FromSec1Code 0x216 = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem fs_at_218 : fetchRel p384FromSec1Code 0x218 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem fs_at_21a : fetchRel p384FromSec1Code 0x21A = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem fs_at_21e : fetchRel p384FromSec1Code 0x21E = some (.jalr ra ra 0xFFFFF906, 4) := by decide
theorem fs_at_222 : fetchRel p384FromSec1Code 0x222 = some (.aluImm .add a0 sp 0x210, 2) := by decide
theorem fs_at_224 : fetchRel p384FromSec1Code 0x224 = some (.aluImm .add a1 sp 0x274, 2) := by decide
theorem fs_at_226 : fetchRel p384FromSec1Code 0x226 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem fs_at_22a : fetchRel p384FromSec1Code 0x22A = some (.auipc ra 0x10000, 4) := by decide
theorem fs_at_22e : fetchRel p384FromSec1Code 0x22E = some (.jalr ra ra 0xFFFFF8CA, 4) := by decide
theorem fs_at_232 : fetchRel p384FromSec1Code 0x232 = some (.store .sb sp (23 : Fin 32) 0x270, 4) := by decide
theorem fs_at_236 : fetchRel p384FromSec1Code 0x236 = some (.aluImm .add a0 sp 0x394, 2) := by decide
theorem fs_at_238 : fetchRel p384FromSec1Code 0x238 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem fs_at_23a : fetchRel p384FromSec1Code 0x23A = some (.aluImm .add (25 : Fin 32) sp 0x394, 4) := by decide
theorem fs_at_23e : fetchRel p384FromSec1Code 0x23E = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_242 : fetchRel p384FromSec1Code 0x242 = some (.jalr ra ra 0xFFFFFEFA, 4) := by decide
theorem fs_at_246 : fetchRel p384FromSec1Code 0x246 = some (.aluImm .add a0 sp 0xDC, 2) := by decide
theorem fs_at_248 : fetchRel p384FromSec1Code 0x248 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem fs_at_24a : fetchRel p384FromSec1Code 0x24A = some (.aluImm .add (9 : Fin 32) sp 0xDC, 2) := by decide
theorem fs_at_24c : fetchRel p384FromSec1Code 0x24C = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_250 : fetchRel p384FromSec1Code 0x250 = some (.jalr ra ra 0xFFFFFEEC, 4) := by decide
theorem fs_at_254 : fetchRel p384FromSec1Code 0x254 = some (.aluImm .add (18 : Fin 32) x0 0x0, 2) := by decide
theorem fs_at_256 : fetchRel p384FromSec1Code 0x256 = some (.aluImm .add (8 : Fin 32) x0 0xC, 2) := by decide
theorem fs_at_258 : fetchRel p384FromSec1Code 0x258 = some (.branch .beq (8 : Fin 32) x0 0x1C, 2) := by decide
theorem fs_at_25a : fetchRel p384FromSec1Code 0x25A = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem fs_at_25c : fetchRel p384FromSec1Code 0x25C = some (.load .lw a1 (25 : Fin 32) 0x0, 4) := by decide
theorem fs_at_260 : fetchRel p384FromSec1Code 0x260 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem fs_at_262 : fetchRel p384FromSec1Code 0x262 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem fs_at_266 : fetchRel p384FromSec1Code 0x266 = some (.jalr ra ra 0x364, 4) := by decide
theorem fs_at_26a : fetchRel p384FromSec1Code 0x26A = some (.alu .add (18 : Fin 32) x0 a1, 2) := by decide
theorem fs_at_26c : fetchRel p384FromSec1Code 0x26C = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem fs_at_26e : fetchRel p384FromSec1Code 0x26E = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x4, 2) := by decide
theorem fs_at_270 : fetchRel p384FromSec1Code 0x270 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem fs_at_272 : fetchRel p384FromSec1Code 0x272 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE8, 2) := by decide
theorem fs_at_274 : fetchRel p384FromSec1Code 0x274 = some (.aluImm .add a0 sp 0x3C4, 2) := by decide
theorem fs_at_276 : fetchRel p384FromSec1Code 0x276 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem fs_at_278 : fetchRel p384FromSec1Code 0x278 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem fs_at_27c : fetchRel p384FromSec1Code 0x27C = some (.jalr ra ra 0xFFFFFC9A, 4) := by decide
theorem fs_at_280 : fetchRel p384FromSec1Code 0x280 = some (.aluImm .add a1 sp 0x10C, 2) := by decide
theorem fs_at_282 : fetchRel p384FromSec1Code 0x282 = some (.aluImm .and (8 : Fin 32) a0 0xFF, 4) := by decide
theorem fs_at_286 : fetchRel p384FromSec1Code 0x286 = some (.alu .add a0 x0 a1, 2) := by decide
theorem fs_at_288 : fetchRel p384FromSec1Code 0x288 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem fs_at_28a : fetchRel p384FromSec1Code 0x28A = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem fs_at_28e : fetchRel p384FromSec1Code 0x28E = some (.jalr ra ra 0xFFFFFC88, 4) := by decide
theorem fs_at_292 : fetchRel p384FromSec1Code 0x292 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem fs_at_296 : fetchRel p384FromSec1Code 0x296 = some (.aluImm .xor a0 a0 0xFFFFFFFF, 4) := by decide
theorem fs_at_29a : fetchRel p384FromSec1Code 0x29A = some (.alu .and a0 (18 : Fin 32) a0, 4) := by decide
theorem fs_at_29e : fetchRel p384FromSec1Code 0x29E = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem fs_at_2a0 : fetchRel p384FromSec1Code 0x2A0 = some (.alu .or a0 a0 (8 : Fin 32), 2) := by decide
theorem fs_at_2a2 : fetchRel p384FromSec1Code 0x2A2 = some (.auipc ra 0x8000, 4) := by decide
theorem fs_at_2a6 : fetchRel p384FromSec1Code 0x2A6 = some (.jalr ra ra 0x748, 4) := by decide
theorem fs_at_2aa : fetchRel p384FromSec1Code 0x2AA = some (.aluImm .add a1 sp 0x10C, 2) := by decide
theorem fs_at_2ac : fetchRel p384FromSec1Code 0x2AC = some (.aluImm .and a3 a0 0xFF, 4) := by decide
theorem fs_at_2b0 : fetchRel p384FromSec1Code 0x2B0 = some (.alu .add a0 x0 a1, 2) := by decide
theorem fs_at_2b2 : fetchRel p384FromSec1Code 0x2B2 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem fs_at_2b4 : fetchRel p384FromSec1Code 0x2B4 = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem fs_at_2b6 : fetchRel p384FromSec1Code 0x2B6 = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_2ba : fetchRel p384FromSec1Code 0x2BA = some (.jalr ra ra 0xFFFFF824, 4) := by decide
theorem fs_at_2be : fetchRel p384FromSec1Code 0x2BE = some (.aluImm .add a0 sp 0xDC, 2) := by decide
theorem fs_at_2c0 : fetchRel p384FromSec1Code 0x2C0 = some (.aluImm .add a1 sp 0x274, 2) := by decide
theorem fs_at_2c2 : fetchRel p384FromSec1Code 0x2C2 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem fs_at_2c6 : fetchRel p384FromSec1Code 0x2C6 = some (.auipc ra 0x10000, 4) := by decide
theorem fs_at_2ca : fetchRel p384FromSec1Code 0x2CA = some (.jalr ra ra 0xFFFFF82E, 4) := by decide
theorem fs_at_2ce : fetchRel p384FromSec1Code 0x2CE = some (.store .sb sp (23 : Fin 32) 0x13C, 4) := by decide
theorem fs_at_2d2 : fetchRel p384FromSec1Code 0x2D2 = some (.store .sb sp (19 : Fin 32) 0x140, 4) := by decide
theorem fs_at_2d6 : fetchRel p384FromSec1Code 0x2D6 = some (.aluImm .add a0 sp 0x74, 2) := by decide
theorem fs_at_2d8 : fetchRel p384FromSec1Code 0x2D8 = some (.aluImm .add a1 sp 0xDC, 2) := by decide
theorem fs_at_2da : fetchRel p384FromSec1Code 0x2DA = some (.jal x0 0x132, 2) := by decide
theorem fs_at_2dc : fetchRel p384FromSec1Code 0x2DC = some (.aluImm .add a1 sp 0x43, 4) := by decide
theorem fs_at_2e0 : fetchRel p384FromSec1Code 0x2E0 = some (.aluImm .add a0 sp 0x210, 2) := by decide
theorem fs_at_2e2 : fetchRel p384FromSec1Code 0x2E2 = some (.auipc ra 0x1000, 4) := by decide
theorem fs_at_2e6 : fetchRel p384FromSec1Code 0x2E6 = some (.jalr ra ra 0xFFFFF956, 4) := by decide
theorem fs_at_2ea : fetchRel p384FromSec1Code 0x2EA = some (.aluImm .add a0 sp 0x2D4, 2) := by decide
theorem fs_at_2ec : fetchRel p384FromSec1Code 0x2EC = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem fs_at_2f0 : fetchRel p384FromSec1Code 0x2F0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem fs_at_2f2 : fetchRel p384FromSec1Code 0x2F2 = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_2f6 : fetchRel p384FromSec1Code 0x2F6 = some (.jalr ra ra 0x79A, 4) := by decide
theorem fs_at_2fa : fetchRel p384FromSec1Code 0x2FA = some (.load .lbu (18 : Fin 32) sp 0x240, 4) := by decide
theorem fs_at_2fe : fetchRel p384FromSec1Code 0x2FE = some (.aluImm .add a0 sp 0x364, 2) := by decide
theorem fs_at_300 : fetchRel p384FromSec1Code 0x300 = some (.aluImm .add a1 sp 0x2D4, 2) := by decide
theorem fs_at_302 : fetchRel p384FromSec1Code 0x302 = some (.aluImm .add a2 sp 0x210, 2) := by decide
theorem fs_at_304 : fetchRel p384FromSec1Code 0x304 = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem fs_at_306 : fetchRel p384FromSec1Code 0x306 = some (.auipc ra 0xE000, 4) := by decide
theorem fs_at_30a : fetchRel p384FromSec1Code 0x30A = some (.jalr ra ra 0x7D4, 4) := by decide
theorem fs_at_30e : fetchRel p384FromSec1Code 0x30E = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem fs_at_310 : fetchRel p384FromSec1Code 0x310 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem fs_at_312 : fetchRel p384FromSec1Code 0x312 = some (.auipc ra 0x1000, 4) := by decide
theorem fs_at_316 : fetchRel p384FromSec1Code 0x316 = some (.jalr ra ra 0xFFFFF926, 4) := by decide
theorem fs_at_31a : fetchRel p384FromSec1Code 0x31A = some (.aluImm .add a0 sp 0x304, 2) := by decide
theorem fs_at_31c : fetchRel p384FromSec1Code 0x31C = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem fs_at_320 : fetchRel p384FromSec1Code 0x320 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem fs_at_322 : fetchRel p384FromSec1Code 0x322 = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_326 : fetchRel p384FromSec1Code 0x326 = some (.jalr ra ra 0x76A, 4) := by decide
theorem fs_at_32a : fetchRel p384FromSec1Code 0x32A = some (.load .lbu (19 : Fin 32) sp 0x174, 4) := by decide
theorem fs_at_32e : fetchRel p384FromSec1Code 0x32E = some (.aluImm .add a0 sp 0x3C4, 2) := by decide
theorem fs_at_330 : fetchRel p384FromSec1Code 0x330 = some (.aluImm .add a1 sp 0x304, 2) := by decide
theorem fs_at_332 : fetchRel p384FromSec1Code 0x332 = some (.aluImm .add a2 sp 0x144, 2) := by decide
theorem fs_at_334 : fetchRel p384FromSec1Code 0x334 = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem fs_at_336 : fetchRel p384FromSec1Code 0x336 = some (.auipc ra 0xE000, 4) := by decide
theorem fs_at_33a : fetchRel p384FromSec1Code 0x33A = some (.jalr ra ra 0x7A4, 4) := by decide
theorem fs_at_33e : fetchRel p384FromSec1Code 0x33E = some (.aluImm .add a0 sp 0x334, 2) := by decide
theorem fs_at_340 : fetchRel p384FromSec1Code 0x340 = some (.aluImm .add a1 sp 0x364, 2) := by decide
theorem fs_at_342 : fetchRel p384FromSec1Code 0x342 = some (.aluImm .add a2 sp 0x364, 2) := by decide
theorem fs_at_344 : fetchRel p384FromSec1Code 0x344 = some (.auipc ra 0xE000, 4) := by decide
theorem fs_at_348 : fetchRel p384FromSec1Code 0x348 = some (.jalr ra ra 0x7DE, 4) := by decide
theorem fs_at_34c : fetchRel p384FromSec1Code 0x34C = some (.aluImm .add a0 sp 0xDC, 2) := by decide
theorem fs_at_34e : fetchRel p384FromSec1Code 0x34E = some (.aluImm .add a1 sp 0x3C4, 2) := by decide
theorem fs_at_350 : fetchRel p384FromSec1Code 0x350 = some (.aluImm .add a2 sp 0x3C4, 2) := by decide
theorem fs_at_352 : fetchRel p384FromSec1Code 0x352 = some (.auipc ra 0xE000, 4) := by decide
theorem fs_at_356 : fetchRel p384FromSec1Code 0x356 = some (.jalr ra ra 0x7D0, 4) := by decide
theorem fs_at_35a : fetchRel p384FromSec1Code 0x35A = some (.aluImm .add a0 sp 0x1AC, 2) := by decide
theorem fs_at_35c : fetchRel p384FromSec1Code 0x35C = some (.aluImm .add a1 sp 0xDC, 2) := by decide
theorem fs_at_35e : fetchRel p384FromSec1Code 0x35E = some (.aluImm .add a2 sp 0x3C4, 2) := by decide
theorem fs_at_360 : fetchRel p384FromSec1Code 0x360 = some (.auipc ra 0xE000, 4) := by decide
theorem fs_at_364 : fetchRel p384FromSec1Code 0x364 = some (.jalr ra ra 0x7C2, 4) := by decide
theorem fs_at_368 : fetchRel p384FromSec1Code 0x368 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem fs_at_36c : fetchRel p384FromSec1Code 0x36C = some (.aluImm .add a1 a1 0x204, 4) := by decide
theorem fs_at_370 : fetchRel p384FromSec1Code 0x370 = some (.aluImm .add a0 sp 0xDC, 2) := by decide
theorem fs_at_372 : fetchRel p384FromSec1Code 0x372 = some (.aluImm .add a2 sp 0x3C4, 2) := by decide
theorem fs_at_374 : fetchRel p384FromSec1Code 0x374 = some (.auipc ra 0xE000, 4) := by decide
theorem fs_at_378 : fetchRel p384FromSec1Code 0x378 = some (.jalr ra ra 0x7AE, 4) := by decide
theorem fs_at_37c : fetchRel p384FromSec1Code 0x37C = some (.aluImm .add a0 sp 0x394, 2) := by decide
theorem fs_at_37e : fetchRel p384FromSec1Code 0x37E = some (.aluImm .add a1 sp 0x1AC, 2) := by decide
theorem fs_at_380 : fetchRel p384FromSec1Code 0x380 = some (.aluImm .add a2 sp 0xDC, 2) := by decide
theorem fs_at_382 : fetchRel p384FromSec1Code 0x382 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem fs_at_386 : fetchRel p384FromSec1Code 0x386 = some (.jalr ra ra 0x58, 4) := by decide
theorem fs_at_38a : fetchRel p384FromSec1Code 0x38A = some (.lui a2 0x3FCC4000, 4) := by decide
theorem fs_at_38e : fetchRel p384FromSec1Code 0x38E = some (.aluImm .add a2 a2 0x234, 4) := by decide
theorem fs_at_392 : fetchRel p384FromSec1Code 0x392 = some (.aluImm .add a0 sp 0x1AC, 2) := by decide
theorem fs_at_394 : fetchRel p384FromSec1Code 0x394 = some (.aluImm .add a1 sp 0x394, 2) := by decide
theorem fs_at_396 : fetchRel p384FromSec1Code 0x396 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem fs_at_39a : fetchRel p384FromSec1Code 0x39A = some (.jalr ra ra 0x44, 4) := by decide
theorem fs_at_39e : fetchRel p384FromSec1Code 0x39E = some (.aluImm .add a0 sp 0xDC, 2) := by decide
theorem fs_at_3a0 : fetchRel p384FromSec1Code 0x3A0 = some (.aluImm .add a1 sp 0x3C4, 2) := by decide
theorem fs_at_3a2 : fetchRel p384FromSec1Code 0x3A2 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem fs_at_3a6 : fetchRel p384FromSec1Code 0x3A6 = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_3aa : fetchRel p384FromSec1Code 0x3AA = some (.jalr ra ra 0x74E, 4) := by decide
theorem fs_at_3ae : fetchRel p384FromSec1Code 0x3AE = some (.aluImm .add a0 sp 0x10C, 2) := by decide
theorem fs_at_3b0 : fetchRel p384FromSec1Code 0x3B0 = some (.aluImm .add a1 sp 0x364, 2) := by decide
theorem fs_at_3b2 : fetchRel p384FromSec1Code 0x3B2 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem fs_at_3b6 : fetchRel p384FromSec1Code 0x3B6 = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_3ba : fetchRel p384FromSec1Code 0x3BA = some (.jalr ra ra 0x73E, 4) := by decide
theorem fs_at_3be : fetchRel p384FromSec1Code 0x3BE = some (.aluImm .add a0 sp 0x334, 2) := by decide
theorem fs_at_3c0 : fetchRel p384FromSec1Code 0x3C0 = some (.aluImm .add a1 sp 0x1AC, 2) := by decide
theorem fs_at_3c2 : fetchRel p384FromSec1Code 0x3C2 = some (.auipc ra 0xE000, 4) := by decide
theorem fs_at_3c6 : fetchRel p384FromSec1Code 0x3C6 = some (.jalr ra ra 0x772, 4) := by decide
theorem fs_at_3ca : fetchRel p384FromSec1Code 0x3CA = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem fs_at_3ce : fetchRel p384FromSec1Code 0x3CE = some (.auipc ra 0x8000, 4) := by decide
theorem fs_at_3d2 : fetchRel p384FromSec1Code 0x3D2 = some (.jalr ra ra 0x61C, 4) := by decide
theorem fs_at_3d6 : fetchRel p384FromSec1Code 0x3D6 = some (.alu .and a0 (19 : Fin 32) a0, 4) := by decide
theorem fs_at_3da : fetchRel p384FromSec1Code 0x3DA = some (.auipc ra 0x8000, 4) := by decide
theorem fs_at_3de : fetchRel p384FromSec1Code 0x3DE = some (.jalr ra ra 0x610, 4) := by decide
theorem fs_at_3e2 : fetchRel p384FromSec1Code 0x3E2 = some (.alu .and a0 (18 : Fin 32) a0, 4) := by decide
theorem fs_at_3e6 : fetchRel p384FromSec1Code 0x3E6 = some (.auipc ra 0x8000, 4) := by decide
theorem fs_at_3ea : fetchRel p384FromSec1Code 0x3EA = some (.jalr ra ra 0x604, 4) := by decide
theorem fs_at_3ee : fetchRel p384FromSec1Code 0x3EE = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem fs_at_3f0 : fetchRel p384FromSec1Code 0x3F0 = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem fs_at_3f2 : fetchRel p384FromSec1Code 0x3F2 = some (.aluImm .add a1 sp 0xDC, 2) := by decide
theorem fs_at_3f4 : fetchRel p384FromSec1Code 0x3F4 = some (.aluImm .add a2 x0 0x60, 4) := by decide
theorem fs_at_3f8 : fetchRel p384FromSec1Code 0x3F8 = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_3fc : fetchRel p384FromSec1Code 0x3FC = some (.jalr ra ra 0x6FC, 4) := by decide
theorem fs_at_400 : fetchRel p384FromSec1Code 0x400 = some (.store .sb sp x0 0x1A4, 4) := by decide
theorem fs_at_404 : fetchRel p384FromSec1Code 0x404 = some (.store .sb sp (9 : Fin 32) 0x1A8, 4) := by decide
theorem fs_at_408 : fetchRel p384FromSec1Code 0x408 = some (.aluImm .add a0 sp 0x74, 2) := by decide
theorem fs_at_40a : fetchRel p384FromSec1Code 0x40A = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem fs_at_40c : fetchRel p384FromSec1Code 0x40C = some (.auipc ra 0x0, 4) := by decide
theorem fs_at_410 : fetchRel p384FromSec1Code 0x410 = some (.jalr ra ra 0xD0, 4) := by decide
theorem fs_at_414 : fetchRel p384FromSec1Code 0x414 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem fs_at_416 : fetchRel p384FromSec1Code 0x416 = some (.auipc ra 0x0, 4) := by decide
theorem fs_at_41a : fetchRel p384FromSec1Code 0x41A = some (.jalr ra ra 0x6E, 4) := by decide
theorem fs_at_41e : fetchRel p384FromSec1Code 0x41E = some (.load .lbu a1 sp 0xD8, 4) := by decide
theorem fs_at_422 : fetchRel p384FromSec1Code 0x422 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem fs_at_424 : fetchRel p384FromSec1Code 0x424 = some (.alu .and a0 a0 a1, 2) := by decide
theorem fs_at_426 : fetchRel p384FromSec1Code 0x426 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem fs_at_428 : fetchRel p384FromSec1Code 0x428 = some (.store .sb sp a0 0x144, 4) := by decide
theorem fs_at_42c : fetchRel p384FromSec1Code 0x42C = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem fs_at_42e : fetchRel p384FromSec1Code 0x42E = some (.load .lbu a0 sp 0x144, 4) := by decide
theorem fs_at_432 : fetchRel p384FromSec1Code 0x432 = some (.branch .beq a0 x0 0x18, 2) := by decide
theorem fs_at_434 : fetchRel p384FromSec1Code 0x434 = some (.aluImm .add a0 (24 : Fin 32) 0x4, 4) := by decide
theorem fs_at_438 : fetchRel p384FromSec1Code 0x438 = some (.aluImm .add a1 sp 0x74, 2) := by decide
theorem fs_at_43a : fetchRel p384FromSec1Code 0x43A = some (.aluImm .add a2 x0 0x64, 4) := by decide
theorem fs_at_43e : fetchRel p384FromSec1Code 0x43E = some (.auipc ra 0xF000, 4) := by decide
theorem fs_at_442 : fetchRel p384FromSec1Code 0x442 = some (.jalr ra ra 0x6B6, 4) := by decide
theorem fs_at_446 : fetchRel p384FromSec1Code 0x446 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem fs_at_448 : fetchRel p384FromSec1Code 0x448 = some (.jal x0 0x4, 2) := by decide
theorem fs_at_44a : fetchRel p384FromSec1Code 0x44A = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem fs_at_44c : fetchRel p384FromSec1Code 0x44C = some (.store .sw (24 : Fin 32) a0 0x0, 4) := by decide
theorem fs_at_450 : fetchRel p384FromSec1Code 0x450 = some (.aluImm .add a0 sp 0x400, 4) := by decide
theorem fs_at_454 : fetchRel p384FromSec1Code 0x454 = some (.load .lw ra a0 0x1C, 4) := by decide
theorem fs_at_458 : fetchRel p384FromSec1Code 0x458 = some (.load .lw (8 : Fin 32) a0 0x18, 2) := by decide
theorem fs_at_45a : fetchRel p384FromSec1Code 0x45A = some (.load .lw (9 : Fin 32) a0 0x14, 2) := by decide
theorem fs_at_45c : fetchRel p384FromSec1Code 0x45C = some (.load .lw (18 : Fin 32) a0 0x10, 4) := by decide
theorem fs_at_460 : fetchRel p384FromSec1Code 0x460 = some (.load .lw (19 : Fin 32) a0 0xC, 4) := by decide
theorem fs_at_464 : fetchRel p384FromSec1Code 0x464 = some (.load .lw (20 : Fin 32) a0 0x8, 4) := by decide
theorem fs_at_468 : fetchRel p384FromSec1Code 0x468 = some (.load .lw (21 : Fin 32) a0 0x4, 4) := by decide
theorem fs_at_46c : fetchRel p384FromSec1Code 0x46C = some (.load .lw (22 : Fin 32) a0 0x0, 4) := by decide
theorem fs_at_470 : fetchRel p384FromSec1Code 0x470 = some (.aluImm .add a0 sp 0x380, 2) := by decide
theorem fs_at_472 : fetchRel p384FromSec1Code 0x472 = some (.load .lw (23 : Fin 32) a0 0x7C, 4) := by decide
theorem fs_at_476 : fetchRel p384FromSec1Code 0x476 = some (.load .lw (24 : Fin 32) a0 0x78, 4) := by decide
theorem fs_at_47a : fetchRel p384FromSec1Code 0x47A = some (.load .lw (25 : Fin 32) a0 0x74, 4) := by decide
theorem fs_at_47e : fetchRel p384FromSec1Code 0x47E = some (.aluImm .add sp sp 0x420, 4) := by decide
theorem fs_at_482 : fetchRel p384FromSec1Code 0x482 = some (.jalr x0 ra 0x0, 2) := by decide

end C3.RV32.Fs
