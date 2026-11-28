import C3BootProofs.Proofs.TimeDigits
import C3BootProofs.Proofs.Parse
import C3BootProofs.Proofs.Fe25519
import C3BootProofs.Spec.Time

/-!
# `time::date_time`, as compiled

`c3_verify::time::date_time` reads `MMDDHHMMSS` with five calls to
`digits::<2>`, checks the fields, and returns the seconds since the epoch
as a `u64` computed in two 32-bit halves. `dateTime_correct` matches it to
`readDateTime`.
-/

namespace C3.RV32

open C3.Image

abbrev DT : Word := BitVec.ofNat 32 dateTimeAddress
abbrev TD : Word := BitVec.ofNat 32 timeDigits2Address

section
set_option maxRecDepth 20000
theorem dtm_at_0 : fetchRel dateTimeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem dtm_at_2 : fetchRel dateTimeCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem dtm_at_4 : fetchRel dateTimeCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem dtm_at_6 : fetchRel dateTimeCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem dtm_at_8 : fetchRel dateTimeCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem dtm_at_a : fetchRel dateTimeCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem dtm_at_c : fetchRel dateTimeCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem dtm_at_e : fetchRel dateTimeCode 0xE = some (.store .sw sp (21 : Fin 32) 0x14, 2) := by decide
theorem dtm_at_10 : fetchRel dateTimeCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x10, 2) := by decide
theorem dtm_at_12 : fetchRel dateTimeCode 0x12 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem dtm_at_14 : fetchRel dateTimeCode 0x14 = some (.alu .add (18 : Fin 32) x0 a1, 2) := by decide
theorem dtm_at_16 : fetchRel dateTimeCode 0x16 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dtm_at_18 : fetchRel dateTimeCode 0x18 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem dtm_at_1a : fetchRel dateTimeCode 0x1A = some (.alu .add a1 x0 a2, 2) := by decide
theorem dtm_at_1c : fetchRel dateTimeCode 0x1C = some (.auipc ra 0x0, 4) := by decide
theorem dtm_at_20 : fetchRel dateTimeCode 0x20 = some (.jalr ra ra 0x200, 4) := by decide
theorem dtm_at_24 : fetchRel dateTimeCode 0x24 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dtm_at_28 : fetchRel dateTimeCode 0x28 = some (.branch .bne a0 x0 0x52, 2) := by decide
theorem dtm_at_2a : fetchRel dateTimeCode 0x2A = some (.load .lw (22 : Fin 32) sp 0xC, 2) := by decide
theorem dtm_at_2c : fetchRel dateTimeCode 0x2C = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem dtm_at_2e : fetchRel dateTimeCode 0x2E = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem dtm_at_30 : fetchRel dateTimeCode 0x30 = some (.auipc ra 0x0, 4) := by decide
theorem dtm_at_34 : fetchRel dateTimeCode 0x34 = some (.jalr ra ra 0x1EC, 4) := by decide
theorem dtm_at_38 : fetchRel dateTimeCode 0x38 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dtm_at_3c : fetchRel dateTimeCode 0x3C = some (.branch .bne a0 x0 0x3E, 2) := by decide
theorem dtm_at_3e : fetchRel dateTimeCode 0x3E = some (.load .lw (20 : Fin 32) sp 0xC, 2) := by decide
theorem dtm_at_40 : fetchRel dateTimeCode 0x40 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem dtm_at_42 : fetchRel dateTimeCode 0x42 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem dtm_at_44 : fetchRel dateTimeCode 0x44 = some (.auipc ra 0x0, 4) := by decide
theorem dtm_at_48 : fetchRel dateTimeCode 0x48 = some (.jalr ra ra 0x1D8, 4) := by decide
theorem dtm_at_4c : fetchRel dateTimeCode 0x4C = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dtm_at_50 : fetchRel dateTimeCode 0x50 = some (.branch .bne a0 x0 0x2A, 2) := by decide
theorem dtm_at_52 : fetchRel dateTimeCode 0x52 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem dtm_at_54 : fetchRel dateTimeCode 0x54 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem dtm_at_56 : fetchRel dateTimeCode 0x56 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem dtm_at_58 : fetchRel dateTimeCode 0x58 = some (.auipc ra 0x0, 4) := by decide
theorem dtm_at_5c : fetchRel dateTimeCode 0x5C = some (.jalr ra ra 0x1C4, 4) := by decide
theorem dtm_at_60 : fetchRel dateTimeCode 0x60 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dtm_at_64 : fetchRel dateTimeCode 0x64 = some (.branch .bne a0 x0 0x16, 2) := by decide
theorem dtm_at_66 : fetchRel dateTimeCode 0x66 = some (.load .lw (21 : Fin 32) sp 0xC, 2) := by decide
theorem dtm_at_68 : fetchRel dateTimeCode 0x68 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem dtm_at_6a : fetchRel dateTimeCode 0x6A = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem dtm_at_6c : fetchRel dateTimeCode 0x6C = some (.auipc ra 0x0, 4) := by decide
theorem dtm_at_70 : fetchRel dateTimeCode 0x70 = some (.jalr ra ra 0x1B0, 4) := by decide
theorem dtm_at_74 : fetchRel dateTimeCode 0x74 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dtm_at_78 : fetchRel dateTimeCode 0x78 = some (.branch .beq a0 x0 0x24, 2) := by decide
theorem dtm_at_7a : fetchRel dateTimeCode 0x7A = some (.load .lbu a0 sp 0x9, 4) := by decide
theorem dtm_at_7e : fetchRel dateTimeCode 0x7E = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem dtm_at_82 : fetchRel dateTimeCode 0x82 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem dtm_at_84 : fetchRel dateTimeCode 0x84 = some (.store .sb (8 : Fin 32) a1 0x0, 4) := by decide
theorem dtm_at_88 : fetchRel dateTimeCode 0x88 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem dtm_at_8a : fetchRel dateTimeCode 0x8A = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem dtm_at_8c : fetchRel dateTimeCode 0x8C = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem dtm_at_8e : fetchRel dateTimeCode 0x8E = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem dtm_at_90 : fetchRel dateTimeCode 0x90 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem dtm_at_92 : fetchRel dateTimeCode 0x92 = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem dtm_at_94 : fetchRel dateTimeCode 0x94 = some (.load .lw (21 : Fin 32) sp 0x14, 2) := by decide
theorem dtm_at_96 : fetchRel dateTimeCode 0x96 = some (.load .lw (22 : Fin 32) sp 0x10, 2) := by decide
theorem dtm_at_98 : fetchRel dateTimeCode 0x98 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem dtm_at_9a : fetchRel dateTimeCode 0x9A = some (.jalr x0 ra 0x0, 2) := by decide
theorem dtm_at_9c : fetchRel dateTimeCode 0x9C = some (.aluImm .add a0 x0 0x7B2, 4) := by decide
theorem dtm_at_a0 : fetchRel dateTimeCode 0xA0 = some (.branch .bltu (18 : Fin 32) a0 0x98, 4) := by decide
theorem dtm_at_a4 : fetchRel dateTimeCode 0xA4 = some (.aluImm .add a0 (22 : Fin 32) 0xFFFFFFFF, 4) := by decide
theorem dtm_at_a8 : fetchRel dateTimeCode 0xA8 = some (.aluImm .add a1 x0 0xB, 2) := by decide
theorem dtm_at_aa : fetchRel dateTimeCode 0xAA = some (.branch .bltu a1 a0 0x8E, 4) := by decide
theorem dtm_at_ae : fetchRel dateTimeCode 0xAE = some (.branch .beq (20 : Fin 32) x0 0x8A, 4) := by decide
theorem dtm_at_b2 : fetchRel dateTimeCode 0xB2 = some (.load .lw a0 sp 0xC, 2) := by decide
theorem dtm_at_b4 : fetchRel dateTimeCode 0xB4 = some (.aluImm .add a1 x0 0x1F, 2) := by decide
theorem dtm_at_b6 : fetchRel dateTimeCode 0xB6 = some (.lui a2 0x1000, 2) := by decide
theorem dtm_at_b8 : fetchRel dateTimeCode 0xB8 = some (.aluImm .add a3 a2 0x5AA, 4) := by decide
theorem dtm_at_bc : fetchRel dateTimeCode 0xBC = some (.alu .srl a3 a3 (22 : Fin 32), 4) := by decide
theorem dtm_at_c0 : fetchRel dateTimeCode 0xC0 = some (.aluImm .and a3 a3 0x1, 2) := by decide
theorem dtm_at_c2 : fetchRel dateTimeCode 0xC2 = some (.branch .bne a3 x0 0x12, 2) := by decide
theorem dtm_at_c4 : fetchRel dateTimeCode 0xC4 = some (.aluImm .add a1 a2 0xFFFFFA50, 4) := by decide
theorem dtm_at_c8 : fetchRel dateTimeCode 0xC8 = some (.alu .srl a1 a1 (22 : Fin 32), 4) := by decide
theorem dtm_at_cc : fetchRel dateTimeCode 0xCC = some (.aluImm .and a1 a1 0x1, 2) := by decide
theorem dtm_at_ce : fetchRel dateTimeCode 0xCE = some (.branch .beq a1 x0 0x126, 4) := by decide
theorem dtm_at_d2 : fetchRel dateTimeCode 0xD2 = some (.aluImm .add a1 x0 0x1E, 2) := by decide
theorem dtm_at_d4 : fetchRel dateTimeCode 0xD4 = some (.aluImm .add a2 x0 0x3B, 4) := by decide
theorem dtm_at_d8 : fetchRel dateTimeCode 0xD8 = some (.branch .bltu a2 a0 0x60, 4) := by decide
theorem dtm_at_dc : fetchRel dateTimeCode 0xDC = some (.branch .bltu a2 (21 : Fin 32) 0x5C, 4) := by decide
theorem dtm_at_e0 : fetchRel dateTimeCode 0xE0 = some (.aluImm .add a2 x0 0x17, 2) := by decide
theorem dtm_at_e2 : fetchRel dateTimeCode 0xE2 = some (.branch .bltu a2 (19 : Fin 32) 0x56, 4) := by decide
theorem dtm_at_e6 : fetchRel dateTimeCode 0xE6 = some (.branch .bltu a1 (20 : Fin 32) 0x52, 4) := by decide
theorem dtm_at_ea : fetchRel dateTimeCode 0xEA = some (.aluImm .sltu a1 (22 : Fin 32) 0x3, 4) := by decide
theorem dtm_at_ee : fetchRel dateTimeCode 0xEE = some (.aluImm .add a2 x0 0x190, 4) := by decide
theorem dtm_at_f2 : fetchRel dateTimeCode 0xF2 = some (.alu .sub a3 (18 : Fin 32) a1, 4) := by decide
theorem dtm_at_f6 : fetchRel dateTimeCode 0xF6 = some (.alu .divu a1 a3 a2, 4) := by decide
theorem dtm_at_fa : fetchRel dateTimeCode 0xFA = some (.alu .mul a2 a1 a2, 4) := by decide
theorem dtm_at_fe : fetchRel dateTimeCode 0xFE = some (.alu .sub a3 a3 a2, 2) := by decide
theorem dtm_at_100 : fetchRel dateTimeCode 0x100 = some (.aluImm .sll a2 a3 0x10, 4) := by decide
theorem dtm_at_104 : fetchRel dateTimeCode 0x104 = some (.aluImm .add a4 x0 0x64, 4) := by decide
theorem dtm_at_108 : fetchRel dateTimeCode 0x108 = some (.aluImm .srl a2 a2 0x10, 2) := by decide
theorem dtm_at_10a : fetchRel dateTimeCode 0x10A = some (.alu .divu a4 a2 a4, 4) := by decide
theorem dtm_at_10e : fetchRel dateTimeCode 0x10E = some (.aluImm .add a5 x0 0x16D, 4) := by decide
theorem dtm_at_112 : fetchRel dateTimeCode 0x112 = some (.alu .mul a3 a3 a5, 4) := by decide
theorem dtm_at_116 : fetchRel dateTimeCode 0x116 = some (.aluImm .srl a2 a2 0x2, 2) := by decide
theorem dtm_at_118 : fetchRel dateTimeCode 0x118 = some (.alu .add a3 a3 a2, 2) := by decide
theorem dtm_at_11a : fetchRel dateTimeCode 0x11A = some (.alu .sltu a2 a3 a2, 4) := by decide
theorem dtm_at_11e : fetchRel dateTimeCode 0x11E = some (.alu .sltu a5 a3 a4, 4) := by decide
theorem dtm_at_122 : fetchRel dateTimeCode 0x122 = some (.aluImm .xor (9 : Fin 32) a2 0xFFFFFFFF, 4) := by decide
theorem dtm_at_126 : fetchRel dateTimeCode 0x126 = some (.alu .and a5 a5 (9 : Fin 32), 2) := by decide
theorem dtm_at_128 : fetchRel dateTimeCode 0x128 = some (.branch .bne a5 x0 0x7C, 2) := by decide
theorem dtm_at_12a : fetchRel dateTimeCode 0x12A = some (.aluImm .add a5 x0 0x3, 2) := by decide
theorem dtm_at_12c : fetchRel dateTimeCode 0x12C = some (.aluImm .xor a6 a4 0xFFFFFFFF, 4) := by decide
theorem dtm_at_130 : fetchRel dateTimeCode 0x130 = some (.branch .bltu (22 : Fin 32) a5 0xC, 4) := by decide
theorem dtm_at_134 : fetchRel dateTimeCode 0x134 = some (.aluImm .add a5 x0 0xFFFFFFFD, 2) := by decide
theorem dtm_at_136 : fetchRel dateTimeCode 0x136 = some (.jal x0 0x8, 2) := by decide
theorem dtm_at_138 : fetchRel dateTimeCode 0x138 = some (.aluImm .add a0 x0 0x19, 2) := by decide
theorem dtm_at_13a : fetchRel dateTimeCode 0x13A = some (.jal x0 0xFFFFFF44, 2) := by decide
theorem dtm_at_13c : fetchRel dateTimeCode 0x13C = some (.aluImm .add a5 x0 0x9, 2) := by decide
theorem dtm_at_13e : fetchRel dateTimeCode 0x13E = some (.alu .add a5 a5 (22 : Fin 32), 2) := by decide
theorem dtm_at_140 : fetchRel dateTimeCode 0x140 = some (.aluImm .add (9 : Fin 32) x0 0x99, 4) := by decide
theorem dtm_at_144 : fetchRel dateTimeCode 0x144 = some (.alu .mul a5 a5 (9 : Fin 32), 4) := by decide
theorem dtm_at_148 : fetchRel dateTimeCode 0x148 = some (.aluImm .add a5 a5 0x2, 2) := by decide
theorem dtm_at_14a : fetchRel dateTimeCode 0x14A = some (.aluImm .sll a5 a5 0x10, 2) := by decide
theorem dtm_at_14c : fetchRel dateTimeCode 0x14C = some (.aluImm .add (9 : Fin 32) x0 0x5, 2) := by decide
theorem dtm_at_14e : fetchRel dateTimeCode 0x14E = some (.aluImm .srl a5 a5 0x10, 2) := by decide
theorem dtm_at_150 : fetchRel dateTimeCode 0x150 = some (.alu .divu a5 a5 (9 : Fin 32), 4) := by decide
theorem dtm_at_154 : fetchRel dateTimeCode 0x154 = some (.lui (9 : Fin 32) 0x24000, 4) := by decide
theorem dtm_at_158 : fetchRel dateTimeCode 0x158 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFAB1, 4) := by decide
theorem dtm_at_15c : fetchRel dateTimeCode 0x15C = some (.alu .mul a4 a1 (9 : Fin 32), 4) := by decide
theorem dtm_at_160 : fetchRel dateTimeCode 0x160 = some (.alu .mulhu a1 a1 (9 : Fin 32), 4) := by decide
theorem dtm_at_164 : fetchRel dateTimeCode 0x164 = some (.lui (9 : Fin 32) 0xFFFF0000, 2) := by decide
theorem dtm_at_166 : fetchRel dateTimeCode 0x166 = some (.alu .or (9 : Fin 32) a6 (9 : Fin 32), 4) := by decide
theorem dtm_at_16a : fetchRel dateTimeCode 0x16A = some (.alu .add a5 a5 a4, 2) := by decide
theorem dtm_at_16c : fetchRel dateTimeCode 0x16C = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem dtm_at_170 : fetchRel dateTimeCode 0x170 = some (.alu .add a5 a5 (9 : Fin 32), 2) := by decide
theorem dtm_at_172 : fetchRel dateTimeCode 0x172 = some (.alu .add a1 a1 a4, 2) := by decide
theorem dtm_at_174 : fetchRel dateTimeCode 0x174 = some (.alu .sltu a4 a5 (9 : Fin 32), 4) := by decide
theorem dtm_at_178 : fetchRel dateTimeCode 0x178 = some (.alu .add a1 a1 a4, 2) := by decide
theorem dtm_at_17a : fetchRel dateTimeCode 0x17A = some (.alu .add a3 a3 a5, 2) := by decide
theorem dtm_at_17c : fetchRel dateTimeCode 0x17C = some (.alu .add a1 a1 a2, 2) := by decide
theorem dtm_at_17e : fetchRel dateTimeCode 0x17E = some (.alu .sltu a2 a3 a5, 4) := by decide
theorem dtm_at_182 : fetchRel dateTimeCode 0x182 = some (.alu .add (20 : Fin 32) (20 : Fin 32) a3, 2) := by decide
theorem dtm_at_184 : fetchRel dateTimeCode 0x184 = some (.alu .add a1 a1 a2, 2) := by decide
theorem dtm_at_186 : fetchRel dateTimeCode 0x186 = some (.alu .sltu a2 (20 : Fin 32) a3, 4) := by decide
theorem dtm_at_18a : fetchRel dateTimeCode 0x18A = some (.alu .add a1 a1 a2, 2) := by decide
theorem dtm_at_18c : fetchRel dateTimeCode 0x18C = some (.lui a3 0xB0000, 4) := by decide
theorem dtm_at_190 : fetchRel dateTimeCode 0x190 = some (.aluImm .add a2 a1 0xFFFFFFFF, 4) := by decide
theorem dtm_at_194 : fetchRel dateTimeCode 0x194 = some (.aluImm .add a1 a3 0xFFFFFA6B, 4) := by decide
theorem dtm_at_198 : fetchRel dateTimeCode 0x198 = some (.alu .sltu a3 x0 a2, 4) := by decide
theorem dtm_at_19c : fetchRel dateTimeCode 0x19C = some (.alu .sltu a1 a1 (20 : Fin 32), 4) := by decide
theorem dtm_at_1a0 : fetchRel dateTimeCode 0x1A0 = some (.alu .or a1 a1 a3, 2) := by decide
theorem dtm_at_1a2 : fetchRel dateTimeCode 0x1A2 = some (.branch .bne a1 x0 0x6, 2) := by decide
theorem dtm_at_1a4 : fetchRel dateTimeCode 0x1A4 = some (.aluImm .add a0 x0 0x6, 2) := by decide
theorem dtm_at_1a6 : fetchRel dateTimeCode 0x1A6 = some (.jal x0 0xFFFFFED8, 2) := by decide
theorem dtm_at_1a8 : fetchRel dateTimeCode 0x1A8 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dtm_at_1aa : fetchRel dateTimeCode 0x1AA = some (.aluImm .add a3 x0 0x3C, 4) := by decide
theorem dtm_at_1ae : fetchRel dateTimeCode 0x1AE = some (.lui a4 0x1000, 2) := by decide
theorem dtm_at_1b0 : fetchRel dateTimeCode 0x1B0 = some (.alu .mul a3 (21 : Fin 32) a3, 4) := by decide
theorem dtm_at_1b4 : fetchRel dateTimeCode 0x1B4 = some (.aluImm .add a4 a4 0xFFFFFE10, 4) := by decide
theorem dtm_at_1b8 : fetchRel dateTimeCode 0x1B8 = some (.lui a5 0x15000, 2) := by decide
theorem dtm_at_1ba : fetchRel dateTimeCode 0x1BA = some (.alu .mul a4 (19 : Fin 32) a4, 4) := by decide
theorem dtm_at_1be : fetchRel dateTimeCode 0x1BE = some (.aluImm .add a5 a5 0x180, 4) := by decide
theorem dtm_at_1c2 : fetchRel dateTimeCode 0x1C2 = some (.alu .mul a2 a2 a5, 4) := by decide
theorem dtm_at_1c6 : fetchRel dateTimeCode 0x1C6 = some (.alu .mulhu (9 : Fin 32) (20 : Fin 32) a5, 4) := by decide
theorem dtm_at_1ca : fetchRel dateTimeCode 0x1CA = some (.alu .mul a5 (20 : Fin 32) a5, 4) := by decide
theorem dtm_at_1ce : fetchRel dateTimeCode 0x1CE = some (.alu .add a0 a0 a3, 2) := by decide
theorem dtm_at_1d0 : fetchRel dateTimeCode 0x1D0 = some (.alu .add a0 a0 a4, 2) := by decide
theorem dtm_at_1d2 : fetchRel dateTimeCode 0x1D2 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem dtm_at_1d4 : fetchRel dateTimeCode 0x1D4 = some (.lui a3 0x86DAA000, 4) := by decide
theorem dtm_at_1d8 : fetchRel dateTimeCode 0x1D8 = some (.alu .add a0 a0 a5, 2) := by decide
theorem dtm_at_1da : fetchRel dateTimeCode 0x1DA = some (.aluImm .add a3 a3 0xFFFFFE00, 4) := by decide
theorem dtm_at_1de : fetchRel dateTimeCode 0x1DE = some (.alu .sltu a4 a0 a5, 4) := by decide
theorem dtm_at_1e2 : fetchRel dateTimeCode 0x1E2 = some (.alu .add a3 a3 a0, 2) := by decide
theorem dtm_at_1e4 : fetchRel dateTimeCode 0x1E4 = some (.alu .add a2 a2 a4, 2) := by decide
theorem dtm_at_1e6 : fetchRel dateTimeCode 0x1E6 = some (.alu .sltu a0 a3 a0, 4) := by decide
theorem dtm_at_1ea : fetchRel dateTimeCode 0x1EA = some (.alu .add a0 a0 a2, 2) := by decide
theorem dtm_at_1ec : fetchRel dateTimeCode 0x1EC = some (.aluImm .add a0 a0 0xFFFFFFF1, 2) := by decide
theorem dtm_at_1ee : fetchRel dateTimeCode 0x1EE = some (.store .sw (8 : Fin 32) a3 0x8, 2) := by decide
theorem dtm_at_1f0 : fetchRel dateTimeCode 0x1F0 = some (.store .sw (8 : Fin 32) a0 0xC, 2) := by decide
theorem dtm_at_1f2 : fetchRel dateTimeCode 0x1F2 = some (.jal x0 0xFFFFFE92, 2) := by decide
theorem dtm_at_1f4 : fetchRel dateTimeCode 0x1F4 = some (.aluImm .and a1 (18 : Fin 32) 0x3, 4) := by decide
theorem dtm_at_1f8 : fetchRel dateTimeCode 0x1F8 = some (.branch .beq a1 x0 0x6, 2) := by decide
theorem dtm_at_1fa : fetchRel dateTimeCode 0x1FA = some (.aluImm .add a1 x0 0x1C, 2) := by decide
theorem dtm_at_1fc : fetchRel dateTimeCode 0x1FC = some (.jal x0 0xFFFFFED8, 2) := by decide
theorem dtm_at_1fe : fetchRel dateTimeCode 0x1FE = some (.aluImm .add a1 x0 0x64, 4) := by decide
theorem dtm_at_202 : fetchRel dateTimeCode 0x202 = some (.alu .remu a1 (18 : Fin 32) a1, 4) := by decide
theorem dtm_at_206 : fetchRel dateTimeCode 0x206 = some (.aluImm .add a2 x0 0x190, 4) := by decide
theorem dtm_at_20a : fetchRel dateTimeCode 0x20A = some (.alu .remu a2 (18 : Fin 32) a2, 4) := by decide
theorem dtm_at_20e : fetchRel dateTimeCode 0x20E = some (.alu .sltu a1 x0 a1, 4) := by decide
theorem dtm_at_212 : fetchRel dateTimeCode 0x212 = some (.aluImm .sltu a2 a2 0x1, 4) := by decide
theorem dtm_at_216 : fetchRel dateTimeCode 0x216 = some (.alu .or a1 a1 a2, 2) := by decide
theorem dtm_at_218 : fetchRel dateTimeCode 0x218 = some (.aluImm .add a1 a1 0x1C, 2) := by decide
theorem dtm_at_21a : fetchRel dateTimeCode 0x21A = some (.jal x0 0xFFFFFEBA, 2) := by decide
end

theorem readDigits2_mem (M : Word → BitVec 8) (p : Word) (n : Nat) :
    readDigits 2 (memBytes M p n) =
      if n < 2 then none else (digits2Of (M p) (M (p + 1))).map fun v => (v, memBytes M (p + 2) (n - 2)) := by
  rcases n with _ | _ | n
  · rfl
  · rw [memBytes_succ, memBytes_zero]
    simp only [readDigits, require, bind, Option.bind]
    split <;> rfl
  · rw [memBytes_succ, memBytes_succ, show p + 1 + 1 = p + 2 by rw [BitVec.add_assoc]; rfl,
      if_neg (by omega), show n + 1 + 1 - 2 = n by omega]
    unfold digits2Of isDigit
    obtain ⟨x, hx⟩ : ∃ x, (M p).toNat = x := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, (M (p + 1)).toNat = y := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, memBytes M (p + 2) n = r := ⟨_, rfl⟩
    rw [hx, hy, hr]
    simp only [readDigits, require, bind, Option.bind, pure]
    by_cases h0 : 48 ≤ x ∧ x ≤ 57 <;> by_cases h1 : 48 ≤ y ∧ y ≤ 57 <;> simp [h0, h1]

theorem dn_add (a b : Word) : (aluEval .add a b).toNat = (a.toNat + b.toNat) % 2 ^ 32 := BitVec.toNat_add a b
theorem dn_sub (a b : Word) : (aluEval .sub a b).toNat = (2 ^ 32 - b.toNat + a.toNat) % 2 ^ 32 :=
  BitVec.toNat_sub a b
theorem dn_mul (a b : Word) : (aluEval .mul a b).toNat = a.toNat * b.toNat % 2 ^ 32 := BitVec.toNat_mul a b
theorem dn_mulhu (a b : Word) : (aluEval .mulhu a b).toNat = a.toNat * b.toNat / 2 ^ 32 := by
  show (BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have ha := a.isLt; have hb := b.isLt
  have hp : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega
theorem dn_divu (a b : Word) (hb : b.toNat ≠ 0) : (aluEval .divu a b).toNat = a.toNat / b.toNat := by
  show (if b = 0 then _ else _ : Word).toNat = _
  rw [if_neg (fun h => hb (by rw [h]; rfl)), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)]
theorem dn_remu (a b : Word) (hb : b.toNat ≠ 0) : (aluEval .remu a b).toNat = a.toNat % b.toNat := by
  show (if b = 0 then _ else _ : Word).toNat = _
  rw [if_neg (fun h => hb (by rw [h]; rfl)), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt)]
theorem dn_sltu (a b : Word) : (aluEval .sltu a b).toNat = if a.toNat < b.toNat then 1 else 0 := by
  show (if a.ult b then (1 : Word) else 0).toNat = _
  by_cases h : a.toNat < b.toNat
  · rw [if_pos (by simp [BitVec.ult, h]), if_pos h]; rfl
  · rw [if_neg (by simp [BitVec.ult, h]), if_neg h]; rfl
theorem dn_srl (a b : Word) : (aluEval .srl a b).toNat = a.toNat / 2 ^ (b.toNat % 32) := by
  show (a >>> (b.toNat % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
theorem dn_sll (a b : Word) : (aluEval .sll a b).toNat = a.toNat * 2 ^ (b.toNat % 32) % 2 ^ 32 := by
  show (a <<< (b.toNat % 32)).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
theorem dn_ofNat (k : Nat) (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem dn_z (x : Word) : aluEval .add 0 x = x := BitVec.zero_add x
theorem dn_z' (x : Word) : aluEval .add (BitVec.ofNat 32 0) x = x := BitVec.zero_add x
theorem dn_divuL (a : Word) (k : Nat) (hk : 0 < k) (hk2 : k < 2 ^ 32) :
    (aluEval .divu a (BitVec.ofNat 32 k)).toNat = a.toNat / k := by
  rw [dn_divu _ _ (by rw [dn_ofNat _ hk2]; omega), dn_ofNat _ hk2]
theorem dn_remuL (a : Word) (k : Nat) (hk : 0 < k) (hk2 : k < 2 ^ 32) :
    (aluEval .remu a (BitVec.ofNat 32 k)).toNat = a.toNat % k := by
  rw [dn_remu _ _ (by rw [dn_ofNat _ hk2]; omega), dn_ofNat _ hk2]

/-- `days_from_civil` as the code computes it: the day count plus 719468,
the days from 0000-03-01 to the epoch. -/
theorem dt_days (Y M D : Nat) (hY : 1970 ≤ Y) (hM1 : 1 ≤ M) (hM2 : M ≤ 12) (hD : 1 ≤ D) :
    let y := Y - (if M < 3 then 1 else 0)
    let yoe := y % 400
    daysFromCivil Y M D + 719468 =
      y / 400 * 146097 + (yoe * 365 + yoe / 4 - yoe / 100) + ((153 * (if M < 3 then M + 9 else M - 3) + 2) / 5 + D - 1) := by
  intro y yoe
  unfold daysFromCivil
  by_cases h : M < 3
  · simp only [y, yoe, if_pos h, if_pos (show M ≤ 2 by omega), if_neg (show ¬ M > 2 by omega)]
    have h5 : 306 ≤ (153 * (M + 9) + 2) / 5 := by omega
    by_cases hy : Y - 1 < 2000
    · have h4 : (Y - 1) / 400 = 4 := by omega
      rw [h4]
      by_cases h69 : Y - 1 = 1969
      · rw [h69]; omega
      · omega
    · omega
  · simp only [y, yoe, if_neg h, if_neg (show ¬ M ≤ 2 by omega), if_pos (show M > 2 by omega)]
    by_cases hy : Y < 2000
    · have h4 : Y / 400 = 4 := by omega
      rw [h4]; omega
    · omega

def dtC1 : List BInstr :=
  [.aluImm .sltu a1 (22 : Fin 32) 0x3, .aluImm .add a2 x0 0x190, .alu .sub a3 (18 : Fin 32) a1, .alu .divu a1 a3 a2, .alu .mul a2 a1 a2, .alu .sub a3 a3 a2]
def dtC2 : List BInstr :=
  [.aluImm .sll a2 a3 0x10, .aluImm .add a4 x0 0x64, .aluImm .srl a2 a2 0x10, .alu .divu a4 a2 a4, .aluImm .add a5 x0 0x16D, .alu .mul a3 a3 a5, .aluImm .srl a2 a2 0x2]
def dtC3 : List BInstr :=
  [.alu .add a3 a3 a2, .alu .sltu a2 a3 a2, .alu .sltu a5 a3 a4, .aluImm .xor (9 : Fin 32) a2 0xFFFFFFFF, .alu .and a5 a5 (9 : Fin 32)]
def dtC4 : List BInstr :=
  [.aluImm .add a5 x0 0x3, .aluImm .xor a6 a4 0xFFFFFFFF]
def dtC5 : List BInstr :=
  [.alu .add a5 a5 (22 : Fin 32), .aluImm .add (9 : Fin 32) x0 0x99, .alu .mul a5 a5 (9 : Fin 32), .aluImm .add a5 a5 0x2, .aluImm .sll a5 a5 0x10, .aluImm .add (9 : Fin 32) x0 0x5, .aluImm .srl a5 a5 0x10, .alu .divu a5 a5 (9 : Fin 32), .lui (9 : Fin 32) 0x24000, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFAB1]
def dtC6 : List BInstr :=
  [.alu .mul a4 a1 (9 : Fin 32), .alu .mulhu a1 a1 (9 : Fin 32), .lui (9 : Fin 32) 0xFFFF0000, .alu .or (9 : Fin 32) a6 (9 : Fin 32), .alu .add a5 a5 a4, .alu .sltu a4 a5 a4, .alu .add a5 a5 (9 : Fin 32), .alu .add a1 a1 a4, .alu .sltu a4 a5 (9 : Fin 32), .alu .add a1 a1 a4]
def dtC7 : List BInstr :=
  [.alu .add a3 a3 a5, .alu .add a1 a1 a2, .alu .sltu a2 a3 a5, .alu .add (20 : Fin 32) (20 : Fin 32) a3, .alu .add a1 a1 a2, .alu .sltu a2 (20 : Fin 32) a3, .alu .add a1 a1 a2]
def dtC8 : List BInstr :=
  [.lui a3 0xB0000, .aluImm .add a2 a1 0xFFFFFFFF, .aluImm .add a1 a3 0xFFFFFA6B, .alu .sltu a3 x0 a2, .alu .sltu a1 a1 (20 : Fin 32), .alu .or a1 a1 a3]
def dtC9 : List BInstr :=
  [.aluImm .add a1 x0 0x0, .aluImm .add a3 x0 0x3C, .lui a4 0x1000, .alu .mul a3 (21 : Fin 32) a3, .aluImm .add a4 a4 0xFFFFFE10, .lui a5 0x15000, .alu .mul a4 (19 : Fin 32) a4, .aluImm .add a5 a5 0x180, .alu .mul a2 a2 a5, .alu .mulhu (9 : Fin 32) (20 : Fin 32) a5, .alu .mul a5 (20 : Fin 32) a5, .alu .add a0 a0 a3, .alu .add a0 a0 a4, .alu .add a2 a2 (9 : Fin 32), .lui a3 0x86DAA000, .alu .add a0 a0 a5, .aluImm .add a3 a3 0xFFFFFE00, .alu .sltu a4 a0 a5, .alu .add a3 a3 a0, .alu .add a2 a2 a4, .alu .sltu a0 a3 a0, .alu .add a0 a0 a2, .aluImm .add a0 a0 0xFFFFFFF1, .sw (8 : Fin 32) a3 0x8, .sw (8 : Fin 32) a0 0xC]

section
set_option maxRecDepth 20000
theorem dtC1_end : blockEnd dateTimeCode 0xEA dtC1 = some 0x100 := by decide
theorem dtC2_end : blockEnd dateTimeCode 0x100 dtC2 = some 0x118 := by decide
theorem dtC3_end : blockEnd dateTimeCode 0x118 dtC3 = some 0x128 := by decide
theorem dtC4_end : blockEnd dateTimeCode 0x12A dtC4 = some 0x130 := by decide
theorem dtC5_end : blockEnd dateTimeCode 0x13E dtC5 = some 0x15C := by decide
theorem dtC6_end : blockEnd dateTimeCode 0x15C dtC6 = some 0x17A := by decide
theorem dtC7_end : blockEnd dateTimeCode 0x17A dtC7 = some 0x18C := by decide
theorem dtC8_end : blockEnd dateTimeCode 0x18C dtC8 = some 0x1A2 := by decide
theorem dtC9_end : blockEnd dateTimeCode 0x1A8 dtC9 = some 0x1F2 := by decide
end

macro "dnv" : tactic => `(tactic| ((try simp only [dn_z, dn_z', BitVec.ofNat_eq_ofNat]) <;> apply BitVec.eq_of_toNat_eq <;> simp (disch := omega) only [dn_divuL, dn_remuL, dn_add, dn_sub, dn_mul, dn_mulhu, dn_sltu, dn_srl, dn_sll, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd]))
macro "dno" : tactic => `(tactic| (dnv <;> (repeat' split) <;> omega))
macro "dno" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (dnv <;> (try simp only [$ts,*]) <;> (repeat' split) <;> omega))

theorem dn_addN (a b : Nat) : aluEval .add (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) =
    BitVec.ofNat 32 ((a + b) % 4294967296) := by
  apply BitVec.eq_of_toNat_eq; simp only [dn_add, BitVec.toNat_ofNat]; omega
theorem dn_mulN (a b : Nat) : aluEval .mul (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) =
    BitVec.ofNat 32 (a * b % 4294967296) := by
  apply BitVec.eq_of_toNat_eq; simp only [dn_mul, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mul_mod]
theorem dn_mulhuN (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) :
    aluEval .mulhu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = BitVec.ofNat 32 (a * b / 4294967296) := by
  show BitVec.ofNat 32 _ = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
theorem dn_carry (lo x : Nat) (h1 : lo < 4294967296) (h2 : x < 4294967296) :
    aluEval .sltu (BitVec.ofNat 32 ((lo + x) % 4294967296)) (BitVec.ofNat 32 x) =
      BitVec.ofNat 32 ((lo + x) / 4294967296) := by
  apply BitVec.eq_of_toNat_eq
  rw [dn_sltu, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt h2]
  split <;> omega
theorem dn_ofNat_congr {a b : Nat} (h : a = b) : BitVec.ofNat 32 a = BitVec.ofNat 32 b := by rw [h]

macro "dnc" : tactic => `(tactic| (simp (disch := omega) only [BitVec.ofNat_eq_ofNat, dn_mulN, dn_mulhuN, dn_addN, dn_carry, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add, Nat.add_zero]))

theorem dtC1_val (M0 : Word → BitVec 8) (f : Fin 32 → Word) {Y Mo l : Nat} (hY : 1970 ≤ Y)
    (hY2 : Y < 2 ^ 32) (hM : Mo < 2 ^ 32) (hl : (if Mo < 3 then 1 else 0) = l)
    (h18 : f 18 = BitVec.ofNat 32 Y) (h22 : f 22 = BitVec.ofNat 32 Mo) :
    (runBlock dtC1 (M0, f)).2 a1 = BitVec.ofNat 32 ((Y - l) / 400) ∧
    (runBlock dtC1 (M0, f)).2 a3 = BitVec.ofNat 32 ((Y - l) % 400) := by
  simp +decide only [runBlock, BInstr.run, dtC1, upd_app, ↓reduceIte]
  rw [h18, h22]
  have tY : Y % 2 ^ 32 = Y := Nat.mod_eq_of_lt hY2
  have tM : Mo % 2 ^ 32 = Mo := Nat.mod_eq_of_lt hM
  have hl1 : l ≤ 1 := by rw [← hl]; split <;> omega
  refine ⟨?_, ?_⟩ <;> dnv <;> simp only [tY, tM, hl] <;> omega

theorem dtC2_val (M0 : Word → BitVec 8) (f : Fin 32 → Word) {yoe : Nat} (hy : yoe < 400)
    (h13 : f a3 = BitVec.ofNat 32 yoe) :
    (runBlock dtC2 (M0, f)).2 a2 = BitVec.ofNat 32 (yoe / 4) ∧
    (runBlock dtC2 (M0, f)).2 a4 = BitVec.ofNat 32 (yoe / 100) ∧
    (runBlock dtC2 (M0, f)).2 a3 = BitVec.ofNat 32 (yoe * 365) := by
  simp +decide only [runBlock, BInstr.run, dtC2, upd_app, ↓reduceIte]
  rw [h13]
  have tY : yoe % 2 ^ 32 = yoe := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩ <;> dno

theorem dtC3_val (M0 : Word → BitVec 8) (f : Fin 32 → Word) {yoe : Nat} (hy : yoe < 400)
    (h12 : f a2 = BitVec.ofNat 32 (yoe / 4)) (h14 : f a4 = BitVec.ofNat 32 (yoe / 100))
    (h13 : f a3 = BitVec.ofNat 32 (yoe * 365)) :
    (runBlock dtC3 (M0, f)).2 a3 = BitVec.ofNat 32 (yoe * 365 + yoe / 4) ∧
    (runBlock dtC3 (M0, f)).2 a2 = 0 ∧ (runBlock dtC3 (M0, f)).2 a5 = 0 := by
  simp +decide only [runBlock, BInstr.run, dtC3, upd_app, ↓reduceIte]
  rw [h12, h13, h14]
  have m1 : yoe * 365 % 4294967296 = yoe * 365 := Nat.mod_eq_of_lt (by omega)
  have m2 : yoe / 4 % 4294967296 = yoe / 4 := Nat.mod_eq_of_lt (by omega)
  have m3 : yoe / 100 % 4294967296 = yoe / 100 := Nat.mod_eq_of_lt (by omega)
  have m4 : (yoe * 365 + yoe / 4) % 4294967296 = yoe * 365 + yoe / 4 := Nat.mod_eq_of_lt (by omega)
  have e1 : aluEval .sltu (aluEval .add (BitVec.ofNat 32 (yoe * 365)) (BitVec.ofNat 32 (yoe / 4)))
      (BitVec.ofNat 32 (yoe / 4)) = 0 := by dno [m1, m2, m3, m4]
  have e2 : aluEval .sltu (aluEval .add (BitVec.ofNat 32 (yoe * 365)) (BitVec.ofNat 32 (yoe / 4)))
      (BitVec.ofNat 32 (yoe / 100)) = 0 := by dno [m1, m2, m3, m4]
  rw [e1, e2]
  exact ⟨by dno [m1, m2, m3, m4], rfl, rfl⟩

theorem dtC4_val (M0 : Word → BitVec 8) (f : Fin 32 → Word) {c : Nat} (hc : c ≤ 3) (hz : f 0 = 0)
    (h14 : f a4 = BitVec.ofNat 32 c) :
    (runBlock dtC4 (M0, f)).2 a5 = 3 ∧ (runBlock dtC4 (M0, f)).2 a6 = BitVec.ofNat 32 (4294967295 - c) := by
  simp +decide only [runBlock, BInstr.run, dtC4, upd_app, ↓reduceIte]
  rw [h14, hz]
  refine ⟨rfl, ?_⟩
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> decide

theorem dtC5_val (M0 : Word → BitVec 8) (f : Fin 32 → Word) {k Mo mp : Nat} (hk : k < 2 ^ 32) (hM : Mo < 2 ^ 32)
    (hmp : (k + Mo) % 4294967296 = mp) (hmp2 : mp ≤ 11)
    (h15 : f a5 = BitVec.ofNat 32 k) (h22 : f 22 = BitVec.ofNat 32 Mo) :
    (runBlock dtC5 (M0, f)).2 a5 = BitVec.ofNat 32 ((153 * mp + 2) / 5) ∧
    (runBlock dtC5 (M0, f)).2 9 = BitVec.ofNat 32 146097 := by
  simp +decide only [runBlock, BInstr.run, dtC5, upd_app, ↓reduceIte]
  rw [h15, h22]
  have tk : k % 4294967296 = k := Nat.mod_eq_of_lt hk
  have tM : Mo % 4294967296 = Mo := Nat.mod_eq_of_lt hM
  have m1 : mp * 153 % 4294967296 = mp * 153 := Nat.mod_eq_of_lt (by omega)
  have m2 : (mp * 153 + 2) % 4294967296 = mp * 153 + 2 := Nat.mod_eq_of_lt (by omega)
  have m3 : (mp * 153 + 2) * 65536 % 4294967296 = (mp * 153 + 2) * 65536 := Nat.mod_eq_of_lt (by omega)
  have m4 : (mp * 153 + 2) * 65536 / 65536 = mp * 153 + 2 := Nat.mul_div_cancel _ (by decide)
  have m5 : (153 * mp + 2) / 5 % 4294967296 = (153 * mp + 2) / 5 := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, by decide⟩
  dnv
  simp only [tk, tM, hmp, m1, m2, m3, m4, m5]
  omega

theorem dtC6_val (M0 : Word → BitVec 8) (f : Fin 32 → Word) {era c B : Nat} (he : era < 10737419) (hc : c ≤ 3)
    (hB : B < 400) (h11 : f a1 = BitVec.ofNat 32 era) (h9 : f 9 = BitVec.ofNat 32 146097)
    (h16 : f a6 = BitVec.ofNat 32 (4294967295 - c)) (h15 : f a5 = BitVec.ofNat 32 B) :
    (runBlock dtC6 (M0, f)).2 a5 = BitVec.ofNat 32 ((era * 146097 + B + (4294967295 - c)) % 4294967296) ∧
    (runBlock dtC6 (M0, f)).2 a1 = BitVec.ofNat 32 ((era * 146097 + B + (4294967295 - c)) / 4294967296) := by
  simp +decide only [runBlock, BInstr.run, dtC6, upd_app, ↓reduceIte]
  rw [h11, h9, h16, h15]
  have eo : aluEval .or (BitVec.ofNat 32 (4294967295 - c)) 0xFFFF0000 = BitVec.ofNat 32 (4294967295 - c) := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> decide
  rw [eo]
  dnc
  exact ⟨dn_ofNat_congr (by omega), dn_ofNat_congr (by omega)⟩

theorem dtC7_val (M0 : Word → BitVec 8) (f : Fin 32 → Word) {A lo hi D : Nat} (hA : A < 2 ^ 20) (hlo : lo < 2 ^ 32)
    (hhi : hi < 2 ^ 20) (hD : D < 100) (h13 : f a3 = BitVec.ofNat 32 A) (h15 : f a5 = BitVec.ofNat 32 lo)
    (h11 : f a1 = BitVec.ofNat 32 hi) (h12 : f a2 = 0) (h20 : f 20 = BitVec.ofNat 32 D) :
    (runBlock dtC7 (M0, f)).2 20 = BitVec.ofNat 32 ((hi * 4294967296 + lo + A + D) % 4294967296) ∧
    (runBlock dtC7 (M0, f)).2 a1 = BitVec.ofNat 32 ((hi * 4294967296 + lo + A + D) / 4294967296) := by
  simp +decide only [runBlock, BInstr.run, dtC7, upd_app, ↓reduceIte]
  rw [h13, h15, h11, h12, h20]
  dnc
  exact ⟨dn_ofNat_congr (by omega), dn_ofNat_congr (by omega)⟩

theorem dn_sltuN (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) :
    aluEval .sltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = BitVec.ofNat 32 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [dn_sltu, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  split <;> rfl

theorem dtC8_val (M0 : Word → BitVec 8) (f : Fin 32 → Word) {lo hi : Nat} (hlo : lo < 2 ^ 32)
    (hhi : 1 ≤ hi) (hhi2 : hi < 2 ^ 20) (h11 : f a1 = BitVec.ofNat 32 hi)
    (h20 : f 20 = BitVec.ofNat 32 lo) (hV : 719468 ≤ (hi - 1) * 4294967296 + lo) :
    (runBlock dtC8 (M0, f)).2 a2 = BitVec.ofNat 32 (hi - 1) ∧
    branchTaken .bne ((runBlock dtC8 (M0, f)).2 a1) 0 = true := by
  simp +decide only [runBlock, BInstr.run, dtC8, upd_app, ↓reduceIte]
  rw [h11, h20]
  have ea : aluEval .add (BitVec.ofNat 32 hi) 0xFFFFFFFF = BitVec.ofNat 32 (hi - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
    omega
  have e7 : aluEval .add 0xB0000 0xFFFFFA6B = BitVec.ofNat 32 719467 := by decide
  have e0 : (0 : Word) = BitVec.ofNat 32 0 := rfl
  refine ⟨ea, ?_⟩
  rw [ea, e7, e0, dn_sltuN _ _ (by decide) (by omega), dn_sltuN _ _ (by decide) (by omega)]
  by_cases h1 : hi - 1 = 0
  · rw [if_pos (by omega : 719467 < lo), if_neg (by omega : ¬ 0 < hi - 1)]; decide
  · rw [if_pos (by omega : 0 < hi - 1)]
    split <;> decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 4000000 in
theorem dtC9_val (M0 : Word → BitVec 8) (f : Fin 32 → Word) {vh vl h mi s : Nat} (hvl : vl < 2 ^ 32)
    (hvh : vh < 2 ^ 10) (hh : h ≤ 23) (hmi : mi ≤ 59) (hs : s ≤ 59) (hV : 719468 ≤ vh * 4294967296 + vl)
    (h12 : f a2 = BitVec.ofNat 32 vh) (h20 : f 20 = BitVec.ofNat 32 vl) (h21 : f 21 = BitVec.ofNat 32 mi)
    (h19 : f 19 = BitVec.ofNat 32 h) (h10 : f a0 = BitVec.ofNat 32 s) (hz : f 0 = 0) :
    (runBlock dtC9 (M0, f)).2 a1 = 0 ∧
    (runBlock dtC9 (M0, f)).2 a3 = BitVec.ofNat 32
      (((vh * 4294967296 + vl - 719468) * 86400 + h * 3600 + mi * 60 + s) % 4294967296) ∧
    (runBlock dtC9 (M0, f)).2 a0 = BitVec.ofNat 32
      (((vh * 4294967296 + vl - 719468) * 86400 + h * 3600 + mi * 60 + s) / 4294967296) := by
  simp +decide only [runBlock, BInstr.run, dtC9, upd_app, ↓reduceIte]
  rw [h12, h20, h21, h19, h10, hz]
  dnc
  have m1 : mi * 60 % 4294967296 = mi * 60 := Nat.mod_eq_of_lt (by omega)
  have m2 : h * 3600 % 4294967296 = h * 3600 := Nat.mod_eq_of_lt (by omega)
  have m3 : (s + mi * 60) % 4294967296 = s + mi * 60 := Nat.mod_eq_of_lt (by omega)
  have m4 : (s + mi * 60 + h * 3600) % 4294967296 = s + mi * 60 + h * 3600 := Nat.mod_eq_of_lt (by omega)
  have m5 : vh * 86400 % 4294967296 = vh * 86400 := Nat.mod_eq_of_lt (by omega)
  simp only [m1, m2, m3, m4, m5]
  obtain ⟨Pl, hPl⟩ : ∃ Pl, vl * 86400 % 4294967296 = Pl := ⟨_, rfl⟩
  obtain ⟨Ph, hPh⟩ : ∃ Ph, vl * 86400 / 4294967296 = Ph := ⟨_, rfl⟩
  have hP : vl * 86400 = Ph * 4294967296 + Pl := by rw [← hPl, ← hPh]; omega
  have hPl' : Pl < 4294967296 := by rw [← hPl]; exact Nat.mod_lt _ (by decide)
  have hPh' : Ph < 86400 := by omega
  rw [hPl, hPh]
  obtain ⟨A1, hA1⟩ : ∃ A1, (s + mi * 60 + h * 3600 + Pl) % 4294967296 = A1 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C1, (s + mi * 60 + h * 3600 + Pl) / 4294967296 = C1 := ⟨_, rfl⟩
  have hA : s + mi * 60 + h * 3600 + Pl = C1 * 4294967296 + A1 := by rw [← hA1, ← hC1]; omega
  have hA1' : A1 < 4294967296 := by rw [← hA1]; exact Nat.mod_lt _ (by decide)
  rw [hA1, hC1]
  obtain ⟨A3, hA3⟩ : ∃ A3, (2262474240 + A1) % 4294967296 = A3 := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C2, (2262474240 + A1) / 4294967296 = C2 := ⟨_, rfl⟩
  have hB : 2262474240 + A1 = C2 * 4294967296 + A3 := by rw [← hA3, ← hC2]; omega
  have hA3' : A3 < 4294967296 := by rw [← hA3]; exact Nat.mod_lt _ (by decide)
  rw [hA3, hC2]
  have hC1' : C1 ≤ 1 := by omega
  have hC2' : C2 ≤ 1 := by omega
  have ht : (vh * 4294967296 + vl - 719468) * 86400 + h * 3600 + mi * 60 + s =
      (vh * 86400 + Ph + C1 + C2 - 15) * 4294967296 + A3 := by omega
  rw [ht]
  refine ⟨trivial, dn_ofNat_congr (by omega), dn_ofNat_congr (by omega)⟩



theorem dn_bltu (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) :
    branchTaken .bltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (a < b) := by
  simp only [branchTaken, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem dt_blk {is : List BInstr} {Mx : Word → BitVec 8} {n : Machine} {off off' : Nat}
    (st : St Mx DT n off (reg n)) (hc : CodeIn Mx DT dateTimeCode) (he : blockEnd dateTimeCode off is = some off')
    (hok : BlockOk DT dateTimeCode.length is (Mx, reg n)) :
    ∃ n', Steps n n' ∧ St (runBlock is (Mx, reg n)).1 DT n' off' (reg n') ∧
      ∀ q, reg n' q = (runBlock is (Mx, reg n)).2 q := by
  obtain ⟨n', c, u⟩ := St.block is st hc he hok
  exact ⟨n', c, ⟨u.pc, u.mem, fun _ => rfl⟩, u.regs⟩

theorem dt_eV (T d : Nat) (hV : T - 4294967296 = d + 719468) (hT : 4294967296 + 719468 ≤ T) :
    (T / 4294967296 - 1) * 4294967296 + T % 4294967296 - 719468 = d := by
  have h1 := Nat.div_add_mod' T 4294967296
  have h2 : 1 ≤ T / 4294967296 := (Nat.le_div_iff_mul_le (by decide)).mpr (Nat.le_trans (by decide) hT)
  generalize T / 4294967296 = q at h1 h2 ⊢
  generalize T % 4294967296 = r at h1 h2 ⊢
  rw [Nat.sub_one_mul, ← Nat.sub_add_comm (Nat.le_mul_of_pos_left _ h2), h1, hV, Nat.add_sub_cancel]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- From 0xEA, with the fields checked: `days_from_civil` and the seconds,
stored as two words at `s0 + 8`, and on to the shared exit at 0x84 with
the tag 0 in `a1`. -/
theorem dt_arith {Mx : Word → BitVec 8} {n : Machine} {out : Word} {Y Mo D h mi s : Nat}
    (st : St Mx DT n 0xEA (reg n)) (hc : CodeIn Mx DT dateTimeCode)
    (hY : 1970 ≤ Y) (hY2 : Y < 2 ^ 32) (hM1 : 1 ≤ Mo) (hM2 : Mo ≤ 12) (hD1 : 1 ≤ D) (hD2 : D ≤ 31) (hh : h ≤ 23)
    (hmi : mi ≤ 59) (hs : s ≤ 59)
    (r18 : reg n 18 = BitVec.ofNat 32 Y) (r22 : reg n 22 = BitVec.ofNat 32 Mo) (r20 : reg n 20 = BitVec.ofNat 32 D)
    (r19 : reg n 19 = BitVec.ofNat 32 h) (r21 : reg n 21 = BitVec.ofNat 32 mi) (r10 : reg n a0 = BitVec.ofNat 32 s)
    (r8 : reg n 8 = out) (ho : (out + 8).toNat % 4 = 0) (ho' : (out + 0xC).toNat % 4 = 0)
    (sO8 : Sep (out + 8) 4 DT dateTimeCode.length) (sOC : Sep (out + 0xC) 4 DT dateTimeCode.length) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore32 Mx (out + 8)
        (BitVec.ofNat 32 ((daysFromCivil Y Mo D * 86400 + h * 3600 + mi * 60 + s) % 4294967296))) (out + 0xC)
        (BitVec.ofNat 32 ((daysFromCivil Y Mo D * 86400 + h * 3600 + mi * 60 + s) / 4294967296))) DT n' 0x84 (reg n') ∧
      reg n' a1 = 0 ∧ ∀ q, q.val ∈ [2, 3, 4, 8, 18, 19, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  have hz := st.zero
  obtain ⟨l, hl⟩ : ∃ l, (if Mo < 3 then 1 else 0) = l := ⟨_, rfl⟩
  have hl1 : l ≤ 1 := by rw [← hl]; split <;> omega
  -- 0xEA: the era and the year of the era
  obtain ⟨n1, c1, u1, R1⟩ := dt_blk st hc dtC1_end (by simp only [BlockOk, BInstr.ok, dtC1, and_self])
  have u1' : St Mx DT n1 0x100 (reg n1) := by have := u1; rwa [show (runBlock dtC1 (Mx, reg n)).1 = Mx from rfl] at this
  obtain ⟨v1a1, v1a3⟩ := dtC1_val Mx (reg n) hY hY2 (by omega) hl r18 r22
  rw [← R1] at v1a1 v1a3
  have K1 : ∀ q, q ∉ dtC1.filterMap BInstr.dst → reg n1 q = reg n q := fun q hq => by
    rw [R1]; exact runBlock_reg _ _ _ q hz hq
  -- 0x100
  obtain ⟨n2, c2, u2, R2⟩ := dt_blk u1' hc dtC2_end (by simp only [BlockOk, BInstr.ok, dtC2, and_self])
  have u2' : St Mx DT n2 0x118 (reg n2) := by have := u2; rwa [show (runBlock dtC2 (Mx, reg n1)).1 = Mx from rfl] at this
  obtain ⟨v2a2, v2a4, v2a3⟩ := dtC2_val Mx (reg n1) (Nat.mod_lt _ (by decide)) v1a3
  rw [← R2] at v2a2 v2a4 v2a3
  have K2 : ∀ q, q ∉ dtC2.filterMap BInstr.dst → reg n2 q = reg n1 q := fun q hq => by
    rw [R2]; exact runBlock_reg _ _ _ q u1'.zero hq
  -- 0x118
  obtain ⟨n3, c3, u3, R3⟩ := dt_blk u2' hc dtC3_end (by simp only [BlockOk, BInstr.ok, dtC3, and_self])
  have u3' : St Mx DT n3 0x128 (reg n3) := by have := u3; rwa [show (runBlock dtC3 (Mx, reg n2)).1 = Mx from rfl] at this
  obtain ⟨v3a3, v3a2, v3a5⟩ := dtC3_val Mx (reg n2) (Nat.mod_lt _ (by decide)) v2a2 v2a4 v2a3
  rw [← R3] at v3a3 v3a2 v3a5
  have K3 : ∀ q, q ∉ dtC3.filterMap BInstr.dst → reg n3 q = reg n2 q := fun q hq => by
    rw [R3]; exact runBlock_reg _ _ _ q u2'.zero hq
  obtain ⟨n4, d4, u4⟩ := u3'.notTaken hc 0x12A dtm_at_128 (by decide) (by
    simp only [branchTaken]; rw [v3a5, u3'.zero]; decide)
  -- 0x12A
  obtain ⟨n5, c5, u5, R5⟩ := dt_blk u4.self hc dtC4_end (by simp only [BlockOk, BInstr.ok, dtC4, and_self])
  have u5' : St Mx DT n5 0x130 (reg n5) := by have := u5; rwa [show (runBlock dtC4 (Mx, reg n4)).1 = Mx from rfl] at this
  have v3a4 : reg n3 a4 = BitVec.ofNat 32 ((Y - l) % 400 / 100) := by rw [K3 _ (by decide), v2a4]
  obtain ⟨v5a5, v5a6⟩ := dtC4_val Mx (reg n4) (c := (Y - l) % 400 / 100) (by omega) u4.self.zero
    (by rw [u4.regs, v3a4])
  rw [← R5] at v5a5 v5a6
  have K5 : ∀ q, q ∉ dtC4.filterMap BInstr.dst → reg n5 q = reg n3 q := fun q hq => by
    rw [R5, runBlock_reg _ _ _ q u4.self.zero hq, u4.regs]
  have r22_5 : reg n5 22 = BitVec.ofNat 32 Mo := by
    rw [K5 _ (by decide), K3 _ (by decide), K2 _ (by decide), K1 _ (by decide), r22]
  -- 0x130: the month's offset into a March-based year
  obtain ⟨k, mp, hk, hmp, hmp2, hmpv, n7, c7, u7, v7, K7⟩ : ∃ k mp : Nat, k < 2 ^ 32 ∧ (k + Mo) % 4294967296 = mp ∧
      mp ≤ 11 ∧ mp = (if Mo < 3 then Mo + 9 else Mo - 3) ∧ ∃ n7, Steps n5 n7 ∧ St Mx DT n7 0x13E (reg n7) ∧
      reg n7 a5 = BitVec.ofNat 32 k ∧ ∀ q, q ≠ a5 → reg n7 q = reg n5 q := by
    by_cases hM3 : Mo < 3
    · obtain ⟨n6, d6, u6⟩ := u5'.taken hc 0x13C dtm_at_130 (by decide) (by
        rw [r22_5, v5a5, show (3 : Word) = BitVec.ofNat 32 3 from rfl, dn_bltu _ _ (by omega) (by decide)]
        exact decide_eq_true hM3)
      obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hc dtm_at_13c (off' := 0x13E) (by decide)
      refine ⟨9, Mo + 9, by decide, by omega, by omega, by rw [if_pos hM3], n7,
        .cons d6 (.single d7), u7.self, ?_, fun q hq => ?_⟩
      · rw [u7.regs, upd_app]; simp only [↓reduceIte]; rw [u6.self.zero]; rfl
      · rw [u7.regs, upd_ne' hq u6.self.zero, u6.regs]
    · obtain ⟨n6, d6, u6⟩ := u5'.notTaken hc 0x134 dtm_at_130 (by decide) (by
        rw [r22_5, v5a5, show (3 : Word) = BitVec.ofNat 32 3 from rfl, dn_bltu _ _ (by omega) (by decide)]
        exact decide_eq_false hM3)
      obtain ⟨n6', d6', u6'⟩ := u6.self.aluImm hc dtm_at_134 (off' := 0x136) (by decide)
      obtain ⟨n7, d7, u7⟩ := u6'.self.jump hc dtm_at_136 (off' := 0x13E) (by decide) (by rw [u6'.pc]; decide)
      refine ⟨4294967293, Mo - 3, by decide, by omega, by omega, by rw [if_neg hM3], n7,
        .cons d6 (.cons d6' (.single d7)), u7.self, ?_, fun q hq => ?_⟩
      · rw [u7.regs, u6'.regs, upd_app]; simp only [↓reduceIte]; rw [u6.self.zero]; rfl
      · rw [u7.regs, u6'.regs, upd_ne' hq u6.self.zero, u6.regs]
  have r22_7 : reg n7 22 = BitVec.ofNat 32 Mo := by rw [K7 _ (by decide), r22_5]
  -- 0x13E
  obtain ⟨n8, c8, u8, R8⟩ := dt_blk u7 hc dtC5_end (by simp only [BlockOk, BInstr.ok, dtC5, and_self])
  have u8' : St Mx DT n8 0x15C (reg n8) := by have := u8; rwa [show (runBlock dtC5 (Mx, reg n7)).1 = Mx from rfl] at this
  obtain ⟨v8a5, v8s1⟩ := dtC5_val Mx (reg n7) hk (by omega) hmp hmp2 v7 r22_7
  rw [← R8] at v8a5 v8s1
  have K8 : ∀ q, q ∉ dtC5.filterMap BInstr.dst → reg n8 q = reg n7 q := fun q hq => by
    rw [R8]; exact runBlock_reg _ _ _ q u7.zero hq
  -- registers set before the branch, still in place at 0x15C
  have back : ∀ q, q ∉ dtC5.filterMap BInstr.dst → q ≠ a5 → q ∉ dtC4.filterMap BInstr.dst →
      reg n8 q = reg n3 q := fun q h1 h2 h3 => by rw [K8 q h1, K7 q h2, K5 q h3]
  have v8a1 : reg n8 a1 = BitVec.ofNat 32 ((Y - l) / 400) := by
    rw [back _ (by decide) (by decide) (by decide), K3 _ (by decide), K2 _ (by decide), v1a1]
  have v8a6 : reg n8 a6 = BitVec.ofNat 32 (4294967295 - (Y - l) % 400 / 100) := by
    rw [K8 _ (by decide), K7 _ (by decide), v5a6]
  -- 0x15C
  obtain ⟨n9, c9, u9, R9⟩ := dt_blk u8' hc dtC6_end (by simp only [BlockOk, BInstr.ok, dtC6, and_self])
  have u9' : St Mx DT n9 0x17A (reg n9) := by have := u9; rwa [show (runBlock dtC6 (Mx, reg n8)).1 = Mx from rfl] at this
  obtain ⟨v9a5, v9a1⟩ := dtC6_val Mx (reg n8) (era := (Y - l) / 400) (c := (Y - l) % 400 / 100)
    (B := (153 * mp + 2) / 5) (by omega) (by omega) (by omega) v8a1 v8s1 v8a6 v8a5
  rw [← R9] at v9a5 v9a1
  have K9 : ∀ q, q ∉ dtC6.filterMap BInstr.dst → reg n9 q = reg n8 q := fun q hq => by
    rw [R9]; exact runBlock_reg _ _ _ q u8'.zero hq
  obtain ⟨S, hS⟩ : ∃ S, (Y - l) / 400 * 146097 + (153 * mp + 2) / 5 + (4294967295 - (Y - l) % 400 / 100) = S :=
    ⟨_, rfl⟩
  rw [hS] at v9a5 v9a1
  have back9 : ∀ q, q ∉ dtC6.filterMap BInstr.dst → q ∉ dtC5.filterMap BInstr.dst → q ≠ a5 →
      q ∉ dtC4.filterMap BInstr.dst → reg n9 q = reg n3 q := fun q h0 h1 h2 h3 => by rw [K9 q h0, back q h1 h2 h3]
  have v9a3 : reg n9 a3 = BitVec.ofNat 32 ((Y - l) % 400 * 365 + (Y - l) % 400 / 4) := by
    rw [back9 _ (by decide) (by decide) (by decide) (by decide), v3a3]
  have v9a2 : reg n9 a2 = 0 := by rw [back9 _ (by decide) (by decide) (by decide) (by decide), v3a2]
  have v9s4 : reg n9 20 = BitVec.ofNat 32 D := by
    rw [back9 _ (by decide) (by decide) (by decide) (by decide), K3 _ (by decide), K2 _ (by decide),
      K1 _ (by decide), r20]
  -- 0x17A
  obtain ⟨n10, c10, u10, R10⟩ := dt_blk u9' hc dtC7_end (by simp only [BlockOk, BInstr.ok, dtC7, and_self])
  have u10' : St Mx DT n10 0x18C (reg n10) := by
    have := u10; rwa [show (runBlock dtC7 (Mx, reg n9)).1 = Mx from rfl] at this
  have hSb : S < 2 ^ 42 := by omega
  obtain ⟨v10s4, v10a1⟩ := dtC7_val Mx (reg n9) (A := (Y - l) % 400 * 365 + (Y - l) % 400 / 4)
    (lo := S % 4294967296) (hi := S / 4294967296) (D := D) (by omega) (Nat.mod_lt _ (by decide)) (by omega)
    (by omega) v9a3 v9a5 v9a1 v9a2 v9s4
  rw [← R10] at v10s4 v10a1
  have K10 : ∀ q, q ∉ dtC7.filterMap BInstr.dst → reg n10 q = reg n9 q := fun q hq => by
    rw [R10]; exact runBlock_reg _ _ _ q u9'.zero hq
  obtain ⟨T, hT⟩ : ∃ T, S / 4294967296 * 4294967296 + S % 4294967296 + ((Y - l) % 400 * 365 + (Y - l) % 400 / 4) + D
      = T := ⟨_, rfl⟩
  rw [hT] at v10s4 v10a1
  -- the day count, as `days_from_civil` gives it
  have hdays := dt_days Y Mo D hY hM1 hM2 hD1
  simp only [hl] at hdays
  have hV : T - 4294967296 = daysFromCivil Y Mo D + 719468 := by
    rw [hdays, ← hT, ← hS, hmpv]; omega
  have hTb : 4294967296 + 719468 ≤ T ∧ T < 2 ^ 42 := ⟨by omega, by omega⟩
  -- 0x18C: the check that the count reaches the epoch, which holds
  obtain ⟨n11, c11, u11, R11⟩ := dt_blk u10' hc dtC8_end (by simp only [BlockOk, BInstr.ok, dtC8, and_self])
  have u11' : St Mx DT n11 0x1A2 (reg n11) := by
    have := u11; rwa [show (runBlock dtC8 (Mx, reg n10)).1 = Mx from rfl] at this
  obtain ⟨v11a2, br11⟩ := dtC8_val Mx (reg n10) (lo := T % 4294967296) (hi := T / 4294967296)
    (Nat.mod_lt _ (by decide)) (by omega) (by omega) v10a1 v10s4 (by omega)
  rw [← R11] at v11a2 br11
  have K11 : ∀ q, q ∉ dtC8.filterMap BInstr.dst → reg n11 q = reg n10 q := fun q hq => by
    rw [R11]; exact runBlock_reg _ _ _ q u10'.zero hq
  obtain ⟨n12, d12, u12⟩ := u11'.taken hc 0x1A8 dtm_at_1a2 (by decide) (by rw [u11'.zero]; exact br11)
  -- registers the arithmetic leaves alone since 0xEA
  have Kall : ∀ q, q ∉ dtC1.filterMap BInstr.dst → q ∉ dtC2.filterMap BInstr.dst →
      q ∉ dtC3.filterMap BInstr.dst → q ∉ dtC4.filterMap BInstr.dst → q ≠ a5 →
      q ∉ dtC5.filterMap BInstr.dst → q ∉ dtC6.filterMap BInstr.dst → q ∉ dtC7.filterMap BInstr.dst →
      q ∉ dtC8.filterMap BInstr.dst → reg n12 q = reg n q := fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    rw [u12.regs, K11 q h9, K10 q h8, back9 q h7 h6 h5 h4, K3 q h3, K2 q h2, K1 q h1]
  have r12_8 : reg n12 8 = out := by
    rw [Kall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), r8]
  -- 0x1A8: the seconds, and the two stores
  obtain ⟨n13, c13, u13, R13⟩ := dt_blk u12.self hc dtC9_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, dtC9, upd_app, ↓reduceIte, and_true, true_and]
    rw [r12_8]; exact ⟨⟨ho, sO8⟩, ho', sOC⟩)
  obtain ⟨v13a1, v13a3, v13a0⟩ := dtC9_val Mx (reg n12) (vh := T / 4294967296 - 1) (vl := T % 4294967296)
    (h := h) (mi := mi) (s := s) (Nat.mod_lt _ (by decide)) (by omega) hh hmi hs (by omega)
    (by rw [u12.regs, v11a2])
    (by rw [u12.regs, K11 _ (by decide), v10s4])
    (by rw [Kall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), r21])
    (by rw [Kall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), r19])
    (by rw [Kall _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), r10])
    u12.self.zero
  have eV := dt_eV T (daysFromCivil Y Mo D) hV hTb.1
  rw [eV] at v13a3 v13a0
  have eM : (runBlock dtC9 (Mx, reg n12)).1 = memStore32 (memStore32 Mx (reg n12 8 + 8)
      ((runBlock dtC9 (Mx, reg n12)).2 a3)) (reg n12 8 + 0xC) ((runBlock dtC9 (Mx, reg n12)).2 a0) := rfl
  rw [eM, v13a3, v13a0, r12_8] at u13
  obtain ⟨n14, d14, u14⟩ := u13.jump (by
      intro i hi
      rw [memStore32_get_sep (sOC.subR (c := i) (l := 1) (by omega)),
        memStore32_get_sep (sO8.subR (c := i) (l := 1) (by omega))]
      exact hc i hi) dtm_at_1f2 (off' := 0x84) (by decide) (by rw [u13.pc]; decide)
  refine ⟨n14, c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (.cons d12 (c13.trans (.single d14)))))))))))), u14.self, ?_, fun q hq => ?_⟩
  · rw [u14.regs, R13, v13a1]
  · have hq' : q ∉ dtC9.filterMap BInstr.dst := by revert hq; revert q; decide
    rw [u14.regs, R13, runBlock_reg _ _ _ q u12.self.zero hq',
      Kall q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]


def dtE1 : List BInstr :=
  [.lw a0 sp 0xC, .aluImm .add a1 x0 0x1F, .lui a2 0x1000, .aluImm .add a3 a2 0x5AA, .alu .srl a3 a3 (22 : Fin 32), .aluImm .and a3 a3 0x1]
def dtE2 : List BInstr :=
  [.aluImm .add a1 a2 0xFFFFFA50, .alu .srl a1 a1 (22 : Fin 32), .aluImm .and a1 a1 0x1]
def dtE3 : List BInstr :=
  [.aluImm .add a1 x0 0x64, .alu .remu a1 (18 : Fin 32) a1, .aluImm .add a2 x0 0x190, .alu .remu a2 (18 : Fin 32) a2, .alu .sltu a1 x0 a1, .aluImm .sltu a2 a2 0x1, .alu .or a1 a1 a2, .aluImm .add a1 a1 0x1C]

section
set_option maxRecDepth 20000
theorem dtE1_end : blockEnd dateTimeCode 0xB2 dtE1 = some 0xC2 := by decide
theorem dtE2_end : blockEnd dateTimeCode 0xC4 dtE2 = some 0xCE := by decide
theorem dtE3_end : blockEnd dateTimeCode 0x1FE dtE3 = some 0x21A := by decide
end

theorem dt_m31 : ∀ i : Fin 13, 1 ≤ i.val → (branchTaken .bne (aluEval .and (aluEval .srl (aluEval .add 0x1000 0x5AA)
    (BitVec.ofNat 32 i.val)) 1) 0 = true ↔
    (i.val = 1 ∨ i.val = 3 ∨ i.val = 5 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 10 ∨ i.val = 12)) := by decide
theorem dt_m30 : ∀ i : Fin 13, 1 ≤ i.val → (branchTaken .beq (aluEval .and (aluEval .srl
    (aluEval .add 0x1000 0xFFFFFA50) (BitVec.ofNat 32 i.val)) 1) 0 = true ↔
    ¬(i.val = 4 ∨ i.val = 6 ∨ i.val = 9 ∨ i.val = 11)) := by decide
theorem dn_and3 (x : Word) : (aluEval .and x 3).toNat = x.toNat % 4 := and_low (k := 2) (by decide) (by decide)

theorem dt_y4 (Y : Nat) (hY : Y < 2 ^ 32) :
    branchTaken .beq (aluEval .and (BitVec.ofNat 32 Y) 3) 0 = decide (Y % 4 = 0) := by
  have h := dn_and3 (BitVec.ofNat 32 Y)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hY] at h
  unfold branchTaken
  by_cases h4 : Y % 4 = 0
  · have e : aluEval .and (BitVec.ofNat 32 Y) 3 = 0 := BitVec.eq_of_toNat_eq (by rw [h, h4]; rfl)
    rw [e, decide_eq_true h4]; rfl
  · rw [decide_eq_false h4]
    exact (beq_eq_false_iff_ne).mpr (fun e => h4 (by rw [e] at h; exact h.symm))

theorem dt_leap (Y : Nat) (hY : Y < 2 ^ 32) (h4 : Y % 4 = 0) :
    aluEval .add (aluEval .or (aluEval .sltu 0 (aluEval .remu (BitVec.ofNat 32 Y) (aluEval .add 0 100)))
      (aluEval .sltu (aluEval .remu (BitVec.ofNat 32 Y) (aluEval .add 0 400)) 1)) 0x1C =
    BitVec.ofNat 32 (if isLeapYear Y then 29 else 28) := by
  have r1 : aluEval .remu (BitVec.ofNat 32 Y) (aluEval .add 0 100) = BitVec.ofNat 32 (Y % 100) := by
    rw [dn_z]; apply BitVec.eq_of_toNat_eq
    rw [show (100 : Word) = BitVec.ofNat 32 100 from rfl, dn_remuL _ _ (by decide) (by decide)]
    simp only [BitVec.toNat_ofNat]; omega
  have r2 : aluEval .remu (BitVec.ofNat 32 Y) (aluEval .add 0 400) = BitVec.ofNat 32 (Y % 400) := by
    rw [dn_z]; apply BitVec.eq_of_toNat_eq
    rw [show (400 : Word) = BitVec.ofNat 32 400 from rfl, dn_remuL _ _ (by decide) (by decide)]
    simp only [BitVec.toNat_ofNat]; omega
  rw [r1, r2, show (0 : Word) = BitVec.ofNat 32 0 from rfl, show (1 : Word) = BitVec.ofNat 32 1 from rfl,
    dn_sltuN _ _ (by decide) (by omega), dn_sltuN _ _ (by omega) (by decide)]
  by_cases h1 : Y % 100 = 0
  · by_cases h2 : Y % 400 = 0
    · have hl : isLeapYear Y = true := by unfold isLeapYear; rw [h4, h1, h2]; rfl
      rw [if_neg (by omega), if_pos (by omega), hl]; decide
    · have hb : (Y % 400 == 0) = false := beq_eq_false_iff_ne.mpr h2
      have hl : isLeapYear Y = false := by unfold isLeapYear; rw [h4, h1, hb]; rfl
      rw [if_neg (by omega), if_neg (by omega), hl]; decide
  · have hb : (Y % 100 != 0) = true := bne_iff_ne.mpr h1
    have hl : isLeapYear Y = true := by unfold isLeapYear; rw [h4, hb]; rfl
    rw [if_pos (by omega), if_neg (by omega), hl]; decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From 0xB2: the days in the month, in `a1`, and the seconds, in `a0`. -/
theorem dt_dim {Mx : Word → BitVec 8} {n : Machine} {F : Word} {Y Mo s : Nat}
    (st : St Mx DT n 0xB2 (reg n)) (hc : CodeIn Mx DT dateTimeCode) (hY2 : Y < 2 ^ 32) (hM1 : 1 ≤ Mo)
    (hM2 : Mo ≤ 12) (r18 : reg n 18 = BitVec.ofNat 32 Y) (r22 : reg n 22 = BitVec.ofNat 32 Mo) (rsp : reg n sp = F)
    (hF : (F + 0xC).toNat % 4 = 0) (ls : memLoad32 Mx (F + 0xC) = BitVec.ofNat 32 s) :
    ∃ n', Steps n n' ∧ St Mx DT n' 0xD4 (reg n') ∧ reg n' a1 = BitVec.ofNat 32 (daysInMonth Y Mo) ∧
      reg n' a0 = BitVec.ofNat 32 s ∧ ∀ q, q.val ∉ [10, 11, 12, 13] → reg n' q = reg n q := by
  have hz := st.zero
  obtain ⟨n1, c1, u1, R1⟩ := dt_blk st hc dtE1_end (by
    simp +decide only [BlockOk, BInstr.ok, dtE1, and_true, true_and]; rw [rsp]; exact hF)
  have u1' : St Mx DT n1 0xC2 (reg n1) := by have := u1; rwa [show (runBlock dtE1 (Mx, reg n)).1 = Mx from rfl] at this
  have K1 : ∀ q, q.val ∉ [10, 11, 12, 13] → reg n1 q = reg n q := fun q hq => by
    have hd : q ∉ dtE1.filterMap BInstr.dst := by
      simp only [dtE1, List.filterMap_cons, List.filterMap_nil, BInstr.dst, Option.some]
      revert hq; revert q; decide
    rw [R1]; exact runBlock_reg _ _ _ q hz hd
  have v1a0 : reg n1 a0 = BitVec.ofNat 32 s := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, dtE1, upd_app, ↓reduceIte]; rw [rsp, ls]
  have v1a3 : reg n1 a3 = aluEval .and (aluEval .srl (aluEval .add 0x1000 0x5AA) (BitVec.ofNat 32 Mo)) 1 := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, dtE1, upd_app, ↓reduceIte]; rw [r22]
  have v1a2 : reg n1 a2 = 0x1000 := by rw [R1]; simp +decide only [runBlock, BInstr.run, dtE1, upd_app, ↓reduceIte]
  have v1a1 : reg n1 a1 = 31 := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, dtE1, upd_app, ↓reduceIte]
  have m31 := dt_m31 ⟨Mo, by omega⟩ hM1
  have m30 := dt_m30 ⟨Mo, by omega⟩ hM1
  simp only at m31 m30
  by_cases h31 : Mo = 1 ∨ Mo = 3 ∨ Mo = 5 ∨ Mo = 7 ∨ Mo = 8 ∨ Mo = 10 ∨ Mo = 12
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc 0xD4 dtm_at_c2 (by decide) (by rw [v1a3, u1'.zero]; exact m31.mpr h31)
    refine ⟨n2, c1.trans (.single d2), u2.self, ?_, by rw [u2.regs, v1a0], fun q hq => by rw [u2.regs, K1 q hq]⟩
    rw [u2.regs, v1a1]; unfold daysInMonth; rw [if_pos h31]; rfl
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc 0xC4 dtm_at_c2 (by decide) (by
    rw [v1a3, u1'.zero]; exact Bool.eq_false_iff.mpr (fun h => h31 (m31.mp h)))
  obtain ⟨n3, c3, u3, R3⟩ := dt_blk u2.self hc dtE2_end (by simp only [BlockOk, BInstr.ok, dtE2, and_self])
  have u3' : St Mx DT n3 0xCE (reg n3) := by
    have := u3; rwa [show (runBlock dtE2 (Mx, reg n2)).1 = Mx from rfl] at this
  have v3a1 : reg n3 a1 = aluEval .and (aluEval .srl (aluEval .add 0x1000 0xFFFFFA50) (BitVec.ofNat 32 Mo)) 1 := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, dtE2, upd_app, ↓reduceIte]
    simp only [u2.regs]; rw [v1a2, K1 _ (by decide), r22]
  have K3 : ∀ q, q ≠ a1 → reg n3 q = reg n1 q := fun q hq => by
    have hd : q ∉ dtE2.filterMap BInstr.dst := by
      simp only [dtE2, List.filterMap_cons, List.filterMap_nil, BInstr.dst, Option.some, List.mem_cons,
        List.mem_nil_iff, or_false, or_self]
      exact hq
    rw [R3, runBlock_reg _ _ _ q u2.self.zero hd, u2.regs]
  by_cases h30 : Mo = 4 ∨ Mo = 6 ∨ Mo = 9 ∨ Mo = 11
  · obtain ⟨n4, d4, u4⟩ := u3'.notTaken hc 0xD2 dtm_at_ce (by decide) (by
      rw [v3a1, u3'.zero]; exact Bool.eq_false_iff.mpr (fun h => m30.mp h h30))
    obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc dtm_at_d2 (off' := 0xD4) (by decide)
    refine ⟨n5, c1.trans (.cons d2 (c3.trans (.cons d4 (.single d5)))), u5.self, ?_, ?_, fun q hq => ?_⟩
    · rw [u5.regs, upd_app]; simp only [↓reduceIte]; rw [u4.self.zero]
      unfold daysInMonth; rw [if_neg h31, if_pos h30]; rfl
    · rw [u5.regs, upd_ne' (by decide) u4.self.zero, u4.regs, K3 _ (by decide), v1a0]
    · rw [u5.regs, upd_ne' (by intro h; apply hq; rw [h]; decide) u4.self.zero, u4.regs,
        K3 q (by intro h; apply hq; rw [h]; decide), K1 q hq]
  have hM : Mo = 2 := by omega
  obtain ⟨n4, d4, u4⟩ := u3'.taken hc 0x1F4 dtm_at_ce (by decide) (by rw [v3a1, u3'.zero]; exact m30.mpr h30)
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc dtm_at_1f4 (off' := 0x1F8) (by decide)
  have v5a1 : reg n5 a1 = aluEval .and (BitVec.ofNat 32 Y) 3 := by
    rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u4.regs, K3 _ (by decide), K1 _ (by decide), r18]
  have K5 : ∀ q, q.val ∉ [10, 11, 12, 13] → reg n5 q = reg n q := fun q hq => by
    rw [u5.regs, upd_ne' (by intro h; apply hq; rw [h]; decide) u4.self.zero, u4.regs,
      K3 q (by intro h; apply hq; rw [h]; decide), K1 q hq]
  have v5a0 : reg n5 a0 = BitVec.ofNat 32 s := by
    rw [u5.regs, upd_ne' (by decide) u4.self.zero, u4.regs, K3 _ (by decide), v1a0]
  have hdim : daysInMonth Y Mo = if isLeapYear Y then 29 else 28 := by
    unfold daysInMonth; rw [if_neg h31, if_neg h30, if_pos hM]
  by_cases h4 : Y % 4 = 0
  · obtain ⟨n6, d6, u6⟩ := u5.self.taken hc 0x1FE dtm_at_1f8 (by decide) (by
      rw [v5a1, u5.self.zero, dt_y4 Y hY2]; exact decide_eq_true h4)
    obtain ⟨n7, c7, u7, R7⟩ := dt_blk u6.self hc dtE3_end (by simp only [BlockOk, BInstr.ok, dtE3, and_self])
    have u7' : St Mx DT n7 0x21A (reg n7) := by
      have := u7; rwa [show (runBlock dtE3 (Mx, reg n6)).1 = Mx from rfl] at this
    obtain ⟨n8, d8, u8⟩ := u7'.jump hc dtm_at_21a (off' := 0xD4) (by decide) (by rw [u7'.pc]; decide)
    have K7 : ∀ q, q.val ∉ [10, 11, 12, 13] → reg n7 q = reg n q := fun q hq => by
      have hd : q ∉ dtE3.filterMap BInstr.dst := by
        simp only [dtE3, List.filterMap_cons, List.filterMap_nil, BInstr.dst, Option.some]
        revert hq; revert q; decide
      rw [R7, runBlock_reg _ _ _ q u6.self.zero hd, u6.regs, K5 q hq]
    refine ⟨n8, c1.trans (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (c7.trans (.single d8))))))), u8.self,
      ?_, ?_, fun q hq => by rw [u8.regs, K7 q hq]⟩
    · rw [u8.regs, R7, hdim]
      simp +decide only [runBlock, BInstr.run, dtE3, upd_app, ↓reduceIte]
      rw [u6.regs, K5 _ (by decide), r18, u6.self.zero]
      exact dt_leap Y hY2 h4
    · rw [u8.regs, R7, runBlock_reg _ _ _ _ u6.self.zero (by decide), u6.regs, v5a0]
  · obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc 0x1FA dtm_at_1f8 (by decide) (by
      rw [v5a1, u5.self.zero, dt_y4 Y hY2]; exact decide_eq_false h4)
    obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hc dtm_at_1fa (off' := 0x1FC) (by decide)
    obtain ⟨n8, d8, u8⟩ := u7.self.jump hc dtm_at_1fc (off' := 0xD4) (by decide) (by rw [u7.pc]; decide)
    refine ⟨n8, c1.trans (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.single d8))))))), u8.self,
      ?_, ?_, fun q hq => ?_⟩
    · rw [u8.regs, u7.regs, upd_app]; simp only [↓reduceIte]; rw [u6.self.zero, hdim]
      have : isLeapYear Y = false := by
        unfold isLeapYear; rw [beq_eq_false_iff_ne.mpr h4]; rfl
      rw [this]; rfl
    · rw [u8.regs, u7.regs, upd_ne' (by decide) u6.self.zero, u6.regs, v5a0]
    · rw [u8.regs, u7.regs, upd_ne' (by intro h; apply hq; rw [h]; decide) u6.self.zero, u6.regs, K5 q hq]


/-- The field check `readDateTime` makes. -/
def dtOk (Y Mo D h mi s : Nat) : Bool :=
  Y ≥ 1970 && 1 ≤ Mo && Mo ≤ 12 && 1 ≤ D && D ≤ daysInMonth Y Mo && h ≤ 23 && mi ≤ 59 && s ≤ 59

theorem dtOk_true {Y Mo D h mi s : Nat} : dtOk Y Mo D h mi s = true ↔
    1970 ≤ Y ∧ 1 ≤ Mo ∧ Mo ≤ 12 ∧ 1 ≤ D ∧ D ≤ daysInMonth Y Mo ∧ h ≤ 23 ∧ mi ≤ 59 ∧ s ≤ 59 := by
  unfold dtOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem dim_le (Y Mo : Nat) : daysInMonth Y Mo ≤ 31 := by
  unfold daysInMonth; split
  · exact Nat.le_refl _
  · split
    · decide
    · split
      · split <;> decide
      · decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From 0x9C, with the five fields read: on to 0xEA with the seconds in
`a0` when they pass `readDateTime`'s check, and to the `BadTime` exit at
0x138 when they don't. -/
theorem dt_check {Mx : Word → BitVec 8} {n : Machine} {F : Word} {Y Mo D h mi s : Nat}
    (st : St Mx DT n 0x9C (reg n)) (hc : CodeIn Mx DT dateTimeCode) (hY2 : Y < 2 ^ 32) (hMo : Mo < 100)
    (hD : D < 100) (hh : h < 100) (hmi : mi < 100) (hs : s < 100)
    (r18 : reg n 18 = BitVec.ofNat 32 Y) (r22 : reg n 22 = BitVec.ofNat 32 Mo) (r20 : reg n 20 = BitVec.ofNat 32 D)
    (r19 : reg n 19 = BitVec.ofNat 32 h) (r21 : reg n 21 = BitVec.ofNat 32 mi) (rsp : reg n sp = F)
    (hF : (F + 0xC).toNat % 4 = 0) (ls : memLoad32 Mx (F + 0xC) = BitVec.ofNat 32 s) :
    ∃ n', Steps n n' ∧ (∀ q, q.val ∉ [10, 11, 12, 13] → reg n' q = reg n q) ∧
      ((dtOk Y Mo D h mi s = true ∧ St Mx DT n' 0xEA (reg n') ∧ reg n' a0 = BitVec.ofNat 32 s) ∨
       (dtOk Y Mo D h mi s = false ∧ St Mx DT n' 0x138 (reg n'))) := by
  have hz := st.zero
  have bad : ∀ (P : Prop), ¬ P → (dtOk Y Mo D h mi s = true → P) → dtOk Y Mo D h mi s = false :=
    fun _ hP hi => Bool.eq_false_iff.mpr fun e => hP (hi e)
  obtain ⟨n1, d1, u1⟩ := st.aluImm hc dtm_at_9c (off' := 0xA0) (by decide)
  have K1 : ∀ q, q.val ∉ [10, 11, 12, 13] → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) hz]
  have v1 : reg n1 a0 = BitVec.ofNat 32 1970 := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]; rfl
  by_cases hY : Y < 1970
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x138 dtm_at_a0 (by decide) (by
      rw [K1 _ (by decide), r18, v1, dn_bltu _ _ hY2 (by decide)]; exact decide_eq_true hY)
    exact ⟨n2, .cons d1 (.single d2), fun q hq => by rw [u2.regs, K1 q hq],
      .inr ⟨bad _ (by omega : ¬ 1970 ≤ Y) fun e => (dtOk_true.mp e).1, u2.self⟩⟩
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0xA4 dtm_at_a0 (by decide) (by
    rw [K1 _ (by decide), r18, v1, dn_bltu _ _ hY2 (by decide)]; exact decide_eq_false hY)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc dtm_at_a4 (off' := 0xA8) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc dtm_at_a8 (off' := 0xAA) (by decide)
  have K4 : ∀ q, q.val ∉ [10, 11, 12, 13] → reg n4 q = reg n q := fun q hq => by
    rw [u4.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) u3.self.zero, u3.regs,
      upd_ne' (by intro e; apply hq; rw [e]; decide) u2.self.zero, u2.regs, K1 q hq]
  have v4a0 : reg n4 a0 = BitVec.ofNat 32 ((Mo + 4294967295) % 4294967296) := by
    rw [u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u2.regs, K1 _ (by decide), r22, show (0xFFFFFFFF : Word) = BitVec.ofNat 32 4294967295 from rfl, dn_addN]
  have v4a1 : reg n4 a1 = BitVec.ofNat 32 11 := by
    rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u3.self.zero]; rfl
  by_cases hM : Mo = 0 ∨ 12 < Mo
  · obtain ⟨n5, d5, u5⟩ := u4.self.taken hc 0x138 dtm_at_aa (by decide) (by
      rw [v4a1, v4a0, dn_bltu _ _ (by decide) (Nat.mod_lt _ (by decide))]; exact decide_eq_true (by omega))
    exact ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), fun q hq => by rw [u5.regs, K4 q hq],
      .inr ⟨bad (1 ≤ Mo ∧ Mo ≤ 12) (by omega) fun e => ⟨(dtOk_true.mp e).2.1, (dtOk_true.mp e).2.2.1⟩, u5.self⟩⟩
  obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hc 0xAE dtm_at_aa (by decide) (by
    rw [v4a1, v4a0, dn_bltu _ _ (by decide) (Nat.mod_lt _ (by decide))]; exact decide_eq_false (by omega))
  have e0 : (0 : Word) = BitVec.ofNat 32 0 := rfl
  by_cases hD0 : D = 0
  · obtain ⟨n6, d6, u6⟩ := u5.self.taken hc 0x138 dtm_at_ae (by decide) (by
      rw [u5.regs, K4 _ (by decide), r20, u5.self.zero, hD0]; rfl)
    exact ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))),
      fun q hq => by rw [u6.regs, u5.regs, K4 q hq],
      .inr ⟨bad (1 ≤ D) (by omega) fun e => (dtOk_true.mp e).2.2.2.1, u6.self⟩⟩
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc 0xB2 dtm_at_ae (by decide) (by
    rw [u5.regs, K4 _ (by decide), r20, u5.self.zero, e0]
    simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
    intro e; exact hD0 (by have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega))
  obtain ⟨n7, c7, u7, v7a1, v7a0, K7⟩ := dt_dim (Y := Y) (Mo := Mo) (s := s) (F := F) u6.self hc hY2 (by omega) (by omega)
    (by rw [u6.regs, u5.regs, K4 _ (by decide), r18]) (by rw [u6.regs, u5.regs, K4 _ (by decide), r22])
    (by rw [u6.regs, u5.regs, K4 _ (by decide), rsp]) hF ls
  have K7' : ∀ q, q.val ∉ [10, 11, 12, 13] → reg n7 q = reg n q := fun q hq => by
    rw [K7 q hq, u6.regs, u5.regs, K4 q hq]
  have pre : Steps n n7 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c7)))))
  obtain ⟨n8, d8, u8⟩ := u7.aluImm hc dtm_at_d4 (off' := 0xD8) (by decide)
  have K8 : ∀ q, q.val ∉ [10, 11, 12, 13] → reg n8 q = reg n q := fun q hq => by
    rw [u8.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) u7.zero, K7' q hq]
  have v8a2 : reg n8 a2 = BitVec.ofNat 32 59 := by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u7.zero]; rfl
  have v8a0 : reg n8 a0 = BitVec.ofNat 32 s := by rw [u8.regs, upd_ne' (by decide) u7.zero, v7a0]
  have hdim := dim_le Y Mo
  by_cases hs59 : 59 < s
  · obtain ⟨n9, d9, u9⟩ := u8.self.taken hc 0x138 dtm_at_d8 (by decide) (by
      rw [v8a2, v8a0, dn_bltu _ _ (by decide) (by omega)]; exact decide_eq_true hs59)
    exact ⟨n9, pre.trans (.cons d8 (.single d9)), fun q hq => by rw [u9.regs, K8 q hq],
      .inr ⟨bad (s ≤ 59) (by omega) fun e => (dtOk_true.mp e).2.2.2.2.2.2.2, u9.self⟩⟩
  obtain ⟨n9, d9, u9⟩ := u8.self.notTaken hc 0xDC dtm_at_d8 (by decide) (by
    rw [v8a2, v8a0, dn_bltu _ _ (by decide) (by omega)]; exact decide_eq_false hs59)
  by_cases hm59 : 59 < mi
  · obtain ⟨n10, d10, u10⟩ := u9.self.taken hc 0x138 dtm_at_dc (by decide) (by
      simp only [u9.regs]; rw [v8a2, K8 _ (by decide), r21, dn_bltu _ _ (by decide) (by omega)]; exact decide_eq_true hm59)
    exact ⟨n10, pre.trans (.cons d8 (.cons d9 (.single d10))), fun q hq => by rw [u10.regs, u9.regs, K8 q hq],
      .inr ⟨bad (mi ≤ 59) (by omega) fun e => (dtOk_true.mp e).2.2.2.2.2.2.1, u10.self⟩⟩
  obtain ⟨n10, d10, u10⟩ := u9.self.notTaken hc 0xE0 dtm_at_dc (by decide) (by
    simp only [u9.regs]; rw [v8a2, K8 _ (by decide), r21, dn_bltu _ _ (by decide) (by omega)]; exact decide_eq_false hm59)
  obtain ⟨n11, d11, u11⟩ := u10.self.aluImm hc dtm_at_e0 (off' := 0xE2) (by decide)
  have K11 : ∀ q, q.val ∉ [10, 11, 12, 13] → reg n11 q = reg n q := fun q hq => by
    rw [u11.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) u10.self.zero, u10.regs, u9.regs, K8 q hq]
  have v11a2 : reg n11 a2 = BitVec.ofNat 32 23 := by
    rw [u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u10.self.zero]; rfl
  have v11a1 : reg n11 a1 = BitVec.ofNat 32 (daysInMonth Y Mo) := by
    rw [u11.regs, upd_ne' (by decide) u10.self.zero, u10.regs, u9.regs, u8.regs, upd_ne' (by decide) u7.zero, v7a1]
  have v11a0 : reg n11 a0 = BitVec.ofNat 32 s := by
    rw [u11.regs, upd_ne' (by decide) u10.self.zero, u10.regs, u9.regs, v8a0]
  have pre2 : Steps n n11 := pre.trans (.cons d8 (.cons d9 (.cons d10 (.single d11))))
  by_cases hh23 : 23 < h
  · obtain ⟨n12, d12, u12⟩ := u11.self.taken hc 0x138 dtm_at_e2 (by decide) (by
      rw [v11a2, K11 _ (by decide), r19, dn_bltu _ _ (by decide) (by omega)]; exact decide_eq_true hh23)
    exact ⟨n12, pre2.trans (.single d12), fun q hq => by rw [u12.regs, K11 q hq],
      .inr ⟨bad (h ≤ 23) (by omega) fun e => (dtOk_true.mp e).2.2.2.2.2.1, u12.self⟩⟩
  obtain ⟨n12, d12, u12⟩ := u11.self.notTaken hc 0xE6 dtm_at_e2 (by decide) (by
    rw [v11a2, K11 _ (by decide), r19, dn_bltu _ _ (by decide) (by omega)]; exact decide_eq_false hh23)
  by_cases hdd : daysInMonth Y Mo < D
  · obtain ⟨n13, d13, u13⟩ := u12.self.taken hc 0x138 dtm_at_e6 (by decide) (by
      simp only [u12.regs]; rw [v11a1, K11 _ (by decide), r20, dn_bltu _ _ (by omega) (by omega)]; exact decide_eq_true hdd)
    exact ⟨n13, pre2.trans (.cons d12 (.single d13)), fun q hq => by rw [u13.regs, u12.regs, K11 q hq],
      .inr ⟨bad (D ≤ daysInMonth Y Mo) (by omega) fun e => (dtOk_true.mp e).2.2.2.2.1, u13.self⟩⟩
  obtain ⟨n13, d13, u13⟩ := u12.self.notTaken hc 0xEA dtm_at_e6 (by decide) (by
    simp only [u12.regs]; rw [v11a1, K11 _ (by decide), r20, dn_bltu _ _ (by omega) (by omega)]; exact decide_eq_false hdd)
  refine ⟨n13, pre2.trans (.cons d12 (.single d13)), fun q hq => by rw [u13.regs, u12.regs, K11 q hq],
    .inl ⟨dtOk_true.mpr ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, u13.self,
      by rw [u13.regs, u12.regs, v11a0]⟩⟩


theorem dn_sep1 {a x : Word} (h : Sep a 1 x 1) : x ≠ a := fun e => h 0 (by decide) 0 (by decide) (by
  rw [add_ofNat_zero, add_ofNat_zero, e])

theorem dn_sub2 (k : Nat) (h2 : 2 ≤ k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k + 0xFFFFFFFE = BitVec.ofNat 32 (k - 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFE : Word).toNat = 4294967294 from rfl]
  omega

/-- What one `digits::<2>` call leaves: the bytes outside its result at `D`
and the reader at `d` as they were, and either `BadTime` or the number with
the reader two bytes on. -/
theorem digits2Mem_cases (M : Word → BitVec 8) (D d q : Word) (k : Nat) (hk : k < 2 ^ 32) (sDd : Sep D 8 d 8) :
    (∀ x, Sep D 8 x 1 → Sep d 8 x 1 → digits2Mem M D d q k x = M x) ∧
    ((readDigits 2 (memBytes M q k) = none ∧ digits2Mem M D d q k D = 1 ∧ digits2Mem M D d q k (D + 1) = 0x19) ∨
     (∃ v, readDigits 2 (memBytes M q k) = some (v, memBytes M (q + 2) (k - 2)) ∧ v < 100 ∧
       digits2Mem M D d q k D = 0 ∧ memLoad32 (digits2Mem M D d q k) (D + 4) = BitVec.ofNat 32 v ∧
       memLoad32 (digits2Mem M D d q k) d = q + 2 ∧
       memLoad32 (digits2Mem M D d q k) (d + 4) = BitVec.ofNat 32 (k - 2) ∧ 2 ≤ k)) := by
  have oD : ∀ {c n e l : Nat}, c + n ≤ e ∨ e + l ≤ c → c + n ≤ 8 → e + l ≤ 8 →
      Sep (D + BitVec.ofNat 32 c) n (D + BitVec.ofNat 32 e) l := fun h h1 h2 => sep_offsets D h (by omega) (by omega)
  have od : ∀ {c n e l : Nat}, c + n ≤ e ∨ e + l ≤ c → c + n ≤ 8 → e + l ≤ 8 →
      Sep (d + BitVec.ofNat 32 c) n (d + BitVec.ofNat 32 e) l := fun h h1 h2 => sep_offsets d h (by omega) (by omega)
  have D0 : D = D + BitVec.ofNat 32 0 := (add_ofNat_zero D).symm
  have d0 : d = d + BitVec.ofNat 32 0 := (add_ofNat_zero d).symm
  have D1 : D + 1 = D + BitVec.ofNat 32 1 := rfl
  have D4 : D + 4 = D + BitVec.ofNat 32 4 := rfl
  have d4 : d + 4 = d + BitVec.ofNat 32 4 := rfl
  have s01 : D + 1 ≠ D := by
    have := oD (c := 0) (n := 1) (e := 1) (l := 1) (by omega) (by omega) (by omega); rw [← D0, ← D1] at this
    exact dn_sep1 this
  have fr8 : ∀ {c : Nat} {x : Word}, c < 8 → Sep D 8 x 1 → x ≠ D + BitVec.ofNat 32 c := fun {c x} hc hx =>
    dn_sep1 (hx.sub (c := c) (l := 1) (by omega))
  unfold digits2Mem
  rw [readDigits2_mem]
  by_cases h2 : k < 2
  · rw [if_pos h2, if_pos h2]
    refine ⟨fun x hx _ => ?_, .inl ⟨rfl, memStore8_same _ _ _, by rw [memStore8_ne s01, memStore8_same]⟩⟩
    rw [memStore8_ne (by rw [D0]; exact fr8 (by decide) hx), memStore8_ne (by rw [D1]; exact fr8 (by decide) hx)]
  rw [if_neg h2, if_neg h2]
  cases hdg : digits2Of (M q) (M (q + 1)) with
  | none =>
    dsimp only
    refine ⟨fun x hx hx' => ?_, .inl ⟨rfl, memStore8_same _ _ _, by rw [memStore8_ne s01, memStore8_same]⟩⟩
    rw [memStore8_ne (by rw [D0]; exact fr8 (by decide) hx), memStore8_ne (by rw [D1]; exact fr8 (by decide) hx),
      memStore32_get_sep (by rw [d4]; exact hx'.sub (by decide)),
      memStore32_get_sep (by rw [d0]; exact hx'.sub (by decide))]
  | some v =>
    dsimp only
    have hv : v < 100 := by
      unfold digits2Of at hdg
      split at hdg
      · rename_i h
        cases hdg
        have := td_lt _ h.1; have := td_lt _ h.2; omega
      · cases hdg
    have sDd' : ∀ {c n e l : Nat}, c + n ≤ 8 → e + l ≤ 8 →
        Sep (D + BitVec.ofNat 32 c) n (d + BitVec.ofNat 32 e) l := fun h1 h2 => (sDd.sub h1).subR h2
    refine ⟨fun x hx hx' => ?_, .inr ⟨v, rfl, hv, memStore8_same _ _ _, ?_, ?_, ?_, by omega⟩⟩
    · rw [memStore8_ne (by rw [D0]; exact fr8 (by decide) hx), memStore32_get_sep (by rw [D4]; exact hx.sub (by decide)),
        memStore32_get_sep (by rw [d4]; exact hx'.sub (by decide)),
        memStore32_get_sep (by rw [d0]; exact hx'.sub (by decide))]
    · have e0 := oD (c := 0) (n := 1) (e := 4) (l := 4) (by omega) (by omega) (by omega)
      rw [← D0, ← D4] at e0
      rw [memLoad32_store8_sep e0, memLoad32_store32_same]
    · have e1 := sDd' (c := 0) (n := 1) (e := 0) (l := 4) (by omega) (by omega)
      have e2 := sDd' (c := 4) (n := 4) (e := 0) (l := 4) (by omega) (by omega)
      have e3 := od (c := 4) (n := 4) (e := 0) (l := 4) (by omega) (by omega) (by omega)
      rw [← D0, ← d0] at e1; rw [← D4, ← d0] at e2; rw [← d4, ← d0] at e3
      rw [memLoad32_store8_sep e1, memLoad32_store32_sep e2, memLoad32_store32_sep e3, memLoad32_store32_same]
    · have e1 := sDd' (c := 0) (n := 1) (e := 4) (l := 4) (by omega) (by omega)
      have e2 := sDd' (c := 4) (n := 4) (e := 4) (l := 4) (by omega) (by omega)
      rw [← D0, ← d4] at e1; rw [← D4, ← d4] at e2
      rw [memLoad32_store8_sep e1, memLoad32_store32_sep e2, memLoad32_store32_same, dn_sub2 k (by omega) hk]




abbrev dtmPs : List (Fin 32 × Word) :=
  [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20), ((19 : Fin 32), 0x1C),
   ((20 : Fin 32), 0x18), ((21 : Fin 32), 0x14), ((22 : Fin 32), 0x10)]

def dtA : List BInstr :=
  [.alu .add (9 : Fin 32) x0 a2, .alu .add (18 : Fin 32) x0 a1, .alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 0x8, .alu .add a1 x0 a2]
def dtB1 : List BInstr :=
  [.lw (22 : Fin 32) sp 0xC, .aluImm .add a0 sp 0x8, .alu .add a1 x0 (9 : Fin 32)]
def dtB2 : List BInstr :=
  [.lw (20 : Fin 32) sp 0xC, .aluImm .add a0 sp 0x8, .alu .add a1 x0 (9 : Fin 32)]
def dtB3 : List BInstr :=
  [.lw (19 : Fin 32) sp 0xC, .aluImm .add a0 sp 0x8, .alu .add a1 x0 (9 : Fin 32)]
def dtB4 : List BInstr :=
  [.lw (21 : Fin 32) sp 0xC, .aluImm .add a0 sp 0x8, .alu .add a1 x0 (9 : Fin 32)]
def dtT : List BInstr :=
  [.sb (8 : Fin 32) a0 0x1, .aluImm .add a1 x0 0x1]

section
set_option maxRecDepth 20000
theorem dtA_end : blockEnd dateTimeCode 0x12 dtA = some 0x1C := by decide
theorem dtB1_end : blockEnd dateTimeCode 0x2A dtB1 = some 0x30 := by decide
theorem dtB2_end : blockEnd dateTimeCode 0x3E dtB2 = some 0x44 := by decide
theorem dtB3_end : blockEnd dateTimeCode 0x52 dtB3 = some 0x58 := by decide
theorem dtB4_end : blockEnd dateTimeCode 0x66 dtB4 = some 0x6C := by decide
theorem dtT_end : blockEnd dateTimeCode 0x7E dtT = some 0x84 := by decide
theorem dtmSave_end : blockEnd dateTimeCode 2 (saveBlock dtmPs) = some 0x12 := by decide
theorem dtmRestore_end : blockEnd dateTimeCode 0x88 (restoreBlock dtmPs) = some 0x98 := by decide
end

theorem dt_zext8 : ∀ b : BitVec 8, (b.zeroExtend 32).extractLsb' 0 8 = b := by decide

theorem dn_memBytes_eq {M M' : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M' (p + BitVec.ofNat 32 i)) {c l : Nat} (hl : c + l ≤ n) :
    memBytes M (p + BitVec.ofNat 32 c) l = memBytes M' (p + BitVec.ofNat 32 c) l :=
  (memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact (h _ (by omega)).symm).symm

theorem rdt_ok (Y : Nat) {b0 b1 b2 b3 b4 b5 : Bytes} {v1 v2 v3 v4 v5 : Nat}
    (e1 : readDigits 2 b0 = some (v1, b1)) (e2 : readDigits 2 b1 = some (v2, b2))
    (e3 : readDigits 2 b2 = some (v3, b3)) (e4 : readDigits 2 b3 = some (v4, b4))
    (e5 : readDigits 2 b4 = some (v5, b5)) :
    readDateTime Y b0 = if dtOk Y v1 v2 v3 v4 v5 then
      some (daysFromCivil Y v1 v2 * 86400 + v3 * 3600 + v4 * 60 + v5, b5) else none := by
  unfold readDateTime
  simp only [e1, e2, e3, e4, e5, bind, Option.bind, require]
  cases h : dtOk Y v1 v2 v3 v4 v5 <;> unfold dtOk at h <;> simp only [h, Bool.false_eq_true, ↓reduceIte] <;> rfl

theorem rdt_fail1 (Y : Nat) {b0 : Bytes} (e1 : readDigits 2 b0 = none) : readDateTime Y b0 = none := by
  unfold readDateTime; simp only [e1, bind, Option.bind]
theorem rdt_fail2 (Y : Nat) {b0 b1 : Bytes} {v1 : Nat} (e1 : readDigits 2 b0 = some (v1, b1))
    (e2 : readDigits 2 b1 = none) : readDateTime Y b0 = none := by
  unfold readDateTime; simp only [e1, e2, bind, Option.bind]
theorem rdt_fail3 (Y : Nat) {b0 b1 b2 : Bytes} {v1 v2 : Nat} (e1 : readDigits 2 b0 = some (v1, b1))
    (e2 : readDigits 2 b1 = some (v2, b2)) (e3 : readDigits 2 b2 = none) : readDateTime Y b0 = none := by
  unfold readDateTime; simp only [e1, e2, e3, bind, Option.bind]
theorem rdt_fail4 (Y : Nat) {b0 b1 b2 b3 : Bytes} {v1 v2 v3 : Nat} (e1 : readDigits 2 b0 = some (v1, b1))
    (e2 : readDigits 2 b1 = some (v2, b2)) (e3 : readDigits 2 b2 = some (v3, b3)) (e4 : readDigits 2 b3 = none) :
    readDateTime Y b0 = none := by
  unfold readDateTime; simp only [e1, e2, e3, e4, bind, Option.bind]
theorem rdt_fail5 (Y : Nat) {b0 b1 b2 b3 b4 : Bytes} {v1 v2 v3 v4 : Nat} (e1 : readDigits 2 b0 = some (v1, b1))
    (e2 : readDigits 2 b1 = some (v2, b2)) (e3 : readDigits 2 b2 = some (v3, b3)) (e4 : readDigits 2 b3 = some (v4, b4))
    (e5 : readDigits 2 b4 = none) : readDateTime Y b0 = none := by
  unfold readDateTime; simp only [e1, e2, e3, e4, e5, bind, Option.bind]

theorem dt_days_lt {Y M D : Nat} (hY2 : Y < 2 ^ 32) (hY : 1970 ≤ Y) (hM1 : 1 ≤ M) (hM2 : M ≤ 12) (hD1 : 1 ≤ D)
    (hD : D < 100) : daysFromCivil Y M D < 2 ^ 41 := by
  have h := dt_days Y M D hY hM1 hM2 hD1
  simp only at h
  obtain ⟨y, hy⟩ : ∃ y, Y - (if M < 3 then 1 else 0) = y := ⟨_, rfl⟩
  obtain ⟨mp, hmp⟩ : ∃ mp, (if M < 3 then M + 9 else M - 3) = mp := ⟨_, rfl⟩
  have hy2 : y < 4294967296 := by rw [← hy]; split <;> omega
  have hmp2 : mp ≤ 11 := by rw [← hmp]; split <;> omega
  rw [hy, hmp] at h
  have e1 : y / 400 ≤ 10737418 := by omega
  have e2 : y / 400 * 146097 ≤ 10737418 * 146097 := Nat.mul_le_mul_right _ e1
  have e3 : y % 400 * 365 + y % 400 / 4 - y % 400 / 100 ≤ 399 * 365 + 99 := by omega
  have e4 : (153 * mp + 2) / 5 + D - 1 ≤ 437 := by omega
  have e5 : daysFromCivil Y M D + 719468 ≤ 10737418 * 146097 + (399 * 365 + 99) + 437 := by
    rw [h]; exact Nat.add_le_add (Nat.add_le_add e2 e3) e4
  exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ 719468) e5) (by decide)

theorem dt_t_lt {Y M D h mi s : Nat} (hY2 : Y < 2 ^ 32) (hY : 1970 ≤ Y) (hM1 : 1 ≤ M) (hM2 : M ≤ 12) (hD1 : 1 ≤ D)
    (hD : D < 100) (hh : h ≤ 23) (hmi : mi ≤ 59) (hs : s ≤ 59) :
    daysFromCivil Y M D * 86400 + h * 3600 + mi * 60 + s < 2 ^ 64 := by
  have h2 : h * 3600 + mi * 60 + s ≤ 86399 := by omega
  have hb := dt_days_lt hY2 hY hM1 hM2 hD1 hD
  have h1 : daysFromCivil Y M D * 86400 ≤ 2 ^ 41 * 86400 := Nat.mul_le_mul_right _ (Nat.le_of_lt hb)
  calc daysFromCivil Y M D * 86400 + h * 3600 + mi * 60 + s
      = daysFromCivil Y M D * 86400 + (h * 3600 + mi * 60 + s) := by simp only [Nat.add_assoc]
    _ ≤ 2 ^ 41 * 86400 + 86399 := Nat.add_le_add h1 h2
    _ < 2 ^ 64 := by decide

theorem dn_code_hi {b : Word} {l i : Nat} (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) (hi : i < l) :
    0x40000000 ≤ (b + BitVec.ofNat 32 i).toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `time::date_time`**: with the year in `a1` and a reader
at `d` over the `n` bytes at `p`, it writes `readDateTime`'s answer to the
`Result<u64, Error>` at `out`. When `readDateTime` reads a time `t`, the tag
is 0, `t` is at `out + 8` as two words, and the reader is 10 bytes on; when
it fails, the tag is 1 and the error is `BadTime` (0x19). It returns with
`sp` and the callee-saved registers restored and writes only `out`, the
reader, and the 0x30 bytes of stack below `sp`. -/
theorem dateTime_correct (m : Machine) {sp0 out d p Y retAddr : Word} {n : Nat}
    (hc0 : CodeIn m.mem DT dateTimeCode) (hcT : CodeIn m.mem TD timeDigits2Code)
    (hpc : m.pc = DT) (ha0 : reg m a0 = out) (ha1 : reg m a1 = Y) (ha2 : reg m a2 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0x30 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (how : out.toNat + 16 ≤ 0x40000000) (hoa : out.toNat % 4 = 0)
    (hdw : d.toNat + 8 ≤ 0x40000000) (hda : d.toNat % 4 = 0)
    (hn : n < 2 ^ 32) (lp : memLoad32 m.mem d = p) (ln : memLoad32 m.mem (d + 4) = BitVec.ofNat 32 n)
    (sOG : Sep out 16 (sp0 + 0xFFFFFFD0) 0x30) (sDG : Sep d 8 (sp0 + 0xFFFFFFD0) 0x30) (sOD : Sep out 16 d 8)
    (sPG : Sep p n (sp0 + 0xFFFFFFD0) 0x30) (sPD : Sep p n d 8) (sDP : Sep d 8 p 10) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ t rest, readDateTime Y.toNat (memBytes m.mem p n) = some (t, rest) →
        t < 2 ^ 64 ∧ m'.mem out = 0 ∧ memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
        memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧ rest = memBytes m.mem (p + 10) (n - 10) ∧
        memLoad32 m'.mem d = p + 10 ∧ memLoad32 m'.mem (d + 4) = BitVec.ofNat 32 (n - 10)) ∧
      (readDateTime Y.toNat (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFD0) 0x30 x 1 → Sep out 16 x 1 → Sep d 8 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFD0 = F := ⟨_, rfl⟩
  rw [hF] at sOG sDG sPG ⊢
  have hFn : F.toNat = sp0.toNat - 0x30 := by
    rw [← hF, BitVec.toNat_add, show (0xFFFFFFD0 : Word).toNat = 2 ^ 32 - 0x30 from rfl]; have := sp0.isLt; omega
  have hFc : ∀ c, c ≤ 0x30 → (F + BitVec.ofNat 32 c).toNat = F.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFa : F.toNat % 4 = 0 := by omega
  have eFS : F + 0x30 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have offs : ∀ {c n e k : Nat}, c + n ≤ e ∨ e + k ≤ c → c + n ≤ 0x30 → e + k ≤ 0x30 →
      Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 e) k := fun h h1 h2 => sep_offsets F h (by omega) (by omega)
  have inF : ∀ {c l : Nat} {x : Word}, Sep F 0x30 x 1 → c + l ≤ 0x30 → Sep (F + BitVec.ofNat 32 c) l x 1 :=
    fun hx h => (hx.symm.subR h).symm
  have hiF : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep F 0x30 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hiD : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep d 8 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hiO : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep out 16 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by
      rw [hM _ (hiF _ (dn_code_hi h1 h2 hi')) (hiD _ (dn_code_hi h1 h2 hi'))]; exact hc i hi'
  have hDTn : DT.toNat = (img% dateTimeAddress) := by decide
  have hTDn : TD.toNat = (img% timeDigits2Address) := by decide
  have cdDT : ∀ {M' : Word → BitVec 8}, (∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → M' x = m.mem x) →
      CodeIn M' DT dateTimeCode := fun hM => cd hc0 (by rw [hDTn]; decide) (by rw [hDTn]; decide) hM
  have cdTD : ∀ {M' : Word → BitVec 8}, (∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → M' x = m.mem x) →
      CodeIn M' TD timeDigits2Code := fun hM => cd hcT (by rw [hTDn]; decide) (by rw [hTDn]; decide) hM
  have hiC : ∀ {c l : Nat} {a : Word} {len : Nat}, c + l ≤ 0x30 → 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (F + BitVec.ofNat 32 c) l a len := fun h h1 h2 => sep_of_le (by rw [hFc _ (by omega)]; omega) h2
  have st0 : St m.mem DT m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc0 dtm_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = F := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hF
  have slotO : ∀ o : Word, F + o = F + BitVec.ofNat 32 o.toNat := fun o => by rw [ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0x2C → Sep (F + o) 4 DT dateTimeCode.length := fun o ho => by
    rw [slotO]; exact hiC (by omega) (by rw [hDTn]; decide) (by rw [hDTn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock dtmPs) u1 hc0 dtmSave_end (saveBlock_ok _ dtmPs _ fun q hq => by
      rw [sp1]
      simp only [dtmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hFa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) dtmPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep F 0x30 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside dtmPs fun q hq => by
      simp only [dtmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [slotO]; exact inF hx (by decide))
  have slots : ∀ r o, (r, o) ∈ dtmPs → memLoad32 Ms (F + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [dtmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot dtmPs _ hm (by
      simp only [dtmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> decide), upd_ne (by
        simp only [dtmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ <;> decide) hr]
  have IMs' : ∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → Ms x = m.mem x := fun x hx _ => IMs x hx
  have hc2 : CodeIn Ms DT dateTimeCode := cdDT IMs'
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block dtA u2.self hc2 dtA_end (by simp only [BlockOk, BInstr.ok, dtA, and_self])
  have R3 : ∀ q, reg m3 q = (runBlock dtA (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms DT m3 0x1C (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have v3 : reg m3 9 = d ∧ reg m3 18 = Y ∧ reg m3 8 = out ∧ reg m3 a0 = F + 8 ∧ reg m3 a1 = d ∧ reg m3 sp = F := by
    simp +decide only [R3, runBlock, BInstr.run, dtA, upd_app, ↓reduceIte]
    rw [r2 a2 (by decide), r2 a1 (by decide), r2 a0 (by decide), ha2, ha1, ha0, sp2, u2.self.zero]
    simp only [ev_add, zw, and_self]
  obtain ⟨v39, v318, v38, v3a0, v3a1, v3sp⟩ := v3
  have K3 : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m3 q = reg m q := fun q hq => by
    have hd : q ∉ dtA.filterMap BInstr.dst := by
      simp only [dtA, List.filterMap_cons, List.filterMap_nil, BInstr.dst, Option.some]
      revert hq; revert q; decide
    rw [R3, runBlock_reg _ _ _ q u2.self.zero hd, r2 q (by revert hq; revert q; decide)]
  -- facts about the result buffer of `digits::<2>`, at `F + 8`
  have hD8 : (F + 8).toNat = F.toNat + 8 := hFc 8 (by decide)
  have hD8a : (F + 8).toNat % 4 = 0 := by omega
  have sD8d : Sep (F + 8) 8 d 8 := (sDG.symm.sub (c := 8) (l := 8) (by decide))
  have sD8T : Sep (F + 8) 8 TD timeDigits2Code.length := hiC (by decide) (by rw [hTDn]; decide) (by rw [hTDn]; decide)
  have sdT : Sep d 8 TD timeDigits2Code.length := sep_of_le (by rw [hTDn]; omega) (by rw [hTDn]; decide)
  have hPm : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → Mx x = m.mem x) →
      ∀ i, i < n → Mx (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) := fun hM i hi =>
    hM _ (sPG.symm.subR (c := i) (l := 1) (by omega)) (sPD.symm.subR (c := i) (l := 1) (by omega))
  -- one call to `digits::<2>`, reading the bytes at `p + j`, and the load of its tag
  have dig : ∀ {Mx : Word → BitVec 8} {nn : Machine} {c j : Nat} {imm o : Word},
      St Mx DT nn c (reg nn) → fetchRel dateTimeCode c = some (.auipc ra imm, 4) →
      fetchRel dateTimeCode (c + 4) = some (.jalr ra ra o, 4) → DT + BitVec.ofNat 32 c + imm + o = TD →
      (DT + BitVec.ofNat 32 (c + 8)).toNat % 2 = 0 →
      fetchRel dateTimeCode (c + 8) = some (.load .lbu a0 sp 0x8, 4) → j ≤ 8 → j ≤ n →
      (∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → Mx x = m.mem x) →
      (∀ c', 0x10 ≤ c' → c' < 0x30 → Mx (F + BitVec.ofNat 32 c') = Ms (F + BitVec.ofNat 32 c')) →
      memLoad32 Mx d = p + BitVec.ofNat 32 j → memLoad32 Mx (d + 4) = BitVec.ofNat 32 (n - j) →
      reg nn sp = F → reg nn a0 = F + 8 → reg nn a1 = d →
      ∃ nn' Mx', Steps nn nn' ∧ St Mx' DT nn' (c + 0xC) (reg nn') ∧
        (∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → Mx' x = m.mem x) ∧
        (∀ c', 0x10 ≤ c' → c' < 0x30 → Mx' (F + BitVec.ofNat 32 c') = Ms (F + BitVec.ofNat 32 c')) ∧
        (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' q = reg nn q) ∧
        ((readDigits 2 (memBytes m.mem (p + BitVec.ofNat 32 j) (n - j)) = none ∧ reg nn' a0 = 1 ∧
            Mx' (F + 9) = 0x19) ∨
         (∃ v, readDigits 2 (memBytes m.mem (p + BitVec.ofNat 32 j) (n - j)) =
            some (v, memBytes m.mem (p + BitVec.ofNat 32 (j + 2)) (n - (j + 2))) ∧ v < 100 ∧ reg nn' a0 = 0 ∧
          memLoad32 Mx' (F + 0xC) = BitVec.ofNat 32 v ∧ memLoad32 Mx' d = p + BitVec.ofNat 32 (j + 2) ∧
          memLoad32 Mx' (d + 4) = BitVec.ofNat 32 (n - (j + 2)) ∧ j + 2 ≤ n)) := by
    intro Mx nn c j imm o st h1 h2 hb hev h3 hj8 hjn hI hS lq lk rsp ra0 ra1
    have hcx := cdDT hI
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa hcx h1 h2 hb (by decide)
    have r1 := PEnv.reg1 regs1 st.zero
    obtain ⟨n2, c2, pc2, mem2, k2⟩ := timeDigits2_correct n1 (base := TD) (retAddr := DT + BitVec.ofNat 32 (c + 8))
      (out := F + 8) (d := d) (p := p + BitVec.ofNat 32 j) (n := n - j) (by decide)
      (by rw [mem1]; exact cdTD hI) pc1 (by rw [r1 a0 (by decide), ra0]) (by rw [r1 a1 (by decide), ra1]) hda hD8a
      (by omega) (by rw [mem1, lq]) (by rw [mem1, lk]) sD8T sdT (sDP.subR (c := j) (l := 2) (by omega))
      (by rw [regs1]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ hev)
    rw [mem1] at mem2
    obtain ⟨frm, cs⟩ := digits2Mem_cases Mx (F + 8) d (p + BitVec.ofNat 32 j) (n - j) (by omega) sD8d
    rw [← mem2] at frm cs
    have I2 : ∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → n2.mem x = m.mem x := fun x hx hx' => by
      rw [frm x (inF hx (by decide)) hx', hI x hx hx']
    have hcx2 := cdDT I2
    have u2 : St n2.mem DT n2 (c + 8) (reg n2) := ⟨by rw [pc2], rfl, fun _ => rfl⟩
    obtain ⟨n3, d3, u3⟩ := u2.lbu hcx2 h3 (off' := c + 0xC) (ofNat_add_ofNat (c + 8) 4)
    have sp2' : reg n2 sp = F := by rw [k2 sp (by decide), r1 sp (by decide), rsp]
    have a03 : reg n3 a0 = (n2.mem (F + 8)).zeroExtend 32 := by
      rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2']
    have K3' : ∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg nn q :=
      fun q hq => by
        rw [u3.regs, upd_ne' (by revert hq; revert q; decide) u2.zero, k2 q (by revert hq; revert q; decide),
          r1 q (by revert hq; revert q; decide)]
    have hmb : memBytes Mx (p + BitVec.ofNat 32 j) (n - j) = memBytes m.mem (p + BitVec.ofNat 32 j) (n - j) :=
      dn_memBytes_eq (hPm hI) (by omega)
    have S' : ∀ c', 0x10 ≤ c' → c' < 0x30 → n2.mem (F + BitVec.ofNat 32 c') = Ms (F + BitVec.ofNat 32 c') :=
      fun c' h1 h2 => by
        rw [frm _ (by rw [show F + 8 = F + BitVec.ofNat 32 8 from rfl]; exact offs (by omega) (by omega) (by omega))
          (sDG.subR (c := c') (l := 1) (by omega)), hS c' h1 h2]
    have pre : Steps nn n3 := c1.trans (c2.trans (.single d3))
    rcases cs with ⟨hr, h8, h9⟩ | ⟨v, hr, hv, h8, h12, hd0, hd4, h2⟩
    · refine ⟨n3, n2.mem, pre, u3.self, I2, S', K3', .inl ⟨by rw [← hmb]; exact hr, by rw [a03, h8]; rfl, ?_⟩⟩
      rw [show F + 9 = F + 8 + 1 by rw [BitVec.add_assoc]; rfl]; exact h9
    · have hq2 : p + BitVec.ofNat 32 j + 2 = p + BitVec.ofNat 32 (j + 2) := add_ofNat_assoc p j 2
      have hmb2 : memBytes Mx (p + BitVec.ofNat 32 (j + 2)) (n - (j + 2)) =
          memBytes m.mem (p + BitVec.ofNat 32 (j + 2)) (n - (j + 2)) := dn_memBytes_eq (hPm hI) (by omega)
      have e2 : n - j - 2 = n - (j + 2) := by omega
      rw [hq2, e2] at hr; rw [hq2] at hd0; rw [e2] at hd4
      refine ⟨n3, n2.mem, pre, u3.self, I2, S', K3', .inr ⟨v, by rw [← hmb, hr, hmb2], hv, by rw [a03, h8]; rfl,
        ?_, hd0, hd4, by omega⟩⟩
      rw [show F + 0xC = F + 8 + 4 by rw [BitVec.add_assoc]; rfl]; exact h12
  -- the exit, from 0x84: store the tag in `a1`, restore the registers, and return
  have hpsp : ∀ p ∈ dtmPs, p.1 ≠ sp := by decide
  have sOC : ∀ {c l : Nat}, c + l ≤ 16 → Sep (out + BitVec.ofNat 32 c) l DT dateTimeCode.length := fun {c l} h => by
    have e : (out + BitVec.ofNat 32 c).toNat = out.toNat + c := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact sep_of_le (by rw [e, hDTn]; omega) (by rw [hDTn]; decide)
  have tail84 : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, St Mt DT nn 0x84 (reg nn) →
      CodeIn Mt DT dateTimeCode → reg nn sp = F → reg nn 8 = out → reg nn a1 = v →
      (∀ c', 0x10 ≤ c' → c' < 0x30 → Mt (F + BitVec.ofNat 32 c') = Ms (F + BitVec.ofNat 32 c')) →
      (∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      ∃ nn', Steps nn nn' ∧ nn'.pc = retAddr ∧ reg nn' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' q = reg m q) ∧
        nn'.mem = memStore8 Mt out (v.extractLsb' 0 8) := by
    intro Mt nn v st hct rsp r8 ra1 hsl' hK
    obtain ⟨n1, d1, u1⟩ := st.sb hct dtm_at_84 (off' := 0x88) (by decide)
    rw [r8, add_lit_zero, ra1] at u1
    have hct1 : CodeIn (memStore8 Mt out (v.extractLsb' 0 8)) DT dateTimeCode := by
      have := sOC (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact hct.store8 this
    have slotT : ∀ o : Word, 0x10 ≤ o.toNat → o.toNat + 4 ≤ 0x30 →
        memLoad32 (memStore8 Mt out (v.extractLsb' 0 8)) (F + o) = memLoad32 Ms (F + o) := fun o h1 h2 => by
      rw [slotO]; apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, memStore8_ne (by
        have := sOG.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this
        exact dn_sep1 (this.subR (c := o.toNat + j) (l := 1) (by omega))), hsl' _ (by omega) (by omega)]
    obtain ⟨n2, c2', u2'⟩ := St.block (restoreBlock dtmPs) u1 hct1 dtmRestore_end
      (restoreBlock_ok (memStore8 Mt out (v.extractLsb' 0 8)) F dtmPs (reg nn) rsp hpsp fun q hq => by
        simp only [dtmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run (memStore8 Mt out (v.extractLsb' 0 8)) F dtmPs (reg nn) rsp hpsp] at u2'
    have rsp' : restoreRegs (memStore8 Mt out (v.extractLsb' 0 8)) F (reg nn) dtmPs sp = F := by
      rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    obtain ⟨n3, d3, u3⟩ := u2'.aluImm hct1 dtm_at_98 (off' := 0x9A) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hct1 dtm_at_9a
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs (memStore8 Mt out (v.extractLsb' 0 8)) F f ps q = f q := by
      intro f ps q hq0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
    have hslot : ∀ r o, (r, o) ∈ dtmPs → reg n4 r = reg m r := fun r o hm => by
      rw [regs4]
      simp only [dtmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
        rw [slotT _ (by decide) (by decide)]; exact slots _ _ (by decide)
    refine ⟨n4, .cons d1 (c2'.trans (.cons d3 (.single d4))), ?_, ?_, fun q hq => ?_, ?_⟩
    · rw [pc4, ← regs4, hslot ra 0x2C (by decide), hra, add_lit_zero, hret]
    · rw [regs4]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [rsp', eFS]
    · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q.val ∈ [3, 4, 23, 24, 25, 26, 27]) q hq with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hL
      · exact hslot _ 0x2C (by decide)
      · exact hslot _ 0x28 (by decide)
      · exact hslot _ 0x24 (by decide)
      · exact hslot _ 0x20 (by decide)
      · exact hslot _ 0x1C (by decide)
      · exact hslot _ 0x18 (by decide)
      · exact hslot _ 0x14 (by decide)
      · exact hslot _ 0x10 (by decide)
      · obtain ⟨hv, hs, hps⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ dtmPs, p.1 ≠ q) := by revert hL; revert q; decide
        rw [regs4, upd_ne hv hs, rr _ _ q hv hps, hK q hL]
    · rw [mem4]
  -- the error exit, from 0x7E with the error code in `a0`
  have tail7E : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, St Mt DT nn 0x7E (reg nn) →
      CodeIn Mt DT dateTimeCode → reg nn sp = F → reg nn 8 = out → reg nn a0 = v →
      (∀ c', 0x10 ≤ c' → c' < 0x30 → Mt (F + BitVec.ofNat 32 c') = Ms (F + BitVec.ofNat 32 c')) →
      (∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      ∃ nn', Steps nn nn' ∧ nn'.pc = retAddr ∧ reg nn' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' q = reg m q) ∧
        nn'.mem = memStore8 (memStore8 Mt (out + 1) (v.extractLsb' 0 8)) out 1 := by
    intro Mt nn v st hct rsp r8 ra0 hsl' hK
    obtain ⟨n1, c1, u1⟩ := St.block dtT st hct dtT_end (by
      simp +decide only [BlockOk, BInstr.ok, dtT, and_true, true_and]; rw [r8]; exact sOC (c := 1) (l := 1) (by decide))
    have R1 : ∀ q, reg n1 q = (runBlock dtT (Mt, reg nn)).2 q := u1.regs
    have eM : (runBlock dtT (Mt, reg nn)).1 = memStore8 Mt (out + 1) (v.extractLsb' 0 8) := by
      simp +decide only [runBlock, BInstr.run, dtT]; rw [r8, ra0]
    rw [eM] at u1
    have so1 : Sep (out + 1) 1 DT dateTimeCode.length := sOC (c := 1) (l := 1) (by decide)
    have u1' : St (memStore8 Mt (out + 1) (v.extractLsb' 0 8)) DT n1 0x84 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
    obtain ⟨n2, c2, pc2, sp2, K2, mem2⟩ := tail84 (v := 1) u1' (hct.store8 so1)
      (by rw [R1]; simp +decide only [runBlock, BInstr.run, dtT, upd_app, ↓reduceIte]; exact rsp)
      (by rw [R1]; simp +decide only [runBlock, BInstr.run, dtT, upd_app, ↓reduceIte]; exact r8)
      (by rw [R1]; simp +decide only [runBlock, BInstr.run, dtT, upd_app, ↓reduceIte]; rw [st.zero]; rfl)
      (fun c' h1 h2 => by
        have hne : F + BitVec.ofNat 32 c' ≠ out + 1 := by
          have := sOG.sub (c := 1) (l := 1) (by decide)
          exact dn_sep1 (this.subR (c := c') (l := 1) (by omega))
        rw [memStore8_ne hne, hsl' c' h1 h2])
      (fun q hq => by
        have hd : q ∉ dtT.filterMap BInstr.dst := by
          simp only [dtT, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
          revert hq; revert q; decide
        rw [R1, runBlock_reg _ _ _ q st.zero hd, hK q hq])
    exact ⟨n2, c1.trans c2, pc2, sp2, K2, by rw [mem2]; rfl⟩
  have o01 : out + 1 ≠ out := by
    have := sep_offsets out (c := 0) (n := 1) (d := 1) (k := 1) (by omega) (by omega) (by omega)
    rw [add_ofNat_zero] at this; exact dn_sep1 this
  have xo0 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out := fun hx => by
    have := hx.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact dn_sep1 this
  have xo1 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out + 1 := fun hx => dn_sep1 (hx.sub (c := 1) (l := 1) (by decide))
  -- the end with `BadTime`, from 0x7E with the code in `a0`
  have finE : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, Steps m nn → St Mt DT nn 0x7E (reg nn) →
      (∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → Mt x = m.mem x) →
      (∀ c', 0x10 ≤ c' → c' < 0x30 → Mt (F + BitVec.ofNat 32 c') = Ms (F + BitVec.ofNat 32 c')) →
      reg nn sp = F → reg nn 8 = out → reg nn a0 = v → v.extractLsb' 0 8 = 0x19 →
      (∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      readDateTime Y.toNat (memBytes m.mem p n) = none →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t rest, readDateTime Y.toNat (memBytes m.mem p n) = some (t, rest) →
          t < 2 ^ 64 ∧ m'.mem out = 0 ∧ memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧ rest = memBytes m.mem (p + 10) (n - 10) ∧
          memLoad32 m'.mem d = p + 10 ∧ memLoad32 m'.mem (d + 4) = BitVec.ofNat 32 (n - 10)) ∧
        (readDateTime Y.toNat (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
        ∀ x, Sep F 0x30 x 1 → Sep out 16 x 1 → Sep d 8 x 1 → m'.mem x = m.mem x := by
    intro Mt nn v pre st hI hS rsp r8 ra0 hv hK hspec
    obtain ⟨n2, c2, pc2, sp2, K2, mem2⟩ := tail7E st (cdDT hI) rsp r8 ra0 hS hK
    rw [hv] at mem2
    have hE : ∀ t rest, readDateTime Y.toNat (memBytes m.mem p n) = some (t, rest) → False := fun t rest h => by
      rw [hspec] at h; cases h
    refine ⟨n2, pre.trans c2, pc2, sp2, K2, fun t rest h => (hE t rest h).elim, fun _ => ⟨?_, ?_⟩,
      fun x hx hx1 hx2 => ?_⟩
    · rw [mem2, memStore8_same]
    · rw [mem2, memStore8_ne o01, memStore8_same]
    · rw [mem2, memStore8_ne (xo0 hx1), memStore8_ne (xo1 hx1), hI x hx hx2]
  -- `digits::<2>` failed: its code, at `F + 9`, goes out
  have finErr : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt DT nn 0x7A (reg nn) →
      (∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → Mt x = m.mem x) →
      (∀ c', 0x10 ≤ c' → c' < 0x30 → Mt (F + BitVec.ofNat 32 c') = Ms (F + BitVec.ofNat 32 c')) →
      Mt (F + 9) = 0x19 → reg nn sp = F → reg nn 8 = out →
      (∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      readDateTime Y.toNat (memBytes m.mem p n) = none →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t rest, readDateTime Y.toNat (memBytes m.mem p n) = some (t, rest) →
          t < 2 ^ 64 ∧ m'.mem out = 0 ∧ memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧ rest = memBytes m.mem (p + 10) (n - 10) ∧
          memLoad32 m'.mem d = p + 10 ∧ memLoad32 m'.mem (d + 4) = BitVec.ofNat 32 (n - 10)) ∧
        (readDateTime Y.toNat (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
        ∀ x, Sep F 0x30 x 1 → Sep out 16 x 1 → Sep d 8 x 1 → m'.mem x = m.mem x := by
    intro Mt nn pre st hI hS h9 rsp r8 hK hspec
    obtain ⟨n1, d1, u1⟩ := st.lbu (cdDT hI) dtm_at_7a (off' := 0x7E) (by decide)
    refine finE (v := (Mt (F + 9)).zeroExtend 32) (pre.trans (.single d1)) u1.self hI hS
      (by rw [u1.regs, upd_ne' (by decide) st.zero, rsp])
      (by rw [u1.regs, upd_ne' (by decide) st.zero, r8])
      (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp])
      (by rw [h9]; exact dt_zext8 _)
      (fun q hq => by rw [u1.regs, upd_ne' (by revert hq; revert q; decide) st.zero, hK q hq]) hspec
  -- a field failed the check: `BadTime`
  have finBad : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt DT nn 0x138 (reg nn) →
      (∀ x, Sep F 0x30 x 1 → Sep d 8 x 1 → Mt x = m.mem x) →
      (∀ c', 0x10 ≤ c' → c' < 0x30 → Mt (F + BitVec.ofNat 32 c') = Ms (F + BitVec.ofNat 32 c')) →
      reg nn sp = F → reg nn 8 = out →
      (∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      readDateTime Y.toNat (memBytes m.mem p n) = none →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t rest, readDateTime Y.toNat (memBytes m.mem p n) = some (t, rest) →
          t < 2 ^ 64 ∧ m'.mem out = 0 ∧ memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧ rest = memBytes m.mem (p + 10) (n - 10) ∧
          memLoad32 m'.mem d = p + 10 ∧ memLoad32 m'.mem (d + 4) = BitVec.ofNat 32 (n - 10)) ∧
        (readDateTime Y.toNat (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
        ∀ x, Sep F 0x30 x 1 → Sep out 16 x 1 → Sep d 8 x 1 → m'.mem x = m.mem x := by
    intro Mt nn pre st hI hS rsp r8 hK hspec
    obtain ⟨n1, d1, u1⟩ := st.aluImm (cdDT hI) dtm_at_138 (off' := 0x13A) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.jump (cdDT hI) dtm_at_13a (off' := 0x7E) (by decide) (by rw [u1.pc]; decide)
    refine finE (v := 0x19) (pre.trans (.cons d1 (.single d2))) u2.self hI hS
      (by rw [u2.regs, u1.regs, upd_ne' (by decide) st.zero, rsp])
      (by rw [u2.regs, u1.regs, upd_ne' (by decide) st.zero, r8])
      (by rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl) (by decide)
      (fun q hq => by rw [u2.regs, u1.regs, upd_ne' (by revert hq; revert q; decide) st.zero, hK q hq]) hspec
  -- the reader as `date_time` finds it
  have lq0 : memLoad32 Ms d = p + BitVec.ofNat 32 0 := by
    rw [add_ofNat_zero, ← lp]
    exact memLoad32_congr fun j hj => IMs _ ((sDG.sub (c := j) (l := 1) (by omega)).symm)
  have lk0 : memLoad32 Ms (d + 4) = BitVec.ofNat 32 (n - 0) := by
    rw [Nat.sub_zero, ← ln]
    exact memLoad32_congr fun j hj => by
      rw [show d + 4 + BitVec.ofNat 32 j = d + BitVec.ofNat 32 (4 + j) by
        rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
      exact IMs _ ((sDG.sub (c := 4 + j) (l := 1) (by omega)).symm)
  have hFC : (F + 0xC).toNat % 4 = 0 := by rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, hFc _ (by decide)]; omega
  have kk0 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg m3 q = reg m q := fun q hq =>
    K3 q (by revert hq; revert q; decide)
  have pre0 : Steps m m3 := .cons d1 (c2.trans c3)
  -- call 1: the bytes at `p + 0`
  obtain ⟨q1, M1, cq1, uq1, Iq1, Sq1, Kq1, rr1⟩ := dig (j := 0) u3' dtm_at_1c dtm_at_20 (by decide)
    (by decide) dtm_at_24 (by decide) (by omega) IMs' (fun _ _ _ => rfl) lq0 lk0 v3sp v3a0 v3a1
  have preq1 : Steps m q1 := pre0.trans cq1
  have spq1 : reg q1 sp = F := by rw [Kq1 sp (by decide), v3sp]
  have r8q1 : reg q1 8 = out := by rw [Kq1 8 (by decide), v38]
  have r9q1 : reg q1 9 = d := by rw [Kq1 9 (by decide), v39]
  have kkq1 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg q1 q = reg m q := fun q hq => by
    rw [Kq1 q (by revert hq; revert q; decide), kk0 q hq]
  rcases rr1 with ⟨hr, ha0q, h9q⟩ | ⟨v1, hr1, hv1, ha0q1, hm1, hd1, hk1, hj1⟩
  · obtain ⟨ne, de, ue⟩ := uq1.taken (cdDT Iq1) 0x7A dtm_at_28 (by decide) (by rw [ha0q, uq1.zero]; decide)
    exact finErr (preq1.trans (.single de)) ue.self Iq1 Sq1 h9q (by rw [ue.regs, spq1]) (by rw [ue.regs, r8q1])
      (fun q hq => by rw [ue.regs, kkq1 q hq]) (rdt_fail1 _ (by rw [add_ofNat_zero, Nat.sub_zero] at hr; exact hr))
  rw [add_ofNat_zero, Nat.sub_zero] at hr1
  obtain ⟨nb1, db1, ub1⟩ := uq1.notTaken (cdDT Iq1) 0x2A dtm_at_28 (by decide) (by
    rw [ha0q1, uq1.zero]; decide)
  obtain ⟨b1, cb1, ubb1⟩ := St.block dtB1 ub1.self (cdDT Iq1) dtB1_end (by
    simp +decide only [BlockOk, BInstr.ok, dtB1, and_true, true_and]; rw [ub1.regs, spq1]; exact hFC)
  have Rb1 : ∀ q, reg b1 q = (runBlock dtB1 (M1, reg nb1)).2 q := ubb1.regs
  have ub1' : St M1 DT b1 0x30 (reg b1) := ⟨ubb1.pc, by rw [ubb1.mem]; rfl, fun _ => rfl⟩
  have vb1 : reg b1 22 = BitVec.ofNat 32 v1 ∧ reg b1 a0 = F + 8 ∧ reg b1 a1 = d := by
    simp +decide only [Rb1, runBlock, BInstr.run, dtB1, upd_app, ↓reduceIte]
    simp only [ub1.regs]; rw [spq1, hm1, r9q1]; simp only [ev_add, zw, and_self]
  have Kb1 : ∀ q, q.val ∉ [10, 11, 22] → reg b1 q = reg q1 q := fun q hq => by
    have hd' : q ∉ dtB1.filterMap BInstr.dst := by
      simp only [dtB1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [Rb1, runBlock_reg _ _ _ q ub1.self.zero hd', ub1.regs]
  have spb1 : reg b1 sp = F := by rw [Kb1 sp (by decide), spq1]
  have r8b1 : reg b1 8 = out := by rw [Kb1 8 (by decide), r8q1]
  have r9b1 : reg b1 9 = d := by rw [Kb1 9 (by decide), r9q1]
  have kkb1 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg b1 q = reg m q := fun q hq => by
    rw [Kb1 q (by revert hq; revert q; decide), kkq1 q hq]
  have preb1 : Steps m b1 := preq1.trans (.cons db1 cb1)
  -- call 2: the bytes at `p + 2`
  obtain ⟨q2, M2, cq2, uq2, Iq2, Sq2, Kq2, rr2⟩ := dig (j := 2) ub1' dtm_at_30 dtm_at_34 (by decide)
    (by decide) dtm_at_38 (by decide) (by omega) Iq1 Sq1 hd1 hk1 spb1 vb1.2.1 vb1.2.2
  have preq2 : Steps m q2 := preb1.trans cq2
  have spq2 : reg q2 sp = F := by rw [Kq2 sp (by decide), spb1]
  have r8q2 : reg q2 8 = out := by rw [Kq2 8 (by decide), r8b1]
  have r9q2 : reg q2 9 = d := by rw [Kq2 9 (by decide), r9b1]
  have kkq2 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg q2 q = reg m q := fun q hq => by
    rw [Kq2 q (by revert hq; revert q; decide), kkb1 q hq]
  rcases rr2 with ⟨hr, ha0q, h9q⟩ | ⟨v2, hr2, hv2, ha0q2, hm2, hd2, hk2, hj2⟩
  · obtain ⟨ne, de, ue⟩ := uq2.taken (cdDT Iq2) 0x7A dtm_at_3c (by decide) (by rw [ha0q, uq2.zero]; decide)
    exact finErr (preq2.trans (.single de)) ue.self Iq2 Sq2 h9q (by rw [ue.regs, spq2]) (by rw [ue.regs, r8q2])
      (fun q hq => by rw [ue.regs, kkq2 q hq]) (rdt_fail2 _ hr1 hr)
  obtain ⟨nb2, db2, ub2⟩ := uq2.notTaken (cdDT Iq2) 0x3E dtm_at_3c (by decide) (by
    rw [ha0q2, uq2.zero]; decide)
  obtain ⟨b2, cb2, ubb2⟩ := St.block dtB2 ub2.self (cdDT Iq2) dtB2_end (by
    simp +decide only [BlockOk, BInstr.ok, dtB2, and_true, true_and]; rw [ub2.regs, spq2]; exact hFC)
  have Rb2 : ∀ q, reg b2 q = (runBlock dtB2 (M2, reg nb2)).2 q := ubb2.regs
  have ub2' : St M2 DT b2 0x44 (reg b2) := ⟨ubb2.pc, by rw [ubb2.mem]; rfl, fun _ => rfl⟩
  have vb2 : reg b2 20 = BitVec.ofNat 32 v2 ∧ reg b2 a0 = F + 8 ∧ reg b2 a1 = d := by
    simp +decide only [Rb2, runBlock, BInstr.run, dtB2, upd_app, ↓reduceIte]
    simp only [ub2.regs]; rw [spq2, hm2, r9q2]; simp only [ev_add, zw, and_self]
  have Kb2 : ∀ q, q.val ∉ [10, 11, 20] → reg b2 q = reg q2 q := fun q hq => by
    have hd' : q ∉ dtB2.filterMap BInstr.dst := by
      simp only [dtB2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [Rb2, runBlock_reg _ _ _ q ub2.self.zero hd', ub2.regs]
  have spb2 : reg b2 sp = F := by rw [Kb2 sp (by decide), spq2]
  have r8b2 : reg b2 8 = out := by rw [Kb2 8 (by decide), r8q2]
  have r9b2 : reg b2 9 = d := by rw [Kb2 9 (by decide), r9q2]
  have kkb2 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg b2 q = reg m q := fun q hq => by
    rw [Kb2 q (by revert hq; revert q; decide), kkq2 q hq]
  have preb2 : Steps m b2 := preq2.trans (.cons db2 cb2)
  -- call 3: the bytes at `p + 4`
  obtain ⟨q3, M3, cq3, uq3, Iq3, Sq3, Kq3, rr3⟩ := dig (j := 4) ub2' dtm_at_44 dtm_at_48 (by decide)
    (by decide) dtm_at_4c (by decide) (by omega) Iq2 Sq2 hd2 hk2 spb2 vb2.2.1 vb2.2.2
  have preq3 : Steps m q3 := preb2.trans cq3
  have spq3 : reg q3 sp = F := by rw [Kq3 sp (by decide), spb2]
  have r8q3 : reg q3 8 = out := by rw [Kq3 8 (by decide), r8b2]
  have r9q3 : reg q3 9 = d := by rw [Kq3 9 (by decide), r9b2]
  have kkq3 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg q3 q = reg m q := fun q hq => by
    rw [Kq3 q (by revert hq; revert q; decide), kkb2 q hq]
  rcases rr3 with ⟨hr, ha0q, h9q⟩ | ⟨v3, hr3, hv3, ha0q3, hm3, hd3, hk3, hj3⟩
  · obtain ⟨ne, de, ue⟩ := uq3.taken (cdDT Iq3) 0x7A dtm_at_50 (by decide) (by rw [ha0q, uq3.zero]; decide)
    exact finErr (preq3.trans (.single de)) ue.self Iq3 Sq3 h9q (by rw [ue.regs, spq3]) (by rw [ue.regs, r8q3])
      (fun q hq => by rw [ue.regs, kkq3 q hq]) (rdt_fail3 _ hr1 hr2 hr)
  obtain ⟨nb3, db3, ub3⟩ := uq3.notTaken (cdDT Iq3) 0x52 dtm_at_50 (by decide) (by
    rw [ha0q3, uq3.zero]; decide)
  obtain ⟨b3, cb3, ubb3⟩ := St.block dtB3 ub3.self (cdDT Iq3) dtB3_end (by
    simp +decide only [BlockOk, BInstr.ok, dtB3, and_true, true_and]; rw [ub3.regs, spq3]; exact hFC)
  have Rb3 : ∀ q, reg b3 q = (runBlock dtB3 (M3, reg nb3)).2 q := ubb3.regs
  have ub3' : St M3 DT b3 0x58 (reg b3) := ⟨ubb3.pc, by rw [ubb3.mem]; rfl, fun _ => rfl⟩
  have vb3 : reg b3 19 = BitVec.ofNat 32 v3 ∧ reg b3 a0 = F + 8 ∧ reg b3 a1 = d := by
    simp +decide only [Rb3, runBlock, BInstr.run, dtB3, upd_app, ↓reduceIte]
    simp only [ub3.regs]; rw [spq3, hm3, r9q3]; simp only [ev_add, zw, and_self]
  have Kb3 : ∀ q, q.val ∉ [10, 11, 19] → reg b3 q = reg q3 q := fun q hq => by
    have hd' : q ∉ dtB3.filterMap BInstr.dst := by
      simp only [dtB3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [Rb3, runBlock_reg _ _ _ q ub3.self.zero hd', ub3.regs]
  have spb3 : reg b3 sp = F := by rw [Kb3 sp (by decide), spq3]
  have r8b3 : reg b3 8 = out := by rw [Kb3 8 (by decide), r8q3]
  have r9b3 : reg b3 9 = d := by rw [Kb3 9 (by decide), r9q3]
  have kkb3 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg b3 q = reg m q := fun q hq => by
    rw [Kb3 q (by revert hq; revert q; decide), kkq3 q hq]
  have preb3 : Steps m b3 := preq3.trans (.cons db3 cb3)
  -- call 4: the bytes at `p + 6`
  obtain ⟨q4, M4, cq4, uq4, Iq4, Sq4, Kq4, rr4⟩ := dig (j := 6) ub3' dtm_at_58 dtm_at_5c (by decide)
    (by decide) dtm_at_60 (by decide) (by omega) Iq3 Sq3 hd3 hk3 spb3 vb3.2.1 vb3.2.2
  have preq4 : Steps m q4 := preb3.trans cq4
  have spq4 : reg q4 sp = F := by rw [Kq4 sp (by decide), spb3]
  have r8q4 : reg q4 8 = out := by rw [Kq4 8 (by decide), r8b3]
  have r9q4 : reg q4 9 = d := by rw [Kq4 9 (by decide), r9b3]
  have kkq4 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg q4 q = reg m q := fun q hq => by
    rw [Kq4 q (by revert hq; revert q; decide), kkb3 q hq]
  rcases rr4 with ⟨hr, ha0q, h9q⟩ | ⟨v4, hr4, hv4, ha0q4, hm4, hd4, hk4, hj4⟩
  · obtain ⟨ne, de, ue⟩ := uq4.taken (cdDT Iq4) 0x7A dtm_at_64 (by decide) (by rw [ha0q, uq4.zero]; decide)
    exact finErr (preq4.trans (.single de)) ue.self Iq4 Sq4 h9q (by rw [ue.regs, spq4]) (by rw [ue.regs, r8q4])
      (fun q hq => by rw [ue.regs, kkq4 q hq]) (rdt_fail4 _ hr1 hr2 hr3 hr)
  obtain ⟨nb4, db4, ub4⟩ := uq4.notTaken (cdDT Iq4) 0x66 dtm_at_64 (by decide) (by
    rw [ha0q4, uq4.zero]; decide)
  obtain ⟨b4, cb4, ubb4⟩ := St.block dtB4 ub4.self (cdDT Iq4) dtB4_end (by
    simp +decide only [BlockOk, BInstr.ok, dtB4, and_true, true_and]; rw [ub4.regs, spq4]; exact hFC)
  have Rb4 : ∀ q, reg b4 q = (runBlock dtB4 (M4, reg nb4)).2 q := ubb4.regs
  have ub4' : St M4 DT b4 0x6C (reg b4) := ⟨ubb4.pc, by rw [ubb4.mem]; rfl, fun _ => rfl⟩
  have vb4 : reg b4 21 = BitVec.ofNat 32 v4 ∧ reg b4 a0 = F + 8 ∧ reg b4 a1 = d := by
    simp +decide only [Rb4, runBlock, BInstr.run, dtB4, upd_app, ↓reduceIte]
    simp only [ub4.regs]; rw [spq4, hm4, r9q4]; simp only [ev_add, zw, and_self]
  have Kb4 : ∀ q, q.val ∉ [10, 11, 21] → reg b4 q = reg q4 q := fun q hq => by
    have hd' : q ∉ dtB4.filterMap BInstr.dst := by
      simp only [dtB4, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [Rb4, runBlock_reg _ _ _ q ub4.self.zero hd', ub4.regs]
  have spb4 : reg b4 sp = F := by rw [Kb4 sp (by decide), spq4]
  have r8b4 : reg b4 8 = out := by rw [Kb4 8 (by decide), r8q4]
  have r9b4 : reg b4 9 = d := by rw [Kb4 9 (by decide), r9q4]
  have kkb4 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg b4 q = reg m q := fun q hq => by
    rw [Kb4 q (by revert hq; revert q; decide), kkq4 q hq]
  have preb4 : Steps m b4 := preq4.trans (.cons db4 cb4)
  -- call 5: the bytes at `p + 8`
  obtain ⟨q5, M5, cq5, uq5, Iq5, Sq5, Kq5, rr5⟩ := dig (j := 8) ub4' dtm_at_6c dtm_at_70 (by decide)
    (by decide) dtm_at_74 (by decide) (by omega) Iq4 Sq4 hd4 hk4 spb4 vb4.2.1 vb4.2.2
  have preq5 : Steps m q5 := preb4.trans cq5
  have spq5 : reg q5 sp = F := by rw [Kq5 sp (by decide), spb4]
  have r8q5 : reg q5 8 = out := by rw [Kq5 8 (by decide), r8b4]
  have r9q5 : reg q5 9 = d := by rw [Kq5 9 (by decide), r9b4]
  have kkq5 : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg q5 q = reg m q := fun q hq => by
    rw [Kq5 q (by revert hq; revert q; decide), kkb4 q hq]
  rcases rr5 with ⟨hr, ha0q, h9q⟩ | ⟨v5, hr5, hv5, ha0q5, hm5, hd5, hk5, hj5⟩
  · obtain ⟨ne, de, ue⟩ := uq5.notTaken (cdDT Iq5) 0x7A dtm_at_78 (by decide) (by rw [ha0q, uq5.zero]; decide)
    exact finErr (preq5.trans (.single de)) ue.self Iq5 Sq5 h9q (by rw [ue.regs, spq5]) (by rw [ue.regs, r8q5])
      (fun q hq => by rw [ue.regs, kkq5 q hq]) (rdt_fail5 _ hr1 hr2 hr3 hr4 hr)
  obtain ⟨n9c, d9c, u9c⟩ := uq5.taken (cdDT Iq5) 0x9C dtm_at_78 (by decide) (by rw [ha0q5, uq5.zero]; decide)
  -- the five fields, in place at 0x9C
  have g22 : reg n9c 22 = BitVec.ofNat 32 v1 := by
    rw [u9c.regs, Kq5 _ (by decide), Kb4 _ (by decide), Kq4 _ (by decide), Kb3 _ (by decide), Kq3 _ (by decide),
      Kb2 _ (by decide), Kq2 _ (by decide), vb1.1]
  have g20 : reg n9c 20 = BitVec.ofNat 32 v2 := by
    rw [u9c.regs, Kq5 _ (by decide), Kb4 _ (by decide), Kq4 _ (by decide), Kb3 _ (by decide), Kq3 _ (by decide),
      vb2.1]
  have g19 : reg n9c 19 = BitVec.ofNat 32 v3 := by
    rw [u9c.regs, Kq5 _ (by decide), Kb4 _ (by decide), Kq4 _ (by decide), vb3.1]
  have g21 : reg n9c 21 = BitVec.ofNat 32 v4 := by rw [u9c.regs, Kq5 _ (by decide), vb4.1]
  have g18 : reg n9c 18 = BitVec.ofNat 32 Y.toNat := by
    rw [u9c.regs, Kq5 _ (by decide), Kb4 _ (by decide), Kq4 _ (by decide), Kb3 _ (by decide), Kq3 _ (by decide),
      Kb2 _ (by decide), Kq2 _ (by decide), Kb1 _ (by decide), Kq1 _ (by decide), v318, ofNat_toNat_self]
  have gsp : reg n9c sp = F := by rw [u9c.regs, spq5]
  have g8 : reg n9c 8 = out := by rw [u9c.regs, r8q5]
  have gkk : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg n9c q = reg m q := fun q hq => by
    rw [u9c.regs, kkq5 q hq]
  have hspec := rdt_ok Y.toNat hr1 hr2 hr3 hr4 hr5
  obtain ⟨nc, ccc, Kc, hcs⟩ := dt_check (Y := Y.toNat) (Mo := v1) (D := v2) (h := v3) (mi := v4) (s := v5) (F := F)
    u9c.self (cdDT Iq5) Y.isLt hv1 hv2 hv3 hv4 hv5 g18 g22 g20 g19 g21 gsp hFC hm5
  have prec : Steps m nc := preq5.trans (.cons d9c ccc)
  have csp : reg nc sp = F := by rw [Kc sp (by decide), gsp]
  have c8 : reg nc 8 = out := by rw [Kc 8 (by decide), g8]
  have ckk : ∀ q, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → reg nc q = reg m q := fun q hq => by
    rw [Kc q (by revert hq; revert q; decide), gkk q hq]
  rcases hcs with ⟨hok, uc, ca0⟩ | ⟨hok, uc⟩
  rotate_left
  · exact finBad prec uc Iq5 Sq5 csp c8 ckk (by rw [hspec, hok]; rfl)
  obtain ⟨hY, hM1, hM2, hD1, hD2, hh, hmi, hs⟩ := dtOk_true.mp hok
  have so8 : (out + 8).toNat % 4 = 0 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have so12 : (out + 0xC).toNat % 4 = 0 := by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨na, ca, ua, a1a, Ka⟩ := dt_arith (Y := Y.toNat) (Mo := v1) (D := v2) (h := v3) (mi := v4) (s := v5)
    (out := out) uc (cdDT Iq5) hY Y.isLt hM1 hM2 hD1 (Nat.le_trans hD2 (dim_le _ _)) hh hmi hs
    (by rw [Kc _ (by decide), g18]) (by rw [Kc _ (by decide), g22]) (by rw [Kc _ (by decide), g20])
    (by rw [Kc _ (by decide), g19]) (by rw [Kc _ (by decide), g21]) ca0 c8 so8 so12
    (sOC (c := 8) (l := 4) (by decide)) (sOC (c := 0xC) (l := 4) (by decide))
  obtain ⟨T0, hT0⟩ : ∃ T0, daysFromCivil Y.toNat v1 v2 * 86400 + v3 * 3600 + v4 * 60 + v5 = T0 := ⟨_, rfl⟩
  rw [hT0] at ua
  -- the result buffer `out` and the reader `d`, apart from each other and from the frame
  have sx8 : ∀ {x : Word}, Sep out 16 x 1 → Sep (out + 8) 4 x 1 := fun hx => hx.sub (c := 8) (l := 4) (by decide)
  have sx12 : ∀ {x : Word}, Sep out 16 x 1 → Sep (out + 0xC) 4 x 1 := fun hx => hx.sub (c := 0xC) (l := 4) (by decide)
  have sFo : ∀ {c' : Nat}, c' < 0x30 → Sep out 16 (F + BitVec.ofNat 32 c') 1 := fun {c'} h => sOG.subR (c := c') (l := 1) h
  obtain ⟨nf, cf, pcf, spf, Kf, memf⟩ := tail84 (v := 0) ua
    ((cdDT Iq5).store32 (sOC (c := 8) (l := 4) (by decide)) |>.store32 (sOC (c := 0xC) (l := 4) (by decide)))
    (by rw [Ka sp (by decide), csp]) (by rw [Ka 8 (by decide), c8]) a1a
    (fun c' h1 h2 => by rw [memStore32_get_sep (sx12 (sFo h2)), memStore32_get_sep (sx8 (sFo h2)), Sq5 c' h1 h2])
    (fun q hq => by rw [Ka q (by revert hq; revert q; decide), ckk q hq])
  have hspec' : readDateTime Y.toNat (memBytes m.mem p n) =
      some (T0, memBytes m.mem (p + BitVec.ofNat 32 (8 + 2)) (n - (8 + 2))) := by rw [hspec, hok, ← hT0]; rfl
  have hT64 : T0 < 2 ^ 64 := by
    rw [← hT0]; exact dt_t_lt Y.isLt hY hM1 hM2 hD1 hv2 hh hmi hs
  have s0_8 : Sep out 1 (out + 8) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 8) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s0_12 : Sep out 1 (out + 0xC) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 0xC) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s12_8 : Sep (out + 0xC) 4 (out + 8) 4 := sep_offsets out (c := 0xC) (n := 4) (d := 8) (k := 4) (by omega)
    (by omega) (by omega)
  have sod : ∀ {c l e : Nat}, c + l ≤ 16 → e + 4 ≤ 8 → Sep (out + BitVec.ofNat 32 c) l (d + BitVec.ofNat 32 e) 4 :=
    fun h1 h2 => (sOD.sub h1).subR h2
  have s0d : Sep out 1 d 4 := by have := sod (c := 0) (l := 1) (e := 0) (by omega) (by omega); rwa [add_ofNat_zero, add_ofNat_zero] at this
  have s8d : Sep (out + 8) 4 d 4 := by have := sod (c := 8) (l := 4) (e := 0) (by omega) (by omega); rwa [add_ofNat_zero] at this
  have s12d : Sep (out + 0xC) 4 d 4 := by have := sod (c := 0xC) (l := 4) (e := 0) (by omega) (by omega); rwa [add_ofNat_zero] at this
  have s0d4 : Sep out 1 (d + 4) 4 := by have := sod (c := 0) (l := 1) (e := 4) (by omega) (by omega); rwa [add_ofNat_zero] at this
  have s8d4 : Sep (out + 8) 4 (d + 4) 4 := sod (c := 8) (l := 4) (e := 4) (by omega) (by omega)
  have s12d4 : Sep (out + 0xC) 4 (d + 4) 4 := sod (c := 0xC) (l := 4) (e := 4) (by omega) (by omega)
  have hE : ∀ t rest, readDateTime Y.toNat (memBytes m.mem p n) = some (t, rest) →
      t = T0 ∧ rest = memBytes m.mem (p + BitVec.ofNat 32 (8 + 2)) (n - (8 + 2)) := fun t rest h => by
    rw [hspec'] at h; cases h; exact ⟨rfl, rfl⟩
  have hN : readDateTime Y.toNat (memBytes m.mem p n) = none → False := fun h => by rw [hspec'] at h; cases h
  refine ⟨nf, prec.trans (ca.trans cf), pcf, spf, Kf, fun t rest h => ?_, fun h => (hN h).elim,
    fun x hx hx1 hx2 => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hE t rest h
    refine ⟨hT64, by rw [memf, memStore8_same]; rfl, ?_, ?_, rfl, ?_, ?_⟩
    · rw [memf, memLoad32_store8_sep s0_8, memLoad32_store32_sep s12_8, memLoad32_store32_same]
    · rw [memf, memLoad32_store8_sep s0_12, memLoad32_store32_same]
    · rw [memf, memLoad32_store8_sep s0d, memLoad32_store32_sep s12d, memLoad32_store32_sep s8d, hd5]; rfl
    · rw [memf, memLoad32_store8_sep s0d4, memLoad32_store32_sep s12d4, memLoad32_store32_sep s8d4, hk5]
  · rw [memf, memStore8_ne (xo0 hx1), memStore32_get_sep (sx12 hx1), memStore32_get_sep (sx8 hx1), Iq5 x hx hx2]

end C3.RV32
