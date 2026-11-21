import C3BootProofs.Proofs.ShaTools
import C3BootProofs.Proofs.UintSelect12
import C3BootProofs.Image.Bootloader

/-!
# `sha2::sha256::compress256`, compact backend: code and environment

The decoded instructions of the compiled compression function and of
`RangeFrom::index`, which it calls to slice each block, and `KCEnv`, where
the function runs.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000

theorem kc_at_0 : fetchRel sha256CompressCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF20, 2) := by decide
theorem kc_at_2 : fetchRel sha256CompressCode 0x2 = some (.store .sw sp ra 0xDC, 2) := by decide
theorem kc_at_4 : fetchRel sha256CompressCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xD8, 2) := by decide
theorem kc_at_6 : fetchRel sha256CompressCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xD4, 2) := by decide
theorem kc_at_8 : fetchRel sha256CompressCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xD0, 2) := by decide
theorem kc_at_a : fetchRel sha256CompressCode 0xA = some (.store .sw sp (19 : Fin 32) 0xCC, 2) := by decide
theorem kc_at_c : fetchRel sha256CompressCode 0xC = some (.store .sw sp (20 : Fin 32) 0xC8, 2) := by decide
theorem kc_at_e : fetchRel sha256CompressCode 0xE = some (.store .sw sp (21 : Fin 32) 0xC4, 2) := by decide
theorem kc_at_10 : fetchRel sha256CompressCode 0x10 = some (.store .sw sp (22 : Fin 32) 0xC0, 2) := by decide
theorem kc_at_12 : fetchRel sha256CompressCode 0x12 = some (.store .sw sp (23 : Fin 32) 0xBC, 2) := by decide
theorem kc_at_14 : fetchRel sha256CompressCode 0x14 = some (.store .sw sp (24 : Fin 32) 0xB8, 2) := by decide
theorem kc_at_16 : fetchRel sha256CompressCode 0x16 = some (.store .sw sp (25 : Fin 32) 0xB4, 2) := by decide
theorem kc_at_18 : fetchRel sha256CompressCode 0x18 = some (.store .sw sp (26 : Fin 32) 0xB0, 2) := by decide
theorem kc_at_1a : fetchRel sha256CompressCode 0x1A = some (.store .sw sp (27 : Fin 32) 0xAC, 2) := by decide
theorem kc_at_1c : fetchRel sha256CompressCode 0x1C = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem kc_at_1e : fetchRel sha256CompressCode 0x1E = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem kc_at_20 : fetchRel sha256CompressCode 0x20 = some (.aluImm .sll a2 a2 0x6, 2) := by decide
theorem kc_at_22 : fetchRel sha256CompressCode 0x22 = some (.load .lw (23 : Fin 32) a0 0x0, 4) := by decide
theorem kc_at_26 : fetchRel sha256CompressCode 0x26 = some (.load .lw a0 a0 0x4, 2) := by decide
theorem kc_at_28 : fetchRel sha256CompressCode 0x28 = some (.store .sw sp a0 0x28, 2) := by decide
theorem kc_at_2a : fetchRel sha256CompressCode 0x2A = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem kc_at_2c : fetchRel sha256CompressCode 0x2C = some (.load .lw a0 a3 0x8, 2) := by decide
theorem kc_at_2e : fetchRel sha256CompressCode 0x2E = some (.store .sw sp a0 0x24, 2) := by decide
theorem kc_at_30 : fetchRel sha256CompressCode 0x30 = some (.load .lw (25 : Fin 32) (18 : Fin 32) 0xC, 4) := by decide
theorem kc_at_34 : fetchRel sha256CompressCode 0x34 = some (.load .lw (26 : Fin 32) (18 : Fin 32) 0x10, 4) := by decide
theorem kc_at_38 : fetchRel sha256CompressCode 0x38 = some (.load .lw a0 a3 0x14, 2) := by decide
theorem kc_at_3a : fetchRel sha256CompressCode 0x3A = some (.store .sw sp a0 0x20, 2) := by decide
theorem kc_at_3c : fetchRel sha256CompressCode 0x3C = some (.load .lw a0 a3 0x18, 2) := by decide
theorem kc_at_3e : fetchRel sha256CompressCode 0x3E = some (.store .sw sp a0 0x1C, 2) := by decide
theorem kc_at_40 : fetchRel sha256CompressCode 0x40 = some (.load .lw (24 : Fin 32) (18 : Fin 32) 0x1C, 4) := by decide
theorem kc_at_44 : fetchRel sha256CompressCode 0x44 = some (.alu .add a2 a2 a1, 2) := by decide
theorem kc_at_46 : fetchRel sha256CompressCode 0x46 = some (.store .sw sp a2 0x8, 2) := by decide
theorem kc_at_48 : fetchRel sha256CompressCode 0x48 = some (.aluImm .add (27 : Fin 32) sp 0x6C, 4) := by decide
theorem kc_at_4c : fetchRel sha256CompressCode 0x4C = some (.aluImm .add (19 : Fin 32) x0 0x10, 2) := by decide
theorem kc_at_4e : fetchRel sha256CompressCode 0x4E = some (.aluImm .add (20 : Fin 32) sp 0x2C, 4) := by decide
theorem kc_at_52 : fetchRel sha256CompressCode 0x52 = some (.aluImm .add (21 : Fin 32) x0 0x3, 2) := by decide
theorem kc_at_54 : fetchRel sha256CompressCode 0x54 = some (.load .lw a0 sp 0x8, 2) := by decide
theorem kc_at_56 : fetchRel sha256CompressCode 0x56 = some (.branch .beq (9 : Fin 32) a0 0x1D8, 4) := by decide
theorem kc_at_5a : fetchRel sha256CompressCode 0x5A = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem kc_at_5c : fetchRel sha256CompressCode 0x5C = some (.aluImm .add (22 : Fin 32) (9 : Fin 32) 0x40, 4) := by decide
theorem kc_at_60 : fetchRel sha256CompressCode 0x60 = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFFC0, 4) := by decide
theorem kc_at_64 : fetchRel sha256CompressCode 0x64 = some (.branch .beq a0 x0 0x3C, 2) := by decide
theorem kc_at_66 : fetchRel sha256CompressCode 0x66 = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem kc_at_6a : fetchRel sha256CompressCode 0x6A = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem kc_at_6c : fetchRel sha256CompressCode 0x6C = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem kc_at_6e : fetchRel sha256CompressCode 0x6E = some (.auipc ra 0x0, 4) := by decide
theorem kc_at_72 : fetchRel sha256CompressCode 0x72 = some (.jalr ra ra 0x1EC, 4) := by decide
theorem kc_at_76 : fetchRel sha256CompressCode 0x76 = some (.branch .bgeu (21 : Fin 32) a1 0x1D6, 4) := by decide
theorem kc_at_7a : fetchRel sha256CompressCode 0x7A = some (.load .lbu a1 a0 0x2, 4) := by decide
theorem kc_at_7e : fetchRel sha256CompressCode 0x7E = some (.load .lbu a2 a0 0x0, 4) := by decide
theorem kc_at_82 : fetchRel sha256CompressCode 0x82 = some (.load .lbu a3 a0 0x1, 4) := by decide
theorem kc_at_86 : fetchRel sha256CompressCode 0x86 = some (.load .lbu a0 a0 0x3, 4) := by decide
theorem kc_at_8a : fetchRel sha256CompressCode 0x8A = some (.aluImm .sll a1 a1 0x8, 2) := by decide
theorem kc_at_8c : fetchRel sha256CompressCode 0x8C = some (.aluImm .sll a3 a3 0x10, 2) := by decide
theorem kc_at_8e : fetchRel sha256CompressCode 0x8E = some (.aluImm .sll a2 a2 0x18, 2) := by decide
theorem kc_at_90 : fetchRel sha256CompressCode 0x90 = some (.alu .or a0 a0 a1, 2) := by decide
theorem kc_at_92 : fetchRel sha256CompressCode 0x92 = some (.alu .or a2 a2 a3, 2) := by decide
theorem kc_at_94 : fetchRel sha256CompressCode 0x94 = some (.alu .or a0 a0 a2, 2) := by decide
theorem kc_at_96 : fetchRel sha256CompressCode 0x96 = some (.alu .add a1 (27 : Fin 32) (8 : Fin 32), 4) := by decide
theorem kc_at_9a : fetchRel sha256CompressCode 0x9A = some (.store .sw a1 a0 0x0, 2) := by decide
theorem kc_at_9c : fetchRel sha256CompressCode 0x9C = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem kc_at_9e : fetchRel sha256CompressCode 0x9E = some (.jal x0 0xFFFFFFC2, 2) := by decide
theorem kc_at_a0 : fetchRel sha256CompressCode 0xA0 = some (.store .sw sp (22 : Fin 32) 0xC, 2) := by decide
theorem kc_at_a2 : fetchRel sha256CompressCode 0xA2 = some (.aluImm .add a0 sp 0x2C, 2) := by decide
theorem kc_at_a4 : fetchRel sha256CompressCode 0xA4 = some (.aluImm .add a1 sp 0x6C, 2) := by decide
theorem kc_at_a6 : fetchRel sha256CompressCode 0xA6 = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem kc_at_aa : fetchRel sha256CompressCode 0xAA = some (.aluImm .add (22 : Fin 32) sp 0x2C, 4) := by decide
theorem kc_at_ae : fetchRel sha256CompressCode 0xAE = some (.auipc ra 0x0, 4) := by decide
theorem kc_at_b2 : fetchRel sha256CompressCode 0xB2 = some (.jalr ra ra 0x76E, 4) := by decide
theorem kc_at_b6 : fetchRel sha256CompressCode 0xB6 = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem kc_at_b8 : fetchRel sha256CompressCode 0xB8 = some (.lui (7 : Fin 32) 0x3FCC5000, 4) := by decide
theorem kc_at_bc : fetchRel sha256CompressCode 0xBC = some (.aluImm .add (7 : Fin 32) (7 : Fin 32) 0xFFFFFEBC, 4) := by decide
theorem kc_at_c0 : fetchRel sha256CompressCode 0xC0 = some (.store .sw sp (26 : Fin 32) 0x10, 2) := by decide
theorem kc_at_c2 : fetchRel sha256CompressCode 0xC2 = some (.alu .add a0 x0 (26 : Fin 32), 2) := by decide
theorem kc_at_c4 : fetchRel sha256CompressCode 0xC4 = some (.store .sw sp (23 : Fin 32) 0x18, 2) := by decide
theorem kc_at_c6 : fetchRel sha256CompressCode 0xC6 = some (.alu .add a2 x0 (23 : Fin 32), 2) := by decide
theorem kc_at_c8 : fetchRel sha256CompressCode 0xC8 = some (.alu .add (26 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem kc_at_ca : fetchRel sha256CompressCode 0xCA = some (.load .lw (17 : Fin 32) sp 0x1C, 2) := by decide
theorem kc_at_cc : fetchRel sha256CompressCode 0xCC = some (.load .lw (5 : Fin 32) sp 0x20, 2) := by decide
theorem kc_at_ce : fetchRel sha256CompressCode 0xCE = some (.store .sw sp (25 : Fin 32) 0x14, 2) := by decide
theorem kc_at_d0 : fetchRel sha256CompressCode 0xD0 = some (.load .lw a6 sp 0x24, 2) := by decide
theorem kc_at_d2 : fetchRel sha256CompressCode 0xD2 = some (.load .lw (29 : Fin 32) sp 0x28, 2) := by decide
theorem kc_at_d4 : fetchRel sha256CompressCode 0xD4 = some (.aluImm .add (9 : Fin 32) (8 : Fin 32) 0xFFFFFFC0, 4) := by decide
theorem kc_at_d8 : fetchRel sha256CompressCode 0xD8 = some (.alu .add (30 : Fin 32) x0 a2, 2) := by decide
theorem kc_at_da : fetchRel sha256CompressCode 0xDA = some (.alu .add (6 : Fin 32) x0 a0, 2) := by decide
theorem kc_at_dc : fetchRel sha256CompressCode 0xDC = some (.branch .beq (9 : Fin 32) x0 0x10E, 4) := by decide
theorem kc_at_e0 : fetchRel sha256CompressCode 0xE0 = some (.aluImm .add (28 : Fin 32) (8 : Fin 32) 0x1, 4) := by decide
theorem kc_at_e4 : fetchRel sha256CompressCode 0xE4 = some (.branch .bgeu (8 : Fin 32) (19 : Fin 32) 0xA, 4) := by decide
theorem kc_at_e8 : fetchRel sha256CompressCode 0xE8 = some (.load .lw a0 (22 : Fin 32) 0x0, 4) := by decide
theorem kc_at_ec : fetchRel sha256CompressCode 0xEC = some (.jal x0 0x74, 2) := by decide
theorem kc_at_ee : fetchRel sha256CompressCode 0xEE = some (.aluImm .and a0 (28 : Fin 32) 0xF, 4) := by decide
theorem kc_at_f2 : fetchRel sha256CompressCode 0xF2 = some (.aluImm .add a2 (8 : Fin 32) 0xE, 4) := by decide
theorem kc_at_f6 : fetchRel sha256CompressCode 0xF6 = some (.aluImm .sll a0 a0 0x2, 2) := by decide
theorem kc_at_f8 : fetchRel sha256CompressCode 0xF8 = some (.aluImm .and a2 a2 0xF, 2) := by decide
theorem kc_at_fa : fetchRel sha256CompressCode 0xFA = some (.alu .add a0 a0 (20 : Fin 32), 2) := by decide
theorem kc_at_fc : fetchRel sha256CompressCode 0xFC = some (.aluImm .sll a2 a2 0x2, 2) := by decide
theorem kc_at_fe : fetchRel sha256CompressCode 0xFE = some (.load .lw a0 a0 0x0, 2) := by decide
theorem kc_at_100 : fetchRel sha256CompressCode 0x100 = some (.alu .add a2 a2 (20 : Fin 32), 2) := by decide
theorem kc_at_102 : fetchRel sha256CompressCode 0x102 = some (.aluImm .and (9 : Fin 32) (8 : Fin 32) 0xF, 4) := by decide
theorem kc_at_106 : fetchRel sha256CompressCode 0x106 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x9, 2) := by decide
theorem kc_at_108 : fetchRel sha256CompressCode 0x108 = some (.aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x2, 2) := by decide
theorem kc_at_10a : fetchRel sha256CompressCode 0x10A = some (.aluImm .and (8 : Fin 32) (8 : Fin 32) 0xF, 2) := by decide
theorem kc_at_10c : fetchRel sha256CompressCode 0x10C = some (.alu .add (9 : Fin 32) (9 : Fin 32) (20 : Fin 32), 2) := by decide
theorem kc_at_10e : fetchRel sha256CompressCode 0x10E = some (.aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x2, 2) := by decide
theorem kc_at_110 : fetchRel sha256CompressCode 0x110 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (20 : Fin 32), 2) := by decide
theorem kc_at_112 : fetchRel sha256CompressCode 0x112 = some (.load .lw a5 a2 0x0, 2) := by decide
theorem kc_at_114 : fetchRel sha256CompressCode 0x114 = some (.load .lw (31 : Fin 32) (9 : Fin 32) 0x0, 4) := by decide
theorem kc_at_118 : fetchRel sha256CompressCode 0x118 = some (.load .lw ra (8 : Fin 32) 0x0, 4) := by decide
theorem kc_at_11c : fetchRel sha256CompressCode 0x11C = some (.aluImm .srl a3 a0 0x7, 4) := by decide
theorem kc_at_120 : fetchRel sha256CompressCode 0x120 = some (.aluImm .sll a2 a0 0x19, 4) := by decide
theorem kc_at_124 : fetchRel sha256CompressCode 0x124 = some (.aluImm .srl (8 : Fin 32) a0 0x12, 4) := by decide
theorem kc_at_128 : fetchRel sha256CompressCode 0x128 = some (.aluImm .sll (23 : Fin 32) a0 0xE, 4) := by decide
theorem kc_at_12c : fetchRel sha256CompressCode 0x12C = some (.alu .or a3 a3 a2, 2) := by decide
theorem kc_at_12e : fetchRel sha256CompressCode 0x12E = some (.alu .or (23 : Fin 32) (23 : Fin 32) (8 : Fin 32), 4) := by decide
theorem kc_at_132 : fetchRel sha256CompressCode 0x132 = some (.aluImm .srl (8 : Fin 32) a5 0x11, 4) := by decide
theorem kc_at_136 : fetchRel sha256CompressCode 0x136 = some (.aluImm .sll a2 a5 0xF, 4) := by decide
theorem kc_at_13a : fetchRel sha256CompressCode 0x13A = some (.alu .xor a3 a3 (23 : Fin 32), 4) := by decide
theorem kc_at_13e : fetchRel sha256CompressCode 0x13E = some (.alu .or (23 : Fin 32) a2 (8 : Fin 32), 4) := by decide
theorem kc_at_142 : fetchRel sha256CompressCode 0x142 = some (.aluImm .srl (8 : Fin 32) a5 0x13, 4) := by decide
theorem kc_at_146 : fetchRel sha256CompressCode 0x146 = some (.aluImm .sll a2 a5 0xD, 4) := by decide
theorem kc_at_14a : fetchRel sha256CompressCode 0x14A = some (.alu .or a2 a2 (8 : Fin 32), 2) := by decide
theorem kc_at_14c : fetchRel sha256CompressCode 0x14C = some (.aluImm .srl a0 a0 0x3, 2) := by decide
theorem kc_at_14e : fetchRel sha256CompressCode 0x14E = some (.alu .xor a0 a0 a3, 2) := by decide
theorem kc_at_150 : fetchRel sha256CompressCode 0x150 = some (.alu .xor a2 (23 : Fin 32) a2, 4) := by decide
theorem kc_at_154 : fetchRel sha256CompressCode 0x154 = some (.aluImm .srl a5 a5 0xA, 2) := by decide
theorem kc_at_156 : fetchRel sha256CompressCode 0x156 = some (.alu .add (31 : Fin 32) (31 : Fin 32) ra, 2) := by decide
theorem kc_at_158 : fetchRel sha256CompressCode 0x158 = some (.alu .xor a2 a2 a5, 2) := by decide
theorem kc_at_15a : fetchRel sha256CompressCode 0x15A = some (.alu .add a0 a0 (31 : Fin 32), 2) := by decide
theorem kc_at_15c : fetchRel sha256CompressCode 0x15C = some (.alu .add a0 a0 a2, 2) := by decide
theorem kc_at_15e : fetchRel sha256CompressCode 0x15E = some (.store .sw (9 : Fin 32) a0 0x0, 2) := by decide
theorem kc_at_160 : fetchRel sha256CompressCode 0x160 = some (.aluImm .srl a2 (6 : Fin 32) 0x6, 4) := by decide
theorem kc_at_164 : fetchRel sha256CompressCode 0x164 = some (.aluImm .sll a3 (6 : Fin 32) 0x1A, 4) := by decide
theorem kc_at_168 : fetchRel sha256CompressCode 0x168 = some (.aluImm .srl a5 (6 : Fin 32) 0xB, 4) := by decide
theorem kc_at_16c : fetchRel sha256CompressCode 0x16C = some (.aluImm .sll a1 (6 : Fin 32) 0x15, 4) := by decide
theorem kc_at_170 : fetchRel sha256CompressCode 0x170 = some (.alu .or a2 a2 a3, 2) := by decide
theorem kc_at_172 : fetchRel sha256CompressCode 0x172 = some (.alu .or a1 a1 a5, 2) := by decide
theorem kc_at_174 : fetchRel sha256CompressCode 0x174 = some (.alu .xor a1 a1 a2, 2) := by decide
theorem kc_at_176 : fetchRel sha256CompressCode 0x176 = some (.aluImm .srl a2 (6 : Fin 32) 0x19, 4) := by decide
theorem kc_at_17a : fetchRel sha256CompressCode 0x17A = some (.aluImm .sll a3 (6 : Fin 32) 0x7, 4) := by decide
theorem kc_at_17e : fetchRel sha256CompressCode 0x17E = some (.aluImm .xor a5 (6 : Fin 32) 0xFFFFFFFF, 4) := by decide
theorem kc_at_182 : fetchRel sha256CompressCode 0x182 = some (.load .lw (9 : Fin 32) (7 : Fin 32) 0x0, 4) := by decide
theorem kc_at_186 : fetchRel sha256CompressCode 0x186 = some (.alu .or a2 a2 a3, 2) := by decide
theorem kc_at_188 : fetchRel sha256CompressCode 0x188 = some (.alu .and a3 (17 : Fin 32) a5, 4) := by decide
theorem kc_at_18c : fetchRel sha256CompressCode 0x18C = some (.alu .add a3 a3 (26 : Fin 32), 2) := by decide
theorem kc_at_18e : fetchRel sha256CompressCode 0x18E = some (.alu .and a5 (5 : Fin 32) (6 : Fin 32), 4) := by decide
theorem kc_at_192 : fetchRel sha256CompressCode 0x192 = some (.alu .xor a1 a1 a2, 2) := by decide
theorem kc_at_194 : fetchRel sha256CompressCode 0x194 = some (.alu .add a3 a3 a5, 2) := by decide
theorem kc_at_196 : fetchRel sha256CompressCode 0x196 = some (.alu .add a1 a1 a3, 2) := by decide
theorem kc_at_198 : fetchRel sha256CompressCode 0x198 = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem kc_at_19a : fetchRel sha256CompressCode 0x19A = some (.aluImm .srl a2 (30 : Fin 32) 0x2, 4) := by decide
theorem kc_at_19e : fetchRel sha256CompressCode 0x19E = some (.aluImm .sll a3 (30 : Fin 32) 0x1E, 4) := by decide
theorem kc_at_1a2 : fetchRel sha256CompressCode 0x1A2 = some (.aluImm .srl a5 (30 : Fin 32) 0xD, 4) := by decide
theorem kc_at_1a6 : fetchRel sha256CompressCode 0x1A6 = some (.aluImm .sll a4 (30 : Fin 32) 0x13, 4) := by decide
theorem kc_at_1aa : fetchRel sha256CompressCode 0x1AA = some (.alu .or a2 a2 a3, 2) := by decide
theorem kc_at_1ac : fetchRel sha256CompressCode 0x1AC = some (.alu .or a4 a4 a5, 2) := by decide
theorem kc_at_1ae : fetchRel sha256CompressCode 0x1AE = some (.alu .add a1 a1 a0, 2) := by decide
theorem kc_at_1b0 : fetchRel sha256CompressCode 0x1B0 = some (.alu .xor a2 a2 a4, 2) := by decide
theorem kc_at_1b2 : fetchRel sha256CompressCode 0x1B2 = some (.aluImm .srl a0 (30 : Fin 32) 0x16, 4) := by decide
theorem kc_at_1b6 : fetchRel sha256CompressCode 0x1B6 = some (.aluImm .sll a3 (30 : Fin 32) 0xA, 4) := by decide
theorem kc_at_1ba : fetchRel sha256CompressCode 0x1BA = some (.alu .or a0 a0 a3, 2) := by decide
theorem kc_at_1bc : fetchRel sha256CompressCode 0x1BC = some (.alu .xor a3 (29 : Fin 32) a6, 4) := by decide
theorem kc_at_1c0 : fetchRel sha256CompressCode 0x1C0 = some (.alu .and a3 a3 (30 : Fin 32), 4) := by decide
theorem kc_at_1c4 : fetchRel sha256CompressCode 0x1C4 = some (.alu .and a4 (29 : Fin 32) a6, 4) := by decide
theorem kc_at_1c8 : fetchRel sha256CompressCode 0x1C8 = some (.alu .xor a0 a0 a2, 2) := by decide
theorem kc_at_1ca : fetchRel sha256CompressCode 0x1CA = some (.alu .xor a3 a3 a4, 2) := by decide
theorem kc_at_1cc : fetchRel sha256CompressCode 0x1CC = some (.alu .add a2 a3 a0, 4) := by decide
theorem kc_at_1d0 : fetchRel sha256CompressCode 0x1D0 = some (.alu .add a0 a1 (25 : Fin 32), 4) := by decide
theorem kc_at_1d4 : fetchRel sha256CompressCode 0x1D4 = some (.alu .add a2 a2 a1, 2) := by decide
theorem kc_at_1d6 : fetchRel sha256CompressCode 0x1D6 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x4, 2) := by decide
theorem kc_at_1d8 : fetchRel sha256CompressCode 0x1D8 = some (.aluImm .add (7 : Fin 32) (7 : Fin 32) 0x4, 2) := by decide
theorem kc_at_1da : fetchRel sha256CompressCode 0x1DA = some (.alu .add (8 : Fin 32) x0 (28 : Fin 32), 2) := by decide
theorem kc_at_1dc : fetchRel sha256CompressCode 0x1DC = some (.alu .add (26 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem kc_at_1de : fetchRel sha256CompressCode 0x1DE = some (.alu .add (17 : Fin 32) x0 (5 : Fin 32), 2) := by decide
theorem kc_at_1e0 : fetchRel sha256CompressCode 0x1E0 = some (.alu .add (5 : Fin 32) x0 (6 : Fin 32), 2) := by decide
theorem kc_at_1e2 : fetchRel sha256CompressCode 0x1E2 = some (.alu .add (25 : Fin 32) x0 a6, 2) := by decide
theorem kc_at_1e4 : fetchRel sha256CompressCode 0x1E4 = some (.alu .add a6 x0 (29 : Fin 32), 2) := by decide
theorem kc_at_1e6 : fetchRel sha256CompressCode 0x1E6 = some (.alu .add (29 : Fin 32) x0 (30 : Fin 32), 2) := by decide
theorem kc_at_1e8 : fetchRel sha256CompressCode 0x1E8 = some (.jal x0 0xFFFFFEEC, 2) := by decide
theorem kc_at_1ea : fetchRel sha256CompressCode 0x1EA = some (.load .lw (23 : Fin 32) sp 0x18, 2) := by decide
theorem kc_at_1ec : fetchRel sha256CompressCode 0x1EC = some (.alu .add (23 : Fin 32) (23 : Fin 32) (30 : Fin 32), 2) := by decide
theorem kc_at_1ee : fetchRel sha256CompressCode 0x1EE = some (.load .lw a0 sp 0x28, 2) := by decide
theorem kc_at_1f0 : fetchRel sha256CompressCode 0x1F0 = some (.alu .add a0 a0 (29 : Fin 32), 2) := by decide
theorem kc_at_1f2 : fetchRel sha256CompressCode 0x1F2 = some (.load .lw a1 sp 0x24, 2) := by decide
theorem kc_at_1f4 : fetchRel sha256CompressCode 0x1F4 = some (.alu .add a1 a1 a6, 2) := by decide
theorem kc_at_1f6 : fetchRel sha256CompressCode 0x1F6 = some (.load .lw a2 sp 0x14, 2) := by decide
theorem kc_at_1f8 : fetchRel sha256CompressCode 0x1F8 = some (.alu .add (25 : Fin 32) (25 : Fin 32) a2, 2) := by decide
theorem kc_at_1fa : fetchRel sha256CompressCode 0x1FA = some (.store .sw (18 : Fin 32) (23 : Fin 32) 0x0, 4) := by decide
theorem kc_at_1fe : fetchRel sha256CompressCode 0x1FE = some (.store .sw sp a0 0x28, 2) := by decide
theorem kc_at_200 : fetchRel sha256CompressCode 0x200 = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem kc_at_202 : fetchRel sha256CompressCode 0x202 = some (.store .sw a3 a0 0x4, 2) := by decide
theorem kc_at_204 : fetchRel sha256CompressCode 0x204 = some (.store .sw sp a1 0x24, 2) := by decide
theorem kc_at_206 : fetchRel sha256CompressCode 0x206 = some (.store .sw a3 a1 0x8, 2) := by decide
theorem kc_at_208 : fetchRel sha256CompressCode 0x208 = some (.store .sw (18 : Fin 32) (25 : Fin 32) 0xC, 4) := by decide
theorem kc_at_20c : fetchRel sha256CompressCode 0x20C = some (.load .lw a0 sp 0x10, 2) := by decide
theorem kc_at_20e : fetchRel sha256CompressCode 0x20E = some (.alu .add a0 a0 (6 : Fin 32), 2) := by decide
theorem kc_at_210 : fetchRel sha256CompressCode 0x210 = some (.load .lw a1 sp 0x20, 2) := by decide
theorem kc_at_212 : fetchRel sha256CompressCode 0x212 = some (.alu .add a1 a1 (5 : Fin 32), 2) := by decide
theorem kc_at_214 : fetchRel sha256CompressCode 0x214 = some (.load .lw a2 sp 0x1C, 2) := by decide
theorem kc_at_216 : fetchRel sha256CompressCode 0x216 = some (.alu .add a2 a2 (17 : Fin 32), 2) := by decide
theorem kc_at_218 : fetchRel sha256CompressCode 0x218 = some (.alu .add (24 : Fin 32) (24 : Fin 32) (26 : Fin 32), 2) := by decide
theorem kc_at_21a : fetchRel sha256CompressCode 0x21A = some (.alu .add (26 : Fin 32) x0 a0, 2) := by decide
theorem kc_at_21c : fetchRel sha256CompressCode 0x21C = some (.store .sw a3 a0 0x10, 2) := by decide
theorem kc_at_21e : fetchRel sha256CompressCode 0x21E = some (.store .sw sp a1 0x20, 2) := by decide
theorem kc_at_220 : fetchRel sha256CompressCode 0x220 = some (.store .sw a3 a1 0x14, 2) := by decide
theorem kc_at_222 : fetchRel sha256CompressCode 0x222 = some (.store .sw sp a2 0x1C, 2) := by decide
theorem kc_at_224 : fetchRel sha256CompressCode 0x224 = some (.store .sw a3 a2 0x18, 2) := by decide
theorem kc_at_226 : fetchRel sha256CompressCode 0x226 = some (.store .sw (18 : Fin 32) (24 : Fin 32) 0x1C, 4) := by decide
theorem kc_at_22a : fetchRel sha256CompressCode 0x22A = some (.load .lw (9 : Fin 32) sp 0xC, 2) := by decide
theorem kc_at_22c : fetchRel sha256CompressCode 0x22C = some (.jal x0 0xFFFFFE28, 2) := by decide
theorem kc_at_22e : fetchRel sha256CompressCode 0x22E = some (.load .lw ra sp 0xDC, 2) := by decide
theorem kc_at_230 : fetchRel sha256CompressCode 0x230 = some (.load .lw (8 : Fin 32) sp 0xD8, 2) := by decide
theorem kc_at_232 : fetchRel sha256CompressCode 0x232 = some (.load .lw (9 : Fin 32) sp 0xD4, 2) := by decide
theorem kc_at_234 : fetchRel sha256CompressCode 0x234 = some (.load .lw (18 : Fin 32) sp 0xD0, 2) := by decide
theorem kc_at_236 : fetchRel sha256CompressCode 0x236 = some (.load .lw (19 : Fin 32) sp 0xCC, 2) := by decide
theorem kc_at_238 : fetchRel sha256CompressCode 0x238 = some (.load .lw (20 : Fin 32) sp 0xC8, 2) := by decide
theorem kc_at_23a : fetchRel sha256CompressCode 0x23A = some (.load .lw (21 : Fin 32) sp 0xC4, 2) := by decide
theorem kc_at_23c : fetchRel sha256CompressCode 0x23C = some (.load .lw (22 : Fin 32) sp 0xC0, 2) := by decide
theorem kc_at_23e : fetchRel sha256CompressCode 0x23E = some (.load .lw (23 : Fin 32) sp 0xBC, 2) := by decide
theorem kc_at_240 : fetchRel sha256CompressCode 0x240 = some (.load .lw (24 : Fin 32) sp 0xB8, 2) := by decide
theorem kc_at_242 : fetchRel sha256CompressCode 0x242 = some (.load .lw (25 : Fin 32) sp 0xB4, 2) := by decide
theorem kc_at_244 : fetchRel sha256CompressCode 0x244 = some (.load .lw (26 : Fin 32) sp 0xB0, 2) := by decide
theorem kc_at_246 : fetchRel sha256CompressCode 0x246 = some (.load .lw (27 : Fin 32) sp 0xAC, 2) := by decide
theorem kc_at_248 : fetchRel sha256CompressCode 0x248 = some (.aluImm .add sp sp 0xE0, 2) := by decide
theorem kc_at_24a : fetchRel sha256CompressCode 0x24A = some (.jalr x0 ra 0x0, 2) := by decide
theorem kc_at_24c : fetchRel sha256CompressCode 0x24C = some (.alu .add a2 x0 a1, 2) := by decide
theorem kc_at_24e : fetchRel sha256CompressCode 0x24E = some (.aluImm .add a1 x0 0x4, 2) := by decide
theorem kc_at_250 : fetchRel sha256CompressCode 0x250 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem kc_at_252 : fetchRel sha256CompressCode 0x252 = some (.auipc ra 0xFFFF9000, 4) := by decide
theorem kc_at_256 : fetchRel sha256CompressCode 0x256 = some (.jalr ra ra 0x4, 4) := by decide

theorem rfi_at_0 : fetchRel rangeFromIndexCode 0x0 = some (.branch .bltu a2 a0 0xC, 4) := by decide
theorem rfi_at_4 : fetchRel rangeFromIndexCode 0x4 = some (.alu .sub a2 a2 a0, 2) := by decide
theorem rfi_at_6 : fetchRel rangeFromIndexCode 0x6 = some (.alu .add a0 a0 a1, 2) := by decide
theorem rfi_at_8 : fetchRel rangeFromIndexCode 0x8 = some (.alu .add a1 x0 a2, 2) := by decide
theorem rfi_at_a : fetchRel rangeFromIndexCode 0xA = some (.jalr x0 ra 0x0, 2) := by decide
theorem rfi_at_c : fetchRel rangeFromIndexCode 0xC = some (.alu .add a1 x0 a2, 2) := by decide
theorem rfi_at_e : fetchRel rangeFromIndexCode 0xE = some (.auipc ra 0xFFFF9000, 4) := by decide
theorem rfi_at_12 : fetchRel rangeFromIndexCode 0x12 = some (.jalr ra ra 0xFFFFFFEE, 4) := by decide

end

/-- The registers `compress256` saves in its frame, at offsets from its `sp`. -/
abbrev kcPs : List (Fin 32 × Word) :=
  [(ra, 0xDC), ((8 : Fin 32), 0xD8), ((9 : Fin 32), 0xD4), ((18 : Fin 32), 0xD0), ((19 : Fin 32), 0xCC),
   ((20 : Fin 32), 0xC8), ((21 : Fin 32), 0xC4), ((22 : Fin 32), 0xC0), ((23 : Fin 32), 0xBC),
   ((24 : Fin 32), 0xB8), ((25 : Fin 32), 0xB4), ((26 : Fin 32), 0xB0), ((27 : Fin 32), 0xAC)]

section
set_option maxRecDepth 20000
theorem kcSave_end : blockEnd sha256CompressCode 2 (saveBlock kcPs) = some 0x1C := by decide
theorem kcRestore_end : blockEnd sha256CompressCode 0x22E (restoreBlock kcPs) = some 0x248 := by decide
end

/-- `RangeFrom::index` on a 64-byte block: `&block[off..]` for `off ≤ 64`. -/
theorem rangeFromIndex_ok {B cur retAddr : Word} {off : Nat} {m : Machine}
    (hc : CodeIn m.mem B rangeFromIndexCode) (hpc : m.pc = B) (hoff : off ≤ 0x40)
    (ha0 : reg m a0 = BitVec.ofNat 32 off) (ha1 : reg m a1 = cur) (ha2 : reg m a2 = 0x40)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = m.mem ∧
      reg m' a0 = cur + BitVec.ofNat 32 off ∧ reg m' a1 = BitVec.ofNat 32 (0x40 - off) ∧
      reg m' a2 = BitVec.ofNat 32 (0x40 - off) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m' q = reg m q := by
  have s0 : St m.mem B m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hnb : branchTaken .bltu (reg m a2) (reg m a0) = false := by
    unfold branchTaken; rw [ha2, ha0]
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    have h64 : (0x40 : Word).toNat = 64 := rfl
    have ho : off % 2 ^ 32 = off := Nat.mod_eq_of_lt (by omega)
    rw [h64, ho]; exact decide_eq_false (by omega)
  obtain ⟨m1, d1, u1⟩ := s0.notTaken hc 4 rfi_at_0 (by decide) hnb
  obtain ⟨m2, d2, u2⟩ := u1.alu hc rfi_at_4 (off' := 6) (by decide)
  obtain ⟨m3, d3, u3⟩ := u2.alu hc rfi_at_6 (off' := 8) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.alu hc rfi_at_8 (off' := 0xA) (by decide)
  obtain ⟨m5, d5, pc5, mem5, regs5⟩ := u4.jalr hc rfi_at_a
  have sub_eq : (0x40 : Word) - BitVec.ofNat 32 off = BitVec.ofNat 32 (0x40 - off) := by
    apply BitVec.eq_of_toNat_eq
    have h64 : (0x40 : Word).toNat = 64 := rfl
    rw [BitVec.toNat_sub, h64, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine ⟨m5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), ?_, mem5, ?_, ?_, ?_, ?_⟩
  · rw [pc5]; simp +decide only [upd, ↓reduceIte]; rw [add_lit_zero, hra, hret]
  · rw [regs5]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ha0, ha1, BitVec.add_comm]
  · rw [regs5]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ha2, ha0, sub_eq]; exact BitVec.zero_add _
  · rw [regs5]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ha2, ha0, sub_eq]
  · intro q q0 q1 q2
    rw [regs5]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, s0.zero]
    · simp only [upd, h0, q0, q1, q2, ite_false]

set_option maxRecDepth 20000 in
/-- The round constants as the image stores them. -/
theorem kcK_words {M : Word → BitVec 8} (hk : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData) :
    ∀ t, t < 64 → memLoad32 M (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t)) = Sha256.k[t]! := by
  have he : ∀ t : Fin 64, (byteAt shaKData (4 * t.val + 3) ++ byteAt shaKData (4 * t.val + 2) ++
      byteAt shaKData (4 * t.val + 1) ++ byteAt shaKData (4 * t.val)) = Sha256.k[t.val]! := by decide +kernel
  intro t ht
  rw [← he ⟨t, ht⟩]
  unfold memLoad32
  have b0 := hk (4 * t) (by have : shaKData.length = 256 := rfl; omega)
  have b1 : M (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t) + 1) = byteAt shaKData (4 * t + 1) := by
    rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]
    exact hk _ (by have : shaKData.length = 256 := rfl; omega)
  have b2 : M (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t) + 2) = byteAt shaKData (4 * t + 2) := by
    rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]
    exact hk _ (by have : shaKData.length = 256 := rfl; omega)
  have b3 : M (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t) + 3) = byteAt shaKData (4 * t + 3) := by
    rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, add_ofNat_assoc]
    exact hk _ (by have : shaKData.length = 256 := rfl; omega)
  rw [b3, b2, b1, b0]

/-- Where `sha2::sha256::compress256` runs: its code at `P`, `RangeFrom::index`
and `memcpy` where the image puts them, the round constants at
`shaKAddress`, the 32-byte state at `stp`, `n` 64-byte blocks at `bp`
without wrapping, and the 0xE0-byte frame below `sp0`, apart from the code,
the constants, the state, and the blocks. -/
structure KCEnv (M : Word → BitVec 8) (P sp0 stp bp : Word) (n : Nat) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P sha256CompressCode
  idx : CodeIn M (P + 0x25A) rangeFromIndexCode
  stub : CodeIn M (P + 0x81C) memcpyStubCode
  body : CodeIn M (P + 0x824) memcpyBodyCode
  kdata : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  hsp : sp0.toNat % 4 = 0
  hS : 0xE0 ≤ sp0.toNat
  hstp : stp.toNat % 4 = 0
  hwbp : bp.toNat + 64 * n < 2 ^ 32
  sC : Sep (sp0 + 0xFFFFFF20) 0xE0 P sha256CompressCode.length
  sI : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0x25A) rangeFromIndexCode.length
  sU : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0x81C) memcpyStubCode.length
  sB : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0x824) memcpyBodyCode.length
  sK : Sep (sp0 + 0xFFFFFF20) 0xE0 (BitVec.ofNat 32 shaKAddress) 256
  stC : Sep stp 32 P sha256CompressCode.length
  stI : Sep stp 32 (P + 0x25A) rangeFromIndexCode.length
  stU : Sep stp 32 (P + 0x81C) memcpyStubCode.length
  stB : Sep stp 32 (P + 0x824) memcpyBodyCode.length
  stK : Sep stp 32 (BitVec.ofNat 32 shaKAddress) 256
  stF : Sep stp 32 (sp0 + 0xFFFFFF20) 0xE0
  bF : Sep bp (64 * n) (sp0 + 0xFFFFFF20) 0xE0
  bSt : Sep bp (64 * n) stp 32

end C3.RV32
