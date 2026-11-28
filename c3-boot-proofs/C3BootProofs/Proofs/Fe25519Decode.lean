import C3BootProofs.Proofs.Fe25519

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000

theorem fr_at_0 : fetchRel feReduceCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem fr_at_2 : fetchRel feReduceCode 0x2 = some (.store .sw sp (8 : Fin 32) 0x1C, 2) := by decide
theorem fr_at_4 : fetchRel feReduceCode 0x4 = some (.store .sw sp (9 : Fin 32) 0x18, 2) := by decide
theorem fr_at_6 : fetchRel feReduceCode 0x6 = some (.store .sw sp (18 : Fin 32) 0x14, 2) := by decide
theorem fr_at_8 : fetchRel feReduceCode 0x8 = some (.store .sw sp (19 : Fin 32) 0x10, 2) := by decide
theorem fr_at_a : fetchRel feReduceCode 0xA = some (.store .sw sp (20 : Fin 32) 0xC, 2) := by decide
theorem fr_at_c : fetchRel feReduceCode 0xC = some (.load .lw a6 a1 0x0, 4) := by decide
theorem fr_at_10 : fetchRel feReduceCode 0x10 = some (.load .lw (6 : Fin 32) a1 0x4, 4) := by decide
theorem fr_at_14 : fetchRel feReduceCode 0x14 = some (.lui (17 : Fin 32) 0x4000000, 4) := by decide
theorem fr_at_18 : fetchRel feReduceCode 0x18 = some (.load .lw a4 a1 0x8, 2) := by decide
theorem fr_at_1a : fetchRel feReduceCode 0x1A = some (.load .lw (5 : Fin 32) a1 0xC, 4) := by decide
theorem fr_at_1e : fetchRel feReduceCode 0x1E = some (.load .lw (7 : Fin 32) a1 0x20, 4) := by decide
theorem fr_at_22 : fetchRel feReduceCode 0x22 = some (.load .lw (28 : Fin 32) a1 0x24, 4) := by decide
theorem fr_at_26 : fetchRel feReduceCode 0x26 = some (.aluImm .sll a2 (6 : Fin 32) 0x6, 4) := by decide
theorem fr_at_2a : fetchRel feReduceCode 0x2A = some (.aluImm .srl a5 a6 0x1A, 4) := by decide
theorem fr_at_2e : fetchRel feReduceCode 0x2E = some (.aluImm .srl a3 (6 : Fin 32) 0x1A, 4) := by decide
theorem fr_at_32 : fetchRel feReduceCode 0x32 = some (.alu .or a2 a2 a5, 2) := by decide
theorem fr_at_34 : fetchRel feReduceCode 0x34 = some (.alu .add (6 : Fin 32) (5 : Fin 32) a3, 4) := by decide
theorem fr_at_38 : fetchRel feReduceCode 0x38 = some (.alu .add (5 : Fin 32) a4 a2, 4) := by decide
theorem fr_at_3c : fetchRel feReduceCode 0x3C = some (.load .lw a2 a1 0x28, 2) := by decide
theorem fr_at_3e : fetchRel feReduceCode 0x3E = some (.load .lw (30 : Fin 32) a1 0x2C, 4) := by decide
theorem fr_at_42 : fetchRel feReduceCode 0x42 = some (.alu .sltu a4 (5 : Fin 32) a4, 4) := by decide
theorem fr_at_46 : fetchRel feReduceCode 0x46 = some (.aluImm .sll a3 (28 : Fin 32) 0x6, 4) := by decide
theorem fr_at_4a : fetchRel feReduceCode 0x4A = some (.alu .add (31 : Fin 32) (6 : Fin 32) a4, 4) := by decide
theorem fr_at_4e : fetchRel feReduceCode 0x4E = some (.aluImm .srl a5 (7 : Fin 32) 0x1A, 4) := by decide
theorem fr_at_52 : fetchRel feReduceCode 0x52 = some (.aluImm .add (29 : Fin 32) (17 : Fin 32) 0xFFFFFFFF, 4) := by decide
theorem fr_at_56 : fetchRel feReduceCode 0x56 = some (.alu .or a3 a3 a5, 2) := by decide
theorem fr_at_58 : fetchRel feReduceCode 0x58 = some (.aluImm .srl a5 (28 : Fin 32) 0x1A, 4) := by decide
theorem fr_at_5c : fetchRel feReduceCode 0x5C = some (.alu .add (6 : Fin 32) a2 a3, 4) := by decide
theorem fr_at_60 : fetchRel feReduceCode 0x60 = some (.alu .add a5 a5 (30 : Fin 32), 2) := by decide
theorem fr_at_62 : fetchRel feReduceCode 0x62 = some (.alu .sltu a2 (6 : Fin 32) a2, 4) := by decide
theorem fr_at_66 : fetchRel feReduceCode 0x66 = some (.alu .add a2 a2 a5, 2) := by decide
theorem fr_at_68 : fetchRel feReduceCode 0x68 = some (.alu .and (17 : Fin 32) (7 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fr_at_6c : fetchRel feReduceCode 0x6C = some (.load .lw (8 : Fin 32) a1 0x10, 2) := by decide
theorem fr_at_6e : fetchRel feReduceCode 0x6E = some (.load .lw (7 : Fin 32) a1 0x14, 4) := by decide
theorem fr_at_72 : fetchRel feReduceCode 0x72 = some (.aluImm .sll a4 (31 : Fin 32) 0x7, 4) := by decide
theorem fr_at_76 : fetchRel feReduceCode 0x76 = some (.aluImm .srl a5 (5 : Fin 32) 0x19, 4) := by decide
theorem fr_at_7a : fetchRel feReduceCode 0x7A = some (.alu .or a4 a4 a5, 2) := by decide
theorem fr_at_7c : fetchRel feReduceCode 0x7C = some (.aluImm .srl a5 (31 : Fin 32) 0x19, 4) := by decide
theorem fr_at_80 : fetchRel feReduceCode 0x80 = some (.load .lw (28 : Fin 32) a1 0x18, 4) := by decide
theorem fr_at_84 : fetchRel feReduceCode 0x84 = some (.load .lw (30 : Fin 32) a1 0x1C, 4) := by decide
theorem fr_at_88 : fetchRel feReduceCode 0x88 = some (.alu .add (31 : Fin 32) (7 : Fin 32) a5, 4) := by decide
theorem fr_at_8c : fetchRel feReduceCode 0x8C = some (.alu .add (7 : Fin 32) (8 : Fin 32) a4, 4) := by decide
theorem fr_at_90 : fetchRel feReduceCode 0x90 = some (.aluImm .sll a4 a2 0x7, 4) := by decide
theorem fr_at_94 : fetchRel feReduceCode 0x94 = some (.load .lw a3 a1 0x30, 2) := by decide
theorem fr_at_96 : fetchRel feReduceCode 0x96 = some (.aluImm .srl a5 (6 : Fin 32) 0x19, 4) := by decide
theorem fr_at_9a : fetchRel feReduceCode 0x9A = some (.load .lw (9 : Fin 32) a1 0x34, 2) := by decide
theorem fr_at_9c : fetchRel feReduceCode 0x9C = some (.alu .sltu (8 : Fin 32) (7 : Fin 32) (8 : Fin 32), 4) := by decide
theorem fr_at_a0 : fetchRel feReduceCode 0xA0 = some (.alu .or a4 a4 a5, 2) := by decide
theorem fr_at_a2 : fetchRel feReduceCode 0xA2 = some (.aluImm .srl a2 a2 0x19, 2) := by decide
theorem fr_at_a4 : fetchRel feReduceCode 0xA4 = some (.load .lw a5 a1 0x38, 2) := by decide
theorem fr_at_a6 : fetchRel feReduceCode 0xA6 = some (.load .lw (18 : Fin 32) a1 0x3C, 4) := by decide
theorem fr_at_aa : fetchRel feReduceCode 0xAA = some (.alu .add (19 : Fin 32) a3 a4, 4) := by decide
theorem fr_at_ae : fetchRel feReduceCode 0xAE = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem fr_at_b0 : fetchRel feReduceCode 0xB0 = some (.alu .sltu a3 (19 : Fin 32) a3, 4) := by decide
theorem fr_at_b4 : fetchRel feReduceCode 0xB4 = some (.alu .add (31 : Fin 32) (31 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fr_at_b6 : fetchRel feReduceCode 0xB6 = some (.alu .add a2 a2 a3, 2) := by decide
theorem fr_at_b8 : fetchRel feReduceCode 0xB8 = some (.aluImm .sll a3 (31 : Fin 32) 0x6, 4) := by decide
theorem fr_at_bc : fetchRel feReduceCode 0xBC = some (.aluImm .srl (8 : Fin 32) (7 : Fin 32) 0x1A, 4) := by decide
theorem fr_at_c0 : fetchRel feReduceCode 0xC0 = some (.alu .or (8 : Fin 32) (8 : Fin 32) a3, 2) := by decide
theorem fr_at_c2 : fetchRel feReduceCode 0xC2 = some (.aluImm .srl a3 (31 : Fin 32) 0x1A, 4) := by decide
theorem fr_at_c6 : fetchRel feReduceCode 0xC6 = some (.aluImm .sll (9 : Fin 32) a2 0x6, 4) := by decide
theorem fr_at_ca : fetchRel feReduceCode 0xCA = some (.aluImm .srl a4 (19 : Fin 32) 0x1A, 4) := by decide
theorem fr_at_ce : fetchRel feReduceCode 0xCE = some (.alu .add (30 : Fin 32) (30 : Fin 32) a3, 2) := by decide
theorem fr_at_d0 : fetchRel feReduceCode 0xD0 = some (.alu .or a3 a4 (9 : Fin 32), 4) := by decide
theorem fr_at_d4 : fetchRel feReduceCode 0xD4 = some (.aluImm .srl a2 a2 0x1A, 2) := by decide
theorem fr_at_d6 : fetchRel feReduceCode 0xD6 = some (.alu .add (31 : Fin 32) a5 a3, 4) := by decide
theorem fr_at_da : fetchRel feReduceCode 0xDA = some (.alu .add (18 : Fin 32) (18 : Fin 32) a2, 2) := by decide
theorem fr_at_dc : fetchRel feReduceCode 0xDC = some (.alu .sltu a4 (31 : Fin 32) a5, 4) := by decide
theorem fr_at_e0 : fetchRel feReduceCode 0xE0 = some (.alu .add (20 : Fin 32) (28 : Fin 32) (8 : Fin 32), 4) := by decide
theorem fr_at_e4 : fetchRel feReduceCode 0xE4 = some (.alu .add a4 a4 (18 : Fin 32), 2) := by decide
theorem fr_at_e6 : fetchRel feReduceCode 0xE6 = some (.aluImm .sll a5 a4 0x7, 4) := by decide
theorem fr_at_ea : fetchRel feReduceCode 0xEA = some (.load .lw (9 : Fin 32) a1 0x40, 2) := by decide
theorem fr_at_ec : fetchRel feReduceCode 0xEC = some (.aluImm .srl a3 (31 : Fin 32) 0x19, 4) := by decide
theorem fr_at_f0 : fetchRel feReduceCode 0xF0 = some (.load .lw a2 a1 0x44, 2) := by decide
theorem fr_at_f2 : fetchRel feReduceCode 0xF2 = some (.alu .sltu (28 : Fin 32) (20 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fr_at_f6 : fetchRel feReduceCode 0xF6 = some (.alu .or a3 a3 a5, 2) := by decide
theorem fr_at_f8 : fetchRel feReduceCode 0xF8 = some (.aluImm .srl a4 a4 0x19, 2) := by decide
theorem fr_at_fa : fetchRel feReduceCode 0xFA = some (.load .lw a5 a1 0x48, 2) := by decide
theorem fr_at_fc : fetchRel feReduceCode 0xFC = some (.load .lw a1 a1 0x4C, 2) := by decide
theorem fr_at_fe : fetchRel feReduceCode 0xFE = some (.alu .add (18 : Fin 32) (9 : Fin 32) a3, 4) := by decide
theorem fr_at_102 : fetchRel feReduceCode 0x102 = some (.alu .add a4 a4 a2, 2) := by decide
theorem fr_at_104 : fetchRel feReduceCode 0x104 = some (.alu .sltu (9 : Fin 32) (18 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fr_at_108 : fetchRel feReduceCode 0x108 = some (.alu .add a2 (30 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fr_at_10c : fetchRel feReduceCode 0x10C = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem fr_at_10e : fetchRel feReduceCode 0x10E = some (.aluImm .sll (9 : Fin 32) a4 0x6, 4) := by decide
theorem fr_at_112 : fetchRel feReduceCode 0x112 = some (.aluImm .srl a3 (18 : Fin 32) 0x1A, 4) := by decide
theorem fr_at_116 : fetchRel feReduceCode 0x116 = some (.aluImm .sll (8 : Fin 32) a2 0x7, 4) := by decide
theorem fr_at_11a : fetchRel feReduceCode 0x11A = some (.alu .or a3 a3 (9 : Fin 32), 2) := by decide
theorem fr_at_11c : fetchRel feReduceCode 0x11C = some (.aluImm .srl a4 a4 0x1A, 2) := by decide
theorem fr_at_11e : fetchRel feReduceCode 0x11E = some (.alu .add (9 : Fin 32) a5 a3, 4) := by decide
theorem fr_at_122 : fetchRel feReduceCode 0x122 = some (.alu .add a1 a1 a4, 2) := by decide
theorem fr_at_124 : fetchRel feReduceCode 0x124 = some (.alu .sltu a4 (9 : Fin 32) a5, 4) := by decide
theorem fr_at_128 : fetchRel feReduceCode 0x128 = some (.aluImm .srl a5 (20 : Fin 32) 0x19, 4) := by decide
theorem fr_at_12c : fetchRel feReduceCode 0x12C = some (.alu .add a1 a1 a4, 2) := by decide
theorem fr_at_12e : fetchRel feReduceCode 0x12E = some (.aluImm .sll a4 a1 0x7, 4) := by decide
theorem fr_at_132 : fetchRel feReduceCode 0x132 = some (.aluImm .srl a3 (9 : Fin 32) 0x19, 4) := by decide
theorem fr_at_136 : fetchRel feReduceCode 0x136 = some (.alu .or a5 a5 (8 : Fin 32), 2) := by decide
theorem fr_at_138 : fetchRel feReduceCode 0x138 = some (.alu .or a3 a3 a4, 2) := by decide
theorem fr_at_13a : fetchRel feReduceCode 0x13A = some (.aluImm .srl a1 a1 0x19, 2) := by decide
theorem fr_at_13c : fetchRel feReduceCode 0x13C = some (.aluImm .add a4 x0 0x13, 2) := by decide
theorem fr_at_13e : fetchRel feReduceCode 0x13E = some (.alu .mul (28 : Fin 32) a1 a4, 4) := by decide
theorem fr_at_142 : fetchRel feReduceCode 0x142 = some (.alu .mul (8 : Fin 32) a3 a4, 4) := by decide
theorem fr_at_146 : fetchRel feReduceCode 0x146 = some (.alu .mulhu a3 a3 a4, 4) := by decide
theorem fr_at_14a : fetchRel feReduceCode 0x14A = some (.alu .add a5 a5 (17 : Fin 32), 2) := by decide
theorem fr_at_14c : fetchRel feReduceCode 0x14C = some (.aluImm .srl a2 a2 0x19, 2) := by decide
theorem fr_at_14e : fetchRel feReduceCode 0x14E = some (.alu .sltu a4 a5 (17 : Fin 32), 4) := by decide
theorem fr_at_152 : fetchRel feReduceCode 0x152 = some (.alu .add a2 a2 a4, 2) := by decide
theorem fr_at_154 : fetchRel feReduceCode 0x154 = some (.lui (17 : Fin 32) 0x2000000, 4) := by decide
theorem fr_at_158 : fetchRel feReduceCode 0x158 = some (.alu .and a4 a6 (29 : Fin 32), 4) := by decide
theorem fr_at_15c : fetchRel feReduceCode 0x15C = some (.aluImm .add (17 : Fin 32) (17 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem fr_at_15e : fetchRel feReduceCode 0x15E = some (.alu .and a6 (5 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fr_at_162 : fetchRel feReduceCode 0x162 = some (.alu .and (5 : Fin 32) (6 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fr_at_166 : fetchRel feReduceCode 0x166 = some (.aluImm .sll a2 a2 0x6, 2) := by decide
theorem fr_at_168 : fetchRel feReduceCode 0x168 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem fr_at_16a : fetchRel feReduceCode 0x16A = some (.alu .add a3 a3 (28 : Fin 32), 2) := by decide
theorem fr_at_16c : fetchRel feReduceCode 0x16C = some (.alu .sltu (8 : Fin 32) a4 (8 : Fin 32), 4) := by decide
theorem fr_at_170 : fetchRel feReduceCode 0x170 = some (.aluImm .srl a1 a5 0x1A, 4) := by decide
theorem fr_at_174 : fetchRel feReduceCode 0x174 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem fr_at_176 : fetchRel feReduceCode 0x176 = some (.aluImm .sll a3 a3 0x6, 2) := by decide
theorem fr_at_178 : fetchRel feReduceCode 0x178 = some (.aluImm .srl (8 : Fin 32) a4 0x1A, 4) := by decide
theorem fr_at_17c : fetchRel feReduceCode 0x17C = some (.alu .or a1 a1 a2, 2) := by decide
theorem fr_at_17e : fetchRel feReduceCode 0x17E = some (.alu .or a3 a3 (8 : Fin 32), 2) := by decide
theorem fr_at_180 : fetchRel feReduceCode 0x180 = some (.alu .add (5 : Fin 32) (5 : Fin 32) a1, 2) := by decide
theorem fr_at_182 : fetchRel feReduceCode 0x182 = some (.alu .add a3 a3 a6, 2) := by decide
theorem fr_at_184 : fetchRel feReduceCode 0x184 = some (.alu .and a2 a4 (29 : Fin 32), 4) := by decide
theorem fr_at_188 : fetchRel feReduceCode 0x188 = some (.alu .and a4 (7 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fr_at_18c : fetchRel feReduceCode 0x18C = some (.alu .and (8 : Fin 32) (20 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fr_at_190 : fetchRel feReduceCode 0x190 = some (.alu .and a5 a5 (29 : Fin 32), 4) := by decide
theorem fr_at_194 : fetchRel feReduceCode 0x194 = some (.alu .and a1 (19 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fr_at_198 : fetchRel feReduceCode 0x198 = some (.alu .and a6 (31 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fr_at_19c : fetchRel feReduceCode 0x19C = some (.alu .and (6 : Fin 32) (18 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fr_at_1a0 : fetchRel feReduceCode 0x1A0 = some (.alu .and (9 : Fin 32) (9 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fr_at_1a4 : fetchRel feReduceCode 0x1A4 = some (.store .sw a0 a2 0x0, 2) := by decide
theorem fr_at_1a6 : fetchRel feReduceCode 0x1A6 = some (.store .sw a0 a3 0x4, 2) := by decide
theorem fr_at_1a8 : fetchRel feReduceCode 0x1A8 = some (.store .sw a0 a4 0x8, 2) := by decide
theorem fr_at_1aa : fetchRel feReduceCode 0x1AA = some (.store .sw a0 (8 : Fin 32) 0xC, 2) := by decide
theorem fr_at_1ac : fetchRel feReduceCode 0x1AC = some (.store .sw a0 a5 0x10, 2) := by decide
theorem fr_at_1ae : fetchRel feReduceCode 0x1AE = some (.store .sw a0 (5 : Fin 32) 0x14, 4) := by decide
theorem fr_at_1b2 : fetchRel feReduceCode 0x1B2 = some (.store .sw a0 a1 0x18, 2) := by decide
theorem fr_at_1b4 : fetchRel feReduceCode 0x1B4 = some (.store .sw a0 a6 0x1C, 4) := by decide
theorem fr_at_1b8 : fetchRel feReduceCode 0x1B8 = some (.store .sw a0 (6 : Fin 32) 0x20, 4) := by decide
theorem fr_at_1bc : fetchRel feReduceCode 0x1BC = some (.store .sw a0 (9 : Fin 32) 0x24, 2) := by decide
theorem fr_at_1be : fetchRel feReduceCode 0x1BE = some (.load .lw (8 : Fin 32) sp 0x1C, 2) := by decide
theorem fr_at_1c0 : fetchRel feReduceCode 0x1C0 = some (.load .lw (9 : Fin 32) sp 0x18, 2) := by decide
theorem fr_at_1c2 : fetchRel feReduceCode 0x1C2 = some (.load .lw (18 : Fin 32) sp 0x14, 2) := by decide
theorem fr_at_1c4 : fetchRel feReduceCode 0x1C4 = some (.load .lw (19 : Fin 32) sp 0x10, 2) := by decide
theorem fr_at_1c6 : fetchRel feReduceCode 0x1C6 = some (.load .lw (20 : Fin 32) sp 0xC, 2) := by decide
theorem fr_at_1c8 : fetchRel feReduceCode 0x1C8 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem fr_at_1ca : fetchRel feReduceCode 0x1CA = some (.jalr x0 ra 0x0, 2) := by decide


theorem fmu_at_0 : fetchRel feMulCode 0x0 = some (.aluImm .add sp sp 0xFFFFFEE0, 2) := by decide
theorem fmu_at_2 : fetchRel feMulCode 0x2 = some (.aluImm .add a3 sp 0x100, 2) := by decide
theorem fmu_at_4 : fetchRel feMulCode 0x4 = some (.store .sw a3 ra 0x1C, 4) := by decide
theorem fmu_at_8 : fetchRel feMulCode 0x8 = some (.store .sw a3 (8 : Fin 32) 0x18, 2) := by decide
theorem fmu_at_a : fetchRel feMulCode 0xA = some (.store .sw a3 (9 : Fin 32) 0x14, 2) := by decide
theorem fmu_at_c : fetchRel feMulCode 0xC = some (.store .sw a3 (18 : Fin 32) 0x10, 4) := by decide
theorem fmu_at_10 : fetchRel feMulCode 0x10 = some (.store .sw a3 (19 : Fin 32) 0xC, 4) := by decide
theorem fmu_at_14 : fetchRel feMulCode 0x14 = some (.store .sw a3 (20 : Fin 32) 0x8, 4) := by decide
theorem fmu_at_18 : fetchRel feMulCode 0x18 = some (.store .sw a3 (21 : Fin 32) 0x4, 4) := by decide
theorem fmu_at_1c : fetchRel feMulCode 0x1C = some (.store .sw a3 (22 : Fin 32) 0x0, 4) := by decide
theorem fmu_at_20 : fetchRel feMulCode 0x20 = some (.store .sw sp (23 : Fin 32) 0xFC, 2) := by decide
theorem fmu_at_22 : fetchRel feMulCode 0x22 = some (.store .sw sp (24 : Fin 32) 0xF8, 2) := by decide
theorem fmu_at_24 : fetchRel feMulCode 0x24 = some (.store .sw sp (25 : Fin 32) 0xF4, 2) := by decide
theorem fmu_at_26 : fetchRel feMulCode 0x26 = some (.store .sw sp (26 : Fin 32) 0xF0, 2) := by decide
theorem fmu_at_28 : fetchRel feMulCode 0x28 = some (.store .sw sp (27 : Fin 32) 0xEC, 2) := by decide
theorem fmu_at_2a : fetchRel feMulCode 0x2A = some (.store .sw sp a0 0x58, 2) := by decide
theorem fmu_at_2c : fetchRel feMulCode 0x2C = some (.load .lw a0 a2 0x24, 2) := by decide
theorem fmu_at_2e : fetchRel feMulCode 0x2E = some (.store .sw sp a0 0x54, 2) := by decide
theorem fmu_at_30 : fetchRel feMulCode 0x30 = some (.load .lw a3 a2 0x1C, 2) := by decide
theorem fmu_at_32 : fetchRel feMulCode 0x32 = some (.store .sw sp a3 0x44, 2) := by decide
theorem fmu_at_34 : fetchRel feMulCode 0x34 = some (.aluImm .add (6 : Fin 32) x0 0x13, 2) := by decide
theorem fmu_at_36 : fetchRel feMulCode 0x36 = some (.load .lw a4 a2 0x14, 2) := by decide
theorem fmu_at_38 : fetchRel feMulCode 0x38 = some (.store .sw sp a4 0x2C, 2) := by decide
theorem fmu_at_3a : fetchRel feMulCode 0x3A = some (.alu .mul (8 : Fin 32) a0 (6 : Fin 32), 4) := by decide
theorem fmu_at_3e : fetchRel feMulCode 0x3E = some (.store .sw sp (8 : Fin 32) 0x70, 2) := by decide
theorem fmu_at_40 : fetchRel feMulCode 0x40 = some (.alu .mul (28 : Fin 32) a3 (6 : Fin 32), 4) := by decide
theorem fmu_at_44 : fetchRel feMulCode 0x44 = some (.store .sw sp (28 : Fin 32) 0x60, 2) := by decide
theorem fmu_at_46 : fetchRel feMulCode 0x46 = some (.load .lw a3 a1 0x4, 2) := by decide
theorem fmu_at_48 : fetchRel feMulCode 0x48 = some (.store .sw sp a3 0x94, 2) := by decide
theorem fmu_at_4a : fetchRel feMulCode 0x4A = some (.load .lw (23 : Fin 32) a1 0xC, 4) := by decide
theorem fmu_at_4e : fetchRel feMulCode 0x4E = some (.load .lw (30 : Fin 32) a2 0x18, 4) := by decide
theorem fmu_at_52 : fetchRel feMulCode 0x52 = some (.store .sw sp (30 : Fin 32) 0x30, 2) := by decide
theorem fmu_at_54 : fetchRel feMulCode 0x54 = some (.alu .mul (27 : Fin 32) a4 (6 : Fin 32), 4) := by decide
theorem fmu_at_58 : fetchRel feMulCode 0x58 = some (.load .lw (5 : Fin 32) a1 0x8, 4) := by decide
theorem fmu_at_5c : fetchRel feMulCode 0x5C = some (.load .lw (29 : Fin 32) a1 0x14, 4) := by decide
theorem fmu_at_60 : fetchRel feMulCode 0x60 = some (.load .lw a4 a2 0xC, 2) := by decide
theorem fmu_at_62 : fetchRel feMulCode 0x62 = some (.store .sw sp a4 0x6C, 2) := by decide
theorem fmu_at_64 : fetchRel feMulCode 0x64 = some (.aluImm .sll a3 a3 0x1, 2) := by decide
theorem fmu_at_66 : fetchRel feMulCode 0x66 = some (.aluImm .sll (9 : Fin 32) (23 : Fin 32) 0x1, 4) := by decide
theorem fmu_at_6a : fetchRel feMulCode 0x6A = some (.alu .mulhu a6 a3 (8 : Fin 32), 4) := by decide
theorem fmu_at_6e : fetchRel feMulCode 0x6E = some (.store .sw sp a3 0x74, 2) := by decide
theorem fmu_at_70 : fetchRel feMulCode 0x70 = some (.alu .mulhu (7 : Fin 32) (9 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_74 : fetchRel feMulCode 0x74 = some (.store .sw sp (9 : Fin 32) 0x78, 2) := by decide
theorem fmu_at_76 : fetchRel feMulCode 0x76 = some (.load .lw ra a1 0x18, 4) := by decide
theorem fmu_at_7a : fetchRel feMulCode 0x7A = some (.load .lw (24 : Fin 32) a1 0x1C, 4) := by decide
theorem fmu_at_7e : fetchRel feMulCode 0x7E = some (.aluImm .sll a0 (29 : Fin 32) 0x1, 4) := by decide
theorem fmu_at_82 : fetchRel feMulCode 0x82 = some (.store .sw sp a0 0x80, 2) := by decide
theorem fmu_at_84 : fetchRel feMulCode 0x84 = some (.load .lw a5 a2 0x4, 2) := by decide
theorem fmu_at_86 : fetchRel feMulCode 0x86 = some (.store .sw sp a5 0x5C, 2) := by decide
theorem fmu_at_88 : fetchRel feMulCode 0x88 = some (.alu .mulhu (17 : Fin 32) a0 (27 : Fin 32), 4) := by decide
theorem fmu_at_8c : fetchRel feMulCode 0x8C = some (.alu .mul (31 : Fin 32) a3 (8 : Fin 32), 4) := by decide
theorem fmu_at_90 : fetchRel feMulCode 0x90 = some (.alu .mul (8 : Fin 32) (9 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_94 : fetchRel feMulCode 0x94 = some (.alu .mul (18 : Fin 32) a4 (6 : Fin 32), 4) := by decide
theorem fmu_at_98 : fetchRel feMulCode 0x98 = some (.alu .mul (28 : Fin 32) a0 (27 : Fin 32), 4) := by decide
theorem fmu_at_9c : fetchRel feMulCode 0x9C = some (.alu .add a6 a6 (7 : Fin 32), 2) := by decide
theorem fmu_at_9e : fetchRel feMulCode 0x9E = some (.load .lw (7 : Fin 32) a2 0x8, 4) := by decide
theorem fmu_at_a2 : fetchRel feMulCode 0xA2 = some (.store .sw sp (7 : Fin 32) 0x64, 2) := by decide
theorem fmu_at_a4 : fetchRel feMulCode 0xA4 = some (.alu .mul (9 : Fin 32) a5 (6 : Fin 32), 4) := by decide
theorem fmu_at_a8 : fetchRel feMulCode 0xA8 = some (.alu .add a5 a6 (17 : Fin 32), 4) := by decide
theorem fmu_at_ac : fetchRel feMulCode 0xAC = some (.load .lw (25 : Fin 32) a1 0x24, 4) := by decide
theorem fmu_at_b0 : fetchRel feMulCode 0xB0 = some (.alu .add a3 (8 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fmu_at_b4 : fetchRel feMulCode 0xB4 = some (.aluImm .sll a4 (24 : Fin 32) 0x1, 4) := by decide
theorem fmu_at_b8 : fetchRel feMulCode 0xB8 = some (.store .sw sp a4 0x7C, 2) := by decide
theorem fmu_at_ba : fetchRel feMulCode 0xBA = some (.alu .sltu (8 : Fin 32) a3 (8 : Fin 32), 4) := by decide
theorem fmu_at_be : fetchRel feMulCode 0xBE = some (.alu .mul a6 a4 (18 : Fin 32), 4) := by decide
theorem fmu_at_c2 : fetchRel feMulCode 0xC2 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem fmu_at_c4 : fetchRel feMulCode 0xC4 = some (.alu .add (28 : Fin 32) (28 : Fin 32) a3, 2) := by decide
theorem fmu_at_c6 : fetchRel feMulCode 0xC6 = some (.load .lw (8 : Fin 32) a2 0x20, 2) := by decide
theorem fmu_at_c8 : fetchRel feMulCode 0xC8 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem fmu_at_ca : fetchRel feMulCode 0xCA = some (.aluImm .sll a0 (25 : Fin 32) 0x1, 4) := by decide
theorem fmu_at_ce : fetchRel feMulCode 0xCE = some (.store .sw sp a0 0x88, 2) := by decide
theorem fmu_at_d0 : fetchRel feMulCode 0xD0 = some (.alu .mulhu (31 : Fin 32) a4 (18 : Fin 32), 4) := by decide
theorem fmu_at_d4 : fetchRel feMulCode 0xD4 = some (.alu .mulhu a4 a0 (9 : Fin 32), 4) := by decide
theorem fmu_at_d8 : fetchRel feMulCode 0xD8 = some (.load .lw (21 : Fin 32) a1 0x0, 4) := by decide
theorem fmu_at_dc : fetchRel feMulCode 0xDC = some (.load .lw (20 : Fin 32) a2 0x0, 4) := by decide
theorem fmu_at_e0 : fetchRel feMulCode 0xE0 = some (.alu .mul (17 : Fin 32) a0 (9 : Fin 32), 4) := by decide
theorem fmu_at_e4 : fetchRel feMulCode 0xE4 = some (.alu .sltu a3 (28 : Fin 32) a3, 4) := by decide
theorem fmu_at_e8 : fetchRel feMulCode 0xE8 = some (.alu .add a6 a6 (28 : Fin 32), 2) := by decide
theorem fmu_at_ea : fetchRel feMulCode 0xEA = some (.alu .mul (26 : Fin 32) (8 : Fin 32) (6 : Fin 32), 4) := by decide
theorem fmu_at_ee : fetchRel feMulCode 0xEE = some (.alu .add a5 a5 a3, 2) := by decide
theorem fmu_at_f0 : fetchRel feMulCode 0xF0 = some (.alu .sltu (9 : Fin 32) a6 (28 : Fin 32), 4) := by decide
theorem fmu_at_f4 : fetchRel feMulCode 0xF4 = some (.alu .mul (19 : Fin 32) (30 : Fin 32) (6 : Fin 32), 4) := by decide
theorem fmu_at_f8 : fetchRel feMulCode 0xF8 = some (.alu .mulhu (28 : Fin 32) (20 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fmu_at_fc : fetchRel feMulCode 0xFC = some (.alu .add a0 a5 (31 : Fin 32), 4) := by decide
theorem fmu_at_100 : fetchRel feMulCode 0x100 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem fmu_at_102 : fetchRel feMulCode 0x102 = some (.load .lw (22 : Fin 32) a1 0x10, 4) := by decide
theorem fmu_at_106 : fetchRel feMulCode 0x106 = some (.alu .mul a3 (20 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fmu_at_10a : fetchRel feMulCode 0x10A = some (.load .lw (9 : Fin 32) a2 0x10, 2) := by decide
theorem fmu_at_10c : fetchRel feMulCode 0x10C = some (.store .sw sp (9 : Fin 32) 0x18, 2) := by decide
theorem fmu_at_10e : fetchRel feMulCode 0x10E = some (.alu .add (17 : Fin 32) (17 : Fin 32) a6, 2) := by decide
theorem fmu_at_110 : fetchRel feMulCode 0x110 = some (.alu .add a2 x0 (5 : Fin 32), 2) := by decide
theorem fmu_at_112 : fetchRel feMulCode 0x112 = some (.store .sw sp (5 : Fin 32) 0x8, 2) := by decide
theorem fmu_at_114 : fetchRel feMulCode 0x114 = some (.alu .mul (5 : Fin 32) (5 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_118 : fetchRel feMulCode 0x118 = some (.alu .mulhu a2 a2 (26 : Fin 32), 4) := by decide
theorem fmu_at_11c : fetchRel feMulCode 0x11C = some (.alu .add a0 a0 a4, 2) := by decide
theorem fmu_at_11e : fetchRel feMulCode 0x11E = some (.alu .sltu a4 (17 : Fin 32) a6, 4) := by decide
theorem fmu_at_122 : fetchRel feMulCode 0x122 = some (.alu .add a4 a4 (28 : Fin 32), 2) := by decide
theorem fmu_at_124 : fetchRel feMulCode 0x124 = some (.alu .mulhu a6 (22 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_128 : fetchRel feMulCode 0x128 = some (.alu .add a0 a0 a4, 2) := by decide
theorem fmu_at_12a : fetchRel feMulCode 0x12A = some (.alu .mul (30 : Fin 32) (9 : Fin 32) (6 : Fin 32), 4) := by decide
theorem fmu_at_12e : fetchRel feMulCode 0x12E = some (.alu .add a3 a3 (17 : Fin 32), 2) := by decide
theorem fmu_at_130 : fetchRel feMulCode 0x130 = some (.alu .mul a5 (22 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_134 : fetchRel feMulCode 0x134 = some (.alu .mul a4 (7 : Fin 32) (6 : Fin 32), 4) := by decide
theorem fmu_at_138 : fetchRel feMulCode 0x138 = some (.alu .sltu (8 : Fin 32) a3 (17 : Fin 32), 4) := by decide
theorem fmu_at_13c : fetchRel feMulCode 0x13C = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem fmu_at_13e : fetchRel feMulCode 0x13E = some (.alu .add (5 : Fin 32) (5 : Fin 32) a3, 2) := by decide
theorem fmu_at_140 : fetchRel feMulCode 0x140 = some (.load .lw (31 : Fin 32) a1 0x20, 4) := by decide
theorem fmu_at_144 : fetchRel feMulCode 0x144 = some (.alu .sltu a3 (5 : Fin 32) a3, 4) := by decide
theorem fmu_at_148 : fetchRel feMulCode 0x148 = some (.alu .add a2 a2 a0, 2) := by decide
theorem fmu_at_14a : fetchRel feMulCode 0x14A = some (.alu .add a3 a3 a6, 2) := by decide
theorem fmu_at_14c : fetchRel feMulCode 0x14C = some (.alu .mul (28 : Fin 32) ra (30 : Fin 32), 4) := by decide
theorem fmu_at_150 : fetchRel feMulCode 0x150 = some (.alu .mulhu (8 : Fin 32) ra (30 : Fin 32), 4) := by decide
theorem fmu_at_154 : fetchRel feMulCode 0x154 = some (.alu .add (7 : Fin 32) a2 a3, 4) := by decide
theorem fmu_at_158 : fetchRel feMulCode 0x158 = some (.alu .add a5 a5 (5 : Fin 32), 2) := by decide
theorem fmu_at_15a : fetchRel feMulCode 0x15A = some (.alu .sltu (5 : Fin 32) a5 (5 : Fin 32), 4) := by decide
theorem fmu_at_15e : fetchRel feMulCode 0x15E = some (.alu .mulhu (6 : Fin 32) (31 : Fin 32) a4, 4) := by decide
theorem fmu_at_162 : fetchRel feMulCode 0x162 = some (.store .sw sp (23 : Fin 32) 0x90, 2) := by decide
theorem fmu_at_164 : fetchRel feMulCode 0x164 = some (.alu .mulhu a6 (23 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_168 : fetchRel feMulCode 0x168 = some (.store .sw sp (29 : Fin 32) 0x68, 2) := by decide
theorem fmu_at_16a : fetchRel feMulCode 0x16A = some (.alu .mulhu a2 (29 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_16e : fetchRel feMulCode 0x16E = some (.alu .mul (17 : Fin 32) (31 : Fin 32) a4, 4) := by decide
theorem fmu_at_172 : fetchRel feMulCode 0x172 = some (.store .sw sp (24 : Fin 32) 0x8C, 2) := by decide
theorem fmu_at_174 : fetchRel feMulCode 0x174 = some (.alu .mulhu a1 (24 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fmu_at_178 : fetchRel feMulCode 0x178 = some (.alu .mul a3 (23 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_17c : fetchRel feMulCode 0x17C = some (.alu .mul a0 (29 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_180 : fetchRel feMulCode 0x180 = some (.alu .add (5 : Fin 32) (5 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fmu_at_182 : fetchRel feMulCode 0x182 = some (.alu .add (28 : Fin 32) (28 : Fin 32) a5, 2) := by decide
theorem fmu_at_184 : fetchRel feMulCode 0x184 = some (.alu .add (5 : Fin 32) (5 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fmu_at_186 : fetchRel feMulCode 0x186 = some (.alu .sltu a5 (28 : Fin 32) a5, 4) := by decide
theorem fmu_at_18a : fetchRel feMulCode 0x18A = some (.alu .add a5 a5 (6 : Fin 32), 2) := by decide
theorem fmu_at_18c : fetchRel feMulCode 0x18C = some (.alu .mul (8 : Fin 32) (24 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fmu_at_190 : fetchRel feMulCode 0x190 = some (.alu .add (5 : Fin 32) (5 : Fin 32) a5, 2) := by decide
theorem fmu_at_192 : fetchRel feMulCode 0x192 = some (.alu .add a2 a2 a6, 2) := by decide
theorem fmu_at_194 : fetchRel feMulCode 0x194 = some (.alu .add a1 a1 a2, 2) := by decide
theorem fmu_at_196 : fetchRel feMulCode 0x196 = some (.alu .add (17 : Fin 32) (17 : Fin 32) (28 : Fin 32), 2) := by decide
theorem fmu_at_198 : fetchRel feMulCode 0x198 = some (.store .sw sp (17 : Fin 32) 0x50, 2) := by decide
theorem fmu_at_19a : fetchRel feMulCode 0x19A = some (.alu .add a3 a3 a0, 2) := by decide
theorem fmu_at_19c : fetchRel feMulCode 0x19C = some (.store .sw sp (25 : Fin 32) 0x84, 2) := by decide
theorem fmu_at_19e : fetchRel feMulCode 0x19E = some (.alu .mulhu a2 (25 : Fin 32) a4, 4) := by decide
theorem fmu_at_1a2 : fetchRel feMulCode 0x1A2 = some (.alu .mul a4 (25 : Fin 32) a4, 4) := by decide
theorem fmu_at_1a6 : fetchRel feMulCode 0x1A6 = some (.alu .sltu a0 a3 a0, 4) := by decide
theorem fmu_at_1aa : fetchRel feMulCode 0x1AA = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_1ac : fetchRel feMulCode 0x1AC = some (.alu .sltu a1 (17 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_1b0 : fetchRel feMulCode 0x1B0 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a3, 2) := by decide
theorem fmu_at_1b2 : fetchRel feMulCode 0x1B2 = some (.load .lw (6 : Fin 32) sp 0x5C, 2) := by decide
theorem fmu_at_1b4 : fetchRel feMulCode 0x1B4 = some (.alu .mulhu a5 (21 : Fin 32) (6 : Fin 32), 4) := by decide
theorem fmu_at_1b8 : fetchRel feMulCode 0x1B8 = some (.alu .sltu a3 (8 : Fin 32) a3, 4) := by decide
theorem fmu_at_1bc : fetchRel feMulCode 0x1BC = some (.alu .mul a6 (21 : Fin 32) (6 : Fin 32), 4) := by decide
theorem fmu_at_1c0 : fetchRel feMulCode 0x1C0 = some (.alu .add a1 a1 (5 : Fin 32), 2) := by decide
theorem fmu_at_1c2 : fetchRel feMulCode 0x1C2 = some (.store .sw sp a1 0x4C, 2) := by decide
theorem fmu_at_1c4 : fetchRel feMulCode 0x1C4 = some (.alu .add a0 a0 a3, 2) := by decide
theorem fmu_at_1c6 : fetchRel feMulCode 0x1C6 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_1c8 : fetchRel feMulCode 0x1C8 = some (.load .lw a2 sp 0x94, 2) := by decide
theorem fmu_at_1ca : fetchRel feMulCode 0x1CA = some (.alu .mulhu a1 (20 : Fin 32) a2, 4) := by decide
theorem fmu_at_1ce : fetchRel feMulCode 0x1CE = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem fmu_at_1d0 : fetchRel feMulCode 0x1D0 = some (.alu .mul a2 (20 : Fin 32) a2, 4) := by decide
theorem fmu_at_1d4 : fetchRel feMulCode 0x1D4 = some (.alu .sltu a3 a4 (8 : Fin 32), 4) := by decide
theorem fmu_at_1d8 : fetchRel feMulCode 0x1D8 = some (.load .lw (7 : Fin 32) sp 0x70, 2) := by decide
theorem fmu_at_1da : fetchRel feMulCode 0x1DA = some (.load .lw (24 : Fin 32) sp 0x8, 2) := by decide
theorem fmu_at_1dc : fetchRel feMulCode 0x1DC = some (.alu .mul (17 : Fin 32) (24 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fmu_at_1e0 : fetchRel feMulCode 0x1E0 = some (.alu .add a3 a3 a5, 2) := by decide
theorem fmu_at_1e2 : fetchRel feMulCode 0x1E2 = some (.alu .mulhu a5 (24 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fmu_at_1e6 : fetchRel feMulCode 0x1E6 = some (.alu .add a6 a6 a4, 2) := by decide
theorem fmu_at_1e8 : fetchRel feMulCode 0x1E8 = some (.load .lw (25 : Fin 32) sp 0x60, 2) := by decide
theorem fmu_at_1ea : fetchRel feMulCode 0x1EA = some (.alu .mulhu (8 : Fin 32) (22 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_1ee : fetchRel feMulCode 0x1EE = some (.alu .add a0 a0 a3, 2) := by decide
theorem fmu_at_1f0 : fetchRel feMulCode 0x1F0 = some (.alu .sltu a3 a6 a4, 4) := by decide
theorem fmu_at_1f4 : fetchRel feMulCode 0x1F4 = some (.alu .add a1 a1 a3, 2) := by decide
theorem fmu_at_1f6 : fetchRel feMulCode 0x1F6 = some (.alu .mul a3 (22 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_1fa : fetchRel feMulCode 0x1FA = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_1fc : fetchRel feMulCode 0x1FC = some (.alu .add a2 a2 a6, 2) := by decide
theorem fmu_at_1fe : fetchRel feMulCode 0x1FE = some (.alu .sltu a1 a2 a6, 4) := by decide
theorem fmu_at_202 : fetchRel feMulCode 0x202 = some (.alu .add (17 : Fin 32) (17 : Fin 32) a2, 2) := by decide
theorem fmu_at_204 : fetchRel feMulCode 0x204 = some (.alu .add a1 a1 a5, 2) := by decide
theorem fmu_at_206 : fetchRel feMulCode 0x206 = some (.alu .sltu a2 (17 : Fin 32) a2, 4) := by decide
theorem fmu_at_20a : fetchRel feMulCode 0x20A = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_20c : fetchRel feMulCode 0x20C = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem fmu_at_20e : fetchRel feMulCode 0x20E = some (.alu .mul (23 : Fin 32) ra (27 : Fin 32), 4) := by decide
theorem fmu_at_212 : fetchRel feMulCode 0x212 = some (.alu .mulhu a6 ra (27 : Fin 32), 4) := by decide
theorem fmu_at_216 : fetchRel feMulCode 0x216 = some (.alu .add (29 : Fin 32) a0 a2, 4) := by decide
theorem fmu_at_21a : fetchRel feMulCode 0x21A = some (.alu .add a3 a3 (17 : Fin 32), 2) := by decide
theorem fmu_at_21c : fetchRel feMulCode 0x21C = some (.alu .sltu a2 a3 (17 : Fin 32), 4) := by decide
theorem fmu_at_220 : fetchRel feMulCode 0x220 = some (.alu .mulhu (5 : Fin 32) (31 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_224 : fetchRel feMulCode 0x224 = some (.load .lw a1 sp 0x74, 2) := by decide
theorem fmu_at_226 : fetchRel feMulCode 0x226 = some (.alu .mulhu (28 : Fin 32) a1 (6 : Fin 32), 4) := by decide
theorem fmu_at_22a : fetchRel feMulCode 0x22A = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem fmu_at_22c : fetchRel feMulCode 0x22C = some (.alu .add (9 : Fin 32) x0 (7 : Fin 32), 2) := by decide
theorem fmu_at_22e : fetchRel feMulCode 0x22E = some (.alu .mulhu a4 (8 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fmu_at_232 : fetchRel feMulCode 0x232 = some (.alu .mul (7 : Fin 32) (31 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_236 : fetchRel feMulCode 0x236 = some (.load .lw a0 sp 0x80, 2) := by decide
theorem fmu_at_238 : fetchRel feMulCode 0x238 = some (.alu .mulhu a5 a0 (25 : Fin 32), 4) := by decide
theorem fmu_at_23c : fetchRel feMulCode 0x23C = some (.alu .mul (17 : Fin 32) a1 (6 : Fin 32), 4) := by decide
theorem fmu_at_240 : fetchRel feMulCode 0x240 = some (.alu .mul (6 : Fin 32) (8 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fmu_at_244 : fetchRel feMulCode 0x244 = some (.alu .add a2 a2 a6, 2) := by decide
theorem fmu_at_246 : fetchRel feMulCode 0x246 = some (.alu .add a6 a3 (23 : Fin 32), 4) := by decide
theorem fmu_at_24a : fetchRel feMulCode 0x24A = some (.alu .add a2 a2 (29 : Fin 32), 2) := by decide
theorem fmu_at_24c : fetchRel feMulCode 0x24C = some (.alu .sltu a3 a6 a3, 4) := by decide
theorem fmu_at_250 : fetchRel feMulCode 0x250 = some (.alu .add a3 a3 (5 : Fin 32), 2) := by decide
theorem fmu_at_252 : fetchRel feMulCode 0x252 = some (.alu .mul (8 : Fin 32) a0 (25 : Fin 32), 4) := by decide
theorem fmu_at_256 : fetchRel feMulCode 0x256 = some (.alu .add (9 : Fin 32) a2 a3, 4) := by decide
theorem fmu_at_25a : fetchRel feMulCode 0x25A = some (.alu .add a1 a4 (28 : Fin 32), 4) := by decide
theorem fmu_at_25e : fetchRel feMulCode 0x25E = some (.alu .add a1 a1 a5, 2) := by decide
theorem fmu_at_260 : fetchRel feMulCode 0x260 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a6, 2) := by decide
theorem fmu_at_262 : fetchRel feMulCode 0x262 = some (.store .sw sp (7 : Fin 32) 0x40, 2) := by decide
theorem fmu_at_264 : fetchRel feMulCode 0x264 = some (.alu .add a5 (6 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fmu_at_268 : fetchRel feMulCode 0x268 = some (.load .lw a2 sp 0x7C, 2) := by decide
theorem fmu_at_26a : fetchRel feMulCode 0x26A = some (.alu .mulhu a3 a2 (27 : Fin 32), 4) := by decide
theorem fmu_at_26e : fetchRel feMulCode 0x26E = some (.alu .sltu a0 a5 (6 : Fin 32), 4) := by decide
theorem fmu_at_272 : fetchRel feMulCode 0x272 = some (.alu .mul (5 : Fin 32) a2 (27 : Fin 32), 4) := by decide
theorem fmu_at_276 : fetchRel feMulCode 0x276 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_278 : fetchRel feMulCode 0x278 = some (.alu .sltu a1 (7 : Fin 32) a6, 4) := by decide
theorem fmu_at_27c : fetchRel feMulCode 0x27C = some (.alu .add (8 : Fin 32) (8 : Fin 32) a5, 2) := by decide
theorem fmu_at_27e : fetchRel feMulCode 0x27E = some (.load .lw (28 : Fin 32) sp 0x64, 2) := by decide
theorem fmu_at_280 : fetchRel feMulCode 0x280 = some (.alu .mulhu a2 (21 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_284 : fetchRel feMulCode 0x284 = some (.alu .sltu a5 (8 : Fin 32) a5, 4) := by decide
theorem fmu_at_288 : fetchRel feMulCode 0x288 = some (.alu .mul a6 (21 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_28c : fetchRel feMulCode 0x28C = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem fmu_at_28e : fetchRel feMulCode 0x28E = some (.store .sw sp a1 0x3C, 2) := by decide
theorem fmu_at_290 : fetchRel feMulCode 0x290 = some (.alu .add a0 a0 a5, 2) := by decide
theorem fmu_at_292 : fetchRel feMulCode 0x292 = some (.alu .add a0 a0 a3, 2) := by decide
theorem fmu_at_294 : fetchRel feMulCode 0x294 = some (.load .lw a3 sp 0x88, 2) := by decide
theorem fmu_at_296 : fetchRel feMulCode 0x296 = some (.alu .mulhu a1 a3 (18 : Fin 32), 4) := by decide
theorem fmu_at_29a : fetchRel feMulCode 0x29A = some (.alu .mul a3 a3 (18 : Fin 32), 4) := by decide
theorem fmu_at_29e : fetchRel feMulCode 0x29E = some (.alu .add a4 (8 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fmu_at_2a2 : fetchRel feMulCode 0x2A2 = some (.alu .sltu a5 a4 (8 : Fin 32), 4) := by decide
theorem fmu_at_2a6 : fetchRel feMulCode 0x2A6 = some (.alu .mul (17 : Fin 32) (24 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fmu_at_2aa : fetchRel feMulCode 0x2AA = some (.alu .add a2 a2 a5, 2) := by decide
theorem fmu_at_2ac : fetchRel feMulCode 0x2AC = some (.alu .mulhu a5 (24 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fmu_at_2b0 : fetchRel feMulCode 0x2B0 = some (.alu .add a6 a6 a4, 2) := by decide
theorem fmu_at_2b2 : fetchRel feMulCode 0x2B2 = some (.alu .mulhu (8 : Fin 32) (22 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_2b6 : fetchRel feMulCode 0x2B6 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_2b8 : fetchRel feMulCode 0x2B8 = some (.alu .sltu a2 a6 a4, 4) := by decide
theorem fmu_at_2bc : fetchRel feMulCode 0x2BC = some (.alu .add a1 a1 a2, 2) := by decide
theorem fmu_at_2be : fetchRel feMulCode 0x2BE = some (.alu .mul a2 (22 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_2c2 : fetchRel feMulCode 0x2C2 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_2c4 : fetchRel feMulCode 0x2C4 = some (.alu .add a3 a3 a6, 2) := by decide
theorem fmu_at_2c6 : fetchRel feMulCode 0x2C6 = some (.alu .sltu a1 a3 a6, 4) := by decide
theorem fmu_at_2ca : fetchRel feMulCode 0x2CA = some (.alu .add (17 : Fin 32) (17 : Fin 32) a3, 2) := by decide
theorem fmu_at_2cc : fetchRel feMulCode 0x2CC = some (.alu .add a1 a1 a5, 2) := by decide
theorem fmu_at_2ce : fetchRel feMulCode 0x2CE = some (.alu .sltu a3 (17 : Fin 32) a3, 4) := by decide
theorem fmu_at_2d2 : fetchRel feMulCode 0x2D2 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_2d4 : fetchRel feMulCode 0x2D4 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem fmu_at_2d6 : fetchRel feMulCode 0x2D6 = some (.alu .mul a6 ra (19 : Fin 32), 4) := by decide
theorem fmu_at_2da : fetchRel feMulCode 0x2DA = some (.alu .mulhu (6 : Fin 32) ra (19 : Fin 32), 4) := by decide
theorem fmu_at_2de : fetchRel feMulCode 0x2DE = some (.alu .add (5 : Fin 32) a0 a3, 4) := by decide
theorem fmu_at_2e2 : fetchRel feMulCode 0x2E2 = some (.alu .add a2 a2 (17 : Fin 32), 2) := by decide
theorem fmu_at_2e4 : fetchRel feMulCode 0x2E4 = some (.alu .sltu (7 : Fin 32) a2 (17 : Fin 32), 4) := by decide
theorem fmu_at_2e8 : fetchRel feMulCode 0x2E8 = some (.alu .mulhu (17 : Fin 32) (31 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fmu_at_2ec : fetchRel feMulCode 0x2EC = some (.load .lw a3 sp 0x94, 2) := by decide
theorem fmu_at_2ee : fetchRel feMulCode 0x2EE = some (.alu .add a5 x0 (28 : Fin 32), 2) := by decide
theorem fmu_at_2f0 : fetchRel feMulCode 0x2F0 = some (.alu .mulhu (28 : Fin 32) a3 (28 : Fin 32), 4) := by decide
theorem fmu_at_2f4 : fetchRel feMulCode 0x2F4 = some (.load .lw (8 : Fin 32) sp 0x68, 2) := by decide
theorem fmu_at_2f6 : fetchRel feMulCode 0x2F6 = some (.alu .mulhu a1 (8 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_2fa : fetchRel feMulCode 0x2FA = some (.alu .mul (18 : Fin 32) (31 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fmu_at_2fe : fetchRel feMulCode 0x2FE = some (.load .lw a0 sp 0x8C, 2) := by decide
theorem fmu_at_300 : fetchRel feMulCode 0x300 = some (.alu .mulhu a4 a0 (19 : Fin 32), 4) := by decide
theorem fmu_at_304 : fetchRel feMulCode 0x304 = some (.alu .mul (29 : Fin 32) a3 a5, 4) := by decide
theorem fmu_at_308 : fetchRel feMulCode 0x308 = some (.alu .mul a3 (8 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_30c : fetchRel feMulCode 0x30C = some (.alu .add (6 : Fin 32) (6 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fmu_at_30e : fetchRel feMulCode 0x30E = some (.alu .add a6 a6 a2, 2) := by decide
theorem fmu_at_310 : fetchRel feMulCode 0x310 = some (.alu .add (5 : Fin 32) (5 : Fin 32) (6 : Fin 32), 2) := by decide
theorem fmu_at_312 : fetchRel feMulCode 0x312 = some (.alu .sltu a2 a6 a2, 4) := by decide
theorem fmu_at_316 : fetchRel feMulCode 0x316 = some (.alu .add a2 a2 (17 : Fin 32), 2) := by decide
theorem fmu_at_318 : fetchRel feMulCode 0x318 = some (.alu .mul (8 : Fin 32) a0 (19 : Fin 32), 4) := by decide
theorem fmu_at_31c : fetchRel feMulCode 0x31C = some (.alu .add (5 : Fin 32) (5 : Fin 32) a2, 2) := by decide
theorem fmu_at_31e : fetchRel feMulCode 0x31E = some (.alu .add a1 a1 (28 : Fin 32), 2) := by decide
theorem fmu_at_320 : fetchRel feMulCode 0x320 = some (.alu .add a1 a1 a4, 2) := by decide
theorem fmu_at_322 : fetchRel feMulCode 0x322 = some (.alu .add a0 a6 (18 : Fin 32), 4) := by decide
theorem fmu_at_326 : fetchRel feMulCode 0x326 = some (.store .sw sp a0 0x38, 2) := by decide
theorem fmu_at_328 : fetchRel feMulCode 0x328 = some (.alu .add a5 a3 (29 : Fin 32), 4) := by decide
theorem fmu_at_32c : fetchRel feMulCode 0x32C = some (.load .lw a2 sp 0x84, 2) := by decide
theorem fmu_at_32e : fetchRel feMulCode 0x32E = some (.alu .mulhu a4 a2 (30 : Fin 32), 4) := by decide
theorem fmu_at_332 : fetchRel feMulCode 0x332 = some (.alu .mul (17 : Fin 32) a2 (30 : Fin 32), 4) := by decide
theorem fmu_at_336 : fetchRel feMulCode 0x336 = some (.alu .sltu a3 a5 a3, 4) := by decide
theorem fmu_at_33a : fetchRel feMulCode 0x33A = some (.alu .add a1 a1 a3, 2) := by decide
theorem fmu_at_33c : fetchRel feMulCode 0x33C = some (.alu .sltu a3 a0 a6, 4) := by decide
theorem fmu_at_340 : fetchRel feMulCode 0x340 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a5, 2) := by decide
theorem fmu_at_342 : fetchRel feMulCode 0x342 = some (.load .lw (25 : Fin 32) sp 0x6C, 2) := by decide
theorem fmu_at_344 : fetchRel feMulCode 0x344 = some (.alu .mulhu a2 (21 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_348 : fetchRel feMulCode 0x348 = some (.alu .sltu a5 (8 : Fin 32) a5, 4) := by decide
theorem fmu_at_34c : fetchRel feMulCode 0x34C = some (.alu .mul a6 (21 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_350 : fetchRel feMulCode 0x350 = some (.alu .add a3 a3 (5 : Fin 32), 2) := by decide
theorem fmu_at_352 : fetchRel feMulCode 0x352 = some (.store .sw sp a3 0x34, 2) := by decide
theorem fmu_at_354 : fetchRel feMulCode 0x354 = some (.alu .add a1 a1 a5, 2) := by decide
theorem fmu_at_356 : fetchRel feMulCode 0x356 = some (.alu .add a0 a1 a4, 4) := by decide
theorem fmu_at_35a : fetchRel feMulCode 0x35A = some (.load .lw a3 sp 0x90, 2) := by decide
theorem fmu_at_35c : fetchRel feMulCode 0x35C = some (.alu .add (30 : Fin 32) x0 (20 : Fin 32), 2) := by decide
theorem fmu_at_35e : fetchRel feMulCode 0x35E = some (.alu .mul a1 (20 : Fin 32) a3, 4) := by decide
theorem fmu_at_362 : fetchRel feMulCode 0x362 = some (.alu .add a4 (8 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fmu_at_366 : fetchRel feMulCode 0x366 = some (.alu .mulhu a3 (20 : Fin 32) a3, 4) := by decide
theorem fmu_at_36a : fetchRel feMulCode 0x36A = some (.alu .sltu a5 a4 (8 : Fin 32), 4) := by decide
theorem fmu_at_36e : fetchRel feMulCode 0x36E = some (.load .lw (18 : Fin 32) sp 0x5C, 2) := by decide
theorem fmu_at_370 : fetchRel feMulCode 0x370 = some (.alu .mulhu (8 : Fin 32) (24 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_374 : fetchRel feMulCode 0x374 = some (.alu .add a2 a2 a5, 2) := by decide
theorem fmu_at_376 : fetchRel feMulCode 0x376 = some (.alu .mul a5 (24 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_37a : fetchRel feMulCode 0x37A = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_37c : fetchRel feMulCode 0x37C = some (.alu .add a6 a6 a4, 2) := by decide
theorem fmu_at_37e : fetchRel feMulCode 0x37E = some (.alu .sltu a2 a6 a4, 4) := by decide
theorem fmu_at_382 : fetchRel feMulCode 0x382 = some (.load .lw (9 : Fin 32) sp 0x70, 2) := by decide
theorem fmu_at_384 : fetchRel feMulCode 0x384 = some (.alu .mulhu (17 : Fin 32) (22 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fmu_at_388 : fetchRel feMulCode 0x388 = some (.alu .add a1 a1 a6, 2) := by decide
theorem fmu_at_38a : fetchRel feMulCode 0x38A = some (.alu .mul a4 (22 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fmu_at_38e : fetchRel feMulCode 0x38E = some (.alu .add a2 a2 a3, 2) := by decide
theorem fmu_at_390 : fetchRel feMulCode 0x390 = some (.alu .sltu a3 a1 a6, 4) := by decide
theorem fmu_at_394 : fetchRel feMulCode 0x394 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_396 : fetchRel feMulCode 0x396 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem fmu_at_398 : fetchRel feMulCode 0x398 = some (.alu .add a5 a5 a1, 2) := by decide
theorem fmu_at_39a : fetchRel feMulCode 0x39A = some (.load .lw (29 : Fin 32) sp 0x60, 2) := by decide
theorem fmu_at_39c : fetchRel feMulCode 0x39C = some (.store .sw sp ra 0x4, 2) := by decide
theorem fmu_at_39e : fetchRel feMulCode 0x39E = some (.alu .mul a6 ra (29 : Fin 32), 4) := by decide
theorem fmu_at_3a2 : fetchRel feMulCode 0x3A2 = some (.alu .add a0 a0 a3, 2) := by decide
theorem fmu_at_3a4 : fetchRel feMulCode 0x3A4 = some (.alu .sltu a1 a5 a1, 4) := by decide
theorem fmu_at_3a8 : fetchRel feMulCode 0x3A8 = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem fmu_at_3aa : fetchRel feMulCode 0x3AA = some (.alu .mulhu (17 : Fin 32) ra (29 : Fin 32), 4) := by decide
theorem fmu_at_3ae : fetchRel feMulCode 0x3AE = some (.alu .add a4 a4 a5, 2) := by decide
theorem fmu_at_3b0 : fetchRel feMulCode 0x3B0 = some (.alu .add (28 : Fin 32) x0 (31 : Fin 32), 2) := by decide
theorem fmu_at_3b2 : fetchRel feMulCode 0x3B2 = some (.alu .mulhu (5 : Fin 32) (31 : Fin 32) (27 : Fin 32), 4) := by decide
theorem fmu_at_3b6 : fetchRel feMulCode 0x3B6 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_3b8 : fetchRel feMulCode 0x3B8 = some (.alu .sltu a1 a4 a5, 4) := by decide
theorem fmu_at_3bc : fetchRel feMulCode 0x3BC = some (.load .lw a5 sp 0x74, 2) := by decide
theorem fmu_at_3be : fetchRel feMulCode 0x3BE = some (.alu .mulhu (6 : Fin 32) a5 (25 : Fin 32), 4) := by decide
theorem fmu_at_3c2 : fetchRel feMulCode 0x3C2 = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem fmu_at_3c4 : fetchRel feMulCode 0x3C4 = some (.alu .mulhu a2 (8 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_3c8 : fetchRel feMulCode 0x3C8 = some (.alu .add a6 a6 a4, 2) := by decide
theorem fmu_at_3ca : fetchRel feMulCode 0x3CA = some (.alu .mul a3 (31 : Fin 32) (27 : Fin 32), 4) := by decide
theorem fmu_at_3ce : fetchRel feMulCode 0x3CE = some (.alu .mul (7 : Fin 32) a5 (25 : Fin 32), 4) := by decide
theorem fmu_at_3d2 : fetchRel feMulCode 0x3D2 = some (.alu .mul a5 (8 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_3d6 : fetchRel feMulCode 0x3D6 = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem fmu_at_3d8 : fetchRel feMulCode 0x3D8 = some (.alu .sltu a4 a6 a4, 4) := by decide
theorem fmu_at_3dc : fetchRel feMulCode 0x3DC = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_3de : fetchRel feMulCode 0x3DE = some (.alu .add a4 a4 (5 : Fin 32), 2) := by decide
theorem fmu_at_3e0 : fetchRel feMulCode 0x3E0 = some (.load .lw a1 sp 0x80, 2) := by decide
theorem fmu_at_3e2 : fetchRel feMulCode 0x3E2 = some (.alu .mulhu (17 : Fin 32) a1 (9 : Fin 32), 4) := by decide
theorem fmu_at_3e6 : fetchRel feMulCode 0x3E6 = some (.alu .mul (8 : Fin 32) a1 (9 : Fin 32), 4) := by decide
theorem fmu_at_3ea : fetchRel feMulCode 0x3EA = some (.alu .add a0 a0 a4, 2) := by decide
theorem fmu_at_3ec : fetchRel feMulCode 0x3EC = some (.alu .add a2 a2 (6 : Fin 32), 2) := by decide
theorem fmu_at_3ee : fetchRel feMulCode 0x3EE = some (.alu .add a1 a6 a3, 4) := by decide
theorem fmu_at_3f2 : fetchRel feMulCode 0x3F2 = some (.store .sw sp a1 0x28, 2) := by decide
theorem fmu_at_3f4 : fetchRel feMulCode 0x3F4 = some (.load .lw (9 : Fin 32) sp 0x7C, 2) := by decide
theorem fmu_at_3f6 : fetchRel feMulCode 0x3F6 = some (.alu .mulhu a3 (9 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fmu_at_3fa : fetchRel feMulCode 0x3FA = some (.alu .sltu a4 a1 a6, 4) := by decide
theorem fmu_at_3fe : fetchRel feMulCode 0x3FE = some (.alu .add (7 : Fin 32) (7 : Fin 32) a5, 2) := by decide
theorem fmu_at_400 : fetchRel feMulCode 0x400 = some (.alu .sltu a5 (7 : Fin 32) a5, 4) := by decide
theorem fmu_at_404 : fetchRel feMulCode 0x404 = some (.alu .mul a1 (9 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fmu_at_408 : fetchRel feMulCode 0x408 = some (.alu .add a0 a0 a4, 2) := by decide
theorem fmu_at_40a : fetchRel feMulCode 0x40A = some (.store .sw sp a0 0x24, 2) := by decide
theorem fmu_at_40c : fetchRel feMulCode 0x40C = some (.alu .add a2 a2 a5, 2) := by decide
theorem fmu_at_40e : fetchRel feMulCode 0x40E = some (.alu .add a2 a2 (17 : Fin 32), 2) := by decide
theorem fmu_at_410 : fetchRel feMulCode 0x410 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fmu_at_412 : fetchRel feMulCode 0x412 = some (.load .lw ra sp 0x18, 2) := by decide
theorem fmu_at_414 : fetchRel feMulCode 0x414 = some (.alu .mul a0 (21 : Fin 32) ra, 4) := by decide
theorem fmu_at_418 : fetchRel feMulCode 0x418 = some (.alu .mulhu a4 (21 : Fin 32) ra, 4) := by decide
theorem fmu_at_41c : fetchRel feMulCode 0x41C = some (.alu .add (31 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem fmu_at_41e : fetchRel feMulCode 0x41E = some (.alu .add a2 a2 a3, 2) := by decide
theorem fmu_at_420 : fetchRel feMulCode 0x420 = some (.alu .sltu a3 (8 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fmu_at_424 : fetchRel feMulCode 0x424 = some (.alu .add a2 a2 a3, 2) := by decide
theorem fmu_at_426 : fetchRel feMulCode 0x426 = some (.load .lw a5 sp 0x88, 2) := by decide
theorem fmu_at_428 : fetchRel feMulCode 0x428 = some (.alu .mul a3 a5 (27 : Fin 32), 4) := by decide
theorem fmu_at_42c : fetchRel feMulCode 0x42C = some (.alu .mulhu a5 a5 (27 : Fin 32), 4) := by decide
theorem fmu_at_430 : fetchRel feMulCode 0x430 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem fmu_at_432 : fetchRel feMulCode 0x432 = some (.alu .sltu (8 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem fmu_at_436 : fetchRel feMulCode 0x436 = some (.load .lw (23 : Fin 32) sp 0x64, 2) := by decide
theorem fmu_at_438 : fetchRel feMulCode 0x438 = some (.alu .mulhu a6 (24 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_43c : fetchRel feMulCode 0x43C = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem fmu_at_43e : fetchRel feMulCode 0x43E = some (.alu .mul (8 : Fin 32) (24 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_442 : fetchRel feMulCode 0x442 = some (.alu .add a2 a2 a4, 2) := by decide
theorem fmu_at_444 : fetchRel feMulCode 0x444 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_446 : fetchRel feMulCode 0x446 = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fmu_at_44a : fetchRel feMulCode 0x44A = some (.alu .mulhu (17 : Fin 32) (22 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fmu_at_44e : fetchRel feMulCode 0x44E = some (.alu .add a3 a3 a0, 2) := by decide
theorem fmu_at_450 : fetchRel feMulCode 0x450 = some (.alu .mul a4 (22 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fmu_at_454 : fetchRel feMulCode 0x454 = some (.alu .add a1 a1 a5, 2) := by decide
theorem fmu_at_456 : fetchRel feMulCode 0x456 = some (.alu .sltu a0 a3 a0, 4) := by decide
theorem fmu_at_45a : fetchRel feMulCode 0x45A = some (.alu .add a1 a1 a2, 2) := by decide
theorem fmu_at_45c : fetchRel feMulCode 0x45C = some (.alu .add a0 a0 a6, 2) := by decide
theorem fmu_at_45e : fetchRel feMulCode 0x45E = some (.alu .add (8 : Fin 32) (8 : Fin 32) a3, 2) := by decide
theorem fmu_at_460 : fetchRel feMulCode 0x460 = some (.load .lw (21 : Fin 32) sp 0x4, 2) := by decide
theorem fmu_at_462 : fetchRel feMulCode 0x462 = some (.alu .mul a6 (21 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_466 : fetchRel feMulCode 0x466 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_468 : fetchRel feMulCode 0x468 = some (.alu .sltu a1 (8 : Fin 32) a3, 4) := by decide
theorem fmu_at_46c : fetchRel feMulCode 0x46C = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem fmu_at_46e : fetchRel feMulCode 0x46E = some (.alu .mulhu (17 : Fin 32) (21 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_472 : fetchRel feMulCode 0x472 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem fmu_at_474 : fetchRel feMulCode 0x474 = some (.alu .add a5 x0 (28 : Fin 32), 2) := by decide
theorem fmu_at_476 : fetchRel feMulCode 0x476 = some (.alu .mulhu (5 : Fin 32) (28 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_47a : fetchRel feMulCode 0x47A = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_47c : fetchRel feMulCode 0x47C = some (.alu .sltu a1 a4 (8 : Fin 32), 4) := by decide
theorem fmu_at_480 : fetchRel feMulCode 0x480 = some (.load .lw a3 sp 0x94, 2) := by decide
theorem fmu_at_482 : fetchRel feMulCode 0x482 = some (.alu .mulhu (6 : Fin 32) a3 ra, 4) := by decide
theorem fmu_at_486 : fetchRel feMulCode 0x486 = some (.load .lw (8 : Fin 32) sp 0x90, 2) := by decide
theorem fmu_at_488 : fetchRel feMulCode 0x488 = some (.alu .mulhu a2 (8 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_48c : fetchRel feMulCode 0x48C = some (.alu .add a6 a6 a4, 2) := by decide
theorem fmu_at_48e : fetchRel feMulCode 0x48E = some (.alu .mul (28 : Fin 32) (28 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_492 : fetchRel feMulCode 0x492 = some (.alu .add (27 : Fin 32) x0 a5, 2) := by decide
theorem fmu_at_494 : fetchRel feMulCode 0x494 = some (.alu .mul (7 : Fin 32) a3 ra, 4) := by decide
theorem fmu_at_498 : fetchRel feMulCode 0x498 = some (.alu .mul a5 (8 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_49c : fetchRel feMulCode 0x49C = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem fmu_at_49e : fetchRel feMulCode 0x49E = some (.alu .sltu a4 a6 a4, 4) := by decide
theorem fmu_at_4a2 : fetchRel feMulCode 0x4A2 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_4a4 : fetchRel feMulCode 0x4A4 = some (.alu .add a4 a4 (5 : Fin 32), 2) := by decide
theorem fmu_at_4a6 : fetchRel feMulCode 0x4A6 = some (.load .lw a1 sp 0x8C, 2) := by decide
theorem fmu_at_4a8 : fetchRel feMulCode 0x4A8 = some (.alu .mulhu (17 : Fin 32) a1 (26 : Fin 32), 4) := by decide
theorem fmu_at_4ac : fetchRel feMulCode 0x4AC = some (.alu .mul (8 : Fin 32) a1 (26 : Fin 32), 4) := by decide
theorem fmu_at_4b0 : fetchRel feMulCode 0x4B0 = some (.alu .add a0 a0 a4, 2) := by decide
theorem fmu_at_4b2 : fetchRel feMulCode 0x4B2 = some (.alu .add a2 a2 (6 : Fin 32), 2) := by decide
theorem fmu_at_4b4 : fetchRel feMulCode 0x4B4 = some (.alu .add (28 : Fin 32) (28 : Fin 32) a6, 2) := by decide
theorem fmu_at_4b6 : fetchRel feMulCode 0x4B6 = some (.store .sw sp (28 : Fin 32) 0x20, 2) := by decide
theorem fmu_at_4b8 : fetchRel feMulCode 0x4B8 = some (.load .lw a1 sp 0x84, 2) := by decide
theorem fmu_at_4ba : fetchRel feMulCode 0x4BA = some (.alu .mulhu a4 a1 (19 : Fin 32), 4) := by decide
theorem fmu_at_4be : fetchRel feMulCode 0x4BE = some (.alu .sltu a3 (28 : Fin 32) a6, 4) := by decide
theorem fmu_at_4c2 : fetchRel feMulCode 0x4C2 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a5, 2) := by decide
theorem fmu_at_4c4 : fetchRel feMulCode 0x4C4 = some (.alu .mul a1 a1 (19 : Fin 32), 4) := by decide
theorem fmu_at_4c8 : fetchRel feMulCode 0x4C8 = some (.alu .sltu a5 (7 : Fin 32) a5, 4) := by decide
theorem fmu_at_4cc : fetchRel feMulCode 0x4CC = some (.alu .add a0 a0 a3, 2) := by decide
theorem fmu_at_4ce : fetchRel feMulCode 0x4CE = some (.store .sw sp a0 0x1C, 2) := by decide
theorem fmu_at_4d0 : fetchRel feMulCode 0x4D0 = some (.alu .add a2 a2 a5, 2) := by decide
theorem fmu_at_4d2 : fetchRel feMulCode 0x4D2 = some (.alu .add a2 a2 (17 : Fin 32), 2) := by decide
theorem fmu_at_4d4 : fetchRel feMulCode 0x4D4 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fmu_at_4d6 : fetchRel feMulCode 0x4D6 = some (.load .lw (28 : Fin 32) sp 0x2C, 2) := by decide
theorem fmu_at_4d8 : fetchRel feMulCode 0x4D8 = some (.alu .mul a0 (31 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_4dc : fetchRel feMulCode 0x4DC = some (.alu .mulhu a3 (31 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_4e0 : fetchRel feMulCode 0x4E0 = some (.alu .add a2 a2 a4, 2) := by decide
theorem fmu_at_4e2 : fetchRel feMulCode 0x4E2 = some (.alu .sltu a4 (8 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fmu_at_4e6 : fetchRel feMulCode 0x4E6 = some (.alu .add a2 a2 a4, 2) := by decide
theorem fmu_at_4e8 : fetchRel feMulCode 0x4E8 = some (.load .lw (19 : Fin 32) sp 0x68, 2) := by decide
theorem fmu_at_4ea : fetchRel feMulCode 0x4EA = some (.alu .mul a4 (20 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_4ee : fetchRel feMulCode 0x4EE = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem fmu_at_4f0 : fetchRel feMulCode 0x4F0 = some (.alu .mulhu a5 (20 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_4f4 : fetchRel feMulCode 0x4F4 = some (.alu .sltu (8 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem fmu_at_4f8 : fetchRel feMulCode 0x4F8 = some (.alu .mulhu a6 (24 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_4fc : fetchRel feMulCode 0x4FC = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem fmu_at_4fe : fetchRel feMulCode 0x4FE = some (.alu .mul (8 : Fin 32) (24 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_502 : fetchRel feMulCode 0x502 = some (.alu .add a2 a2 a3, 2) := by decide
theorem fmu_at_504 : fetchRel feMulCode 0x504 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_506 : fetchRel feMulCode 0x506 = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fmu_at_50a : fetchRel feMulCode 0x50A = some (.alu .add (20 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem fmu_at_50c : fetchRel feMulCode 0x50C = some (.alu .mul (17 : Fin 32) (22 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_510 : fetchRel feMulCode 0x510 = some (.alu .add a4 a4 a0, 2) := by decide
theorem fmu_at_512 : fetchRel feMulCode 0x512 = some (.alu .mulhu a3 (22 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_516 : fetchRel feMulCode 0x516 = some (.alu .add a1 a1 a5, 2) := by decide
theorem fmu_at_518 : fetchRel feMulCode 0x518 = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem fmu_at_51c : fetchRel feMulCode 0x51C = some (.alu .add a1 a1 a2, 2) := by decide
theorem fmu_at_51e : fetchRel feMulCode 0x51E = some (.alu .add a0 a0 a6, 2) := by decide
theorem fmu_at_520 : fetchRel feMulCode 0x520 = some (.alu .add (5 : Fin 32) a1 a0, 4) := by decide
theorem fmu_at_524 : fetchRel feMulCode 0x524 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a4, 2) := by decide
theorem fmu_at_526 : fetchRel feMulCode 0x526 = some (.alu .sltu a1 (8 : Fin 32) a4, 4) := by decide
theorem fmu_at_52a : fetchRel feMulCode 0x52A = some (.load .lw (18 : Fin 32) sp 0x70, 2) := by decide
theorem fmu_at_52c : fetchRel feMulCode 0x52C = some (.alu .mulhu (6 : Fin 32) (21 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_530 : fetchRel feMulCode 0x530 = some (.alu .add (17 : Fin 32) (17 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fmu_at_532 : fetchRel feMulCode 0x532 = some (.alu .mul (7 : Fin 32) (21 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_536 : fetchRel feMulCode 0x536 = some (.alu .add a1 a1 a3, 2) := by decide
theorem fmu_at_538 : fetchRel feMulCode 0x538 = some (.alu .sltu a3 (17 : Fin 32) (8 : Fin 32), 4) := by decide
theorem fmu_at_53c : fetchRel feMulCode 0x53C = some (.alu .mulhu a5 (27 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fmu_at_540 : fetchRel feMulCode 0x540 = some (.load .lw a0 sp 0x74, 2) := by decide
theorem fmu_at_542 : fetchRel feMulCode 0x542 = some (.alu .mul a6 a0 (28 : Fin 32), 4) := by decide
theorem fmu_at_546 : fetchRel feMulCode 0x546 = some (.alu .mulhu (8 : Fin 32) a0 (28 : Fin 32), 4) := by decide
theorem fmu_at_54a : fetchRel feMulCode 0x54A = some (.load .lw a2 sp 0x78, 2) := by decide
theorem fmu_at_54c : fetchRel feMulCode 0x54C = some (.alu .mulhu a0 a2 (25 : Fin 32), 4) := by decide
theorem fmu_at_550 : fetchRel feMulCode 0x550 = some (.alu .mul a2 a2 (25 : Fin 32), 4) := by decide
theorem fmu_at_554 : fetchRel feMulCode 0x554 = some (.load .lw (9 : Fin 32) sp 0x80, 2) := by decide
theorem fmu_at_556 : fetchRel feMulCode 0x556 = some (.alu .mulhu a4 (9 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fmu_at_55a : fetchRel feMulCode 0x55A = some (.alu .add a1 a1 (5 : Fin 32), 2) := by decide
theorem fmu_at_55c : fetchRel feMulCode 0x55C = some (.alu .add a3 a3 (6 : Fin 32), 2) := by decide
theorem fmu_at_55e : fetchRel feMulCode 0x55E = some (.alu .add a1 a1 a3, 2) := by decide
theorem fmu_at_560 : fetchRel feMulCode 0x560 = some (.alu .add (7 : Fin 32) (7 : Fin 32) (17 : Fin 32), 2) := by decide
theorem fmu_at_562 : fetchRel feMulCode 0x562 = some (.alu .sltu a3 (7 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fmu_at_566 : fetchRel feMulCode 0x566 = some (.alu .mul (17 : Fin 32) (27 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fmu_at_56a : fetchRel feMulCode 0x56A = some (.alu .add a3 a3 a5, 2) := by decide
theorem fmu_at_56c : fetchRel feMulCode 0x56C = some (.alu .mul a5 (9 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fmu_at_570 : fetchRel feMulCode 0x570 = some (.alu .add (5 : Fin 32) a1 a3, 4) := by decide
theorem fmu_at_574 : fetchRel feMulCode 0x574 = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem fmu_at_576 : fetchRel feMulCode 0x576 = some (.alu .add a0 a0 a4, 2) := by decide
theorem fmu_at_578 : fetchRel feMulCode 0x578 = some (.alu .add a6 a6 a2, 2) := by decide
theorem fmu_at_57a : fetchRel feMulCode 0x57A = some (.alu .sltu a2 a6 a2, 4) := by decide
theorem fmu_at_57e : fetchRel feMulCode 0x57E = some (.load .lw a1 sp 0x7C, 2) := by decide
theorem fmu_at_580 : fetchRel feMulCode 0x580 = some (.alu .mulhu a3 a1 (18 : Fin 32), 4) := by decide
theorem fmu_at_584 : fetchRel feMulCode 0x584 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_586 : fetchRel feMulCode 0x586 = some (.load .lw (25 : Fin 32) sp 0x30, 2) := by decide
theorem fmu_at_588 : fetchRel feMulCode 0x588 = some (.alu .mulhu a2 (31 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_58c : fetchRel feMulCode 0x58C = some (.alu .add (17 : Fin 32) (17 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fmu_at_58e : fetchRel feMulCode 0x58E = some (.store .sw sp (17 : Fin 32) 0x14, 2) := by decide
theorem fmu_at_590 : fetchRel feMulCode 0x590 = some (.alu .mul a4 a1 (18 : Fin 32), 4) := by decide
theorem fmu_at_594 : fetchRel feMulCode 0x594 = some (.alu .sltu (8 : Fin 32) (17 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fmu_at_598 : fetchRel feMulCode 0x598 = some (.alu .add a5 a5 a6, 2) := by decide
theorem fmu_at_59a : fetchRel feMulCode 0x59A = some (.alu .sltu a1 a5 a6, 4) := by decide
theorem fmu_at_59e : fetchRel feMulCode 0x59E = some (.alu .mul a6 (31 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_5a2 : fetchRel feMulCode 0x5A2 = some (.alu .add (5 : Fin 32) (5 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fmu_at_5a4 : fetchRel feMulCode 0x5A4 = some (.store .sw sp (5 : Fin 32) 0x10, 2) := by decide
theorem fmu_at_5a6 : fetchRel feMulCode 0x5A6 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_5a8 : fetchRel feMulCode 0x5A8 = some (.alu .add a0 a0 a3, 2) := by decide
theorem fmu_at_5aa : fetchRel feMulCode 0x5AA = some (.load .lw a3 sp 0x88, 2) := by decide
theorem fmu_at_5ac : fetchRel feMulCode 0x5AC = some (.alu .mul a1 a3 (29 : Fin 32), 4) := by decide
theorem fmu_at_5b0 : fetchRel feMulCode 0x5B0 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_5b2 : fetchRel feMulCode 0x5B2 = some (.alu .mulhu (5 : Fin 32) a3 (29 : Fin 32), 4) := by decide
theorem fmu_at_5b6 : fetchRel feMulCode 0x5B6 = some (.alu .add a4 a4 a5, 2) := by decide
theorem fmu_at_5b8 : fetchRel feMulCode 0x5B8 = some (.alu .mulhu a3 (24 : Fin 32) ra, 4) := by decide
theorem fmu_at_5bc : fetchRel feMulCode 0x5BC = some (.alu .sltu a5 a4 a5, 4) := by decide
theorem fmu_at_5c0 : fetchRel feMulCode 0x5C0 = some (.alu .mul (8 : Fin 32) (24 : Fin 32) ra, 4) := by decide
theorem fmu_at_5c4 : fetchRel feMulCode 0x5C4 = some (.alu .add a0 a0 a5, 2) := by decide
theorem fmu_at_5c6 : fetchRel feMulCode 0x5C6 = some (.alu .add a6 a6 a4, 2) := by decide
theorem fmu_at_5c8 : fetchRel feMulCode 0x5C8 = some (.alu .sltu a4 a6 a4, 4) := by decide
theorem fmu_at_5cc : fetchRel feMulCode 0x5CC = some (.alu .mulhu a5 (22 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_5d0 : fetchRel feMulCode 0x5D0 = some (.alu .add a1 a1 a6, 2) := by decide
theorem fmu_at_5d2 : fetchRel feMulCode 0x5D2 = some (.alu .mul a2 (22 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_5d6 : fetchRel feMulCode 0x5D6 = some (.alu .add a0 a0 a4, 2) := by decide
theorem fmu_at_5d8 : fetchRel feMulCode 0x5D8 = some (.alu .sltu a4 a1 a6, 4) := by decide
theorem fmu_at_5dc : fetchRel feMulCode 0x5DC = some (.alu .add a0 a0 (5 : Fin 32), 2) := by decide
theorem fmu_at_5de : fetchRel feMulCode 0x5DE = some (.alu .add a3 a3 a4, 2) := by decide
theorem fmu_at_5e0 : fetchRel feMulCode 0x5E0 = some (.alu .add a6 a0 a3, 4) := by decide
theorem fmu_at_5e4 : fetchRel feMulCode 0x5E4 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a1, 2) := by decide
theorem fmu_at_5e6 : fetchRel feMulCode 0x5E6 = some (.alu .sltu a1 (8 : Fin 32) a1, 4) := by decide
theorem fmu_at_5ea : fetchRel feMulCode 0x5EA = some (.alu .mulhu (6 : Fin 32) (21 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fmu_at_5ee : fetchRel feMulCode 0x5EE = some (.alu .add (29 : Fin 32) a1 a5, 4) := by decide
theorem fmu_at_5f2 : fetchRel feMulCode 0x5F2 = some (.alu .mul (7 : Fin 32) (21 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fmu_at_5f6 : fetchRel feMulCode 0x5F6 = some (.alu .add (17 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem fmu_at_5f8 : fetchRel feMulCode 0x5F8 = some (.alu .add a5 (8 : Fin 32) a2, 4) := by decide
theorem fmu_at_5fc : fetchRel feMulCode 0x5FC = some (.alu .mulhu (5 : Fin 32) (27 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_600 : fetchRel feMulCode 0x600 = some (.load .lw a1 sp 0x94, 2) := by decide
theorem fmu_at_602 : fetchRel feMulCode 0x602 = some (.alu .mulhu a0 a1 (25 : Fin 32), 4) := by decide
theorem fmu_at_606 : fetchRel feMulCode 0x606 = some (.load .lw (9 : Fin 32) sp 0x90, 2) := by decide
theorem fmu_at_608 : fetchRel feMulCode 0x608 = some (.alu .mulhu a2 (9 : Fin 32) ra, 4) := by decide
theorem fmu_at_60c : fetchRel feMulCode 0x60C = some (.alu .sltu (8 : Fin 32) a5 (8 : Fin 32), 4) := by decide
theorem fmu_at_610 : fetchRel feMulCode 0x610 = some (.alu .mulhu a3 (19 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_614 : fetchRel feMulCode 0x614 = some (.alu .mul a4 a1 (25 : Fin 32), 4) := by decide
theorem fmu_at_618 : fetchRel feMulCode 0x618 = some (.alu .mul a1 (9 : Fin 32) ra, 4) := by decide
theorem fmu_at_61c : fetchRel feMulCode 0x61C = some (.alu .add a6 a6 (29 : Fin 32), 2) := by decide
theorem fmu_at_61e : fetchRel feMulCode 0x61E = some (.alu .add (6 : Fin 32) (6 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fmu_at_620 : fetchRel feMulCode 0x620 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a5, 2) := by decide
theorem fmu_at_622 : fetchRel feMulCode 0x622 = some (.alu .mul (8 : Fin 32) (19 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_626 : fetchRel feMulCode 0x626 = some (.alu .add a6 a6 (6 : Fin 32), 2) := by decide
theorem fmu_at_628 : fetchRel feMulCode 0x628 = some (.alu .sltu a5 (7 : Fin 32) a5, 4) := by decide
theorem fmu_at_62c : fetchRel feMulCode 0x62C = some (.alu .add (5 : Fin 32) (5 : Fin 32) a5, 2) := by decide
theorem fmu_at_62e : fetchRel feMulCode 0x62E = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_630 : fetchRel feMulCode 0x630 = some (.alu .add a0 a0 a3, 2) := by decide
theorem fmu_at_632 : fetchRel feMulCode 0x632 = some (.load .lw a5 sp 0x84, 2) := by decide
theorem fmu_at_634 : fetchRel feMulCode 0x634 = some (.alu .mulhu a2 a5 (26 : Fin 32), 4) := by decide
theorem fmu_at_638 : fetchRel feMulCode 0x638 = some (.alu .add a4 a4 a1, 2) := by decide
theorem fmu_at_63a : fetchRel feMulCode 0x63A = some (.load .lw (21 : Fin 32) sp 0x44, 2) := by decide
theorem fmu_at_63c : fetchRel feMulCode 0x63C = some (.alu .mulhu a3 (31 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fmu_at_640 : fetchRel feMulCode 0x640 = some (.alu .sltu a1 a4 a1, 4) := by decide
theorem fmu_at_644 : fetchRel feMulCode 0x644 = some (.alu .mul a5 a5 (26 : Fin 32), 4) := by decide
theorem fmu_at_648 : fetchRel feMulCode 0x648 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_64a : fetchRel feMulCode 0x64A = some (.alu .add (8 : Fin 32) (8 : Fin 32) a4, 2) := by decide
theorem fmu_at_64c : fetchRel feMulCode 0x64C = some (.alu .sltu a1 (8 : Fin 32) a4, 4) := by decide
theorem fmu_at_650 : fetchRel feMulCode 0x650 = some (.alu .mul a4 (31 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fmu_at_654 : fetchRel feMulCode 0x654 = some (.alu .add a6 a6 (5 : Fin 32), 2) := by decide
theorem fmu_at_656 : fetchRel feMulCode 0x656 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_658 : fetchRel feMulCode 0x658 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_65a : fetchRel feMulCode 0x65A = some (.load .lw a1 sp 0x8C, 2) := by decide
theorem fmu_at_65c : fetchRel feMulCode 0x65C = some (.store .sw sp (30 : Fin 32) 0xC, 2) := by decide
theorem fmu_at_65e : fetchRel feMulCode 0x65E = some (.alu .mul (5 : Fin 32) (30 : Fin 32) a1, 4) := by decide
theorem fmu_at_662 : fetchRel feMulCode 0x662 = some (.alu .add a0 a0 a3, 2) := by decide
theorem fmu_at_664 : fetchRel feMulCode 0x664 = some (.alu .mulhu a2 (30 : Fin 32) a1, 4) := by decide
theorem fmu_at_668 : fetchRel feMulCode 0x668 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem fmu_at_66a : fetchRel feMulCode 0x66A = some (.alu .mulhu a3 (24 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_66e : fetchRel feMulCode 0x66E = some (.alu .sltu (8 : Fin 32) a5 (8 : Fin 32), 4) := by decide
theorem fmu_at_672 : fetchRel feMulCode 0x672 = some (.alu .mul a1 (24 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_676 : fetchRel feMulCode 0x676 = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem fmu_at_678 : fetchRel feMulCode 0x678 = some (.alu .add a4 a4 a5, 2) := by decide
theorem fmu_at_67a : fetchRel feMulCode 0x67A = some (.alu .sltu a5 a4 a5, 4) := by decide
theorem fmu_at_67e : fetchRel feMulCode 0x67E = some (.load .lw (19 : Fin 32) sp 0x6C, 2) := by decide
theorem fmu_at_680 : fetchRel feMulCode 0x680 = some (.alu .mulhu (8 : Fin 32) (22 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_684 : fetchRel feMulCode 0x684 = some (.alu .add a0 a0 a5, 2) := by decide
theorem fmu_at_686 : fetchRel feMulCode 0x686 = some (.alu .add (5 : Fin 32) (5 : Fin 32) a4, 2) := by decide
theorem fmu_at_688 : fetchRel feMulCode 0x688 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_68a : fetchRel feMulCode 0x68A = some (.alu .sltu a2 (5 : Fin 32) a4, 4) := by decide
theorem fmu_at_68e : fetchRel feMulCode 0x68E = some (.alu .add a2 a2 a3, 2) := by decide
theorem fmu_at_690 : fetchRel feMulCode 0x690 = some (.alu .mul (6 : Fin 32) (27 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_694 : fetchRel feMulCode 0x694 = some (.alu .add a1 a1 (5 : Fin 32), 2) := by decide
theorem fmu_at_696 : fetchRel feMulCode 0x696 = some (.alu .mul a3 (22 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_69a : fetchRel feMulCode 0x69A = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_69c : fetchRel feMulCode 0x69C = some (.alu .sltu a2 a1 (5 : Fin 32), 4) := by decide
theorem fmu_at_6a0 : fetchRel feMulCode 0x6A0 = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem fmu_at_6a2 : fetchRel feMulCode 0x6A2 = some (.alu .mulhu (30 : Fin 32) (17 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fmu_at_6a6 : fetchRel feMulCode 0x6A6 = some (.alu .add (29 : Fin 32) a0 a2, 4) := by decide
theorem fmu_at_6aa : fetchRel feMulCode 0x6AA = some (.load .lw a0 sp 0x74, 2) := by decide
theorem fmu_at_6ac : fetchRel feMulCode 0x6AC = some (.alu .mul (5 : Fin 32) a0 (21 : Fin 32), 4) := by decide
theorem fmu_at_6b0 : fetchRel feMulCode 0x6B0 = some (.alu .mulhu (18 : Fin 32) a0 (21 : Fin 32), 4) := by decide
theorem fmu_at_6b4 : fetchRel feMulCode 0x6B4 = some (.load .lw a0 sp 0x78, 2) := by decide
theorem fmu_at_6b6 : fetchRel feMulCode 0x6B6 = some (.alu .mulhu a2 a0 (28 : Fin 32), 4) := by decide
theorem fmu_at_6ba : fetchRel feMulCode 0x6BA = some (.alu .mul a5 a0 (28 : Fin 32), 4) := by decide
theorem fmu_at_6be : fetchRel feMulCode 0x6BE = some (.load .lw (8 : Fin 32) sp 0x80, 2) := by decide
theorem fmu_at_6c0 : fetchRel feMulCode 0x6C0 = some (.alu .mulhu a0 (8 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_6c4 : fetchRel feMulCode 0x6C4 = some (.alu .add a4 (7 : Fin 32) (6 : Fin 32), 4) := by decide
theorem fmu_at_6c8 : fetchRel feMulCode 0x6C8 = some (.store .sw sp a4 0x74, 2) := by decide
theorem fmu_at_6ca : fetchRel feMulCode 0x6CA = some (.alu .add a3 a3 a1, 2) := by decide
theorem fmu_at_6cc : fetchRel feMulCode 0x6CC = some (.alu .sltu a1 a3 a1, 4) := by decide
theorem fmu_at_6d0 : fetchRel feMulCode 0x6D0 = some (.alu .mul (6 : Fin 32) (17 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fmu_at_6d4 : fetchRel feMulCode 0x6D4 = some (.alu .add a1 a1 (30 : Fin 32), 2) := by decide
theorem fmu_at_6d6 : fetchRel feMulCode 0x6D6 = some (.alu .sltu (9 : Fin 32) a4 (7 : Fin 32), 4) := by decide
theorem fmu_at_6da : fetchRel feMulCode 0x6DA = some (.alu .add a6 a6 (9 : Fin 32), 2) := by decide
theorem fmu_at_6dc : fetchRel feMulCode 0x6DC = some (.store .sw sp a6 0x78, 2) := by decide
theorem fmu_at_6de : fetchRel feMulCode 0x6DE = some (.alu .add (29 : Fin 32) (29 : Fin 32) a1, 2) := by decide
theorem fmu_at_6e0 : fetchRel feMulCode 0x6E0 = some (.alu .add a2 a2 (18 : Fin 32), 2) := by decide
theorem fmu_at_6e2 : fetchRel feMulCode 0x6E2 = some (.alu .mul (9 : Fin 32) (8 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_6e6 : fetchRel feMulCode 0x6E6 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_6e8 : fetchRel feMulCode 0x6E8 = some (.alu .add (5 : Fin 32) (5 : Fin 32) a5, 2) := by decide
theorem fmu_at_6ea : fetchRel feMulCode 0x6EA = some (.alu .sltu a2 (5 : Fin 32) a5, 4) := by decide
theorem fmu_at_6ee : fetchRel feMulCode 0x6EE = some (.load .lw a4 sp 0x70, 2) := by decide
theorem fmu_at_6f0 : fetchRel feMulCode 0x6F0 = some (.alu .mulhu a5 (27 : Fin 32) a4, 4) := by decide
theorem fmu_at_6f4 : fetchRel feMulCode 0x6F4 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_6f6 : fetchRel feMulCode 0x6F6 = some (.alu .add a2 a3 (6 : Fin 32), 4) := by decide
theorem fmu_at_6fa : fetchRel feMulCode 0x6FA = some (.alu .add (19 : Fin 32) x0 (20 : Fin 32), 2) := by decide
theorem fmu_at_6fc : fetchRel feMulCode 0x6FC = some (.load .lw a1 sp 0x7C, 2) := by decide
theorem fmu_at_6fe : fetchRel feMulCode 0x6FE = some (.alu .mul (18 : Fin 32) a1 (20 : Fin 32), 4) := by decide
theorem fmu_at_702 : fetchRel feMulCode 0x702 = some (.alu .mulhu (20 : Fin 32) a1 (20 : Fin 32), 4) := by decide
theorem fmu_at_706 : fetchRel feMulCode 0x706 = some (.alu .sltu a3 a2 a3, 4) := by decide
theorem fmu_at_70a : fetchRel feMulCode 0x70A = some (.load .lw (26 : Fin 32) sp 0x48, 2) := by decide
theorem fmu_at_70c : fetchRel feMulCode 0x70C = some (.alu .mul (7 : Fin 32) (31 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_710 : fetchRel feMulCode 0x710 = some (.alu .add (9 : Fin 32) (9 : Fin 32) (5 : Fin 32), 2) := by decide
theorem fmu_at_712 : fetchRel feMulCode 0x712 = some (.alu .mulhu (30 : Fin 32) (31 : Fin 32) (26 : Fin 32), 4) := by decide
theorem fmu_at_716 : fetchRel feMulCode 0x716 = some (.alu .sltu a1 (9 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fmu_at_71a : fetchRel feMulCode 0x71A = some (.load .lw (8 : Fin 32) sp 0x88, 2) := by decide
theorem fmu_at_71c : fetchRel feMulCode 0x71C = some (.alu .mulhu (5 : Fin 32) (8 : Fin 32) a4, 4) := by decide
theorem fmu_at_720 : fetchRel feMulCode 0x720 = some (.alu .add a3 a3 a5, 2) := by decide
theorem fmu_at_722 : fetchRel feMulCode 0x722 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_724 : fetchRel feMulCode 0x724 = some (.alu .mul a1 (8 : Fin 32) a4, 4) := by decide
theorem fmu_at_728 : fetchRel feMulCode 0x728 = some (.alu .mul a5 (27 : Fin 32) a4, 4) := by decide
theorem fmu_at_72c : fetchRel feMulCode 0x72C = some (.alu .add (6 : Fin 32) x0 (27 : Fin 32), 2) := by decide
theorem fmu_at_72e : fetchRel feMulCode 0x72E = some (.alu .add a0 a0 (20 : Fin 32), 2) := by decide
theorem fmu_at_730 : fetchRel feMulCode 0x730 = some (.alu .add a4 (9 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_734 : fetchRel feMulCode 0x734 = some (.alu .sltu (8 : Fin 32) a4 (9 : Fin 32), 4) := by decide
theorem fmu_at_738 : fetchRel feMulCode 0x738 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a4, 2) := by decide
theorem fmu_at_73a : fetchRel feMulCode 0x73A = some (.alu .add (30 : Fin 32) (30 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fmu_at_73c : fetchRel feMulCode 0x73C = some (.alu .sltu a4 (7 : Fin 32) a4, 4) := by decide
theorem fmu_at_740 : fetchRel feMulCode 0x740 = some (.alu .add a0 a0 (30 : Fin 32), 2) := by decide
theorem fmu_at_742 : fetchRel feMulCode 0x742 = some (.alu .add a4 a4 (5 : Fin 32), 2) := by decide
theorem fmu_at_744 : fetchRel feMulCode 0x744 = some (.alu .add a3 a3 (29 : Fin 32), 2) := by decide
theorem fmu_at_746 : fetchRel feMulCode 0x746 = some (.alu .add a0 a0 a4, 2) := by decide
theorem fmu_at_748 : fetchRel feMulCode 0x748 = some (.alu .add (29 : Fin 32) a2 a5, 4) := by decide
theorem fmu_at_74c : fetchRel feMulCode 0x74C = some (.alu .mul (9 : Fin 32) (24 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_750 : fetchRel feMulCode 0x750 = some (.alu .add a1 a1 (7 : Fin 32), 2) := by decide
theorem fmu_at_752 : fetchRel feMulCode 0x752 = some (.alu .mulhu (8 : Fin 32) (24 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fmu_at_756 : fetchRel feMulCode 0x756 = some (.alu .mul (30 : Fin 32) (22 : Fin 32) ra, 4) := by decide
theorem fmu_at_75a : fetchRel feMulCode 0x75A = some (.alu .mulhu a4 (22 : Fin 32) ra, 4) := by decide
theorem fmu_at_75e : fetchRel feMulCode 0x75E = some (.alu .sltu (5 : Fin 32) (29 : Fin 32) a2, 4) := by decide
theorem fmu_at_762 : fetchRel feMulCode 0x762 = some (.alu .sltu a2 a1 (7 : Fin 32), 4) := by decide
theorem fmu_at_766 : fetchRel feMulCode 0x766 = some (.alu .mul (7 : Fin 32) (17 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_76a : fetchRel feMulCode 0x76A = some (.alu .mulhu a5 (17 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_76e : fetchRel feMulCode 0x76E = some (.alu .add (5 : Fin 32) (5 : Fin 32) a3, 2) := by decide
theorem fmu_at_770 : fetchRel feMulCode 0x770 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_772 : fetchRel feMulCode 0x772 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a1, 2) := by decide
theorem fmu_at_774 : fetchRel feMulCode 0x774 = some (.load .lw a6 sp 0xC, 2) := by decide
theorem fmu_at_776 : fetchRel feMulCode 0x776 = some (.alu .mulhu a3 (27 : Fin 32) a6, 4) := by decide
theorem fmu_at_77a : fetchRel feMulCode 0x77A = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem fmu_at_77c : fetchRel feMulCode 0x77C = some (.alu .sltu a1 (9 : Fin 32) a1, 4) := by decide
theorem fmu_at_780 : fetchRel feMulCode 0x780 = some (.alu .add a1 a1 a4, 2) := by decide
theorem fmu_at_782 : fetchRel feMulCode 0x782 = some (.alu .add (30 : Fin 32) (30 : Fin 32) (9 : Fin 32), 2) := by decide
theorem fmu_at_784 : fetchRel feMulCode 0x784 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_786 : fetchRel feMulCode 0x786 = some (.alu .sltu a1 (30 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fmu_at_78a : fetchRel feMulCode 0x78A = some (.alu .add a1 a1 a5, 2) := by decide
theorem fmu_at_78c : fetchRel feMulCode 0x78C = some (.alu .add (27 : Fin 32) (30 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fmu_at_790 : fetchRel feMulCode 0x790 = some (.alu .add (7 : Fin 32) a0 a1, 4) := by decide
theorem fmu_at_794 : fetchRel feMulCode 0x794 = some (.alu .sltu a0 (27 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fmu_at_798 : fetchRel feMulCode 0x798 = some (.alu .add (30 : Fin 32) a0 a3, 4) := by decide
theorem fmu_at_79c : fetchRel feMulCode 0x79C = some (.load .lw a1 sp 0x94, 2) := by decide
theorem fmu_at_79e : fetchRel feMulCode 0x79E = some (.alu .mul a0 a1 (26 : Fin 32), 4) := by decide
theorem fmu_at_7a2 : fetchRel feMulCode 0x7A2 = some (.alu .mulhu a4 a1 (26 : Fin 32), 4) := by decide
theorem fmu_at_7a6 : fetchRel feMulCode 0x7A6 = some (.load .lw a1 sp 0x90, 2) := by decide
theorem fmu_at_7a8 : fetchRel feMulCode 0x7A8 = some (.alu .mulhu a5 a1 (25 : Fin 32), 4) := by decide
theorem fmu_at_7ac : fetchRel feMulCode 0x7AC = some (.alu .mul (9 : Fin 32) a1 (25 : Fin 32), 4) := by decide
theorem fmu_at_7b0 : fetchRel feMulCode 0x7B0 = some (.load .lw a2 sp 0x68, 2) := by decide
theorem fmu_at_7b2 : fetchRel feMulCode 0x7B2 = some (.alu .mulhu (8 : Fin 32) a2 ra, 4) := by decide
theorem fmu_at_7b6 : fetchRel feMulCode 0x7B6 = some (.load .lw a1 sp 0x54, 2) := by decide
theorem fmu_at_7b8 : fetchRel feMulCode 0x7B8 = some (.alu .mul (25 : Fin 32) (31 : Fin 32) a1, 4) := by decide
theorem fmu_at_7bc : fetchRel feMulCode 0x7BC = some (.alu .mulhu (26 : Fin 32) (31 : Fin 32) a1, 4) := by decide
theorem fmu_at_7c0 : fetchRel feMulCode 0x7C0 = some (.alu .mul (18 : Fin 32) (24 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fmu_at_7c4 : fetchRel feMulCode 0x7C4 = some (.alu .mulhu (20 : Fin 32) (24 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fmu_at_7c8 : fetchRel feMulCode 0x7C8 = some (.alu .mul (21 : Fin 32) (22 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_7cc : fetchRel feMulCode 0x7CC = some (.alu .mulhu (31 : Fin 32) (22 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fmu_at_7d0 : fetchRel feMulCode 0x7D0 = some (.alu .mul a1 a2 ra, 4) := by decide
theorem fmu_at_7d4 : fetchRel feMulCode 0x7D4 = some (.load .lw a2 sp 0x8C, 2) := by decide
theorem fmu_at_7d6 : fetchRel feMulCode 0x7D6 = some (.alu .mul (28 : Fin 32) a2 (23 : Fin 32), 4) := by decide
theorem fmu_at_7da : fetchRel feMulCode 0x7DA = some (.alu .mulhu a2 a2 (23 : Fin 32), 4) := by decide
theorem fmu_at_7de : fetchRel feMulCode 0x7DE = some (.alu .add a4 a4 a5, 2) := by decide
theorem fmu_at_7e0 : fetchRel feMulCode 0x7E0 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem fmu_at_7e2 : fetchRel feMulCode 0x7E2 = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem fmu_at_7e4 : fetchRel feMulCode 0x7E4 = some (.alu .sltu a5 a0 (9 : Fin 32), 4) := by decide
theorem fmu_at_7e8 : fetchRel feMulCode 0x7E8 = some (.load .lw a3 sp 0x6C, 2) := by decide
theorem fmu_at_7ea : fetchRel feMulCode 0x7EA = some (.alu .mul (23 : Fin 32) (17 : Fin 32) a3, 4) := by decide
theorem fmu_at_7ee : fetchRel feMulCode 0x7EE = some (.alu .mulhu (17 : Fin 32) (17 : Fin 32) a3, 4) := by decide
theorem fmu_at_7f2 : fetchRel feMulCode 0x7F2 = some (.alu .add a4 a4 a5, 2) := by decide
theorem fmu_at_7f4 : fetchRel feMulCode 0x7F4 = some (.load .lw a3 sp 0x84, 2) := by decide
theorem fmu_at_7f6 : fetchRel feMulCode 0x7F6 = some (.alu .mul a5 a6 a3, 4) := by decide
theorem fmu_at_7fa : fetchRel feMulCode 0x7FA = some (.alu .mulhu (8 : Fin 32) a6 a3, 4) := by decide
theorem fmu_at_7fe : fetchRel feMulCode 0x7FE = some (.alu .mul (22 : Fin 32) (6 : Fin 32) a6, 4) := by decide
theorem fmu_at_802 : fetchRel feMulCode 0x802 = some (.alu .add a1 a1 a0, 2) := by decide
theorem fmu_at_804 : fetchRel feMulCode 0x804 = some (.alu .sltu a0 a1 a0, 4) := by decide
theorem fmu_at_808 : fetchRel feMulCode 0x808 = some (.alu .mul (24 : Fin 32) (6 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_80c : fetchRel feMulCode 0x80C = some (.alu .mulhu (19 : Fin 32) (6 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fmu_at_810 : fetchRel feMulCode 0x810 = some (.alu .add a0 a0 a4, 2) := by decide
theorem fmu_at_812 : fetchRel feMulCode 0x812 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_814 : fetchRel feMulCode 0x814 = some (.alu .add a3 a1 (28 : Fin 32), 4) := by decide
theorem fmu_at_818 : fetchRel feMulCode 0x818 = some (.alu .sltu a1 a3 a1, 4) := by decide
theorem fmu_at_81c : fetchRel feMulCode 0x81C = some (.alu .add (25 : Fin 32) (25 : Fin 32) a3, 2) := by decide
theorem fmu_at_81e : fetchRel feMulCode 0x81E = some (.alu .add a1 a1 (26 : Fin 32), 2) := by decide
theorem fmu_at_820 : fetchRel feMulCode 0x820 = some (.alu .sltu a2 (25 : Fin 32) a3, 4) := by decide
theorem fmu_at_824 : fetchRel feMulCode 0x824 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_826 : fetchRel feMulCode 0x826 = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem fmu_at_828 : fetchRel feMulCode 0x828 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_82a : fetchRel feMulCode 0x82A = some (.alu .add a5 a5 (25 : Fin 32), 2) := by decide
theorem fmu_at_82c : fetchRel feMulCode 0x82C = some (.alu .sltu a1 a5 (25 : Fin 32), 4) := by decide
theorem fmu_at_830 : fetchRel feMulCode 0x830 = some (.alu .add (18 : Fin 32) (18 : Fin 32) a5, 2) := by decide
theorem fmu_at_832 : fetchRel feMulCode 0x832 = some (.alu .add a1 a1 (20 : Fin 32), 2) := by decide
theorem fmu_at_834 : fetchRel feMulCode 0x834 = some (.alu .sltu a2 (18 : Fin 32) a5, 4) := by decide
theorem fmu_at_838 : fetchRel feMulCode 0x838 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_83a : fetchRel feMulCode 0x83A = some (.alu .add a2 a2 (31 : Fin 32), 2) := by decide
theorem fmu_at_83c : fetchRel feMulCode 0x83C = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_83e : fetchRel feMulCode 0x83E = some (.alu .add (21 : Fin 32) (21 : Fin 32) (18 : Fin 32), 2) := by decide
theorem fmu_at_840 : fetchRel feMulCode 0x840 = some (.alu .sltu a1 (21 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fmu_at_844 : fetchRel feMulCode 0x844 = some (.alu .add (23 : Fin 32) (23 : Fin 32) (21 : Fin 32), 2) := by decide
theorem fmu_at_846 : fetchRel feMulCode 0x846 = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem fmu_at_848 : fetchRel feMulCode 0x848 = some (.alu .sltu a2 (23 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fmu_at_84c : fetchRel feMulCode 0x84C = some (.alu .add a0 a0 a1, 2) := by decide
theorem fmu_at_84e : fetchRel feMulCode 0x84E = some (.alu .add a2 a2 (19 : Fin 32), 2) := by decide
theorem fmu_at_850 : fetchRel feMulCode 0x850 = some (.alu .add (7 : Fin 32) (7 : Fin 32) (30 : Fin 32), 2) := by decide
theorem fmu_at_852 : fetchRel feMulCode 0x852 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_854 : fetchRel feMulCode 0x854 = some (.alu .add (22 : Fin 32) (22 : Fin 32) (27 : Fin 32), 2) := by decide
theorem fmu_at_856 : fetchRel feMulCode 0x856 = some (.alu .add (24 : Fin 32) (24 : Fin 32) (23 : Fin 32), 2) := by decide
theorem fmu_at_858 : fetchRel feMulCode 0x858 = some (.alu .sltu a1 (22 : Fin 32) (27 : Fin 32), 4) := by decide
theorem fmu_at_85c : fetchRel feMulCode 0x85C = some (.alu .sltu a2 (24 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fmu_at_860 : fetchRel feMulCode 0x860 = some (.alu .add a1 a1 (7 : Fin 32), 2) := by decide
theorem fmu_at_862 : fetchRel feMulCode 0x862 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fmu_at_864 : fetchRel feMulCode 0x864 = some (.load .lw a2 sp 0x50, 2) := by decide
theorem fmu_at_866 : fetchRel feMulCode 0x866 = some (.store .sw sp a2 0x98, 2) := by decide
theorem fmu_at_868 : fetchRel feMulCode 0x868 = some (.load .lw a2 sp 0x4C, 2) := by decide
theorem fmu_at_86a : fetchRel feMulCode 0x86A = some (.store .sw sp a2 0x9C, 2) := by decide
theorem fmu_at_86c : fetchRel feMulCode 0x86C = some (.load .lw a2 sp 0x40, 2) := by decide
theorem fmu_at_86e : fetchRel feMulCode 0x86E = some (.store .sw sp a2 0xA0, 2) := by decide
theorem fmu_at_870 : fetchRel feMulCode 0x870 = some (.load .lw a2 sp 0x3C, 2) := by decide
theorem fmu_at_872 : fetchRel feMulCode 0x872 = some (.store .sw sp a2 0xA4, 2) := by decide
theorem fmu_at_874 : fetchRel feMulCode 0x874 = some (.load .lw a2 sp 0x38, 2) := by decide
theorem fmu_at_876 : fetchRel feMulCode 0x876 = some (.store .sw sp a2 0xA8, 2) := by decide
theorem fmu_at_878 : fetchRel feMulCode 0x878 = some (.load .lw a2 sp 0x34, 2) := by decide
theorem fmu_at_87a : fetchRel feMulCode 0x87A = some (.store .sw sp a2 0xAC, 2) := by decide
theorem fmu_at_87c : fetchRel feMulCode 0x87C = some (.load .lw a2 sp 0x28, 2) := by decide
theorem fmu_at_87e : fetchRel feMulCode 0x87E = some (.store .sw sp a2 0xB0, 2) := by decide
theorem fmu_at_880 : fetchRel feMulCode 0x880 = some (.load .lw a2 sp 0x24, 2) := by decide
theorem fmu_at_882 : fetchRel feMulCode 0x882 = some (.store .sw sp a2 0xB4, 2) := by decide
theorem fmu_at_884 : fetchRel feMulCode 0x884 = some (.load .lw a2 sp 0x20, 2) := by decide
theorem fmu_at_886 : fetchRel feMulCode 0x886 = some (.store .sw sp a2 0xB8, 2) := by decide
theorem fmu_at_888 : fetchRel feMulCode 0x888 = some (.load .lw a2 sp 0x1C, 2) := by decide
theorem fmu_at_88a : fetchRel feMulCode 0x88A = some (.store .sw sp a2 0xBC, 2) := by decide
theorem fmu_at_88c : fetchRel feMulCode 0x88C = some (.load .lw a2 sp 0x14, 2) := by decide
theorem fmu_at_88e : fetchRel feMulCode 0x88E = some (.store .sw sp a2 0xC0, 2) := by decide
theorem fmu_at_890 : fetchRel feMulCode 0x890 = some (.load .lw a2 sp 0x10, 2) := by decide
theorem fmu_at_892 : fetchRel feMulCode 0x892 = some (.store .sw sp a2 0xC4, 2) := by decide
theorem fmu_at_894 : fetchRel feMulCode 0x894 = some (.load .lw a2 sp 0x74, 2) := by decide
theorem fmu_at_896 : fetchRel feMulCode 0x896 = some (.store .sw sp a2 0xC8, 2) := by decide
theorem fmu_at_898 : fetchRel feMulCode 0x898 = some (.load .lw a2 sp 0x78, 2) := by decide
theorem fmu_at_89a : fetchRel feMulCode 0x89A = some (.store .sw sp a2 0xCC, 2) := by decide
theorem fmu_at_89c : fetchRel feMulCode 0x89C = some (.store .sw sp (29 : Fin 32) 0xD0, 2) := by decide
theorem fmu_at_89e : fetchRel feMulCode 0x89E = some (.store .sw sp (5 : Fin 32) 0xD4, 2) := by decide
theorem fmu_at_8a0 : fetchRel feMulCode 0x8A0 = some (.store .sw sp (22 : Fin 32) 0xD8, 2) := by decide
theorem fmu_at_8a2 : fetchRel feMulCode 0x8A2 = some (.store .sw sp a1 0xDC, 2) := by decide
theorem fmu_at_8a4 : fetchRel feMulCode 0x8A4 = some (.store .sw sp (24 : Fin 32) 0xE0, 2) := by decide
theorem fmu_at_8a6 : fetchRel feMulCode 0x8A6 = some (.store .sw sp a0 0xE4, 2) := by decide
theorem fmu_at_8a8 : fetchRel feMulCode 0x8A8 = some (.aluImm .add a1 sp 0x98, 2) := by decide
theorem fmu_at_8aa : fetchRel feMulCode 0x8AA = some (.load .lw a0 sp 0x58, 2) := by decide
theorem fmu_at_8ac : fetchRel feMulCode 0x8AC = some (.auipc ra 0x0, 4) := by decide
theorem fmu_at_8b0 : fetchRel feMulCode 0x8B0 = some (.jalr ra ra 0x244, 4) := by decide
theorem fmu_at_8b4 : fetchRel feMulCode 0x8B4 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem fmu_at_8b6 : fetchRel feMulCode 0x8B6 = some (.load .lw ra a0 0x1C, 4) := by decide
theorem fmu_at_8ba : fetchRel feMulCode 0x8BA = some (.load .lw (8 : Fin 32) a0 0x18, 2) := by decide
theorem fmu_at_8bc : fetchRel feMulCode 0x8BC = some (.load .lw (9 : Fin 32) a0 0x14, 2) := by decide
theorem fmu_at_8be : fetchRel feMulCode 0x8BE = some (.load .lw (18 : Fin 32) a0 0x10, 4) := by decide
theorem fmu_at_8c2 : fetchRel feMulCode 0x8C2 = some (.load .lw (19 : Fin 32) a0 0xC, 4) := by decide
theorem fmu_at_8c6 : fetchRel feMulCode 0x8C6 = some (.load .lw (20 : Fin 32) a0 0x8, 4) := by decide
theorem fmu_at_8ca : fetchRel feMulCode 0x8CA = some (.load .lw (21 : Fin 32) a0 0x4, 4) := by decide
theorem fmu_at_8ce : fetchRel feMulCode 0x8CE = some (.load .lw (22 : Fin 32) a0 0x0, 4) := by decide
theorem fmu_at_8d2 : fetchRel feMulCode 0x8D2 = some (.load .lw (23 : Fin 32) sp 0xFC, 2) := by decide
theorem fmu_at_8d4 : fetchRel feMulCode 0x8D4 = some (.load .lw (24 : Fin 32) sp 0xF8, 2) := by decide
theorem fmu_at_8d6 : fetchRel feMulCode 0x8D6 = some (.load .lw (25 : Fin 32) sp 0xF4, 2) := by decide
theorem fmu_at_8d8 : fetchRel feMulCode 0x8D8 = some (.load .lw (26 : Fin 32) sp 0xF0, 2) := by decide
theorem fmu_at_8da : fetchRel feMulCode 0x8DA = some (.load .lw (27 : Fin 32) sp 0xEC, 2) := by decide
theorem fmu_at_8dc : fetchRel feMulCode 0x8DC = some (.aluImm .add sp sp 0x120, 2) := by decide
theorem fmu_at_8de : fetchRel feMulCode 0x8DE = some (.jalr x0 ra 0x0, 2) := by decide


theorem fsq_at_0 : fetchRel feSquareInnerCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem fsq_at_2 : fetchRel feSquareInnerCode 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem fsq_at_4 : fetchRel feSquareInnerCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem fsq_at_6 : fetchRel feSquareInnerCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem fsq_at_8 : fetchRel feSquareInnerCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem fsq_at_a : fetchRel feSquareInnerCode 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem fsq_at_c : fetchRel feSquareInnerCode 0xC = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem fsq_at_e : fetchRel feSquareInnerCode 0xE = some (.store .sw sp (21 : Fin 32) 0x34, 2) := by decide
theorem fsq_at_10 : fetchRel feSquareInnerCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x30, 2) := by decide
theorem fsq_at_12 : fetchRel feSquareInnerCode 0x12 = some (.store .sw sp (23 : Fin 32) 0x2C, 2) := by decide
theorem fsq_at_14 : fetchRel feSquareInnerCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x28, 2) := by decide
theorem fsq_at_16 : fetchRel feSquareInnerCode 0x16 = some (.store .sw sp (25 : Fin 32) 0x24, 2) := by decide
theorem fsq_at_18 : fetchRel feSquareInnerCode 0x18 = some (.store .sw sp (26 : Fin 32) 0x20, 2) := by decide
theorem fsq_at_1a : fetchRel feSquareInnerCode 0x1A = some (.store .sw sp (27 : Fin 32) 0x1C, 2) := by decide
theorem fsq_at_1c : fetchRel feSquareInnerCode 0x1C = some (.alu .add (6 : Fin 32) x0 a0, 2) := by decide
theorem fsq_at_1e : fetchRel feSquareInnerCode 0x1E = some (.load .lw a0 a1 0x24, 2) := by decide
theorem fsq_at_20 : fetchRel feSquareInnerCode 0x20 = some (.store .sw sp a0 0x18, 2) := by decide
theorem fsq_at_22 : fetchRel feSquareInnerCode 0x22 = some (.load .lw a6 a1 0x14, 4) := by decide
theorem fsq_at_26 : fetchRel feSquareInnerCode 0x26 = some (.load .lw a5 a1 0x1C, 2) := by decide
theorem fsq_at_28 : fetchRel feSquareInnerCode 0x28 = some (.store .sw sp a5 0xC, 2) := by decide
theorem fsq_at_2a : fetchRel feSquareInnerCode 0x2A = some (.load .lw (29 : Fin 32) a1 0x18, 4) := by decide
theorem fsq_at_2e : fetchRel feSquareInnerCode 0x2E = some (.aluImm .add a3 x0 0x13, 2) := by decide
theorem fsq_at_30 : fetchRel feSquareInnerCode 0x30 = some (.load .lw (25 : Fin 32) a1 0x4, 4) := by decide
theorem fsq_at_34 : fetchRel feSquareInnerCode 0x34 = some (.load .lw (18 : Fin 32) a1 0xC, 4) := by decide
theorem fsq_at_38 : fetchRel feSquareInnerCode 0x38 = some (.alu .mul (22 : Fin 32) a0 a3, 4) := by decide
theorem fsq_at_3c : fetchRel feSquareInnerCode 0x3C = some (.alu .mul a4 a6 a3, 4) := by decide
theorem fsq_at_40 : fetchRel feSquareInnerCode 0x40 = some (.alu .mul (26 : Fin 32) a5 a3, 4) := by decide
theorem fsq_at_44 : fetchRel feSquareInnerCode 0x44 = some (.load .lw a0 a1 0x20, 2) := by decide
theorem fsq_at_46 : fetchRel feSquareInnerCode 0x46 = some (.store .sw sp a0 0x14, 2) := by decide
theorem fsq_at_48 : fetchRel feSquareInnerCode 0x48 = some (.load .lw a5 a1 0x0, 2) := by decide
theorem fsq_at_4a : fetchRel feSquareInnerCode 0x4A = some (.load .lw (20 : Fin 32) a1 0x8, 4) := by decide
theorem fsq_at_4e : fetchRel feSquareInnerCode 0x4E = some (.load .lw (19 : Fin 32) a1 0x10, 4) := by decide
theorem fsq_at_52 : fetchRel feSquareInnerCode 0x52 = some (.aluImm .sll (23 : Fin 32) (25 : Fin 32) 0x1, 4) := by decide
theorem fsq_at_56 : fetchRel feSquareInnerCode 0x56 = some (.aluImm .sll (31 : Fin 32) (18 : Fin 32) 0x1, 4) := by decide
theorem fsq_at_5a : fetchRel feSquareInnerCode 0x5A = some (.alu .mul (27 : Fin 32) (29 : Fin 32) a3, 4) := by decide
theorem fsq_at_5e : fetchRel feSquareInnerCode 0x5E = some (.alu .mul (24 : Fin 32) a0 a3, 4) := by decide
theorem fsq_at_62 : fetchRel feSquareInnerCode 0x62 = some (.alu .mulhu a1 (22 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_66 : fetchRel feSquareInnerCode 0x66 = some (.alu .mulhu a3 (26 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_6a : fetchRel feSquareInnerCode 0x6A = some (.alu .mulhu (9 : Fin 32) a4 a6, 4) := by decide
theorem fsq_at_6e : fetchRel feSquareInnerCode 0x6E = some (.alu .mul (8 : Fin 32) (26 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_72 : fetchRel feSquareInnerCode 0x72 = some (.alu .mul a4 a4 a6, 4) := by decide
theorem fsq_at_76 : fetchRel feSquareInnerCode 0x76 = some (.store .sw sp a6 0x8, 2) := by decide
theorem fsq_at_78 : fetchRel feSquareInnerCode 0x78 = some (.aluImm .sll a0 (20 : Fin 32) 0x1, 4) := by decide
theorem fsq_at_7c : fetchRel feSquareInnerCode 0x7C = some (.alu .mul a2 (22 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_80 : fetchRel feSquareInnerCode 0x80 = some (.aluImm .sll (28 : Fin 32) (19 : Fin 32) 0x1, 4) := by decide
theorem fsq_at_84 : fetchRel feSquareInnerCode 0x84 = some (.alu .mulhu (30 : Fin 32) a5 a5, 4) := by decide
theorem fsq_at_88 : fetchRel feSquareInnerCode 0x88 = some (.alu .mul (21 : Fin 32) a5 a5, 4) := by decide
theorem fsq_at_8c : fetchRel feSquareInnerCode 0x8C = some (.alu .mulhu ra (24 : Fin 32) a0, 4) := by decide
theorem fsq_at_90 : fetchRel feSquareInnerCode 0x90 = some (.store .sw sp a0 0x10, 2) := by decide
theorem fsq_at_92 : fetchRel feSquareInnerCode 0x92 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem fsq_at_94 : fetchRel feSquareInnerCode 0x94 = some (.alu .mulhu (9 : Fin 32) (27 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_98 : fetchRel feSquareInnerCode 0x98 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem fsq_at_9a : fetchRel feSquareInnerCode 0x9A = some (.alu .add a1 a1 a3, 2) := by decide
theorem fsq_at_9c : fetchRel feSquareInnerCode 0x9C = some (.alu .mul a3 (27 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_a0 : fetchRel feSquareInnerCode 0xA0 = some (.alu .sltu (8 : Fin 32) a4 (8 : Fin 32), 4) := by decide
theorem fsq_at_a4 : fetchRel feSquareInnerCode 0xA4 = some (.alu .add a2 a2 a4, 2) := by decide
theorem fsq_at_a6 : fetchRel feSquareInnerCode 0xA6 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem fsq_at_a8 : fetchRel feSquareInnerCode 0xA8 = some (.alu .mul (8 : Fin 32) (24 : Fin 32) a0, 4) := by decide
theorem fsq_at_ac : fetchRel feSquareInnerCode 0xAC = some (.alu .sltu a4 a2 a4, 4) := by decide
theorem fsq_at_b0 : fetchRel feSquareInnerCode 0xB0 = some (.alu .add a1 a1 a4, 2) := by decide
theorem fsq_at_b2 : fetchRel feSquareInnerCode 0xB2 = some (.aluImm .srl a4 a2 0x1F, 4) := by decide
theorem fsq_at_b6 : fetchRel feSquareInnerCode 0xB6 = some (.aluImm .sll a1 a1 0x1, 2) := by decide
theorem fsq_at_b8 : fetchRel feSquareInnerCode 0xB8 = some (.aluImm .sll (5 : Fin 32) a5 0x1, 4) := by decide
theorem fsq_at_bc : fetchRel feSquareInnerCode 0xBC = some (.alu .or (7 : Fin 32) a1 a4, 4) := by decide
theorem fsq_at_c0 : fetchRel feSquareInnerCode 0xC0 = some (.aluImm .sll a2 a2 0x1, 2) := by decide
theorem fsq_at_c2 : fetchRel feSquareInnerCode 0xC2 = some (.alu .add (21 : Fin 32) (21 : Fin 32) a3, 2) := by decide
theorem fsq_at_c4 : fetchRel feSquareInnerCode 0xC4 = some (.alu .sltu a3 (21 : Fin 32) a3, 4) := by decide
theorem fsq_at_c8 : fetchRel feSquareInnerCode 0xC8 = some (.alu .add (30 : Fin 32) (30 : Fin 32) (9 : Fin 32), 2) := by decide
theorem fsq_at_ca : fetchRel feSquareInnerCode 0xCA = some (.alu .add (8 : Fin 32) (8 : Fin 32) (21 : Fin 32), 2) := by decide
theorem fsq_at_cc : fetchRel feSquareInnerCode 0xCC = some (.alu .add (30 : Fin 32) (30 : Fin 32) ra, 2) := by decide
theorem fsq_at_ce : fetchRel feSquareInnerCode 0xCE = some (.alu .sltu a4 (8 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fsq_at_d2 : fetchRel feSquareInnerCode 0xD2 = some (.alu .add a3 a3 (30 : Fin 32), 2) := by decide
theorem fsq_at_d4 : fetchRel feSquareInnerCode 0xD4 = some (.alu .add ra a3 a4, 4) := by decide
theorem fsq_at_d8 : fetchRel feSquareInnerCode 0xD8 = some (.alu .add (21 : Fin 32) (8 : Fin 32) a2, 4) := by decide
theorem fsq_at_dc : fetchRel feSquareInnerCode 0xDC = some (.alu .mul a2 (22 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fsq_at_e0 : fetchRel feSquareInnerCode 0xE0 = some (.alu .mul a4 (26 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fsq_at_e4 : fetchRel feSquareInnerCode 0xE4 = some (.alu .mulhu (9 : Fin 32) (22 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fsq_at_e8 : fetchRel feSquareInnerCode 0xE8 = some (.alu .mulhu a3 (26 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fsq_at_ec : fetchRel feSquareInnerCode 0xEC = some (.aluImm .sll (30 : Fin 32) a6 0x1, 4) := by decide
theorem fsq_at_f0 : fetchRel feSquareInnerCode 0xF0 = some (.alu .sltu (8 : Fin 32) (21 : Fin 32) (8 : Fin 32), 4) := by decide
theorem fsq_at_f4 : fetchRel feSquareInnerCode 0xF4 = some (.alu .add (8 : Fin 32) (8 : Fin 32) ra, 2) := by decide
theorem fsq_at_f6 : fetchRel feSquareInnerCode 0xF6 = some (.alu .mul ra (5 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fsq_at_fa : fetchRel feSquareInnerCode 0xFA = some (.alu .mulhu a5 (5 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fsq_at_fe : fetchRel feSquareInnerCode 0xFE = some (.alu .mulhu a1 (27 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fsq_at_102 : fetchRel feSquareInnerCode 0x102 = some (.alu .mulhu (17 : Fin 32) (24 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_106 : fetchRel feSquareInnerCode 0x106 = some (.alu .mul a0 (27 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fsq_at_10a : fetchRel feSquareInnerCode 0x10A = some (.alu .add a4 a4 a2, 2) := by decide
theorem fsq_at_10c : fetchRel feSquareInnerCode 0x10C = some (.alu .mul a6 (24 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_110 : fetchRel feSquareInnerCode 0x110 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem fsq_at_112 : fetchRel feSquareInnerCode 0x112 = some (.alu .sltu a2 a4 a2, 4) := by decide
theorem fsq_at_116 : fetchRel feSquareInnerCode 0x116 = some (.alu .add (7 : Fin 32) (7 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fsq_at_118 : fetchRel feSquareInnerCode 0x118 = some (.alu .add a2 a2 a3, 2) := by decide
theorem fsq_at_11a : fetchRel feSquareInnerCode 0x11A = some (.aluImm .sll a2 a2 0x1, 2) := by decide
theorem fsq_at_11c : fetchRel feSquareInnerCode 0x11C = some (.aluImm .srl a3 a4 0x1F, 4) := by decide
theorem fsq_at_120 : fetchRel feSquareInnerCode 0x120 = some (.alu .or a2 a2 a3, 2) := by decide
theorem fsq_at_122 : fetchRel feSquareInnerCode 0x122 = some (.alu .add a1 a1 a5, 2) := by decide
theorem fsq_at_124 : fetchRel feSquareInnerCode 0x124 = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem fsq_at_126 : fetchRel feSquareInnerCode 0x126 = some (.alu .add ra ra a0, 2) := by decide
theorem fsq_at_128 : fetchRel feSquareInnerCode 0x128 = some (.aluImm .sll a4 a4 0x1, 2) := by decide
theorem fsq_at_12a : fetchRel feSquareInnerCode 0x12A = some (.alu .add a6 a6 ra, 2) := by decide
theorem fsq_at_12c : fetchRel feSquareInnerCode 0x12C = some (.alu .sltu a0 ra a0, 4) := by decide
theorem fsq_at_130 : fetchRel feSquareInnerCode 0x130 = some (.alu .sltu a3 a6 ra, 4) := by decide
theorem fsq_at_134 : fetchRel feSquareInnerCode 0x134 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fsq_at_136 : fetchRel feSquareInnerCode 0x136 = some (.alu .add a4 a4 a6, 2) := by decide
theorem fsq_at_138 : fetchRel feSquareInnerCode 0x138 = some (.alu .mul (17 : Fin 32) (23 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fsq_at_13c : fetchRel feSquareInnerCode 0x13C = some (.alu .mulhu (25 : Fin 32) (23 : Fin 32) (25 : Fin 32), 4) := by decide
theorem fsq_at_140 : fetchRel feSquareInnerCode 0x140 = some (.alu .mul (9 : Fin 32) (20 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_144 : fetchRel feSquareInnerCode 0x144 = some (.alu .mulhu (8 : Fin 32) (20 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_148 : fetchRel feSquareInnerCode 0x148 = some (.alu .add a0 a0 a3, 2) := by decide
theorem fsq_at_14a : fetchRel feSquareInnerCode 0x14A = some (.alu .sltu a3 a4 a6, 4) := by decide
theorem fsq_at_14e : fetchRel feSquareInnerCode 0x14E = some (.alu .add a0 a0 a3, 2) := by decide
theorem fsq_at_150 : fetchRel feSquareInnerCode 0x150 = some (.store .sw (6 : Fin 32) (21 : Fin 32) 0x0, 4) := by decide
theorem fsq_at_154 : fetchRel feSquareInnerCode 0x154 = some (.store .sw (6 : Fin 32) (7 : Fin 32) 0x4, 4) := by decide
theorem fsq_at_158 : fetchRel feSquareInnerCode 0x158 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fsq_at_15a : fetchRel feSquareInnerCode 0x15A = some (.alu .mul a2 (22 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_15e : fetchRel feSquareInnerCode 0x15E = some (.alu .mul a3 (26 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fsq_at_162 : fetchRel feSquareInnerCode 0x162 = some (.alu .mulhu a1 (22 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_166 : fetchRel feSquareInnerCode 0x166 = some (.alu .mulhu a5 (26 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fsq_at_16a : fetchRel feSquareInnerCode 0x16A = some (.alu .add (8 : Fin 32) (8 : Fin 32) (25 : Fin 32), 2) := by decide
theorem fsq_at_16c : fetchRel feSquareInnerCode 0x16C = some (.alu .add (17 : Fin 32) (17 : Fin 32) (9 : Fin 32), 2) := by decide
theorem fsq_at_16e : fetchRel feSquareInnerCode 0x16E = some (.alu .sltu (9 : Fin 32) (17 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fsq_at_172 : fetchRel feSquareInnerCode 0x172 = some (.store .sw (6 : Fin 32) a4 0x8, 4) := by decide
theorem fsq_at_176 : fetchRel feSquareInnerCode 0x176 = some (.store .sw (6 : Fin 32) a0 0xC, 4) := by decide
theorem fsq_at_17a : fetchRel feSquareInnerCode 0x17A = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem fsq_at_17c : fetchRel feSquareInnerCode 0x17C = some (.alu .mulhu a0 (27 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fsq_at_180 : fetchRel feSquareInnerCode 0x180 = some (.alu .mul a4 (27 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fsq_at_184 : fetchRel feSquareInnerCode 0x184 = some (.alu .mulhu (9 : Fin 32) (24 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_188 : fetchRel feSquareInnerCode 0x188 = some (.alu .add a3 a3 a2, 2) := by decide
theorem fsq_at_18a : fetchRel feSquareInnerCode 0x18A = some (.alu .add a1 a1 a5, 2) := by decide
theorem fsq_at_18c : fetchRel feSquareInnerCode 0x18C = some (.alu .sltu a2 a3 a2, 4) := by decide
theorem fsq_at_190 : fetchRel feSquareInnerCode 0x190 = some (.alu .mul a5 (24 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_194 : fetchRel feSquareInnerCode 0x194 = some (.alu .add (27 : Fin 32) x0 (28 : Fin 32), 2) := by decide
theorem fsq_at_196 : fetchRel feSquareInnerCode 0x196 = some (.alu .add a1 a1 a2, 2) := by decide
theorem fsq_at_198 : fetchRel feSquareInnerCode 0x198 = some (.aluImm .sll a1 a1 0x1, 2) := by decide
theorem fsq_at_19a : fetchRel feSquareInnerCode 0x19A = some (.aluImm .srl a2 a3 0x1F, 4) := by decide
theorem fsq_at_19e : fetchRel feSquareInnerCode 0x19E = some (.alu .or a6 a1 a2, 4) := by decide
theorem fsq_at_1a2 : fetchRel feSquareInnerCode 0x1A2 = some (.aluImm .sll a2 a3 0x1, 4) := by decide
theorem fsq_at_1a6 : fetchRel feSquareInnerCode 0x1A6 = some (.alu .add a4 a4 (17 : Fin 32), 2) := by decide
theorem fsq_at_1a8 : fetchRel feSquareInnerCode 0x1A8 = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem fsq_at_1aa : fetchRel feSquareInnerCode 0x1AA = some (.alu .sltu a3 a4 (17 : Fin 32), 4) := by decide
theorem fsq_at_1ae : fetchRel feSquareInnerCode 0x1AE = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem fsq_at_1b0 : fetchRel feSquareInnerCode 0x1B0 = some (.alu .mul (9 : Fin 32) (18 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_1b4 : fetchRel feSquareInnerCode 0x1B4 = some (.alu .mul (8 : Fin 32) (23 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fsq_at_1b8 : fetchRel feSquareInnerCode 0x1B8 = some (.alu .add a0 a0 a3, 2) := by decide
theorem fsq_at_1ba : fetchRel feSquareInnerCode 0x1BA = some (.alu .add a5 a5 a4, 2) := by decide
theorem fsq_at_1bc : fetchRel feSquareInnerCode 0x1BC = some (.alu .sltu a3 a5 a4, 4) := by decide
theorem fsq_at_1c0 : fetchRel feSquareInnerCode 0x1C0 = some (.alu .add (17 : Fin 32) a5 a2, 4) := by decide
theorem fsq_at_1c4 : fetchRel feSquareInnerCode 0x1C4 = some (.alu .mulhu (7 : Fin 32) (18 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_1c8 : fetchRel feSquareInnerCode 0x1C8 = some (.alu .mulhu (21 : Fin 32) (23 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fsq_at_1cc : fetchRel feSquareInnerCode 0x1CC = some (.alu .add a0 a0 a3, 2) := by decide
theorem fsq_at_1ce : fetchRel feSquareInnerCode 0x1CE = some (.alu .sltu a3 (17 : Fin 32) a5, 4) := by decide
theorem fsq_at_1d2 : fetchRel feSquareInnerCode 0x1D2 = some (.alu .mulhu (25 : Fin 32) (24 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fsq_at_1d6 : fetchRel feSquareInnerCode 0x1D6 = some (.alu .mul a2 (24 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fsq_at_1da : fetchRel feSquareInnerCode 0x1DA = some (.alu .add a0 a0 a3, 2) := by decide
theorem fsq_at_1dc : fetchRel feSquareInnerCode 0x1DC = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem fsq_at_1de : fetchRel feSquareInnerCode 0x1DE = some (.alu .mul a3 (22 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fsq_at_1e2 : fetchRel feSquareInnerCode 0x1E2 = some (.alu .mul a4 (26 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fsq_at_1e6 : fetchRel feSquareInnerCode 0x1E6 = some (.alu .mulhu a1 (22 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fsq_at_1ea : fetchRel feSquareInnerCode 0x1EA = some (.alu .mulhu a5 (26 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fsq_at_1ee : fetchRel feSquareInnerCode 0x1EE = some (.alu .add (7 : Fin 32) (7 : Fin 32) (21 : Fin 32), 2) := by decide
theorem fsq_at_1f0 : fetchRel feSquareInnerCode 0x1F0 = some (.alu .sltu (9 : Fin 32) (8 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fsq_at_1f4 : fetchRel feSquareInnerCode 0x1F4 = some (.alu .add a0 a0 a6, 2) := by decide
theorem fsq_at_1f6 : fetchRel feSquareInnerCode 0x1F6 = some (.alu .add (7 : Fin 32) (7 : Fin 32) (9 : Fin 32), 2) := by decide
theorem fsq_at_1f8 : fetchRel feSquareInnerCode 0x1F8 = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem fsq_at_1fa : fetchRel feSquareInnerCode 0x1FA = some (.alu .add (7 : Fin 32) (7 : Fin 32) (25 : Fin 32), 2) := by decide
theorem fsq_at_1fc : fetchRel feSquareInnerCode 0x1FC = some (.aluImm .sll a6 (29 : Fin 32) 0x1, 4) := by decide
theorem fsq_at_200 : fetchRel feSquareInnerCode 0x200 = some (.alu .sltu (8 : Fin 32) a2 (8 : Fin 32), 4) := by decide
theorem fsq_at_204 : fetchRel feSquareInnerCode 0x204 = some (.alu .add (7 : Fin 32) (7 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fsq_at_206 : fetchRel feSquareInnerCode 0x206 = some (.alu .add a4 a4 a3, 2) := by decide
theorem fsq_at_208 : fetchRel feSquareInnerCode 0x208 = some (.alu .add a1 a1 a5, 2) := by decide
theorem fsq_at_20a : fetchRel feSquareInnerCode 0x20A = some (.alu .sltu a3 a4 a3, 4) := by decide
theorem fsq_at_20e : fetchRel feSquareInnerCode 0x20E = some (.alu .add a1 a1 a3, 2) := by decide
theorem fsq_at_210 : fetchRel feSquareInnerCode 0x210 = some (.aluImm .sll a3 a4 0x1, 4) := by decide
theorem fsq_at_214 : fetchRel feSquareInnerCode 0x214 = some (.aluImm .sll a1 a1 0x1, 2) := by decide
theorem fsq_at_216 : fetchRel feSquareInnerCode 0x216 = some (.alu .add a3 a3 a2, 2) := by decide
theorem fsq_at_218 : fetchRel feSquareInnerCode 0x218 = some (.aluImm .srl a4 a4 0x1F, 2) := by decide
theorem fsq_at_21a : fetchRel feSquareInnerCode 0x21A = some (.alu .sltu a2 a3 a2, 4) := by decide
theorem fsq_at_21e : fetchRel feSquareInnerCode 0x21E = some (.alu .or a1 a1 a4, 2) := by decide
theorem fsq_at_220 : fetchRel feSquareInnerCode 0x220 = some (.alu .add a2 a2 (7 : Fin 32), 2) := by decide
theorem fsq_at_222 : fetchRel feSquareInnerCode 0x222 = some (.alu .add a1 a1 a2, 2) := by decide
theorem fsq_at_224 : fetchRel feSquareInnerCode 0x224 = some (.alu .mul a2 (22 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fsq_at_228 : fetchRel feSquareInnerCode 0x228 = some (.alu .mulhu a4 (22 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fsq_at_22c : fetchRel feSquareInnerCode 0x22C = some (.load .lw (9 : Fin 32) sp 0xC, 2) := by decide
theorem fsq_at_22e : fetchRel feSquareInnerCode 0x22E = some (.alu .mul a5 (26 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fsq_at_232 : fetchRel feSquareInnerCode 0x232 = some (.alu .mulhu (8 : Fin 32) (26 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fsq_at_236 : fetchRel feSquareInnerCode 0x236 = some (.alu .add (26 : Fin 32) x0 (9 : Fin 32), 2) := by decide
theorem fsq_at_238 : fetchRel feSquareInnerCode 0x238 = some (.store .sw (6 : Fin 32) (17 : Fin 32) 0x10, 4) := by decide
theorem fsq_at_23c : fetchRel feSquareInnerCode 0x23C = some (.store .sw (6 : Fin 32) a0 0x14, 4) := by decide
theorem fsq_at_240 : fetchRel feSquareInnerCode 0x240 = some (.store .sw (6 : Fin 32) a3 0x18, 4) := by decide
theorem fsq_at_244 : fetchRel feSquareInnerCode 0x244 = some (.store .sw (6 : Fin 32) a1 0x1C, 4) := by decide
theorem fsq_at_248 : fetchRel feSquareInnerCode 0x248 = some (.alu .mulhu (17 : Fin 32) (19 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_24c : fetchRel feSquareInnerCode 0x24C = some (.alu .mul (7 : Fin 32) (19 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_250 : fetchRel feSquareInnerCode 0x250 = some (.alu .mulhu (21 : Fin 32) (31 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_254 : fetchRel feSquareInnerCode 0x254 = some (.alu .mul (9 : Fin 32) (31 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_258 : fetchRel feSquareInnerCode 0x258 = some (.alu .mul a0 (20 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fsq_at_25c : fetchRel feSquareInnerCode 0x25C = some (.alu .mulhu a1 (20 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fsq_at_260 : fetchRel feSquareInnerCode 0x260 = some (.alu .add a5 a5 a2, 2) := by decide
theorem fsq_at_262 : fetchRel feSquareInnerCode 0x262 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem fsq_at_264 : fetchRel feSquareInnerCode 0x264 = some (.alu .sltu a2 a5 a2, 4) := by decide
theorem fsq_at_268 : fetchRel feSquareInnerCode 0x268 = some (.alu .mul (8 : Fin 32) (24 : Fin 32) a6, 4) := by decide
theorem fsq_at_26c : fetchRel feSquareInnerCode 0x26C = some (.alu .add a2 a2 a4, 2) := by decide
theorem fsq_at_26e : fetchRel feSquareInnerCode 0x26E = some (.aluImm .sll a2 a2 0x1, 2) := by decide
theorem fsq_at_270 : fetchRel feSquareInnerCode 0x270 = some (.aluImm .srl a4 a5 0x1F, 4) := by decide
theorem fsq_at_274 : fetchRel feSquareInnerCode 0x274 = some (.alu .mulhu a3 (24 : Fin 32) a6, 4) := by decide
theorem fsq_at_278 : fetchRel feSquareInnerCode 0x278 = some (.alu .or a6 a2 a4, 4) := by decide
theorem fsq_at_27c : fetchRel feSquareInnerCode 0x27C = some (.aluImm .sll a2 a5 0x1, 4) := by decide
theorem fsq_at_280 : fetchRel feSquareInnerCode 0x280 = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem fsq_at_282 : fetchRel feSquareInnerCode 0x282 = some (.alu .sltu a5 a0 (9 : Fin 32), 4) := by decide
theorem fsq_at_286 : fetchRel feSquareInnerCode 0x286 = some (.alu .add a1 a1 (21 : Fin 32), 2) := by decide
theorem fsq_at_288 : fetchRel feSquareInnerCode 0x288 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a0, 2) := by decide
theorem fsq_at_28a : fetchRel feSquareInnerCode 0x28A = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem fsq_at_28c : fetchRel feSquareInnerCode 0x28C = some (.alu .sltu a0 (7 : Fin 32) a0, 4) := by decide
theorem fsq_at_290 : fetchRel feSquareInnerCode 0x290 = some (.alu .add a1 a1 a5, 2) := by decide
theorem fsq_at_292 : fetchRel feSquareInnerCode 0x292 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fsq_at_294 : fetchRel feSquareInnerCode 0x294 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fsq_at_296 : fetchRel feSquareInnerCode 0x296 = some (.alu .sltu a1 (8 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fsq_at_29a : fetchRel feSquareInnerCode 0x29A = some (.alu .add a0 a0 a3, 2) := by decide
theorem fsq_at_29c : fetchRel feSquareInnerCode 0x29C = some (.alu .add (7 : Fin 32) a0 a1, 4) := by decide
theorem fsq_at_2a0 : fetchRel feSquareInnerCode 0x2A0 = some (.alu .add (17 : Fin 32) (8 : Fin 32) a2, 4) := by decide
theorem fsq_at_2a4 : fetchRel feSquareInnerCode 0x2A4 = some (.alu .sltu a1 (17 : Fin 32) (8 : Fin 32), 4) := by decide
theorem fsq_at_2a8 : fetchRel feSquareInnerCode 0x2A8 = some (.alu .mulhu a3 (29 : Fin 32) (22 : Fin 32), 4) := by decide
theorem fsq_at_2ac : fetchRel feSquareInnerCode 0x2AC = some (.load .lw ra sp 0x8, 2) := by decide
theorem fsq_at_2ae : fetchRel feSquareInnerCode 0x2AE = some (.alu .mulhu (21 : Fin 32) ra (5 : Fin 32), 4) := by decide
theorem fsq_at_2b2 : fetchRel feSquareInnerCode 0x2B2 = some (.alu .mul a5 (29 : Fin 32) (22 : Fin 32), 4) := by decide
theorem fsq_at_2b6 : fetchRel feSquareInnerCode 0x2B6 = some (.alu .mulhu a4 (19 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_2ba : fetchRel feSquareInnerCode 0x2BA = some (.load .lw (28 : Fin 32) sp 0x10, 2) := by decide
theorem fsq_at_2bc : fetchRel feSquareInnerCode 0x2BC = some (.alu .mulhu a2 (28 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fsq_at_2c0 : fetchRel feSquareInnerCode 0x2C0 = some (.alu .mul (8 : Fin 32) (19 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_2c4 : fetchRel feSquareInnerCode 0x2C4 = some (.alu .mul a0 (28 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fsq_at_2c8 : fetchRel feSquareInnerCode 0x2C8 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a1, 2) := by decide
theorem fsq_at_2ca : fetchRel feSquareInnerCode 0x2CA = some (.alu .mul a1 ra (5 : Fin 32), 4) := by decide
theorem fsq_at_2ce : fetchRel feSquareInnerCode 0x2CE = some (.aluImm .sll (20 : Fin 32) (26 : Fin 32) 0x1, 4) := by decide
theorem fsq_at_2d2 : fetchRel feSquareInnerCode 0x2D2 = some (.alu .add a6 a6 (7 : Fin 32), 2) := by decide
theorem fsq_at_2d4 : fetchRel feSquareInnerCode 0x2D4 = some (.alu .mul (7 : Fin 32) (24 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fsq_at_2d8 : fetchRel feSquareInnerCode 0x2D8 = some (.aluImm .sll a3 a3 0x1, 2) := by decide
theorem fsq_at_2da : fetchRel feSquareInnerCode 0x2DA = some (.alu .mulhu (25 : Fin 32) (24 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fsq_at_2de : fetchRel feSquareInnerCode 0x2DE = some (.aluImm .srl (9 : Fin 32) a5 0x1F, 4) := by decide
theorem fsq_at_2e2 : fetchRel feSquareInnerCode 0x2E2 = some (.alu .or a3 a3 (9 : Fin 32), 2) := by decide
theorem fsq_at_2e4 : fetchRel feSquareInnerCode 0x2E4 = some (.alu .add a2 a2 a4, 2) := by decide
theorem fsq_at_2e6 : fetchRel feSquareInnerCode 0x2E6 = some (.alu .add a2 a2 (21 : Fin 32), 2) := by decide
theorem fsq_at_2e8 : fetchRel feSquareInnerCode 0x2E8 = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem fsq_at_2ea : fetchRel feSquareInnerCode 0x2EA = some (.alu .sltu a4 a0 (8 : Fin 32), 4) := by decide
theorem fsq_at_2ee : fetchRel feSquareInnerCode 0x2EE = some (.alu .add a1 a1 a0, 2) := by decide
theorem fsq_at_2f0 : fetchRel feSquareInnerCode 0x2F0 = some (.alu .add a2 a2 a4, 2) := by decide
theorem fsq_at_2f2 : fetchRel feSquareInnerCode 0x2F2 = some (.alu .sltu a0 a1 a0, 4) := by decide
theorem fsq_at_2f6 : fetchRel feSquareInnerCode 0x2F6 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fsq_at_2f8 : fetchRel feSquareInnerCode 0x2F8 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a1, 2) := by decide
theorem fsq_at_2fa : fetchRel feSquareInnerCode 0x2FA = some (.alu .add a0 a0 (25 : Fin 32), 2) := by decide
theorem fsq_at_2fc : fetchRel feSquareInnerCode 0x2FC = some (.alu .sltu a1 (7 : Fin 32) a1, 4) := by decide
theorem fsq_at_300 : fetchRel feSquareInnerCode 0x300 = some (.aluImm .sll a5 a5 0x1, 2) := by decide
theorem fsq_at_302 : fetchRel feSquareInnerCode 0x302 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fsq_at_304 : fetchRel feSquareInnerCode 0x304 = some (.alu .add a0 a0 a3, 2) := by decide
theorem fsq_at_306 : fetchRel feSquareInnerCode 0x306 = some (.alu .add a5 a5 (7 : Fin 32), 2) := by decide
theorem fsq_at_308 : fetchRel feSquareInnerCode 0x308 = some (.alu .sltu a1 a5 (7 : Fin 32), 4) := by decide
theorem fsq_at_30c : fetchRel feSquareInnerCode 0x30C = some (.alu .mul a2 (20 : Fin 32) (22 : Fin 32), 4) := by decide
theorem fsq_at_310 : fetchRel feSquareInnerCode 0x310 = some (.alu .mulhu a3 (20 : Fin 32) (22 : Fin 32), 4) := by decide
theorem fsq_at_314 : fetchRel feSquareInnerCode 0x314 = some (.store .sw (6 : Fin 32) (17 : Fin 32) 0x20, 4) := by decide
theorem fsq_at_318 : fetchRel feSquareInnerCode 0x318 = some (.store .sw (6 : Fin 32) a6 0x24, 4) := by decide
theorem fsq_at_31c : fetchRel feSquareInnerCode 0x31C = some (.alu .add a0 a0 a1, 2) := by decide
theorem fsq_at_31e : fetchRel feSquareInnerCode 0x31E = some (.alu .mulhu a1 (19 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_322 : fetchRel feSquareInnerCode 0x322 = some (.alu .mulhu a4 (31 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fsq_at_326 : fetchRel feSquareInnerCode 0x326 = some (.alu .mulhu (9 : Fin 32) (30 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_32a : fetchRel feSquareInnerCode 0x32A = some (.alu .mul a6 (19 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_32e : fetchRel feSquareInnerCode 0x32E = some (.alu .mul (8 : Fin 32) (31 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fsq_at_332 : fetchRel feSquareInnerCode 0x332 = some (.store .sw (6 : Fin 32) a5 0x28, 4) := by decide
theorem fsq_at_336 : fetchRel feSquareInnerCode 0x336 = some (.store .sw (6 : Fin 32) a0 0x2C, 4) := by decide
theorem fsq_at_33a : fetchRel feSquareInnerCode 0x33A = some (.alu .mul a0 (30 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_33e : fetchRel feSquareInnerCode 0x33E = some (.aluImm .srl a5 a2 0x1F, 4) := by decide
theorem fsq_at_342 : fetchRel feSquareInnerCode 0x342 = some (.aluImm .sll a3 a3 0x1, 2) := by decide
theorem fsq_at_344 : fetchRel feSquareInnerCode 0x344 = some (.alu .or (17 : Fin 32) a3 a5, 4) := by decide
theorem fsq_at_348 : fetchRel feSquareInnerCode 0x348 = some (.alu .mul (7 : Fin 32) (29 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_34c : fetchRel feSquareInnerCode 0x34C = some (.alu .add a1 a1 a4, 2) := by decide
theorem fsq_at_34e : fetchRel feSquareInnerCode 0x34E = some (.alu .mulhu a4 (29 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_352 : fetchRel feSquareInnerCode 0x352 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem fsq_at_354 : fetchRel feSquareInnerCode 0x354 = some (.load .lw (18 : Fin 32) sp 0x14, 2) := by decide
theorem fsq_at_356 : fetchRel feSquareInnerCode 0x356 = some (.alu .mul (9 : Fin 32) (24 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fsq_at_35a : fetchRel feSquareInnerCode 0x35A = some (.alu .mulhu a3 (24 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fsq_at_35e : fetchRel feSquareInnerCode 0x35E = some (.alu .add a6 a6 (8 : Fin 32), 2) := by decide
theorem fsq_at_360 : fetchRel feSquareInnerCode 0x360 = some (.alu .sltu (8 : Fin 32) a6 (8 : Fin 32), 4) := by decide
theorem fsq_at_364 : fetchRel feSquareInnerCode 0x364 = some (.alu .add a0 a0 a6, 2) := by decide
theorem fsq_at_366 : fetchRel feSquareInnerCode 0x366 = some (.alu .sltu a5 a0 a6, 4) := by decide
theorem fsq_at_36a : fetchRel feSquareInnerCode 0x36A = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem fsq_at_36c : fetchRel feSquareInnerCode 0x36C = some (.alu .add a1 a1 a5, 2) := by decide
theorem fsq_at_36e : fetchRel feSquareInnerCode 0x36E = some (.alu .add (7 : Fin 32) (7 : Fin 32) a0, 2) := by decide
theorem fsq_at_370 : fetchRel feSquareInnerCode 0x370 = some (.alu .add a1 a1 a4, 2) := by decide
theorem fsq_at_372 : fetchRel feSquareInnerCode 0x372 = some (.alu .sltu a0 (7 : Fin 32) a0, 4) := by decide
theorem fsq_at_376 : fetchRel feSquareInnerCode 0x376 = some (.aluImm .sll a2 a2 0x1, 2) := by decide
theorem fsq_at_378 : fetchRel feSquareInnerCode 0x378 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fsq_at_37a : fetchRel feSquareInnerCode 0x37A = some (.alu .add a0 a0 a3, 2) := by decide
theorem fsq_at_37c : fetchRel feSquareInnerCode 0x37C = some (.alu .add (9 : Fin 32) (9 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fsq_at_37e : fetchRel feSquareInnerCode 0x37E = some (.alu .sltu a1 (9 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fsq_at_382 : fetchRel feSquareInnerCode 0x382 = some (.alu .mulhu a6 (29 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_386 : fetchRel feSquareInnerCode 0x386 = some (.alu .mulhu a4 ra (28 : Fin 32), 4) := by decide
theorem fsq_at_38a : fetchRel feSquareInnerCode 0x38A = some (.alu .mulhu a5 (31 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fsq_at_38e : fetchRel feSquareInnerCode 0x38E = some (.alu .mul (8 : Fin 32) ra (28 : Fin 32), 4) := by decide
theorem fsq_at_392 : fetchRel feSquareInnerCode 0x392 = some (.alu .mul a3 (31 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fsq_at_396 : fetchRel feSquareInnerCode 0x396 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fsq_at_398 : fetchRel feSquareInnerCode 0x398 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem fsq_at_39a : fetchRel feSquareInnerCode 0x39A = some (.alu .add a0 a0 (17 : Fin 32), 2) := by decide
theorem fsq_at_39c : fetchRel feSquareInnerCode 0x39C = some (.alu .sltu a1 a2 (9 : Fin 32), 4) := by decide
theorem fsq_at_3a0 : fetchRel feSquareInnerCode 0x3A0 = some (.alu .mul (17 : Fin 32) (29 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_3a4 : fetchRel feSquareInnerCode 0x3A4 = some (.alu .mul (9 : Fin 32) (18 : Fin 32) (22 : Fin 32), 4) := by decide
theorem fsq_at_3a8 : fetchRel feSquareInnerCode 0x3A8 = some (.alu .add (7 : Fin 32) a0 a1, 4) := by decide
theorem fsq_at_3ac : fetchRel feSquareInnerCode 0x3AC = some (.alu .mulhu a1 (18 : Fin 32) (22 : Fin 32), 4) := by decide
theorem fsq_at_3b0 : fetchRel feSquareInnerCode 0x3B0 = some (.alu .add a4 a4 a5, 2) := by decide
theorem fsq_at_3b2 : fetchRel feSquareInnerCode 0x3B2 = some (.alu .mul a5 (26 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_3b6 : fetchRel feSquareInnerCode 0x3B6 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem fsq_at_3b8 : fetchRel feSquareInnerCode 0x3B8 = some (.alu .add a4 a4 a6, 2) := by decide
theorem fsq_at_3ba : fetchRel feSquareInnerCode 0x3BA = some (.alu .mulhu a0 (26 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_3be : fetchRel feSquareInnerCode 0x3BE = some (.alu .sltu (8 : Fin 32) a3 (8 : Fin 32), 4) := by decide
theorem fsq_at_3c2 : fetchRel feSquareInnerCode 0x3C2 = some (.store .sw (6 : Fin 32) a2 0x30, 4) := by decide
theorem fsq_at_3c6 : fetchRel feSquareInnerCode 0x3C6 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem fsq_at_3c8 : fetchRel feSquareInnerCode 0x3C8 = some (.aluImm .srl a2 (9 : Fin 32) 0x1F, 4) := by decide
theorem fsq_at_3cc : fetchRel feSquareInnerCode 0x3CC = some (.alu .add (17 : Fin 32) (17 : Fin 32) a3, 2) := by decide
theorem fsq_at_3ce : fetchRel feSquareInnerCode 0x3CE = some (.aluImm .sll a1 a1 0x1, 2) := by decide
theorem fsq_at_3d0 : fetchRel feSquareInnerCode 0x3D0 = some (.alu .sltu a3 (17 : Fin 32) a3, 4) := by decide
theorem fsq_at_3d4 : fetchRel feSquareInnerCode 0x3D4 = some (.alu .or a1 a1 a2, 2) := by decide
theorem fsq_at_3d6 : fetchRel feSquareInnerCode 0x3D6 = some (.alu .add a3 a3 a4, 2) := by decide
theorem fsq_at_3d8 : fetchRel feSquareInnerCode 0x3D8 = some (.aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem fsq_at_3da : fetchRel feSquareInnerCode 0x3DA = some (.alu .add a5 a5 (17 : Fin 32), 2) := by decide
theorem fsq_at_3dc : fetchRel feSquareInnerCode 0x3DC = some (.alu .add a0 a0 a3, 2) := by decide
theorem fsq_at_3de : fetchRel feSquareInnerCode 0x3DE = some (.alu .sltu a2 a5 (17 : Fin 32), 4) := by decide
theorem fsq_at_3e2 : fetchRel feSquareInnerCode 0x3E2 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fsq_at_3e4 : fetchRel feSquareInnerCode 0x3E4 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a5, 2) := by decide
theorem fsq_at_3e6 : fetchRel feSquareInnerCode 0x3E6 = some (.alu .mulhu a2 (29 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_3ea : fetchRel feSquareInnerCode 0x3EA = some (.alu .mulhu a3 (19 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fsq_at_3ee : fetchRel feSquareInnerCode 0x3EE = some (.store .sw (6 : Fin 32) (7 : Fin 32) 0x34, 4) := by decide
theorem fsq_at_3f2 : fetchRel feSquareInnerCode 0x3F2 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fsq_at_3f4 : fetchRel feSquareInnerCode 0x3F4 = some (.alu .sltu a1 (9 : Fin 32) a5, 4) := by decide
theorem fsq_at_3f8 : fetchRel feSquareInnerCode 0x3F8 = some (.alu .mulhu a4 (30 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_3fc : fetchRel feSquareInnerCode 0x3FC = some (.alu .mul a5 (29 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_400 : fetchRel feSquareInnerCode 0x400 = some (.alu .mul (8 : Fin 32) (19 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fsq_at_404 : fetchRel feSquareInnerCode 0x404 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fsq_at_406 : fetchRel feSquareInnerCode 0x406 = some (.alu .mul a1 (30 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_40a : fetchRel feSquareInnerCode 0x40A = some (.store .sw (6 : Fin 32) (9 : Fin 32) 0x38, 4) := by decide
theorem fsq_at_40e : fetchRel feSquareInnerCode 0x40E = some (.store .sw (6 : Fin 32) a0 0x3C, 4) := by decide
theorem fsq_at_412 : fetchRel feSquareInnerCode 0x412 = some (.alu .mul (17 : Fin 32) (20 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_416 : fetchRel feSquareInnerCode 0x416 = some (.alu .add a2 a2 a3, 2) := by decide
theorem fsq_at_418 : fetchRel feSquareInnerCode 0x418 = some (.alu .mulhu a3 (18 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_41c : fetchRel feSquareInnerCode 0x41C = some (.alu .mulhu (9 : Fin 32) (20 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_420 : fetchRel feSquareInnerCode 0x420 = some (.alu .add a4 a4 a2, 2) := by decide
theorem fsq_at_422 : fetchRel feSquareInnerCode 0x422 = some (.load .lw (30 : Fin 32) sp 0x18, 2) := by decide
theorem fsq_at_424 : fetchRel feSquareInnerCode 0x424 = some (.alu .mul a6 (30 : Fin 32) (22 : Fin 32), 4) := by decide
theorem fsq_at_428 : fetchRel feSquareInnerCode 0x428 = some (.alu .mulhu a2 (30 : Fin 32) (22 : Fin 32), 4) := by decide
theorem fsq_at_42c : fetchRel feSquareInnerCode 0x42C = some (.alu .add (8 : Fin 32) (8 : Fin 32) a5, 2) := by decide
theorem fsq_at_42e : fetchRel feSquareInnerCode 0x42E = some (.alu .sltu a5 (8 : Fin 32) a5, 4) := by decide
theorem fsq_at_432 : fetchRel feSquareInnerCode 0x432 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem fsq_at_434 : fetchRel feSquareInnerCode 0x434 = some (.alu .add a4 a4 a5, 2) := by decide
theorem fsq_at_436 : fetchRel feSquareInnerCode 0x436 = some (.alu .sltu a5 a1 (8 : Fin 32), 4) := by decide
theorem fsq_at_43a : fetchRel feSquareInnerCode 0x43A = some (.alu .add a4 a4 a5, 2) := by decide
theorem fsq_at_43c : fetchRel feSquareInnerCode 0x43C = some (.alu .add a0 a1 (17 : Fin 32), 4) := by decide
theorem fsq_at_440 : fetchRel feSquareInnerCode 0x440 = some (.alu .mul a5 (18 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_444 : fetchRel feSquareInnerCode 0x444 = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fsq_at_448 : fetchRel feSquareInnerCode 0x448 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem fsq_at_44a : fetchRel feSquareInnerCode 0x44A = some (.alu .add a1 a1 a3, 2) := by decide
theorem fsq_at_44c : fetchRel feSquareInnerCode 0x44C = some (.aluImm .srl a3 a6 0x1F, 4) := by decide
theorem fsq_at_450 : fetchRel feSquareInnerCode 0x450 = some (.aluImm .sll a2 a2 0x1, 2) := by decide
theorem fsq_at_452 : fetchRel feSquareInnerCode 0x452 = some (.alu .or (17 : Fin 32) a2 a3, 4) := by decide
theorem fsq_at_456 : fetchRel feSquareInnerCode 0x456 = some (.alu .add (7 : Fin 32) a4 a1, 4) := by decide
theorem fsq_at_45a : fetchRel feSquareInnerCode 0x45A = some (.alu .mul a3 (29 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_45e : fetchRel feSquareInnerCode 0x45E = some (.alu .mulhu a4 (29 : Fin 32) (31 : Fin 32), 4) := by decide
theorem fsq_at_462 : fetchRel feSquareInnerCode 0x462 = some (.alu .mul (9 : Fin 32) (27 : Fin 32) ra, 4) := by decide
theorem fsq_at_466 : fetchRel feSquareInnerCode 0x466 = some (.alu .mulhu (8 : Fin 32) (27 : Fin 32) ra, 4) := by decide
theorem fsq_at_46a : fetchRel feSquareInnerCode 0x46A = some (.alu .add a5 a5 a0, 2) := by decide
theorem fsq_at_46c : fetchRel feSquareInnerCode 0x46C = some (.alu .mulhu a2 (26 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_470 : fetchRel feSquareInnerCode 0x470 = some (.alu .mul a1 (26 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fsq_at_474 : fetchRel feSquareInnerCode 0x474 = some (.alu .sltu a0 a5 a0, 4) := by decide
theorem fsq_at_478 : fetchRel feSquareInnerCode 0x478 = some (.alu .add a0 a0 (7 : Fin 32), 2) := by decide
theorem fsq_at_47a : fetchRel feSquareInnerCode 0x47A = some (.alu .mul (7 : Fin 32) (18 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_47e : fetchRel feSquareInnerCode 0x47E = some (.alu .add (17 : Fin 32) (17 : Fin 32) a0, 2) := by decide
theorem fsq_at_480 : fetchRel feSquareInnerCode 0x480 = some (.alu .mul (28 : Fin 32) (30 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_484 : fetchRel feSquareInnerCode 0x484 = some (.alu .mulhu (5 : Fin 32) (30 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fsq_at_488 : fetchRel feSquareInnerCode 0x488 = some (.alu .mulhu a0 (18 : Fin 32) (23 : Fin 32), 4) := by decide
theorem fsq_at_48c : fetchRel feSquareInnerCode 0x48C = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem fsq_at_48e : fetchRel feSquareInnerCode 0x48E = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem fsq_at_490 : fetchRel feSquareInnerCode 0x490 = some (.alu .add a2 a2 a4, 2) := by decide
theorem fsq_at_492 : fetchRel feSquareInnerCode 0x492 = some (.alu .sltu a3 (9 : Fin 32) a3, 4) := by decide
theorem fsq_at_496 : fetchRel feSquareInnerCode 0x496 = some (.alu .add a2 a2 a3, 2) := by decide
theorem fsq_at_498 : fetchRel feSquareInnerCode 0x498 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem fsq_at_49a : fetchRel feSquareInnerCode 0x49A = some (.alu .sltu a3 a1 (9 : Fin 32), 4) := by decide
theorem fsq_at_49e : fetchRel feSquareInnerCode 0x49E = some (.alu .add (7 : Fin 32) (7 : Fin 32) a1, 2) := by decide
theorem fsq_at_4a0 : fetchRel feSquareInnerCode 0x4A0 = some (.alu .add a2 a2 a3, 2) := by decide
theorem fsq_at_4a2 : fetchRel feSquareInnerCode 0x4A2 = some (.alu .sltu a1 (7 : Fin 32) a1, 4) := by decide
theorem fsq_at_4a6 : fetchRel feSquareInnerCode 0x4A6 = some (.alu .add a0 a0 a2, 2) := by decide
theorem fsq_at_4a8 : fetchRel feSquareInnerCode 0x4A8 = some (.alu .add a1 a1 (5 : Fin 32), 2) := by decide
theorem fsq_at_4aa : fetchRel feSquareInnerCode 0x4AA = some (.alu .add a0 a0 a1, 2) := by decide
theorem fsq_at_4ac : fetchRel feSquareInnerCode 0x4AC = some (.aluImm .sll a6 a6 0x1, 2) := by decide
theorem fsq_at_4ae : fetchRel feSquareInnerCode 0x4AE = some (.alu .add a6 a6 a5, 2) := by decide
theorem fsq_at_4b0 : fetchRel feSquareInnerCode 0x4B0 = some (.alu .add (28 : Fin 32) (28 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fsq_at_4b2 : fetchRel feSquareInnerCode 0x4B2 = some (.alu .sltu a1 a6 a5, 4) := by decide
theorem fsq_at_4b6 : fetchRel feSquareInnerCode 0x4B6 = some (.alu .sltu a2 (28 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fsq_at_4ba : fetchRel feSquareInnerCode 0x4BA = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem fsq_at_4bc : fetchRel feSquareInnerCode 0x4BC = some (.alu .add a0 a0 a2, 2) := by decide
theorem fsq_at_4be : fetchRel feSquareInnerCode 0x4BE = some (.store .sw (6 : Fin 32) a6 0x40, 4) := by decide
theorem fsq_at_4c2 : fetchRel feSquareInnerCode 0x4C2 = some (.alu .add a2 x0 (6 : Fin 32), 2) := by decide
theorem fsq_at_4c4 : fetchRel feSquareInnerCode 0x4C4 = some (.store .sw a2 a1 0x44, 2) := by decide
theorem fsq_at_4c6 : fetchRel feSquareInnerCode 0x4C6 = some (.store .sw (6 : Fin 32) (28 : Fin 32) 0x48, 4) := by decide
theorem fsq_at_4ca : fetchRel feSquareInnerCode 0x4CA = some (.store .sw a2 a0 0x4C, 2) := by decide
theorem fsq_at_4cc : fetchRel feSquareInnerCode 0x4CC = some (.load .lw ra sp 0x4C, 2) := by decide
theorem fsq_at_4ce : fetchRel feSquareInnerCode 0x4CE = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem fsq_at_4d0 : fetchRel feSquareInnerCode 0x4D0 = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem fsq_at_4d2 : fetchRel feSquareInnerCode 0x4D2 = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem fsq_at_4d4 : fetchRel feSquareInnerCode 0x4D4 = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem fsq_at_4d6 : fetchRel feSquareInnerCode 0x4D6 = some (.load .lw (20 : Fin 32) sp 0x38, 2) := by decide
theorem fsq_at_4d8 : fetchRel feSquareInnerCode 0x4D8 = some (.load .lw (21 : Fin 32) sp 0x34, 2) := by decide
theorem fsq_at_4da : fetchRel feSquareInnerCode 0x4DA = some (.load .lw (22 : Fin 32) sp 0x30, 2) := by decide
theorem fsq_at_4dc : fetchRel feSquareInnerCode 0x4DC = some (.load .lw (23 : Fin 32) sp 0x2C, 2) := by decide
theorem fsq_at_4de : fetchRel feSquareInnerCode 0x4DE = some (.load .lw (24 : Fin 32) sp 0x28, 2) := by decide
theorem fsq_at_4e0 : fetchRel feSquareInnerCode 0x4E0 = some (.load .lw (25 : Fin 32) sp 0x24, 2) := by decide
theorem fsq_at_4e2 : fetchRel feSquareInnerCode 0x4E2 = some (.load .lw (26 : Fin 32) sp 0x20, 2) := by decide
theorem fsq_at_4e4 : fetchRel feSquareInnerCode 0x4E4 = some (.load .lw (27 : Fin 32) sp 0x1C, 2) := by decide
theorem fsq_at_4e6 : fetchRel feSquareInnerCode 0x4E6 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem fsq_at_4e8 : fetchRel feSquareInnerCode 0x4E8 = some (.jalr x0 ra 0x0, 2) := by decide

end

end C3.RV32
