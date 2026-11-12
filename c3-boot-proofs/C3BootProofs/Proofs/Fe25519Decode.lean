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

end

end C3.RV32
