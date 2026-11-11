import C3BootProofs.Proofs.Block

/-!
# The P-256 field multiplication's instructions, decoded from the image's bytes

`scripts/decode-lemmas.py` wrote these from `llvm-objdump` output; `decide`
checks each against the extracted bytes.
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

theorem si_at_0 : fetchRel subInnerCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem si_at_2 : fetchRel subInnerCode 0x2 = some (.auipc (5 : Fin 32) 0xE000, 4) := by decide
theorem si_at_6 : fetchRel subInnerCode 0x6 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFC32, 4) := by decide
theorem si_at_a : fetchRel subInnerCode 0xA = some (.store .sw sp (24 : Fin 32) 0x8, 2) := by decide
theorem si_at_c : fetchRel subInnerCode 0xC = some (.store .sw sp (25 : Fin 32) 0x4, 2) := by decide
theorem si_at_e : fetchRel subInnerCode 0xE = some (.store .sw sp (26 : Fin 32) 0x0, 2) := by decide
theorem si_at_10 : fetchRel subInnerCode 0x10 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem si_at_12 : fetchRel subInnerCode 0x12 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem si_at_14 : fetchRel subInnerCode 0x14 = some (.load .lw a2 a1 0x0, 2) := by decide
theorem si_at_16 : fetchRel subInnerCode 0x16 = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem si_at_18 : fetchRel subInnerCode 0x18 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem si_at_1a : fetchRel subInnerCode 0x1A = some (.alu .add a0 x0 a2, 2) := by decide
theorem si_at_1c : fetchRel subInnerCode 0x1C = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem si_at_1e : fetchRel subInnerCode 0x1E = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem si_at_22 : fetchRel subInnerCode 0x22 = some (.jalr ra ra 0x144, 4) := by decide
theorem si_at_26 : fetchRel subInnerCode 0x26 = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem si_at_28 : fetchRel subInnerCode 0x28 = some (.load .lw a0 (8 : Fin 32) 0x4, 2) := by decide
theorem si_at_2a : fetchRel subInnerCode 0x2A = some (.load .lw a2 (9 : Fin 32) 0x4, 2) := by decide
theorem si_at_2c : fetchRel subInnerCode 0x2C = some (.alu .add a3 x0 a1, 2) := by decide
theorem si_at_2e : fetchRel subInnerCode 0x2E = some (.alu .add a1 x0 a2, 2) := by decide
theorem si_at_30 : fetchRel subInnerCode 0x30 = some (.alu .add a2 x0 a3, 2) := by decide
theorem si_at_32 : fetchRel subInnerCode 0x32 = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem si_at_36 : fetchRel subInnerCode 0x36 = some (.jalr ra ra 0x130, 4) := by decide
theorem si_at_3a : fetchRel subInnerCode 0x3A = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem si_at_3c : fetchRel subInnerCode 0x3C = some (.load .lw a0 (8 : Fin 32) 0x8, 2) := by decide
theorem si_at_3e : fetchRel subInnerCode 0x3E = some (.load .lw a2 (9 : Fin 32) 0x8, 2) := by decide
theorem si_at_40 : fetchRel subInnerCode 0x40 = some (.alu .add a3 x0 a1, 2) := by decide
theorem si_at_42 : fetchRel subInnerCode 0x42 = some (.alu .add a1 x0 a2, 2) := by decide
theorem si_at_44 : fetchRel subInnerCode 0x44 = some (.alu .add a2 x0 a3, 2) := by decide
theorem si_at_46 : fetchRel subInnerCode 0x46 = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem si_at_4a : fetchRel subInnerCode 0x4A = some (.jalr ra ra 0x11C, 4) := by decide
theorem si_at_4e : fetchRel subInnerCode 0x4E = some (.alu .add (21 : Fin 32) x0 a0, 2) := by decide
theorem si_at_50 : fetchRel subInnerCode 0x50 = some (.load .lw a0 (8 : Fin 32) 0xC, 2) := by decide
theorem si_at_52 : fetchRel subInnerCode 0x52 = some (.load .lw a2 (9 : Fin 32) 0xC, 2) := by decide
theorem si_at_54 : fetchRel subInnerCode 0x54 = some (.alu .add a3 x0 a1, 2) := by decide
theorem si_at_56 : fetchRel subInnerCode 0x56 = some (.alu .add a1 x0 a2, 2) := by decide
theorem si_at_58 : fetchRel subInnerCode 0x58 = some (.alu .add a2 x0 a3, 2) := by decide
theorem si_at_5a : fetchRel subInnerCode 0x5A = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem si_at_5e : fetchRel subInnerCode 0x5E = some (.jalr ra ra 0x108, 4) := by decide
theorem si_at_62 : fetchRel subInnerCode 0x62 = some (.alu .add (22 : Fin 32) x0 a0, 2) := by decide
theorem si_at_64 : fetchRel subInnerCode 0x64 = some (.load .lw a0 (8 : Fin 32) 0x10, 2) := by decide
theorem si_at_66 : fetchRel subInnerCode 0x66 = some (.load .lw a2 (9 : Fin 32) 0x10, 2) := by decide
theorem si_at_68 : fetchRel subInnerCode 0x68 = some (.alu .add a3 x0 a1, 2) := by decide
theorem si_at_6a : fetchRel subInnerCode 0x6A = some (.alu .add a1 x0 a2, 2) := by decide
theorem si_at_6c : fetchRel subInnerCode 0x6C = some (.alu .add a2 x0 a3, 2) := by decide
theorem si_at_6e : fetchRel subInnerCode 0x6E = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem si_at_72 : fetchRel subInnerCode 0x72 = some (.jalr ra ra 0xF4, 4) := by decide
theorem si_at_76 : fetchRel subInnerCode 0x76 = some (.alu .add (24 : Fin 32) x0 a0, 2) := by decide
theorem si_at_78 : fetchRel subInnerCode 0x78 = some (.load .lw a0 (8 : Fin 32) 0x14, 2) := by decide
theorem si_at_7a : fetchRel subInnerCode 0x7A = some (.load .lw a2 (9 : Fin 32) 0x14, 2) := by decide
theorem si_at_7c : fetchRel subInnerCode 0x7C = some (.alu .add a3 x0 a1, 2) := by decide
theorem si_at_7e : fetchRel subInnerCode 0x7E = some (.alu .add a1 x0 a2, 2) := by decide
theorem si_at_80 : fetchRel subInnerCode 0x80 = some (.alu .add a2 x0 a3, 2) := by decide
theorem si_at_82 : fetchRel subInnerCode 0x82 = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem si_at_86 : fetchRel subInnerCode 0x86 = some (.jalr ra ra 0xE0, 4) := by decide
theorem si_at_8a : fetchRel subInnerCode 0x8A = some (.alu .add (23 : Fin 32) x0 a0, 2) := by decide
theorem si_at_8c : fetchRel subInnerCode 0x8C = some (.load .lw a0 (8 : Fin 32) 0x18, 2) := by decide
theorem si_at_8e : fetchRel subInnerCode 0x8E = some (.load .lw a2 (9 : Fin 32) 0x18, 2) := by decide
theorem si_at_90 : fetchRel subInnerCode 0x90 = some (.alu .add a3 x0 a1, 2) := by decide
theorem si_at_92 : fetchRel subInnerCode 0x92 = some (.alu .add a1 x0 a2, 2) := by decide
theorem si_at_94 : fetchRel subInnerCode 0x94 = some (.alu .add a2 x0 a3, 2) := by decide
theorem si_at_96 : fetchRel subInnerCode 0x96 = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem si_at_9a : fetchRel subInnerCode 0x9A = some (.jalr ra ra 0xCC, 4) := by decide
theorem si_at_9e : fetchRel subInnerCode 0x9E = some (.alu .add (25 : Fin 32) x0 a0, 2) := by decide
theorem si_at_a0 : fetchRel subInnerCode 0xA0 = some (.load .lw a0 (8 : Fin 32) 0x1C, 2) := by decide
theorem si_at_a2 : fetchRel subInnerCode 0xA2 = some (.load .lw a2 (9 : Fin 32) 0x1C, 2) := by decide
theorem si_at_a4 : fetchRel subInnerCode 0xA4 = some (.alu .add a3 x0 a1, 2) := by decide
theorem si_at_a6 : fetchRel subInnerCode 0xA6 = some (.alu .add a1 x0 a2, 2) := by decide
theorem si_at_a8 : fetchRel subInnerCode 0xA8 = some (.alu .add a2 x0 a3, 2) := by decide
theorem si_at_aa : fetchRel subInnerCode 0xAA = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem si_at_ae : fetchRel subInnerCode 0xAE = some (.jalr ra ra 0xB8, 4) := by decide
theorem si_at_b2 : fetchRel subInnerCode 0xB2 = some (.alu .add (26 : Fin 32) x0 a0, 2) := by decide
theorem si_at_b4 : fetchRel subInnerCode 0xB4 = some (.load .lw a0 (8 : Fin 32) 0x20, 2) := by decide
theorem si_at_b6 : fetchRel subInnerCode 0xB6 = some (.load .lw a2 (9 : Fin 32) 0x20, 2) := by decide
theorem si_at_b8 : fetchRel subInnerCode 0xB8 = some (.alu .add a3 x0 a1, 2) := by decide
theorem si_at_ba : fetchRel subInnerCode 0xBA = some (.alu .add a1 x0 a2, 2) := by decide
theorem si_at_bc : fetchRel subInnerCode 0xBC = some (.alu .add a2 x0 a3, 2) := by decide
theorem si_at_be : fetchRel subInnerCode 0xBE = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem si_at_c2 : fetchRel subInnerCode 0xC2 = some (.jalr ra ra 0xA4, 4) := by decide
theorem si_at_c6 : fetchRel subInnerCode 0xC6 = some (.alu .add (19 : Fin 32) (19 : Fin 32) a1, 2) := by decide
theorem si_at_c8 : fetchRel subInnerCode 0xC8 = some (.alu .add (20 : Fin 32) (20 : Fin 32) a1, 2) := by decide
theorem si_at_ca : fetchRel subInnerCode 0xCA = some (.alu .sltu a0 (19 : Fin 32) a1, 4) := by decide
theorem si_at_ce : fetchRel subInnerCode 0xCE = some (.alu .add a0 a0 (20 : Fin 32), 2) := by decide
theorem si_at_d0 : fetchRel subInnerCode 0xD0 = some (.alu .sltu a2 (20 : Fin 32) a1, 4) := by decide
theorem si_at_d4 : fetchRel subInnerCode 0xD4 = some (.alu .sltu a3 a0 (20 : Fin 32), 4) := by decide
theorem si_at_d8 : fetchRel subInnerCode 0xD8 = some (.alu .add (21 : Fin 32) (21 : Fin 32) a1, 2) := by decide
theorem si_at_da : fetchRel subInnerCode 0xDA = some (.alu .add a2 a2 a3, 2) := by decide
theorem si_at_dc : fetchRel subInnerCode 0xDC = some (.alu .add a2 a2 (21 : Fin 32), 2) := by decide
theorem si_at_de : fetchRel subInnerCode 0xDE = some (.alu .sltu a3 (21 : Fin 32) a1, 4) := by decide
theorem si_at_e2 : fetchRel subInnerCode 0xE2 = some (.alu .sltu a4 a2 (21 : Fin 32), 4) := by decide
theorem si_at_e6 : fetchRel subInnerCode 0xE6 = some (.alu .add a3 a3 a4, 2) := by decide
theorem si_at_e8 : fetchRel subInnerCode 0xE8 = some (.alu .add (22 : Fin 32) (22 : Fin 32) a3, 2) := by decide
theorem si_at_ea : fetchRel subInnerCode 0xEA = some (.alu .sltu a3 (22 : Fin 32) a3, 4) := by decide
theorem si_at_ee : fetchRel subInnerCode 0xEE = some (.alu .add (24 : Fin 32) (24 : Fin 32) a3, 2) := by decide
theorem si_at_f0 : fetchRel subInnerCode 0xF0 = some (.aluImm .and a4 a1 0x1, 4) := by decide
theorem si_at_f4 : fetchRel subInnerCode 0xF4 = some (.alu .sltu a3 (24 : Fin 32) a3, 4) := by decide
theorem si_at_f8 : fetchRel subInnerCode 0xF8 = some (.alu .add (26 : Fin 32) (26 : Fin 32) a1, 2) := by decide
theorem si_at_fa : fetchRel subInnerCode 0xFA = some (.alu .add (23 : Fin 32) (23 : Fin 32) a3, 2) := by decide
theorem si_at_fc : fetchRel subInnerCode 0xFC = some (.alu .add (25 : Fin 32) (25 : Fin 32) a4, 2) := by decide
theorem si_at_fe : fetchRel subInnerCode 0xFE = some (.alu .sltu a3 (23 : Fin 32) a3, 4) := by decide
theorem si_at_102 : fetchRel subInnerCode 0x102 = some (.alu .sltu a4 (25 : Fin 32) a4, 4) := by decide
theorem si_at_106 : fetchRel subInnerCode 0x106 = some (.alu .add a3 a3 (25 : Fin 32), 2) := by decide
theorem si_at_108 : fetchRel subInnerCode 0x108 = some (.alu .sltu a5 a3 (25 : Fin 32), 4) := by decide
theorem si_at_10c : fetchRel subInnerCode 0x10C = some (.store .sw (18 : Fin 32) (19 : Fin 32) 0x0, 4) := by decide
theorem si_at_110 : fetchRel subInnerCode 0x110 = some (.alu .add (8 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem si_at_112 : fetchRel subInnerCode 0x112 = some (.store .sw (8 : Fin 32) a0 0x4, 2) := by decide
theorem si_at_114 : fetchRel subInnerCode 0x114 = some (.store .sw (8 : Fin 32) a2 0x8, 2) := by decide
theorem si_at_116 : fetchRel subInnerCode 0x116 = some (.store .sw (18 : Fin 32) (22 : Fin 32) 0xC, 4) := by decide
theorem si_at_11a : fetchRel subInnerCode 0x11A = some (.alu .add a4 a4 a5, 2) := by decide
theorem si_at_11c : fetchRel subInnerCode 0x11C = some (.alu .add a4 a4 (26 : Fin 32), 2) := by decide
theorem si_at_11e : fetchRel subInnerCode 0x11E = some (.store .sw (18 : Fin 32) (24 : Fin 32) 0x10, 4) := by decide
theorem si_at_122 : fetchRel subInnerCode 0x122 = some (.store .sw (18 : Fin 32) (23 : Fin 32) 0x14, 4) := by decide
theorem si_at_126 : fetchRel subInnerCode 0x126 = some (.store .sw (8 : Fin 32) a3 0x18, 2) := by decide
theorem si_at_128 : fetchRel subInnerCode 0x128 = some (.store .sw (8 : Fin 32) a4 0x1C, 2) := by decide
theorem si_at_12a : fetchRel subInnerCode 0x12A = some (.store .sw (8 : Fin 32) a1 0x20, 2) := by decide
theorem si_at_12c : fetchRel subInnerCode 0x12C = some (.auipc (5 : Fin 32) 0xE000, 4) := by decide
theorem si_at_130 : fetchRel subInnerCode 0x130 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFD12, 4) := by decide
theorem si_at_134 : fetchRel subInnerCode 0x134 = some (.load .lw (24 : Fin 32) sp 0x8, 2) := by decide
theorem si_at_136 : fetchRel subInnerCode 0x136 = some (.load .lw (25 : Fin 32) sp 0x4, 2) := by decide
theorem si_at_138 : fetchRel subInnerCode 0x138 = some (.load .lw (26 : Fin 32) sp 0x0, 2) := by decide
theorem si_at_13a : fetchRel subInnerCode 0x13A = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem si_at_13c : fetchRel subInnerCode 0x13C = some (.jalr x0 ra 0x0, 2) := by decide

theorem wm_at_0 : fetchRel wideMulCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem wm_at_2 : fetchRel wideMulCode 0x2 = some (.auipc (5 : Fin 32) 0x12000, 4) := by decide
theorem wm_at_6 : fetchRel wideMulCode 0x6 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0x428, 4) := by decide
theorem wm_at_a : fetchRel wideMulCode 0xA = some (.store .sw sp (22 : Fin 32) 0x40, 2) := by decide
theorem wm_at_c : fetchRel wideMulCode 0xC = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem wm_at_e : fetchRel wideMulCode 0xE = some (.alu .add (21 : Fin 32) x0 a1, 2) := by decide
theorem wm_at_10 : fetchRel wideMulCode 0x10 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem wm_at_12 : fetchRel wideMulCode 0x12 = some (.alu .add a0 x0 sp, 2) := by decide
theorem wm_at_14 : fetchRel wideMulCode 0x14 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem wm_at_18 : fetchRel wideMulCode 0x18 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem wm_at_1a : fetchRel wideMulCode 0x1A = some (.alu .add (22 : Fin 32) x0 sp, 2) := by decide
theorem wm_at_1c : fetchRel wideMulCode 0x1C = some (.auipc ra 0x13000, 4) := by decide
theorem wm_at_20 : fetchRel wideMulCode 0x20 = some (.jalr ra ra 0xFFFFF9C8, 4) := by decide
theorem wm_at_24 : fetchRel wideMulCode 0x24 = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem wm_at_26 : fetchRel wideMulCode 0x26 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem wm_at_2a : fetchRel wideMulCode 0x2A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem wm_at_2c : fetchRel wideMulCode 0x2C = some (.aluImm .add (20 : Fin 32) sp 0x20, 4) := by decide
theorem wm_at_30 : fetchRel wideMulCode 0x30 = some (.auipc ra 0x13000, 4) := by decide
theorem wm_at_34 : fetchRel wideMulCode 0x34 = some (.jalr ra ra 0xFFFFF9B4, 4) := by decide
theorem wm_at_38 : fetchRel wideMulCode 0x38 = some (.aluImm .add (5 : Fin 32) x0 0x0, 2) := by decide
theorem wm_at_3a : fetchRel wideMulCode 0x3A = some (.alu .add a6 x0 sp, 2) := by decide
theorem wm_at_3c : fetchRel wideMulCode 0x3C = some (.aluImm .add (6 : Fin 32) x0 0x8, 2) := by decide
theorem wm_at_3e : fetchRel wideMulCode 0x3E = some (.branch .beq (6 : Fin 32) x0 0x72, 4) := by decide
theorem wm_at_42 : fetchRel wideMulCode 0x42 = some (.aluImm .add (28 : Fin 32) x0 0x0, 2) := by decide
theorem wm_at_44 : fetchRel wideMulCode 0x44 = some (.aluImm .sll (17 : Fin 32) (5 : Fin 32) 0x2, 4) := by decide
theorem wm_at_48 : fetchRel wideMulCode 0x48 = some (.alu .add a0 (21 : Fin 32) (17 : Fin 32), 4) := by decide
theorem wm_at_4c : fetchRel wideMulCode 0x4C = some (.load .lw (7 : Fin 32) a0 0x0, 4) := by decide
theorem wm_at_50 : fetchRel wideMulCode 0x50 = some (.aluImm .add (8 : Fin 32) x0 0x8, 2) := by decide
theorem wm_at_52 : fetchRel wideMulCode 0x52 = some (.alu .add (9 : Fin 32) x0 (19 : Fin 32), 2) := by decide
theorem wm_at_54 : fetchRel wideMulCode 0x54 = some (.alu .add a0 x0 (5 : Fin 32), 2) := by decide
theorem wm_at_56 : fetchRel wideMulCode 0x56 = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem wm_at_58 : fetchRel wideMulCode 0x58 = some (.alu .add a3 x0 a6, 2) := by decide
theorem wm_at_5a : fetchRel wideMulCode 0x5A = some (.branch .beq (8 : Fin 32) x0 0x46, 2) := by decide
theorem wm_at_5c : fetchRel wideMulCode 0x5C = some (.load .lw a4 (9 : Fin 32) 0x0, 2) := by decide
theorem wm_at_5e : fetchRel wideMulCode 0x5E = some (.alu .mulhu a2 a4 (7 : Fin 32), 4) := by decide
theorem wm_at_62 : fetchRel wideMulCode 0x62 = some (.alu .mul a4 a4 (7 : Fin 32), 4) := by decide
theorem wm_at_66 : fetchRel wideMulCode 0x66 = some (.branch .bgeu a0 (6 : Fin 32) 0x1A, 4) := by decide
theorem wm_at_6a : fetchRel wideMulCode 0x6A = some (.load .lw a5 a1 0x0, 2) := by decide
theorem wm_at_6c : fetchRel wideMulCode 0x6C = some (.alu .add (28 : Fin 32) (28 : Fin 32) a5, 2) := by decide
theorem wm_at_6e : fetchRel wideMulCode 0x6E = some (.alu .sltu a5 (28 : Fin 32) a5, 4) := by decide
theorem wm_at_72 : fetchRel wideMulCode 0x72 = some (.alu .add a4 a4 (28 : Fin 32), 2) := by decide
theorem wm_at_74 : fetchRel wideMulCode 0x74 = some (.alu .sltu (28 : Fin 32) a4 (28 : Fin 32), 4) := by decide
theorem wm_at_78 : fetchRel wideMulCode 0x78 = some (.alu .add a2 a2 a5, 2) := by decide
theorem wm_at_7a : fetchRel wideMulCode 0x7A = some (.alu .add (28 : Fin 32) (28 : Fin 32) a2, 2) := by decide
theorem wm_at_7c : fetchRel wideMulCode 0x7C = some (.store .sw a1 a4 0x0, 2) := by decide
theorem wm_at_7e : fetchRel wideMulCode 0x7E = some (.jal x0 0x16, 2) := by decide
theorem wm_at_80 : fetchRel wideMulCode 0x80 = some (.load .lw a5 a3 0x0, 2) := by decide
theorem wm_at_82 : fetchRel wideMulCode 0x82 = some (.alu .add (28 : Fin 32) (28 : Fin 32) a5, 2) := by decide
theorem wm_at_84 : fetchRel wideMulCode 0x84 = some (.alu .sltu a5 (28 : Fin 32) a5, 4) := by decide
theorem wm_at_88 : fetchRel wideMulCode 0x88 = some (.alu .add a4 a4 (28 : Fin 32), 2) := by decide
theorem wm_at_8a : fetchRel wideMulCode 0x8A = some (.alu .sltu (28 : Fin 32) a4 (28 : Fin 32), 4) := by decide
theorem wm_at_8e : fetchRel wideMulCode 0x8E = some (.alu .add a2 a2 a5, 2) := by decide
theorem wm_at_90 : fetchRel wideMulCode 0x90 = some (.alu .add (28 : Fin 32) (28 : Fin 32) a2, 2) := by decide
theorem wm_at_92 : fetchRel wideMulCode 0x92 = some (.store .sw a3 a4 0x0, 2) := by decide
theorem wm_at_94 : fetchRel wideMulCode 0x94 = some (.aluImm .add a3 a3 0x4, 2) := by decide
theorem wm_at_96 : fetchRel wideMulCode 0x96 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem wm_at_98 : fetchRel wideMulCode 0x98 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem wm_at_9a : fetchRel wideMulCode 0x9A = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem wm_at_9c : fetchRel wideMulCode 0x9C = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem wm_at_9e : fetchRel wideMulCode 0x9E = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFBE, 2) := by decide
theorem wm_at_a0 : fetchRel wideMulCode 0xA0 = some (.alu .add (17 : Fin 32) (17 : Fin 32) (20 : Fin 32), 2) := by decide
theorem wm_at_a2 : fetchRel wideMulCode 0xA2 = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0x1, 2) := by decide
theorem wm_at_a4 : fetchRel wideMulCode 0xA4 = some (.store .sw (17 : Fin 32) (28 : Fin 32) 0x0, 4) := by decide
theorem wm_at_a8 : fetchRel wideMulCode 0xA8 = some (.aluImm .add a6 a6 0x4, 2) := by decide
theorem wm_at_aa : fetchRel wideMulCode 0xAA = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x4, 2) := by decide
theorem wm_at_ac : fetchRel wideMulCode 0xAC = some (.branch .bne (5 : Fin 32) (6 : Fin 32) 0xFFFFFF96, 4) := by decide
theorem wm_at_b0 : fetchRel wideMulCode 0xB0 = some (.alu .add a1 x0 sp, 2) := by decide
theorem wm_at_b2 : fetchRel wideMulCode 0xB2 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem wm_at_b6 : fetchRel wideMulCode 0xB6 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem wm_at_b8 : fetchRel wideMulCode 0xB8 = some (.auipc ra 0x13000, 4) := by decide
theorem wm_at_bc : fetchRel wideMulCode 0xBC = some (.jalr ra ra 0xFFFFF994, 4) := by decide
theorem wm_at_c0 : fetchRel wideMulCode 0xC0 = some (.aluImm .add a0 (18 : Fin 32) 0x20, 4) := by decide
theorem wm_at_c4 : fetchRel wideMulCode 0xC4 = some (.aluImm .add a1 sp 0x20, 2) := by decide
theorem wm_at_c6 : fetchRel wideMulCode 0xC6 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem wm_at_ca : fetchRel wideMulCode 0xCA = some (.auipc ra 0x13000, 4) := by decide
theorem wm_at_ce : fetchRel wideMulCode 0xCE = some (.jalr ra ra 0xFFFFF982, 4) := by decide
theorem wm_at_d2 : fetchRel wideMulCode 0xD2 = some (.auipc (5 : Fin 32) 0x12000, 4) := by decide
theorem wm_at_d6 : fetchRel wideMulCode 0xD6 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0x348, 4) := by decide
theorem wm_at_da : fetchRel wideMulCode 0xDA = some (.load .lw (22 : Fin 32) sp 0x40, 2) := by decide
theorem wm_at_dc : fetchRel wideMulCode 0xDC = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem wm_at_de : fetchRel wideMulCode 0xDE = some (.jalr x0 ra 0x0, 2) := by decide

theorem fm_at_0 : fetchRel fieldMulCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF30, 2) := by decide
theorem fm_at_2 : fetchRel fieldMulCode 0x2 = some (.store .sw sp ra 0xCC, 2) := by decide
theorem fm_at_4 : fetchRel fieldMulCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xC8, 2) := by decide
theorem fm_at_6 : fetchRel fieldMulCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xC4, 2) := by decide
theorem fm_at_8 : fetchRel fieldMulCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xC0, 2) := by decide
theorem fm_at_a : fetchRel fieldMulCode 0xA = some (.store .sw sp (19 : Fin 32) 0xBC, 2) := by decide
theorem fm_at_c : fetchRel fieldMulCode 0xC = some (.store .sw sp (20 : Fin 32) 0xB8, 2) := by decide
theorem fm_at_e : fetchRel fieldMulCode 0xE = some (.store .sw sp (21 : Fin 32) 0xB4, 2) := by decide
theorem fm_at_10 : fetchRel fieldMulCode 0x10 = some (.store .sw sp (22 : Fin 32) 0xB0, 2) := by decide
theorem fm_at_12 : fetchRel fieldMulCode 0x12 = some (.store .sw sp (23 : Fin 32) 0xAC, 2) := by decide
theorem fm_at_14 : fetchRel fieldMulCode 0x14 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem fm_at_16 : fetchRel fieldMulCode 0x16 = some (.alu .add a0 x0 sp, 2) := by decide
theorem fm_at_18 : fetchRel fieldMulCode 0x18 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem fm_at_1c : fetchRel fieldMulCode 0x1C = some (.jalr ra ra 0xFFFFFECC, 4) := by decide
theorem fm_at_20 : fetchRel fieldMulCode 0x20 = some (.load .lw a4 sp 0x0, 2) := by decide
theorem fm_at_22 : fetchRel fieldMulCode 0x22 = some (.load .lw a0 sp 0xC, 2) := by decide
theorem fm_at_24 : fetchRel fieldMulCode 0x24 = some (.load .lw a2 sp 0x4, 2) := by decide
theorem fm_at_26 : fetchRel fieldMulCode 0x26 = some (.load .lw (22 : Fin 32) sp 0x8, 2) := by decide
theorem fm_at_28 : fetchRel fieldMulCode 0x28 = some (.load .lw a5 sp 0x10, 2) := by decide
theorem fm_at_2a : fetchRel fieldMulCode 0x2A = some (.load .lw (20 : Fin 32) sp 0x14, 2) := by decide
theorem fm_at_2c : fetchRel fieldMulCode 0x2C = some (.load .lw (9 : Fin 32) sp 0x18, 2) := by decide
theorem fm_at_2e : fetchRel fieldMulCode 0x2E = some (.load .lw (30 : Fin 32) sp 0x1C, 2) := by decide
theorem fm_at_30 : fetchRel fieldMulCode 0x30 = some (.alu .add (21 : Fin 32) a0 a4, 4) := by decide
theorem fm_at_34 : fetchRel fieldMulCode 0x34 = some (.alu .sltu a0 (21 : Fin 32) a0, 4) := by decide
theorem fm_at_38 : fetchRel fieldMulCode 0x38 = some (.load .lw (31 : Fin 32) sp 0x20, 2) := by decide
theorem fm_at_3a : fetchRel fieldMulCode 0x3A = some (.load .lw (29 : Fin 32) sp 0x24, 2) := by decide
theorem fm_at_3c : fetchRel fieldMulCode 0x3C = some (.load .lw (28 : Fin 32) sp 0x28, 2) := by decide
theorem fm_at_3e : fetchRel fieldMulCode 0x3E = some (.load .lw (7 : Fin 32) sp 0x2C, 2) := by decide
theorem fm_at_40 : fetchRel fieldMulCode 0x40 = some (.alu .add a5 a5 a0, 2) := by decide
theorem fm_at_42 : fetchRel fieldMulCode 0x42 = some (.alu .sltu a0 a5 a0, 4) := by decide
theorem fm_at_46 : fetchRel fieldMulCode 0x46 = some (.aluImm .add (19 : Fin 32) x0 0xFFFFFFFF, 2) := by decide
theorem fm_at_48 : fetchRel fieldMulCode 0x48 = some (.alu .mulhu (8 : Fin 32) a4 (19 : Fin 32), 4) := by decide
theorem fm_at_4c : fetchRel fieldMulCode 0x4C = some (.load .lw (6 : Fin 32) sp 0x30, 2) := by decide
theorem fm_at_4e : fetchRel fieldMulCode 0x4E = some (.load .lw (5 : Fin 32) sp 0x34, 2) := by decide
theorem fm_at_50 : fetchRel fieldMulCode 0x50 = some (.load .lw (17 : Fin 32) sp 0x38, 2) := by decide
theorem fm_at_52 : fetchRel fieldMulCode 0x52 = some (.load .lw a6 sp 0x3C, 2) := by decide
theorem fm_at_54 : fetchRel fieldMulCode 0x54 = some (.alu .add (20 : Fin 32) (20 : Fin 32) a0, 2) := by decide
theorem fm_at_56 : fetchRel fieldMulCode 0x56 = some (.alu .sltu a0 (20 : Fin 32) a0, 4) := by decide
theorem fm_at_5a : fetchRel fieldMulCode 0x5A = some (.alu .add a1 (9 : Fin 32) a4, 4) := by decide
theorem fm_at_5e : fetchRel fieldMulCode 0x5E = some (.alu .sltu (9 : Fin 32) a1 (9 : Fin 32), 4) := by decide
theorem fm_at_62 : fetchRel fieldMulCode 0x62 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fm_at_64 : fetchRel fieldMulCode 0x64 = some (.alu .sub a3 (30 : Fin 32) a4, 4) := by decide
theorem fm_at_68 : fetchRel fieldMulCode 0x68 = some (.alu .sub a4 x0 a4, 4) := by decide
theorem fm_at_6c : fetchRel fieldMulCode 0x6C = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fm_at_70 : fetchRel fieldMulCode 0x70 = some (.alu .sltu a4 a3 a4, 4) := by decide
theorem fm_at_74 : fetchRel fieldMulCode 0x74 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem fm_at_76 : fetchRel fieldMulCode 0x76 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem fm_at_78 : fetchRel fieldMulCode 0x78 = some (.alu .add (9 : Fin 32) a3 a1, 4) := by decide
theorem fm_at_7c : fetchRel fieldMulCode 0x7C = some (.alu .add (30 : Fin 32) a5 a2, 4) := by decide
theorem fm_at_80 : fetchRel fieldMulCode 0x80 = some (.alu .sltu a3 (9 : Fin 32) a3, 4) := by decide
theorem fm_at_84 : fetchRel fieldMulCode 0x84 = some (.alu .sltu a5 (30 : Fin 32) a5, 4) := by decide
theorem fm_at_88 : fetchRel fieldMulCode 0x88 = some (.alu .add a3 a3 a4, 2) := by decide
theorem fm_at_8a : fetchRel fieldMulCode 0x8A = some (.alu .add a5 a5 (20 : Fin 32), 2) := by decide
theorem fm_at_8c : fetchRel fieldMulCode 0x8C = some (.alu .add (31 : Fin 32) (31 : Fin 32) a3, 2) := by decide
theorem fm_at_8e : fetchRel fieldMulCode 0x8E = some (.alu .sltu a4 a5 (20 : Fin 32), 4) := by decide
theorem fm_at_92 : fetchRel fieldMulCode 0x92 = some (.alu .add a4 a4 a0, 2) := by decide
theorem fm_at_94 : fetchRel fieldMulCode 0x94 = some (.alu .mulhu (8 : Fin 32) a2 (19 : Fin 32), 4) := by decide
theorem fm_at_98 : fetchRel fieldMulCode 0x98 = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem fm_at_9c : fetchRel fieldMulCode 0x9C = some (.alu .add a1 (9 : Fin 32) a2, 4) := by decide
theorem fm_at_a0 : fetchRel fieldMulCode 0xA0 = some (.alu .sltu (20 : Fin 32) (31 : Fin 32) a3, 4) := by decide
theorem fm_at_a4 : fetchRel fieldMulCode 0xA4 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fm_at_a6 : fetchRel fieldMulCode 0xA6 = some (.alu .sltu (9 : Fin 32) a1 (9 : Fin 32), 4) := by decide
theorem fm_at_aa : fetchRel fieldMulCode 0xAA = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fm_at_ae : fetchRel fieldMulCode 0xAE = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem fm_at_b0 : fetchRel fieldMulCode 0xB0 = some (.alu .sub a2 (31 : Fin 32) a2, 4) := by decide
theorem fm_at_b4 : fetchRel fieldMulCode 0xB4 = some (.alu .sltu (9 : Fin 32) a2 (31 : Fin 32), 4) := by decide
theorem fm_at_b8 : fetchRel fieldMulCode 0xB8 = some (.alu .add a3 a2 a1, 4) := by decide
theorem fm_at_bc : fetchRel fieldMulCode 0xBC = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem fm_at_be : fetchRel fieldMulCode 0xBE = some (.alu .sltu a2 a3 a2, 4) := by decide
theorem fm_at_c2 : fetchRel fieldMulCode 0xC2 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a2, 2) := by decide
theorem fm_at_c4 : fetchRel fieldMulCode 0xC4 = some (.alu .add (31 : Fin 32) a5 (22 : Fin 32), 4) := by decide
theorem fm_at_c8 : fetchRel fieldMulCode 0xC8 = some (.alu .add (29 : Fin 32) (29 : Fin 32) (20 : Fin 32), 2) := by decide
theorem fm_at_ca : fetchRel fieldMulCode 0xCA = some (.alu .sltu a5 (31 : Fin 32) a5, 4) := by decide
theorem fm_at_ce : fetchRel fieldMulCode 0xCE = some (.alu .sltu (20 : Fin 32) (29 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fm_at_d2 : fetchRel fieldMulCode 0xD2 = some (.alu .add a5 a5 a4, 2) := by decide
theorem fm_at_d4 : fetchRel fieldMulCode 0xD4 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (29 : Fin 32), 2) := by decide
theorem fm_at_d6 : fetchRel fieldMulCode 0xD6 = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem fm_at_da : fetchRel fieldMulCode 0xDA = some (.alu .add a4 a4 a0, 2) := by decide
theorem fm_at_dc : fetchRel fieldMulCode 0xDC = some (.alu .mulhu (23 : Fin 32) (22 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fm_at_e0 : fetchRel fieldMulCode 0xE0 = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem fm_at_e4 : fetchRel fieldMulCode 0xE4 = some (.alu .add a1 a3 (22 : Fin 32), 4) := by decide
theorem fm_at_e8 : fetchRel fieldMulCode 0xE8 = some (.alu .sltu a2 (8 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fm_at_ec : fetchRel fieldMulCode 0xEC = some (.alu .add a0 a0 a1, 2) := by decide
theorem fm_at_ee : fetchRel fieldMulCode 0xEE = some (.alu .sltu a3 a1 a3, 4) := by decide
theorem fm_at_f2 : fetchRel fieldMulCode 0xF2 = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fm_at_f6 : fetchRel fieldMulCode 0xF6 = some (.alu .add a1 a1 a3, 2) := by decide
theorem fm_at_f8 : fetchRel fieldMulCode 0xF8 = some (.alu .sub a3 (8 : Fin 32) (22 : Fin 32), 4) := by decide
theorem fm_at_fc : fetchRel fieldMulCode 0xFC = some (.alu .sltu (8 : Fin 32) a3 (8 : Fin 32), 4) := by decide
theorem fm_at_100 : fetchRel fieldMulCode 0x100 = some (.alu .add (9 : Fin 32) a3 a1, 4) := by decide
theorem fm_at_104 : fetchRel fieldMulCode 0x104 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (23 : Fin 32), 2) := by decide
theorem fm_at_106 : fetchRel fieldMulCode 0x106 = some (.alu .sltu a3 (9 : Fin 32) a3, 4) := by decide
theorem fm_at_10a : fetchRel fieldMulCode 0x10A = some (.alu .add a2 a2 (20 : Fin 32), 2) := by decide
theorem fm_at_10c : fetchRel fieldMulCode 0x10C = some (.alu .add (8 : Fin 32) (8 : Fin 32) a3, 2) := by decide
theorem fm_at_10e : fetchRel fieldMulCode 0x10E = some (.alu .add (28 : Fin 32) (28 : Fin 32) a2, 2) := by decide
theorem fm_at_110 : fetchRel fieldMulCode 0x110 = some (.alu .add (29 : Fin 32) a5 (21 : Fin 32), 4) := by decide
theorem fm_at_114 : fetchRel fieldMulCode 0x114 = some (.alu .sltu (20 : Fin 32) (28 : Fin 32) a2, 4) := by decide
theorem fm_at_118 : fetchRel fieldMulCode 0x118 = some (.alu .sltu a5 (29 : Fin 32) a5, 4) := by decide
theorem fm_at_11c : fetchRel fieldMulCode 0x11C = some (.alu .add (8 : Fin 32) (8 : Fin 32) (28 : Fin 32), 2) := by decide
theorem fm_at_11e : fetchRel fieldMulCode 0x11E = some (.alu .add a5 a5 a4, 2) := by decide
theorem fm_at_120 : fetchRel fieldMulCode 0x120 = some (.alu .sltu a2 (8 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fm_at_124 : fetchRel fieldMulCode 0x124 = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem fm_at_128 : fetchRel fieldMulCode 0x128 = some (.alu .add a4 a4 a0, 2) := by decide
theorem fm_at_12a : fetchRel fieldMulCode 0x12A = some (.alu .mulhu a3 (21 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fm_at_12e : fetchRel fieldMulCode 0x12E = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem fm_at_132 : fetchRel fieldMulCode 0x132 = some (.alu .add a1 (9 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fm_at_136 : fetchRel fieldMulCode 0x136 = some (.alu .add (20 : Fin 32) (20 : Fin 32) a2, 2) := by decide
theorem fm_at_138 : fetchRel fieldMulCode 0x138 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fm_at_13a : fetchRel fieldMulCode 0x13A = some (.alu .sltu (9 : Fin 32) a1 (9 : Fin 32), 4) := by decide
theorem fm_at_13e : fetchRel fieldMulCode 0x13E = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fm_at_142 : fetchRel fieldMulCode 0x142 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem fm_at_144 : fetchRel fieldMulCode 0x144 = some (.alu .sub (9 : Fin 32) (8 : Fin 32) (21 : Fin 32), 4) := by decide
theorem fm_at_148 : fetchRel fieldMulCode 0x148 = some (.alu .sltu (8 : Fin 32) (9 : Fin 32) (8 : Fin 32), 4) := by decide
theorem fm_at_14c : fetchRel fieldMulCode 0x14C = some (.alu .add a2 (9 : Fin 32) a1, 4) := by decide
theorem fm_at_150 : fetchRel fieldMulCode 0x150 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem fm_at_152 : fetchRel fieldMulCode 0x152 = some (.alu .sltu (9 : Fin 32) a2 (9 : Fin 32), 4) := by decide
theorem fm_at_156 : fetchRel fieldMulCode 0x156 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem fm_at_158 : fetchRel fieldMulCode 0x158 = some (.alu .add (28 : Fin 32) a5 (30 : Fin 32), 4) := by decide
theorem fm_at_15c : fetchRel fieldMulCode 0x15C = some (.alu .add (7 : Fin 32) (7 : Fin 32) (20 : Fin 32), 2) := by decide
theorem fm_at_15e : fetchRel fieldMulCode 0x15E = some (.alu .sltu a5 (28 : Fin 32) a5, 4) := by decide
theorem fm_at_162 : fetchRel fieldMulCode 0x162 = some (.alu .sltu (20 : Fin 32) (7 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fm_at_166 : fetchRel fieldMulCode 0x166 = some (.alu .add a5 a5 a4, 2) := by decide
theorem fm_at_168 : fetchRel fieldMulCode 0x168 = some (.alu .add (9 : Fin 32) (9 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fm_at_16a : fetchRel fieldMulCode 0x16A = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem fm_at_16e : fetchRel fieldMulCode 0x16E = some (.alu .add a4 a4 a0, 2) := by decide
theorem fm_at_170 : fetchRel fieldMulCode 0x170 = some (.alu .mulhu (8 : Fin 32) (30 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fm_at_174 : fetchRel fieldMulCode 0x174 = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem fm_at_178 : fetchRel fieldMulCode 0x178 = some (.alu .add a1 a2 (30 : Fin 32), 4) := by decide
theorem fm_at_17c : fetchRel fieldMulCode 0x17C = some (.alu .sltu (7 : Fin 32) (9 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fm_at_180 : fetchRel fieldMulCode 0x180 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fm_at_182 : fetchRel fieldMulCode 0x182 = some (.alu .sltu a2 a1 a2, 4) := by decide
theorem fm_at_186 : fetchRel fieldMulCode 0x186 = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fm_at_18a : fetchRel fieldMulCode 0x18A = some (.alu .add a1 a1 a2, 2) := by decide
theorem fm_at_18c : fetchRel fieldMulCode 0x18C = some (.alu .sub a2 (9 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fm_at_190 : fetchRel fieldMulCode 0x190 = some (.alu .sltu (9 : Fin 32) a2 (9 : Fin 32), 4) := by decide
theorem fm_at_194 : fetchRel fieldMulCode 0x194 = some (.alu .add a3 a2 a1, 4) := by decide
theorem fm_at_198 : fetchRel fieldMulCode 0x198 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem fm_at_19a : fetchRel fieldMulCode 0x19A = some (.alu .sltu a2 a3 a2, 4) := by decide
theorem fm_at_19e : fetchRel fieldMulCode 0x19E = some (.alu .add (20 : Fin 32) (20 : Fin 32) (7 : Fin 32), 2) := by decide
theorem fm_at_1a0 : fetchRel fieldMulCode 0x1A0 = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem fm_at_1a2 : fetchRel fieldMulCode 0x1A2 = some (.alu .add (6 : Fin 32) (6 : Fin 32) (20 : Fin 32), 2) := by decide
theorem fm_at_1a4 : fetchRel fieldMulCode 0x1A4 = some (.alu .add (7 : Fin 32) a5 (31 : Fin 32), 4) := by decide
theorem fm_at_1a8 : fetchRel fieldMulCode 0x1A8 = some (.alu .sltu (30 : Fin 32) (6 : Fin 32) (20 : Fin 32), 4) := by decide
theorem fm_at_1ac : fetchRel fieldMulCode 0x1AC = some (.alu .sltu a5 (7 : Fin 32) a5, 4) := by decide
theorem fm_at_1b0 : fetchRel fieldMulCode 0x1B0 = some (.alu .add a2 a2 (6 : Fin 32), 2) := by decide
theorem fm_at_1b2 : fetchRel fieldMulCode 0x1B2 = some (.alu .add a5 a5 a4, 2) := by decide
theorem fm_at_1b4 : fetchRel fieldMulCode 0x1B4 = some (.alu .sltu (8 : Fin 32) a2 (6 : Fin 32), 4) := by decide
theorem fm_at_1b8 : fetchRel fieldMulCode 0x1B8 = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem fm_at_1bc : fetchRel fieldMulCode 0x1BC = some (.alu .add a4 a4 a0, 2) := by decide
theorem fm_at_1be : fetchRel fieldMulCode 0x1BE = some (.alu .mulhu (9 : Fin 32) (31 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fm_at_1c2 : fetchRel fieldMulCode 0x1C2 = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem fm_at_1c6 : fetchRel fieldMulCode 0x1C6 = some (.alu .add a1 a3 (31 : Fin 32), 4) := by decide
theorem fm_at_1ca : fetchRel fieldMulCode 0x1CA = some (.alu .add (30 : Fin 32) (30 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fm_at_1cc : fetchRel fieldMulCode 0x1CC = some (.alu .add a0 a0 a1, 2) := by decide
theorem fm_at_1ce : fetchRel fieldMulCode 0x1CE = some (.alu .sltu a3 a1 a3, 4) := by decide
theorem fm_at_1d2 : fetchRel fieldMulCode 0x1D2 = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fm_at_1d6 : fetchRel fieldMulCode 0x1D6 = some (.alu .add a1 a1 a3, 2) := by decide
theorem fm_at_1d8 : fetchRel fieldMulCode 0x1D8 = some (.alu .sub a3 a2 (31 : Fin 32), 4) := by decide
theorem fm_at_1dc : fetchRel fieldMulCode 0x1DC = some (.alu .sltu a2 a3 a2, 4) := by decide
theorem fm_at_1e0 : fetchRel fieldMulCode 0x1E0 = some (.alu .add (8 : Fin 32) a3 a1, 4) := by decide
theorem fm_at_1e4 : fetchRel fieldMulCode 0x1E4 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem fm_at_1e6 : fetchRel fieldMulCode 0x1E6 = some (.alu .sltu a3 (8 : Fin 32) a3, 4) := by decide
theorem fm_at_1ea : fetchRel fieldMulCode 0x1EA = some (.alu .add a3 a3 a2, 2) := by decide
theorem fm_at_1ec : fetchRel fieldMulCode 0x1EC = some (.alu .add (6 : Fin 32) a5 (29 : Fin 32), 4) := by decide
theorem fm_at_1f0 : fetchRel fieldMulCode 0x1F0 = some (.alu .add (5 : Fin 32) (5 : Fin 32) (30 : Fin 32), 2) := by decide
theorem fm_at_1f2 : fetchRel fieldMulCode 0x1F2 = some (.alu .sltu a5 (6 : Fin 32) a5, 4) := by decide
theorem fm_at_1f6 : fetchRel fieldMulCode 0x1F6 = some (.alu .sltu (30 : Fin 32) (5 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fm_at_1fa : fetchRel fieldMulCode 0x1FA = some (.alu .add a5 a5 a4, 2) := by decide
theorem fm_at_1fc : fetchRel fieldMulCode 0x1FC = some (.alu .add a3 a3 (5 : Fin 32), 2) := by decide
theorem fm_at_1fe : fetchRel fieldMulCode 0x1FE = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem fm_at_202 : fetchRel fieldMulCode 0x202 = some (.alu .add a4 a4 a0, 2) := by decide
theorem fm_at_204 : fetchRel fieldMulCode 0x204 = some (.alu .mulhu a2 (29 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fm_at_208 : fetchRel fieldMulCode 0x208 = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem fm_at_20c : fetchRel fieldMulCode 0x20C = some (.alu .add a1 (8 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fm_at_210 : fetchRel fieldMulCode 0x210 = some (.alu .sltu (5 : Fin 32) a3 (5 : Fin 32), 4) := by decide
theorem fm_at_214 : fetchRel fieldMulCode 0x214 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fm_at_216 : fetchRel fieldMulCode 0x216 = some (.alu .sltu (8 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem fm_at_21a : fetchRel fieldMulCode 0x21A = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fm_at_21e : fetchRel fieldMulCode 0x21E = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem fm_at_220 : fetchRel fieldMulCode 0x220 = some (.alu .sub (8 : Fin 32) a3 (29 : Fin 32), 4) := by decide
theorem fm_at_224 : fetchRel fieldMulCode 0x224 = some (.alu .sltu a3 (8 : Fin 32) a3, 4) := by decide
theorem fm_at_228 : fetchRel fieldMulCode 0x228 = some (.alu .add (9 : Fin 32) (8 : Fin 32) a1, 4) := by decide
theorem fm_at_22c : fetchRel fieldMulCode 0x22C = some (.alu .add a2 a2 a3, 2) := by decide
theorem fm_at_22e : fetchRel fieldMulCode 0x22E = some (.alu .sltu a3 (9 : Fin 32) (8 : Fin 32), 4) := by decide
theorem fm_at_232 : fetchRel fieldMulCode 0x232 = some (.alu .add (30 : Fin 32) (30 : Fin 32) (5 : Fin 32), 2) := by decide
theorem fm_at_234 : fetchRel fieldMulCode 0x234 = some (.alu .add a2 a2 a3, 2) := by decide
theorem fm_at_236 : fetchRel fieldMulCode 0x236 = some (.alu .add (17 : Fin 32) (17 : Fin 32) (30 : Fin 32), 2) := by decide
theorem fm_at_238 : fetchRel fieldMulCode 0x238 = some (.alu .add (5 : Fin 32) a5 (28 : Fin 32), 4) := by decide
theorem fm_at_23c : fetchRel fieldMulCode 0x23C = some (.alu .sltu (29 : Fin 32) (17 : Fin 32) (30 : Fin 32), 4) := by decide
theorem fm_at_240 : fetchRel fieldMulCode 0x240 = some (.alu .sltu a5 (5 : Fin 32) a5, 4) := by decide
theorem fm_at_244 : fetchRel fieldMulCode 0x244 = some (.alu .add a2 a2 (17 : Fin 32), 2) := by decide
theorem fm_at_246 : fetchRel fieldMulCode 0x246 = some (.alu .add a5 a5 a4, 2) := by decide
theorem fm_at_248 : fetchRel fieldMulCode 0x248 = some (.alu .sltu (8 : Fin 32) a2 (17 : Fin 32), 4) := by decide
theorem fm_at_24c : fetchRel fieldMulCode 0x24C = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem fm_at_250 : fetchRel fieldMulCode 0x250 = some (.alu .add a4 a4 a0, 2) := by decide
theorem fm_at_252 : fetchRel fieldMulCode 0x252 = some (.alu .mulhu a3 (28 : Fin 32) (19 : Fin 32), 4) := by decide
theorem fm_at_256 : fetchRel fieldMulCode 0x256 = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem fm_at_25a : fetchRel fieldMulCode 0x25A = some (.alu .add a1 (9 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fm_at_25e : fetchRel fieldMulCode 0x25E = some (.alu .add (29 : Fin 32) (29 : Fin 32) (8 : Fin 32), 2) := by decide
theorem fm_at_260 : fetchRel fieldMulCode 0x260 = some (.alu .add a0 a0 a1, 2) := by decide
theorem fm_at_262 : fetchRel fieldMulCode 0x262 = some (.alu .sltu (9 : Fin 32) a1 (9 : Fin 32), 4) := by decide
theorem fm_at_266 : fetchRel fieldMulCode 0x266 = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem fm_at_26a : fetchRel fieldMulCode 0x26A = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem fm_at_26c : fetchRel fieldMulCode 0x26C = some (.alu .sub (9 : Fin 32) a2 (28 : Fin 32), 4) := by decide
theorem fm_at_270 : fetchRel fieldMulCode 0x270 = some (.alu .sltu a2 (9 : Fin 32) a2, 4) := by decide
theorem fm_at_274 : fetchRel fieldMulCode 0x274 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem fm_at_276 : fetchRel fieldMulCode 0x276 = some (.alu .add a2 a2 a3, 2) := by decide
theorem fm_at_278 : fetchRel fieldMulCode 0x278 = some (.alu .sltu a3 a1 (9 : Fin 32), 4) := by decide
theorem fm_at_27c : fetchRel fieldMulCode 0x27C = some (.alu .add a2 a2 a3, 2) := by decide
theorem fm_at_27e : fetchRel fieldMulCode 0x27E = some (.alu .add a6 a6 (29 : Fin 32), 2) := by decide
theorem fm_at_280 : fetchRel fieldMulCode 0x280 = some (.alu .add a2 a2 a6, 2) := by decide
theorem fm_at_282 : fetchRel fieldMulCode 0x282 = some (.alu .sltu a3 a6 (29 : Fin 32), 4) := by decide
theorem fm_at_286 : fetchRel fieldMulCode 0x286 = some (.alu .sltu (9 : Fin 32) a2 a6, 4) := by decide
theorem fm_at_28a : fetchRel fieldMulCode 0x28A = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem fm_at_28c : fetchRel fieldMulCode 0x28C = some (.store .sw sp (7 : Fin 32) 0x64, 2) := by decide
theorem fm_at_28e : fetchRel fieldMulCode 0x28E = some (.store .sw sp (6 : Fin 32) 0x68, 2) := by decide
theorem fm_at_290 : fetchRel fieldMulCode 0x290 = some (.store .sw sp (5 : Fin 32) 0x6C, 2) := by decide
theorem fm_at_292 : fetchRel fieldMulCode 0x292 = some (.store .sw sp a5 0x70, 2) := by decide
theorem fm_at_294 : fetchRel fieldMulCode 0x294 = some (.store .sw sp a4 0x74, 2) := by decide
theorem fm_at_296 : fetchRel fieldMulCode 0x296 = some (.store .sw sp a0 0x78, 2) := by decide
theorem fm_at_298 : fetchRel fieldMulCode 0x298 = some (.store .sw sp a1 0x7C, 2) := by decide
theorem fm_at_29a : fetchRel fieldMulCode 0x29A = some (.store .sw sp a2 0x80, 2) := by decide
theorem fm_at_29c : fetchRel fieldMulCode 0x29C = some (.store .sw sp a3 0x84, 2) := by decide
theorem fm_at_29e : fetchRel fieldMulCode 0x29E = some (.store .sw sp (19 : Fin 32) 0x88, 2) := by decide
theorem fm_at_2a0 : fetchRel fieldMulCode 0x2A0 = some (.store .sw sp (19 : Fin 32) 0x8C, 2) := by decide
theorem fm_at_2a2 : fetchRel fieldMulCode 0x2A2 = some (.store .sw sp (19 : Fin 32) 0x90, 2) := by decide
theorem fm_at_2a4 : fetchRel fieldMulCode 0x2A4 = some (.store .sw sp x0 0x94, 2) := by decide
theorem fm_at_2a6 : fetchRel fieldMulCode 0x2A6 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem fm_at_2a8 : fetchRel fieldMulCode 0x2A8 = some (.store .sw sp x0 0x98, 2) := by decide
theorem fm_at_2aa : fetchRel fieldMulCode 0x2AA = some (.store .sw sp x0 0x9C, 2) := by decide
theorem fm_at_2ac : fetchRel fieldMulCode 0x2AC = some (.store .sw sp a0 0xA0, 2) := by decide
theorem fm_at_2ae : fetchRel fieldMulCode 0x2AE = some (.store .sw sp (19 : Fin 32) 0xA4, 2) := by decide
theorem fm_at_2b0 : fetchRel fieldMulCode 0x2B0 = some (.store .sw sp x0 0xA8, 2) := by decide
theorem fm_at_2b2 : fetchRel fieldMulCode 0x2B2 = some (.aluImm .add a0 sp 0x40, 2) := by decide
theorem fm_at_2b4 : fetchRel fieldMulCode 0x2B4 = some (.aluImm .add a1 sp 0x64, 2) := by decide
theorem fm_at_2b6 : fetchRel fieldMulCode 0x2B6 = some (.aluImm .add a2 sp 0x88, 2) := by decide
theorem fm_at_2b8 : fetchRel fieldMulCode 0x2B8 = some (.auipc ra 0x0, 4) := by decide
theorem fm_at_2bc : fetchRel fieldMulCode 0x2BC = some (.jalr ra ra 0x144, 4) := by decide
theorem fm_at_2c0 : fetchRel fieldMulCode 0x2C0 = some (.load .lw a0 sp 0x40, 2) := by decide
theorem fm_at_2c2 : fetchRel fieldMulCode 0x2C2 = some (.load .lw a1 sp 0x44, 2) := by decide
theorem fm_at_2c4 : fetchRel fieldMulCode 0x2C4 = some (.load .lw a2 sp 0x48, 2) := by decide
theorem fm_at_2c6 : fetchRel fieldMulCode 0x2C6 = some (.load .lw a3 sp 0x4C, 2) := by decide
theorem fm_at_2c8 : fetchRel fieldMulCode 0x2C8 = some (.load .lw a4 sp 0x50, 2) := by decide
theorem fm_at_2ca : fetchRel fieldMulCode 0x2CA = some (.load .lw a5 sp 0x54, 2) := by decide
theorem fm_at_2cc : fetchRel fieldMulCode 0x2CC = some (.load .lw (9 : Fin 32) sp 0x58, 2) := by decide
theorem fm_at_2ce : fetchRel fieldMulCode 0x2CE = some (.load .lw (8 : Fin 32) sp 0x5C, 2) := by decide
theorem fm_at_2d0 : fetchRel fieldMulCode 0x2D0 = some (.store .sw (18 : Fin 32) a0 0x0, 4) := by decide
theorem fm_at_2d4 : fetchRel fieldMulCode 0x2D4 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem fm_at_2d6 : fetchRel fieldMulCode 0x2D6 = some (.store .sw a0 a1 0x4, 2) := by decide
theorem fm_at_2d8 : fetchRel fieldMulCode 0x2D8 = some (.store .sw a0 a2 0x8, 2) := by decide
theorem fm_at_2da : fetchRel fieldMulCode 0x2DA = some (.store .sw a0 a3 0xC, 2) := by decide
theorem fm_at_2dc : fetchRel fieldMulCode 0x2DC = some (.store .sw a0 a4 0x10, 2) := by decide
theorem fm_at_2de : fetchRel fieldMulCode 0x2DE = some (.store .sw a0 a5 0x14, 2) := by decide
theorem fm_at_2e0 : fetchRel fieldMulCode 0x2E0 = some (.store .sw a0 (9 : Fin 32) 0x18, 2) := by decide
theorem fm_at_2e2 : fetchRel fieldMulCode 0x2E2 = some (.store .sw a0 (8 : Fin 32) 0x1C, 2) := by decide
theorem fm_at_2e4 : fetchRel fieldMulCode 0x2E4 = some (.load .lw ra sp 0xCC, 2) := by decide
theorem fm_at_2e6 : fetchRel fieldMulCode 0x2E6 = some (.load .lw (8 : Fin 32) sp 0xC8, 2) := by decide
theorem fm_at_2e8 : fetchRel fieldMulCode 0x2E8 = some (.load .lw (9 : Fin 32) sp 0xC4, 2) := by decide
theorem fm_at_2ea : fetchRel fieldMulCode 0x2EA = some (.load .lw (18 : Fin 32) sp 0xC0, 2) := by decide
theorem fm_at_2ec : fetchRel fieldMulCode 0x2EC = some (.load .lw (19 : Fin 32) sp 0xBC, 2) := by decide
theorem fm_at_2ee : fetchRel fieldMulCode 0x2EE = some (.load .lw (20 : Fin 32) sp 0xB8, 2) := by decide
theorem fm_at_2f0 : fetchRel fieldMulCode 0x2F0 = some (.load .lw (21 : Fin 32) sp 0xB4, 2) := by decide
theorem fm_at_2f2 : fetchRel fieldMulCode 0x2F2 = some (.load .lw (22 : Fin 32) sp 0xB0, 2) := by decide
theorem fm_at_2f4 : fetchRel fieldMulCode 0x2F4 = some (.load .lw (23 : Fin 32) sp 0xAC, 2) := by decide
theorem fm_at_2f6 : fetchRel fieldMulCode 0x2F6 = some (.aluImm .add sp sp 0xD0, 2) := by decide
theorem fm_at_2f8 : fetchRel fieldMulCode 0x2F8 = some (.jalr x0 ra 0x0, 2) := by decide

end C3.RV32
