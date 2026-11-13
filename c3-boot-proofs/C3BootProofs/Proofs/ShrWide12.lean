import C3BootProofs.Proofs.CondNeg12

/-!
# `safegcd`'s `shr_in_place_wide::<12, 2>`, as compiled

Bernstein-Yang inversion keeps a 448-bit value as a 12-limb `lo` and a 2-limb
`hi`, and this function shifts it right by `shift` bits, for `shift` from 1
to 63. The compiled code builds the bits of `hi` that move into `lo` in a
two-word buffer (`hi << (64 - shift)`), shifts `hi` right through
`UintRef::leading_mut` and `trailing` into the same buffer and stores it,
shifts `lo` right into a zeroed 12-word buffer the same way, copies that
into `lo` through a second buffer with two `memcpy` calls, and ORs the
moved bits into `lo`'s top words.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem sh_at_0 : fetchRel shr12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF70, 2) := by decide
theorem sh_at_2 : fetchRel shr12Code 0x2 = some (.store .sw sp ra 0x8C, 2) := by decide
theorem sh_at_4 : fetchRel shr12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x88, 2) := by decide
theorem sh_at_6 : fetchRel shr12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x84, 2) := by decide
theorem sh_at_8 : fetchRel shr12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x80, 2) := by decide
theorem sh_at_a : fetchRel shr12Code 0xA = some (.store .sw sp (19 : Fin 32) 0x7C, 2) := by decide
theorem sh_at_c : fetchRel shr12Code 0xC = some (.store .sw sp (20 : Fin 32) 0x78, 2) := by decide
theorem sh_at_e : fetchRel shr12Code 0xE = some (.store .sw sp (21 : Fin 32) 0x74, 2) := by decide
theorem sh_at_10 : fetchRel shr12Code 0x10 = some (.store .sw sp (22 : Fin 32) 0x70, 2) := by decide
theorem sh_at_12 : fetchRel shr12Code 0x12 = some (.store .sw sp (23 : Fin 32) 0x6C, 2) := by decide
theorem sh_at_14 : fetchRel shr12Code 0x14 = some (.alu .add (21 : Fin 32) x0 a2, 2) := by decide
theorem sh_at_16 : fetchRel shr12Code 0x16 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem sh_at_18 : fetchRel shr12Code 0x18 = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem sh_at_1c : fetchRel shr12Code 0x1C = some (.alu .sub a1 a2 (21 : Fin 32), 4) := by decide
theorem sh_at_20 : fetchRel shr12Code 0x20 = some (.branch .bgeu a1 a2 0x1BA, 4) := by decide
theorem sh_at_24 : fetchRel shr12Code 0x24 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem sh_at_26 : fetchRel shr12Code 0x26 = some (.store .sw sp x0 0x38, 2) := by decide
theorem sh_at_28 : fetchRel shr12Code 0x28 = some (.store .sw sp x0 0x3C, 2) := by decide
theorem sh_at_2a : fetchRel shr12Code 0x2A = some (.aluImm .srl a2 a1 0x5, 4) := by decide
theorem sh_at_2e : fetchRel shr12Code 0x2E = some (.aluImm .sll a0 a2 0x2, 4) := by decide
theorem sh_at_32 : fetchRel shr12Code 0x32 = some (.aluImm .add a3 sp 0x38, 2) := by decide
theorem sh_at_34 : fetchRel shr12Code 0x34 = some (.alu .add a0 a0 a3, 2) := by decide
theorem sh_at_36 : fetchRel shr12Code 0x36 = some (.aluImm .add a3 a2 0xFFFFFFFE, 4) := by decide
theorem sh_at_3a : fetchRel shr12Code 0x3A = some (.alu .add a4 x0 a0, 2) := by decide
theorem sh_at_3c : fetchRel shr12Code 0x3C = some (.alu .add a5 x0 (19 : Fin 32), 2) := by decide
theorem sh_at_3e : fetchRel shr12Code 0x3E = some (.branch .beq a3 x0 0xE, 2) := by decide
theorem sh_at_40 : fetchRel shr12Code 0x40 = some (.load .lw (9 : Fin 32) a5 0x0, 2) := by decide
theorem sh_at_42 : fetchRel shr12Code 0x42 = some (.aluImm .add a5 a5 0x4, 2) := by decide
theorem sh_at_44 : fetchRel shr12Code 0x44 = some (.store .sw a4 (9 : Fin 32) 0x0, 2) := by decide
theorem sh_at_46 : fetchRel shr12Code 0x46 = some (.aluImm .add a4 a4 0x4, 2) := by decide
theorem sh_at_48 : fetchRel shr12Code 0x48 = some (.aluImm .add a3 a3 0x1, 2) := by decide
theorem sh_at_4a : fetchRel shr12Code 0x4A = some (.branch .bne a3 x0 0xFFFFFFF6, 2) := by decide
theorem sh_at_4c : fetchRel shr12Code 0x4C = some (.aluImm .and a1 a1 0x1F, 2) := by decide
theorem sh_at_4e : fetchRel shr12Code 0x4E = some (.branch .beq a1 x0 0x22, 2) := by decide
theorem sh_at_50 : fetchRel shr12Code 0x50 = some (.aluImm .add a3 x0 0x0, 2) := by decide
theorem sh_at_52 : fetchRel shr12Code 0x52 = some (.aluImm .add a4 x0 0x20, 4) := by decide
theorem sh_at_56 : fetchRel shr12Code 0x56 = some (.alu .sub a4 a4 a1, 2) := by decide
theorem sh_at_58 : fetchRel shr12Code 0x58 = some (.aluImm .add a2 a2 0xFFFFFFFE, 2) := by decide
theorem sh_at_5a : fetchRel shr12Code 0x5A = some (.branch .beq a2 x0 0x16, 2) := by decide
theorem sh_at_5c : fetchRel shr12Code 0x5C = some (.load .lw a5 a0 0x0, 2) := by decide
theorem sh_at_5e : fetchRel shr12Code 0x5E = some (.alu .sll (9 : Fin 32) a5 a1, 4) := by decide
theorem sh_at_62 : fetchRel shr12Code 0x62 = some (.alu .or (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem sh_at_64 : fetchRel shr12Code 0x64 = some (.alu .srl a3 a5 a4, 4) := by decide
theorem sh_at_68 : fetchRel shr12Code 0x68 = some (.store .sw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem sh_at_6a : fetchRel shr12Code 0x6A = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem sh_at_6c : fetchRel shr12Code 0x6C = some (.aluImm .add a2 a2 0x1, 2) := by decide
theorem sh_at_6e : fetchRel shr12Code 0x6E = some (.branch .bne a2 x0 0xFFFFFFEE, 2) := by decide
theorem sh_at_70 : fetchRel shr12Code 0x70 = some (.load .lw a0 sp 0x38, 2) := by decide
theorem sh_at_72 : fetchRel shr12Code 0x72 = some (.load .lw (22 : Fin 32) sp 0x3C, 2) := by decide
theorem sh_at_74 : fetchRel shr12Code 0x74 = some (.aluImm .add a1 x0 0x3F, 4) := by decide
theorem sh_at_78 : fetchRel shr12Code 0x78 = some (.store .sw sp a0 0x0, 2) := by decide
theorem sh_at_7a : fetchRel shr12Code 0x7A = some (.store .sw sp (22 : Fin 32) 0x4, 2) := by decide
theorem sh_at_7c : fetchRel shr12Code 0x7C = some (.branch .bltu a1 (21 : Fin 32) 0x15E, 4) := by decide
theorem sh_at_80 : fetchRel shr12Code 0x80 = some (.aluImm .srl (20 : Fin 32) (21 : Fin 32) 0x5, 4) := by decide
theorem sh_at_84 : fetchRel shr12Code 0x84 = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem sh_at_86 : fetchRel shr12Code 0x86 = some (.store .sw sp x0 0x38, 2) := by decide
theorem sh_at_88 : fetchRel shr12Code 0x88 = some (.store .sw sp x0 0x3C, 2) := by decide
theorem sh_at_8a : fetchRel shr12Code 0x8A = some (.alu .sub a2 a0 (20 : Fin 32), 4) := by decide
theorem sh_at_8e : fetchRel shr12Code 0x8E = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem sh_at_90 : fetchRel shr12Code 0x90 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem sh_at_92 : fetchRel shr12Code 0x92 = some (.auipc ra 0x0, 4) := by decide
theorem sh_at_96 : fetchRel shr12Code 0x96 = some (.jalr ra ra 0x15C, 4) := by decide
theorem sh_at_9a : fetchRel shr12Code 0x9A = some (.alu .add (23 : Fin 32) x0 a0, 2) := by decide
theorem sh_at_9c : fetchRel shr12Code 0x9C = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem sh_at_9e : fetchRel shr12Code 0x9E = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem sh_at_a0 : fetchRel shr12Code 0xA0 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem sh_at_a2 : fetchRel shr12Code 0xA2 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem sh_at_a4 : fetchRel shr12Code 0xA4 = some (.auipc ra 0x0, 4) := by decide
theorem sh_at_a8 : fetchRel shr12Code 0xA8 = some (.jalr ra ra 0x15A, 4) := by decide
theorem sh_at_ac : fetchRel shr12Code 0xAC = some (.branch .bne (8 : Fin 32) a1 0x126, 4) := by decide
theorem sh_at_b0 : fetchRel shr12Code 0xB0 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem sh_at_b2 : fetchRel shr12Code 0xB2 = some (.alu .add a2 x0 (23 : Fin 32), 2) := by decide
theorem sh_at_b4 : fetchRel shr12Code 0xB4 = some (.branch .beq (8 : Fin 32) x0 0xE, 2) := by decide
theorem sh_at_b6 : fetchRel shr12Code 0xB6 = some (.load .lw a3 a0 0x0, 2) := by decide
theorem sh_at_b8 : fetchRel shr12Code 0xB8 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem sh_at_ba : fetchRel shr12Code 0xBA = some (.store .sw a2 a3 0x0, 2) := by decide
theorem sh_at_bc : fetchRel shr12Code 0xBC = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem sh_at_be : fetchRel shr12Code 0xBE = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem sh_at_c0 : fetchRel shr12Code 0xC0 = some (.branch .bne a1 x0 0xFFFFFFF6, 2) := by decide
theorem sh_at_c2 : fetchRel shr12Code 0xC2 = some (.aluImm .and (9 : Fin 32) (21 : Fin 32) 0x1F, 4) := by decide
theorem sh_at_c6 : fetchRel shr12Code 0xC6 = some (.branch .beq (9 : Fin 32) x0 0x28, 2) := by decide
theorem sh_at_c8 : fetchRel shr12Code 0xC8 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem sh_at_ca : fetchRel shr12Code 0xCA = some (.aluImm .sll a1 (8 : Fin 32) 0x2, 4) := by decide
theorem sh_at_ce : fetchRel shr12Code 0xCE = some (.alu .add a2 a1 (23 : Fin 32), 4) := by decide
theorem sh_at_d2 : fetchRel shr12Code 0xD2 = some (.aluImm .add a1 x0 0x20, 4) := by decide
theorem sh_at_d6 : fetchRel shr12Code 0xD6 = some (.alu .sub a1 a1 (9 : Fin 32), 2) := by decide
theorem sh_at_d8 : fetchRel shr12Code 0xD8 = some (.aluImm .add a2 a2 0xFFFFFFFC, 2) := by decide
theorem sh_at_da : fetchRel shr12Code 0xDA = some (.branch .beq (8 : Fin 32) x0 0x14, 2) := by decide
theorem sh_at_dc : fetchRel shr12Code 0xDC = some (.load .lw a3 a2 0x0, 2) := by decide
theorem sh_at_de : fetchRel shr12Code 0xDE = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem sh_at_e0 : fetchRel shr12Code 0xE0 = some (.alu .srl a4 a3 (9 : Fin 32), 4) := by decide
theorem sh_at_e4 : fetchRel shr12Code 0xE4 = some (.alu .or a4 a4 a0, 2) := by decide
theorem sh_at_e6 : fetchRel shr12Code 0xE6 = some (.alu .sll a0 a3 a1, 4) := by decide
theorem sh_at_ea : fetchRel shr12Code 0xEA = some (.store .sw a2 a4 0x0, 2) := by decide
theorem sh_at_ec : fetchRel shr12Code 0xEC = some (.jal x0 0xFFFFFFEC, 2) := by decide
theorem sh_at_ee : fetchRel shr12Code 0xEE = some (.load .lw a0 sp 0x38, 2) := by decide
theorem sh_at_f0 : fetchRel shr12Code 0xF0 = some (.load .lw a1 sp 0x3C, 2) := by decide
theorem sh_at_f2 : fetchRel shr12Code 0xF2 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem sh_at_f4 : fetchRel shr12Code 0xF4 = some (.store .sw a2 a0 0x0, 2) := by decide
theorem sh_at_f6 : fetchRel shr12Code 0xF6 = some (.store .sw a2 a1 0x4, 2) := by decide
theorem sh_at_f8 : fetchRel shr12Code 0xF8 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem sh_at_fa : fetchRel shr12Code 0xFA = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem sh_at_fe : fetchRel shr12Code 0xFE = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem sh_at_100 : fetchRel shr12Code 0x100 = some (.auipc ra 0x1000, 4) := by decide
theorem sh_at_104 : fetchRel shr12Code 0x104 = some (.jalr ra ra 0x624, 4) := by decide
theorem sh_at_108 : fetchRel shr12Code 0x108 = some (.aluImm .add a0 x0 0xC, 2) := by decide
theorem sh_at_10a : fetchRel shr12Code 0x10A = some (.alu .sub a2 a0 (20 : Fin 32), 4) := by decide
theorem sh_at_10e : fetchRel shr12Code 0x10E = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem sh_at_110 : fetchRel shr12Code 0x110 = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem sh_at_112 : fetchRel shr12Code 0x112 = some (.auipc ra 0x0, 4) := by decide
theorem sh_at_116 : fetchRel shr12Code 0x116 = some (.jalr ra ra 0xDC, 4) := by decide
theorem sh_at_11a : fetchRel shr12Code 0x11A = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem sh_at_11c : fetchRel shr12Code 0x11C = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem sh_at_11e : fetchRel shr12Code 0x11E = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem sh_at_120 : fetchRel shr12Code 0x120 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem sh_at_122 : fetchRel shr12Code 0x122 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem sh_at_124 : fetchRel shr12Code 0x124 = some (.auipc ra 0x0, 4) := by decide
theorem sh_at_128 : fetchRel shr12Code 0x128 = some (.jalr ra ra 0xDA, 4) := by decide
theorem sh_at_12c : fetchRel shr12Code 0x12C = some (.branch .bne (8 : Fin 32) a1 0xA6, 4) := by decide
theorem sh_at_130 : fetchRel shr12Code 0x130 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem sh_at_132 : fetchRel shr12Code 0x132 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem sh_at_134 : fetchRel shr12Code 0x134 = some (.branch .beq (8 : Fin 32) x0 0xE, 2) := by decide
theorem sh_at_136 : fetchRel shr12Code 0x136 = some (.load .lw a3 a0 0x0, 2) := by decide
theorem sh_at_138 : fetchRel shr12Code 0x138 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem sh_at_13a : fetchRel shr12Code 0x13A = some (.store .sw a2 a3 0x0, 2) := by decide
theorem sh_at_13c : fetchRel shr12Code 0x13C = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem sh_at_13e : fetchRel shr12Code 0x13E = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem sh_at_140 : fetchRel shr12Code 0x140 = some (.branch .bne a1 x0 0xFFFFFFF6, 2) := by decide
theorem sh_at_142 : fetchRel shr12Code 0x142 = some (.branch .beq (9 : Fin 32) x0 0x28, 2) := by decide
theorem sh_at_144 : fetchRel shr12Code 0x144 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem sh_at_146 : fetchRel shr12Code 0x146 = some (.aluImm .sll a1 (8 : Fin 32) 0x2, 4) := by decide
theorem sh_at_14a : fetchRel shr12Code 0x14A = some (.alu .add a2 a1 (19 : Fin 32), 4) := by decide
theorem sh_at_14e : fetchRel shr12Code 0x14E = some (.aluImm .add a1 x0 0x20, 4) := by decide
theorem sh_at_152 : fetchRel shr12Code 0x152 = some (.alu .sub a1 a1 (9 : Fin 32), 2) := by decide
theorem sh_at_154 : fetchRel shr12Code 0x154 = some (.aluImm .add a2 a2 0xFFFFFFFC, 2) := by decide
theorem sh_at_156 : fetchRel shr12Code 0x156 = some (.branch .beq (8 : Fin 32) x0 0x14, 2) := by decide
theorem sh_at_158 : fetchRel shr12Code 0x158 = some (.load .lw a3 a2 0x0, 2) := by decide
theorem sh_at_15a : fetchRel shr12Code 0x15A = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem sh_at_15c : fetchRel shr12Code 0x15C = some (.alu .srl a4 a3 (9 : Fin 32), 4) := by decide
theorem sh_at_160 : fetchRel shr12Code 0x160 = some (.alu .or a4 a4 a0, 2) := by decide
theorem sh_at_162 : fetchRel shr12Code 0x162 = some (.alu .sll a0 a3 a1, 4) := by decide
theorem sh_at_166 : fetchRel shr12Code 0x166 = some (.store .sw a2 a4 0x0, 2) := by decide
theorem sh_at_168 : fetchRel shr12Code 0x168 = some (.jal x0 0xFFFFFFEC, 2) := by decide
theorem sh_at_16a : fetchRel shr12Code 0x16A = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem sh_at_16c : fetchRel shr12Code 0x16C = some (.aluImm .add a1 sp 0x38, 2) := by decide
theorem sh_at_16e : fetchRel shr12Code 0x16E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem sh_at_172 : fetchRel shr12Code 0x172 = some (.auipc ra 0x1000, 4) := by decide
theorem sh_at_176 : fetchRel shr12Code 0x176 = some (.jalr ra ra 0x61A, 4) := by decide
theorem sh_at_17a : fetchRel shr12Code 0x17A = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem sh_at_17c : fetchRel shr12Code 0x17C = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem sh_at_180 : fetchRel shr12Code 0x180 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem sh_at_182 : fetchRel shr12Code 0x182 = some (.auipc ra 0x1000, 4) := by decide
theorem sh_at_186 : fetchRel shr12Code 0x186 = some (.jalr ra ra 0x60A, 4) := by decide
theorem sh_at_18a : fetchRel shr12Code 0x18A = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1F, 2) := by decide
theorem sh_at_18c : fetchRel shr12Code 0x18C = some (.aluImm .srl (9 : Fin 32) (9 : Fin 32) 0x5, 2) := by decide
theorem sh_at_18e : fetchRel shr12Code 0x18E = some (.alu .add (20 : Fin 32) (20 : Fin 32) (9 : Fin 32), 2) := by decide
theorem sh_at_190 : fetchRel shr12Code 0x190 = some (.aluImm .add a0 x0 0xC, 2) := by decide
theorem sh_at_192 : fetchRel shr12Code 0x192 = some (.alu .sub a0 a0 (20 : Fin 32), 4) := by decide
theorem sh_at_196 : fetchRel shr12Code 0x196 = some (.branch .beq (20 : Fin 32) x0 0x4E, 4) := by decide
theorem sh_at_19a : fetchRel shr12Code 0x19A = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem sh_at_19c : fetchRel shr12Code 0x19C = some (.alu .sub a1 a1 (20 : Fin 32), 4) := by decide
theorem sh_at_1a0 : fetchRel shr12Code 0x1A0 = some (.aluImm .sll a0 a0 0x2, 2) := by decide
theorem sh_at_1a2 : fetchRel shr12Code 0x1A2 = some (.aluImm .sll a1 a1 0x2, 2) := by decide
theorem sh_at_1a4 : fetchRel shr12Code 0x1A4 = some (.alu .add a2 x0 sp, 2) := by decide
theorem sh_at_1a6 : fetchRel shr12Code 0x1A6 = some (.alu .add a0 a0 (18 : Fin 32), 2) := by decide
theorem sh_at_1a8 : fetchRel shr12Code 0x1A8 = some (.alu .add a1 a1 a2, 2) := by decide
theorem sh_at_1aa : fetchRel shr12Code 0x1AA = some (.load .lw a2 a0 0x0, 2) := by decide
theorem sh_at_1ac : fetchRel shr12Code 0x1AC = some (.load .lw a1 a1 0x0, 2) := by decide
theorem sh_at_1ae : fetchRel shr12Code 0x1AE = some (.alu .or a1 a1 a2, 2) := by decide
theorem sh_at_1b0 : fetchRel shr12Code 0x1B0 = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem sh_at_1b2 : fetchRel shr12Code 0x1B2 = some (.store .sw a0 a1 0x0, 2) := by decide
theorem sh_at_1b4 : fetchRel shr12Code 0x1B4 = some (.branch .beq (20 : Fin 32) a2 0x8, 4) := by decide
theorem sh_at_1b8 : fetchRel shr12Code 0x1B8 = some (.store .sw (18 : Fin 32) (22 : Fin 32) 0x2C, 4) := by decide
theorem sh_at_1bc : fetchRel shr12Code 0x1BC = some (.load .lw ra sp 0x8C, 2) := by decide
theorem sh_at_1be : fetchRel shr12Code 0x1BE = some (.load .lw (8 : Fin 32) sp 0x88, 2) := by decide
theorem sh_at_1c0 : fetchRel shr12Code 0x1C0 = some (.load .lw (9 : Fin 32) sp 0x84, 2) := by decide
theorem sh_at_1c2 : fetchRel shr12Code 0x1C2 = some (.load .lw (18 : Fin 32) sp 0x80, 2) := by decide
theorem sh_at_1c4 : fetchRel shr12Code 0x1C4 = some (.load .lw (19 : Fin 32) sp 0x7C, 2) := by decide
theorem sh_at_1c6 : fetchRel shr12Code 0x1C6 = some (.load .lw (20 : Fin 32) sp 0x78, 2) := by decide
theorem sh_at_1c8 : fetchRel shr12Code 0x1C8 = some (.load .lw (21 : Fin 32) sp 0x74, 2) := by decide
theorem sh_at_1ca : fetchRel shr12Code 0x1CA = some (.load .lw (22 : Fin 32) sp 0x70, 2) := by decide
theorem sh_at_1cc : fetchRel shr12Code 0x1CC = some (.load .lw (23 : Fin 32) sp 0x6C, 2) := by decide
theorem sh_at_1ce : fetchRel shr12Code 0x1CE = some (.aluImm .add sp sp 0x90, 2) := by decide
theorem sh_at_1d0 : fetchRel shr12Code 0x1D0 = some (.jalr x0 ra 0x0, 2) := by decide
theorem lm_at_0 : fetchRel leadMut12Code 0x0 = some (.branch .bltu a1 a2 0x8, 4) := by decide
theorem lm_at_4 : fetchRel leadMut12Code 0x4 = some (.alu .add a1 x0 a2, 2) := by decide
theorem lm_at_6 : fetchRel leadMut12Code 0x6 = some (.jalr x0 ra 0x0, 2) := by decide
theorem tr_at_0 : fetchRel trailing12Code 0x0 = some (.branch .bltu a1 a2 0xE, 4) := by decide
theorem tr_at_4 : fetchRel trailing12Code 0x4 = some (.aluImm .sll a3 a2 0x2, 4) := by decide
theorem tr_at_8 : fetchRel trailing12Code 0x8 = some (.alu .add a0 a0 a3, 2) := by decide
theorem tr_at_a : fetchRel trailing12Code 0xA = some (.alu .sub a1 a1 a2, 2) := by decide
theorem tr_at_c : fetchRel trailing12Code 0xC = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem srl_nat (x r : Word) (h : r.toNat < 32) : (aluEval .srl x r).toNat = x.toNat / 2 ^ r.toNat := by
  show (x >>> (r.toNat % 32)).toNat = _
  rw [Nat.mod_eq_of_lt h, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem sll_nat (x r : Word) (h : r.toNat < 32) : (aluEval .sll x r).toNat = x.toNat * 2 ^ r.toNat % 2 ^ 32 := by
  show (x <<< (r.toNat % 32)).toNat = _
  rw [Nat.mod_eq_of_lt h, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- An OR of a word whose low `i` bits are zero and a word below `2^i` is
their sum. -/
theorem or_nat (a b : Word) {i : Nat} (ha : a.toNat % 2 ^ i = 0) (hb : b.toNat < 2 ^ i) :
    (aluEval .or a b).toNat = a.toNat + b.toNat := by
  show (a ||| b).toNat = _
  rw [BitVec.toNat_or]
  have e : a.toNat = 2 ^ i * (a.toNat / 2 ^ i) := by
    have := Nat.div_add_mod a.toNat (2 ^ i); omega
  rw [e, ← Nat.two_pow_add_eq_or_of_lt hb]

theorem or_nat' (a b : Word) {i : Nat} (ha : a.toNat < 2 ^ i) (hb : b.toNat % 2 ^ i = 0) :
    (aluEval .or a b).toNat = a.toNat + b.toNat := by
  show (a ||| b).toNat = _
  rw [BitVec.toNat_or, Nat.or_comm]
  have e : b.toNat = 2 ^ i * (b.toNat / 2 ^ i) := by
    have := Nat.div_add_mod b.toNat (2 ^ i); omega
  rw [e, ← Nat.two_pow_add_eq_or_of_lt ha]; omega

theorem zw (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

/-- The function's frame: its `sp` while it runs. -/
abbrev shF (sp0 : Word) : Word := sp0 + 0xFFFFFF70

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev shPs : List (Fin 32 × Word) :=
  [(ra, 0x8C), ((8 : Fin 32), 0x88), ((9 : Fin 32), 0x84), ((18 : Fin 32), 0x80), ((19 : Fin 32), 0x7C),
   ((20 : Fin 32), 0x78), ((21 : Fin 32), 0x74), ((22 : Fin 32), 0x70), ((23 : Fin 32), 0x6C)]

/-- From 0x14 to 0x20: keep the shift and `hi`, and `64 - shift`. -/
def shMov : List BInstr :=
  [.alu .add (21 : Fin 32) x0 a2, .alu .add (19 : Fin 32) x0 a1, .aluImm .add a2 x0 0x40,
   .alu .sub a1 a2 (21 : Fin 32)]

/-- From 0x24 to 0x3E: keep `lo`, zero the buffer at 0x38, and set up the
copy of `hi` into it. -/
def shInit : List BInstr :=
  [.alu .add (18 : Fin 32) x0 a0, .sw sp x0 0x38, .sw sp x0 0x3C, .aluImm .srl a2 a1 0x5, .aluImm .sll a0 a2 0x2,
   .aluImm .add a3 sp 0x38, .alu .add a0 a0 a3, .aluImm .add a3 a2 0xFFFFFFFE, .alu .add a4 x0 a0,
   .alu .add a5 x0 (19 : Fin 32)]

/-- One pass of the copy of `hi` into the buffer, from 0x40 to 0x4A. -/
def shL1 : List BInstr :=
  [.lw (9 : Fin 32) a5 0x0, .aluImm .add a5 a5 0x4, .sw a4 (9 : Fin 32) 0x0, .aluImm .add a4 a4 0x4,
   .aluImm .add a3 a3 0x1]

/-- From 0x50 to 0x5A: the shift loop's carry, `32 - bits`, and count. -/
def shL2i : List BInstr :=
  [.aluImm .add a3 x0 0x0, .aluImm .add a4 x0 0x20, .alu .sub a4 a4 a1, .aluImm .add a2 a2 0xFFFFFFFE]

/-- One pass of the left shift of the buffer, from 0x5C to 0x6E. -/
def shL2 : List BInstr :=
  [.lw a5 a0 0x0, .alu .sll (9 : Fin 32) a5 a1, .alu .or (9 : Fin 32) (9 : Fin 32) a3, .alu .srl a3 a5 a4,
   .sw a0 (9 : Fin 32) 0x0, .aluImm .add a0 a0 0x4, .aluImm .add a2 a2 0x1]

/-- From 0x70 to 0x7C: copy the buffer to `F` and keep its top word. -/
def shTail : List BInstr :=
  [.lw a0 sp 0x38, .lw (22 : Fin 32) sp 0x3C, .aluImm .add a1 x0 0x3F, .sw sp a0 0x0, .sw sp (22 : Fin 32) 0x4]

/-- One pass of the word copy that `hi` and `lo` go through, from 0xB6 and
from 0x136. -/
def shCpy : List BInstr :=
  [.lw a3 a0 0x0, .aluImm .add a0 a0 0x4, .sw a2 a3 0x0, .aluImm .add a2 a2 0x4, .aluImm .add a1 a1 0xFFFFFFFF]

/-- One pass of the right shift that `hi` and `lo` go through, from 0xDC
and from 0x158. -/
def shSrB : List BInstr :=
  [.lw a3 a2 0x0, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, .alu .srl a4 a3 (9 : Fin 32),
   .alu .or a4 a4 a0, .alu .sll a0 a3 a1, .sw a2 a4 0x0]

section
set_option maxRecDepth 20000
theorem shSrAH_end : blockEnd shr12Code 0xD8 [.aluImm .add a2 a2 0xFFFFFFFC] = some (0xD8 + 2) := by decide
theorem shSrAL_end : blockEnd shr12Code 0x154 [.aluImm .add a2 a2 0xFFFFFFFC] = some (0x154 + 2) := by decide
theorem shSrBH_end : blockEnd shr12Code (0xD8 + 4) shSrB = some (0xD8 + 0x14) := by decide
theorem shSrBL_end : blockEnd shr12Code (0x154 + 4) shSrB = some (0x154 + 0x14) := by decide
theorem shCpyH_end : blockEnd shr12Code 0xB6 shCpy = some (0xB6 + 0xA) := by decide
theorem shCpyL_end : blockEnd shr12Code 0x136 shCpy = some (0x136 + 0xA) := by decide
theorem shL1_end : blockEnd shr12Code 0x40 shL1 = some 0x4A := by decide
theorem shAnd_end : blockEnd shr12Code 0x4C [.aluImm .and a1 a1 0x1F] = some 0x4E := by decide
theorem shL2i_end : blockEnd shr12Code 0x50 shL2i = some 0x5A := by decide
theorem shL2_end : blockEnd shr12Code 0x5C shL2 = some 0x6E := by decide
theorem shTail_end : blockEnd shr12Code 0x70 shTail = some 0x7C := by decide
theorem shSave_end : blockEnd shr12Code 2 (saveBlock shPs) = some 0x14 := by decide
theorem shMov_end : blockEnd shr12Code 0x14 shMov = some 0x20 := by decide
theorem shInit_end : blockEnd shr12Code 0x24 shInit = some 0x3E := by decide
end

set_option maxRecDepth 20000 in
theorem shPs_range : ∀ p ∈ shPs, p.2.toNat % 4 = 0 ∧ 0x6C ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x90 := by decide

/-- Where `shr_in_place_wide::<12, 2>` runs: its code and its callees' at
their offsets, its 0x90-byte frame below `sp0`, and `lo` and `hi`, aligned
and apart from each other, the frame, and the code they could reach. -/
structure SHEnv (M : Word → BitVec 8) (P sp0 lo hi : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P shr12Code
  lm : CodeIn M (P + 0x1EE) leadMut12Code
  tr : CodeIn M (P + 0x1FE) trailing12Code
  mset : CodeIn M (P + 0x1724) memsetCode
  stub : CodeIn M (P + 0x178C) memcpyStubCode
  body : CodeIn M (P + 0x1794) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x90 ≤ sp0.toNat
  hlo : lo.toNat % 4 = 0
  hhi : hi.toNat % 4 = 0
  hwl : lo.toNat + 48 < 2 ^ 32
  hwh : hi.toNat + 8 < 2 ^ 32
  sC : Sep (shF sp0) 0x90 P shr12Code.length
  sLm : Sep (shF sp0) 0x90 (P + 0x1EE) leadMut12Code.length
  sTr : Sep (shF sp0) 0x90 (P + 0x1FE) trailing12Code.length
  sMs : Sep (shF sp0) 0x90 (P + 0x1724) memsetCode.length
  sU : Sep (shF sp0) 0x90 (P + 0x178C) memcpyStubCode.length
  sB : Sep (shF sp0) 0x90 (P + 0x1794) memcpyBodyCode.length
  sL : Sep lo 48 (shF sp0) 0x90
  sH : Sep hi 8 (shF sp0) 0x90
  sLH : Sep lo 48 hi 8
  lC : Sep lo 48 P shr12Code.length
  lB : Sep lo 48 (P + 0x1794) memcpyBodyCode.length
  hC : Sep hi 8 P shr12Code.length
  hLm : Sep hi 8 (P + 0x1EE) leadMut12Code.length
  hTr : Sep hi 8 (P + 0x1FE) trailing12Code.length
  hMs : Sep hi 8 (P + 0x1724) memsetCode.length
  hU : Sep hi 8 (P + 0x178C) memcpyStubCode.length
  hB : Sep hi 8 (P + 0x1794) memcpyBodyCode.length

theorem shF_w {sp0 : Word} (h : 0x90 ≤ sp0.toNat) : (shF sp0).toNat + 0x90 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFF70 : Word).toNat = 4294967152 := rfl
  have := sp0.isLt
  omega

theorem shF_in {sp0 b : Word} {c l k : Nat} (h : c + l ≤ 0x90) (hx : Sep (shF sp0) 0x90 b k) :
    Sep (shF sp0 + BitVec.ofNat 32 c) l b k := hx.sub h

/-- The registers the function leaves alone. -/
def shKeep (q : Fin 32) : Bool := q.val ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The prologue, from entry to the copy of `hi` at 0x40: save the
registers, keep the arguments, zero the buffer at `F + 0x38`, and point at
the buffer's word `(64 - shift) / 32`. -/
theorem sh_pro (m : Machine) {P sp0 lo hi : Word} {s : Nat} (env : SHEnv m.mem P sp0 lo hi) (hpc : m.pc = P)
    (hsp : reg m sp = sp0) (ha0 : reg m a0 = lo) (ha1 : reg m a1 = hi) (ha2 : reg m a2 = BitVec.ofNat 32 s)
    (hs1 : 1 ≤ s) (hs2 : s ≤ 63) :
    ∃ n M, Steps m n ∧ St M P n 0x40 (reg n) ∧
      (∀ x, Sep (shF sp0) 0x90 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ shPs → memLoad32 M (shF sp0 + o) = reg m r) ∧
      memLoad32 M (shF sp0 + BitVec.ofNat 32 0x38) = 0 ∧ memLoad32 M (shF sp0 + BitVec.ofNat 32 0x3C) = 0 ∧
      (∀ x, Sep (shF sp0 + BitVec.ofNat 32 0x38) 8 x 1 → Sep (shF sp0 + BitVec.ofNat 32 0x6C) 0x24 x 1 →
        M x = m.mem x) ∧
      reg n sp = shF sp0 ∧ reg n 21 = BitVec.ofNat 32 s ∧ reg n 19 = hi ∧ reg n 18 = lo ∧
      reg n a1 = BitVec.ofNat 32 (64 - s) ∧ reg n a2 = BitVec.ofNat 32 ((64 - s) / 32) ∧
      reg n a0 = shF sp0 + 0x38 + BitVec.ofNat 32 (4 * ((64 - s) / 32)) ∧
      reg n a3 = BitVec.ofNat 32 ((64 - s) / 32) + 0xFFFFFFFE ∧
      reg n a4 = shF sp0 + 0x38 + BitVec.ofNat 32 (4 * ((64 - s) / 32)) ∧ reg n a5 = hi ∧
      ∀ q, shKeep q = true → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hFw := shF_w env.hS
  have hFa : (shF sp0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF70) (by decide)
  have sFC : Sep (shF sp0) 0x90 P shr12Code.length := env.sC
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code sh_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF70) sp = shF sp0 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock shPs) u1 env.code shSave_end (saveBlock_ok _ shPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (shPs_range p hp).1, frm_sep' sFC (by have := shPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (shF sp0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF70)) shPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (shF sp0) 0x90 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside shPs fun p hp => frm_sep' hx (by have := shPs_range p hp; omega)
  have frSv' : ∀ x, Sep (shF sp0 + BitVec.ofNat 32 0x6C) 0x24 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; refine saveMem_outside shPs fun p hp => ?_
    have h := shPs_range p hp
    have := hx.sub (c := p.2.toNat - 0x6C) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x6C + (p.2.toNat - 0x6C) = p.2.toNat by omega, ofNat_toNat_self] at this
  have cIn : ∀ {M' : Word → BitVec 8}, (∀ x, Sep (shF sp0) 0x90 x 1 → M' x = m.mem x) →
      CodeIn M' P shr12Code := fun hM i hi => by
    rw [hM _ (sFC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  obtain ⟨m3, c3, u3⟩ := St.block shMov u2.self (cIn frSv) shMov_end
    (by simp [BlockOk, BInstr.ok, shMov])
  simp only [runBlock, BInstr.run, shMov] at u3
  have r2 : ∀ q, reg m2 q = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF70) q := u2.regs
  have g3 : ∀ q, reg m3 q = _ := u3.regs
  have e1 : reg m3 a1 = BitVec.ofNat 32 (64 - s) := by
    rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval, r2]
    (try rw [hz]); rw [ha2]; apply BitVec.eq_of_toNat_eq
    have z0 : (0 : Word).toNat = 0 := rfl
    have z64 : (64 : Word).toNat = 64 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, z0, z64]; omega
  have e2 : reg m3 a2 = 0x40 := by
    rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval, r2]; first | done | rfl | (rw [hz]; rfl)
  obtain ⟨m4, d4, u4⟩ := u3.self.notTaken (cIn frSv) 0x24 sh_at_20 (by decide) (by
    have hu : (BitVec.ofNat 32 (64 - s)).ult 64 = true := by
      simp only [BitVec.ult, decide_eq_true_eq]; rw [BitVec.toNat_ofNat]; show (64 - s) % 2 ^ 32 < 64; omega
    rw [e1, e2]; show (!(BitVec.ofNat 32 (64 - s)).ult 64) = false; rw [hu]; rfl)
  obtain ⟨m5, c5, u5⟩ := St.block shInit u4 (cIn frSv) shInit_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, shInit, upd_app, ↓reduceIte, and_true, true_and]
    rw [g3]; simp +decide only [upd_app, ↓reduceIte]
    rw [show reg m2 sp = shF sp0 from by rw [u2.regs]; exact sp1]
    exact ⟨⟨aligned_add hFa (k := 0x38) (by decide), shF_in (c := 0x38) (by decide) sFC⟩,
      ⟨aligned_add hFa (k := 0x3C) (by decide), shF_in (c := 0x3C) (by decide) sFC⟩⟩)
  simp +decide only [runBlock, BInstr.run, shInit, upd_app, ↓reduceIte, g3, r2, hsp, ev_add] at u5
  have g5 : ∀ q, reg m5 q = _ := u5.regs
  have f5 : ∀ x, Sep (shF sp0) 0x90 x 1 → m5.mem x = m.mem x := fun x hx => by
    rw [u5.mem, memStore32_get_sep (frm_sep' hx (c := 0x3C) (by decide)),
      memStore32_get_sep (frm_sep' hx (c := 0x38) (by decide)), frSv x hx]
  have hA1 : aluEval .sub (0 + 64) (0 + reg m a2) = BitVec.ofNat 32 (64 - s) := by
    rw [ha2]; apply BitVec.eq_of_toNat_eq
    have z0 : (0 : Word).toNat = 0 := rfl
    have z64 : (64 : Word).toNat = 64 := rfl
    simp only [aluEval, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, z0, z64]; omega
  have hA2 : aluEval .srl (BitVec.ofNat 32 (64 - s)) 5 = BitVec.ofNat 32 ((64 - s) / 32) := by
    apply BitVec.eq_of_toNat_eq
    show ((BitVec.ofNat 32 (64 - s)) >>> ((5 : Word).toNat % 32)).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    show (64 - s) % 2 ^ 32 / 2 ^ 5 = (64 - s) / 32 % 2 ^ 32; omega
  have ews : (64 - s) / 32 = 0 ∨ (64 - s) / 32 = 1 := by omega
  have ea2 : reg m5 a2 = BitVec.ofNat 32 ((64 - s) / 32) := by
    rw [g5]; simp +decide only [upd_app, ↓reduceIte]; rw [hA1, hA2]
  have ea0 : reg m5 a0 = shF sp0 + BitVec.ofNat 32 0x38 + BitVec.ofNat 32 (4 * ((64 - s) / 32)) := by
    have hsll : aluEval .sll (BitVec.ofNat 32 ((64 - s) / 32)) 2 = BitVec.ofNat 32 (4 * ((64 - s) / 32)) := by
      apply BitVec.eq_of_toNat_eq
      rw [sll_nat _ _ (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      show (64 - s) / 32 % 2 ^ 32 * 2 ^ 2 % 2 ^ 32 = 4 * ((64 - s) / 32) % 2 ^ 32; omega
    rw [g5]; simp +decide only [upd_app, ↓reduceIte]; rw [hA1, hA2, hsll, BitVec.add_comm]; rfl
  have ea3 : reg m5 a3 = BitVec.ofNat 32 ((64 - s) / 32) + 0xFFFFFFFE := by
    rw [g5]; simp +decide only [upd_app, ↓reduceIte]; rw [hA1, hA2]; first | done | rfl
  have hc5 := cIn (M' := m5.mem) f5
  rw [u5.mem] at hc5
  obtain ⟨m6, d6, u6⟩ := u5.self.notTaken hc5
    0x40 sh_at_3e (by decide) (by
      rw [ea3, u5.self.zero]; simp only [branchTaken]
      rcases ews with h | h <;> rw [h] <;> decide)
  have g6 : ∀ q, reg m6 q = reg m5 q := fun q => by rw [u6.regs, g5]
  refine ⟨m6, _, .cons d1 (c2.trans (c3.trans (.cons d4 (c5.trans (.single d6))))), u6.self,
    fun x hx => ?_, fun r o h => ?_, ?_, ?_, fun x h8 h6 => ?_, ?_, ?_, ?_, ?_, ?_, by rw [g6, ea2],
    by rw [g6, ea0]; rfl, by rw [g6, ea3], ?_, ?_, fun q hq => ?_⟩
  · rw [memStore32_get_sep (frm_sep' hx (c := 0x3C) (by decide)),
      memStore32_get_sep (frm_sep' hx (c := 0x38) (by decide)), frSv x hx]
  · obtain ⟨_, ho1, ho2⟩ := shPs_range (r, o) h
    dsimp only at ho1 ho2
    rw [← hMsv]
    simp only [shPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  · simp (disch := decide) only [ls_lit, ls_same]
  · simp (disch := decide) only [ls_lit, ls_same]
  · have h3C : Sep (shF sp0 + 0x3C) 4 x 1 := by
      have := h8.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
    have h38 : Sep (shF sp0 + 0x38) 4 x 1 := by
      have := h8.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep h3C, memStore32_get_sep h38, frSv' x h6]
  · simp +decide only [g6, g5, g3, r2, upd_app, ↓reduceIte, hsp, ev_add]
  · simp +decide only [g6, g5, g3, r2, upd_app, ↓reduceIte, hz, ha2, ev_add, zw]
  · simp +decide only [g6, g5, g3, r2, upd_app, ↓reduceIte, hz, ha1, ev_add, zw]
  · simp +decide only [g6, g5, g3, r2, upd_app, ↓reduceIte, hz, ha0, ev_add, zw]
  · rw [g6, ← e1]
    simp +decide only [g5, upd_app, ↓reduceIte]
  · rw [g6, show reg m5 a4 = reg m5 a0 by simp +decide only [g5, upd_app, ↓reduceIte, ev_add, zw],
      ea0]; rfl
  · simp +decide only [g6, g5, g3, r2, upd_app, ↓reduceIte, hz, ha1, ev_add, zw]
  · have k := fun r (hr : shKeep r = false) => pkeep_ne hq hr
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u6.self.zero, hz]
    simp only [g6, g5, g3, r2, upd_app, h0, k sp rfl, k a0 rfl, k a1 rfl, k a2 rfl, k a3 rfl, k a4 rfl, k a5 rfl,
      k 18 rfl, k 19 rfl, k 21 rfl, ite_false]


/-- The registers a pass of the copy into the buffer leaves alone. -/
def shL1Keep (q : Fin 32) : Bool := q.val ∉ [0, 9, 13, 14, 15]

set_option maxRecDepth 20000 in
/-- **One pass of the copy of `hi`**, from 0x40: the word at `src` goes to
`dst`, both pointers advance, and the count `c` goes up by one. -/
theorem sh_l1 {M : Word → BitVec 8} {P src dst c : Word} {n : Machine} (s : St M P n 0x40 (reg n))
    (hc : CodeIn M P shr12Code) (hs : src.toNat % 4 = 0) (hd : dst.toNat % 4 = 0)
    (sD : Sep dst 4 P shr12Code.length) (r15 : reg n a5 = src) (r14 : reg n a4 = dst) (r13 : reg n a3 = c) :
    ∃ n', Steps n n' ∧ St (memStore32 M dst (memLoad32 M src)) P n'
        (if c + 1 = 0 then 0x4C else 0x40) (reg n') ∧
      reg n' a5 = src + 4 ∧ reg n' a4 = dst + 4 ∧ reg n' a3 = c + 1 ∧ reg n' 9 = memLoad32 M src ∧
      ∀ q, shL1Keep q = true → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block shL1 s hc shL1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, shL1, upd_app, ↓reduceIte, and_true, true_and]
    rw [r15, r14, add_lit_zero, add_lit_zero]; exact ⟨hs, hd, sD⟩)
  simp +decide only [runBlock, BInstr.run, shL1, upd_app, ↓reduceIte, r15, r14, r13, add_lit_zero] at u1
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  have hc1 := hc.store32 (v := memLoad32 M src) sD
  have e13 : reg n1 a3 = c + 1 := by rw [g1]; simp +decide only [upd_app, ↓reduceIte, r13, ev_add]
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a5 = src + 4 ∧ reg n2 a4 = dst + 4 ∧ reg n2 a3 = c + 1 ∧ reg n2 9 = memLoad32 M src ∧
      ∀ q, shL1Keep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, g1]; simp +decide only [upd_app, ↓reduceIte, r15, ev_add],
      by rw [h2, g1]; simp +decide only [upd_app, ↓reduceIte, r14, ev_add], by rw [h2, e13],
      by rw [h2, g1]; simp +decide only [upd_app, ↓reduceIte, r15, add_lit_zero], fun q hq => ?_⟩
    have k := fun r (hr : shL1Keep r = false) => pkeep_ne hq hr
    have h0 : q.val ≠ 0 := fun e => absurd (show shL1Keep q = false by unfold shL1Keep; simp [e]) (by rw [hq]; decide)
    rw [h2, g1]; simp only [upd_app, h0, k 9 rfl, k a3 rfl, k a4 rfl, k a5 rfl, ite_false]
  by_cases hl : c + 1 = 0
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x4C sh_at_4a (by decide) (by
      rw [e13, hl, u1.self.zero]; rfl)
    exact ⟨n2, c1.trans (.single d2), by rw [if_pos hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x40 sh_at_4a (by decide) (by
      rw [e13, u1.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; exact hl)
    exact ⟨n2, c1.trans (.single d2), by rw [if_neg hl]; exact u2.self, post n2 u2.regs⟩


/-- The registers a pass of the left shift leaves alone. -/
def shL2Keep (q : Fin 32) : Bool := q.val ∉ [0, 9, 10, 12, 13, 15]

/-- The word a pass of the left shift stores: the word at `p` shifted left
`b` bits, with the bits that moved out of the word below. -/
abbrev shlW (w b carry : Word) : Word := aluEval .or (aluEval .sll w b) carry

set_option maxRecDepth 20000 in
/-- **One pass of the left shift of the buffer**, from 0x5C. -/
theorem sh_l2 {M : Word → BitVec 8} {P p b r carry c : Word} {n : Machine} (s : St M P n 0x5C (reg n))
    (hc : CodeIn M P shr12Code) (hp : p.toNat % 4 = 0) (sD : Sep p 4 P shr12Code.length)
    (r10 : reg n a0 = p) (r11 : reg n a1 = b) (r14 : reg n a4 = r) (r13 : reg n a3 = carry) (r12 : reg n a2 = c) :
    ∃ n', Steps n n' ∧ St (memStore32 M p (shlW (memLoad32 M p) b carry)) P n'
        (if c + 1 = 0 then 0x70 else 0x5C) (reg n') ∧
      reg n' a0 = p + 4 ∧ reg n' a3 = aluEval .srl (memLoad32 M p) r ∧ reg n' a2 = c + 1 ∧
      ∀ q, shL2Keep q = true → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block shL2 s hc shL2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, shL2, upd_app, ↓reduceIte, and_true, true_and]
    rw [r10, add_lit_zero]; exact ⟨hp, hp, sD⟩)
  simp +decide only [runBlock, BInstr.run, shL2, upd_app, ↓reduceIte, r10, r11, r12, r13, r14,
    add_lit_zero] at u1
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  have hc1 := hc.store32 (v := shlW (memLoad32 M p) b carry) sD
  have e12 : reg n1 a2 = c + 1 := by rw [g1]; simp +decide only [upd_app, ↓reduceIte, r12, ev_add]
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a0 = p + 4 ∧ reg n2 a3 = aluEval .srl (memLoad32 M p) r ∧ reg n2 a2 = c + 1 ∧
      ∀ q, shL2Keep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, g1]; simp +decide only [upd_app, ↓reduceIte, r10, ev_add],
      by rw [h2, g1]; simp +decide only [upd_app, ↓reduceIte, r10, r14, add_lit_zero], by rw [h2, e12],
      fun q hq => ?_⟩
    have k := fun r (hr : shL2Keep r = false) => pkeep_ne hq hr
    have h0 : q.val ≠ 0 := fun e => absurd (show shL2Keep q = false by unfold shL2Keep; simp [e]) (by rw [hq]; decide)
    rw [h2, g1]; simp only [upd_app, h0, k 9 rfl, k a0 rfl, k a2 rfl, k a3 rfl, k a5 rfl, ite_false]
  by_cases hl : c + 1 = 0
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x70 sh_at_6e (by decide) (by
      rw [e12, hl, u1.self.zero]; rfl)
    exact ⟨n2, c1.trans (.single d2), by rw [if_pos hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x5C sh_at_6e (by decide) (by
      rw [e12, u1.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; exact hl)
    exact ⟨n2, c1.trans (.single d2), by rw [if_neg hl]; exact u2.self, post n2 u2.regs⟩


theorem shSep0 {a b : Word} {n k : Nat} (h : Sep (a + BitVec.ofNat 32 0) n b k) : Sep a n b k := by
  rwa [add_ofNat_zero] at h

/-- The registers a pass of the word copy leaves alone. -/
def shCpyKeep (q : Fin 32) : Bool := q.val ∉ [0, 10, 11, 12, 13]

theorem shCnt_dec {k i : Nat} (h : i < k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 (k - i) + 0xFFFFFFFF = BitVec.ofNat 32 (k - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : (0xFFFFFFFF : Word).toNat = 4294967295 := rfl
  rw [this]; omega

theorem shCnt_ne {k i : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 (k - (i + 1)) != 0) = decide (i + 1 < k) := by
  by_cases h : i + 1 < k
  · rw [decide_eq_true h]; simp only [bne_iff_ne, ne_eq]; intro e
    have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat] at this; simp at this; omega
  · rw [decide_eq_false h, show k - (i + 1) = 0 by omega]; rfl

set_option maxRecDepth 20000 in
/-- **One pass of the word copy**, from `o`, either copy's start. -/
theorem sh_cpy_iter {o : Nat} {M : Word → BitVec 8} {P src dst : Word} {n : Machine} {i k : Nat}
    (hE : blockEnd shr12Code o shCpy = some (o + 0xA))
    (hB : fetchRel shr12Code (o + 0xA) = some (.branch .bne a1 x0 0xFFFFFFF6, 2))
    (hT : BitVec.ofNat 32 (o + 0xA) + 0xFFFFFFF6 = BitVec.ofNat 32 o)
    (hF : BitVec.ofNat 32 (o + 0xA) + 2 = BitVec.ofNat 32 (o + 0xC))
    (s : St M P n o (reg n)) (hc : CodeIn M P shr12Code) (hik : i < k) (hk : k < 2 ^ 32)
    (hs : (src + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0) (hd : (dst + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0)
    (sD : Sep (dst + BitVec.ofNat 32 (4 * i)) 4 P shr12Code.length)
    (r10 : reg n a0 = src + BitVec.ofNat 32 (4 * i)) (r12 : reg n a2 = dst + BitVec.ofNat 32 (4 * i))
    (r11 : reg n a1 = BitVec.ofNat 32 (k - i)) :
    ∃ n', Steps n n' ∧ St (memStore32 M (dst + BitVec.ofNat 32 (4 * i)) (memLoad32 M (src + BitVec.ofNat 32 (4 * i))))
        P n' (if i + 1 < k then o else o + 0xC) (reg n') ∧
      reg n' a0 = src + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = dst + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a1 = BitVec.ofNat 32 (k - (i + 1)) ∧ ∀ q, shCpyKeep q = true → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block shCpy s hc hE (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, shCpy, upd_app, ↓reduceIte, and_true, true_and]
    rw [r10, r12, add_lit_zero, add_lit_zero]; exact ⟨hs, hd, sD⟩)
  simp +decide only [runBlock, BInstr.run, shCpy, upd_app, ↓reduceIte, r10, r11, r12, add_lit_zero] at u1
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  have hc1 := hc.store32 (v := memLoad32 M (src + BitVec.ofNat 32 (4 * i))) sD
  have e11 : reg n1 a1 = BitVec.ofNat 32 (k - (i + 1)) := by
    rw [g1]; simp +decide only [upd_app, ↓reduceIte, ev_add]; exact shCnt_dec hik hk
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a0 = src + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a2 = dst + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 a1 = BitVec.ofNat 32 (k - (i + 1)) ∧ ∀ q, shCpyKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, g1]; simp +decide only [upd_app, ↓reduceIte, ev_add]; exact ptr4 _ _,
      by rw [h2, g1]; simp +decide only [upd_app, ↓reduceIte, ev_add]; exact ptr4 _ _, by rw [h2, e11],
      fun q hq => ?_⟩
    have k := fun r (hr : shCpyKeep r = false) => pkeep_ne hq hr
    have h0 : q.val ≠ 0 := fun e => absurd (show shCpyKeep q = false by unfold shCpyKeep; simp [e]) (by rw [hq]; decide)
    rw [h2, g1]; simp only [upd_app, h0, k a0 rfl, k a1 rfl, k a2 rfl, k a3 rfl, ite_false]
  have hb : branchTaken .bne (reg n1 a1) (reg n1 x0) = decide (i + 1 < k) := by
    rw [e11, u1.self.zero]; exact shCnt_ne hk
  by_cases hl : i + 1 < k
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 o hB hT (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 (o + 0xC) hB hF (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The word copy**, from word `i` to its end: `k` words from `src` to
`dst`, which don't overlap. -/
theorem sh_cpy_loop {o : Nat} {P src dst : Word} {M0 : Word → BitVec 8} {k : Nat}
    (hE : blockEnd shr12Code o shCpy = some (o + 0xA))
    (hB : fetchRel shr12Code (o + 0xA) = some (.branch .bne a1 x0 0xFFFFFFF6, 2))
    (hT : BitVec.ofNat 32 (o + 0xA) + 0xFFFFFFF6 = BitVec.ofNat 32 o)
    (hF : BitVec.ofNat 32 (o + 0xA) + 2 = BitVec.ofNat 32 (o + 0xC))
    (hk : k < 2 ^ 32) (hs : src.toNat % 4 = 0) (hd : dst.toNat % 4 = 0) (hdw : dst.toNat + 4 * k ≤ 2 ^ 32)
    (hc0 : CodeIn M0 P shr12Code) (sD : Sep dst (4 * k) P shr12Code.length) (sS : Sep dst (4 * k) src (4 * k)) :
    ∀ m i, i + m + 1 = k → ∀ {n : Machine}, St (copyWords M0 dst src i) P n o (reg n) →
      reg n a0 = src + BitVec.ofNat 32 (4 * i) → reg n a2 = dst + BitVec.ofNat 32 (4 * i) →
      reg n a1 = BitVec.ofNat 32 (k - i) →
      ∃ n', Steps n n' ∧ St (copyWords M0 dst src k) P n' (o + 0xC) (reg n') ∧
        reg n' a0 = src + BitVec.ofNat 32 (4 * k) ∧ reg n' a2 = dst + BitVec.ofNat 32 (4 * k) ∧
        ∀ q, shCpyKeep q = true → reg n' q = reg n q := by
  have cIn : ∀ i, i ≤ k → CodeIn (copyWords M0 dst src i) P shr12Code := fun i hi j hj => by
    rw [copyWords_outside i ((sD.sub (c := 0) (l := 4 * i) (by omega) |> shSep0).subR (c := j) (l := 1)
      (by omega))]
    exact hc0 j hj
  have step : ∀ i, i < k → ∀ {n : Machine}, St (copyWords M0 dst src i) P n o (reg n) →
      reg n a0 = src + BitVec.ofNat 32 (4 * i) → reg n a2 = dst + BitVec.ofNat 32 (4 * i) →
      reg n a1 = BitVec.ofNat 32 (k - i) →
      ∃ n', Steps n n' ∧ St (copyWords M0 dst src (i + 1)) P n' (if i + 1 < k then o else o + 0xC) (reg n') ∧
        reg n' a0 = src + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = dst + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' a1 = BitVec.ofNat 32 (k - (i + 1)) ∧ ∀ q, shCpyKeep q = true → reg n' q = reg n q := by
    intro i hi n st r10 r12 r11
    have sDi : Sep (dst + BitVec.ofNat 32 (4 * i)) 4 P shr12Code.length := sD.sub (by omega)
    obtain ⟨n1, c1, u1, e10, e12, e11, fr⟩ := sh_cpy_iter hE hB hT hF st (cIn i (by omega)) hi hk
      (aligned_add hs (by omega)) (aligned_add hd (by omega)) sDi r10 r12 r11
    rw [copyWords_load_sep (by
      have := sS.sub (c := 0) (l := 4 * i) (by omega) |> shSep0
      exact this.subR (by omega))] at u1
    exact ⟨n1, c1, u1, e10, e12, e11, fr⟩
  intro m
  induction m with
  | zero =>
    intro i hi n st r10 r12 r11
    have ik : i + 1 = k := hi
    obtain ⟨n1, c1, u1, e10, e12, _, fr⟩ := step i (by omega) st r10 r12 r11
    rw [ite_eq_right (by omega), ik] at u1
    rw [ik] at e10 e12
    exact ⟨n1, c1, u1, e10, e12, fr⟩
  | succ m ih =>
    intro i hi n st r10 r12 r11
    obtain ⟨n1, c1, u1, e10, e12, e11, fr⟩ := step i (by omega) st r10 r12 r11
    rw [ite_eq_left (by omega)] at u1
    obtain ⟨n', c', u', e10', e12', fr'⟩ := ih (i + 1) (by omega) u1 e10 e12 e11
    exact ⟨n', c1.trans c', u', e10', e12', fun q hq => by rw [fr' q hq, fr q hq]⟩


theorem accV_split (M : Word → BitVec 8) (B : Word) (a : Nat) :
    ∀ b, accV M B (a + b) = accV M B a + 2 ^ (32 * a) * accV M (B + BitVec.ofNat 32 (4 * a)) b
  | 0 => by simp [accV]
  | b + 1 => by
    rw [← Nat.add_assoc, accV_succ1, accV_split M B a b, accV_succ1, add_ofNat_assoc,
      show 4 * a + 4 * b = 4 * (a + b) by omega, show 32 * (a + b) = 32 * a + 32 * b by omega, Nat.pow_add]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
    omega

/-- The right shift's arithmetic for one word. -/
theorem sr_step {x H C L X P t u A : Nat} (htu : t * u = 2 ^ 32) (hC : C = u * A)
    (hinv : (H * t + A) * (2 ^ 32 * P) + (L + x * P) = X) :
    ((x / t + C + 2 ^ 32 * H) * t + x % t) * P + L = X := by
  have e1 := Nat.div_add_mod x t
  have e1P : t * (x / t) * P + x % t * P = x * P := by rw [← Nat.add_mul, e1]
  have eC : u * A * t * P = 2 ^ 32 * (A * P) := by
    rw [Nat.mul_comm u A, Nat.mul_assoc A u t, Nat.mul_comm u t, htu]
    simp only [Nat.mul_comm, Nat.mul_assoc]
  subst hC
  rw [← hinv]
  simp only [Nat.add_mul] at e1P eC ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] at e1P eC ⊢
  omega

theorem shPow_split {b : Nat} (hb : b ≤ 32) : 2 ^ b * 2 ^ (32 - b) = 2 ^ 32 := by
  rw [← Nat.pow_add, Nat.add_sub_cancel' hb]

/-- `x << (32 - b)`, as the loop computes its next carry, is `x`'s low `b`
bits at the top of the word. -/
theorem sll_carry (x : Word) {b : Nat} (hb : b ≤ 32) (h32 : 32 - b < 32) :
    (aluEval .sll x (BitVec.ofNat 32 (32 - b))).toNat = x.toNat % 2 ^ b * 2 ^ (32 - b) := by
  rw [sll_nat _ _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 32 - b < 2 ^ 32)]
  have e := Nat.div_add_mod x.toNat (2 ^ b)
  have hlt : x.toNat % 2 ^ b * 2 ^ (32 - b) < 2 ^ 32 := by
    rw [← shPow_split hb]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos b)) (Nat.two_pow_pos _)
  conv => lhs; rw [← e]
  rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ b), Nat.mul_assoc, Nat.mul_comm (2 ^ (32 - b)), shPow_split hb,
    Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem srl_lt (x : Word) {b : Nat} (hb : b ≤ 32) : x.toNat / 2 ^ b < 2 ^ (32 - b) := by
  apply Nat.div_lt_of_lt_mul; rw [shPow_split hb]; exact x.isLt

theorem sh_pc_even {P : Word} (hP : P.toNat % 2 = 0) {m : Machine} {o : Word} {off off' : Nat}
    (hpc : m.pc = P + BitVec.ofNat 32 off) (hn : BitVec.ofNat 32 off + o = BitVec.ofNat 32 off')
    (h2 : off' % 2 = 0) : (m.pc + o).getLsbD 0 = false := by
  rw [hpc, BitVec.add_assoc, hn]; exact even_bit0 (even_at P hP off' h2)

/-- The registers a pass of the right shift leaves alone. -/
def shSrKeep (q : Fin 32) : Bool := q.val ∉ [0, 8, 10, 12, 13, 14]

/-- Where a right shift's loop sits in the code: its head at `o`. -/
structure SrAt (o : Nat) : Prop where
  hA : blockEnd shr12Code o [.aluImm .add a2 a2 0xFFFFFFFC] = some (o + 2)
  hQ : fetchRel shr12Code (o + 2) = some (.branch .beq (8 : Fin 32) x0 0x14, 2)
  hB : blockEnd shr12Code (o + 4) shSrB = some (o + 0x14)
  hJ : fetchRel shr12Code (o + 0x14) = some (.jal x0 0xFFFFFFEC, 2)
  hF : BitVec.ofNat 32 (o + 2) + 2 = BitVec.ofNat 32 (o + 4)
  hT : BitVec.ofNat 32 (o + 2) + 0x14 = BitVec.ofNat 32 (o + 0x16)
  hN : BitVec.ofNat 32 (o + 0x14) + 0xFFFFFFEC = BitVec.ofNat 32 o
  ho : o % 2 = 0

theorem srAtH : SrAt 0xD8 :=
  ⟨shSrAH_end, sh_at_da, shSrBH_end, sh_at_ec, by decide, by decide, by decide, by decide⟩

theorem srAtL : SrAt 0x154 :=
  ⟨shSrAL_end, sh_at_156, shSrBL_end, sh_at_168, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 20000 in
/-- **One pass of the right shift**, from the loop's head at `o`, for word
`k` of the buffer at `B`: it stores the word shifted right `b` bits, with
the carry `c` from the word above, and carries its low bits down. -/
theorem sh_sr_iter {o : Nat} (at_ : SrAt o) {M : Word → BitVec 8} {P B c r b : Word} {n : Machine} {k : Nat}
    (hP : P.toNat % 2 = 0) (s : St M P n o (reg n)) (hc : CodeIn M P shr12Code) (hk : k + 1 < 2 ^ 32)
    (hB4 : (B + BitVec.ofNat 32 (4 * k)).toNat % 4 = 0) (sD : Sep (B + BitVec.ofNat 32 (4 * k)) 4 P shr12Code.length)
    (r8 : reg n 8 = BitVec.ofNat 32 (k + 1)) (r12 : reg n a2 = B + BitVec.ofNat 32 (4 * (k + 1)))
    (r10 : reg n a0 = c) (r11 : reg n a1 = r) (r9 : reg n 9 = b) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (B + BitVec.ofNat 32 (4 * k))
        (aluEval .or (aluEval .srl (memLoad32 M (B + BitVec.ofNat 32 (4 * k))) b) c)) P n' o (reg n') ∧
      reg n' 8 = BitVec.ofNat 32 k ∧ reg n' a2 = B + BitVec.ofNat 32 (4 * k) ∧
      reg n' a0 = aluEval .sll (memLoad32 M (B + BitVec.ofNat 32 (4 * k))) r ∧
      ∀ q, shSrKeep q = true → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block _ s hc at_.hA (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  have e12 : B + BitVec.ofNat 32 (4 * (k + 1)) + 0xFFFFFFFC = B + BitVec.ofNat 32 (4 * k) := by
    have : (0xFFFFFFFC : Word).toNat = 4294967292 := rfl
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, this]
    omega
  have g1 : ∀ q, reg n1 q = upd (reg n) a2 (aluEval .add (reg n a2) 0xFFFFFFFC) q := u1.regs
  have e8 : reg n1 8 = BitVec.ofNat 32 (k + 1) := by rw [g1, upd_ne (by decide) (by decide), r8]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc (o + 4) at_.hQ at_.hF (by
    rw [e8, u1.self.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
    have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at this; simp at this; omega)
  have ra2 : reg n2 a2 = B + BitVec.ofNat 32 (4 * k) := by
    rw [u2.regs, g1, upd_same (by decide), r12]; exact e12
  obtain ⟨n3, c3, u3⟩ := St.block shSrB u2.self hc at_.hB (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, shSrB, upd_app, ↓reduceIte, and_true, true_and]
    rw [ra2, add_lit_zero]; exact ⟨hB4, hB4, sD⟩)
  simp +decide only [runBlock, BInstr.run, shSrB, upd_app, ↓reduceIte, ra2, add_lit_zero] at u3
  have hc3 := hc.store32 (v := aluEval .or (aluEval .srl (memLoad32 M (B + BitVec.ofNat 32 (4 * k))) b) c) sD
  have g3 : ∀ q, reg n3 q = _ := u3.regs
  have k2 : ∀ q, q ≠ a2 → reg n2 q = reg n q := fun q h => by
    rw [u2.regs, g1]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s.zero.symm
    · exact upd_ne h0 h
  rw [k2 9 (by decide), r9, k2 a0 (by decide), r10, k2 a1 (by decide), r11] at u3
  obtain ⟨n4, d4, u4⟩ := u3.jump hc3 at_.hJ at_.hN (sh_pc_even hP u3.pc at_.hN at_.ho)
  refine ⟨n4, c1.trans (.cons d2 (c3.trans (.single d4))), ⟨u4.pc, u4.mem, fun _ => rfl⟩, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte, ev_add]
    rw [k2 8 (by decide), r8]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : (0xFFFFFFFF : Word).toNat = 4294967295 := rfl
    rw [this]; omega
  · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact ra2
  · rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]
  · have kk := fun r (hr : shSrKeep r = false) => pkeep_ne hq hr
    have h0 : q.val ≠ 0 := fun e => absurd (show shSrKeep q = false by unfold shSrKeep; simp [e]) (by rw [hq]; decide)
    rw [u4.regs]; simp only [upd_app, h0, kk 8 rfl, kk a0 rfl, kk a3 rfl, kk a4 rfl, ite_false]
    exact k2 q (kk a2 rfl)


/-- The right shift's exit, from its head at `o` with no words left. -/
theorem sh_sr_exit {o : Nat} (at_ : SrAt o) {M : Word → BitVec 8} {P : Word} {n : Machine}
    (s : St M P n o (reg n)) (hc : CodeIn M P shr12Code) (r8 : reg n 8 = 0) :
    ∃ n', Steps n n' ∧ St M P n' (o + 0x16) (reg n') ∧ ∀ q, q ≠ a2 → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block _ s hc at_.hA (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  have k1 : ∀ q, q ≠ a2 → reg n1 q = reg n q := fun q h => by
    rw [u1.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s.zero.symm
    · exact upd_ne h0 h
  obtain ⟨n2, d2, u2⟩ := u1.self.taken hc (o + 0x16) at_.hQ at_.hT (by
    rw [k1 8 (by decide), r8, u1.self.zero]; rfl)
  exact ⟨n2, c1.trans (.single d2), u2.self, fun q h => by rw [u2.regs, k1 q h]⟩

/-- **The right shift**, from its head at `o` with `k` words left: the `nW`
words at `B` end as their value in `M0` shifted right `b` bits. -/
theorem sh_sr_loop {o : Nat} (at_ : SrAt o) {P B : Word} {M0 : Word → BitVec 8} {nW b : Nat}
    (hP : P.toNat % 2 = 0) (hb1 : 1 ≤ b) (hb2 : b ≤ 31) (hn : nW ≤ 12) (hB : B.toNat % 4 = 0)
    (hBw : B.toNat + 4 * nW ≤ 2 ^ 32) (sD : Sep B (4 * nW) P shr12Code.length) (hc0 : CodeIn M0 P shr12Code) :
    ∀ k, k ≤ nW → ∀ {M : Word → BitVec 8} {n : Machine} {C : Word},
      St M P n o (reg n) →
      (∀ x, Sep (B + BitVec.ofNat 32 (4 * k)) (4 * (nW - k)) x 1 → M x = M0 x) →
      C.toNat % 2 ^ (32 - b) = 0 →
      (accV M (B + BitVec.ofNat 32 (4 * k)) (nW - k) * 2 ^ b + C.toNat / 2 ^ (32 - b)) * 2 ^ (32 * k) +
        accV M0 B k = accV M0 B nW →
      reg n 8 = BitVec.ofNat 32 k → reg n a2 = B + BitVec.ofNat 32 (4 * k) → reg n a0 = C →
      reg n a1 = BitVec.ofNat 32 (32 - b) → reg n 9 = BitVec.ofNat 32 b →
      ∃ n' M', Steps n n' ∧ St M' P n' (o + 0x16) (reg n') ∧
        (∀ x, Sep B (4 * nW) x 1 → M' x = M0 x) ∧ accV M' B nW = accV M0 B nW / 2 ^ b ∧
        ∀ q, shSrKeep q = true → reg n' q = reg n q := by
  have htu := shPow_split (b := b) (by omega)
  have cIn : ∀ k, k ≤ nW → ∀ {M : Word → BitVec 8},
      (∀ x, Sep (B + BitVec.ofNat 32 (4 * k)) (4 * (nW - k)) x 1 → M x = M0 x) → CodeIn M P shr12Code :=
    fun k hk M hf i hi => by
      rw [hf _ ((sD.sub (c := 4 * k) (l := 4 * (nW - k)) (by omega)).subR (c := i) (l := 1) (by omega))]
      exact hc0 i hi
  intro k
  induction k with
  | zero =>
    intro _ M n C st hf hC hinv r8 r12 r10 r11 r9
    obtain ⟨n1, c1, u1, k1⟩ := sh_sr_exit at_ st (cIn 0 (Nat.zero_le _) hf) r8
    refine ⟨n1, M, c1, u1, fun x hx => hf x (by rwa [add_ofNat_zero, Nat.sub_zero]), ?_,
      fun q hq => k1 q (pkeep_ne hq rfl)⟩
    rw [add_ofNat_zero, Nat.sub_zero] at hinv
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, accV, Nat.add_zero] at hinv
    have hCu : C.toNat / 2 ^ (32 - b) < 2 ^ b := by
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm, htu]; exact C.isLt
    rw [← hinv, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos b), Nat.div_eq_of_lt hCu, Nat.add_zero]
  | succ k ih =>
    intro hk M n C st hf hC hinv r8 r12 r10 r11 r9
    have hc := cIn (k + 1) hk hf
    have sDk : Sep (B + BitVec.ofNat 32 (4 * k)) 4 P shr12Code.length := sD.sub (by omega)
    have sIn : ∀ x, Sep (B + BitVec.ofNat 32 (4 * k)) (4 * (nW - k)) x 1 →
        Sep (B + BitVec.ofNat 32 (4 * (k + 1))) (4 * (nW - (k + 1))) x 1 := fun x hx => by
      have := hx.sub (c := 4) (l := 4 * (nW - (k + 1))) (by omega)
      rwa [add_ofNat_assoc, show 4 * k + 4 = 4 * (k + 1) by omega] at this
    obtain ⟨n1, c1, u1, e8, e12, e10, fr⟩ := sh_sr_iter at_ hP st hc (by omega) (aligned_add hB (by omega)) sDk
      (by rw [r8]) r12 r10 r11 r9
    obtain ⟨x, hx⟩ : ∃ x, memLoad32 M (B + BitVec.ofNat 32 (4 * k)) = x := ⟨_, rfl⟩
    rw [hx] at u1 e10
    have hx0 : x = memLoad32 M0 (B + BitVec.ofNat 32 (4 * k)) := by
      rw [← hx]
      exact memLoad32_congr fun j hj => hf _ (by
        have := sep_offsets B (c := 4 * k + j) (n := 1) (d := 4 * (k + 1)) (k := 4 * (nW - (k + 1)))
          (.inl (by omega)) (by omega) (by omega)
        rw [add_ofNat_assoc]; exact this.symm)
    obtain ⟨y, hy⟩ : ∃ y, aluEval .or (aluEval .srl x (BitVec.ofNat 32 b)) C = y := ⟨_, rfl⟩
    rw [hy] at u1
    have hyv : y.toNat = x.toNat / 2 ^ b + C.toNat := by
      rw [← hy, or_nat' _ _ (i := 32 - b) (by rw [srl_nat _ _ (by rw [BitVec.toNat_ofNat]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2 ^ 32)]; exact srl_lt x (by omega)) hC,
        srl_nat _ _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2 ^ 32)]
    have hC' := sll_carry x (b := b) (by omega) (by omega)
    have hinv' : (accV (memStore32 M (B + BitVec.ofNat 32 (4 * k)) y) (B + BitVec.ofNat 32 (4 * k)) (nW - k) * 2 ^ b +
        (aluEval .sll x (BitVec.ofNat 32 (32 - b))).toNat / 2 ^ (32 - b)) * 2 ^ (32 * k) + accV M0 B k =
        accV M0 B nW := by
      rw [hC', Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      have hsplit := accV_split (memStore32 M (B + BitVec.ofNat 32 (4 * k)) y) (B + BitVec.ofNat 32 (4 * k)) 1
        (nW - (k + 1))
      rw [show 1 + (nW - (k + 1)) = nW - k by omega, add_ofNat_assoc, show 4 * k + 4 * 1 = 4 * (k + 1) by omega]
        at hsplit
      rw [hsplit]
      have h1 : accV (memStore32 M (B + BitVec.ofNat 32 (4 * k)) y) (B + BitVec.ofNat 32 (4 * k)) 1 = y.toNat := by
        simp only [accV, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, add_ofNat_zero,
          memLoad32_store32_same]
      have h2 : accV (memStore32 M (B + BitVec.ofNat 32 (4 * k)) y) (B + BitVec.ofNat 32 (4 * (k + 1)))
          (nW - (k + 1)) = accV M (B + BitVec.ofNat 32 (4 * (k + 1))) (nW - (k + 1)) := by
        refine accV_congr _ fun i hi => memLoad32_store32_sep ?_
        have := sep_offsets B (c := 4 * k) (n := 4) (d := 4 * (k + 1) + 4 * i) (k := 4)
          (.inl (by omega)) (by omega) (by omega)
        rwa [← add_ofNat_assoc] at this
      rw [h1, h2, hyv, show 32 * 1 = 32 by rfl]
      apply sr_step htu (A := C.toNat / 2 ^ (32 - b)) (by have := Nat.div_add_mod C.toNat (2 ^ (32 - b)); omega)
      rw [← hinv, accV_succ1, ← hx0, show 32 * (k + 1) = 32 + 32 * k by omega, Nat.pow_add]
    obtain ⟨n', M', c', u', hf', hv', fr'⟩ := ih (by omega) u1 (fun z hz => by
        rw [memStore32_get_sep (shSep0 (hz.sub (c := 0) (l := 4) (by omega)))]
        exact hf z (sIn z hz))
      (by rw [hC', Nat.mul_mod_left]) hinv' e8 e12 e10 (by rw [fr 11 rfl, r11]) (by rw [fr 9 rfl, r9])
    exact ⟨n', M', c1.trans c', u', hf', hv', fun q hq => by rw [fr' q hq, fr q hq]⟩

end C3.RV32
