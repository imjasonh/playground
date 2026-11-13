import C3BootProofs.Proofs.P384PtEnv

/-!
# Where the compiled P-384 point addition runs, and its calls

`primeorder`'s `add_assign` for P-384, as compiled, has the same shape as
the P-256 one in `PointEnv.lean`: it keeps 17 field elements in a 0x350-byte
frame and makes 46 calls, to `mul`, `add`, and `sub` on
`ConstMontyForm<p384::FieldParams, 12>`, `FieldElement::double`, and three
`memcpy`s that write the result into `lhs`. The multiplication needs the
most stack below the frame, 0xF0 bytes, so the stack it may change is the
0x440 bytes below `sp`, which this file calls `S`; the frame starts 0xF0
bytes into it.

`A3Inv` is what holds at each point between the calls, and the lemmas here
carry it across one call or one argument instruction, with the call's
result.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem p3pa_at_0 : fetchRel p384PtAddCode 0x0 = some (.aluImm .add sp sp 0xFFFFFCB0, 4) := by decide
theorem p3pa_at_4 : fetchRel p384PtAddCode 0x4 = some (.aluImm .add a2 sp 0x300, 2) := by decide
theorem p3pa_at_6 : fetchRel p384PtAddCode 0x6 = some (.store .sw a2 ra 0x4C, 4) := by decide
theorem p3pa_at_a : fetchRel p384PtAddCode 0xA = some (.store .sw a2 (8 : Fin 32) 0x48, 2) := by decide
theorem p3pa_at_c : fetchRel p384PtAddCode 0xC = some (.store .sw a2 (9 : Fin 32) 0x44, 2) := by decide
theorem p3pa_at_e : fetchRel p384PtAddCode 0xE = some (.store .sw a2 (18 : Fin 32) 0x40, 4) := by decide
theorem p3pa_at_12 : fetchRel p384PtAddCode 0x12 = some (.store .sw a2 (19 : Fin 32) 0x3C, 4) := by decide
theorem p3pa_at_16 : fetchRel p384PtAddCode 0x16 = some (.store .sw a2 (20 : Fin 32) 0x38, 4) := by decide
theorem p3pa_at_1a : fetchRel p384PtAddCode 0x1A = some (.store .sw a2 (21 : Fin 32) 0x34, 4) := by decide
theorem p3pa_at_1e : fetchRel p384PtAddCode 0x1E = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem p3pa_at_20 : fetchRel p384PtAddCode 0x20 = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem p3pa_at_22 : fetchRel p384PtAddCode 0x22 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem p3pa_at_24 : fetchRel p384PtAddCode 0x24 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem p3pa_at_26 : fetchRel p384PtAddCode 0x26 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem p3pa_at_28 : fetchRel p384PtAddCode 0x28 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_2c : fetchRel p384PtAddCode 0x2C = some (.jalr ra ra 0xFFFFF9FC, 4) := by decide
theorem p3pa_at_30 : fetchRel p384PtAddCode 0x30 = some (.aluImm .add (19 : Fin 32) (20 : Fin 32) 0x30, 4) := by decide
theorem p3pa_at_34 : fetchRel p384PtAddCode 0x34 = some (.aluImm .add (21 : Fin 32) (9 : Fin 32) 0x30, 4) := by decide
theorem p3pa_at_38 : fetchRel p384PtAddCode 0x38 = some (.aluImm .add a0 sp 0x184, 2) := by decide
theorem p3pa_at_3a : fetchRel p384PtAddCode 0x3A = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem p3pa_at_3c : fetchRel p384PtAddCode 0x3C = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem p3pa_at_3e : fetchRel p384PtAddCode 0x3E = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_42 : fetchRel p384PtAddCode 0x42 = some (.jalr ra ra 0xFFFFF9E6, 4) := by decide
theorem p3pa_at_46 : fetchRel p384PtAddCode 0x46 = some (.aluImm .add (18 : Fin 32) (20 : Fin 32) 0x60, 4) := by decide
theorem p3pa_at_4a : fetchRel p384PtAddCode 0x4A = some (.aluImm .add (8 : Fin 32) (9 : Fin 32) 0x60, 4) := by decide
theorem p3pa_at_4e : fetchRel p384PtAddCode 0x4E = some (.aluImm .add a0 sp 0x94, 2) := by decide
theorem p3pa_at_50 : fetchRel p384PtAddCode 0x50 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem p3pa_at_52 : fetchRel p384PtAddCode 0x52 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem p3pa_at_54 : fetchRel p384PtAddCode 0x54 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_58 : fetchRel p384PtAddCode 0x58 = some (.jalr ra ra 0xFFFFF9D0, 4) := by decide
theorem p3pa_at_5c : fetchRel p384PtAddCode 0x5C = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem p3pa_at_5e : fetchRel p384PtAddCode 0x5E = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem p3pa_at_60 : fetchRel p384PtAddCode 0x60 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem p3pa_at_62 : fetchRel p384PtAddCode 0x62 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_66 : fetchRel p384PtAddCode 0x66 = some (.jalr ra ra 0x27A, 4) := by decide
theorem p3pa_at_6a : fetchRel p384PtAddCode 0x6A = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_6c : fetchRel p384PtAddCode 0x6C = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem p3pa_at_6e : fetchRel p384PtAddCode 0x6E = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem p3pa_at_70 : fetchRel p384PtAddCode 0x70 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_74 : fetchRel p384PtAddCode 0x74 = some (.jalr ra ra 0x26C, 4) := by decide
theorem p3pa_at_78 : fetchRel p384PtAddCode 0x78 = some (.aluImm .add a0 sp 0xF4, 2) := by decide
theorem p3pa_at_7a : fetchRel p384PtAddCode 0x7A = some (.aluImm .add a1 sp 0x124, 2) := by decide
theorem p3pa_at_7c : fetchRel p384PtAddCode 0x7C = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_7e : fetchRel p384PtAddCode 0x7E = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_82 : fetchRel p384PtAddCode 0x82 = some (.jalr ra ra 0xFFFFF9A6, 4) := by decide
theorem p3pa_at_86 : fetchRel p384PtAddCode 0x86 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_88 : fetchRel p384PtAddCode 0x88 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem p3pa_at_8a : fetchRel p384PtAddCode 0x8A = some (.aluImm .add a2 sp 0x184, 2) := by decide
theorem p3pa_at_8c : fetchRel p384PtAddCode 0x8C = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_90 : fetchRel p384PtAddCode 0x90 = some (.jalr ra ra 0x250, 4) := by decide
theorem p3pa_at_94 : fetchRel p384PtAddCode 0x94 = some (.aluImm .add a0 sp 0x244, 2) := by decide
theorem p3pa_at_96 : fetchRel p384PtAddCode 0x96 = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem p3pa_at_98 : fetchRel p384PtAddCode 0x98 = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_9a : fetchRel p384PtAddCode 0x9A = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_9e : fetchRel p384PtAddCode 0x9E = some (.jalr ra ra 0x358, 4) := by decide
theorem p3pa_at_a2 : fetchRel p384PtAddCode 0xA2 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem p3pa_at_a4 : fetchRel p384PtAddCode 0xA4 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem p3pa_at_a6 : fetchRel p384PtAddCode 0xA6 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem p3pa_at_a8 : fetchRel p384PtAddCode 0xA8 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_ac : fetchRel p384PtAddCode 0xAC = some (.jalr ra ra 0x234, 4) := by decide
theorem p3pa_at_b0 : fetchRel p384PtAddCode 0xB0 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_b2 : fetchRel p384PtAddCode 0xB2 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem p3pa_at_b4 : fetchRel p384PtAddCode 0xB4 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem p3pa_at_b6 : fetchRel p384PtAddCode 0xB6 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_ba : fetchRel p384PtAddCode 0xBA = some (.jalr ra ra 0x226, 4) := by decide
theorem p3pa_at_be : fetchRel p384PtAddCode 0xBE = some (.aluImm .add a0 sp 0xF4, 2) := by decide
theorem p3pa_at_c0 : fetchRel p384PtAddCode 0xC0 = some (.aluImm .add a1 sp 0x124, 2) := by decide
theorem p3pa_at_c2 : fetchRel p384PtAddCode 0xC2 = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_c4 : fetchRel p384PtAddCode 0xC4 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_c8 : fetchRel p384PtAddCode 0xC8 = some (.jalr ra ra 0xFFFFF960, 4) := by decide
theorem p3pa_at_cc : fetchRel p384PtAddCode 0xCC = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_ce : fetchRel p384PtAddCode 0xCE = some (.aluImm .add a1 sp 0x184, 2) := by decide
theorem p3pa_at_d0 : fetchRel p384PtAddCode 0xD0 = some (.aluImm .add a2 sp 0x94, 2) := by decide
theorem p3pa_at_d2 : fetchRel p384PtAddCode 0xD2 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_d6 : fetchRel p384PtAddCode 0xD6 = some (.jalr ra ra 0x20A, 4) := by decide
theorem p3pa_at_da : fetchRel p384PtAddCode 0xDA = some (.aluImm .add a0 sp 0x274, 2) := by decide
theorem p3pa_at_dc : fetchRel p384PtAddCode 0xDC = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem p3pa_at_de : fetchRel p384PtAddCode 0xDE = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_e0 : fetchRel p384PtAddCode 0xE0 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_e4 : fetchRel p384PtAddCode 0xE4 = some (.jalr ra ra 0x312, 4) := by decide
theorem p3pa_at_e8 : fetchRel p384PtAddCode 0xE8 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem p3pa_at_ea : fetchRel p384PtAddCode 0xEA = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem p3pa_at_ec : fetchRel p384PtAddCode 0xEC = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem p3pa_at_ee : fetchRel p384PtAddCode 0xEE = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_f2 : fetchRel p384PtAddCode 0xF2 = some (.jalr ra ra 0x1EE, 4) := by decide
theorem p3pa_at_f6 : fetchRel p384PtAddCode 0xF6 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_f8 : fetchRel p384PtAddCode 0xF8 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem p3pa_at_fa : fetchRel p384PtAddCode 0xFA = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem p3pa_at_fc : fetchRel p384PtAddCode 0xFC = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_100 : fetchRel p384PtAddCode 0x100 = some (.jalr ra ra 0x1E0, 4) := by decide
theorem p3pa_at_104 : fetchRel p384PtAddCode 0x104 = some (.aluImm .add a0 sp 0xF4, 2) := by decide
theorem p3pa_at_106 : fetchRel p384PtAddCode 0x106 = some (.aluImm .add a1 sp 0x124, 2) := by decide
theorem p3pa_at_108 : fetchRel p384PtAddCode 0x108 = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_10a : fetchRel p384PtAddCode 0x10A = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_10e : fetchRel p384PtAddCode 0x10E = some (.jalr ra ra 0xFFFFF91A, 4) := by decide
theorem p3pa_at_112 : fetchRel p384PtAddCode 0x112 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_114 : fetchRel p384PtAddCode 0x114 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem p3pa_at_116 : fetchRel p384PtAddCode 0x116 = some (.aluImm .add a2 sp 0x94, 2) := by decide
theorem p3pa_at_118 : fetchRel p384PtAddCode 0x118 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_11c : fetchRel p384PtAddCode 0x11C = some (.jalr ra ra 0x1C4, 4) := by decide
theorem p3pa_at_120 : fetchRel p384PtAddCode 0x120 = some (.aluImm .add a0 sp 0x34, 2) := by decide
theorem p3pa_at_122 : fetchRel p384PtAddCode 0x122 = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem p3pa_at_124 : fetchRel p384PtAddCode 0x124 = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_126 : fetchRel p384PtAddCode 0x126 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_12a : fetchRel p384PtAddCode 0x12A = some (.jalr ra ra 0x2CC, 4) := by decide
theorem p3pa_at_12e : fetchRel p384PtAddCode 0x12E = some (.lui (8 : Fin 32) 0x3FCC4000, 4) := by decide
theorem p3pa_at_132 : fetchRel p384PtAddCode 0x132 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x234, 4) := by decide
theorem p3pa_at_136 : fetchRel p384PtAddCode 0x136 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_138 : fetchRel p384PtAddCode 0x138 = some (.aluImm .add a2 sp 0x94, 2) := by decide
theorem p3pa_at_13a : fetchRel p384PtAddCode 0x13A = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem p3pa_at_13c : fetchRel p384PtAddCode 0x13C = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_140 : fetchRel p384PtAddCode 0x140 = some (.jalr ra ra 0xFFFFF8E8, 4) := by decide
theorem p3pa_at_144 : fetchRel p384PtAddCode 0x144 = some (.aluImm .add a0 sp 0x64, 2) := by decide
theorem p3pa_at_146 : fetchRel p384PtAddCode 0x146 = some (.aluImm .add a1 sp 0x34, 2) := by decide
theorem p3pa_at_148 : fetchRel p384PtAddCode 0x148 = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_14a : fetchRel p384PtAddCode 0x14A = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_14e : fetchRel p384PtAddCode 0x14E = some (.jalr ra ra 0x2A8, 4) := by decide
theorem p3pa_at_152 : fetchRel p384PtAddCode 0x152 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_154 : fetchRel p384PtAddCode 0x154 = some (.aluImm .add a1 sp 0x64, 2) := by decide
theorem p3pa_at_156 : fetchRel p384PtAddCode 0x156 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_15a : fetchRel p384PtAddCode 0x15A = some (.jalr ra ra 0xFFFFFFAA, 4) := by decide
theorem p3pa_at_15e : fetchRel p384PtAddCode 0x15E = some (.aluImm .add a0 sp 0x1B4, 2) := by decide
theorem p3pa_at_160 : fetchRel p384PtAddCode 0x160 = some (.aluImm .add a1 sp 0x154, 2) := by decide
theorem p3pa_at_162 : fetchRel p384PtAddCode 0x162 = some (.aluImm .add a2 sp 0x64, 2) := by decide
theorem p3pa_at_164 : fetchRel p384PtAddCode 0x164 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_168 : fetchRel p384PtAddCode 0x168 = some (.jalr ra ra 0x178, 4) := by decide
theorem p3pa_at_16c : fetchRel p384PtAddCode 0x16C = some (.aluImm .add a0 sp 0x2D4, 2) := by decide
theorem p3pa_at_16e : fetchRel p384PtAddCode 0x16E = some (.aluImm .add a1 sp 0x184, 2) := by decide
theorem p3pa_at_170 : fetchRel p384PtAddCode 0x170 = some (.aluImm .add a2 sp 0x1B4, 2) := by decide
theorem p3pa_at_172 : fetchRel p384PtAddCode 0x172 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_176 : fetchRel p384PtAddCode 0x176 = some (.jalr ra ra 0x280, 4) := by decide
theorem p3pa_at_17a : fetchRel p384PtAddCode 0x17A = some (.aluImm .add a0 sp 0x214, 2) := by decide
theorem p3pa_at_17c : fetchRel p384PtAddCode 0x17C = some (.aluImm .add a1 sp 0x184, 2) := by decide
theorem p3pa_at_17e : fetchRel p384PtAddCode 0x17E = some (.aluImm .add a2 sp 0x1B4, 2) := by decide
theorem p3pa_at_180 : fetchRel p384PtAddCode 0x180 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_184 : fetchRel p384PtAddCode 0x184 = some (.jalr ra ra 0x15C, 4) := by decide
theorem p3pa_at_188 : fetchRel p384PtAddCode 0x188 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_18a : fetchRel p384PtAddCode 0x18A = some (.aluImm .add a1 sp 0x94, 2) := by decide
theorem p3pa_at_18c : fetchRel p384PtAddCode 0x18C = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_190 : fetchRel p384PtAddCode 0x190 = some (.jalr ra ra 0xFFFFFF74, 4) := by decide
theorem p3pa_at_194 : fetchRel p384PtAddCode 0x194 = some (.aluImm .add a0 sp 0x1E4, 2) := by decide
theorem p3pa_at_196 : fetchRel p384PtAddCode 0x196 = some (.aluImm .add a1 sp 0x154, 2) := by decide
theorem p3pa_at_198 : fetchRel p384PtAddCode 0x198 = some (.aluImm .add a2 sp 0x94, 2) := by decide
theorem p3pa_at_19a : fetchRel p384PtAddCode 0x19A = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_19e : fetchRel p384PtAddCode 0x19E = some (.jalr ra ra 0x142, 4) := by decide
theorem p3pa_at_1a2 : fetchRel p384PtAddCode 0x1A2 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem p3pa_at_1a4 : fetchRel p384PtAddCode 0x1A4 = some (.aluImm .add a2 sp 0x34, 2) := by decide
theorem p3pa_at_1a6 : fetchRel p384PtAddCode 0x1A6 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem p3pa_at_1a8 : fetchRel p384PtAddCode 0x1A8 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_1ac : fetchRel p384PtAddCode 0x1AC = some (.jalr ra ra 0xFFFFF87C, 4) := by decide
theorem p3pa_at_1b0 : fetchRel p384PtAddCode 0x1B0 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_1b2 : fetchRel p384PtAddCode 0x1B2 = some (.aluImm .add a1 sp 0x1E4, 2) := by decide
theorem p3pa_at_1b4 : fetchRel p384PtAddCode 0x1B4 = some (.aluImm .add a2 sp 0x4, 2) := by decide
theorem p3pa_at_1b6 : fetchRel p384PtAddCode 0x1B6 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_1ba : fetchRel p384PtAddCode 0x1BA = some (.jalr ra ra 0x126, 4) := by decide
theorem p3pa_at_1be : fetchRel p384PtAddCode 0x1BE = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem p3pa_at_1c0 : fetchRel p384PtAddCode 0x1C0 = some (.aluImm .add a1 sp 0x124, 2) := by decide
theorem p3pa_at_1c2 : fetchRel p384PtAddCode 0x1C2 = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_1c4 : fetchRel p384PtAddCode 0x1C4 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_1c8 : fetchRel p384PtAddCode 0x1C8 = some (.jalr ra ra 0x22E, 4) := by decide
theorem p3pa_at_1cc : fetchRel p384PtAddCode 0x1CC = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_1ce : fetchRel p384PtAddCode 0x1CE = some (.aluImm .add a1 sp 0xC4, 2) := by decide
theorem p3pa_at_1d0 : fetchRel p384PtAddCode 0x1D0 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_1d4 : fetchRel p384PtAddCode 0x1D4 = some (.jalr ra ra 0xFFFFFF30, 4) := by decide
theorem p3pa_at_1d8 : fetchRel p384PtAddCode 0x1D8 = some (.aluImm .add a0 sp 0x2A4, 2) := by decide
theorem p3pa_at_1da : fetchRel p384PtAddCode 0x1DA = some (.aluImm .add a1 sp 0x154, 2) := by decide
theorem p3pa_at_1dc : fetchRel p384PtAddCode 0x1DC = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem p3pa_at_1de : fetchRel p384PtAddCode 0x1DE = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_1e2 : fetchRel p384PtAddCode 0x1E2 = some (.jalr ra ra 0xFE, 4) := by decide
theorem p3pa_at_1e6 : fetchRel p384PtAddCode 0x1E6 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_1e8 : fetchRel p384PtAddCode 0x1E8 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem p3pa_at_1ea : fetchRel p384PtAddCode 0x1EA = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_1ee : fetchRel p384PtAddCode 0x1EE = some (.jalr ra ra 0xFFFFFF16, 4) := by decide
theorem p3pa_at_1f2 : fetchRel p384PtAddCode 0x1F2 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem p3pa_at_1f4 : fetchRel p384PtAddCode 0x1F4 = some (.aluImm .add a1 sp 0x154, 2) := by decide
theorem p3pa_at_1f6 : fetchRel p384PtAddCode 0x1F6 = some (.aluImm .add a2 sp 0x4, 2) := by decide
theorem p3pa_at_1f8 : fetchRel p384PtAddCode 0x1F8 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_1fc : fetchRel p384PtAddCode 0x1FC = some (.jalr ra ra 0xE4, 4) := by decide
theorem p3pa_at_200 : fetchRel p384PtAddCode 0x200 = some (.aluImm .add a0 sp 0x304, 2) := by decide
theorem p3pa_at_202 : fetchRel p384PtAddCode 0x202 = some (.aluImm .add a1 sp 0x124, 2) := by decide
theorem p3pa_at_204 : fetchRel p384PtAddCode 0x204 = some (.aluImm .add a2 sp 0x1E4, 2) := by decide
theorem p3pa_at_206 : fetchRel p384PtAddCode 0x206 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_20a : fetchRel p384PtAddCode 0x20A = some (.jalr ra ra 0x1EC, 4) := by decide
theorem p3pa_at_20e : fetchRel p384PtAddCode 0x20E = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem p3pa_at_210 : fetchRel p384PtAddCode 0x210 = some (.aluImm .add a1 sp 0x214, 2) := by decide
theorem p3pa_at_212 : fetchRel p384PtAddCode 0x212 = some (.aluImm .add a2 sp 0x244, 2) := by decide
theorem p3pa_at_214 : fetchRel p384PtAddCode 0x214 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_218 : fetchRel p384PtAddCode 0x218 = some (.jalr ra ra 0xFFFFF810, 4) := by decide
theorem p3pa_at_21c : fetchRel p384PtAddCode 0x21C = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_21e : fetchRel p384PtAddCode 0x21E = some (.aluImm .add a1 sp 0x274, 2) := by decide
theorem p3pa_at_220 : fetchRel p384PtAddCode 0x220 = some (.aluImm .add a2 sp 0x2A4, 2) := by decide
theorem p3pa_at_222 : fetchRel p384PtAddCode 0x222 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_226 : fetchRel p384PtAddCode 0x226 = some (.jalr ra ra 0xFFFFF802, 4) := by decide
theorem p3pa_at_22a : fetchRel p384PtAddCode 0x22A = some (.aluImm .add a0 sp 0xF4, 2) := by decide
theorem p3pa_at_22c : fetchRel p384PtAddCode 0x22C = some (.aluImm .add a1 sp 0x124, 2) := by decide
theorem p3pa_at_22e : fetchRel p384PtAddCode 0x22E = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_230 : fetchRel p384PtAddCode 0x230 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_234 : fetchRel p384PtAddCode 0x234 = some (.jalr ra ra 0x1C2, 4) := by decide
theorem p3pa_at_238 : fetchRel p384PtAddCode 0x238 = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem p3pa_at_23a : fetchRel p384PtAddCode 0x23A = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem p3pa_at_23e : fetchRel p384PtAddCode 0x23E = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem p3pa_at_240 : fetchRel p384PtAddCode 0x240 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_244 : fetchRel p384PtAddCode 0x244 = some (.jalr ra ra 0x7B6, 4) := by decide
theorem p3pa_at_248 : fetchRel p384PtAddCode 0x248 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem p3pa_at_24a : fetchRel p384PtAddCode 0x24A = some (.aluImm .add a1 sp 0x214, 2) := by decide
theorem p3pa_at_24c : fetchRel p384PtAddCode 0x24C = some (.aluImm .add a2 sp 0x2D4, 2) := by decide
theorem p3pa_at_24e : fetchRel p384PtAddCode 0x24E = some (.auipc ra 0x11000, 4) := by decide
theorem p3pa_at_252 : fetchRel p384PtAddCode 0x252 = some (.jalr ra ra 0x7D6, 4) := by decide
theorem p3pa_at_256 : fetchRel p384PtAddCode 0x256 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_258 : fetchRel p384PtAddCode 0x258 = some (.aluImm .add a1 sp 0x304, 2) := by decide
theorem p3pa_at_25a : fetchRel p384PtAddCode 0x25A = some (.aluImm .add a2 sp 0x2A4, 2) := by decide
theorem p3pa_at_25c : fetchRel p384PtAddCode 0x25C = some (.auipc ra 0x11000, 4) := by decide
theorem p3pa_at_260 : fetchRel p384PtAddCode 0x260 = some (.jalr ra ra 0x7C8, 4) := by decide
theorem p3pa_at_264 : fetchRel p384PtAddCode 0x264 = some (.aluImm .add a0 sp 0xF4, 2) := by decide
theorem p3pa_at_266 : fetchRel p384PtAddCode 0x266 = some (.aluImm .add a1 sp 0x124, 2) := by decide
theorem p3pa_at_268 : fetchRel p384PtAddCode 0x268 = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_26a : fetchRel p384PtAddCode 0x26A = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_26e : fetchRel p384PtAddCode 0x26E = some (.jalr ra ra 0x72, 4) := by decide
theorem p3pa_at_272 : fetchRel p384PtAddCode 0x272 = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem p3pa_at_274 : fetchRel p384PtAddCode 0x274 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem p3pa_at_278 : fetchRel p384PtAddCode 0x278 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem p3pa_at_27a : fetchRel p384PtAddCode 0x27A = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_27e : fetchRel p384PtAddCode 0x27E = some (.jalr ra ra 0x77C, 4) := by decide
theorem p3pa_at_282 : fetchRel p384PtAddCode 0x282 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem p3pa_at_284 : fetchRel p384PtAddCode 0x284 = some (.aluImm .add a1 sp 0x2D4, 2) := by decide
theorem p3pa_at_286 : fetchRel p384PtAddCode 0x286 = some (.aluImm .add a2 sp 0x274, 2) := by decide
theorem p3pa_at_288 : fetchRel p384PtAddCode 0x288 = some (.auipc ra 0x11000, 4) := by decide
theorem p3pa_at_28c : fetchRel p384PtAddCode 0x28C = some (.jalr ra ra 0x79C, 4) := by decide
theorem p3pa_at_290 : fetchRel p384PtAddCode 0x290 = some (.aluImm .add a0 sp 0x154, 2) := by decide
theorem p3pa_at_292 : fetchRel p384PtAddCode 0x292 = some (.aluImm .add a1 sp 0x244, 2) := by decide
theorem p3pa_at_294 : fetchRel p384PtAddCode 0x294 = some (.aluImm .add a2 sp 0x304, 2) := by decide
theorem p3pa_at_296 : fetchRel p384PtAddCode 0x296 = some (.auipc ra 0x11000, 4) := by decide
theorem p3pa_at_29a : fetchRel p384PtAddCode 0x29A = some (.jalr ra ra 0x78E, 4) := by decide
theorem p3pa_at_29e : fetchRel p384PtAddCode 0x29E = some (.aluImm .add a0 sp 0xF4, 2) := by decide
theorem p3pa_at_2a0 : fetchRel p384PtAddCode 0x2A0 = some (.aluImm .add a1 sp 0x124, 2) := by decide
theorem p3pa_at_2a2 : fetchRel p384PtAddCode 0x2A2 = some (.aluImm .add a2 sp 0x154, 2) := by decide
theorem p3pa_at_2a4 : fetchRel p384PtAddCode 0x2A4 = some (.auipc ra 0x0, 4) := by decide
theorem p3pa_at_2a8 : fetchRel p384PtAddCode 0x2A8 = some (.jalr ra ra 0x38, 4) := by decide
theorem p3pa_at_2ac : fetchRel p384PtAddCode 0x2AC = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem p3pa_at_2ae : fetchRel p384PtAddCode 0x2AE = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem p3pa_at_2b2 : fetchRel p384PtAddCode 0x2B2 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem p3pa_at_2b4 : fetchRel p384PtAddCode 0x2B4 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pa_at_2b8 : fetchRel p384PtAddCode 0x2B8 = some (.jalr ra ra 0x742, 4) := by decide
theorem p3pa_at_2bc : fetchRel p384PtAddCode 0x2BC = some (.aluImm .add a0 sp 0x300, 2) := by decide
theorem p3pa_at_2be : fetchRel p384PtAddCode 0x2BE = some (.load .lw ra a0 0x4C, 4) := by decide
theorem p3pa_at_2c2 : fetchRel p384PtAddCode 0x2C2 = some (.load .lw (8 : Fin 32) a0 0x48, 2) := by decide
theorem p3pa_at_2c4 : fetchRel p384PtAddCode 0x2C4 = some (.load .lw (9 : Fin 32) a0 0x44, 2) := by decide
theorem p3pa_at_2c6 : fetchRel p384PtAddCode 0x2C6 = some (.load .lw (18 : Fin 32) a0 0x40, 4) := by decide
theorem p3pa_at_2ca : fetchRel p384PtAddCode 0x2CA = some (.load .lw (19 : Fin 32) a0 0x3C, 4) := by decide
theorem p3pa_at_2ce : fetchRel p384PtAddCode 0x2CE = some (.load .lw (20 : Fin 32) a0 0x38, 4) := by decide
theorem p3pa_at_2d2 : fetchRel p384PtAddCode 0x2D2 = some (.load .lw (21 : Fin 32) a0 0x34, 4) := by decide
theorem p3pa_at_2d6 : fetchRel p384PtAddCode 0x2D6 = some (.aluImm .add sp sp 0x350, 4) := by decide
theorem p3pa_at_2da : fetchRel p384PtAddCode 0x2DA = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The bottom of the stack the point addition may change. -/
abbrev a3S (sp0 : Word) : Word := sp0 + 0xFFFFFBC0

/-- The point addition's frame. -/
abbrev a3G (sp0 : Word) : Word := sp0 + 0xFFFFFCB0

/-- Where the point addition runs: its code at `P`, its callees and theirs
where the image puts them, the modulus and `b`, `lhs` (the first point and
the result) and `rhs` (the second point), each 144 bytes and aligned, and
the 0x440 bytes of stack below `sp0` apart from the code, the constants, and
both points. The result's writes keep `lhs` apart from the code and the
constants too. -/
structure A3Env (M : Word → BitVec 8) (P sp0 lhs rhs : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384PtAddCode
  mulw : CodeIn M (P + 0x11A24) p384MulCode
  mm : CodeIn M (P + 0x10E82) mulMont12Code
  add : CodeIn M (P + 0x2DC) p384AddCode
  sub : CodeIn M (P + 0x3F2) p384SubCode
  dbl : CodeIn M (P + 0x12100) p384DoubleCode
  mset : CodeIn M (P + 0x1298E) memsetCode
  bsub : CodeIn M (P + 0x4C8) borrowingSubCode
  sel : CodeIn M (P + 0x11010) uintSelect12Code
  stub : CodeIn M (P + 0x129F6) memcpyStubCode
  body : CodeIn M (P + 0x129FE) memcpyBodyCode
  pmod : CodeIn M p3M p384ModulusData
  bconst : CodeIn M p3bA p384BData
  hsp : sp0.toNat % 4 = 0
  hS : 0x440 ≤ sp0.toNat
  hl : lhs.toNat % 4 = 0
  hr : rhs.toNat % 4 = 0
  hwl : lhs.toNat + 144 < 2 ^ 32
  sC : Sep (a3S sp0) 0x440 P p384PtAddCode.length
  sMw : Sep (a3S sp0) 0x440 (P + 0x11A24) p384MulCode.length
  sMm : Sep (a3S sp0) 0x440 (P + 0x10E82) mulMont12Code.length
  sA : Sep (a3S sp0) 0x440 (P + 0x2DC) p384AddCode.length
  sSb : Sep (a3S sp0) 0x440 (P + 0x3F2) p384SubCode.length
  sD : Sep (a3S sp0) 0x440 (P + 0x12100) p384DoubleCode.length
  sMs : Sep (a3S sp0) 0x440 (P + 0x1298E) memsetCode.length
  sBs : Sep (a3S sp0) 0x440 (P + 0x4C8) borrowingSubCode.length
  sSel : Sep (a3S sp0) 0x440 (P + 0x11010) uintSelect12Code.length
  sU : Sep (a3S sp0) 0x440 (P + 0x129F6) memcpyStubCode.length
  sB : Sep (a3S sp0) 0x440 (P + 0x129FE) memcpyBodyCode.length
  sP : Sep (a3S sp0) 0x440 p3M 48
  sK : Sep (a3S sp0) 0x440 p3bA 48
  sL : Sep lhs 144 (a3S sp0) 0x440
  sR : Sep rhs 144 (a3S sp0) 0x440
  lC : Sep lhs 144 P p384PtAddCode.length
  lMw : Sep lhs 144 (P + 0x11A24) p384MulCode.length
  lMm : Sep lhs 144 (P + 0x10E82) mulMont12Code.length
  lA : Sep lhs 144 (P + 0x2DC) p384AddCode.length
  lSb : Sep lhs 144 (P + 0x3F2) p384SubCode.length
  lD : Sep lhs 144 (P + 0x12100) p384DoubleCode.length
  lMs : Sep lhs 144 (P + 0x1298E) memsetCode.length
  lBs : Sep lhs 144 (P + 0x4C8) borrowingSubCode.length
  lSel : Sep lhs 144 (P + 0x11010) uintSelect12Code.length
  lU : Sep lhs 144 (P + 0x129F6) memcpyStubCode.length
  lB : Sep lhs 144 (P + 0x129FE) memcpyBodyCode.length
  lP : Sep lhs 144 p3M 48
  lK : Sep lhs 144 p3bA 48

/-- What holds between the point addition's calls, at offset `off`: the
registers `d3Keep` names hold `V`, memory outside `S` and the first `W`
bytes of `lhs` is as it was on entry (`M0`), and the register save slots at
the frame's top hold what they held after the prologue (`Ms`). -/
structure A3Inv (M0 : Word → BitVec 8) (P sp0 lhs : Word) (V : Fin 32 → Word) (Ms : Word → BitVec 8)
    (W : Nat) (M : Word → BitVec 8) (n : Machine) (off : Nat) : Prop where
  st : St M P n off (reg n)
  keep : ∀ q, d3Keep q = true → reg n q = V q
  fr : ∀ x, Sep (a3S sp0) 0x440 x 1 → Sep lhs W x 1 → M x = M0 x
  sv : ∀ c, 0x334 ≤ c → c < 0x350 → M (a3G sp0 + BitVec.ofNat 32 c) = Ms (a3G sp0 + BitVec.ofNat 32 c)

/-- An operand a call may read: aligned, and apart from the callees' stack. -/
def A3Src (sp0 a : Word) : Prop := a.toNat % 4 = 0 ∧ Sep a 48 (a3S sp0) 0xF0

/-- A result slot in the frame: the 48 bytes at `d`, below the save slots. -/
def A3Dst (d : Nat) : Prop := 4 ≤ d ∧ d + 48 ≤ 0x334 ∧ d % 4 = 0

theorem a3G_S (sp0 : Word) (c : Nat) : a3G sp0 + BitVec.ofNat 32 c = a3S sp0 + BitVec.ofNat 32 (0xF0 + c) := by
  rw [← add_ofNat_assoc, show a3G sp0 = a3S sp0 + BitVec.ofNat 32 0xF0 from by
    show sp0 + 0xFFFFFCB0 = sp0 + 0xFFFFFBC0 + BitVec.ofNat 32 0xF0
    rw [BitVec.add_assoc]; rfl]

theorem a3G_mm (sp0 : Word) : a3G sp0 + 0xFFFFFF10 = a3S sp0 := by
  show sp0 + 0xFFFFFCB0 + 0xFFFFFF10 = sp0 + 0xFFFFFBC0
  rw [BitVec.add_assoc]; rfl

theorem a3G_ad (sp0 : Word) : a3G sp0 + 0xFFFFFF4C = a3S sp0 + BitVec.ofNat 32 0x3C := by
  show sp0 + 0xFFFFFCB0 + 0xFFFFFF4C = sp0 + 0xFFFFFBC0 + BitVec.ofNat 32 0x3C
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem a3G_db (sp0 : Word) : a3G sp0 + 0xFFFFFF30 = a3S sp0 + BitVec.ofNat 32 0x20 := by
  show sp0 + 0xFFFFFCB0 + 0xFFFFFF30 = sp0 + 0xFFFFFBC0 + BitVec.ofNat 32 0x20
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

section
variable {M0 : Word → BitVec 8} {P sp0 lhs rhs : Word}

theorem A3Env.hGw (env : A3Env M0 P sp0 lhs rhs) : (a3G sp0).toNat = sp0.toNat - 0x350 := by
  have := env.hS
  show (sp0 + 0xFFFFFCB0).toNat = _
  rw [BitVec.toNat_add]; have : (0xFFFFFCB0 : Word).toNat = 4294966448 := rfl
  have := sp0.isLt; omega

theorem A3Env.hGa (env : A3Env M0 P sp0 lhs rhs) : (a3G sp0).toNat % 4 = 0 :=
  aligned_add env.hsp (k := 0xFFFFFCB0) (by decide)

/-- Code apart from `S` and `lhs` is still there. -/
theorem A3Env.codeT (_env : A3Env M0 P sp0 lhs rhs) {M : Word → BitVec 8} {W : Nat}
    (fr : ∀ x, Sep (a3S sp0) 0x440 x 1 → Sep lhs W x 1 → M x = M0 x) (hW : W ≤ 144)
    {b : Word} {code : List Nat} (hc : CodeIn M0 b code) (hs : Sep (a3S sp0) 0x440 b code.length)
    (hl : Sep lhs 144 b code.length) : CodeIn M b code := fun i hi => by
  rw [fr _ (hs.subR (c := i) (l := 1) (by omega))
    ((sep_base0 (hl.sub (c := 0) (l := W) (by omega))).subR (c := i) (l := 1) (by omega))]
  exact hc i hi

theorem aS_mm {b : Word} {k : Nat} (h : Sep (a3S sp0) 0x440 b k) : Sep (a3G sp0 + 0xFFFFFF10) 0xF0 b k := by
  rw [a3G_mm]; exact sep_base0 (h.sub (c := 0) (l := 0xF0) (by decide))

theorem aS_ad {b : Word} {k : Nat} (h : Sep (a3S sp0) 0x440 b k) : Sep (a3G sp0 + 0xFFFFFF4C) 0xB4 b k := by
  rw [a3G_ad]; exact h.sub (c := 0x3C) (l := 0xB4) (by decide)

theorem aS_db {b : Word} {k : Nat} (h : Sep (a3S sp0) 0x440 b k) : Sep (a3G sp0 + 0xFFFFFF30) 0xD0 b k := by
  rw [a3G_db]; exact h.sub (c := 0x20) (l := 0xD0) (by decide)

theorem A3Dst.al {d : Nat} (env : A3Env M0 P sp0 lhs rhs) (hd : A3Dst d) :
    (a3G sp0 + BitVec.ofNat 32 d).toNat % 4 = 0 := aligned_add env.hGa hd.2.2

theorem A3Dst.wr {d : Nat} (env : A3Env M0 P sp0 lhs rhs) (hd : A3Dst d) :
    (a3G sp0 + BitVec.ofNat 32 d).toNat + 48 < 2 ^ 32 := by
  have := env.hGw; have := env.hS; have := sp0.isLt; have := hd.2.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A result slot is apart from the callees' stack. -/
theorem A3Dst.sS {d : Nat} (hd : A3Dst d) : Sep (a3G sp0 + BitVec.ofNat 32 d) 48 (a3S sp0) 0xF0 := by
  rw [a3G_S]
  exact sep_base0r (sep_offsets _ (c := 0xF0 + d) (n := 48) (d := 0) (k := 0xF0) (.inr (by omega))
    (by have := hd.2.1; omega) (by decide))

theorem A3Dst.inS {d : Nat} (hd : A3Dst d) {b : Word} {k : Nat} (h : Sep (a3S sp0) 0x440 b k) :
    Sep (a3G sp0 + BitVec.ofNat 32 d) 48 b k := by
  rw [a3G_S]; exact h.sub (c := 0xF0 + d) (l := 48) (by have := hd.2.1; omega)

/-- A frame slot below the save slots is an operand. -/
theorem a3src_slot {d : Nat} (env : A3Env M0 P sp0 lhs rhs) (hd : A3Dst d) :
    A3Src sp0 (a3G sp0 + BitVec.ofNat 32 d) := ⟨hd.al env, hd.sS⟩

/-- A coordinate of `lhs` is an operand. -/
theorem a3src_lhs (env : A3Env M0 P sp0 lhs rhs) (k : Nat) (hk : k + 48 ≤ 144) (hk4 : k % 4 = 0) :
    A3Src sp0 (lhs + BitVec.ofNat 32 k) :=
  ⟨aligned_add env.hl hk4, sep_base0r ((env.sL.sub (c := k) (l := 48) hk).subR (c := 0) (l := 0xF0) (by decide))⟩

/-- A coordinate of `rhs` is an operand. -/
theorem a3src_rhs (env : A3Env M0 P sp0 lhs rhs) (k : Nat) (hk : k + 48 ≤ 144) (hk4 : k % 4 = 0) :
    A3Src sp0 (rhs + BitVec.ofNat 32 k) :=
  ⟨aligned_add env.hr hk4, sep_base0r ((env.sR.sub (c := k) (l := 48) hk).subR (c := 0) (l := 0xF0) (by decide))⟩

/-- `b` is an operand. -/
theorem a3src_b (env : A3Env M0 P sp0 lhs rhs) : A3Src sp0 p3bA :=
  ⟨by decide, sep_base0r (env.sK.symm.subR (c := 0) (l := 0xF0) (by decide))⟩

theorem A3Src.sub' {a : Word} (h : A3Src sp0 a) : Sep a 48 (a3G sp0 + 0xFFFFFF10) 0xF0 := by
  rw [a3G_mm]; exact h.2

theorem A3Src.ad {a : Word} (h : A3Src sp0 a) : Sep a 48 (a3G sp0 + 0xFFFFFF4C) 0xB4 := by
  rw [a3G_ad]; exact h.2.subR (c := 0x3C) (l := 0xB4) (by decide)

theorem A3Src.db {a : Word} (h : A3Src sp0 a) : Sep a 48 (a3G sp0 + 0xFFFFFF30) 0xD0 := by
  rw [a3G_db]; exact h.2.subR (c := 0x20) (l := 0xD0) (by decide)

theorem a3_ret_even (env : A3Env M0 P sp0 lhs rhs) {off : Nat} (hoff : off % 2 = 0) :
    (P + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = P + BitVec.ofNat 32 (off + 8) :=
  even_clear _ (even_at P env.hP (off + 8) (by omega))

theorem a3_hS (env : A3Env M0 P sp0 lhs rhs) : 0xF0 ≤ (a3G sp0).toNat := by
  have := env.hGw; have := env.hS; omega

/-- The multiplication wrapper's environment, for a call from the point
addition with its result in the frame. -/
theorem A3Env.mEnv (env : A3Env M0 P sp0 lhs rhs) {M : Word → BitVec 8} {W : Nat}
    (fr : ∀ x, Sep (a3S sp0) 0x440 x 1 → Sep lhs W x 1 → M x = M0 x) (hW : W ≤ 144) {d : Nat} {a b : Word}
    (hd : A3Dst d) (sa : A3Src sp0 a) (sb : A3Src sp0 b) :
    P3MEnv M (P + 0x11A24) (a3G sp0) (a3G sp0 + BitVec.ofNat 32 d) a b := by
  have cT := @A3Env.codeT _ _ _ _ _ env M W fr hW
  have e0 : P + 0x11A24 + 0xFFFFF45E = P + 0x10E82 := by rw [BitVec.add_assoc]; rfl
  have e1 : P + 0x10E82 + 0x1B0C = P + 0x1298E := by rw [BitVec.add_assoc]; rfl
  have e2 : mmBsub (P + 0x10E82) = P + 0x4C8 := by show P + 0x10E82 + 0xFFFEF646 = _; rw [BitVec.add_assoc]; rfl
  have e3 : P + 0x10E82 + 0x18E = P + 0x11010 := by rw [BitVec.add_assoc]; rfl
  have e4 : P + 0x10E82 + 0x1B74 = P + 0x129F6 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0x10E82 + 0x1B7C = P + 0x129FE := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0x11A24 (by decide), cT env.mulw env.sMw env.lMw, cT env.pmod env.sP env.lP, ?_⟩
  rw [e0]
  refine ⟨even_at P env.hP 0x10E82 (by decide), cT env.mm env.sMm env.lMm,
    by rw [e1]; exact cT env.mset env.sMs env.lMs,
    by rw [e2]; exact cT env.bsub env.sBs env.lBs, by rw [e3]; exact cT env.sel env.sSel env.lSel,
    by rw [e4]; exact cT env.stub env.sU env.lU, by rw [e5]; exact cT env.body env.sB env.lB,
    env.hGa, a3_hS env, hd.al env, sa.1, sb.1, by decide, hd.wr env,
    aS_mm env.sMm, by rw [e1]; exact aS_mm env.sMs, by rw [e2]; exact aS_mm env.sBs,
    by rw [e3]; exact aS_mm env.sSel, by rw [e4]; exact aS_mm env.sU, by rw [e5]; exact aS_mm env.sB,
    by rw [a3G_mm]; exact hd.sS, hd.inS env.sMm, by rw [e3]; exact hd.inS env.sSel,
    by rw [e5]; exact hd.inS env.sB, sa.sub', sb.sub', ?_⟩
  rw [a3G_mm]; exact sep_base0r (env.sP.symm.subR (c := 0) (l := 0xF0) (by decide))

theorem a3_hS_ad (env : A3Env M0 P sp0 lhs rhs) : 0xB4 ≤ (a3G sp0).toNat := by
  have := env.hGw; have := env.hS; omega

theorem a3_hS_db (env : A3Env M0 P sp0 lhs rhs) : 0xD0 ≤ (a3G sp0).toNat := by
  have := env.hGw; have := env.hS; omega

/-- `add`'s environment, for a call from the point addition. -/
theorem A3Env.aEnv (env : A3Env M0 P sp0 lhs rhs) {M : Word → BitVec 8} {W : Nat}
    (fr : ∀ x, Sep (a3S sp0) 0x440 x 1 → Sep lhs W x 1 → M x = M0 x) (hW : W ≤ 144) {d : Nat} {a b : Word}
    (hd : A3Dst d) (sa : A3Src sp0 a) (sb : A3Src sp0 b) :
    P3Env M (P + 0x2DC) (a3G sp0) (a3G sp0 + BitVec.ofNat 32 d) a b := by
  have cT := @A3Env.codeT _ _ _ _ _ env M W fr hW
  have e1 : P + 0x2DC + 0x126B2 = P + 0x1298E := by rw [BitVec.add_assoc]; rfl
  have e2 : p3Bsub (P + 0x2DC) = P + 0x4C8 := by show P + 0x2DC + 0x1EC = _; rw [BitVec.add_assoc]; rfl
  have e4 : P + 0x2DC + 0x1271A = P + 0x129F6 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0x2DC + 0x12722 = P + 0x129FE := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0x2DC (by decide), cT env.add env.sA env.lA, by rw [e1]; exact cT env.mset env.sMs env.lMs,
    by rw [e2]; exact cT env.bsub env.sBs env.lBs, by rw [e4]; exact cT env.stub env.sU env.lU,
    by rw [e5]; exact cT env.body env.sB env.lB, cT env.pmod env.sP env.lP,
    env.hGa, a3_hS_ad env, hd.al env, sa.1, sb.1, hd.wr env,
    aS_ad env.sA, by rw [e1]; exact aS_ad env.sMs, by rw [e2]; exact aS_ad env.sBs,
    by rw [e4]; exact aS_ad env.sU, by rw [e5]; exact aS_ad env.sB, aS_ad env.sP,
    hd.inS env.sA, by rw [e5]; exact hd.inS env.sB, ?_, sa.ad, sb.ad⟩
  rw [a3G_ad]; exact hd.sS.subR (c := 0x3C) (l := 0xB4) (by decide)

/-- `sub`'s environment, for a call from the point addition. -/
theorem A3Env.sEnv (env : A3Env M0 P sp0 lhs rhs) {M : Word → BitVec 8} {W : Nat}
    (fr : ∀ x, Sep (a3S sp0) 0x440 x 1 → Sep lhs W x 1 → M x = M0 x) (hW : W ≤ 144) {d : Nat} {a b : Word}
    (hd : A3Dst d) (sa : A3Src sp0 a) (sb : A3Src sp0 b) :
    PSEnv M (P + 0x3F2) (a3G sp0) (a3G sp0 + BitVec.ofNat 32 d) a b := by
  have cT := @A3Env.codeT _ _ _ _ _ env M W fr hW
  have e1 : P + 0x3F2 + 0x1259C = P + 0x1298E := by rw [BitVec.add_assoc]; rfl
  have e2 : psBsub (P + 0x3F2) = P + 0x4C8 := by show P + 0x3F2 + 0xD6 = _; rw [BitVec.add_assoc]; rfl
  have e4 : P + 0x3F2 + 0x12604 = P + 0x129F6 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0x3F2 + 0x1260C = P + 0x129FE := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0x3F2 (by decide), cT env.sub env.sSb env.lSb, by rw [e1]; exact cT env.mset env.sMs env.lMs,
    by rw [e2]; exact cT env.bsub env.sBs env.lBs, by rw [e4]; exact cT env.stub env.sU env.lU,
    by rw [e5]; exact cT env.body env.sB env.lB, cT env.pmod env.sP env.lP,
    env.hGa, a3_hS_ad env, hd.al env, sa.1, sb.1, hd.wr env,
    aS_ad env.sSb, by rw [e1]; exact aS_ad env.sMs, by rw [e2]; exact aS_ad env.sBs,
    by rw [e4]; exact aS_ad env.sU, by rw [e5]; exact aS_ad env.sB, aS_ad env.sP,
    hd.inS env.sSb, by rw [e5]; exact hd.inS env.sB, ?_, sa.ad, sb.ad⟩
  rw [a3G_ad]; exact hd.sS.subR (c := 0x3C) (l := 0xB4) (by decide)

/-- `double`'s environment, for a call from the point addition. -/
theorem A3Env.dEnv (env : A3Env M0 P sp0 lhs rhs) {M : Word → BitVec 8} {W : Nat}
    (fr : ∀ x, Sep (a3S sp0) 0x440 x 1 → Sep lhs W x 1 → M x = M0 x) (hW : W ≤ 144) {d : Nat} {a : Word}
    (hd : A3Dst d) (sa : A3Src sp0 a) :
    PDEnv M (P + 0x12100) (a3G sp0) (a3G sp0 + BitVec.ofNat 32 d) a := by
  have cT := @A3Env.codeT _ _ _ _ _ env M W fr hW
  have e1 : P + 0x12100 + 0x88E = P + 0x1298E := by rw [BitVec.add_assoc]; rfl
  have e2 : pdBsub (P + 0x12100) = P + 0x4C8 := by show P + 0x12100 + 0xFFFEE3C8 = _; rw [BitVec.add_assoc]; rfl
  have e3 : P + 0x12100 + 0xFFFFEF10 = P + 0x11010 := by rw [BitVec.add_assoc]; rfl
  have e4 : P + 0x12100 + 0x8F6 = P + 0x129F6 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0x12100 + 0x8FE = P + 0x129FE := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0x12100 (by decide), cT env.dbl env.sD env.lD,
    by rw [e1]; exact cT env.mset env.sMs env.lMs,
    by rw [e2]; exact cT env.bsub env.sBs env.lBs, by rw [e4]; exact cT env.stub env.sU env.lU,
    by rw [e5]; exact cT env.body env.sB env.lB, by rw [e3]; exact cT env.sel env.sSel env.lSel,
    cT env.pmod env.sP env.lP,
    env.hGa, a3_hS_db env, hd.al env, sa.1, hd.wr env,
    aS_db env.sD, by rw [e1]; exact aS_db env.sMs, by rw [e2]; exact aS_db env.sBs,
    by rw [e4]; exact aS_db env.sU, by rw [e5]; exact aS_db env.sB, by rw [e3]; exact aS_db env.sSel,
    aS_db env.sP, hd.inS env.sD, by rw [e3]; exact hd.inS env.sSel, by rw [e5]; exact hd.inS env.sB, ?_, sa.db⟩
  rw [a3G_db]; exact hd.sS.subR (c := 0x20) (l := 0xD0) (by decide)

/-- The callees' stack and a result slot leave the save slots alone. -/
theorem a3sv_keep {d c : Nat} (hd : A3Dst d) (h1 : 0x334 ≤ c) (h2 : c < 0x350) :
    Sep (a3S sp0) 0xF0 (a3G sp0 + BitVec.ofNat 32 c) 1 ∧
      Sep (a3G sp0 + BitVec.ofNat 32 d) 48 (a3G sp0 + BitVec.ofNat 32 c) 1 := by
  refine ⟨?_, sep_offsets _ (.inl (by have := hd.2.1; omega)) (by have := hd.2.1; omega) (by omega)⟩
  rw [a3G_S]
  exact sep_base0 (sep_offsets _ (c := 0) (n := 0xF0) (d := 0xF0 + c) (k := 1) (.inl (by omega))
    (by decide) (by omega))

/-- After a call that changed only the callees' stack and a result slot, the
invariant holds at the return address. -/
theorem A3Inv.after {M Ms M' : Word → BitVec 8} {V : Fin 32 → Word} {W d off : Nat} {n n' : Machine}
    (I : A3Inv M0 P sp0 lhs V Ms W M n off) (hd : A3Dst d)
    (st : St M' P n' (off + 8) (reg n')) (keep : ∀ q, d3Keep q = true → reg n' q = reg n q)
    (fr : ∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) :
    A3Inv M0 P sp0 lhs V Ms W M' n' (off + 8) :=
  ⟨st, fun q hq => (keep q hq).trans (I.keep q hq),
    fun x hx hl => (fr x (sep_base0 (hx.sub (c := 0) (l := 0xF0) (by decide))) (hd.inS hx)).trans (I.fr x hx hl),
    fun c h1 h2 => (fr _ (a3sv_keep hd h1 h2).1 (a3sv_keep hd h1 h2).2).trans (I.sv c h1 h2)⟩

end

section Calls
variable {M0 M Ms : Word → BitVec 8} {P sp0 lhs rhs : Word} {V : Fin 32 → Word} {W off d : Nat}
  {n : Machine} {imm o a b : Word} {A B : Nat}

set_option maxHeartbeats 1000000 in
/-- A call to the multiplication wrapper: the result slot gets the
Montgomery product of the operands. -/
theorem a3_mul (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 144)
    (hVsp : V sp = a3G sp0)
    (h1 : fetchRel p384PtAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x11A24) (hoff : off % 2 = 0)
    (hd : A3Dst d) (ha0 : reg n a0 = a3G sp0 + BitVec.ofNat 32 d)
    (sa : A3Src sp0 a) (ha1 : reg n a1 = a) (sb : A3Src sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 12) = A) (hB : limbVal (wordsAt M b 12) = B) (hBp : B < p384) :
    ∃ n' M', Steps n n' ∧ A3Inv M0 P sp0 lhs V Ms W M' n' (off + 8) ∧
      (∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (a3G sp0 + BitVec.ofNat 32 d) 12) = p3fm A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0x11A24 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have spn : reg n sp = a3G sp0 := by rw [I.keep sp rfl, hVsp]
  obtain ⟨n', c', pc', sp', k', val', fr'⟩ := p384Mul_correct n1 (by rw [mem1]; exact env.mEnv I.fr hW hd sa sb)
    pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (a3_ret_even env hoff)
    (by rw [r1 sp (by decide), spn]) (by rw [mem1, hB]; exact hBp)
  rw [mem1, hA, hB] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [a3G_mm]; exact hx) hr
  have st' : St n'.mem P n' (off + 8) (reg n') := ⟨by rw [pc'], rfl, fun _ => rfl⟩
  refine ⟨n', n'.mem, c1.trans c', I.after hd st'
    (d3keep_of_mm regs1 I.st.zero st'.zero spn sp' k') frS, frS, val'⟩

set_option maxHeartbeats 1000000 in
/-- A call to `add`. -/
theorem a3_add (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 144)
    (hVsp : V sp = a3G sp0)
    (h1 : fetchRel p384PtAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x2DC) (hoff : off % 2 = 0)
    (hd : A3Dst d) (ha0 : reg n a0 = a3G sp0 + BitVec.ofNat 32 d)
    (sa : A3Src sp0 a) (ha1 : reg n a1 = a) (sb : A3Src sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 12) = A) (hAp : A < p384) (hB : limbVal (wordsAt M b 12) = B) (hBp : B < p384) :
    ∃ n' M', Steps n n' ∧ A3Inv M0 P sp0 lhs V Ms W M' n' (off + 8) ∧
      (∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (a3G sp0 + BitVec.ofNat 32 d) 12) = p3fa A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0x2DC (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have spn : reg n sp = a3G sp0 := by rw [I.keep sp rfl, hVsp]
  obtain ⟨n', c', pc', sp', k', val', fr'⟩ := p384Add_correct n1 (by rw [mem1]; exact env.aEnv I.fr hW hd sa sb)
    pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (a3_ret_even env hoff) (by rw [r1 sp (by decide), spn])
  rw [mem1, hA, hB, p3AddRes_mod hAp hBp] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 →
      n'.mem x = M x := fun x hx hr =>
    fr' x (by rw [a3G_ad]; exact hx.sub (c := 0x3C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (d3keep_of_call regs1 I.st.zero k') frS, frS, val'⟩

set_option maxHeartbeats 1000000 in
/-- A call to `sub`. -/
theorem a3_sub (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 144)
    (hVsp : V sp = a3G sp0)
    (h1 : fetchRel p384PtAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x3F2) (hoff : off % 2 = 0)
    (hd : A3Dst d) (ha0 : reg n a0 = a3G sp0 + BitVec.ofNat 32 d)
    (sa : A3Src sp0 a) (ha1 : reg n a1 = a) (sb : A3Src sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 12) = A) (hAp : A < p384) (hB : limbVal (wordsAt M b 12) = B) (hBp : B < p384) :
    ∃ n' M', Steps n n' ∧ A3Inv M0 P sp0 lhs V Ms W M' n' (off + 8) ∧
      (∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (a3G sp0 + BitVec.ofNat 32 d) 12) = p3fs A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0x3F2 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have spn : reg n sp = a3G sp0 := by rw [I.keep sp rfl, hVsp]
  obtain ⟨n', c', pc', sp', k', val', fr'⟩ := p384Sub_correct n1 (by rw [mem1]; exact env.sEnv I.fr hW hd sa sb)
    pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (a3_ret_even env hoff) (by rw [r1 sp (by decide), spn])
  rw [mem1, hA, hB, p3SubRes_mod hAp hBp] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 →
      n'.mem x = M x := fun x hx hr =>
    fr' x (by rw [a3G_ad]; exact hx.sub (c := 0x3C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (d3keep_of_call regs1 I.st.zero k') frS, frS, val'⟩

set_option maxHeartbeats 1000000 in
/-- A call to `double`. -/
theorem a3_dbl (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 144)
    (hVsp : V sp = a3G sp0)
    (h1 : fetchRel p384PtAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x12100) (hoff : off % 2 = 0)
    (hd : A3Dst d) (ha0 : reg n a0 = a3G sp0 + BitVec.ofNat 32 d)
    (sa : A3Src sp0 a) (ha1 : reg n a1 = a)
    (hA : limbVal (wordsAt M a 12) = A) (hAp : A < p384) :
    ∃ n' M', Steps n n' ∧ A3Inv M0 P sp0 lhs V Ms W M' n' (off + 8) ∧
      (∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (a3G sp0 + BitVec.ofNat 32 d) 12) = p3fd A := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0x12100 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have spn : reg n sp = a3G sp0 := by rw [I.keep sp rfl, hVsp]
  obtain ⟨n', c', pc', sp', k', val', fr'⟩ := p384Double_correct n1 (by rw [mem1]; exact env.dEnv I.fr hW hd sa)
    pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (a3_ret_even env hoff) (by rw [r1 sp (by decide), spn])
  rw [mem1, hA, p3AddRes_mod hAp hAp] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 →
      n'.mem x = M x := fun x hx hr =>
    fr' x (by rw [a3G_db]; exact hx.sub (c := 0x20) (l := 0xD0) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (d3keep_of_call regs1 I.st.zero k') frS, frS, val'⟩

set_option maxHeartbeats 1000000 in
/-- A `memcpy` of a frame slot into the coordinate of `lhs` at `k`, the next
48 bytes of the result. -/
theorem a3_cpy {k : Nat} (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms k M n off)
    (hk : k + 48 ≤ 144) (hk4 : k % 4 = 0)
    (h1 : fetchRel p384PtAddCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtAddCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x129F6) (hoff : off % 2 = 0)
    (hd : A3Dst d) (ha0 : reg n a0 = lhs + BitVec.ofNat 32 k)
    (ha1 : reg n a1 = a3G sp0 + BitVec.ofNat 32 d) (ha2 : reg n a2 = 0x30) :
    ∃ n' M', Steps n n' ∧ A3Inv M0 P sp0 lhs V Ms (k + 48) M' n' (off + 8) ∧
      (∀ x, Sep (lhs + BitVec.ofNat 32 k) 48 x 1 → M' x = M x) ∧
      wordsAt M' (lhs + BitVec.ofNat 32 k) 12 = wordsAt M (a3G sp0 + BitVec.ofNat 32 d) 12 := by
  have hW : k ≤ 144 := by omega
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr hW env.code env.sC env.lC) h1 h2 hb
    (even_at P env.hP 0x129F6 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have e : P + 0x129F6 + 8 = P + 0x129FE := by rw [BitVec.add_assoc]; rfl
  have hwl := env.hwl
  have hdw : (lhs + BitVec.ofNat 32 k).toNat = lhs.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sLk : Sep (lhs + BitVec.ofNat 32 k) 48 (a3S sp0) 0x440 := env.sL.sub (c := k) (l := 48) hk
  obtain ⟨n', c', pc', mem', a0', regs'⟩ := memcpy_aligned n1 (P + 0x129F6) (P + BitVec.ofNat 32 (off + 8))
    (lhs + BitVec.ofNat 32 k) (a3G sp0 + BitVec.ofNat 32 d) 12
    (fun i hi => by rw [mem1]; exact env.codeT I.fr hW env.stub env.sU env.lU i hi)
    (fun i hi => by rw [mem1, e]; exact env.codeT I.fr hW env.body env.sB env.lB i hi)
    (even_at P env.hP 0x129F6 (by decide)) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]; rfl)
    (by rw [regs1]; simp +decide [upd]) (a3_ret_even env hoff) (by decide) (by omega) (by decide)
    (aligned_add env.hl hk4) (hd.al env) (hd.inS sLk.symm).symm
    (by rw [e]; exact env.lB.sub (c := k) (l := 48) hk)
  rw [mem1] at mem'
  have out : ∀ x, Sep (lhs + BitVec.ofNat 32 k) 48 x 1 → n'.mem x = M x := fun x hx => by
    rw [mem']; exact copyWords_outside 12 hx
  refine ⟨n', n'.mem, c1.trans c', ⟨⟨by rw [pc'], rfl, fun _ => rfl⟩, fun q hq => ?_, fun x hx hl => ?_,
    fun c h1 h2 => ?_⟩, out, ?_⟩
  · have k' := fun r (hr : d3Keep r = false) => bkeep_ne hq hr
    rw [regs' q (k' a1 rfl) (k' a2 rfl) (k' a3 rfl) (k' a4 rfl) (k' a5 rfl) (k' a6 rfl) (k' a7 rfl)
      (k' t0 rfl) (k' t1 rfl), r1 q (k' ra rfl)]
    exact I.keep q hq
  · rw [out x (hl.sub (c := k) (l := 48) (by omega))]
    exact I.fr x hx (sep_base0 (hl.sub (c := 0) (l := k) (by omega)))
  · rw [out _ (by rw [a3G_S]; exact sLk.subR (c := 0xF0 + c) (l := 1) (by omega))]
    exact I.sv c h1 h2
  · rw [mem']
    unfold wordsAt
    exact List.map_congr_left fun i hi => copyWords_load 12 i (List.mem_range.mp hi) (by omega)

end Calls

section Keep
variable {M0 M M' Ms : Word → BitVec 8} {P sp0 lhs rhs : Word} {V : Fin 32 → Word} {off : Nat} {n : Machine}

/-- Before any result is written, an operand outside `S` reads as on entry. -/
theorem A3Inv.inp (I : A3Inv M0 P sp0 lhs V Ms 0 M n off) {a : Word} (h : Sep a 48 (a3S sp0) 0x440) :
    wordsAt M a 12 = wordsAt M0 a 12 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => I.fr _
    (by rw [add_ofNat_assoc]; exact h.symm.subR (c := 4 * i + j) (l := 1) (by omega))
    (fun _ h0 _ _ => absurd h0 (Nat.not_lt_zero _))

/-- `b` reads as on entry whatever has been written. -/
theorem A3Inv.bval {W : Nat} (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n off)
    (hW : W ≤ 144) : limbVal (wordsAt M p3bA 12) = p3B :=
  p3B_val (env.codeT I.fr hW env.bconst env.sK env.lK)

/-- A call that changed only the callees' stack and the slot at `d` left the
slot at `c` alone. -/
theorem a3slot_keep {d c : Nat}
    (f : ∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x)
    (hd : A3Dst d) (hc : A3Dst c) (hdc : d + 48 ≤ c ∨ c + 48 ≤ d) :
    wordsAt M' (a3G sp0 + BitVec.ofNat 32 c) 12 = wordsAt M (a3G sp0 + BitVec.ofNat 32 c) 12 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc (a3G sp0) c (4 * i), add_ofNat_assoc (a3G sp0) (c + 4 * i) j]
    have := hc.2.1; have := hd.2.1
    exact f _ (by
        rw [a3G_S]
        exact sep_base0 (sep_offsets _ (c := 0) (n := 0xF0) (d := 0xF0 + (c + 4 * i + j)) (k := 1)
          (.inl (by omega)) (by decide) (by omega)))
      (sep_offsets _ (c := d) (n := 48) (d := c + 4 * i + j) (k := 1)
        (by rcases hdc with h | h
            · exact .inl (by omega)
            · exact .inr (by omega)) (by omega) (by omega))

/-- A call that changed only `S` left the coordinate of `lhs` at `k` alone. -/
theorem a3lhs_keep (env : A3Env M0 P sp0 lhs rhs) {d k : Nat}
    (f : ∀ x, Sep (a3S sp0) 0xF0 x 1 → Sep (a3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x)
    (hd : A3Dst d) (hk : k + 48 ≤ 144) :
    wordsAt M' (lhs + BitVec.ofNat 32 k) 12 = wordsAt M (lhs + BitVec.ofNat 32 k) 12 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc lhs k (4 * i), add_ofNat_assoc lhs (k + 4 * i) j]
    have hs := env.sL.sub (c := k + 4 * i + j) (l := 1) (by omega)
    exact f _ (sep_base0r (hs.subR (c := 0) (l := 0xF0) (by decide))).symm (hd.inS hs.symm)

/-- A `memcpy` into the coordinate of `lhs` at `k` left the frame slot at `c`
alone. -/
theorem a3slot_keep_cpy (env : A3Env M0 P sp0 lhs rhs) {k c : Nat} (hk : k + 48 ≤ 144)
    (f : ∀ x, Sep (lhs + BitVec.ofNat 32 k) 48 x 1 → M' x = M x) (hc : A3Dst c) :
    wordsAt M' (a3G sp0 + BitVec.ofNat 32 c) 12 = wordsAt M (a3G sp0 + BitVec.ofNat 32 c) 12 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc (a3G sp0) c (4 * i), add_ofNat_assoc (a3G sp0) (c + 4 * i) j]
    exact f _ ((hc.inS (env.sL.sub (c := k) (l := 48) hk).symm).symm.subR (c := 4 * i + j) (l := 1) (by omega) |>
      fun h => by rw [add_ofNat_assoc] at h; simpa only [Nat.add_assoc] using h)

/-- A `memcpy` into the coordinate of `lhs` at `k` left the one at `k'`
alone. -/
theorem a3lhs_keep_cpy {k k' : Nat} (hk : k + 48 ≤ 144) (hk' : k' + 48 ≤ k)
    (f : ∀ x, Sep (lhs + BitVec.ofNat 32 k) 48 x 1 → M' x = M x) :
    wordsAt M' (lhs + BitVec.ofNat 32 k') 12 = wordsAt M (lhs + BitVec.ofNat 32 k') 12 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc lhs k' (4 * i), add_ofNat_assoc lhs (k' + 4 * i) j]
    exact f _ (sep_offsets _ (.inr (by omega)) (by omega) (by omega))

end Keep

section Steps
variable {M0 M Ms : Word → BitVec 8} {P sp0 lhs rhs : Word} {V : Fin 32 → Word} {W off off' : Nat}
  {n : Machine}

/-- `addi rd, rs, imm` into a register `d3Keep` doesn't name. -/
theorem a3_addi (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 144)
    {rd rs : Fin 32} {imm len : Word}
    (hf : fetchRel p384PtAddCode off = some (.aluImm .add rd rs imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hk : d3Keep rd = false) :
    ∃ n', Steps n n' ∧ A3Inv M0 P sp0 lhs V Ms W M n' off' ∧ reg n' rd = reg n rs + imm ∧
      ∀ q, q ≠ rd → reg n' q = reg n q := by
  obtain ⟨n', d, u⟩ := I.st.aluImm (env.codeT I.fr hW env.code env.sC env.lC) hf hn
  have h0 : rd.val ≠ 0 := fun h => by
    have : rd = 0 := Fin.ext h
    subst this; exact absurd hk (by decide)
  have ne : ∀ q, q ≠ rd → reg n' q = reg n q := fun q hq => by
    rw [u.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact I.st.zero.symm
    · exact upd_ne hq0 hq
  exact ⟨n', .single d, ⟨u.self, fun q hq => (ne q (bkeep_ne hq hk)).trans (I.keep q hq), I.fr, I.sv⟩,
    by rw [u.regs, upd_same h0]; rfl, ne⟩

/-- `addi rd, rs, imm` into a register `d3Keep` names: `V` changes there. -/
theorem a3_addiK (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 144)
    {rd rs : Fin 32} {imm len : Word}
    (hf : fetchRel p384PtAddCode off = some (.aluImm .add rd rs imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (h0 : rd.val ≠ 0) :
    ∃ n', Steps n n' ∧ A3Inv M0 P sp0 lhs (upd V rd (reg n rs + imm)) Ms W M n' off' ∧
      reg n' rd = reg n rs + imm ∧ ∀ q, q ≠ rd → reg n' q = reg n q := by
  obtain ⟨n', d, u⟩ := I.st.aluImm (env.codeT I.fr hW env.code env.sC env.lC) hf hn
  have ne : ∀ q, q ≠ rd → reg n' q = reg n q := fun q hq => by
    rw [u.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact I.st.zero.symm
    · exact upd_ne hq0 hq
  have same : reg n' rd = reg n rs + imm := by rw [u.regs, upd_same h0]; rfl
  refine ⟨n', .single d, ⟨u.self, fun q hq => ?_, I.fr, I.sv⟩, same, ne⟩
  by_cases hq0 : q.val = 0
  · have : q = 0 := Fin.ext hq0
    subst this; simp [upd]; exact u.self.zero
  by_cases e : q = rd
  · subst e; rw [same, upd_same h0]
  · rw [ne q e, upd_ne hq0 e]; exact I.keep q hq

/-- `lui rd, imm` into a register `d3Keep` names. -/
theorem a3_luiK (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 144)
    {rd : Fin 32} {imm len : Word}
    (hf : fetchRel p384PtAddCode off = some (.lui rd imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (h0 : rd.val ≠ 0) :
    ∃ n', Steps n n' ∧ A3Inv M0 P sp0 lhs (upd V rd imm) Ms W M n' off' ∧ reg n' rd = imm := by
  obtain ⟨n', d, u⟩ := I.st.lui (env.codeT I.fr hW env.code env.sC env.lC) hf hn
  have same : reg n' rd = imm := by rw [u.regs, upd_same h0]
  refine ⟨n', .single d, ⟨u.self, fun q hq => ?_, I.fr, I.sv⟩, same⟩
  by_cases hq0 : q.val = 0
  · have : q = 0 := Fin.ext hq0
    subst this; simp [upd]; exact u.self.zero
  by_cases e : q = rd
  · subst e; rw [same, upd_same h0]
  · rw [u.regs, upd_ne hq0 e, upd_ne hq0 e]; exact I.keep q hq

/-- `mv rd, rs` into a register `d3Keep` doesn't name. -/
theorem a3_mv (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n off) (hW : W ≤ 144)
    {rd rs : Fin 32} {len : Word}
    (hf : fetchRel p384PtAddCode off = some (.alu .add rd 0 rs, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hk : d3Keep rd = false) :
    ∃ n', Steps n n' ∧ A3Inv M0 P sp0 lhs V Ms W M n' off' ∧ reg n' rd = reg n rs ∧
      ∀ q, q ≠ rd → reg n' q = reg n q := by
  obtain ⟨n', d, u⟩ := I.st.alu (env.codeT I.fr hW env.code env.sC env.lC) hf hn
  have h0 : rd.val ≠ 0 := fun h => by
    have : rd = 0 := Fin.ext h
    subst this; exact absurd hk (by decide)
  have ne : ∀ q, q ≠ rd → reg n' q = reg n q := fun q hq => by
    rw [u.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact I.st.zero.symm
    · exact upd_ne hq0 hq
  exact ⟨n', .single d, ⟨u.self, fun q hq => (ne q (bkeep_ne hq hk)).trans (I.keep q hq), I.fr, I.sv⟩,
    by rw [u.regs, upd_same h0]; show reg n 0 + reg n rs = reg n rs; rw [I.st.zero]; exact BitVec.zero_add _, ne⟩

end Steps

/-- The registers the point addition saves, with their offsets in its frame. -/
abbrev a3Ps : List (Fin 32 × Nat) :=
  [(ra, 0x34C), ((8 : Fin 32), 0x348), ((9 : Fin 32), 0x344), ((18 : Fin 32), 0x340),
   ((19 : Fin 32), 0x33C), ((20 : Fin 32), 0x338), ((21 : Fin 32), 0x334)]

theorem a3_slot_addr (sp0 o : Word) (c : Nat) (h : (0x300 : Word) + o = BitVec.ofNat 32 c) :
    a3G sp0 + 0x300 + o = a3G sp0 + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc (a3G sp0), h]

set_option maxHeartbeats 4000000 in
/-- The point addition's prologue, to 0x22: make the 0x350-byte frame, save
`ra` and `s0` through `s5` at its top, and keep the points' addresses in `s1`
and `s4`. -/
theorem a3_pro (m : Machine) {P sp0 lhs rhs : Word} (env : A3Env m.mem P sp0 lhs rhs) (hpc : m.pc = P)
    (ha0 : reg m a0 = lhs) (ha1 : reg m a1 = rhs) (hsp : reg m sp = sp0) :
    ∃ n Ms, Steps m n ∧ A3Inv m.mem P sp0 lhs (reg n) Ms 0 Ms n 0x22 ∧
      reg n sp = a3G sp0 ∧ reg n (9 : Fin 32) = rhs ∧ reg n (20 : Fin 32) = lhs ∧
      (∀ q, q ≠ sp → q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → reg n q = reg m q) ∧
      ∀ r c, (r, c) ∈ a3Ps → memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 c) = reg m r := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGa := env.hGa
  have F2 : ∀ x, Sep (a3S sp0) 0x440 x 1 → m.mem x = m.mem x := fun _ _ => rfl
  have codeS : ∀ {M' : Word → BitVec 8}, (∀ x, Sep (a3S sp0) 0x440 x 1 → M' x = m.mem x) →
      CodeIn M' P p384PtAddCode := fun hM i hi => by
    rw [hM _ (env.sC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have slotS : ∀ c, 0x334 ≤ c → c + 4 ≤ 0x350 → ∀ x, Sep (a3S sp0) 0x440 x 1 →
      Sep (a3G sp0 + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 x hx => by
    rw [a3G_S]; exact hx.sub (by omega)
  obtain ⟨n1, d1, u1⟩ := s0.aluImm (codeS F2) p3pa_at_0 (off' := 4) (by decide)
  have e1 : reg n1 sp = a3G sp0 := by rw [u1.regs, upd_same (by decide), hsp]; rfl
  have k1 : ∀ q, q ≠ sp → reg n1 q = reg m q := fun q h => by
    rw [u1.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · exact upd_ne h0 h
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm (codeS F2) p3pa_at_4 (off' := 6) (by decide)
  have e2 : reg n2 a2 = a3G sp0 + 0x300 := by rw [u2.regs, upd_same (by decide), e1]; rfl
  have k2 : ∀ q, q ≠ a2 → reg n2 q = reg n1 q := fun q h => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u1.self.zero.symm
    · exact upd_ne h0 h
  obtain ⟨n3, d3, u3⟩ := u2.self.sw (codeS F2) p3pa_at_6 (off' := 0xA) (by decide)
    (by rw [e2, a3_slot_addr sp0 0x4C 0x34C rfl]; exact aligned_add hGa (by decide))
  rw [e2, a3_slot_addr sp0 0x4C 0x34C rfl] at u3
  obtain ⟨M3, hM3⟩ : ∃ M, memStore32 m.mem (a3G sp0 + BitVec.ofNat 32 0x34C) (reg n2 ra) = M := ⟨_, rfl⟩
  rw [hM3] at u3
  have F3 : ∀ x, Sep (a3S sp0) 0x440 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, memStore32_get_sep (slotS 0x34C (by decide) (by decide) x hx), F2 x hx]
  obtain ⟨n4, d4, u4⟩ := u3.sw (codeS F3) p3pa_at_a (off' := 0xC) (by decide)
    (by rw [e2, a3_slot_addr sp0 0x48 0x348 rfl]; exact aligned_add hGa (by decide))
  rw [e2, a3_slot_addr sp0 0x48 0x348 rfl] at u4
  obtain ⟨M4, hM4⟩ : ∃ M, memStore32 M3 (a3G sp0 + BitVec.ofNat 32 0x348) (reg n2 (8 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM4] at u4
  have F4 : ∀ x, Sep (a3S sp0) 0x440 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, memStore32_get_sep (slotS 0x348 (by decide) (by decide) x hx), F3 x hx]
  obtain ⟨n5, d5, u5⟩ := u4.sw (codeS F4) p3pa_at_c (off' := 0xE) (by decide)
    (by rw [e2, a3_slot_addr sp0 0x44 0x344 rfl]; exact aligned_add hGa (by decide))
  rw [e2, a3_slot_addr sp0 0x44 0x344 rfl] at u5
  obtain ⟨M5, hM5⟩ : ∃ M, memStore32 M4 (a3G sp0 + BitVec.ofNat 32 0x344) (reg n2 (9 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM5] at u5
  have F5 : ∀ x, Sep (a3S sp0) 0x440 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5, memStore32_get_sep (slotS 0x344 (by decide) (by decide) x hx), F4 x hx]
  obtain ⟨n6, d6, u6⟩ := u5.sw (codeS F5) p3pa_at_e (off' := 0x12) (by decide)
    (by rw [e2, a3_slot_addr sp0 0x40 0x340 rfl]; exact aligned_add hGa (by decide))
  rw [e2, a3_slot_addr sp0 0x40 0x340 rfl] at u6
  obtain ⟨M6, hM6⟩ : ∃ M, memStore32 M5 (a3G sp0 + BitVec.ofNat 32 0x340) (reg n2 (18 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM6] at u6
  have F6 : ∀ x, Sep (a3S sp0) 0x440 x 1 → M6 x = m.mem x := fun x hx => by
    rw [← hM6, memStore32_get_sep (slotS 0x340 (by decide) (by decide) x hx), F5 x hx]
  obtain ⟨n7, d7, u7⟩ := u6.sw (codeS F6) p3pa_at_12 (off' := 0x16) (by decide)
    (by rw [e2, a3_slot_addr sp0 0x3C 0x33C rfl]; exact aligned_add hGa (by decide))
  rw [e2, a3_slot_addr sp0 0x3C 0x33C rfl] at u7
  obtain ⟨M7, hM7⟩ : ∃ M, memStore32 M6 (a3G sp0 + BitVec.ofNat 32 0x33C) (reg n2 (19 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM7] at u7
  have F7 : ∀ x, Sep (a3S sp0) 0x440 x 1 → M7 x = m.mem x := fun x hx => by
    rw [← hM7, memStore32_get_sep (slotS 0x33C (by decide) (by decide) x hx), F6 x hx]
  obtain ⟨n8, d8, u8⟩ := u7.sw (codeS F7) p3pa_at_16 (off' := 0x1A) (by decide)
    (by rw [e2, a3_slot_addr sp0 0x38 0x338 rfl]; exact aligned_add hGa (by decide))
  rw [e2, a3_slot_addr sp0 0x38 0x338 rfl] at u8
  obtain ⟨M8, hM8⟩ : ∃ M, memStore32 M7 (a3G sp0 + BitVec.ofNat 32 0x338) (reg n2 (20 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM8] at u8
  have F8 : ∀ x, Sep (a3S sp0) 0x440 x 1 → M8 x = m.mem x := fun x hx => by
    rw [← hM8, memStore32_get_sep (slotS 0x338 (by decide) (by decide) x hx), F7 x hx]
  obtain ⟨n9, d9, u9⟩ := u8.sw (codeS F8) p3pa_at_1a (off' := 0x1E) (by decide)
    (by rw [e2, a3_slot_addr sp0 0x34 0x334 rfl]; exact aligned_add hGa (by decide))
  rw [e2, a3_slot_addr sp0 0x34 0x334 rfl] at u9
  obtain ⟨M9, hM9⟩ : ∃ M, memStore32 M8 (a3G sp0 + BitVec.ofNat 32 0x334) (reg n2 (21 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM9] at u9
  have F9 : ∀ x, Sep (a3S sp0) 0x440 x 1 → M9 x = m.mem x := fun x hx => by
    rw [← hM9, memStore32_get_sep (slotS 0x334 (by decide) (by decide) x hx), F8 x hx]
  obtain ⟨n10, d10, u10⟩ := u9.alu (codeS F9) p3pa_at_1e (off' := 0x20) (by decide)
  obtain ⟨n11, d11, u11⟩ := u10.self.alu (codeS F9) p3pa_at_20 (off' := 0x22) (by decide)
  have k11 : ∀ q, q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → reg n11 q = reg n2 q := fun q h9 h20 => by
    rw [u11.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u2.self.zero.symm
    · rw [upd_ne h0 h20, u10.regs, upd_ne h0 h9]
  refine ⟨n11, M9, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.single d11)))))))))),
    ⟨u11.self, fun _ _ => rfl, fun x hx _ => F9 x hx, fun _ _ _ => rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k11 sp (by decide) (by decide), k2 sp (by decide), e1]
  · rw [u11.regs, upd_ne (by decide) (by decide), u10.regs, upd_same (by decide)]
    show reg n2 0 + reg n2 a1 = rhs
    rw [u2.self.zero, k2 a1 (by decide), k1 a1 (by decide), ha1]; exact BitVec.zero_add _
  · rw [u11.regs, upd_same (by decide)]
    show reg n10 0 + reg n10 a0 = lhs
    rw [u10.self.zero, u10.regs, upd_ne (by decide) (by decide), k2 a0 (by decide), k1 a0 (by decide), ha0]
    exact BitVec.zero_add _
  · intro q hsp' ha2 h9 h20
    rw [k11 q h9 h20, k2 q ha2, k1 q hsp']
  · intro r c h
    simp only [a3Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [← hM9, ← hM8, ← hM7, ← hM6, ← hM5, ← hM4, ← hM3]
      simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
      rw [k2 _ (by decide), k1 _ (by decide)]

set_option maxHeartbeats 4000000 in
/-- The point addition's epilogue, from 0x2BC: restore `ra` and `s0` through
`s5` from the save slots, drop the frame, and return. -/
theorem a3_epi {M0 M Ms : Word → BitVec 8} {P sp0 lhs rhs : Word} {V : Fin 32 → Word} {W : Nat} {n : Machine}
    (env : A3Env M0 P sp0 lhs rhs) (I : A3Inv M0 P sp0 lhs V Ms W M n 0x2BC) (hW : W ≤ 144)
    (hVsp : V sp = a3G sp0) :
    ∃ m', Steps n m' ∧ m'.pc = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 0x34C) &&& ~~~1 ∧ m'.mem = M ∧
      reg m' sp = sp0 ∧ (∀ r c, (r, c) ∈ a3Ps → reg m' r = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 c)) ∧
      ∀ q, d3Keep q = true → q ≠ sp → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (21 : Fin 32) → reg m' q = V q := by
  have cM := env.codeT I.fr hW env.code env.sC env.lC
  have hGa := env.hGa
  have ld : ∀ c, 0x334 ≤ c → c + 4 ≤ 0x350 →
      memLoad32 M (a3G sp0 + BitVec.ofNat 32 c) = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact I.sv (c + j) (by omega) (by omega)
  obtain ⟨n1, d1, u1⟩ := I.st.aluImm cM p3pa_at_2bc (off' := 0x2BE) (by decide)
  have a1 : reg n1 a0 = a3G sp0 + 0x300 := by
    rw [u1.regs, upd_same (by decide), I.keep sp rfl, hVsp]; rfl
  have k1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q h => by
    rw [u1.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact I.st.zero.symm
    · exact upd_ne h0 h
  obtain ⟨n2, d2, u2⟩ := u1.self.lw cM p3pa_at_2be (off' := 0x2C2) (by decide)
    (by rw [a1, a3_slot_addr sp0 0x4C 0x34C rfl]; exact aligned_add hGa (by decide))
  have v2 : reg n2 ra = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 0x34C) := by
    rw [u2.regs, upd_same (by decide), a1, a3_slot_addr sp0 0x4C 0x34C rfl, ld _ (by decide) (by decide)]
  have k2 : ∀ q, q ≠ ra → reg n2 q = reg n1 q := fun q h => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u1.self.zero.symm
    · exact upd_ne h0 h
  have a2 : reg n2 a0 = a3G sp0 + 0x300 := by rw [k2 a0 (by decide), a1]
  obtain ⟨n3, d3, u3⟩ := u2.self.lw cM p3pa_at_2c2 (off' := 0x2C4) (by decide)
    (by rw [a2, a3_slot_addr sp0 0x48 0x348 rfl]; exact aligned_add hGa (by decide))
  have v3 : reg n3 (8 : Fin 32) = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 0x348) := by
    rw [u3.regs, upd_same (by decide), a2, a3_slot_addr sp0 0x48 0x348 rfl, ld _ (by decide) (by decide)]
  have k3 : ∀ q, q ≠ (8 : Fin 32) → reg n3 q = reg n2 q := fun q h => by
    rw [u3.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u2.self.zero.symm
    · exact upd_ne h0 h
  have a3 : reg n3 a0 = a3G sp0 + 0x300 := by rw [k3 a0 (by decide), a2]
  obtain ⟨n4, d4, u4⟩ := u3.self.lw cM p3pa_at_2c4 (off' := 0x2C6) (by decide)
    (by rw [a3, a3_slot_addr sp0 0x44 0x344 rfl]; exact aligned_add hGa (by decide))
  have v4 : reg n4 (9 : Fin 32) = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 0x344) := by
    rw [u4.regs, upd_same (by decide), a3, a3_slot_addr sp0 0x44 0x344 rfl, ld _ (by decide) (by decide)]
  have k4 : ∀ q, q ≠ (9 : Fin 32) → reg n4 q = reg n3 q := fun q h => by
    rw [u4.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u3.self.zero.symm
    · exact upd_ne h0 h
  have a4 : reg n4 a0 = a3G sp0 + 0x300 := by rw [k4 a0 (by decide), a3]
  obtain ⟨n5, d5, u5⟩ := u4.self.lw cM p3pa_at_2c6 (off' := 0x2CA) (by decide)
    (by rw [a4, a3_slot_addr sp0 0x40 0x340 rfl]; exact aligned_add hGa (by decide))
  have v5 : reg n5 (18 : Fin 32) = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 0x340) := by
    rw [u5.regs, upd_same (by decide), a4, a3_slot_addr sp0 0x40 0x340 rfl, ld _ (by decide) (by decide)]
  have k5 : ∀ q, q ≠ (18 : Fin 32) → reg n5 q = reg n4 q := fun q h => by
    rw [u5.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u4.self.zero.symm
    · exact upd_ne h0 h
  have a5 : reg n5 a0 = a3G sp0 + 0x300 := by rw [k5 a0 (by decide), a4]
  obtain ⟨n6, d6, u6⟩ := u5.self.lw cM p3pa_at_2ca (off' := 0x2CE) (by decide)
    (by rw [a5, a3_slot_addr sp0 0x3C 0x33C rfl]; exact aligned_add hGa (by decide))
  have v6 : reg n6 (19 : Fin 32) = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 0x33C) := by
    rw [u6.regs, upd_same (by decide), a5, a3_slot_addr sp0 0x3C 0x33C rfl, ld _ (by decide) (by decide)]
  have k6 : ∀ q, q ≠ (19 : Fin 32) → reg n6 q = reg n5 q := fun q h => by
    rw [u6.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u5.self.zero.symm
    · exact upd_ne h0 h
  have a6 : reg n6 a0 = a3G sp0 + 0x300 := by rw [k6 a0 (by decide), a5]
  obtain ⟨n7, d7, u7⟩ := u6.self.lw cM p3pa_at_2ce (off' := 0x2D2) (by decide)
    (by rw [a6, a3_slot_addr sp0 0x38 0x338 rfl]; exact aligned_add hGa (by decide))
  have v7 : reg n7 (20 : Fin 32) = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 0x338) := by
    rw [u7.regs, upd_same (by decide), a6, a3_slot_addr sp0 0x38 0x338 rfl, ld _ (by decide) (by decide)]
  have k7 : ∀ q, q ≠ (20 : Fin 32) → reg n7 q = reg n6 q := fun q h => by
    rw [u7.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u6.self.zero.symm
    · exact upd_ne h0 h
  have a7 : reg n7 a0 = a3G sp0 + 0x300 := by rw [k7 a0 (by decide), a6]
  obtain ⟨n8, d8, u8⟩ := u7.self.lw cM p3pa_at_2d2 (off' := 0x2D6) (by decide)
    (by rw [a7, a3_slot_addr sp0 0x34 0x334 rfl]; exact aligned_add hGa (by decide))
  have v8 : reg n8 (21 : Fin 32) = memLoad32 Ms (a3G sp0 + BitVec.ofNat 32 0x334) := by
    rw [u8.regs, upd_same (by decide), a7, a3_slot_addr sp0 0x34 0x334 rfl, ld _ (by decide) (by decide)]
  have k8 : ∀ q, q ≠ (21 : Fin 32) → reg n8 q = reg n7 q := fun q h => by
    rw [u8.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u7.self.zero.symm
    · exact upd_ne h0 h
  have a8 : reg n8 a0 = a3G sp0 + 0x300 := by rw [k8 a0 (by decide), a7]
  obtain ⟨n9, d9, u9⟩ := u8.self.aluImm cM p3pa_at_2d6 (off' := 0x2DA) (by decide)
  have k9 : ∀ q, q ≠ sp → reg n9 q = reg n8 q := fun q h => by
    rw [u9.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u8.self.zero.symm
    · exact upd_ne h0 h
  obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.self.jalr cM p3pa_at_2da
  have back : ∀ q, q ≠ a0 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
      q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (21 : Fin 32) → reg n8 q = reg n q :=
    fun q h0 h1 h8 h9 h18 h19 h20 h21 => by
      rw [k8 q h21, k7 q h20, k6 q h19, k5 q h18, k4 q h9, k3 q h8, k2 q h1, k1 q h0]
  refine ⟨n10, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.single d10))))))))), ?_, mem10, ?_, ?_, ?_⟩
  · rw [pc10, k9 ra (by decide), k8 ra (by decide), k7 ra (by decide), k6 ra (by decide), k5 ra (by decide),
      k4 ra (by decide), k3 ra (by decide), v2, add_lit_zero]
  · rw [regs10, u9.regs, upd_same (by decide), back sp (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), I.keep sp rfl, hVsp]
    show sp0 + 0xFFFFFCB0 + 0x350 = sp0
    rw [BitVec.add_assoc]; exact BitVec.add_zero _
  · intro r c h
    rw [regs10]
    simp only [a3Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide),
        k4 _ (by decide), k3 _ (by decide), v2]
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide),
        k4 _ (by decide), v3]
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), v4]
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), v5]
    · rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), v6]
    · rw [k9 _ (by decide), k8 _ (by decide), v7]
    · rw [k9 _ (by decide), v8]
  · intro q hq hsp' h8 h9 h18 h19 h20 h21
    rw [regs10, k9 q hsp', back q (bkeep_ne hq (show d3Keep a0 = false from rfl))
      (bkeep_ne hq (show d3Keep ra = false from rfl)) h8 h9 h18 h19 h20 h21]
    exact I.keep q hq

/-- Complete point addition for `a = -3` (Renes, Costello, and Batina 2015,
algorithm 4), in the order of `primeorder`'s `add_assign`, over the field
operations modulo P-384's `p` in Montgomery form: `b` is the curve constant. -/
def p3Add (b x1 y1 z1 x2 y2 z2 : Nat) : Nat × Nat × Nat :=
  let xx := p3fm x1 x2
  let yy := p3fm y1 y2
  let zz := p3fm z1 z2
  let xyPairs := p3fs (p3fm (p3fa x1 y1) (p3fa x2 y2)) (p3fa xx yy)
  let yzPairs := p3fs (p3fm (p3fa y1 z1) (p3fa y2 z2)) (p3fa yy zz)
  let xzPairs := p3fs (p3fm (p3fa x1 z1) (p3fa x2 z2)) (p3fa xx zz)
  let bzzPart := p3fs xzPairs (p3fm b zz)
  let bzz3Part := p3fa (p3fd bzzPart) bzzPart
  let yyMBzz3 := p3fs yy bzz3Part
  let yyPBzz3 := p3fa yy bzz3Part
  let zz3 := p3fa (p3fd zz) zz
  let bxzPart := p3fs (p3fm b xzPairs) (p3fa zz3 xx)
  let bxz3Part := p3fa (p3fd bxzPart) bxzPart
  let xx3MZz3 := p3fs (p3fa (p3fd xx) xx) zz3
  (p3fs (p3fm yyPBzz3 xyPairs) (p3fm yzPairs bxz3Part),
   p3fa (p3fm yyPBzz3 yyMBzz3) (p3fm xx3MZz3 bxz3Part),
   p3fa (p3fm yyMBzz3 yzPairs) (p3fm xyPairs xx3MZz3))

end C3.RV32
