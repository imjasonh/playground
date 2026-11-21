import C3BootProofs.Proofs.P384Mont
import C3BootProofs.Proofs.P384Add
import C3BootProofs.Proofs.P384Sub
import C3BootProofs.Proofs.PointEnv

/-!
# Where the compiled P-384 point doubling runs, and its calls

`<ProjectivePoint<p384::NistP384> as Group>::double`, as compiled, copies the
point into a 0x450-byte frame, keeps 20 field elements there, and makes 37
calls: the field multiplication and squaring wrappers, `add`, `sub`, and
`double` on `ConstMontyForm<p384::FieldParams, 12>`, and `memcpy`. The
multiplication needs the most stack below the frame, 0xF0 bytes, so the stack
it may change is the 0x540 bytes below `sp`, which this file calls `S`; the
frame starts 0xF0 bytes into it.

`D3Inv` is what holds at each point between the calls, and the lemmas here
carry it across one call or one argument instruction, with the call's
result.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem p3pd_at_0 : fetchRel p384PtDoubleCode 0x0 = some (.aluImm .add sp sp 0xFFFFFBB0, 4) := by decide
theorem p3pd_at_4 : fetchRel p384PtDoubleCode 0x4 = some (.aluImm .add a2 sp 0x400, 4) := by decide
theorem p3pd_at_8 : fetchRel p384PtDoubleCode 0x8 = some (.store .sw a2 ra 0x4C, 4) := by decide
theorem p3pd_at_c : fetchRel p384PtDoubleCode 0xC = some (.store .sw a2 (8 : Fin 32) 0x48, 2) := by decide
theorem p3pd_at_e : fetchRel p384PtDoubleCode 0xE = some (.store .sw a2 (9 : Fin 32) 0x44, 2) := by decide
theorem p3pd_at_10 : fetchRel p384PtDoubleCode 0x10 = some (.store .sw a2 (18 : Fin 32) 0x40, 4) := by decide
theorem p3pd_at_14 : fetchRel p384PtDoubleCode 0x14 = some (.store .sw a2 (19 : Fin 32) 0x3C, 4) := by decide
theorem p3pd_at_18 : fetchRel p384PtDoubleCode 0x18 = some (.store .sw a2 (20 : Fin 32) 0x38, 4) := by decide
theorem p3pd_at_1c : fetchRel p384PtDoubleCode 0x1C = some (.store .sw a2 (21 : Fin 32) 0x34, 4) := by decide
theorem p3pd_at_20 : fetchRel p384PtDoubleCode 0x20 = some (.store .sw a2 (22 : Fin 32) 0x30, 4) := by decide
theorem p3pd_at_24 : fetchRel p384PtDoubleCode 0x24 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem p3pd_at_26 : fetchRel p384PtDoubleCode 0x26 = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem p3pd_at_28 : fetchRel p384PtDoubleCode 0x28 = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem p3pd_at_2a : fetchRel p384PtDoubleCode 0x2A = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem p3pd_at_2e : fetchRel p384PtDoubleCode 0x2E = some (.auipc ra 0x13000, 4) := by decide
theorem p3pd_at_32 : fetchRel p384PtDoubleCode 0x32 = some (.jalr ra ra 0xFFFFFC26, 4) := by decide
theorem p3pd_at_36 : fetchRel p384PtDoubleCode 0x36 = some (.aluImm .add a0 sp 0xA0, 2) := by decide
theorem p3pd_at_38 : fetchRel p384PtDoubleCode 0x38 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem p3pd_at_3a : fetchRel p384PtDoubleCode 0x3A = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_3e : fetchRel p384PtDoubleCode 0x3E = some (.jalr ra ra 0x3EC, 4) := by decide
theorem p3pd_at_42 : fetchRel p384PtDoubleCode 0x42 = some (.aluImm .add (18 : Fin 32) sp 0x40, 4) := by decide
theorem p3pd_at_46 : fetchRel p384PtDoubleCode 0x46 = some (.aluImm .add a0 sp 0xD0, 2) := by decide
theorem p3pd_at_48 : fetchRel p384PtDoubleCode 0x48 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem p3pd_at_4a : fetchRel p384PtDoubleCode 0x4A = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_4e : fetchRel p384PtDoubleCode 0x4E = some (.jalr ra ra 0x3DC, 4) := by decide
theorem p3pd_at_52 : fetchRel p384PtDoubleCode 0x52 = some (.aluImm .add (19 : Fin 32) sp 0x70, 4) := by decide
theorem p3pd_at_56 : fetchRel p384PtDoubleCode 0x56 = some (.aluImm .add a0 sp 0x190, 2) := by decide
theorem p3pd_at_58 : fetchRel p384PtDoubleCode 0x58 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem p3pd_at_5a : fetchRel p384PtDoubleCode 0x5A = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_5e : fetchRel p384PtDoubleCode 0x5E = some (.jalr ra ra 0x3CC, 4) := by decide
theorem p3pd_at_62 : fetchRel p384PtDoubleCode 0x62 = some (.aluImm .add (22 : Fin 32) (9 : Fin 32) 0x30, 4) := by decide
theorem p3pd_at_66 : fetchRel p384PtDoubleCode 0x66 = some (.aluImm .add a0 sp 0x3A0, 2) := by decide
theorem p3pd_at_68 : fetchRel p384PtDoubleCode 0x68 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem p3pd_at_6a : fetchRel p384PtDoubleCode 0x6A = some (.alu .add a2 x0 (22 : Fin 32), 2) := by decide
theorem p3pd_at_6c : fetchRel p384PtDoubleCode 0x6C = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_70 : fetchRel p384PtDoubleCode 0x70 = some (.jalr ra ra 0xFFFFFC16, 4) := by decide
theorem p3pd_at_74 : fetchRel p384PtDoubleCode 0x74 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem p3pd_at_76 : fetchRel p384PtDoubleCode 0x76 = some (.aluImm .add a1 sp 0x3A0, 2) := by decide
theorem p3pd_at_78 : fetchRel p384PtDoubleCode 0x78 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_7c : fetchRel p384PtDoubleCode 0x7C = some (.jalr ra ra 0x2E6, 4) := by decide
theorem p3pd_at_80 : fetchRel p384PtDoubleCode 0x80 = some (.aluImm .add (8 : Fin 32) (9 : Fin 32) 0x60, 4) := by decide
theorem p3pd_at_84 : fetchRel p384PtDoubleCode 0x84 = some (.aluImm .add a0 sp 0x3A0, 2) := by decide
theorem p3pd_at_86 : fetchRel p384PtDoubleCode 0x86 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem p3pd_at_88 : fetchRel p384PtDoubleCode 0x88 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem p3pd_at_8a : fetchRel p384PtDoubleCode 0x8A = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_8e : fetchRel p384PtDoubleCode 0x8E = some (.jalr ra ra 0xFFFFFBF8, 4) := by decide
theorem p3pd_at_92 : fetchRel p384PtDoubleCode 0x92 = some (.aluImm .add a0 sp 0x130, 2) := by decide
theorem p3pd_at_94 : fetchRel p384PtDoubleCode 0x94 = some (.aluImm .add a1 sp 0x3A0, 2) := by decide
theorem p3pd_at_96 : fetchRel p384PtDoubleCode 0x96 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_9a : fetchRel p384PtDoubleCode 0x9A = some (.jalr ra ra 0x2C8, 4) := by decide
theorem p3pd_at_9e : fetchRel p384PtDoubleCode 0x9E = some (.lui (21 : Fin 32) 0x3FCC4000, 4) := by decide
theorem p3pd_at_a2 : fetchRel p384PtDoubleCode 0xA2 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x234, 4) := by decide
theorem p3pd_at_a6 : fetchRel p384PtDoubleCode 0xA6 = some (.aluImm .add a0 sp 0x3A0, 2) := by decide
theorem p3pd_at_a8 : fetchRel p384PtDoubleCode 0xA8 = some (.aluImm .add a2 sp 0x190, 2) := by decide
theorem p3pd_at_aa : fetchRel p384PtDoubleCode 0xAA = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem p3pd_at_ac : fetchRel p384PtDoubleCode 0xAC = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_b0 : fetchRel p384PtDoubleCode 0xB0 = some (.jalr ra ra 0xFFFFFBD6, 4) := by decide
theorem p3pd_at_b4 : fetchRel p384PtDoubleCode 0xB4 = some (.aluImm .add a0 sp 0x160, 2) := by decide
theorem p3pd_at_b6 : fetchRel p384PtDoubleCode 0xB6 = some (.aluImm .add a1 sp 0x3A0, 2) := by decide
theorem p3pd_at_b8 : fetchRel p384PtDoubleCode 0xB8 = some (.aluImm .add a2 sp 0x130, 2) := by decide
theorem p3pd_at_ba : fetchRel p384PtDoubleCode 0xBA = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_be : fetchRel p384PtDoubleCode 0xBE = some (.jalr ra ra 0x596, 4) := by decide
theorem p3pd_at_c2 : fetchRel p384PtDoubleCode 0xC2 = some (.aluImm .add a0 sp 0x3A0, 2) := by decide
theorem p3pd_at_c4 : fetchRel p384PtDoubleCode 0xC4 = some (.aluImm .add a1 sp 0x160, 2) := by decide
theorem p3pd_at_c6 : fetchRel p384PtDoubleCode 0xC6 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_ca : fetchRel p384PtDoubleCode 0xCA = some (.jalr ra ra 0x298, 4) := by decide
theorem p3pd_at_ce : fetchRel p384PtDoubleCode 0xCE = some (.aluImm .add a0 sp 0x340, 2) := by decide
theorem p3pd_at_d0 : fetchRel p384PtDoubleCode 0xD0 = some (.aluImm .add a1 sp 0x3A0, 2) := by decide
theorem p3pd_at_d2 : fetchRel p384PtDoubleCode 0xD2 = some (.aluImm .add a2 sp 0x160, 2) := by decide
theorem p3pd_at_d4 : fetchRel p384PtDoubleCode 0xD4 = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_d8 : fetchRel p384PtDoubleCode 0xD8 = some (.jalr ra ra 0x466, 4) := by decide
theorem p3pd_at_dc : fetchRel p384PtDoubleCode 0xDC = some (.aluImm .add a0 sp 0x370, 2) := by decide
theorem p3pd_at_de : fetchRel p384PtDoubleCode 0xDE = some (.aluImm .add a1 sp 0xD0, 2) := by decide
theorem p3pd_at_e0 : fetchRel p384PtDoubleCode 0xE0 = some (.aluImm .add a2 sp 0x340, 2) := by decide
theorem p3pd_at_e2 : fetchRel p384PtDoubleCode 0xE2 = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_e6 : fetchRel p384PtDoubleCode 0xE6 = some (.jalr ra ra 0x56E, 4) := by decide
theorem p3pd_at_ea : fetchRel p384PtDoubleCode 0xEA = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p3pd_at_ec : fetchRel p384PtDoubleCode 0xEC = some (.aluImm .add a1 sp 0xD0, 2) := by decide
theorem p3pd_at_ee : fetchRel p384PtDoubleCode 0xEE = some (.aluImm .add a2 sp 0x340, 2) := by decide
theorem p3pd_at_f0 : fetchRel p384PtDoubleCode 0xF0 = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_f4 : fetchRel p384PtDoubleCode 0xF4 = some (.jalr ra ra 0x44A, 4) := by decide
theorem p3pd_at_f8 : fetchRel p384PtDoubleCode 0xF8 = some (.aluImm .add a0 sp 0x1F0, 2) := by decide
theorem p3pd_at_fa : fetchRel p384PtDoubleCode 0xFA = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p3pd_at_fc : fetchRel p384PtDoubleCode 0xFC = some (.aluImm .add a2 sp 0x370, 2) := by decide
theorem p3pd_at_fe : fetchRel p384PtDoubleCode 0xFE = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_102 : fetchRel p384PtDoubleCode 0x102 = some (.jalr ra ra 0xFFFFFB84, 4) := by decide
theorem p3pd_at_106 : fetchRel p384PtDoubleCode 0x106 = some (.aluImm .add a0 sp 0x220, 2) := by decide
theorem p3pd_at_108 : fetchRel p384PtDoubleCode 0x108 = some (.aluImm .add a1 sp 0x370, 2) := by decide
theorem p3pd_at_10a : fetchRel p384PtDoubleCode 0x10A = some (.aluImm .add a2 sp 0x100, 2) := by decide
theorem p3pd_at_10c : fetchRel p384PtDoubleCode 0x10C = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_110 : fetchRel p384PtDoubleCode 0x110 = some (.jalr ra ra 0xFFFFFB76, 4) := by decide
theorem p3pd_at_114 : fetchRel p384PtDoubleCode 0x114 = some (.aluImm .add a0 sp 0x310, 2) := by decide
theorem p3pd_at_116 : fetchRel p384PtDoubleCode 0x116 = some (.aluImm .add a1 sp 0x190, 2) := by decide
theorem p3pd_at_118 : fetchRel p384PtDoubleCode 0x118 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_11c : fetchRel p384PtDoubleCode 0x11C = some (.jalr ra ra 0x246, 4) := by decide
theorem p3pd_at_120 : fetchRel p384PtDoubleCode 0x120 = some (.aluImm .add a0 sp 0x3A0, 2) := by decide
theorem p3pd_at_122 : fetchRel p384PtDoubleCode 0x122 = some (.aluImm .add a1 sp 0x310, 2) := by decide
theorem p3pd_at_124 : fetchRel p384PtDoubleCode 0x124 = some (.aluImm .add a2 sp 0x190, 2) := by decide
theorem p3pd_at_126 : fetchRel p384PtDoubleCode 0x126 = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_12a : fetchRel p384PtDoubleCode 0x12A = some (.jalr ra ra 0x414, 4) := by decide
theorem p3pd_at_12e : fetchRel p384PtDoubleCode 0x12E = some (.aluImm .add a0 sp 0x2E0, 2) := by decide
theorem p3pd_at_130 : fetchRel p384PtDoubleCode 0x130 = some (.aluImm .add a2 sp 0x130, 2) := by decide
theorem p3pd_at_132 : fetchRel p384PtDoubleCode 0x132 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem p3pd_at_134 : fetchRel p384PtDoubleCode 0x134 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_138 : fetchRel p384PtDoubleCode 0x138 = some (.jalr ra ra 0xFFFFFB4E, 4) := by decide
theorem p3pd_at_13c : fetchRel p384PtDoubleCode 0x13C = some (.aluImm .add a0 sp 0x310, 2) := by decide
theorem p3pd_at_13e : fetchRel p384PtDoubleCode 0x13E = some (.aluImm .add a1 sp 0x3A0, 2) := by decide
theorem p3pd_at_140 : fetchRel p384PtDoubleCode 0x140 = some (.aluImm .add a2 sp 0xA0, 2) := by decide
theorem p3pd_at_142 : fetchRel p384PtDoubleCode 0x142 = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_146 : fetchRel p384PtDoubleCode 0x146 = some (.jalr ra ra 0x3F8, 4) := by decide
theorem p3pd_at_14a : fetchRel p384PtDoubleCode 0x14A = some (.aluImm .add a0 sp 0x250, 2) := by decide
theorem p3pd_at_14c : fetchRel p384PtDoubleCode 0x14C = some (.aluImm .add a1 sp 0x2E0, 2) := by decide
theorem p3pd_at_14e : fetchRel p384PtDoubleCode 0x14E = some (.aluImm .add a2 sp 0x310, 2) := by decide
theorem p3pd_at_150 : fetchRel p384PtDoubleCode 0x150 = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_154 : fetchRel p384PtDoubleCode 0x154 = some (.jalr ra ra 0x500, 4) := by decide
theorem p3pd_at_158 : fetchRel p384PtDoubleCode 0x158 = some (.aluImm .add a0 sp 0x310, 2) := by decide
theorem p3pd_at_15a : fetchRel p384PtDoubleCode 0x15A = some (.aluImm .add a1 sp 0x250, 2) := by decide
theorem p3pd_at_15c : fetchRel p384PtDoubleCode 0x15C = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_160 : fetchRel p384PtDoubleCode 0x160 = some (.jalr ra ra 0x202, 4) := by decide
theorem p3pd_at_164 : fetchRel p384PtDoubleCode 0x164 = some (.aluImm .add a0 sp 0x3D0, 2) := by decide
theorem p3pd_at_166 : fetchRel p384PtDoubleCode 0x166 = some (.aluImm .add a1 sp 0x310, 2) := by decide
theorem p3pd_at_168 : fetchRel p384PtDoubleCode 0x168 = some (.aluImm .add a2 sp 0x250, 2) := by decide
theorem p3pd_at_16a : fetchRel p384PtDoubleCode 0x16A = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_16e : fetchRel p384PtDoubleCode 0x16E = some (.jalr ra ra 0x3D0, 4) := by decide
theorem p3pd_at_172 : fetchRel p384PtDoubleCode 0x172 = some (.aluImm .add a0 sp 0x310, 2) := by decide
theorem p3pd_at_174 : fetchRel p384PtDoubleCode 0x174 = some (.aluImm .add a1 sp 0xA0, 2) := by decide
theorem p3pd_at_176 : fetchRel p384PtDoubleCode 0x176 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_17a : fetchRel p384PtDoubleCode 0x17A = some (.jalr ra ra 0x1E8, 4) := by decide
theorem p3pd_at_17e : fetchRel p384PtDoubleCode 0x17E = some (.aluImm .add a0 sp 0x2E0, 2) := by decide
theorem p3pd_at_180 : fetchRel p384PtDoubleCode 0x180 = some (.aluImm .add a1 sp 0x310, 2) := by decide
theorem p3pd_at_182 : fetchRel p384PtDoubleCode 0x182 = some (.aluImm .add a2 sp 0xA0, 2) := by decide
theorem p3pd_at_184 : fetchRel p384PtDoubleCode 0x184 = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_188 : fetchRel p384PtDoubleCode 0x188 = some (.jalr ra ra 0x3B6, 4) := by decide
theorem p3pd_at_18c : fetchRel p384PtDoubleCode 0x18C = some (.aluImm .add a0 sp 0x280, 2) := by decide
theorem p3pd_at_18e : fetchRel p384PtDoubleCode 0x18E = some (.aluImm .add a1 sp 0x2E0, 2) := by decide
theorem p3pd_at_190 : fetchRel p384PtDoubleCode 0x190 = some (.aluImm .add a2 sp 0x3A0, 2) := by decide
theorem p3pd_at_192 : fetchRel p384PtDoubleCode 0x192 = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_196 : fetchRel p384PtDoubleCode 0x196 = some (.jalr ra ra 0x4BE, 4) := by decide
theorem p3pd_at_19a : fetchRel p384PtDoubleCode 0x19A = some (.aluImm .add a0 sp 0x310, 2) := by decide
theorem p3pd_at_19c : fetchRel p384PtDoubleCode 0x19C = some (.aluImm .add a1 sp 0x280, 2) := by decide
theorem p3pd_at_19e : fetchRel p384PtDoubleCode 0x19E = some (.aluImm .add a2 sp 0x3D0, 2) := by decide
theorem p3pd_at_1a0 : fetchRel p384PtDoubleCode 0x1A0 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_1a4 : fetchRel p384PtDoubleCode 0x1A4 = some (.jalr ra ra 0xFFFFFAE2, 4) := by decide
theorem p3pd_at_1a8 : fetchRel p384PtDoubleCode 0x1A8 = some (.aluImm .add a0 sp 0x2B0, 2) := by decide
theorem p3pd_at_1aa : fetchRel p384PtDoubleCode 0x1AA = some (.aluImm .add a1 sp 0x1F0, 2) := by decide
theorem p3pd_at_1ac : fetchRel p384PtDoubleCode 0x1AC = some (.aluImm .add a2 sp 0x310, 2) := by decide
theorem p3pd_at_1ae : fetchRel p384PtDoubleCode 0x1AE = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_1b2 : fetchRel p384PtDoubleCode 0x1B2 = some (.jalr ra ra 0x38C, 4) := by decide
theorem p3pd_at_1b6 : fetchRel p384PtDoubleCode 0x1B6 = some (.aluImm .add a0 sp 0x310, 2) := by decide
theorem p3pd_at_1b8 : fetchRel p384PtDoubleCode 0x1B8 = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem p3pd_at_1ba : fetchRel p384PtDoubleCode 0x1BA = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem p3pd_at_1bc : fetchRel p384PtDoubleCode 0x1BC = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_1c0 : fetchRel p384PtDoubleCode 0x1C0 = some (.jalr ra ra 0xFFFFFAC6, 4) := by decide
theorem p3pd_at_1c4 : fetchRel p384PtDoubleCode 0x1C4 = some (.aluImm .add a0 sp 0x400, 4) := by decide
theorem p3pd_at_1c8 : fetchRel p384PtDoubleCode 0x1C8 = some (.aluImm .add a1 sp 0x310, 2) := by decide
theorem p3pd_at_1ca : fetchRel p384PtDoubleCode 0x1CA = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_1ce : fetchRel p384PtDoubleCode 0x1CE = some (.jalr ra ra 0x194, 4) := by decide
theorem p3pd_at_1d2 : fetchRel p384PtDoubleCode 0x1D2 = some (.aluImm .add a0 sp 0x310, 2) := by decide
theorem p3pd_at_1d4 : fetchRel p384PtDoubleCode 0x1D4 = some (.aluImm .add a1 sp 0x3D0, 2) := by decide
theorem p3pd_at_1d6 : fetchRel p384PtDoubleCode 0x1D6 = some (.aluImm .add a2 sp 0x400, 4) := by decide
theorem p3pd_at_1da : fetchRel p384PtDoubleCode 0x1DA = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_1de : fetchRel p384PtDoubleCode 0x1DE = some (.jalr ra ra 0xFFFFFAA8, 4) := by decide
theorem p3pd_at_1e2 : fetchRel p384PtDoubleCode 0x1E2 = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem p3pd_at_1e4 : fetchRel p384PtDoubleCode 0x1E4 = some (.aluImm .add a1 sp 0x220, 2) := by decide
theorem p3pd_at_1e6 : fetchRel p384PtDoubleCode 0x1E6 = some (.aluImm .add a2 sp 0x310, 2) := by decide
theorem p3pd_at_1e8 : fetchRel p384PtDoubleCode 0x1E8 = some (.auipc ra 0x0, 4) := by decide
theorem p3pd_at_1ec : fetchRel p384PtDoubleCode 0x1EC = some (.jalr ra ra 0x468, 4) := by decide
theorem p3pd_at_1f0 : fetchRel p384PtDoubleCode 0x1F0 = some (.aluImm .add a0 sp 0x310, 2) := by decide
theorem p3pd_at_1f2 : fetchRel p384PtDoubleCode 0x1F2 = some (.aluImm .add a1 sp 0x400, 4) := by decide
theorem p3pd_at_1f6 : fetchRel p384PtDoubleCode 0x1F6 = some (.aluImm .add a2 sp 0xD0, 2) := by decide
theorem p3pd_at_1f8 : fetchRel p384PtDoubleCode 0x1F8 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_1fc : fetchRel p384PtDoubleCode 0x1FC = some (.jalr ra ra 0xFFFFFA8A, 4) := by decide
theorem p3pd_at_200 : fetchRel p384PtDoubleCode 0x200 = some (.aluImm .add a0 sp 0x2E0, 2) := by decide
theorem p3pd_at_202 : fetchRel p384PtDoubleCode 0x202 = some (.aluImm .add a1 sp 0x310, 2) := by decide
theorem p3pd_at_204 : fetchRel p384PtDoubleCode 0x204 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_208 : fetchRel p384PtDoubleCode 0x208 = some (.jalr ra ra 0x15A, 4) := by decide
theorem p3pd_at_20c : fetchRel p384PtDoubleCode 0x20C = some (.aluImm .add a1 sp 0x2E0, 2) := by decide
theorem p3pd_at_20e : fetchRel p384PtDoubleCode 0x20E = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem p3pd_at_210 : fetchRel p384PtDoubleCode 0x210 = some (.auipc ra 0x12000, 4) := by decide
theorem p3pd_at_214 : fetchRel p384PtDoubleCode 0x214 = some (.jalr ra ra 0x14E, 4) := by decide
theorem p3pd_at_218 : fetchRel p384PtDoubleCode 0x218 = some (.aluImm .add a1 sp 0x2B0, 2) := by decide
theorem p3pd_at_21a : fetchRel p384PtDoubleCode 0x21A = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem p3pd_at_21e : fetchRel p384PtDoubleCode 0x21E = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem p3pd_at_220 : fetchRel p384PtDoubleCode 0x220 = some (.auipc ra 0x13000, 4) := by decide
theorem p3pd_at_224 : fetchRel p384PtDoubleCode 0x224 = some (.jalr ra ra 0xFFFFFA34, 4) := by decide
theorem p3pd_at_228 : fetchRel p384PtDoubleCode 0x228 = some (.aluImm .add a1 sp 0x10, 2) := by decide
theorem p3pd_at_22a : fetchRel p384PtDoubleCode 0x22A = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem p3pd_at_22e : fetchRel p384PtDoubleCode 0x22E = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem p3pd_at_230 : fetchRel p384PtDoubleCode 0x230 = some (.auipc ra 0x13000, 4) := by decide
theorem p3pd_at_234 : fetchRel p384PtDoubleCode 0x234 = some (.jalr ra ra 0xFFFFFA24, 4) := by decide
theorem p3pd_at_238 : fetchRel p384PtDoubleCode 0x238 = some (.aluImm .add a0 sp 0x400, 4) := by decide
theorem p3pd_at_23c : fetchRel p384PtDoubleCode 0x23C = some (.load .lw ra a0 0x4C, 4) := by decide
theorem p3pd_at_240 : fetchRel p384PtDoubleCode 0x240 = some (.load .lw (8 : Fin 32) a0 0x48, 2) := by decide
theorem p3pd_at_242 : fetchRel p384PtDoubleCode 0x242 = some (.load .lw (9 : Fin 32) a0 0x44, 2) := by decide
theorem p3pd_at_244 : fetchRel p384PtDoubleCode 0x244 = some (.load .lw (18 : Fin 32) a0 0x40, 4) := by decide
theorem p3pd_at_248 : fetchRel p384PtDoubleCode 0x248 = some (.load .lw (19 : Fin 32) a0 0x3C, 4) := by decide
theorem p3pd_at_24c : fetchRel p384PtDoubleCode 0x24C = some (.load .lw (20 : Fin 32) a0 0x38, 4) := by decide
theorem p3pd_at_250 : fetchRel p384PtDoubleCode 0x250 = some (.load .lw (21 : Fin 32) a0 0x34, 4) := by decide
theorem p3pd_at_254 : fetchRel p384PtDoubleCode 0x254 = some (.load .lw (22 : Fin 32) a0 0x30, 4) := by decide
theorem p3pd_at_258 : fetchRel p384PtDoubleCode 0x258 = some (.aluImm .add sp sp 0x450, 4) := by decide
theorem p3pd_at_25c : fetchRel p384PtDoubleCode 0x25C = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- Where the image stores P-384's `b` in Montgomery form. -/
abbrev p3bA : Word := BitVec.ofNat 32 p384BAddress

/-- The bottom of the stack the point doubling may change. -/
abbrev d3S (sp0 : Word) : Word := sp0 + 0xFFFFFAC0

/-- The point doubling's frame. -/
abbrev d3G (sp0 : Word) : Word := sp0 + 0xFFFFFBB0

/-- `a + b`, `a - b`, and `2 a` modulo P-384's `p`. -/
def p3fa (a b : Nat) : Nat := (a + b) % p384

def p3fs (a b : Nat) : Nat := (a + p384 - b) % p384

def p3fd (a : Nat) : Nat := (a + a) % p384

theorem p3fa_lt (a b : Nat) : p3fa a b < p384 := Nat.mod_lt _ p384_pos

theorem p3fs_lt (a b : Nat) : p3fs a b < p384 := Nat.mod_lt _ p384_pos

theorem p3fd_lt (a : Nat) : p3fd a < p384 := Nat.mod_lt _ p384_pos

/-- Where the point doubling runs: its code at `P`, its callees and theirs
where the image puts them, the modulus and `b`, the point at `sf` and the
result at `out`, each 144 bytes and aligned, and the 0x540 bytes of stack
below `sp0` apart from the code, the constants, the point, and the result.
The result's writes keep `out` apart from the code they could reach. -/
structure D3Env (M : Word → BitVec 8) (P sp0 out sf : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384PtDoubleCode
  mulw : CodeIn M (P + 0x11C82) p384MulCode
  sqw : CodeIn M (P + 0x12426) p384SqrCode
  mm : CodeIn M (P + 0x110E0) mulMont12Code
  sq : CodeIn M (P + 0x11D8E) sqMont12Code
  add : CodeIn M (P + 0x53A) p384AddCode
  sub : CodeIn M (P + 0x650) p384SubCode
  dbl : CodeIn M (P + 0x1235E) p384DoubleCode
  mset : CodeIn M (P + 0x12BEC) memsetCode
  bsub : CodeIn M (P + 0x726) borrowingSubCode
  sel : CodeIn M (P + 0x1126E) uintSelect12Code
  stub : CodeIn M (P + 0x12C54) memcpyStubCode
  body : CodeIn M (P + 0x12C5C) memcpyBodyCode
  pmod : CodeIn M p3M p384ModulusData
  bconst : CodeIn M p3bA p384BData
  hsp : sp0.toNat % 4 = 0
  hS : 0x540 ≤ sp0.toNat
  hsf : sf.toNat % 4 = 0
  hout : out.toNat % 4 = 0
  hwo : out.toNat + 144 < 2 ^ 32
  sC : Sep (d3S sp0) 0x540 P p384PtDoubleCode.length
  sMw : Sep (d3S sp0) 0x540 (P + 0x11C82) p384MulCode.length
  sSw : Sep (d3S sp0) 0x540 (P + 0x12426) p384SqrCode.length
  sMm : Sep (d3S sp0) 0x540 (P + 0x110E0) mulMont12Code.length
  sSq : Sep (d3S sp0) 0x540 (P + 0x11D8E) sqMont12Code.length
  sA : Sep (d3S sp0) 0x540 (P + 0x53A) p384AddCode.length
  sSb : Sep (d3S sp0) 0x540 (P + 0x650) p384SubCode.length
  sD : Sep (d3S sp0) 0x540 (P + 0x1235E) p384DoubleCode.length
  sMs : Sep (d3S sp0) 0x540 (P + 0x12BEC) memsetCode.length
  sBs : Sep (d3S sp0) 0x540 (P + 0x726) borrowingSubCode.length
  sSel : Sep (d3S sp0) 0x540 (P + 0x1126E) uintSelect12Code.length
  sU : Sep (d3S sp0) 0x540 (P + 0x12C54) memcpyStubCode.length
  sB : Sep (d3S sp0) 0x540 (P + 0x12C5C) memcpyBodyCode.length
  sP : Sep (d3S sp0) 0x540 p3M 48
  sK : Sep (d3S sp0) 0x540 p3bA 48
  sF : Sep sf 144 (d3S sp0) 0x540
  sO : Sep out 144 (d3S sp0) 0x540
  oC : Sep out 144 P p384PtDoubleCode.length
  oB : Sep out 144 (P + 0x12C5C) memcpyBodyCode.length

/-- The registers that no call or argument instruction of the point doubling
changes: all but `ra`, `t0` through `t6`, and `a0` through `a7`. -/
def d3Keep (q : Fin 32) : Bool := q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- What holds between the point doubling's calls, at offset `off`: the
registers `d3Keep` names hold `V`, memory outside `S` is as it was on entry
(`M0`), and the register save slots at the frame's top hold what they held
after the prologue (`Ms`). -/
structure D3Inv (M0 : Word → BitVec 8) (P sp0 : Word) (V : Fin 32 → Word) (Ms : Word → BitVec 8)
    (M : Word → BitVec 8) (n : Machine) (off : Nat) : Prop where
  st : St M P n off (reg n)
  keep : ∀ q, d3Keep q = true → reg n q = V q
  fr : ∀ x, Sep (d3S sp0) 0x540 x 1 → M x = M0 x
  sv : ∀ c, 0x430 ≤ c → c < 0x450 → M (d3G sp0 + BitVec.ofNat 32 c) = Ms (d3G sp0 + BitVec.ofNat 32 c)

/-- An operand a call may read: aligned, and apart from the callees' stack. -/
def D3Src (sp0 a : Word) : Prop := a.toNat % 4 = 0 ∧ Sep a 48 (d3S sp0) 0xF0

/-- A result slot in the frame: the 48 bytes at `d`, below the save slots. -/
def D3Dst (d : Nat) : Prop := 0x10 ≤ d ∧ d + 48 ≤ 0x430 ∧ d % 4 = 0

theorem d3G_S (sp0 : Word) (c : Nat) : d3G sp0 + BitVec.ofNat 32 c = d3S sp0 + BitVec.ofNat 32 (0xF0 + c) := by
  rw [← add_ofNat_assoc, show d3G sp0 = d3S sp0 + BitVec.ofNat 32 0xF0 from by
    show sp0 + 0xFFFFFBB0 = sp0 + 0xFFFFFAC0 + BitVec.ofNat 32 0xF0
    rw [BitVec.add_assoc]; rfl]

theorem d3G_mm (sp0 : Word) : d3G sp0 + 0xFFFFFF10 = d3S sp0 := by
  show sp0 + 0xFFFFFBB0 + 0xFFFFFF10 = sp0 + 0xFFFFFAC0
  rw [BitVec.add_assoc]; rfl

theorem d3G_ad (sp0 : Word) : d3G sp0 + 0xFFFFFF4C = d3S sp0 + BitVec.ofNat 32 0x3C := by
  show sp0 + 0xFFFFFBB0 + 0xFFFFFF4C = sp0 + 0xFFFFFAC0 + BitVec.ofNat 32 0x3C
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem d3G_db (sp0 : Word) : d3G sp0 + 0xFFFFFF30 = d3S sp0 + BitVec.ofNat 32 0x20 := by
  show sp0 + 0xFFFFFBB0 + 0xFFFFFF30 = sp0 + 0xFFFFFAC0 + BitVec.ofNat 32 0x20
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

section
variable {M0 : Word → BitVec 8} {P sp0 out sf : Word}

theorem D3Env.hSw (env : D3Env M0 P sp0 out sf) : (d3S sp0).toNat = sp0.toNat - 0x540 := by
  have := env.hS
  show (sp0 + 0xFFFFFAC0).toNat = _
  rw [BitVec.toNat_add]; have : (0xFFFFFAC0 : Word).toNat = 4294965952 := rfl
  have := sp0.isLt; omega

theorem D3Env.hGw (env : D3Env M0 P sp0 out sf) : (d3G sp0).toNat = sp0.toNat - 0x450 := by
  have := env.hS
  show (sp0 + 0xFFFFFBB0).toNat = _
  rw [BitVec.toNat_add]; have : (0xFFFFFBB0 : Word).toNat = 4294966192 := rfl
  have := sp0.isLt; omega

theorem D3Env.hGa (env : D3Env M0 P sp0 out sf) : (d3G sp0).toNat % 4 = 0 :=
  aligned_add env.hsp (k := 0xFFFFFBB0) (by decide)

theorem D3Env.hSa (env : D3Env M0 P sp0 out sf) : (d3S sp0).toNat % 4 = 0 :=
  aligned_add env.hsp (k := 0xFFFFFAC0) (by decide)

/-- Code apart from `S` is still there. -/
theorem D3Env.codeT (_env : D3Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d3S sp0) 0x540 x 1 → M x = M0 x)
    {b : Word} {code : List Nat} (hc : CodeIn M0 b code) (hs : Sep (d3S sp0) 0x540 b code.length) :
    CodeIn M b code := fun i hi => by
  rw [fr _ (hs.subR (c := i) (l := 1) (by omega))]
  exact hc i hi

theorem sS_sub {b : Word} {k c l : Nat} (h : Sep (d3S sp0) 0x540 b k) (hcl : c + l ≤ 0x540) :
    Sep (d3S sp0 + BitVec.ofNat 32 c) l b k := h.sub hcl

theorem sS_mm {b : Word} {k : Nat} (h : Sep (d3S sp0) 0x540 b k) : Sep (d3G sp0 + 0xFFFFFF10) 0xF0 b k := by
  rw [d3G_mm]; exact sep_base0 (h.sub (c := 0) (l := 0xF0) (by decide))

theorem sS_ad {b : Word} {k : Nat} (h : Sep (d3S sp0) 0x540 b k) : Sep (d3G sp0 + 0xFFFFFF4C) 0xB4 b k := by
  rw [d3G_ad]; exact h.sub (c := 0x3C) (l := 0xB4) (by decide)

theorem sS_db {b : Word} {k : Nat} (h : Sep (d3S sp0) 0x540 b k) : Sep (d3G sp0 + 0xFFFFFF30) 0xD0 b k := by
  rw [d3G_db]; exact h.sub (c := 0x20) (l := 0xD0) (by decide)

theorem D3Dst.al {d : Nat} (env : D3Env M0 P sp0 out sf) (hd : D3Dst d) :
    (d3G sp0 + BitVec.ofNat 32 d).toNat % 4 = 0 := aligned_add env.hGa hd.2.2

theorem D3Dst.wr {d : Nat} (env : D3Env M0 P sp0 out sf) (hd : D3Dst d) :
    (d3G sp0 + BitVec.ofNat 32 d).toNat + 48 < 2 ^ 32 := by
  have := env.hGw; have := env.hS; have := sp0.isLt; have := hd.2.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A result slot is apart from the callees' stack. -/
theorem D3Dst.sS {d : Nat} (hd : D3Dst d) : Sep (d3G sp0 + BitVec.ofNat 32 d) 48 (d3S sp0) 0xF0 := by
  rw [d3G_S]
  exact sep_base0r (sep_offsets _ (c := 0xF0 + d) (n := 48) (d := 0) (k := 0xF0) (.inr (by omega))
    (by have := hd.2.1; omega) (by decide))

theorem D3Dst.inS {d : Nat} (hd : D3Dst d) {b : Word} {k : Nat} (h : Sep (d3S sp0) 0x540 b k) :
    Sep (d3G sp0 + BitVec.ofNat 32 d) 48 b k := by
  rw [d3G_S]; exact h.sub (c := 0xF0 + d) (l := 48) (by have := hd.2.1; omega)

theorem D3Dst.inS' {d : Nat} (hd : D3Dst d) {b : Word} {k : Nat} (h : Sep b k (d3S sp0) 0x540) :
    Sep b k (d3G sp0 + BitVec.ofNat 32 d) 48 := (hd.inS h.symm).symm

/-- A frame slot below the save slots is an operand. -/
theorem d3src_slot {d : Nat} (env : D3Env M0 P sp0 out sf) (hd : D3Dst d) :
    D3Src sp0 (d3G sp0 + BitVec.ofNat 32 d) := ⟨hd.al env, hd.sS⟩

/-- A coordinate of the point is an operand. -/
theorem d3src_sf (env : D3Env M0 P sp0 out sf) (k : Nat) (hk : k + 48 ≤ 144) (hk4 : k % 4 = 0) :
    D3Src sp0 (sf + BitVec.ofNat 32 k) :=
  ⟨aligned_add env.hsf hk4, sep_base0r ((env.sF.sub (c := k) (l := 48) hk).subR (c := 0) (l := 0xF0) (by decide))⟩

/-- `b` is an operand. -/
theorem d3src_b (env : D3Env M0 P sp0 out sf) : D3Src sp0 p3bA :=
  ⟨by decide, sep_base0r (env.sK.symm.subR (c := 0) (l := 0xF0) (by decide))⟩

theorem D3Src.sub' {a : Word} (h : D3Src sp0 a) : Sep a 48 (d3G sp0 + 0xFFFFFF10) 0xF0 := by
  rw [d3G_mm]; exact h.2

theorem D3Src.ad {a : Word} (h : D3Src sp0 a) : Sep a 48 (d3G sp0 + 0xFFFFFF4C) 0xB4 := by
  rw [d3G_ad]; exact h.2.subR (c := 0x3C) (l := 0xB4) (by decide)

theorem D3Src.db {a : Word} (h : D3Src sp0 a) : Sep a 48 (d3G sp0 + 0xFFFFFF30) 0xD0 := by
  rw [d3G_db]; exact h.2.subR (c := 0x20) (l := 0xD0) (by decide)

theorem d3_ret_even (env : D3Env M0 P sp0 out sf) {off : Nat} (hoff : off % 2 = 0) :
    (P + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = P + BitVec.ofNat 32 (off + 8) :=
  even_clear _ (even_at P env.hP (off + 8) (by omega))

theorem d3_hS_mm (env : D3Env M0 P sp0 out sf) : 0xF0 ≤ (d3G sp0).toNat := by
  have := env.hGw; have := env.hS; omega

/-- The multiplication wrapper's environment, for a call from the point
doubling with its result in the frame. -/
theorem D3Env.mEnv (env : D3Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d3S sp0) 0x540 x 1 → M x = M0 x) {d : Nat} {a b : Word}
    (hd : D3Dst d) (sa : D3Src sp0 a) (sb : D3Src sp0 b) :
    P3MEnv M (P + 0x11C82) (d3G sp0) (d3G sp0 + BitVec.ofNat 32 d) a b := by
  have cT := @D3Env.codeT _ _ _ _ _ env M fr
  have e0 : P + 0x11C82 + 0xFFFFF45E = P + 0x110E0 := by rw [BitVec.add_assoc]; rfl
  have e1 : P + 0x110E0 + 0x1B0C = P + 0x12BEC := by rw [BitVec.add_assoc]; rfl
  have e2 : mmBsub (P + 0x110E0) = P + 0x726 := by show P + 0x110E0 + 0xFFFEF646 = _; rw [BitVec.add_assoc]; rfl
  have e3 : P + 0x110E0 + 0x18E = P + 0x1126E := by rw [BitVec.add_assoc]; rfl
  have e4 : P + 0x110E0 + 0x1B74 = P + 0x12C54 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0x110E0 + 0x1B7C = P + 0x12C5C := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0x11C82 (by decide), cT env.mulw env.sMw, cT env.pmod env.sP, ?_⟩
  rw [e0]
  refine ⟨even_at P env.hP 0x110E0 (by decide), cT env.mm env.sMm, by rw [e1]; exact cT env.mset env.sMs,
    by rw [e2]; exact cT env.bsub env.sBs, by rw [e3]; exact cT env.sel env.sSel,
    by rw [e4]; exact cT env.stub env.sU, by rw [e5]; exact cT env.body env.sB,
    env.hGa, d3_hS_mm env, hd.al env, sa.1, sb.1, by decide, hd.wr env,
    sS_mm env.sMm, by rw [e1]; exact sS_mm env.sMs, by rw [e2]; exact sS_mm env.sBs,
    by rw [e3]; exact sS_mm env.sSel, by rw [e4]; exact sS_mm env.sU, by rw [e5]; exact sS_mm env.sB,
    by rw [d3G_mm]; exact hd.sS, hd.inS env.sMm, by rw [e3]; exact hd.inS env.sSel,
    by rw [e5]; exact hd.inS env.sB, sa.sub', sb.sub', ?_⟩
  rw [d3G_mm]; exact sep_base0r (env.sP.symm.subR (c := 0) (l := 0xF0) (by decide))

/-- The squaring wrapper's environment, for a call from the point doubling. -/
theorem D3Env.qEnv (env : D3Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d3S sp0) 0x540 x 1 → M x = M0 x) {d : Nat} {a : Word}
    (hd : D3Dst d) (sa : D3Src sp0 a) :
    P3QEnv M (P + 0x12426) (d3G sp0) (d3G sp0 + BitVec.ofNat 32 d) a := by
  have cT := @D3Env.codeT _ _ _ _ _ env M fr
  have e0 : P + 0x12426 + 0xFFFFF968 = P + 0x11D8E := by rw [BitVec.add_assoc]; rfl
  have e1 : P + 0x11D8E + 0xE5E = P + 0x12BEC := by rw [BitVec.add_assoc]; rfl
  have e2 : sqBsub (P + 0x11D8E) = P + 0x726 := by show P + 0x11D8E + 0xFFFEE998 = _; rw [BitVec.add_assoc]; rfl
  have e3 : P + 0x11D8E + 0xFFFFF4E0 = P + 0x1126E := by rw [BitVec.add_assoc]; rfl
  have e4 : P + 0x11D8E + 0xEC6 = P + 0x12C54 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0x11D8E + 0xECE = P + 0x12C5C := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0x12426 (by decide), cT env.sqw env.sSw, cT env.pmod env.sP, ?_⟩
  rw [e0]
  refine ⟨even_at P env.hP 0x11D8E (by decide), cT env.sq env.sSq, by rw [e1]; exact cT env.mset env.sMs,
    by rw [e2]; exact cT env.bsub env.sBs, by rw [e3]; exact cT env.sel env.sSel,
    by rw [e4]; exact cT env.stub env.sU, by rw [e5]; exact cT env.body env.sB,
    env.hGa, d3_hS_mm env, hd.al env, sa.1, by decide, hd.wr env,
    sS_mm env.sSq, by rw [e1]; exact sS_mm env.sMs, by rw [e2]; exact sS_mm env.sBs,
    by rw [e3]; exact sS_mm env.sSel, by rw [e4]; exact sS_mm env.sU, by rw [e5]; exact sS_mm env.sB,
    by rw [d3G_mm]; exact hd.sS, hd.inS env.sSq, by rw [e3]; exact hd.inS env.sSel,
    by rw [e5]; exact hd.inS env.sB, sa.sub', ?_⟩
  rw [d3G_mm]; exact sep_base0r (env.sP.symm.subR (c := 0) (l := 0xF0) (by decide))

theorem d3_hS_ad (env : D3Env M0 P sp0 out sf) : 0xB4 ≤ (d3G sp0).toNat := by
  have := env.hGw; have := env.hS; omega

theorem d3_hS_db (env : D3Env M0 P sp0 out sf) : 0xD0 ≤ (d3G sp0).toNat := by
  have := env.hGw; have := env.hS; omega

/-- `add`'s environment, for a call from the point doubling. -/
theorem D3Env.aEnv (env : D3Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d3S sp0) 0x540 x 1 → M x = M0 x) {d : Nat} {a b : Word}
    (hd : D3Dst d) (sa : D3Src sp0 a) (sb : D3Src sp0 b) :
    P3Env M (P + 0x53A) (d3G sp0) (d3G sp0 + BitVec.ofNat 32 d) a b := by
  have cT := @D3Env.codeT _ _ _ _ _ env M fr
  have e1 : P + 0x53A + 0x126B2 = P + 0x12BEC := by rw [BitVec.add_assoc]; rfl
  have e2 : p3Bsub (P + 0x53A) = P + 0x726 := by show P + 0x53A + 0x1EC = _; rw [BitVec.add_assoc]; rfl
  have e4 : P + 0x53A + 0x1271A = P + 0x12C54 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0x53A + 0x12722 = P + 0x12C5C := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0x53A (by decide), cT env.add env.sA, by rw [e1]; exact cT env.mset env.sMs,
    by rw [e2]; exact cT env.bsub env.sBs, by rw [e4]; exact cT env.stub env.sU,
    by rw [e5]; exact cT env.body env.sB, cT env.pmod env.sP,
    env.hGa, d3_hS_ad env, hd.al env, sa.1, sb.1, hd.wr env,
    sS_ad env.sA, by rw [e1]; exact sS_ad env.sMs, by rw [e2]; exact sS_ad env.sBs,
    by rw [e4]; exact sS_ad env.sU, by rw [e5]; exact sS_ad env.sB, sS_ad env.sP,
    hd.inS env.sA, by rw [e5]; exact hd.inS env.sB, ?_, sa.ad, sb.ad⟩
  rw [d3G_ad]; exact hd.sS.subR (c := 0x3C) (l := 0xB4) (by decide)

/-- `sub`'s environment, for a call from the point doubling. -/
theorem D3Env.sEnv (env : D3Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d3S sp0) 0x540 x 1 → M x = M0 x) {d : Nat} {a b : Word}
    (hd : D3Dst d) (sa : D3Src sp0 a) (sb : D3Src sp0 b) :
    PSEnv M (P + 0x650) (d3G sp0) (d3G sp0 + BitVec.ofNat 32 d) a b := by
  have cT := @D3Env.codeT _ _ _ _ _ env M fr
  have e1 : P + 0x650 + 0x1259C = P + 0x12BEC := by rw [BitVec.add_assoc]; rfl
  have e2 : psBsub (P + 0x650) = P + 0x726 := by show P + 0x650 + 0xD6 = _; rw [BitVec.add_assoc]; rfl
  have e4 : P + 0x650 + 0x12604 = P + 0x12C54 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0x650 + 0x1260C = P + 0x12C5C := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0x650 (by decide), cT env.sub env.sSb, by rw [e1]; exact cT env.mset env.sMs,
    by rw [e2]; exact cT env.bsub env.sBs, by rw [e4]; exact cT env.stub env.sU,
    by rw [e5]; exact cT env.body env.sB, cT env.pmod env.sP,
    env.hGa, d3_hS_ad env, hd.al env, sa.1, sb.1, hd.wr env,
    sS_ad env.sSb, by rw [e1]; exact sS_ad env.sMs, by rw [e2]; exact sS_ad env.sBs,
    by rw [e4]; exact sS_ad env.sU, by rw [e5]; exact sS_ad env.sB, sS_ad env.sP,
    hd.inS env.sSb, by rw [e5]; exact hd.inS env.sB, ?_, sa.ad, sb.ad⟩
  rw [d3G_ad]; exact hd.sS.subR (c := 0x3C) (l := 0xB4) (by decide)

/-- `double`'s environment, for a call from the point doubling. -/
theorem D3Env.dEnv (env : D3Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d3S sp0) 0x540 x 1 → M x = M0 x) {d : Nat} {a : Word}
    (hd : D3Dst d) (sa : D3Src sp0 a) :
    PDEnv M (P + 0x1235E) (d3G sp0) (d3G sp0 + BitVec.ofNat 32 d) a := by
  have cT := @D3Env.codeT _ _ _ _ _ env M fr
  have e1 : P + 0x1235E + 0x88E = P + 0x12BEC := by rw [BitVec.add_assoc]; rfl
  have e2 : pdBsub (P + 0x1235E) = P + 0x726 := by show P + 0x1235E + 0xFFFEE3C8 = _; rw [BitVec.add_assoc]; rfl
  have e3 : P + 0x1235E + 0xFFFFEF10 = P + 0x1126E := by rw [BitVec.add_assoc]; rfl
  have e4 : P + 0x1235E + 0x8F6 = P + 0x12C54 := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0x1235E + 0x8FE = P + 0x12C5C := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0x1235E (by decide), cT env.dbl env.sD, by rw [e1]; exact cT env.mset env.sMs,
    by rw [e2]; exact cT env.bsub env.sBs, by rw [e4]; exact cT env.stub env.sU,
    by rw [e5]; exact cT env.body env.sB, by rw [e3]; exact cT env.sel env.sSel, cT env.pmod env.sP,
    env.hGa, d3_hS_db env, hd.al env, sa.1, hd.wr env,
    sS_db env.sD, by rw [e1]; exact sS_db env.sMs, by rw [e2]; exact sS_db env.sBs,
    by rw [e4]; exact sS_db env.sU, by rw [e5]; exact sS_db env.sB, by rw [e3]; exact sS_db env.sSel,
    sS_db env.sP, hd.inS env.sD, by rw [e3]; exact hd.inS env.sSel, by rw [e5]; exact hd.inS env.sB, ?_, sa.db⟩
  rw [d3G_db]; exact hd.sS.subR (c := 0x20) (l := 0xD0) (by decide)

/-- The callees' stack and a result slot leave the save slots alone. -/
theorem d3sv_keep {d c : Nat} (hd : D3Dst d) (h1 : 0x430 ≤ c) (h2 : c < 0x450) :
    Sep (d3S sp0) 0xF0 (d3G sp0 + BitVec.ofNat 32 c) 1 ∧
      Sep (d3G sp0 + BitVec.ofNat 32 d) 48 (d3G sp0 + BitVec.ofNat 32 c) 1 := by
  refine ⟨?_, sep_offsets _ (.inl (by have := hd.2.1; omega)) (by have := hd.2.1; omega) (by omega)⟩
  rw [d3G_S]
  exact sep_base0 (sep_offsets _ (c := 0) (n := 0xF0) (d := 0xF0 + c) (k := 1) (.inl (by omega))
    (by decide) (by omega))

/-- After a call that changed only the callees' stack and a result slot, the
invariant holds at the return address. -/
theorem D3Inv.after {M Ms M' : Word → BitVec 8} {V : Fin 32 → Word} {d off : Nat} {n n' : Machine}
    (I : D3Inv M0 P sp0 V Ms M n off) (hd : D3Dst d)
    (st : St M' P n' (off + 8) (reg n')) (keep : ∀ q, d3Keep q = true → reg n' q = reg n q)
    (fr : ∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) :
    D3Inv M0 P sp0 V Ms M' n' (off + 8) :=
  ⟨st, fun q hq => (keep q hq).trans (I.keep q hq),
    fun x hx => (fr x (sep_base0 (hx.sub (c := 0) (l := 0xF0) (by decide))) (hd.inS hx)).trans (I.fr x hx),
    fun c h1 h2 => (fr _ (d3sv_keep hd h1 h2).1 (d3sv_keep hd h1 h2).2).trans (I.sv c h1 h2)⟩

end

set_option maxRecDepth 20000 in
theorem d3keep_mm : ∀ q : Fin 32, d3Keep q = true → q ≠ sp → q.val ≠ 0 →
    q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by decide

section Calls
variable {M0 M Ms : Word → BitVec 8} {P sp0 out sf : Word} {V : Fin 32 → Word} {off d : Nat}
  {n : Machine} {imm o a b : Word} {A B : Nat}

theorem d3keep_of_call {n1 n' : Machine} {L : Word} (regs1 : ∀ r, reg n1 r = upd (reg n) ra L r)
    (hz : reg n 0 = 0)
    (regs' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      reg n' q = reg n1 q) :
    ∀ q, d3Keep q = true → reg n' q = reg n q := fun q hq => by
  have k := fun r (hr : d3Keep r = false) => bkeep_ne hq hr
  rw [regs' q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl)
    (k t0 rfl) (k t1 rfl)]
  exact PEnv.reg1 regs1 hz q (k ra rfl)

theorem d3keep_of_mm {n1 n' : Machine} {L G : Word} (regs1 : ∀ r, reg n1 r = upd (reg n) ra L r)
    (hz : reg n 0 = 0) (hz' : reg n' 0 = 0) (hsp : reg n sp = G) (hsp' : reg n' sp = G)
    (regs' : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n1 q) :
    ∀ q, d3Keep q = true → reg n' q = reg n q := fun q hq => by
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; rw [hz, hz']
  by_cases hs : q = sp
  · subst hs; rw [hsp, hsp']
  rw [regs' q (d3keep_mm q hq hs h0)]
  exact PEnv.reg1 regs1 hz q (bkeep_ne hq (show d3Keep ra = false from rfl))

set_option maxHeartbeats 1000000 in
/-- A call to the multiplication wrapper: the result slot gets the
Montgomery product of the operands. -/
theorem d3_mul (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d3G sp0)
    (h1 : fetchRel p384PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x11C82) (hoff : off % 2 = 0)
    (hd : D3Dst d) (ha0 : reg n a0 = d3G sp0 + BitVec.ofNat 32 d)
    (sa : D3Src sp0 a) (ha1 : reg n a1 = a) (sb : D3Src sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 12) = A) (hB : limbVal (wordsAt M b 12) = B) (hBp : B < p384) :
    ∃ n' M', Steps n n' ∧ D3Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d3G sp0 + BitVec.ofNat 32 d) 12) = p3fm A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0x11C82 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have spn : reg n sp = d3G sp0 := by rw [I.keep sp rfl, hVsp]
  obtain ⟨n', c', pc', sp', k', val', fr'⟩ := p384Mul_correct n1 (by rw [mem1]; exact env.mEnv I.fr hd sa sb) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (d3_ret_even env hoff)
    (by rw [r1 sp (by decide), spn]) (by rw [mem1, hB]; exact hBp)
  rw [mem1, hA, hB] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [d3G_mm]; exact hx) hr
  have st' : St n'.mem P n' (off + 8) (reg n') := ⟨by rw [pc'], rfl, fun _ => rfl⟩
  refine ⟨n', n'.mem, c1.trans c', I.after hd st'
    (d3keep_of_mm regs1 I.st.zero st'.zero spn sp' k') frS, frS, val'⟩

set_option maxHeartbeats 1000000 in
/-- A call to the squaring wrapper. -/
theorem d3_sqr (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d3G sp0)
    (h1 : fetchRel p384PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x12426) (hoff : off % 2 = 0)
    (hd : D3Dst d) (ha0 : reg n a0 = d3G sp0 + BitVec.ofNat 32 d)
    (sa : D3Src sp0 a) (ha1 : reg n a1 = a)
    (hA : limbVal (wordsAt M a 12) = A) (hAp : A < p384) :
    ∃ n' M', Steps n n' ∧ D3Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d3G sp0 + BitVec.ofNat 32 d) 12) = p3fm A A := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0x12426 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have spn : reg n sp = d3G sp0 := by rw [I.keep sp rfl, hVsp]
  obtain ⟨n', c', pc', sp', k', val', fr'⟩ := p384Sqr_correct n1 (by rw [mem1]; exact env.qEnv I.fr hd sa) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (d3_ret_even env hoff)
    (by rw [r1 sp (by decide), spn]) (by rw [mem1, hA]; exact hAp)
  rw [mem1, hA] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [d3G_mm]; exact hx) hr
  have st' : St n'.mem P n' (off + 8) (reg n') := ⟨by rw [pc'], rfl, fun _ => rfl⟩
  refine ⟨n', n'.mem, c1.trans c', I.after hd st'
    (d3keep_of_mm regs1 I.st.zero st'.zero spn sp' k') frS, frS, val'⟩

set_option maxHeartbeats 1000000 in
/-- A call to `add`. -/
theorem d3_add (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d3G sp0)
    (h1 : fetchRel p384PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x53A) (hoff : off % 2 = 0)
    (hd : D3Dst d) (ha0 : reg n a0 = d3G sp0 + BitVec.ofNat 32 d)
    (sa : D3Src sp0 a) (ha1 : reg n a1 = a) (sb : D3Src sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 12) = A) (hAp : A < p384) (hB : limbVal (wordsAt M b 12) = B) (hBp : B < p384) :
    ∃ n' M', Steps n n' ∧ D3Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d3G sp0 + BitVec.ofNat 32 d) 12) = p3fa A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0x53A (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have spn : reg n sp = d3G sp0 := by rw [I.keep sp rfl, hVsp]
  obtain ⟨n', c', pc', sp', k', val', fr'⟩ := p384Add_correct n1 (by rw [mem1]; exact env.aEnv I.fr hd sa sb) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (d3_ret_even env hoff) (by rw [r1 sp (by decide), spn])
  rw [mem1, hA, hB, p3AddRes_mod hAp hBp] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 →
      n'.mem x = M x := fun x hx hr =>
    fr' x (by rw [d3G_ad]; exact hx.sub (c := 0x3C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (d3keep_of_call regs1 I.st.zero k') frS, frS, val'⟩

set_option maxHeartbeats 1000000 in
/-- A call to `sub`. -/
theorem d3_sub (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d3G sp0)
    (h1 : fetchRel p384PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x650) (hoff : off % 2 = 0)
    (hd : D3Dst d) (ha0 : reg n a0 = d3G sp0 + BitVec.ofNat 32 d)
    (sa : D3Src sp0 a) (ha1 : reg n a1 = a) (sb : D3Src sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 12) = A) (hAp : A < p384) (hB : limbVal (wordsAt M b 12) = B) (hBp : B < p384) :
    ∃ n' M', Steps n n' ∧ D3Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d3G sp0 + BitVec.ofNat 32 d) 12) = p3fs A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0x650 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have spn : reg n sp = d3G sp0 := by rw [I.keep sp rfl, hVsp]
  obtain ⟨n', c', pc', sp', k', val', fr'⟩ := p384Sub_correct n1 (by rw [mem1]; exact env.sEnv I.fr hd sa sb) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (d3_ret_even env hoff) (by rw [r1 sp (by decide), spn])
  rw [mem1, hA, hB, p3SubRes_mod hAp hBp] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 →
      n'.mem x = M x := fun x hx hr =>
    fr' x (by rw [d3G_ad]; exact hx.sub (c := 0x3C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (d3keep_of_call regs1 I.st.zero k') frS, frS, val'⟩

set_option maxHeartbeats 1000000 in
/-- A call to `double`. -/
theorem d3_dbl (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d3G sp0)
    (h1 : fetchRel p384PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x1235E) (hoff : off % 2 = 0)
    (hd : D3Dst d) (ha0 : reg n a0 = d3G sp0 + BitVec.ofNat 32 d)
    (sa : D3Src sp0 a) (ha1 : reg n a1 = a)
    (hA : limbVal (wordsAt M a 12) = A) (hAp : A < p384) :
    ∃ n' M', Steps n n' ∧ D3Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d3G sp0 + BitVec.ofNat 32 d) 12) = p3fd A := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0x1235E (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have spn : reg n sp = d3G sp0 := by rw [I.keep sp rfl, hVsp]
  obtain ⟨n', c', pc', sp', k', val', fr'⟩ := p384Double_correct n1 (by rw [mem1]; exact env.dEnv I.fr hd sa) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (d3_ret_even env hoff) (by rw [r1 sp (by decide), spn])
  rw [mem1, hA, p3AddRes_mod hAp hAp] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 →
      n'.mem x = M x := fun x hx hr =>
    fr' x (by rw [d3G_db]; exact hx.sub (c := 0x20) (l := 0xD0) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (d3keep_of_call regs1 I.st.zero k') frS, frS, val'⟩

set_option maxHeartbeats 1000000 in
/-- A `memcpy` of the frame slot at `s` into the one at `d`. -/
theorem d3_cpy (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off) {s : Nat}
    (h1 : fetchRel p384PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x12C54) (hoff : off % 2 = 0)
    (hd : D3Dst d) (hs : D3Dst s) (hds : d + 48 ≤ s ∨ s + 48 ≤ d)
    (ha0 : reg n a0 = d3G sp0 + BitVec.ofNat 32 d)
    (ha1 : reg n a1 = d3G sp0 + BitVec.ofNat 32 s) (ha2 : reg n a2 = 0x30) :
    ∃ n' M', Steps n n' ∧ D3Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x) ∧
      wordsAt M' (d3G sp0 + BitVec.ofNat 32 d) 12 = wordsAt M (d3G sp0 + BitVec.ofNat 32 s) 12 := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0x12C54 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have e : P + 0x12C54 + 8 = P + 0x12C5C := by rw [BitVec.add_assoc]; rfl
  have hGw := env.hGw; have hS := env.hS
  obtain ⟨n', c', pc', mem', a0', regs'⟩ := memcpy_aligned n1 (P + 0x12C54) (P + BitVec.ofNat 32 (off + 8))
    (d3G sp0 + BitVec.ofNat 32 d) (d3G sp0 + BitVec.ofNat 32 s) 12
    (fun i hi => by rw [mem1]; exact env.codeT I.fr env.stub env.sU i hi)
    (fun i hi => by rw [mem1, e]; exact env.codeT I.fr env.body env.sB i hi)
    (even_at P env.hP 0x12C54 (by decide)) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]; rfl)
    (by rw [regs1]; simp +decide [upd]) (d3_ret_even env hoff) (by decide) (hd.wr env) (by decide)
    (hd.al env) (hs.al env)
    (sep_offsets _ (hds.elim (fun h => .inl (by omega)) (fun h => .inr (by omega))) (by have := hd.2.1; omega)
      (by have := hs.2.1; omega))
    (by rw [e]; exact hd.inS env.sB)
  rw [mem1] at mem'
  have out : ∀ x, Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → n'.mem x = M x := fun x hx => by
    rw [mem']; exact copyWords_outside 12 hx
  have frS : ∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → n'.mem x = M x :=
    fun x _ hx => out x hx
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩ (fun q hq => ?_) frS, frS, ?_⟩
  · have k' := fun r (hr : d3Keep r = false) => bkeep_ne hq hr
    rw [regs' q (k' a1 rfl) (k' a2 rfl) (k' a3 rfl) (k' a4 rfl) (k' a5 rfl) (k' a6 rfl) (k' a7 rfl)
      (k' t0 rfl) (k' t1 rfl), r1 q (k' ra rfl)]
  · rw [mem']
    unfold wordsAt
    exact List.map_congr_left fun i hi => copyWords_load 12 i (List.mem_range.mp hi) (hd.wr env |> Nat.le_of_lt)

end Calls

section Keep
variable {M0 M M' Ms : Word → BitVec 8} {P sp0 out sf : Word} {V : Fin 32 → Word} {off : Nat} {n : Machine}

/-- An operand outside `S` reads as on entry. -/
theorem D3Inv.inp (I : D3Inv M0 P sp0 V Ms M n off) {a : Word} (h : Sep a 48 (d3S sp0) 0x540) :
    wordsAt M a 12 = wordsAt M0 a 12 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => I.fr _
    (by rw [add_ofNat_assoc]; exact h.symm.subR (c := 4 * i + j) (l := 1) (by omega))

/-- A call that changed only the callees' stack and the slot at `d` left the
slot at `c` alone. -/
theorem d3slot_keep {d c : Nat}
    (f : ∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x)
    (hd : D3Dst d) (hc : D3Dst c) (hdc : d + 48 ≤ c ∨ c + 48 ≤ d) :
    wordsAt M' (d3G sp0 + BitVec.ofNat 32 c) 12 = wordsAt M (d3G sp0 + BitVec.ofNat 32 c) 12 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc (d3G sp0) c (4 * i), add_ofNat_assoc (d3G sp0) (c + 4 * i) j]
    have := hc.2.1; have := hd.2.1
    exact f _ (by
        rw [d3G_S]
        exact sep_base0 (sep_offsets _ (c := 0) (n := 0xF0) (d := 0xF0 + (c + 4 * i + j)) (k := 1)
          (.inl (by omega)) (by decide) (by omega)))
      (sep_offsets _ (c := d) (n := 48) (d := c + 4 * i + j) (k := 1)
        (by rcases hdc with h | h
            · exact .inl (by omega)
            · exact .inr (by omega)) (by omega) (by omega))

/-- A call that changed only `S` left an operand outside it alone. -/
theorem d3out_keep {d : Nat} {a : Word}
    (f : ∀ x, Sep (d3S sp0) 0xF0 x 1 → Sep (d3G sp0 + BitVec.ofNat 32 d) 48 x 1 → M' x = M x)
    (hd : D3Dst d) (h : Sep a 48 (d3S sp0) 0x540) :
    wordsAt M' a 12 = wordsAt M a 12 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]
    have hs := h.sub (c := 4 * i + j) (l := 1) (by omega)
    exact f _ (sep_base0r (hs.subR (c := 0) (l := 0xF0) (by decide))).symm (hd.inS hs.symm)

end Keep

section Steps
variable {M0 M Ms : Word → BitVec 8} {P sp0 out sf : Word} {V : Fin 32 → Word} {off off' : Nat}
  {n : Machine}

/-- `addi rd, rs, imm` into a register `d3Keep` doesn't name. -/
theorem d3_addi (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off)
    {rd rs : Fin 32} {imm len : Word}
    (hf : fetchRel p384PtDoubleCode off = some (.aluImm .add rd rs imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hk : d3Keep rd = false) :
    ∃ n', Steps n n' ∧ D3Inv M0 P sp0 V Ms M n' off' ∧ reg n' rd = reg n rs + imm ∧
      ∀ q, q ≠ rd → reg n' q = reg n q := by
  obtain ⟨n', d, u⟩ := I.st.aluImm (env.codeT I.fr env.code env.sC) hf hn
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
theorem d3_addiK (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off)
    {rd rs : Fin 32} {imm len : Word}
    (hf : fetchRel p384PtDoubleCode off = some (.aluImm .add rd rs imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (h0 : rd.val ≠ 0) :
    ∃ n', Steps n n' ∧ D3Inv M0 P sp0 (upd V rd (reg n rs + imm)) Ms M n' off' ∧
      reg n' rd = reg n rs + imm ∧ ∀ q, q ≠ rd → reg n' q = reg n q := by
  obtain ⟨n', d, u⟩ := I.st.aluImm (env.codeT I.fr env.code env.sC) hf hn
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
theorem d3_luiK (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off)
    {rd : Fin 32} {imm len : Word}
    (hf : fetchRel p384PtDoubleCode off = some (.lui rd imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (h0 : rd.val ≠ 0) :
    ∃ n', Steps n n' ∧ D3Inv M0 P sp0 (upd V rd imm) Ms M n' off' ∧ reg n' rd = imm := by
  obtain ⟨n', d, u⟩ := I.st.lui (env.codeT I.fr env.code env.sC) hf hn
  have same : reg n' rd = imm := by rw [u.regs, upd_same h0]
  refine ⟨n', .single d, ⟨u.self, fun q hq => ?_, I.fr, I.sv⟩, same⟩
  by_cases hq0 : q.val = 0
  · have : q = 0 := Fin.ext hq0
    subst this; simp [upd]; exact u.self.zero
  by_cases e : q = rd
  · subst e; rw [same, upd_same h0]
  · rw [u.regs, upd_ne hq0 e, upd_ne hq0 e]; exact I.keep q hq

/-- `mv rd, rs` into a register `d3Keep` doesn't name. -/
theorem d3_mv (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n off)
    {rd rs : Fin 32} {len : Word}
    (hf : fetchRel p384PtDoubleCode off = some (.alu .add rd 0 rs, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hk : d3Keep rd = false) :
    ∃ n', Steps n n' ∧ D3Inv M0 P sp0 V Ms M n' off' ∧ reg n' rd = reg n rs ∧
      ∀ q, q ≠ rd → reg n' q = reg n q := by
  obtain ⟨n', d, u⟩ := I.st.alu (env.codeT I.fr env.code env.sC) hf hn
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

/-- The registers the point doubling saves, with their offsets in its frame. -/
def d3Ps : List (Fin 32 × Word) :=
  [(ra, 0x44C), ((8 : Fin 32), 0x448), ((9 : Fin 32), 0x444), ((18 : Fin 32), 0x440), ((19 : Fin 32), 0x43C),
   ((20 : Fin 32), 0x438), ((21 : Fin 32), 0x434), ((22 : Fin 32), 0x430)]

set_option maxRecDepth 20000 in
theorem d3Ps_range : ∀ p ∈ d3Ps, p.2.toNat % 4 = 0 ∧ 0x430 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x450 := by decide

set_option maxRecDepth 20000 in
theorem d3Ps_sp : ∀ p ∈ d3Ps, p.1 ≠ sp := by decide

/-- The prologue's frame, register saves, and argument moves, from 0x0 to
0x2E. -/
def d3ProA : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFBB0, .aluImm .add a2 sp 0x400, .sw a2 ra 0x4C, .sw a2 (8 : Fin 32) 0x48,
   .sw a2 (9 : Fin 32) 0x44, .sw a2 (18 : Fin 32) 0x40, .sw a2 (19 : Fin 32) 0x3C, .sw a2 (20 : Fin 32) 0x38,
   .sw a2 (21 : Fin 32) 0x34, .sw a2 (22 : Fin 32) 0x30, .alu .add (9 : Fin 32) x0 a1,
   .alu .add (20 : Fin 32) x0 a0, .aluImm .add a0 sp 0x10, .aluImm .add a2 x0 0x90]

/-- The epilogue's `memcpy` arguments, from 0x228 to 0x230. -/
def d3EpiA : List BInstr := [.aluImm .add a1 sp 0x10, .aluImm .add a2 x0 0x90, .alu .add a0 x0 (20 : Fin 32)]

/-- The epilogue's register restores and the frame's release, from 0x238 to
0x25C. -/
def d3EpiB : List BInstr :=
  [.aluImm .add a0 sp 0x400, .lw ra a0 0x4C, .lw (8 : Fin 32) a0 0x48, .lw (9 : Fin 32) a0 0x44,
   .lw (18 : Fin 32) a0 0x40, .lw (19 : Fin 32) a0 0x3C, .lw (20 : Fin 32) a0 0x38, .lw (21 : Fin 32) a0 0x34,
   .lw (22 : Fin 32) a0 0x30, .aluImm .add sp sp 0x450]

section
set_option maxRecDepth 20000
theorem d3ProA_end : blockEnd p384PtDoubleCode 0x0 d3ProA = some 0x2E := by decide
theorem d3EpiA_end : blockEnd p384PtDoubleCode 0x228 d3EpiA = some 0x230 := by decide
theorem d3EpiB_end : blockEnd p384PtDoubleCode 0x238 d3EpiB = some 0x25C := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem d3ProA_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock d3ProA (M, f)).1 = saveMem M (f sp + 0xFFFFFBB0) f d3Ps ∧
    (runBlock d3ProA (M, f)).2 sp = f sp + 0xFFFFFBB0 ∧
    (runBlock d3ProA (M, f)).2 (9 : Fin 32) = f a1 ∧ (runBlock d3ProA (M, f)).2 (20 : Fin 32) = f a0 ∧
    (runBlock d3ProA (M, f)).2 a0 = f sp + 0xFFFFFBB0 + 0x10 ∧ (runBlock d3ProA (M, f)).2 a2 = 0x90 ∧
    ∀ q, q ≠ sp → q ≠ a0 → q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → (runBlock d3ProA (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, d3ProA, upd_app, ↓reduceIte, saveMem, d3Ps]
  refine ⟨?_, rfl, BitVec.zero_add _, BitVec.zero_add _, rfl, trivial, fun q h1 h2 h3 h4 h5 => ?_⟩
  · simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [hz]; rfl
    · simp only [h0, h1, h2, h3, h4, h5, ite_false]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem d3EpiB_run {M : Word → BitVec 8} {f : Fin 32 → Word} {G : Word} (hsp : f sp = G) :
    (runBlock d3EpiB (M, f)).1 = M ∧
    (runBlock d3EpiB (M, f)).2 sp = G + 0x450 ∧
    (∀ r o, (r, o) ∈ d3Ps → (runBlock d3EpiB (M, f)).2 r = memLoad32 M (G + o)) ∧
    ∀ q, q.val ∉ [0, 1, 2, 8, 9, 10, 18, 19, 20, 21, 22] → (runBlock d3EpiB (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, d3EpiB, upd_app, ↓reduceIte]
  refine ⟨trivial, by rw [hsp]; rfl, fun r o h => ?_, fun q hq => ?_⟩
  · simp only [d3Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    · simp +decide only [↓reduceIte]
      simp only [hsp, ev_add, BitVec.add_assoc, BitVec.reduceAdd]
      try rfl
  · have h0 : q.val ≠ 0 := fun e => hq (by simp [e])
    have k : ∀ r : Fin 32, r.val ∈ [0, 1, 2, 8, 9, 10, 18, 19, 20, 21, 22] → q ≠ r :=
      fun r hr e => hq (e ▸ hr)
    simp only [h0, k ra (by decide), k sp (by decide), k 8 (by decide), k 9 (by decide), k a0 (by decide),
      k 18 (by decide), k 19 (by decide), k 20 (by decide), k 21 (by decide), k 22 (by decide), ite_false]

theorem d3_sp_lit {sp0 b : Word} {k : Nat} (h : Sep (d3S sp0) 0x540 b k) (c : Nat) (hc : c + 4 ≤ 0x540) (w : Word)
    (hw : (0xFFFFFAC0 : Word) + BitVec.ofNat 32 c = w) : Sep (sp0 + w) 4 b k := by
  rw [← hw, ← BitVec.add_assoc]; exact h.sub hc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The point doubling's prologue, to 0x36: make the frame, save `ra` and
`s0` through `s6` at its top, keep the point's and the result's addresses in
`s1` and `s4`, and copy the point into the frame at 0x10. -/
theorem d3_pro (m : Machine) {P sp0 out sf : Word} (env : D3Env m.mem P sp0 out sf) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = sf) (hsp : reg m sp = sp0) :
    ∃ n Ms, Steps m n ∧ D3Inv m.mem P sp0 (reg n) Ms Ms n 0x36 ∧
      reg n sp = d3G sp0 ∧ reg n (9 : Fin 32) = sf ∧ reg n (20 : Fin 32) = out ∧
      (∀ q, d3Keep q = true → q ≠ sp → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → reg n q = reg m q) ∧
      (∀ r c, (r, c) ∈ d3Ps → memLoad32 Ms (d3G sp0 + c) = reg m r) ∧
      ∀ k, k < 36 → memLoad32 Ms (d3G sp0 + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 (4 * k)) =
        memLoad32 m.mem (sf + BitVec.ofNat 32 (4 * k)) := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGa := env.hGa; have hGw := env.hGw; have hS := env.hS
  obtain ⟨E1, Esp, E9, E20, Ea0, Ea2, Ek⟩ := d3ProA_run (M := m.mem) (f := reg m) hz
  rw [hsp] at E1 Esp Ea0
  obtain ⟨n1, c1, u1⟩ := St.block d3ProA s0 env.code d3ProA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, d3ProA, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add, hsp, BitVec.add_assoc, BitVec.reduceAdd]
    exact ⟨⟨aligned_add env.hsp (k := 0xFFFFFFFC) (by decide), d3_sp_lit env.sC 0x53C (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFF8) (by decide), d3_sp_lit env.sC 0x538 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFF4) (by decide), d3_sp_lit env.sC 0x534 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFF0) (by decide), d3_sp_lit env.sC 0x530 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFEC) (by decide), d3_sp_lit env.sC 0x52C (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFE8) (by decide), d3_sp_lit env.sC 0x528 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFE4) (by decide), d3_sp_lit env.sC 0x524 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFE0) (by decide), d3_sp_lit env.sC 0x520 (by decide) _ rfl⟩⟩)
  rw [E1] at u1
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (sp0 + 0xFFFFFBB0) (reg m) d3Ps = Msv := ⟨_, rfl⟩
  rw [hMsv] at u1
  have frSv : ∀ x, Sep (d3S sp0) 0x540 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    refine saveMem_outside d3Ps fun p hp => ?_
    obtain ⟨_, h1, h2⟩ := d3Ps_range p hp
    have := hx.sub (c := 0xF0 + p.2.toNat) (l := 4) (by omega)
    rwa [← d3G_S, ofNat_toNat_self] at this
  have cSv : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep (d3S sp0) 0x540 b code.length →
      CodeIn Msv b code := fun hc hs i hi => by
    rw [frSv _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have r1 : ∀ r, reg n1 r = (runBlock d3ProA (m.mem, reg m)).2 r := u1.regs
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.self.callRa (cSv env.code env.sC) p3pd_at_2e p3pd_at_32
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x12C54 (by decide))
  have r2 := PEnv.reg1 regs2 u1.self.zero
  have e : P + 0x12C54 + 8 = P + 0x12C5C := by rw [BitVec.add_assoc]; rfl
  have hsfw : (d3G sp0 + BitVec.ofNat 32 0x10).toNat + 4 * 36 < 2 ^ 32 := by
    have := (D3Dst.wr (d := 0x10) env ⟨by decide, by decide, by decide⟩); rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this ⊢
    have := sp0.isLt; omega
  have sDst : Sep (d3G sp0 + BitVec.ofNat 32 0x10) (4 * 36) sf (4 * 36) := by
    rw [d3G_S]; exact (env.sF.symm.sub (c := 0xF0 + 0x10) (l := 144) (by decide))
  obtain ⟨n3, c3, pc3, mem3, a03, regs3⟩ := memcpy_aligned n2 (P + 0x12C54) (P + BitVec.ofNat 32 (0x2E + 8))
    (d3G sp0 + BitVec.ofNat 32 0x10) sf 36
    (fun i hi => by rw [mem2]; exact cSv env.stub env.sU i hi)
    (fun i hi => by rw [mem2, e]; exact cSv env.body env.sB i hi)
    (even_at P env.hP 0x12C54 (by decide)) pc2
    (by rw [r2 a0 (by decide), r1, Ea0]; rfl) (by rw [r2 a1 (by decide), r1, Ek a1 (by decide) (by decide)
        (by decide) (by decide) (by decide), ha1])
    (by rw [r2 a2 (by decide), r1, Ea2]; rfl)
    (by rw [regs2]; simp +decide [upd]) (d3_ret_even env (off := 0x2E) (by decide)) (by decide) hsfw (by decide)
    (aligned_add hGa (by decide)) env.hsf sDst
    (by rw [e, d3G_S]; exact env.sB.sub (c := 0xF0 + 0x10) (l := 4 * 36) (by decide))
  rw [mem2] at mem3
  obtain ⟨Ms, hMs⟩ : ∃ Ms, copyWords Msv (d3G sp0 + BitVec.ofNat 32 0x10) sf 36 = Ms := ⟨_, rfl⟩
  rw [hMs] at mem3
  have frMs : ∀ x, Sep (d3S sp0) 0x540 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs, copyWords_outside 36 (by rw [d3G_S]; exact hx.sub (c := 0xF0 + 0x10) (l := 4 * 36) (by decide)),
      frSv x hx]
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ ra → reg n3 q = (runBlock d3ProA (m.mem, reg m)).2 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 ht0 ht1 hra => by rw [regs3 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1, r2 q hra, r1]
  refine ⟨n3, Ms, c1.trans (c2.trans c3), ⟨⟨by rw [pc3], mem3, fun _ => rfl⟩, fun _ _ => rfl, frMs,
    fun _ _ _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), Esp]
  · rw [k3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), E9, ha1]
  · rw [k3 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), E20, ha0]
  · intro q hq h1 h2 h3
    have k := fun r (hr : d3Keep r = false) => bkeep_ne hq hr
    rw [k3 q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl) (k t0 rfl)
      (k t1 rfl) (k ra rfl), Ek q h1 (k a0 rfl) (k a2 rfl) h2 h3]
  · intro r c h
    obtain ⟨_, h1, h2⟩ := d3Ps_range (r, c) h
    dsimp only at h1 h2
    rw [← hMs, copyWords_load_sep (by
      rw [← ofNat_toNat_self c, d3G_S, d3G_S]
      exact sep_offsets _ (.inl (by omega)) (by omega) (by omega)), ← hMsv]
    simp only [d3Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    · simp only [d3Ps, saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
  · intro k hk
    rw [← hMs, copyWords_load 36 k hk (Nat.le_of_lt hsfw)]
    exact memLoad32_congr fun j hj => frSv _ (by
      rw [add_ofNat_assoc]; exact (env.sF.sub (c := 4 * k + j) (l := 1) (by omega)).symm)

set_option maxRecDepth 20000 in
theorem d3epi_keep : ∀ q : Fin 32, d3Keep q = true → q.val ∉ [0, 2, 8, 9, 18, 19, 20, 21, 22] →
    q.val ∉ [0, 1, 2, 8, 9, 10, 18, 19, 20, 21, 22] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The point doubling's epilogue, from 0x228: copy the result out of the
frame into `out`, restore `ra` and `s0` through `s6` from the save slots,
drop the frame, and return. -/
theorem d3_epi {M0 M Ms : Word → BitVec 8} {P sp0 out sf : Word} {V : Fin 32 → Word} {n : Machine}
    (env : D3Env M0 P sp0 out sf) (I : D3Inv M0 P sp0 V Ms M n 0x228) (hVsp : V sp = d3G sp0)
    (hV20 : V (20 : Fin 32) = out) :
    ∃ m', Steps n m' ∧ m'.pc = memLoad32 Ms (d3G sp0 + 0x44C) &&& ~~~1 ∧
      m'.mem = copyWords M out (d3G sp0 + BitVec.ofNat 32 0x10) 36 ∧ reg m' sp = sp0 ∧
      (∀ r c, (r, c) ∈ d3Ps → reg m' r = memLoad32 Ms (d3G sp0 + c)) ∧
      ∀ q, d3Keep q = true → q.val ∉ [0, 2, 8, 9, 18, 19, 20, 21, 22] → reg m' q = V q := by
  have hGa := env.hGa; have hGw := env.hGw; have hS := env.hS
  have cM := env.codeT I.fr env.code env.sC
  obtain ⟨m1, c1, u1⟩ := St.block d3EpiA I.st cM d3EpiA_end (by simp [BlockOk, BInstr.ok, d3EpiA])
  simp only [runBlock, BInstr.run, d3EpiA] at u1
  have k1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m1 q = reg n q := fun q h0 h1 h2 => by
    rw [u1.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact I.st.zero.symm
    · simp only [upd_app, hq0, h0, h1, h2, ite_false]
  obtain ⟨m2, c2, pc2, mem2, regs2⟩ := u1.self.callRa cM p3pd_at_230 p3pd_at_234
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x12C54 (by decide))
  have r2 := PEnv.reg1 regs2 u1.self.zero
  have e : P + 0x12C54 + 8 = P + 0x12C5C := by rw [BitVec.add_assoc]; rfl
  have hwo := env.hwo
  have sOut : Sep out (4 * 36) (d3G sp0 + BitVec.ofNat 32 0x10) (4 * 36) := by
    rw [d3G_S]; exact env.sO.subR (c := 0xF0 + 0x10) (l := 144) (by decide)
  obtain ⟨m3, c3, pc3, mem3, a03, regs3⟩ := memcpy_aligned m2 (P + 0x12C54) (P + BitVec.ofNat 32 (0x230 + 8))
    out (d3G sp0 + BitVec.ofNat 32 0x10) 36
    (fun i hi => by rw [mem2]; exact env.codeT I.fr env.stub env.sU i hi)
    (fun i hi => by rw [mem2, e]; exact env.codeT I.fr env.body env.sB i hi)
    (even_at P env.hP 0x12C54 (by decide)) pc2
    (by rw [r2 a0 (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [I.keep 20 rfl, hV20]; exact BitVec.zero_add _)
    (by rw [r2 a1 (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [I.keep sp rfl, hVsp]; rfl)
    (by rw [r2 a2 (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs2]; simp +decide [upd]) (d3_ret_even env (off := 0x230) (by decide)) (by decide) (by omega)
    (by decide) env.hout (aligned_add hGa (by decide)) sOut (by rw [e]; exact env.oB)
  rw [mem2] at mem3
  obtain ⟨Mo, hMo⟩ : ∃ Mo, copyWords M out (d3G sp0 + BitVec.ofNat 32 0x10) 36 = Mo := ⟨_, rfl⟩
  rw [hMo] at mem3
  have outS : ∀ x, Sep out 144 x 1 → Mo x = M x := fun x hx => by
    rw [← hMo]; exact copyWords_outside 36 hx
  have cMo : CodeIn Mo P p384PtDoubleCode := fun i hi => by
    rw [outS _ (env.oC.subR (c := i) (l := 1) (by omega))]; exact cM i hi
  have s3 : St Mo P m3 0x238 (reg m3) := ⟨by rw [pc3], mem3, fun _ => rfl⟩
  have sp3 : reg m3 sp = d3G sp0 := by
    rw [regs3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), r2 sp (by decide), k1 sp (by decide) (by decide) (by decide), I.keep sp rfl, hVsp]
  obtain ⟨E1, Esp, Eps, Ek⟩ := d3EpiB_run (M := Mo) (f := reg m3) sp3
  obtain ⟨m4, c4, u4⟩ := St.block d3EpiB s3 cMo d3EpiB_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, d3EpiB, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add, sp3, BitVec.add_assoc, BitVec.reduceAdd]
    exact ⟨aligned_add env.hsp (k := 0xFFFFFFFC) (by decide), aligned_add env.hsp (k := 0xFFFFFFF8) (by decide),
      aligned_add env.hsp (k := 0xFFFFFFF4) (by decide), aligned_add env.hsp (k := 0xFFFFFFF0) (by decide),
      aligned_add env.hsp (k := 0xFFFFFFEC) (by decide), aligned_add env.hsp (k := 0xFFFFFFE8) (by decide),
      aligned_add env.hsp (k := 0xFFFFFFE4) (by decide), aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)⟩)
  rw [E1] at u4
  obtain ⟨m5, d5, pc5, mem5, regs5⟩ := u4.jalr cMo p3pd_at_25c
  have ld : ∀ c : Word, 0x430 ≤ c.toNat → c.toNat + 4 ≤ 0x450 →
      memLoad32 Mo (d3G sp0 + c) = memLoad32 Ms (d3G sp0 + c) := fun c h1 h2 =>
    memLoad32_congr fun j hj => by
      rw [outS _ (by
        rw [← ofNat_toNat_self c, add_ofNat_assoc, d3G_S]
        exact env.sO.subR (c := 0xF0 + (c.toNat + j)) (l := 1) (by omega)),
        ← ofNat_toNat_self c, add_ofNat_assoc]
      exact I.sv _ (by omega) (by omega)
  have ps : ∀ r c, (r, c) ∈ d3Ps → reg m5 r = memLoad32 Ms (d3G sp0 + c) := fun r c h => by
    obtain ⟨_, h1, h2⟩ := d3Ps_range (r, c) h
    rw [regs5, Eps r c h, ld c h1 h2]
  refine ⟨m5, c1.trans (c2.trans (c3.trans (c4.trans (.single d5)))), ?_, ?_, ?_, ps, ?_⟩
  · rw [pc5, add_lit_zero, Eps ra 0x44C (by decide), ld 0x44C (by decide) (by decide)]
  · rw [mem5, ← hMo]
  · rw [regs5, Esp]; show sp0 + 0xFFFFFBB0 + 0x450 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero _
  · intro q hq hn
    have k := fun r (hr : d3Keep r = false) => bkeep_ne hq hr
    rw [regs5, Ek q (d3epi_keep q hq hn),
      regs3 q (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl) (k t0 rfl) (k t1 rfl),
      r2 q (k ra rfl), k1 q (k a0 rfl) (k a1 rfl) (k a2 rfl), I.keep q hq]

/-- P-384's `b` in Montgomery form, as the image stores it at `p3bA`. -/
def p3B : Nat :=
  0xcd08114b604fbff9b62b21f41f022094e3374bee94938ae277f2209b1920022ef729add87a4c32ec081188719d412dcc

set_option exponentiation.threshold 600 in
/-- `p3B` is `b · 2^384 mod p`, with `b` from SEC 2. -/
theorem p3B_mont : p3B = (0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
    * 2 ^ 384) % p384 := by unfold p3B p384; decide

set_option exponentiation.threshold 600 in
theorem p3B_lt : p3B < p384 := by unfold p3B p384; decide

set_option exponentiation.threshold 600 in
theorem p3B_val {M : Word → BitVec 8} (h : CodeIn M p3bA p384BData) : limbVal (wordsAt M p3bA 12) = p3B := by
  have he : ∀ i : Fin 12, (byteAt p384BData (4 * i.val + 3) ++ byteAt p384BData (4 * i.val + 2) ++
      byteAt p384BData (4 * i.val + 1) ++ byteAt p384BData (4 * i.val)) =
      BitVec.ofNat 32 ((p3B / 2 ^ (32 * i.val)) % 2 ^ 32) := by decide +kernel
  have hw : ∀ i, i < 12 → memLoad32 M (p3bA + BitVec.ofNat 32 (4 * i)) =
      BitVec.ofNat 32 ((p3B / 2 ^ (32 * i)) % 2 ^ 32) := fun i hi => by
    rw [← he ⟨i, hi⟩]
    unfold memLoad32
    have hl : p384BData.length = 48 := rfl
    have b0 := h (4 * i) (by omega)
    have b1 : M (p3bA + BitVec.ofNat 32 (4 * i) + 1) = byteAt p384BData (4 * i + 1) := by
      rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    have b2 : M (p3bA + BitVec.ofNat 32 (4 * i) + 2) = byteAt p384BData (4 * i + 2) := by
      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    have b3 : M (p3bA + BitVec.ofNat 32 (4 * i) + 3) = byteAt p384BData (4 * i + 3) := by
      rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    rw [b3, b2, b1, b0]
  rw [limbVal_wordsAt]
  simp only [accV]
  rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide),
    hw 6 (by decide), hw 7 (by decide), hw 8 (by decide), hw 9 (by decide), hw 10 (by decide), hw 11 (by decide)]
  decide

/-- `primeorder`'s point doubling for `a = -3` (Renes, Costello, and Batina
2015, algorithm 6), in the Rust source's order, over the field operations
modulo P-384's `p` in Montgomery form: `b` is the curve constant. -/
def p3Dbl (b X Y Z : Nat) : Nat × Nat × Nat :=
  let xx := p3fm X X
  let yy := p3fm Y Y
  let zz := p3fm Z Z
  let xy2 := p3fd (p3fm X Y)
  let xz2 := p3fd (p3fm X Z)
  let bzz := p3fs (p3fm b zz) xz2
  let bzz3 := p3fa (p3fd bzz) bzz
  let yymb := p3fs yy bzz3
  let yypb := p3fa yy bzz3
  let yf := p3fm yypb yymb
  let xf := p3fm yymb xy2
  let zz3 := p3fa (p3fd zz) zz
  let bxz2 := p3fs (p3fm b xz2) (p3fa zz3 xx)
  let bxz6 := p3fa (p3fd bxz2) bxz2
  let xx3mzz3 := p3fs (p3fa (p3fd xx) xx) zz3
  let y := p3fa yf (p3fm xx3mzz3 bxz6)
  let yz2 := p3fd (p3fm Y Z)
  let x := p3fs xf (p3fm bxz6 yz2)
  let z := p3fd (p3fd (p3fm yz2 yy))
  (x, y, z)

/-- A coordinate of the point's copy in the frame, after the prologue. -/
theorem d3_copy_coord {Ms M : Word → BitVec 8} {G sf a : Word}
    (pcp : ∀ k, k < 36 → memLoad32 Ms (G + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 (4 * k)) =
      memLoad32 M (sf + BitVec.ofNat 32 (4 * k)))
    (c off : Nat) (ha : a = sf + BitVec.ofNat 32 off) (hc : c = 0x10 + off) (hoff : off + 48 ≤ 144)
    (h4 : off % 4 = 0) : wordsAt Ms (G + BitVec.ofNat 32 c) 12 = wordsAt M a 12 := by
  subst ha hc
  unfold wordsAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have := pcp (off / 4 + i) (by omega)
  simp only [add_ofNat_assoc] at this ⊢
  rw [show 0x10 + 4 * (off / 4 + i) = 0x10 + off + 4 * i by omega,
    show 4 * (off / 4 + i) = off + 4 * i by omega] at this
  exact this

/-- A coordinate of the result after the epilogue's `memcpy`. -/
theorem d3_out_coord {M : Word → BitVec 8} {out G a : Word} (off c : Nat) (ha : a = out + BitVec.ofNat 32 off)
    (hc : c = 0x10 + off) (hoff : off + 48 ≤ 144) (h4 : off % 4 = 0) (hwo : out.toNat + 144 < 2 ^ 32) :
    wordsAt (copyWords M out (G + BitVec.ofNat 32 0x10) 36) a 12 = wordsAt M (G + BitVec.ofNat 32 c) 12 := by
  subst ha hc
  unfold wordsAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have := copyWords_load (M := M) (dst := out) (src := G + BitVec.ofNat 32 0x10) 36 (off / 4 + i) (by omega)
    (by omega)
  simp only [add_ofNat_assoc] at this ⊢
  rw [show 4 * (off / 4 + i) = off + 4 * i by omega] at this
  rw [this, Nat.add_assoc]

end C3.RV32
