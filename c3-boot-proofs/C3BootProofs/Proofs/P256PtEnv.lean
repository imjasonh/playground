import C3BootProofs.Proofs.FieldSquare
import C3BootProofs.Proofs.FieldDouble
import C3BootProofs.Proofs.FieldSubOp
import C3BootProofs.Proofs.PointEnv
import C3BootProofs.Proofs.Sha256LoopFrame

/-!
# Where the compiled P-256 point doubling runs, and its calls

`<ProjectivePoint<p256::NistP256> as Group>::double`, as compiled, has the
P-384 doubling's shape (`P384PtEnv.lean`) at P-256's sizes: it copies the
point into a 0x2E0-byte frame and makes 37 calls, to
`FieldElement::multiply` and `square`, `field_impl::add` and `sub`,
`FieldElement::double`, and `memcpy`. `multiply` needs the most stack below
the frame, 0x130 bytes, so the stack it may change is the 0x410 bytes below
`sp`, which this file calls `S`; the frame starts 0x130 bytes into it.

`D2Inv` is what holds at each point between the calls, and the lemmas here
carry it across one call or one argument instruction, with the call's
result.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem p2pd_at_0 : fetchRel p256PtDoubleCode 0x0 = some (.aluImm .add sp sp 0xFFFFFD20, 4) := by decide
theorem p2pd_at_4 : fetchRel p256PtDoubleCode 0x4 = some (.aluImm .add a2 sp 0x280, 2) := by decide
theorem p2pd_at_6 : fetchRel p256PtDoubleCode 0x6 = some (.store .sw a2 ra 0x5C, 4) := by decide
theorem p2pd_at_a : fetchRel p256PtDoubleCode 0xA = some (.store .sw a2 (8 : Fin 32) 0x58, 2) := by decide
theorem p2pd_at_c : fetchRel p256PtDoubleCode 0xC = some (.store .sw a2 (9 : Fin 32) 0x54, 2) := by decide
theorem p2pd_at_e : fetchRel p256PtDoubleCode 0xE = some (.store .sw a2 (18 : Fin 32) 0x50, 4) := by decide
theorem p2pd_at_12 : fetchRel p256PtDoubleCode 0x12 = some (.store .sw a2 (19 : Fin 32) 0x4C, 4) := by decide
theorem p2pd_at_16 : fetchRel p256PtDoubleCode 0x16 = some (.store .sw a2 (20 : Fin 32) 0x48, 4) := by decide
theorem p2pd_at_1a : fetchRel p256PtDoubleCode 0x1A = some (.store .sw a2 (21 : Fin 32) 0x44, 4) := by decide
theorem p2pd_at_1e : fetchRel p256PtDoubleCode 0x1E = some (.store .sw a2 (22 : Fin 32) 0x40, 4) := by decide
theorem p2pd_at_22 : fetchRel p256PtDoubleCode 0x22 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem p2pd_at_24 : fetchRel p256PtDoubleCode 0x24 = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem p2pd_at_26 : fetchRel p256PtDoubleCode 0x26 = some (.alu .add a0 x0 sp, 2) := by decide
theorem p2pd_at_28 : fetchRel p256PtDoubleCode 0x28 = some (.aluImm .add a2 x0 0x60, 4) := by decide
theorem p2pd_at_2c : fetchRel p256PtDoubleCode 0x2C = some (.auipc ra 0x12000, 4) := by decide
theorem p2pd_at_30 : fetchRel p256PtDoubleCode 0x30 = some (.jalr ra ra 0x4D8, 4) := by decide
theorem p2pd_at_34 : fetchRel p256PtDoubleCode 0x34 = some (.aluImm .add a0 sp 0x160, 2) := by decide
theorem p2pd_at_36 : fetchRel p256PtDoubleCode 0x36 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem p2pd_at_38 : fetchRel p256PtDoubleCode 0x38 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_3c : fetchRel p256PtDoubleCode 0x3C = some (.jalr ra ra 0xFFFFFDC6, 4) := by decide
theorem p2pd_at_40 : fetchRel p256PtDoubleCode 0x40 = some (.aluImm .add (18 : Fin 32) sp 0x20, 4) := by decide
theorem p2pd_at_44 : fetchRel p256PtDoubleCode 0x44 = some (.aluImm .add a0 sp 0x220, 2) := by decide
theorem p2pd_at_46 : fetchRel p256PtDoubleCode 0x46 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem p2pd_at_48 : fetchRel p256PtDoubleCode 0x48 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_4c : fetchRel p256PtDoubleCode 0x4C = some (.jalr ra ra 0xFFFFFDB6, 4) := by decide
theorem p2pd_at_50 : fetchRel p256PtDoubleCode 0x50 = some (.aluImm .add (19 : Fin 32) sp 0x40, 4) := by decide
theorem p2pd_at_54 : fetchRel p256PtDoubleCode 0x54 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem p2pd_at_56 : fetchRel p256PtDoubleCode 0x56 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem p2pd_at_58 : fetchRel p256PtDoubleCode 0x58 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_5c : fetchRel p256PtDoubleCode 0x5C = some (.jalr ra ra 0xFFFFFDA6, 4) := by decide
theorem p2pd_at_60 : fetchRel p256PtDoubleCode 0x60 = some (.aluImm .add (22 : Fin 32) (9 : Fin 32) 0x20, 4) := by decide
theorem p2pd_at_64 : fetchRel p256PtDoubleCode 0x64 = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_66 : fetchRel p256PtDoubleCode 0x66 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem p2pd_at_68 : fetchRel p256PtDoubleCode 0x68 = some (.alu .add a2 x0 (22 : Fin 32), 2) := by decide
theorem p2pd_at_6a : fetchRel p256PtDoubleCode 0x6A = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_6e : fetchRel p256PtDoubleCode 0x6E = some (.jalr ra ra 0x2A8, 4) := by decide
theorem p2pd_at_72 : fetchRel p256PtDoubleCode 0x72 = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem p2pd_at_74 : fetchRel p256PtDoubleCode 0x74 = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p2pd_at_76 : fetchRel p256PtDoubleCode 0x76 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_7a : fetchRel p256PtDoubleCode 0x7A = some (.jalr ra ra 0xFFFFFD7E, 4) := by decide
theorem p2pd_at_7e : fetchRel p256PtDoubleCode 0x7E = some (.aluImm .add (8 : Fin 32) (9 : Fin 32) 0x40, 4) := by decide
theorem p2pd_at_82 : fetchRel p256PtDoubleCode 0x82 = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_84 : fetchRel p256PtDoubleCode 0x84 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem p2pd_at_86 : fetchRel p256PtDoubleCode 0x86 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem p2pd_at_88 : fetchRel p256PtDoubleCode 0x88 = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_8c : fetchRel p256PtDoubleCode 0x8C = some (.jalr ra ra 0x28A, 4) := by decide
theorem p2pd_at_90 : fetchRel p256PtDoubleCode 0x90 = some (.aluImm .add a0 sp 0x1E0, 2) := by decide
theorem p2pd_at_92 : fetchRel p256PtDoubleCode 0x92 = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p2pd_at_94 : fetchRel p256PtDoubleCode 0x94 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_98 : fetchRel p256PtDoubleCode 0x98 = some (.jalr ra ra 0xFFFFFD60, 4) := by decide
theorem p2pd_at_9c : fetchRel p256PtDoubleCode 0x9C = some (.lui (21 : Fin 32) 0x3FCC4000, 4) := by decide
theorem p2pd_at_a0 : fetchRel p256PtDoubleCode 0xA0 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x368, 4) := by decide
theorem p2pd_at_a4 : fetchRel p256PtDoubleCode 0xA4 = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_a6 : fetchRel p256PtDoubleCode 0xA6 = some (.aluImm .add a2 sp 0x100, 2) := by decide
theorem p2pd_at_a8 : fetchRel p256PtDoubleCode 0xA8 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem p2pd_at_aa : fetchRel p256PtDoubleCode 0xAA = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_ae : fetchRel p256PtDoubleCode 0xAE = some (.jalr ra ra 0x268, 4) := by decide
theorem p2pd_at_b2 : fetchRel p256PtDoubleCode 0xB2 = some (.aluImm .add a0 sp 0x80, 2) := by decide
theorem p2pd_at_b4 : fetchRel p256PtDoubleCode 0xB4 = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p2pd_at_b6 : fetchRel p256PtDoubleCode 0xB6 = some (.aluImm .add a2 sp 0x1E0, 2) := by decide
theorem p2pd_at_b8 : fetchRel p256PtDoubleCode 0xB8 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_bc : fetchRel p256PtDoubleCode 0xBC = some (.jalr ra ra 0xFFFFFB42, 4) := by decide
theorem p2pd_at_c0 : fetchRel p256PtDoubleCode 0xC0 = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_c2 : fetchRel p256PtDoubleCode 0xC2 = some (.aluImm .add a1 sp 0x80, 2) := by decide
theorem p2pd_at_c4 : fetchRel p256PtDoubleCode 0xC4 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_c8 : fetchRel p256PtDoubleCode 0xC8 = some (.jalr ra ra 0xFFFFFD30, 4) := by decide
theorem p2pd_at_cc : fetchRel p256PtDoubleCode 0xCC = some (.aluImm .add a0 sp 0x200, 2) := by decide
theorem p2pd_at_ce : fetchRel p256PtDoubleCode 0xCE = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p2pd_at_d0 : fetchRel p256PtDoubleCode 0xD0 = some (.aluImm .add a2 sp 0x80, 2) := by decide
theorem p2pd_at_d2 : fetchRel p256PtDoubleCode 0xD2 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_d6 : fetchRel p256PtDoubleCode 0xD6 = some (.jalr ra ra 0xFFFFFA06, 4) := by decide
theorem p2pd_at_da : fetchRel p256PtDoubleCode 0xDA = some (.aluImm .add a0 sp 0x240, 2) := by decide
theorem p2pd_at_dc : fetchRel p256PtDoubleCode 0xDC = some (.aluImm .add a1 sp 0x220, 2) := by decide
theorem p2pd_at_de : fetchRel p256PtDoubleCode 0xDE = some (.aluImm .add a2 sp 0x200, 2) := by decide
theorem p2pd_at_e0 : fetchRel p256PtDoubleCode 0xE0 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_e4 : fetchRel p256PtDoubleCode 0xE4 = some (.jalr ra ra 0xFFFFFB1A, 4) := by decide
theorem p2pd_at_e8 : fetchRel p256PtDoubleCode 0xE8 = some (.aluImm .add a0 sp 0xA0, 2) := by decide
theorem p2pd_at_ea : fetchRel p256PtDoubleCode 0xEA = some (.aluImm .add a1 sp 0x220, 2) := by decide
theorem p2pd_at_ec : fetchRel p256PtDoubleCode 0xEC = some (.aluImm .add a2 sp 0x200, 2) := by decide
theorem p2pd_at_ee : fetchRel p256PtDoubleCode 0xEE = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_f2 : fetchRel p256PtDoubleCode 0xF2 = some (.jalr ra ra 0xFFFFF9EA, 4) := by decide
theorem p2pd_at_f6 : fetchRel p256PtDoubleCode 0xF6 = some (.aluImm .add a0 sp 0xC0, 2) := by decide
theorem p2pd_at_f8 : fetchRel p256PtDoubleCode 0xF8 = some (.aluImm .add a1 sp 0xA0, 2) := by decide
theorem p2pd_at_fa : fetchRel p256PtDoubleCode 0xFA = some (.aluImm .add a2 sp 0x240, 2) := by decide
theorem p2pd_at_fc : fetchRel p256PtDoubleCode 0xFC = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_100 : fetchRel p256PtDoubleCode 0x100 = some (.jalr ra ra 0x216, 4) := by decide
theorem p2pd_at_104 : fetchRel p256PtDoubleCode 0x104 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem p2pd_at_106 : fetchRel p256PtDoubleCode 0x106 = some (.aluImm .add a1 sp 0x240, 2) := by decide
theorem p2pd_at_108 : fetchRel p256PtDoubleCode 0x108 = some (.aluImm .add a2 sp 0x60, 2) := by decide
theorem p2pd_at_10a : fetchRel p256PtDoubleCode 0x10A = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_10e : fetchRel p256PtDoubleCode 0x10E = some (.jalr ra ra 0x208, 4) := by decide
theorem p2pd_at_112 : fetchRel p256PtDoubleCode 0x112 = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_114 : fetchRel p256PtDoubleCode 0x114 = some (.aluImm .add a1 sp 0x100, 2) := by decide
theorem p2pd_at_116 : fetchRel p256PtDoubleCode 0x116 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_11a : fetchRel p256PtDoubleCode 0x11A = some (.jalr ra ra 0xFFFFFCDE, 4) := by decide
theorem p2pd_at_11e : fetchRel p256PtDoubleCode 0x11E = some (.aluImm .add a0 sp 0x260, 2) := by decide
theorem p2pd_at_120 : fetchRel p256PtDoubleCode 0x120 = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p2pd_at_122 : fetchRel p256PtDoubleCode 0x122 = some (.aluImm .add a2 sp 0x100, 2) := by decide
theorem p2pd_at_124 : fetchRel p256PtDoubleCode 0x124 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_128 : fetchRel p256PtDoubleCode 0x128 = some (.jalr ra ra 0xFFFFF9B4, 4) := by decide
theorem p2pd_at_12c : fetchRel p256PtDoubleCode 0x12C = some (.aluImm .add a0 sp 0x1A0, 2) := by decide
theorem p2pd_at_12e : fetchRel p256PtDoubleCode 0x12E = some (.aluImm .add a2 sp 0x1E0, 2) := by decide
theorem p2pd_at_130 : fetchRel p256PtDoubleCode 0x130 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem p2pd_at_132 : fetchRel p256PtDoubleCode 0x132 = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_136 : fetchRel p256PtDoubleCode 0x136 = some (.jalr ra ra 0x1E0, 4) := by decide
theorem p2pd_at_13a : fetchRel p256PtDoubleCode 0x13A = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_13c : fetchRel p256PtDoubleCode 0x13C = some (.aluImm .add a1 sp 0x260, 2) := by decide
theorem p2pd_at_13e : fetchRel p256PtDoubleCode 0x13E = some (.aluImm .add a2 sp 0x160, 2) := by decide
theorem p2pd_at_140 : fetchRel p256PtDoubleCode 0x140 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_144 : fetchRel p256PtDoubleCode 0x144 = some (.jalr ra ra 0xFFFFF998, 4) := by decide
theorem p2pd_at_148 : fetchRel p256PtDoubleCode 0x148 = some (.aluImm .add a0 sp 0x120, 2) := by decide
theorem p2pd_at_14a : fetchRel p256PtDoubleCode 0x14A = some (.aluImm .add a1 sp 0x1A0, 2) := by decide
theorem p2pd_at_14c : fetchRel p256PtDoubleCode 0x14C = some (.aluImm .add a2 sp 0x1C0, 2) := by decide
theorem p2pd_at_14e : fetchRel p256PtDoubleCode 0x14E = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_152 : fetchRel p256PtDoubleCode 0x152 = some (.jalr ra ra 0xFFFFFAAC, 4) := by decide
theorem p2pd_at_156 : fetchRel p256PtDoubleCode 0x156 = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_158 : fetchRel p256PtDoubleCode 0x158 = some (.aluImm .add a1 sp 0x120, 2) := by decide
theorem p2pd_at_15a : fetchRel p256PtDoubleCode 0x15A = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_15e : fetchRel p256PtDoubleCode 0x15E = some (.jalr ra ra 0xFFFFFC9A, 4) := by decide
theorem p2pd_at_162 : fetchRel p256PtDoubleCode 0x162 = some (.aluImm .add a0 sp 0x280, 2) := by decide
theorem p2pd_at_164 : fetchRel p256PtDoubleCode 0x164 = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p2pd_at_166 : fetchRel p256PtDoubleCode 0x166 = some (.aluImm .add a2 sp 0x120, 2) := by decide
theorem p2pd_at_168 : fetchRel p256PtDoubleCode 0x168 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_16c : fetchRel p256PtDoubleCode 0x16C = some (.jalr ra ra 0xFFFFF970, 4) := by decide
theorem p2pd_at_170 : fetchRel p256PtDoubleCode 0x170 = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_172 : fetchRel p256PtDoubleCode 0x172 = some (.aluImm .add a1 sp 0x160, 2) := by decide
theorem p2pd_at_174 : fetchRel p256PtDoubleCode 0x174 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_178 : fetchRel p256PtDoubleCode 0x178 = some (.jalr ra ra 0xFFFFFC80, 4) := by decide
theorem p2pd_at_17c : fetchRel p256PtDoubleCode 0x17C = some (.aluImm .add a0 sp 0x1A0, 2) := by decide
theorem p2pd_at_17e : fetchRel p256PtDoubleCode 0x17E = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p2pd_at_180 : fetchRel p256PtDoubleCode 0x180 = some (.aluImm .add a2 sp 0x160, 2) := by decide
theorem p2pd_at_182 : fetchRel p256PtDoubleCode 0x182 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_186 : fetchRel p256PtDoubleCode 0x186 = some (.jalr ra ra 0xFFFFF956, 4) := by decide
theorem p2pd_at_18a : fetchRel p256PtDoubleCode 0x18A = some (.aluImm .add a0 sp 0x140, 2) := by decide
theorem p2pd_at_18c : fetchRel p256PtDoubleCode 0x18C = some (.aluImm .add a1 sp 0x1A0, 2) := by decide
theorem p2pd_at_18e : fetchRel p256PtDoubleCode 0x18E = some (.aluImm .add a2 sp 0x260, 2) := by decide
theorem p2pd_at_190 : fetchRel p256PtDoubleCode 0x190 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_194 : fetchRel p256PtDoubleCode 0x194 = some (.jalr ra ra 0xFFFFFA6A, 4) := by decide
theorem p2pd_at_198 : fetchRel p256PtDoubleCode 0x198 = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_19a : fetchRel p256PtDoubleCode 0x19A = some (.aluImm .add a1 sp 0x140, 2) := by decide
theorem p2pd_at_19c : fetchRel p256PtDoubleCode 0x19C = some (.aluImm .add a2 sp 0x280, 2) := by decide
theorem p2pd_at_19e : fetchRel p256PtDoubleCode 0x19E = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_1a2 : fetchRel p256PtDoubleCode 0x1A2 = some (.jalr ra ra 0x174, 4) := by decide
theorem p2pd_at_1a6 : fetchRel p256PtDoubleCode 0x1A6 = some (.aluImm .add a0 sp 0x180, 2) := by decide
theorem p2pd_at_1a8 : fetchRel p256PtDoubleCode 0x1A8 = some (.aluImm .add a1 sp 0xC0, 2) := by decide
theorem p2pd_at_1aa : fetchRel p256PtDoubleCode 0x1AA = some (.aluImm .add a2 sp 0x1C0, 2) := by decide
theorem p2pd_at_1ac : fetchRel p256PtDoubleCode 0x1AC = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_1b0 : fetchRel p256PtDoubleCode 0x1B0 = some (.jalr ra ra 0xFFFFF92C, 4) := by decide
theorem p2pd_at_1b4 : fetchRel p256PtDoubleCode 0x1B4 = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_1b6 : fetchRel p256PtDoubleCode 0x1B6 = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem p2pd_at_1b8 : fetchRel p256PtDoubleCode 0x1B8 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem p2pd_at_1ba : fetchRel p256PtDoubleCode 0x1BA = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_1be : fetchRel p256PtDoubleCode 0x1BE = some (.jalr ra ra 0x158, 4) := by decide
theorem p2pd_at_1c2 : fetchRel p256PtDoubleCode 0x1C2 = some (.aluImm .add a0 sp 0x2A0, 2) := by decide
theorem p2pd_at_1c4 : fetchRel p256PtDoubleCode 0x1C4 = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p2pd_at_1c6 : fetchRel p256PtDoubleCode 0x1C6 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_1ca : fetchRel p256PtDoubleCode 0x1CA = some (.jalr ra ra 0xFFFFFC2E, 4) := by decide
theorem p2pd_at_1ce : fetchRel p256PtDoubleCode 0x1CE = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_1d0 : fetchRel p256PtDoubleCode 0x1D0 = some (.aluImm .add a1 sp 0x280, 2) := by decide
theorem p2pd_at_1d2 : fetchRel p256PtDoubleCode 0x1D2 = some (.aluImm .add a2 sp 0x2A0, 2) := by decide
theorem p2pd_at_1d4 : fetchRel p256PtDoubleCode 0x1D4 = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_1d8 : fetchRel p256PtDoubleCode 0x1D8 = some (.jalr ra ra 0x13E, 4) := by decide
theorem p2pd_at_1dc : fetchRel p256PtDoubleCode 0x1DC = some (.alu .add a0 x0 sp, 2) := by decide
theorem p2pd_at_1de : fetchRel p256PtDoubleCode 0x1DE = some (.aluImm .add a1 sp 0xE0, 2) := by decide
theorem p2pd_at_1e0 : fetchRel p256PtDoubleCode 0x1E0 = some (.aluImm .add a2 sp 0x1C0, 2) := by decide
theorem p2pd_at_1e2 : fetchRel p256PtDoubleCode 0x1E2 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_1e6 : fetchRel p256PtDoubleCode 0x1E6 = some (.jalr ra ra 0xFFFFFA18, 4) := by decide
theorem p2pd_at_1ea : fetchRel p256PtDoubleCode 0x1EA = some (.aluImm .add a0 sp 0x1C0, 2) := by decide
theorem p2pd_at_1ec : fetchRel p256PtDoubleCode 0x1EC = some (.aluImm .add a1 sp 0x2A0, 2) := by decide
theorem p2pd_at_1ee : fetchRel p256PtDoubleCode 0x1EE = some (.aluImm .add a2 sp 0x220, 2) := by decide
theorem p2pd_at_1f0 : fetchRel p256PtDoubleCode 0x1F0 = some (.auipc ra 0xF000, 4) := by decide
theorem p2pd_at_1f4 : fetchRel p256PtDoubleCode 0x1F4 = some (.jalr ra ra 0x122, 4) := by decide
theorem p2pd_at_1f8 : fetchRel p256PtDoubleCode 0x1F8 = some (.aluImm .add a0 sp 0x1A0, 2) := by decide
theorem p2pd_at_1fa : fetchRel p256PtDoubleCode 0x1FA = some (.aluImm .add a1 sp 0x1C0, 2) := by decide
theorem p2pd_at_1fc : fetchRel p256PtDoubleCode 0x1FC = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_200 : fetchRel p256PtDoubleCode 0x200 = some (.jalr ra ra 0xFFFFFBF8, 4) := by decide
theorem p2pd_at_204 : fetchRel p256PtDoubleCode 0x204 = some (.aluImm .add a1 sp 0x1A0, 2) := by decide
theorem p2pd_at_206 : fetchRel p256PtDoubleCode 0x206 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem p2pd_at_208 : fetchRel p256PtDoubleCode 0x208 = some (.auipc ra 0x10000, 4) := by decide
theorem p2pd_at_20c : fetchRel p256PtDoubleCode 0x20C = some (.jalr ra ra 0xFFFFFBEC, 4) := by decide
theorem p2pd_at_210 : fetchRel p256PtDoubleCode 0x210 = some (.aluImm .add a1 sp 0x180, 2) := by decide
theorem p2pd_at_212 : fetchRel p256PtDoubleCode 0x212 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem p2pd_at_216 : fetchRel p256PtDoubleCode 0x216 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem p2pd_at_218 : fetchRel p256PtDoubleCode 0x218 = some (.auipc ra 0x12000, 4) := by decide
theorem p2pd_at_21c : fetchRel p256PtDoubleCode 0x21C = some (.jalr ra ra 0x2EC, 4) := by decide
theorem p2pd_at_220 : fetchRel p256PtDoubleCode 0x220 = some (.alu .add a1 x0 sp, 2) := by decide
theorem p2pd_at_222 : fetchRel p256PtDoubleCode 0x222 = some (.aluImm .add a2 x0 0x60, 4) := by decide
theorem p2pd_at_226 : fetchRel p256PtDoubleCode 0x226 = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem p2pd_at_228 : fetchRel p256PtDoubleCode 0x228 = some (.auipc ra 0x12000, 4) := by decide
theorem p2pd_at_22c : fetchRel p256PtDoubleCode 0x22C = some (.jalr ra ra 0x2DC, 4) := by decide
theorem p2pd_at_230 : fetchRel p256PtDoubleCode 0x230 = some (.aluImm .add a0 sp 0x280, 2) := by decide
theorem p2pd_at_232 : fetchRel p256PtDoubleCode 0x232 = some (.load .lw ra a0 0x5C, 4) := by decide
theorem p2pd_at_236 : fetchRel p256PtDoubleCode 0x236 = some (.load .lw (8 : Fin 32) a0 0x58, 2) := by decide
theorem p2pd_at_238 : fetchRel p256PtDoubleCode 0x238 = some (.load .lw (9 : Fin 32) a0 0x54, 2) := by decide
theorem p2pd_at_23a : fetchRel p256PtDoubleCode 0x23A = some (.load .lw (18 : Fin 32) a0 0x50, 4) := by decide
theorem p2pd_at_23e : fetchRel p256PtDoubleCode 0x23E = some (.load .lw (19 : Fin 32) a0 0x4C, 4) := by decide
theorem p2pd_at_242 : fetchRel p256PtDoubleCode 0x242 = some (.load .lw (20 : Fin 32) a0 0x48, 4) := by decide
theorem p2pd_at_246 : fetchRel p256PtDoubleCode 0x246 = some (.load .lw (21 : Fin 32) a0 0x44, 4) := by decide
theorem p2pd_at_24a : fetchRel p256PtDoubleCode 0x24A = some (.load .lw (22 : Fin 32) a0 0x40, 4) := by decide
theorem p2pd_at_24e : fetchRel p256PtDoubleCode 0x24E = some (.aluImm .add sp sp 0x2E0, 4) := by decide
theorem p2pd_at_252 : fetchRel p256PtDoubleCode 0x252 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The bottom of the stack the point doubling may change. -/
abbrev d2S (sp0 : Word) : Word := sp0 + 0xFFFFFBF0

/-- The point doubling's frame. -/
abbrev d2G (sp0 : Word) : Word := sp0 + 0xFFFFFD20

/-- Where the point doubling runs: its code at `P`, its callees and theirs
where the image puts them, `b`, the point at `sf` and the result at `out`,
each 96 bytes and aligned, and the 0x410 bytes of stack below `sp0` apart
from the code, `b`, the point, and the result. The result's writes keep
`out` apart from the code they could reach. -/
structure D2Env (M : Word → BitVec 8) (P sp0 out sf : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p256PtDoubleCode
  mul : CodeIn M (P + 0xF312) fieldMulCode
  wm : CodeIn M (P + 0xB056) wideMulCode
  mset : CodeIn M (P + 0x1249C) memsetCode
  stub : CodeIn M (P + 0x12504) memcpyStubCode
  body : CodeIn M (P + 0x1250C) memcpyBodyCode
  si : CodeIn M (P + 0xF71E) subInnerCode
  bsub : CodeIn M (siBsub (P + 0xF71E)) borrowingSubCode
  add : CodeIn M (P + 0xFAD8) fieldAddCode
  sub : CodeIn M (P + 0xFBFA) fieldSubCode
  dbl : CodeIn M (P + 0xFDF4) fieldDoubleCode
  sqr : CodeIn M (P + 0xFDFE) fieldSquareCode
  bconst : limbVal (wordsAt M bAddr 8) = bMont
  hsp : sp0.toNat % 4 = 0
  hS : 0x410 ≤ sp0.toNat
  hsf : sf.toNat % 4 = 0
  hout : out.toNat % 4 = 0
  hwo : out.toNat + 96 < 2 ^ 32
  sC : Sep (d2S sp0) 0x410 P p256PtDoubleCode.length
  sMul : Sep (d2S sp0) 0x410 (P + 0xF312) fieldMulCode.length
  sWm : Sep (d2S sp0) 0x410 (P + 0xB056) wideMulCode.length
  sMs : Sep (d2S sp0) 0x410 (P + 0x1249C) memsetCode.length
  sU : Sep (d2S sp0) 0x410 (P + 0x12504) memcpyStubCode.length
  sB : Sep (d2S sp0) 0x410 (P + 0x1250C) memcpyBodyCode.length
  sI : Sep (d2S sp0) 0x410 (P + 0xF71E) subInnerCode.length
  sIb : Sep (d2S sp0) 0x410 (siBsub (P + 0xF71E)) borrowingSubCode.length
  sA : Sep (d2S sp0) 0x410 (P + 0xFAD8) fieldAddCode.length
  sSb : Sep (d2S sp0) 0x410 (P + 0xFBFA) fieldSubCode.length
  sD : Sep (d2S sp0) 0x410 (P + 0xFDF4) fieldDoubleCode.length
  sQ : Sep (d2S sp0) 0x410 (P + 0xFDFE) fieldSquareCode.length
  sK : Sep (d2S sp0) 0x410 bAddr 32
  sF : Sep sf 96 (d2S sp0) 0x410
  sO : Sep out 96 (d2S sp0) 0x410
  oC : Sep out 96 P p256PtDoubleCode.length
  oB : Sep out 96 (P + 0x1250C) memcpyBodyCode.length

/-- What holds between the point doubling's calls, at offset `off`: the
registers `paKeep` names hold `V`, memory outside `S` is as it was on entry
(`M0`), and the register save slots at the frame's top hold what they held
after the prologue (`Ms`). -/
structure D2Inv (M0 : Word → BitVec 8) (P sp0 : Word) (V : Fin 32 → Word) (Ms : Word → BitVec 8)
    (M : Word → BitVec 8) (n : Machine) (off : Nat) : Prop where
  st : St M P n off (reg n)
  keep : ∀ q, paKeep q = true → reg n q = V q
  fr : ∀ x, Sep (d2S sp0) 0x410 x 1 → M x = M0 x
  sv : ∀ c, 0x2C0 ≤ c → c < 0x2E0 → M (d2G sp0 + BitVec.ofNat 32 c) = Ms (d2G sp0 + BitVec.ofNat 32 c)

/-- An operand a call may read: aligned, and apart from the callees' stack. -/
def D2Src (sp0 a : Word) : Prop := a.toNat % 4 = 0 ∧ Sep a 32 (d2S sp0) 0x130

/-- A result slot in the frame: the 32 bytes at `d`, below the save slots. -/
def D2Dst (d : Nat) : Prop := 0 ≤ d ∧ d + 32 ≤ 0x2C0 ∧ d % 4 = 0

theorem d2G_S0 (sp0 : Word) : d2G sp0 = d2S sp0 + BitVec.ofNat 32 0x130 := by
  show sp0 + 0xFFFFFD20 = sp0 + 0xFFFFFBF0 + BitVec.ofNat 32 0x130
  rw [BitVec.add_assoc]; rfl

theorem d2G_S (sp0 : Word) (c : Nat) : d2G sp0 + BitVec.ofNat 32 c = d2S sp0 + BitVec.ofNat 32 (0x130 + c) := by
  rw [← add_ofNat_assoc, ← d2G_S0]

theorem d2G_mm (sp0 : Word) : d2G sp0 + 0xFFFFFED0 = d2S sp0 := by
  show sp0 + 0xFFFFFD20 + 0xFFFFFED0 = sp0 + 0xFFFFFBF0
  rw [BitVec.add_assoc]; rfl

theorem d2G_ad (sp0 : Word) : d2G sp0 + 0xFFFFFF4C = d2S sp0 + BitVec.ofNat 32 0x7C := by
  show sp0 + 0xFFFFFD20 + 0xFFFFFF4C = sp0 + 0xFFFFFBF0 + BitVec.ofNat 32 0x7C
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

section
variable {M0 : Word → BitVec 8} {P sp0 out sf : Word}

theorem D2Env.hGw (env : D2Env M0 P sp0 out sf) : (d2G sp0).toNat = sp0.toNat - 0x2E0 := by
  have := env.hS
  show (sp0 + 0xFFFFFD20).toNat = _
  rw [BitVec.toNat_add]; have : (0xFFFFFD20 : Word).toNat = 4294966560 := rfl
  have := sp0.isLt; omega

theorem D2Env.hGa (env : D2Env M0 P sp0 out sf) : (d2G sp0).toNat % 4 = 0 :=
  aligned_add env.hsp (k := 0xFFFFFD20) (by decide)

/-- Code apart from `S` is still there. -/
theorem D2Env.codeT (_env : D2Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d2S sp0) 0x410 x 1 → M x = M0 x)
    {b : Word} {code : List Nat} (hc : CodeIn M0 b code) (hs : Sep (d2S sp0) 0x410 b code.length) :
    CodeIn M b code := fun i hi => by
  rw [fr _ (hs.subR (c := i) (l := 1) (by omega))]
  exact hc i hi

theorem s2_mm {b : Word} {k : Nat} (h : Sep (d2S sp0) 0x410 b k) : Sep (d2G sp0 + 0xFFFFFED0) 0x130 b k := by
  rw [d2G_mm]; exact sep_base0 (h.sub (c := 0) (l := 0x130) (by decide))

theorem s2_ad {b : Word} {k : Nat} (h : Sep (d2S sp0) 0x410 b k) : Sep (d2G sp0 + 0xFFFFFF4C) 0xB4 b k := by
  rw [d2G_ad]; exact h.sub (c := 0x7C) (l := 0xB4) (by decide)

theorem D2Dst.al {d : Nat} (env : D2Env M0 P sp0 out sf) (hd : D2Dst d) :
    (d2G sp0 + BitVec.ofNat 32 d).toNat % 4 = 0 := aligned_add env.hGa hd.2.2

theorem D2Dst.wr {d : Nat} (env : D2Env M0 P sp0 out sf) (hd : D2Dst d) :
    (d2G sp0 + BitVec.ofNat 32 d).toNat + 32 < 2 ^ 32 := by
  have := env.hGw; have := env.hS; have := sp0.isLt; have := hd.2.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A result slot is apart from the callees' stack. -/
theorem D2Dst.sS {d : Nat} (hd : D2Dst d) : Sep (d2G sp0 + BitVec.ofNat 32 d) 32 (d2S sp0) 0x130 := by
  rw [d2G_S]
  exact sep_base0r (sep_offsets _ (c := 0x130 + d) (n := 32) (d := 0) (k := 0x130) (.inr (by omega))
    (by have := hd.2.1; omega) (by decide))

theorem D2Dst.inS {d : Nat} (hd : D2Dst d) {b : Word} {k : Nat} (h : Sep (d2S sp0) 0x410 b k) :
    Sep (d2G sp0 + BitVec.ofNat 32 d) 32 b k := by
  rw [d2G_S]; exact h.sub (c := 0x130 + d) (l := 32) (by have := hd.2.1; omega)

/-- A frame slot below the save slots is an operand. -/
theorem d2src_slot {d : Nat} (env : D2Env M0 P sp0 out sf) (hd : D2Dst d) :
    D2Src sp0 (d2G sp0 + BitVec.ofNat 32 d) := ⟨hd.al env, hd.sS⟩

/-- A coordinate of the point is an operand. -/
theorem d2src_sf (env : D2Env M0 P sp0 out sf) (k : Nat) (hk : k + 32 ≤ 96) (hk4 : k % 4 = 0) :
    D2Src sp0 (sf + BitVec.ofNat 32 k) :=
  ⟨aligned_add env.hsf hk4, sep_base0r ((env.sF.sub (c := k) (l := 32) hk).subR (c := 0) (l := 0x130) (by decide))⟩

/-- `b` is an operand. -/
theorem d2src_b (env : D2Env M0 P sp0 out sf) : D2Src sp0 bAddr :=
  ⟨by decide, sep_base0r (env.sK.symm.subR (c := 0) (l := 0x130) (by decide))⟩

theorem D2Src.mm {a : Word} (h : D2Src sp0 a) : Sep a 32 (d2G sp0 + 0xFFFFFED0) 0x130 := by
  rw [d2G_mm]; exact h.2

theorem D2Src.ad {a : Word} (h : D2Src sp0 a) : Sep a 32 (d2G sp0 + 0xFFFFFF4C) 0xB4 := by
  rw [d2G_ad]; exact h.2.subR (c := 0x7C) (l := 0xB4) (by decide)

theorem d2_ret_even (env : D2Env M0 P sp0 out sf) {off : Nat} (hoff : off % 2 = 0) :
    (P + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = P + BitVec.ofNat 32 (off + 8) :=
  even_clear _ (even_at P env.hP (off + 8) (by omega))

/-- `FieldElement::multiply`'s environment, for a call from the point
doubling with its result in the frame. -/
theorem D2Env.fmEnv (env : D2Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d2S sp0) 0x410 x 1 → M x = M0 x) {d : Nat} {a b : Word}
    (hd : D2Dst d) (sa : D2Src sp0 a) (sb : D2Src sp0 b) :
    FMEnv M (P + 0xF312) (d2G sp0) (d2G sp0 + BitVec.ofNat 32 d) a b := by
  have cT := @D2Env.codeT _ _ _ _ _ env M fr
  have e1 : P + 0xF312 + 0xFFFFBD44 = P + 0xB056 := by rw [BitVec.add_assoc]; rfl
  have e2 : P + 0xF312 + 0x40C = P + 0xF71E := by rw [BitVec.add_assoc]; rfl
  have e5 : P + 0xB056 + 0x7446 = P + 0x1249C := by rw [BitVec.add_assoc]; rfl
  have e6 : P + 0xB056 + 0x74AE = P + 0x12504 := by rw [BitVec.add_assoc]; rfl
  have e7 : P + 0xB056 + 0x74B6 = P + 0x1250C := by rw [BitVec.add_assoc]; rfl
  have hG := env.hGw; have hS := env.hS
  refine ⟨even_at P env.hP 0xF312 (by decide), cT env.mul env.sMul,
    by rw [e1]; exact cT env.wm env.sWm,
    by rw [e1, e5]; exact cT env.mset env.sMs,
    by rw [e1, e6]; exact cT env.stub env.sU, by rw [e1, e7]; exact cT env.body env.sB,
    by rw [e2]; exact cT env.si env.sI, by rw [e2]; exact cT env.bsub env.sIb,
    env.hGa, hd.al env, sa.1, sb.1, by omega, Nat.le_of_lt (hd.wr env),
    s2_mm env.sMul, by rw [e1]; exact s2_mm env.sWm,
    by rw [e1, e5]; exact s2_mm env.sMs, by rw [e1, e6]; exact s2_mm env.sU,
    by rw [e1, e7]; exact s2_mm env.sB, by rw [e2]; exact s2_mm env.sI,
    by rw [e2]; exact s2_mm env.sIb, by rw [d2G_mm]; exact hd.sS, hd.inS env.sMul, sa.mm, sb.mm⟩

/-- `field_impl::add`'s environment, for a call from the point doubling. -/
theorem D2Env.faEnv (env : D2Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d2S sp0) 0x410 x 1 → M x = M0 x) {d : Nat} {a b : Word}
    (hd : D2Dst d) (sa : D2Src sp0 a) (sb : D2Src sp0 b) :
    FAEnv M (P + 0xFAD8) (d2G sp0) (d2G sp0 + BitVec.ofNat 32 d) a b := by
  have cT := @D2Env.codeT _ _ _ _ _ env M fr
  have e : P + 0xFAD8 + 0xFFFFFC46 = P + 0xF71E := by rw [BitVec.add_assoc]; rfl
  have hG := env.hGw; have hS := env.hS
  refine ⟨even_at P env.hP 0xFAD8 (by decide), cT env.add env.sA,
    by rw [e]; exact cT env.si env.sI, by rw [e]; exact cT env.bsub env.sIb,
    env.hGa, hd.al env, sa.1, sb.1, by omega, Nat.le_of_lt (hd.wr env), s2_ad env.sA, by rw [e]; exact s2_ad env.sI,
    by rw [e]; exact s2_ad env.sIb,
    by rw [d2G_ad]; exact hd.sS.subR (c := 0x7C) (l := 0xB4) (by decide), hd.inS env.sA, sa.ad, sb.ad⟩

/-- `field_impl::sub`'s environment, for a call from the point doubling. -/
theorem D2Env.fsEnv (env : D2Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d2S sp0) 0x410 x 1 → M x = M0 x) {d : Nat} {a b : Word}
    (hd : D2Dst d) (sa : D2Src sp0 a) (sb : D2Src sp0 b) :
    FSEnv M (P + 0xFBFA) (d2G sp0) (d2G sp0 + BitVec.ofNat 32 d) a b := by
  have cT := @D2Env.codeT _ _ _ _ _ env M fr
  have e : P + 0xFBFA + 0xFFFFFB24 = P + 0xF71E := by rw [BitVec.add_assoc]; rfl
  have hG := env.hGw; have hS := env.hS
  refine ⟨even_at P env.hP 0xFBFA (by decide), cT env.sub env.sSb,
    by rw [e]; exact cT env.si env.sI, by rw [e]; exact cT env.bsub env.sIb,
    env.hGa, hd.al env, sa.1, sb.1, by omega, Nat.le_of_lt (hd.wr env), s2_ad env.sSb, by rw [e]; exact s2_ad env.sI,
    by rw [e]; exact s2_ad env.sIb,
    by rw [d2G_ad]; exact hd.sS.subR (c := 0x7C) (l := 0xB4) (by decide), hd.inS env.sSb, sa.ad, sb.ad⟩

/-- `FieldElement::double`'s environment, for a call from the point doubling. -/
theorem D2Env.fdEnv (env : D2Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d2S sp0) 0x410 x 1 → M x = M0 x) {d : Nat} {a : Word}
    (hd : D2Dst d) (sa : D2Src sp0 a) :
    FDEnv M (P + 0xFDF4) (d2G sp0) (d2G sp0 + BitVec.ofNat 32 d) a := by
  have e : P + 0xFDF4 + 0xFFFFFCE4 = P + 0xFAD8 := by rw [BitVec.add_assoc]; rfl
  exact ⟨even_at P env.hP 0xFDF4 (by decide), env.codeT fr env.dbl env.sD, by rw [e]; exact env.faEnv fr hd sa sa⟩

/-- `FieldElement::square`'s environment, for a call from the point doubling. -/
theorem D2Env.fqEnv (env : D2Env M0 P sp0 out sf) {M : Word → BitVec 8}
    (fr : ∀ x, Sep (d2S sp0) 0x410 x 1 → M x = M0 x) {d : Nat} {a : Word}
    (hd : D2Dst d) (sa : D2Src sp0 a) :
    FQEnv M (P + 0xFDFE) (d2G sp0) (d2G sp0 + BitVec.ofNat 32 d) a := by
  have e : P + 0xFDFE + 0xFFFFF514 = P + 0xF312 := by rw [BitVec.add_assoc]; rfl
  exact ⟨even_at P env.hP 0xFDFE (by decide), env.codeT fr env.sqr env.sQ, by rw [e]; exact env.fmEnv fr hd sa sa⟩

/-- The callees' stack and a result slot leave the save slots alone. -/
theorem d2sv_keep {d c : Nat} (hd : D2Dst d) (h1 : 0x2C0 ≤ c) (h2 : c < 0x2E0) :
    Sep (d2S sp0) 0x130 (d2G sp0 + BitVec.ofNat 32 c) 1 ∧
      Sep (d2G sp0 + BitVec.ofNat 32 d) 32 (d2G sp0 + BitVec.ofNat 32 c) 1 := by
  refine ⟨?_, sep_offsets _ (.inl (by have := hd.2.1; omega)) (by have := hd.2.1; omega) (by omega)⟩
  rw [d2G_S]
  exact sep_base0 (sep_offsets _ (c := 0) (n := 0x130) (d := 0x130 + c) (k := 1) (.inl (by omega))
    (by decide) (by omega))

/-- After a call that changed only the callees' stack and a result slot, the
invariant holds at the return address. -/
theorem D2Inv.after {M Ms M' : Word → BitVec 8} {V : Fin 32 → Word} {d off : Nat} {n n' : Machine}
    (I : D2Inv M0 P sp0 V Ms M n off) (hd : D2Dst d)
    (st : St M' P n' (off + 8) (reg n')) (keep : ∀ q, paKeep q = true → reg n' q = reg n q)
    (fr : ∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) :
    D2Inv M0 P sp0 V Ms M' n' (off + 8) :=
  ⟨st, fun q hq => (keep q hq).trans (I.keep q hq),
    fun x hx => (fr x (sep_base0 (hx.sub (c := 0) (l := 0x130) (by decide))) (hd.inS hx)).trans (I.fr x hx),
    fun c h1 h2 => (fr _ (d2sv_keep hd h1 h2).1 (d2sv_keep hd h1 h2).2).trans (I.sv c h1 h2)⟩

end

section Calls
variable {M0 M Ms : Word → BitVec 8} {P sp0 out sf : Word} {V : Fin 32 → Word} {off d : Nat}
  {n : Machine} {imm o a b : Word} {A B : Nat}

set_option maxHeartbeats 1000000 in
/-- A call to `FieldElement::multiply`: the result slot gets the Montgomery
product of the operands. -/
theorem d2_mul (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d2G sp0)
    (h1 : fetchRel p256PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xF312) (hoff : off % 2 = 0)
    (hd : D2Dst d) (ha0 : reg n a0 = d2G sp0 + BitVec.ofNat 32 d)
    (sa : D2Src sp0 a) (ha1 : reg n a1 = a) (sb : D2Src sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 8) = A) (hAp : A < p256) (hB : limbVal (wordsAt M b 8) = B) (hBp : B < p256) :
    ∃ n' M', Steps n n' ∧ D2Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d2G sp0 + BitVec.ofNat 32 d) 8) = fm A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0xF312 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  obtain ⟨n', c', pc', sp', regs', val', lt', fr'⟩ := fieldMul_correct n1
    (by rw [mem1]; exact env.fmEnv I.fr hd sa sb) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (d2_ret_even env hoff)
    (by rw [r1 sp (by decide), I.keep sp rfl, hVsp])
  rw [mem1, hA, hB] at val' lt'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [d2G_mm]; exact hx) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (keep_of_call regs1 I.st.zero regs') frS, frS, ?_⟩
  exact mont_fm (lt' (mul_lt_mont hAp hBp)) val'

set_option maxHeartbeats 1000000 in
/-- A call to `FieldElement::square`. -/
theorem d2_sqr (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d2G sp0)
    (h1 : fetchRel p256PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFDFE) (hoff : off % 2 = 0)
    (hd : D2Dst d) (ha0 : reg n a0 = d2G sp0 + BitVec.ofNat 32 d)
    (sa : D2Src sp0 a) (ha1 : reg n a1 = a)
    (hA : limbVal (wordsAt M a 8) = A) (hAp : A < p256) :
    ∃ n' M', Steps n n' ∧ D2Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d2G sp0 + BitVec.ofNat 32 d) 8) = fm A A := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0xFDFE (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  obtain ⟨n', c', pc', sp', regs', val', lt', fr'⟩ := fieldSquare_correct n1
    (by rw [mem1]; exact env.fqEnv I.fr hd sa) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (d2_ret_even env hoff)
    (by rw [r1 sp (by decide), I.keep sp rfl, hVsp])
  rw [mem1, hA] at val' lt'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [d2G_mm]; exact hx) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (keep_of_call regs1 I.st.zero regs') frS, frS, ?_⟩
  exact mont_fm (lt' (mul_lt_mont hAp hAp)) val'

set_option maxHeartbeats 1000000 in
/-- A call to `field_impl::add`. -/
theorem d2_add (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d2G sp0)
    (h1 : fetchRel p256PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFAD8) (hoff : off % 2 = 0)
    (hd : D2Dst d) (ha0 : reg n a0 = d2G sp0 + BitVec.ofNat 32 d)
    (sa : D2Src sp0 a) (ha1 : reg n a1 = a) (sb : D2Src sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 8) = A) (hAp : A < p256) (hB : limbVal (wordsAt M b 8) = B) (hBp : B < p256) :
    ∃ n' M', Steps n n' ∧ D2Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d2G sp0 + BitVec.ofNat 32 d) 8) = fa A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0xFAD8 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  obtain ⟨n', c', pc', sp', regs', val', fr'⟩ := fieldAdd_correct n1
    (by rw [mem1]; exact env.faEnv I.fr hd sa sb) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (d2_ret_even env hoff)
    (by rw [r1 sp (by decide), I.keep sp rfl, hVsp])
  rw [mem1, hA, hB] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [d2G_ad]; exact hx.sub (c := 0x7C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (keep_of_call regs1 I.st.zero regs') frS, frS, ?_⟩
  rw [val', fa_eq hAp hBp]

set_option maxHeartbeats 1000000 in
/-- A call to `field_impl::sub`. -/
theorem d2_sub (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d2G sp0)
    (h1 : fetchRel p256PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFBFA) (hoff : off % 2 = 0)
    (hd : D2Dst d) (ha0 : reg n a0 = d2G sp0 + BitVec.ofNat 32 d)
    (sa : D2Src sp0 a) (ha1 : reg n a1 = a) (sb : D2Src sp0 b) (ha2 : reg n a2 = b)
    (hA : limbVal (wordsAt M a 8) = A) (hAp : A < p256) (hB : limbVal (wordsAt M b 8) = B) (hBp : B < p256) :
    ∃ n' M', Steps n n' ∧ D2Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d2G sp0 + BitVec.ofNat 32 d) 8) = fs A B := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0xFBFA (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  obtain ⟨n', c', pc', sp', regs', val', fr'⟩ := fieldSub_correct n1
    (by rw [mem1]; exact env.fsEnv I.fr hd sa sb) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (d2_ret_even env hoff)
    (by rw [r1 sp (by decide), I.keep sp rfl, hVsp])
  rw [mem1, hA, hB] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [d2G_ad]; exact hx.sub (c := 0x7C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (fun q hq => ?_) frS, frS, ?_⟩
  · have k := fun r (hr : paKeep r = false) => bkeep_ne hq hr
    rw [regs' q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl)
      (k t0 rfl)]
    exact r1 q (k ra rfl)
  · rw [val', fs_eq hAp hBp]

set_option maxHeartbeats 1000000 in
/-- A call to `FieldElement::double`. -/
theorem d2_dbl (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off) (hVsp : V sp = d2G sp0)
    (h1 : fetchRel p256PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFDF4) (hoff : off % 2 = 0)
    (hd : D2Dst d) (ha0 : reg n a0 = d2G sp0 + BitVec.ofNat 32 d)
    (sa : D2Src sp0 a) (ha1 : reg n a1 = a)
    (hA : limbVal (wordsAt M a 8) = A) (hAp : A < p256) :
    ∃ n' M', Steps n n' ∧ D2Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      limbVal (wordsAt M' (d2G sp0 + BitVec.ofNat 32 d) 8) = fd A := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0xFDF4 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  obtain ⟨n', c', pc', sp', regs', val', fr'⟩ := fieldDouble_correct n1
    (by rw [mem1]; exact env.fdEnv I.fr hd sa) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (d2_ret_even env hoff)
    (by rw [r1 sp (by decide), I.keep sp rfl, hVsp])
  rw [mem1, hA] at val'
  rw [mem1] at fr'
  have frS : ∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 →
      n'.mem x = M x := fun x hx hr => fr' x (by rw [d2G_ad]; exact hx.sub (c := 0x7C) (l := 0xB4) (by decide)) hr
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩
    (keep_of_call regs1 I.st.zero regs') frS, frS, ?_⟩
  rw [val', fd_eq hAp]

set_option maxHeartbeats 1000000 in
/-- A `memcpy` of the frame slot at `s` into the one at `d`. -/
theorem d2_cpy (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off) {s : Nat}
    (h1 : fetchRel p256PtDoubleCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256PtDoubleCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x12504) (hoff : off % 2 = 0)
    (hd : D2Dst d) (hs : D2Dst s) (hds : d + 32 ≤ s ∨ s + 32 ≤ d)
    (ha0 : reg n a0 = d2G sp0 + BitVec.ofNat 32 d)
    (ha1 : reg n a1 = d2G sp0 + BitVec.ofNat 32 s) (ha2 : reg n a2 = 0x20) :
    ∃ n' M', Steps n n' ∧ D2Inv M0 P sp0 V Ms M' n' (off + 8) ∧
      (∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x) ∧
      wordsAt M' (d2G sp0 + BitVec.ofNat 32 d) 8 = wordsAt M (d2G sp0 + BitVec.ofNat 32 s) 8 := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := I.st.callRa (env.codeT I.fr env.code env.sC) h1 h2 hb
    (even_at P env.hP 0x12504 (by decide))
  have r1 := PEnv.reg1 regs1 I.st.zero
  have e : P + 0x12504 + 8 = P + 0x1250C := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n', c', pc', mem', a0', regs'⟩ := memcpy_aligned n1 (P + 0x12504) (P + BitVec.ofNat 32 (off + 8))
    (d2G sp0 + BitVec.ofNat 32 d) (d2G sp0 + BitVec.ofNat 32 s) 8
    (fun i hi => by rw [mem1]; exact env.codeT I.fr env.stub env.sU i hi)
    (fun i hi => by rw [mem1, e]; exact env.codeT I.fr env.body env.sB i hi)
    (even_at P env.hP 0x12504 (by decide)) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]; rfl)
    (by rw [regs1]; simp +decide [upd]) (d2_ret_even env hoff) (by decide) (hd.wr env) (by decide)
    (hd.al env) (hs.al env)
    (sep_offsets _ (hds.elim (fun h => .inl (by omega)) (fun h => .inr (by omega))) (by have := hd.2.1; omega)
      (by have := hs.2.1; omega))
    (by rw [e]; exact hd.inS env.sB)
  rw [mem1] at mem'
  have out : ∀ x, Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → n'.mem x = M x := fun x hx => by
    rw [mem']; exact copyWords_outside 8 hx
  have frS : ∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → n'.mem x = M x :=
    fun x _ hx => out x hx
  refine ⟨n', n'.mem, c1.trans c', I.after hd ⟨by rw [pc'], rfl, fun _ => rfl⟩ (fun q hq => ?_) frS, frS, ?_⟩
  · have k' := fun r (hr : paKeep r = false) => bkeep_ne hq hr
    rw [regs' q (k' a1 rfl) (k' a2 rfl) (k' a3 rfl) (k' a4 rfl) (k' a5 rfl) (k' a6 rfl) (k' a7 rfl)
      (k' t0 rfl) (k' t1 rfl), r1 q (k' ra rfl)]
  · rw [mem']
    unfold wordsAt
    exact List.map_congr_left fun i hi => copyWords_load 8 i (List.mem_range.mp hi) (hd.wr env |> Nat.le_of_lt)

end Calls

section Keep
variable {M0 M M' Ms : Word → BitVec 8} {P sp0 out sf : Word} {V : Fin 32 → Word} {off : Nat} {n : Machine}

/-- An operand outside `S` reads as on entry. -/
theorem D2Inv.inp (I : D2Inv M0 P sp0 V Ms M n off) {a : Word} (h : Sep a 32 (d2S sp0) 0x410) :
    wordsAt M a 8 = wordsAt M0 a 8 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => I.fr _
    (by rw [add_ofNat_assoc]; exact h.symm.subR (c := 4 * i + j) (l := 1) (by omega))

/-- A call that changed only the callees' stack and the slot at `d` left the
slot at `c` alone. -/
theorem d2slot_keep {d c : Nat}
    (f : ∀ x, Sep (d2S sp0) 0x130 x 1 → Sep (d2G sp0 + BitVec.ofNat 32 d) 32 x 1 → M' x = M x)
    (hd : D2Dst d) (hc : D2Dst c) (hdc : d + 32 ≤ c ∨ c + 32 ≤ d) :
    wordsAt M' (d2G sp0 + BitVec.ofNat 32 c) 8 = wordsAt M (d2G sp0 + BitVec.ofNat 32 c) 8 :=
  wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc (d2G sp0) c (4 * i), add_ofNat_assoc (d2G sp0) (c + 4 * i) j]
    have := hc.2.1; have := hd.2.1
    exact f _ (by
        rw [d2G_S]
        exact sep_base0 (sep_offsets _ (c := 0) (n := 0x130) (d := 0x130 + (c + 4 * i + j)) (k := 1)
          (.inl (by omega)) (by decide) (by omega)))
      (sep_offsets _ (c := d) (n := 32) (d := c + 4 * i + j) (k := 1)
        (by rcases hdc with h | h
            · exact .inl (by omega)
            · exact .inr (by omega)) (by omega) (by omega))

end Keep

section Steps
variable {M0 M Ms : Word → BitVec 8} {P sp0 out sf : Word} {V : Fin 32 → Word} {off off' : Nat}
  {n : Machine}

/-- `addi rd, rs, imm` into a register `paKeep` doesn't name. -/
theorem d2_addi (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off)
    {rd rs : Fin 32} {imm len : Word}
    (hf : fetchRel p256PtDoubleCode off = some (.aluImm .add rd rs imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hk : paKeep rd = false) :
    ∃ n', Steps n n' ∧ D2Inv M0 P sp0 V Ms M n' off' ∧ reg n' rd = reg n rs + imm ∧
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

/-- `addi rd, rs, imm` into a register `paKeep` names: `V` changes there. -/
theorem d2_addiK (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off)
    {rd rs : Fin 32} {imm len : Word}
    (hf : fetchRel p256PtDoubleCode off = some (.aluImm .add rd rs imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (h0 : rd.val ≠ 0) :
    ∃ n', Steps n n' ∧ D2Inv M0 P sp0 (upd V rd (reg n rs + imm)) Ms M n' off' ∧
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

/-- `lui rd, imm` into a register `paKeep` names. -/
theorem d2_luiK (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off)
    {rd : Fin 32} {imm len : Word}
    (hf : fetchRel p256PtDoubleCode off = some (.lui rd imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (h0 : rd.val ≠ 0) :
    ∃ n', Steps n n' ∧ D2Inv M0 P sp0 (upd V rd imm) Ms M n' off' ∧ reg n' rd = imm := by
  obtain ⟨n', d, u⟩ := I.st.lui (env.codeT I.fr env.code env.sC) hf hn
  have same : reg n' rd = imm := by rw [u.regs, upd_same h0]
  refine ⟨n', .single d, ⟨u.self, fun q hq => ?_, I.fr, I.sv⟩, same⟩
  by_cases hq0 : q.val = 0
  · have : q = 0 := Fin.ext hq0
    subst this; simp [upd]; exact u.self.zero
  by_cases e : q = rd
  · subst e; rw [same, upd_same h0]
  · rw [u.regs, upd_ne hq0 e, upd_ne hq0 e]; exact I.keep q hq

/-- `mv rd, rs` into a register `paKeep` doesn't name. -/
theorem d2_mv (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n off)
    {rd rs : Fin 32} {len : Word}
    (hf : fetchRel p256PtDoubleCode off = some (.alu .add rd 0 rs, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hk : paKeep rd = false) :
    ∃ n', Steps n n' ∧ D2Inv M0 P sp0 V Ms M n' off' ∧ reg n' rd = reg n rs ∧
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
def d2Ps : List (Fin 32 × Word) :=
  [(ra, 0x2DC), ((8 : Fin 32), 0x2D8), ((9 : Fin 32), 0x2D4), ((18 : Fin 32), 0x2D0), ((19 : Fin 32), 0x2CC),
   ((20 : Fin 32), 0x2C8), ((21 : Fin 32), 0x2C4), ((22 : Fin 32), 0x2C0)]

set_option maxRecDepth 20000 in
theorem d2Ps_range : ∀ p ∈ d2Ps, p.2.toNat % 4 = 0 ∧ 0x2C0 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x2E0 := by decide

/-- The prologue's frame, register saves, and argument moves, from 0x0 to
0x2C. -/
def d2ProA : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFD20, .aluImm .add a2 sp 0x280, .sw a2 ra 0x5C, .sw a2 (8 : Fin 32) 0x58,
   .sw a2 (9 : Fin 32) 0x54, .sw a2 (18 : Fin 32) 0x50, .sw a2 (19 : Fin 32) 0x4C, .sw a2 (20 : Fin 32) 0x48,
   .sw a2 (21 : Fin 32) 0x44, .sw a2 (22 : Fin 32) 0x40, .alu .add (9 : Fin 32) x0 a1,
   .alu .add (20 : Fin 32) x0 a0, .alu .add a0 x0 sp, .aluImm .add a2 x0 0x60]

/-- The epilogue's `memcpy` arguments, from 0x220 to 0x228. -/
def d2EpiA : List BInstr := [.alu .add a1 x0 sp, .aluImm .add a2 x0 0x60, .alu .add a0 x0 (20 : Fin 32)]

/-- The epilogue's register restores and the frame's release, from 0x230 to
0x252. -/
def d2EpiB : List BInstr :=
  [.aluImm .add a0 sp 0x280, .lw ra a0 0x5C, .lw (8 : Fin 32) a0 0x58, .lw (9 : Fin 32) a0 0x54,
   .lw (18 : Fin 32) a0 0x50, .lw (19 : Fin 32) a0 0x4C, .lw (20 : Fin 32) a0 0x48, .lw (21 : Fin 32) a0 0x44,
   .lw (22 : Fin 32) a0 0x40, .aluImm .add sp sp 0x2E0]

section
set_option maxRecDepth 20000
theorem d2ProA_end : blockEnd p256PtDoubleCode 0x0 d2ProA = some 0x2C := by decide
theorem d2EpiA_end : blockEnd p256PtDoubleCode 0x220 d2EpiA = some 0x228 := by decide
theorem d2EpiB_end : blockEnd p256PtDoubleCode 0x230 d2EpiB = some 0x252 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem d2ProA_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock d2ProA (M, f)).1 = saveMem M (f sp + 0xFFFFFD20) f d2Ps ∧
    (runBlock d2ProA (M, f)).2 sp = f sp + 0xFFFFFD20 ∧
    (runBlock d2ProA (M, f)).2 (9 : Fin 32) = f a1 ∧ (runBlock d2ProA (M, f)).2 (20 : Fin 32) = f a0 ∧
    (runBlock d2ProA (M, f)).2 a0 = f sp + 0xFFFFFD20 ∧ (runBlock d2ProA (M, f)).2 a2 = 0x60 ∧
    ∀ q, q ≠ sp → q ≠ a0 → q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → (runBlock d2ProA (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, d2ProA, upd_app, ↓reduceIte, saveMem, d2Ps]
  refine ⟨?_, rfl, BitVec.zero_add _, BitVec.zero_add _, BitVec.zero_add _, trivial, fun q h1 h2 h3 h4 h5 => ?_⟩
  · simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [hz]; rfl
    · simp only [h0, h1, h2, h3, h4, h5, ite_false]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem d2EpiB_run {M : Word → BitVec 8} {f : Fin 32 → Word} {G : Word} (hsp : f sp = G) :
    (runBlock d2EpiB (M, f)).1 = M ∧
    (runBlock d2EpiB (M, f)).2 sp = G + 0x2E0 ∧
    (∀ r o, (r, o) ∈ d2Ps → (runBlock d2EpiB (M, f)).2 r = memLoad32 M (G + o)) ∧
    ∀ q, q.val ∉ [0, 1, 2, 8, 9, 10, 18, 19, 20, 21, 22] → (runBlock d2EpiB (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, d2EpiB, upd_app, ↓reduceIte]
  refine ⟨trivial, by rw [hsp]; rfl, fun r o h => ?_, fun q hq => ?_⟩
  · simp only [d2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
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

theorem d2_sp_lit {sp0 b : Word} {k : Nat} (h : Sep (d2S sp0) 0x410 b k) (c : Nat) (hc : c + 4 ≤ 0x410) (w : Word)
    (hw : (0xFFFFFBF0 : Word) + BitVec.ofNat 32 c = w) : Sep (sp0 + w) 4 b k := by
  rw [← hw, ← BitVec.add_assoc]; exact h.sub hc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The point doubling's prologue, to 0x34: make the frame, save `ra` and
`s0` through `s6` at its top, keep the point's and the result's addresses in
`s1` and `s4`, and copy the point into the frame's bottom. -/
theorem d2_pro (m : Machine) {P sp0 out sf : Word} (env : D2Env m.mem P sp0 out sf) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = sf) (hsp : reg m sp = sp0) :
    ∃ n Ms, Steps m n ∧ D2Inv m.mem P sp0 (reg n) Ms Ms n 0x34 ∧
      reg n sp = d2G sp0 ∧ reg n (9 : Fin 32) = sf ∧ reg n (20 : Fin 32) = out ∧
      (∀ q, paKeep q = true → q ≠ sp → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → reg n q = reg m q) ∧
      (∀ r c, (r, c) ∈ d2Ps → memLoad32 Ms (d2G sp0 + c) = reg m r) ∧
      ∀ k, k < 24 → memLoad32 Ms (d2G sp0 + BitVec.ofNat 32 (4 * k)) =
        memLoad32 m.mem (sf + BitVec.ofNat 32 (4 * k)) := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGa := env.hGa; have hGw := env.hGw; have hS := env.hS
  obtain ⟨E1, Esp, E9, E20, Ea0, Ea2, Ek⟩ := d2ProA_run (M := m.mem) (f := reg m) hz
  rw [hsp] at E1 Esp Ea0
  obtain ⟨n1, c1, u1⟩ := St.block d2ProA s0 env.code d2ProA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, d2ProA, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add, hsp, BitVec.add_assoc, BitVec.reduceAdd]
    exact ⟨⟨aligned_add env.hsp (k := 0xFFFFFFFC) (by decide), d2_sp_lit env.sC 0x40C (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFF8) (by decide), d2_sp_lit env.sC 0x408 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFF4) (by decide), d2_sp_lit env.sC 0x404 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFF0) (by decide), d2_sp_lit env.sC 0x400 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFEC) (by decide), d2_sp_lit env.sC 0x3FC (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFE8) (by decide), d2_sp_lit env.sC 0x3F8 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFE4) (by decide), d2_sp_lit env.sC 0x3F4 (by decide) _ rfl⟩, ⟨aligned_add env.hsp (k := 0xFFFFFFE0) (by decide), d2_sp_lit env.sC 0x3F0 (by decide) _ rfl⟩⟩)
  rw [E1] at u1
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (sp0 + 0xFFFFFD20) (reg m) d2Ps = Msv := ⟨_, rfl⟩
  rw [hMsv] at u1
  have frSv : ∀ x, Sep (d2S sp0) 0x410 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    refine saveMem_outside d2Ps fun p hp => ?_
    obtain ⟨_, h1, h2⟩ := d2Ps_range p hp
    have := hx.sub (c := 0x130 + p.2.toNat) (l := 4) (by omega)
    rwa [← d2G_S, ofNat_toNat_self] at this
  have cSv : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep (d2S sp0) 0x410 b code.length →
      CodeIn Msv b code := fun hc hs i hi => by
    rw [frSv _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have r1 : ∀ r, reg n1 r = (runBlock d2ProA (m.mem, reg m)).2 r := u1.regs
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.self.callRa (cSv env.code env.sC) p2pd_at_2c p2pd_at_30
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x12504 (by decide))
  have r2 := PEnv.reg1 regs2 u1.self.zero
  have e : P + 0x12504 + 8 = P + 0x1250C := by rw [BitVec.add_assoc]; rfl
  have hsfw : (d2G sp0).toNat + 4 * 24 < 2 ^ 32 := by
    have := sp0.isLt; omega
  have sDst : Sep (d2G sp0) (4 * 24) sf (4 * 24) := by
    rw [d2G_S0]; exact (env.sF.symm.sub (c := 0x130) (l := 96) (by decide))
  obtain ⟨n3, c3, pc3, mem3, a03, regs3⟩ := memcpy_aligned n2 (P + 0x12504) (P + BitVec.ofNat 32 (0x2C + 8))
    (d2G sp0) sf 24
    (fun i hi => by rw [mem2]; exact cSv env.stub env.sU i hi)
    (fun i hi => by rw [mem2, e]; exact cSv env.body env.sB i hi)
    (even_at P env.hP 0x12504 (by decide)) pc2
    (by rw [r2 a0 (by decide), r1, Ea0]) (by rw [r2 a1 (by decide), r1, Ek a1 (by decide) (by decide)
        (by decide) (by decide) (by decide), ha1])
    (by rw [r2 a2 (by decide), r1, Ea2]; rfl)
    (by rw [regs2]; simp +decide [upd]) (d2_ret_even env (off := 0x2C) (by decide)) (by decide) hsfw (by decide)
    hGa env.hsf sDst
    (by rw [e, d2G_S0]; exact env.sB.sub (c := 0x130) (l := 4 * 24) (by decide))
  rw [mem2] at mem3
  obtain ⟨Ms, hMs⟩ : ∃ Ms, copyWords Msv (d2G sp0) sf 24 = Ms := ⟨_, rfl⟩
  rw [hMs] at mem3
  have frMs : ∀ x, Sep (d2S sp0) 0x410 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs, copyWords_outside 24 (by rw [d2G_S0]; exact hx.sub (c := 0x130) (l := 4 * 24) (by decide)),
      frSv x hx]
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ ra → reg n3 q = (runBlock d2ProA (m.mem, reg m)).2 q :=
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
    have k := fun r (hr : paKeep r = false) => bkeep_ne hq hr
    rw [k3 q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl) (k t0 rfl)
      (k t1 rfl) (k ra rfl), Ek q h1 (k a0 rfl) (k a2 rfl) h2 h3]
  · intro r c h
    obtain ⟨_, h1, h2⟩ := d2Ps_range (r, c) h
    dsimp only at h1 h2
    rw [← hMs, copyWords_load_sep (by
      rw [← ofNat_toNat_self c, d2G_S, d2G_S0]
      exact sep_offsets _ (.inl (by omega)) (by omega) (by omega)), ← hMsv]
    simp only [d2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    · simp only [d2Ps, saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
  · intro k hk
    rw [← hMs, copyWords_load 24 k hk (Nat.le_of_lt hsfw)]
    exact memLoad32_congr fun j hj => frSv _ (by
      rw [add_ofNat_assoc]; exact (env.sF.sub (c := 4 * k + j) (l := 1) (by omega)).symm)

set_option maxRecDepth 20000 in
theorem d2epi_keep : ∀ q : Fin 32, paKeep q = true → q.val ∉ [0, 2, 8, 9, 18, 19, 20, 21, 22] →
    q.val ∉ [0, 1, 2, 8, 9, 10, 18, 19, 20, 21, 22] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The point doubling's epilogue, from 0x220: copy the result out of the
frame into `out`, restore `ra` and `s0` through `s6` from the save slots,
drop the frame, and return. -/
theorem d2_epi {M0 M Ms : Word → BitVec 8} {P sp0 out sf : Word} {V : Fin 32 → Word} {n : Machine}
    (env : D2Env M0 P sp0 out sf) (I : D2Inv M0 P sp0 V Ms M n 0x220) (hVsp : V sp = d2G sp0)
    (hV20 : V (20 : Fin 32) = out) :
    ∃ m', Steps n m' ∧ m'.pc = memLoad32 Ms (d2G sp0 + 0x2DC) &&& ~~~1 ∧
      m'.mem = copyWords M out (d2G sp0) 24 ∧ reg m' sp = sp0 ∧
      (∀ r c, (r, c) ∈ d2Ps → reg m' r = memLoad32 Ms (d2G sp0 + c)) ∧
      ∀ q, paKeep q = true → q.val ∉ [0, 2, 8, 9, 18, 19, 20, 21, 22] → reg m' q = V q := by
  have hGa := env.hGa; have hGw := env.hGw; have hS := env.hS
  have cM := env.codeT I.fr env.code env.sC
  obtain ⟨m1, c1, u1⟩ := St.block d2EpiA I.st cM d2EpiA_end (by simp [BlockOk, BInstr.ok, d2EpiA])
  simp only [runBlock, BInstr.run, d2EpiA] at u1
  have k1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m1 q = reg n q := fun q h0 h1 h2 => by
    rw [u1.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact I.st.zero.symm
    · simp only [upd_app, hq0, h0, h1, h2, ite_false]
  obtain ⟨m2, c2, pc2, mem2, regs2⟩ := u1.self.callRa cM p2pd_at_228 p2pd_at_22c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x12504 (by decide))
  have r2 := PEnv.reg1 regs2 u1.self.zero
  have e : P + 0x12504 + 8 = P + 0x1250C := by rw [BitVec.add_assoc]; rfl
  have hwo := env.hwo
  have sOut : Sep out (4 * 24) (d2G sp0) (4 * 24) := by
    rw [d2G_S0]; exact env.sO.subR (c := 0x130) (l := 96) (by decide)
  obtain ⟨m3, c3, pc3, mem3, a03, regs3⟩ := memcpy_aligned m2 (P + 0x12504) (P + BitVec.ofNat 32 (0x228 + 8))
    out (d2G sp0) 24
    (fun i hi => by rw [mem2]; exact env.codeT I.fr env.stub env.sU i hi)
    (fun i hi => by rw [mem2, e]; exact env.codeT I.fr env.body env.sB i hi)
    (even_at P env.hP 0x12504 (by decide)) pc2
    (by rw [r2 a0 (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]
        (try rw [I.st.zero]); rw [I.keep 20 rfl, hV20]; exact BitVec.zero_add _)
    (by rw [r2 a1 (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]
        (try rw [I.st.zero]); rw [I.keep sp rfl, hVsp]; exact BitVec.zero_add _)
    (by rw [r2 a2 (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs2]; simp +decide [upd]) (d2_ret_even env (off := 0x228) (by decide)) (by decide) (by omega)
    (by decide) env.hout hGa sOut (by rw [e]; exact env.oB)
  rw [mem2] at mem3
  obtain ⟨Mo, hMo⟩ : ∃ Mo, copyWords M out (d2G sp0) 24 = Mo := ⟨_, rfl⟩
  rw [hMo] at mem3
  have outS : ∀ x, Sep out 96 x 1 → Mo x = M x := fun x hx => by
    rw [← hMo]; exact copyWords_outside 24 hx
  have cMo : CodeIn Mo P p256PtDoubleCode := fun i hi => by
    rw [outS _ (env.oC.subR (c := i) (l := 1) (by omega))]; exact cM i hi
  have s3 : St Mo P m3 0x230 (reg m3) := ⟨by rw [pc3], mem3, fun _ => rfl⟩
  have sp3 : reg m3 sp = d2G sp0 := by
    rw [regs3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), r2 sp (by decide), k1 sp (by decide) (by decide) (by decide), I.keep sp rfl, hVsp]
  obtain ⟨E1, Esp, Eps, Ek⟩ := d2EpiB_run (M := Mo) (f := reg m3) sp3
  obtain ⟨m4, c4, u4⟩ := St.block d2EpiB s3 cMo d2EpiB_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, d2EpiB, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add, sp3, BitVec.add_assoc, BitVec.reduceAdd]
    exact ⟨aligned_add env.hsp (k := 0xFFFFFFFC) (by decide), aligned_add env.hsp (k := 0xFFFFFFF8) (by decide),
      aligned_add env.hsp (k := 0xFFFFFFF4) (by decide), aligned_add env.hsp (k := 0xFFFFFFF0) (by decide),
      aligned_add env.hsp (k := 0xFFFFFFEC) (by decide), aligned_add env.hsp (k := 0xFFFFFFE8) (by decide),
      aligned_add env.hsp (k := 0xFFFFFFE4) (by decide), aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)⟩)
  rw [E1] at u4
  obtain ⟨m5, d5, pc5, mem5, regs5⟩ := u4.jalr cMo p2pd_at_252
  have ld : ∀ c : Word, 0x2C0 ≤ c.toNat → c.toNat + 4 ≤ 0x2E0 →
      memLoad32 Mo (d2G sp0 + c) = memLoad32 Ms (d2G sp0 + c) := fun c h1 h2 =>
    memLoad32_congr fun j hj => by
      rw [outS _ (by
        rw [← ofNat_toNat_self c, add_ofNat_assoc, d2G_S]
        exact env.sO.subR (c := 0x130 + (c.toNat + j)) (l := 1) (by omega)),
        ← ofNat_toNat_self c, add_ofNat_assoc]
      exact I.sv _ (by omega) (by omega)
  have ps : ∀ r c, (r, c) ∈ d2Ps → reg m5 r = memLoad32 Ms (d2G sp0 + c) := fun r c h => by
    obtain ⟨_, h1, h2⟩ := d2Ps_range (r, c) h
    rw [regs5, Eps r c h, ld c h1 h2]
  refine ⟨m5, c1.trans (c2.trans (c3.trans (c4.trans (.single d5)))), ?_, ?_, ?_, ps, ?_⟩
  · rw [pc5, add_lit_zero, Eps ra 0x2DC (by decide), ld 0x2DC (by decide) (by decide)]
  · rw [mem5, ← hMo]
  · rw [regs5, Esp]; show sp0 + 0xFFFFFD20 + 0x2E0 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero _
  · intro q hq hn
    have k := fun r (hr : paKeep r = false) => bkeep_ne hq hr
    rw [regs5, Ek q (d2epi_keep q hq hn),
      regs3 q (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl) (k t0 rfl) (k t1 rfl),
      r2 q (k ra rfl), k1 q (k a0 rfl) (k a1 rfl) (k a2 rfl), I.keep q hq]

/-- `primeorder`'s point doubling for `a = -3` (Renes, Costello, and Batina
2015, algorithm 6), in the Rust source's order, over the field operations
modulo P-256's `p` in Montgomery form: `b` is the curve constant. -/
def p2Dbl (b X Y Z : Nat) : Nat × Nat × Nat :=
  let xx := fm X X
  let yy := fm Y Y
  let zz := fm Z Z
  let xy2 := fd (fm X Y)
  let xz2 := fd (fm X Z)
  let bzz := fs (fm b zz) xz2
  let bzz3 := fa (fd bzz) bzz
  let yymb := fs yy bzz3
  let yypb := fa yy bzz3
  let yf := fm yypb yymb
  let xf := fm yymb xy2
  let zz3 := fa (fd zz) zz
  let bxz2 := fs (fm b xz2) (fa zz3 xx)
  let bxz6 := fa (fd bxz2) bxz2
  let xx3mzz3 := fs (fa (fd xx) xx) zz3
  let y := fa yf (fm xx3mzz3 bxz6)
  let yz2 := fd (fm Y Z)
  let x := fs xf (fm bxz6 yz2)
  let z := fd (fd (fm yz2 yy))
  (x, y, z)

/-- A coordinate of the point's copy in the frame, after the prologue. -/
theorem d2_copy_coord {Ms M : Word → BitVec 8} {G sf a : Word}
    (pcp : ∀ k, k < 24 → memLoad32 Ms (G + BitVec.ofNat 32 (4 * k)) = memLoad32 M (sf + BitVec.ofNat 32 (4 * k)))
    (off : Nat) (ha : a = sf + BitVec.ofNat 32 off) (hoff : off + 32 ≤ 96) (h4 : off % 4 = 0) :
    wordsAt Ms (G + BitVec.ofNat 32 off) 8 = wordsAt M a 8 := by
  subst ha
  unfold wordsAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have := pcp (off / 4 + i) (by omega)
  simp only [add_ofNat_assoc] at this ⊢
  rw [show 4 * (off / 4 + i) = off + 4 * i by omega] at this
  exact this

/-- A coordinate of the result after the epilogue's `memcpy`. -/
theorem d2_out_coord {M : Word → BitVec 8} {out G a : Word} (off : Nat) (ha : a = out + BitVec.ofNat 32 off)
    (hoff : off + 32 ≤ 96) (h4 : off % 4 = 0) (hwo : out.toNat + 96 < 2 ^ 32) :
    wordsAt (copyWords M out G 24) a 8 = wordsAt M (G + BitVec.ofNat 32 off) 8 := by
  subst ha
  unfold wordsAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have := copyWords_load (M := M) (dst := out) (src := G) 24 (off / 4 + i) (by omega) (by omega)
  simp only [add_ofNat_assoc] at this ⊢
  rw [show 4 * (off / 4 + i) = off + 4 * i by omega] at this
  exact this

end C3.RV32
