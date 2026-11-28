import C3BootProofs.Proofs.Ed25519VerifyP4b
import C3BootProofs.Image.BootloaderData4

/-!
# `sha384`, as compiled: frame, invariant, calls, prologue, and epilogue

`sha384(data) -> [u8; 48]` keeps a 0x240-byte frame at `F` and calls
functions whose own frames reach 0x420 bytes below it, so the stack it may
write is the 0x660 bytes at `G = F - 0x420`. Between calls the state is
`HfSt`: `sp` at `F`, `gp` and `tp` as on entry, memory outside the stack as
on entry, and the slots of the twelve registers the prologue saves as after
the prologue.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem hf_at_0 : fetchRel sha384FnCode 0x0 = some (.aluImm .add sp sp 0xFFFFFDC0, 4) := by decide
theorem hf_at_4 : fetchRel sha384FnCode 0x4 = some (.aluImm .add a3 sp 0x200, 2) := by decide
theorem hf_at_6 : fetchRel sha384FnCode 0x6 = some (.store .sw a3 ra 0x3C, 4) := by decide
theorem hf_at_a : fetchRel sha384FnCode 0xA = some (.store .sw a3 (8 : Fin 32) 0x38, 2) := by decide
theorem hf_at_c : fetchRel sha384FnCode 0xC = some (.store .sw a3 (9 : Fin 32) 0x34, 2) := by decide
theorem hf_at_e : fetchRel sha384FnCode 0xE = some (.store .sw a3 (18 : Fin 32) 0x30, 4) := by decide
theorem hf_at_12 : fetchRel sha384FnCode 0x12 = some (.store .sw a3 (19 : Fin 32) 0x2C, 4) := by decide
theorem hf_at_16 : fetchRel sha384FnCode 0x16 = some (.store .sw a3 (20 : Fin 32) 0x28, 4) := by decide
theorem hf_at_1a : fetchRel sha384FnCode 0x1A = some (.store .sw a3 (21 : Fin 32) 0x24, 4) := by decide
theorem hf_at_1e : fetchRel sha384FnCode 0x1E = some (.store .sw a3 (22 : Fin 32) 0x20, 4) := by decide
theorem hf_at_22 : fetchRel sha384FnCode 0x22 = some (.store .sw a3 (23 : Fin 32) 0x1C, 4) := by decide
theorem hf_at_26 : fetchRel sha384FnCode 0x26 = some (.store .sw a3 (24 : Fin 32) 0x18, 4) := by decide
theorem hf_at_2a : fetchRel sha384FnCode 0x2A = some (.store .sw a3 (25 : Fin 32) 0x14, 4) := by decide
theorem hf_at_2e : fetchRel sha384FnCode 0x2E = some (.store .sw a3 (26 : Fin 32) 0x10, 4) := by decide
theorem hf_at_32 : fetchRel sha384FnCode 0x32 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem hf_at_34 : fetchRel sha384FnCode 0x34 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem hf_at_36 : fetchRel sha384FnCode 0x36 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem hf_at_38 : fetchRel sha384FnCode 0x38 = some (.store .sb sp x0 0x7F, 4) := by decide
theorem hf_at_3c : fetchRel sha384FnCode 0x3C = some (.aluImm .add (19 : Fin 32) sp 0x80, 4) := by decide
theorem hf_at_40 : fetchRel sha384FnCode 0x40 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem hf_at_44 : fetchRel sha384FnCode 0x44 = some (.aluImm .add a1 a1 0x430, 4) := by decide
theorem hf_at_48 : fetchRel sha384FnCode 0x48 = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem hf_at_4c : fetchRel sha384FnCode 0x4C = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem hf_at_4e : fetchRel sha384FnCode 0x4E = some (.auipc ra 0x10000, 4) := by decide
theorem hf_at_52 : fetchRel sha384FnCode 0x52 = some (.jalr ra ra 0xFFFFF9B2, 4) := by decide
theorem hf_at_56 : fetchRel sha384FnCode 0x56 = some (.aluImm .srl a2 (9 : Fin 32) 0x7, 4) := by decide
theorem hf_at_5a : fetchRel sha384FnCode 0x5A = some (.store .sw sp x0 0xC0, 2) := by decide
theorem hf_at_5c : fetchRel sha384FnCode 0x5C = some (.store .sw sp x0 0xC4, 2) := by decide
theorem hf_at_5e : fetchRel sha384FnCode 0x5E = some (.store .sw sp x0 0xC8, 2) := by decide
theorem hf_at_60 : fetchRel sha384FnCode 0x60 = some (.store .sw sp x0 0xCC, 2) := by decide
theorem hf_at_62 : fetchRel sha384FnCode 0x62 = some (.branch .beq a2 x0 0x34, 2) := by decide
theorem hf_at_64 : fetchRel sha384FnCode 0x64 = some (.lui a0 0x80000000, 4) := by decide
theorem hf_at_68 : fetchRel sha384FnCode 0x68 = some (.aluImm .add a0 a0 0xFFFFFF80, 4) := by decide
theorem hf_at_6c : fetchRel sha384FnCode 0x6C = some (.alu .and a0 a0 (9 : Fin 32), 2) := by decide
theorem hf_at_6e : fetchRel sha384FnCode 0x6E = some (.aluImm .and (9 : Fin 32) (9 : Fin 32) 0x7F, 4) := by decide
theorem hf_at_72 : fetchRel sha384FnCode 0x72 = some (.alu .add (20 : Fin 32) (8 : Fin 32) a0, 4) := by decide
theorem hf_at_76 : fetchRel sha384FnCode 0x76 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem hf_at_78 : fetchRel sha384FnCode 0x78 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem hf_at_7a : fetchRel sha384FnCode 0x7A = some (.auipc ra 0x0, 4) := by decide
theorem hf_at_7e : fetchRel sha384FnCode 0x7E = some (.jalr ra ra 0x208, 4) := by decide
theorem hf_at_82 : fetchRel sha384FnCode 0x82 = some (.store .sb sp (9 : Fin 32) 0x7F, 4) := by decide
theorem hf_at_86 : fetchRel sha384FnCode 0x86 = some (.alu .add a0 x0 sp, 2) := by decide
theorem hf_at_88 : fetchRel sha384FnCode 0x88 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem hf_at_8a : fetchRel sha384FnCode 0x8A = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem hf_at_8c : fetchRel sha384FnCode 0x8C = some (.auipc ra 0x10000, 4) := by decide
theorem hf_at_90 : fetchRel sha384FnCode 0x90 = some (.jalr ra ra 0xFFFFF974, 4) := by decide
theorem hf_at_94 : fetchRel sha384FnCode 0x94 = some (.jal x0 0x14, 2) := by decide
theorem hf_at_96 : fetchRel sha384FnCode 0x96 = some (.alu .add a0 x0 sp, 2) := by decide
theorem hf_at_98 : fetchRel sha384FnCode 0x98 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem hf_at_9a : fetchRel sha384FnCode 0x9A = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem hf_at_9c : fetchRel sha384FnCode 0x9C = some (.auipc ra 0x10000, 4) := by decide
theorem hf_at_a0 : fetchRel sha384FnCode 0xA0 = some (.jalr ra ra 0xFFFFF964, 4) := by decide
theorem hf_at_a4 : fetchRel sha384FnCode 0xA4 = some (.store .sb sp (9 : Fin 32) 0x7F, 4) := by decide
theorem hf_at_a8 : fetchRel sha384FnCode 0xA8 = some (.aluImm .add a0 sp 0xD0, 2) := by decide
theorem hf_at_aa : fetchRel sha384FnCode 0xAA = some (.alu .add a1 x0 sp, 2) := by decide
theorem hf_at_ac : fetchRel sha384FnCode 0xAC = some (.aluImm .add a2 x0 0xD0, 4) := by decide
theorem hf_at_b0 : fetchRel sha384FnCode 0xB0 = some (.aluImm .add (20 : Fin 32) sp 0xD0, 4) := by decide
theorem hf_at_b4 : fetchRel sha384FnCode 0xB4 = some (.auipc ra 0x10000, 4) := by decide
theorem hf_at_b8 : fetchRel sha384FnCode 0xB8 = some (.jalr ra ra 0xFFFFF94C, 4) := by decide
theorem hf_at_bc : fetchRel sha384FnCode 0xBC = some (.aluImm .add a0 sp 0x1A0, 2) := by decide
theorem hf_at_be : fetchRel sha384FnCode 0xBE = some (.auipc ra 0x8000, 4) := by decide
theorem hf_at_c2 : fetchRel sha384FnCode 0xC2 = some (.jalr ra ra 0x7E4, 4) := by decide
theorem hf_at_c6 : fetchRel sha384FnCode 0xC6 = some (.aluImm .add (26 : Fin 32) sp 0x150, 4) := by decide
theorem hf_at_ca : fetchRel sha384FnCode 0xCA = some (.aluImm .add a0 sp 0x1D0, 2) := by decide
theorem hf_at_cc : fetchRel sha384FnCode 0xCC = some (.aluImm .add (8 : Fin 32) sp 0x1D0, 2) := by decide
theorem hf_at_ce : fetchRel sha384FnCode 0xCE = some (.auipc ra 0x8000, 4) := by decide
theorem hf_at_d2 : fetchRel sha384FnCode 0xD2 = some (.jalr ra ra 0x7AA, 4) := by decide
theorem hf_at_d6 : fetchRel sha384FnCode 0xD6 = some (.aluImm .add a0 sp 0x180, 2) := by decide
theorem hf_at_d8 : fetchRel sha384FnCode 0xD8 = some (.load .lw (23 : Fin 32) a0 0x18, 4) := by decide
theorem hf_at_dc : fetchRel sha384FnCode 0xDC = some (.load .lw a2 a0 0x14, 2) := by decide
theorem hf_at_de : fetchRel sha384FnCode 0xDE = some (.load .lw (17 : Fin 32) a0 0x1C, 4) := by decide
theorem hf_at_e2 : fetchRel sha384FnCode 0xE2 = some (.load .lw a4 a0 0x10, 2) := by decide
theorem hf_at_e4 : fetchRel sha384FnCode 0xE4 = some (.load .lbu (25 : Fin 32) sp 0x14F, 4) := by decide
theorem hf_at_e8 : fetchRel sha384FnCode 0xE8 = some (.aluImm .srl a6 (23 : Fin 32) 0x16, 4) := by decide
theorem hf_at_ec : fetchRel sha384FnCode 0xEC = some (.aluImm .sll (5 : Fin 32) (17 : Fin 32) 0xA, 4) := by decide
theorem hf_at_f0 : fetchRel sha384FnCode 0xF0 = some (.aluImm .srl (6 : Fin 32) a2 0x16, 4) := by decide
theorem hf_at_f4 : fetchRel sha384FnCode 0xF4 = some (.aluImm .sll (7 : Fin 32) (23 : Fin 32) 0xA, 4) := by decide
theorem hf_at_f8 : fetchRel sha384FnCode 0xF8 = some (.aluImm .srl (31 : Fin 32) a4 0x16, 4) := by decide
theorem hf_at_fc : fetchRel sha384FnCode 0xFC = some (.aluImm .sll a3 a2 0xA, 4) := by decide
theorem hf_at_100 : fetchRel sha384FnCode 0x100 = some (.alu .or (28 : Fin 32) (5 : Fin 32) a6, 4) := by decide
theorem hf_at_104 : fetchRel sha384FnCode 0x104 = some (.alu .or (29 : Fin 32) (7 : Fin 32) (6 : Fin 32), 4) := by decide
theorem hf_at_108 : fetchRel sha384FnCode 0x108 = some (.alu .or (30 : Fin 32) a3 (31 : Fin 32), 4) := by decide
theorem hf_at_10c : fetchRel sha384FnCode 0x10C = some (.aluImm .sll a5 a4 0xA, 4) := by decide
theorem hf_at_110 : fetchRel sha384FnCode 0x110 = some (.aluImm .sll a0 (25 : Fin 32) 0x3, 4) := by decide
theorem hf_at_114 : fetchRel sha384FnCode 0x114 = some (.alu .or a0 a0 a5, 2) := by decide
theorem hf_at_116 : fetchRel sha384FnCode 0x116 = some (.lui (19 : Fin 32) 0x10000, 2) := by decide
theorem hf_at_118 : fetchRel sha384FnCode 0x118 = some (.aluImm .sll a4 a4 0x2, 2) := by decide
theorem hf_at_11a : fetchRel sha384FnCode 0x11A = some (.aluImm .add a1 (19 : Fin 32) 0xFFFFFF00, 4) := by decide
theorem hf_at_11e : fetchRel sha384FnCode 0x11E = some (.alu .and a4 a4 a1, 2) := by decide
theorem hf_at_120 : fetchRel sha384FnCode 0x120 = some (.aluImm .srl a5 a5 0x18, 2) := by decide
theorem hf_at_122 : fetchRel sha384FnCode 0x122 = some (.alu .or a4 a4 a5, 2) := by decide
theorem hf_at_124 : fetchRel sha384FnCode 0x124 = some (.alu .and a0 a0 a1, 2) := by decide
theorem hf_at_126 : fetchRel sha384FnCode 0x126 = some (.aluImm .sll a0 a0 0x8, 2) := by decide
theorem hf_at_128 : fetchRel sha384FnCode 0x128 = some (.aluImm .sll a5 (25 : Fin 32) 0x1B, 4) := by decide
theorem hf_at_12c : fetchRel sha384FnCode 0x12C = some (.alu .or a4 a4 a5, 2) := by decide
theorem hf_at_12e : fetchRel sha384FnCode 0x12E = some (.aluImm .sll a2 a2 0x2, 2) := by decide
theorem hf_at_130 : fetchRel sha384FnCode 0x130 = some (.alu .and a2 a2 a1, 2) := by decide
theorem hf_at_132 : fetchRel sha384FnCode 0x132 = some (.aluImm .srl a3 a3 0x18, 2) := by decide
theorem hf_at_134 : fetchRel sha384FnCode 0x134 = some (.alu .or (21 : Fin 32) a4 a0, 4) := by decide
theorem hf_at_138 : fetchRel sha384FnCode 0x138 = some (.alu .or a2 a2 a3, 2) := by decide
theorem hf_at_13a : fetchRel sha384FnCode 0x13A = some (.alu .and a0 (30 : Fin 32) a1, 4) := by decide
theorem hf_at_13e : fetchRel sha384FnCode 0x13E = some (.aluImm .sll (31 : Fin 32) (31 : Fin 32) 0x18, 2) := by decide
theorem hf_at_140 : fetchRel sha384FnCode 0x140 = some (.aluImm .sll a0 a0 0x8, 2) := by decide
theorem hf_at_142 : fetchRel sha384FnCode 0x142 = some (.alu .or a2 (31 : Fin 32) a2, 4) := by decide
theorem hf_at_146 : fetchRel sha384FnCode 0x146 = some (.alu .or (22 : Fin 32) a2 a0, 4) := by decide
theorem hf_at_14a : fetchRel sha384FnCode 0x14A = some (.aluImm .sll (23 : Fin 32) (23 : Fin 32) 0x2, 2) := by decide
theorem hf_at_14c : fetchRel sha384FnCode 0x14C = some (.alu .and a0 (23 : Fin 32) a1, 4) := by decide
theorem hf_at_150 : fetchRel sha384FnCode 0x150 = some (.aluImm .srl a2 (7 : Fin 32) 0x18, 4) := by decide
theorem hf_at_154 : fetchRel sha384FnCode 0x154 = some (.alu .or a0 a0 a2, 2) := by decide
theorem hf_at_156 : fetchRel sha384FnCode 0x156 = some (.alu .and a2 (29 : Fin 32) a1, 4) := by decide
theorem hf_at_15a : fetchRel sha384FnCode 0x15A = some (.aluImm .sll a2 a2 0x8, 2) := by decide
theorem hf_at_15c : fetchRel sha384FnCode 0x15C = some (.aluImm .sll (6 : Fin 32) (6 : Fin 32) 0x18, 2) := by decide
theorem hf_at_15e : fetchRel sha384FnCode 0x15E = some (.alu .or a0 (6 : Fin 32) a0, 4) := by decide
theorem hf_at_162 : fetchRel sha384FnCode 0x162 = some (.aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x2, 2) := by decide
theorem hf_at_164 : fetchRel sha384FnCode 0x164 = some (.alu .and a3 (17 : Fin 32) a1, 4) := by decide
theorem hf_at_168 : fetchRel sha384FnCode 0x168 = some (.aluImm .srl a4 (5 : Fin 32) 0x18, 4) := by decide
theorem hf_at_16c : fetchRel sha384FnCode 0x16C = some (.alu .or (23 : Fin 32) a0 a2, 4) := by decide
theorem hf_at_170 : fetchRel sha384FnCode 0x170 = some (.alu .or a3 a3 a4, 2) := by decide
theorem hf_at_172 : fetchRel sha384FnCode 0x172 = some (.alu .and a0 (28 : Fin 32) a1, 4) := by decide
theorem hf_at_176 : fetchRel sha384FnCode 0x176 = some (.aluImm .sll a6 a6 0x18, 2) := by decide
theorem hf_at_178 : fetchRel sha384FnCode 0x178 = some (.aluImm .sll a0 a0 0x8, 2) := by decide
theorem hf_at_17a : fetchRel sha384FnCode 0x17A = some (.alu .or a1 a6 a3, 4) := by decide
theorem hf_at_17e : fetchRel sha384FnCode 0x17E = some (.alu .or (24 : Fin 32) a1 a0, 4) := by decide
theorem hf_at_182 : fetchRel sha384FnCode 0x182 = some (.aluImm .xor (19 : Fin 32) (25 : Fin 32) 0x7F, 4) := by decide
theorem hf_at_186 : fetchRel sha384FnCode 0x186 = some (.alu .add a0 (20 : Fin 32) (25 : Fin 32), 4) := by decide
theorem hf_at_18a : fetchRel sha384FnCode 0x18A = some (.aluImm .add a1 x0 0x80, 4) := by decide
theorem hf_at_18e : fetchRel sha384FnCode 0x18E = some (.store .sb a0 a1 0x0, 4) := by decide
theorem hf_at_192 : fetchRel sha384FnCode 0x192 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem hf_at_194 : fetchRel sha384FnCode 0x194 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem hf_at_196 : fetchRel sha384FnCode 0x196 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem hf_at_198 : fetchRel sha384FnCode 0x198 = some (.auipc ra 0x10000, 4) := by decide
theorem hf_at_19c : fetchRel sha384FnCode 0x19C = some (.jalr ra ra 0xFFFFF800, 4) := by decide
theorem hf_at_1a0 : fetchRel sha384FnCode 0x1A0 = some (.aluImm .add a0 x0 0xF, 2) := by decide
theorem hf_at_1a2 : fetchRel sha384FnCode 0x1A2 = some (.branch .bltu a0 (19 : Fin 32) 0x20, 4) := by decide
theorem hf_at_1a6 : fetchRel sha384FnCode 0x1A6 = some (.aluImm .add a1 sp 0xD0, 2) := by decide
theorem hf_at_1a8 : fetchRel sha384FnCode 0x1A8 = some (.alu .add a0 x0 (26 : Fin 32), 2) := by decide
theorem hf_at_1aa : fetchRel sha384FnCode 0x1AA = some (.auipc ra 0xC000, 4) := by decide
theorem hf_at_1ae : fetchRel sha384FnCode 0x1AE = some (.jalr ra ra 0xFFFFFA5C, 4) := by decide
theorem hf_at_1b2 : fetchRel sha384FnCode 0x1B2 = some (.aluImm .add a0 sp 0xD0, 2) := by decide
theorem hf_at_1b4 : fetchRel sha384FnCode 0x1B4 = some (.aluImm .add a2 x0 0x70, 4) := by decide
theorem hf_at_1b8 : fetchRel sha384FnCode 0x1B8 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem hf_at_1ba : fetchRel sha384FnCode 0x1BA = some (.auipc ra 0xF000, 4) := by decide
theorem hf_at_1be : fetchRel sha384FnCode 0x1BE = some (.jalr ra ra 0x7DE, 4) := by decide
theorem hf_at_1c2 : fetchRel sha384FnCode 0x1C2 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem hf_at_1c4 : fetchRel sha384FnCode 0x1C4 = some (.store .sw a0 (24 : Fin 32) 0x40, 4) := by decide
theorem hf_at_1c8 : fetchRel sha384FnCode 0x1C8 = some (.store .sw a0 (23 : Fin 32) 0x44, 4) := by decide
theorem hf_at_1cc : fetchRel sha384FnCode 0x1CC = some (.store .sw a0 (22 : Fin 32) 0x48, 4) := by decide
theorem hf_at_1d0 : fetchRel sha384FnCode 0x1D0 = some (.store .sw a0 (21 : Fin 32) 0x4C, 4) := by decide
theorem hf_at_1d4 : fetchRel sha384FnCode 0x1D4 = some (.aluImm .add a1 sp 0xD0, 2) := by decide
theorem hf_at_1d6 : fetchRel sha384FnCode 0x1D6 = some (.alu .add a0 x0 (26 : Fin 32), 2) := by decide
theorem hf_at_1d8 : fetchRel sha384FnCode 0x1D8 = some (.auipc ra 0xC000, 4) := by decide
theorem hf_at_1dc : fetchRel sha384FnCode 0x1DC = some (.jalr ra ra 0xFFFFFA2E, 4) := by decide
theorem hf_at_1e0 : fetchRel sha384FnCode 0x1E0 = some (.aluImm .add a6 x0 0x8, 2) := by decide
theorem hf_at_1e2 : fetchRel sha384FnCode 0x1E2 = some (.branch .beq a6 x0 0x4C, 4) := by decide
theorem hf_at_1e6 : fetchRel sha384FnCode 0x1E6 = some (.alu .add a0 x0 (26 : Fin 32), 2) := by decide
theorem hf_at_1e8 : fetchRel sha384FnCode 0x1E8 = some (.load .lw a1 a0 0x4, 2) := by decide
theorem hf_at_1ea : fetchRel sha384FnCode 0x1EA = some (.load .lw a2 a0 0x0, 2) := by decide
theorem hf_at_1ec : fetchRel sha384FnCode 0x1EC = some (.aluImm .srl (17 : Fin 32) a1 0x18, 4) := by decide
theorem hf_at_1f0 : fetchRel sha384FnCode 0x1F0 = some (.aluImm .srl a4 a2 0x18, 4) := by decide
theorem hf_at_1f4 : fetchRel sha384FnCode 0x1F4 = some (.aluImm .srl a5 a2 0x8, 4) := by decide
theorem hf_at_1f8 : fetchRel sha384FnCode 0x1F8 = some (.aluImm .srl (9 : Fin 32) a2 0x10, 4) := by decide
theorem hf_at_1fc : fetchRel sha384FnCode 0x1FC = some (.aluImm .srl a0 a1 0x8, 4) := by decide
theorem hf_at_200 : fetchRel sha384FnCode 0x200 = some (.aluImm .srl a3 a1 0x10, 4) := by decide
theorem hf_at_204 : fetchRel sha384FnCode 0x204 = some (.store .sb (8 : Fin 32) a4 0x4, 4) := by decide
theorem hf_at_208 : fetchRel sha384FnCode 0x208 = some (.store .sb (8 : Fin 32) (9 : Fin 32) 0x5, 4) := by decide
theorem hf_at_20c : fetchRel sha384FnCode 0x20C = some (.store .sb (8 : Fin 32) a5 0x6, 4) := by decide
theorem hf_at_210 : fetchRel sha384FnCode 0x210 = some (.store .sb (8 : Fin 32) a2 0x7, 4) := by decide
theorem hf_at_214 : fetchRel sha384FnCode 0x214 = some (.store .sb (8 : Fin 32) (17 : Fin 32) 0x0, 4) := by decide
theorem hf_at_218 : fetchRel sha384FnCode 0x218 = some (.store .sb (8 : Fin 32) a3 0x1, 4) := by decide
theorem hf_at_21c : fetchRel sha384FnCode 0x21C = some (.store .sb (8 : Fin 32) a0 0x2, 4) := by decide
theorem hf_at_220 : fetchRel sha384FnCode 0x220 = some (.store .sb (8 : Fin 32) a1 0x3, 4) := by decide
theorem hf_at_224 : fetchRel sha384FnCode 0x224 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x8, 2) := by decide
theorem hf_at_226 : fetchRel sha384FnCode 0x226 = some (.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x8, 2) := by decide
theorem hf_at_228 : fetchRel sha384FnCode 0x228 = some (.aluImm .add a6 a6 0xFFFFFFFF, 2) := by decide
theorem hf_at_22a : fetchRel sha384FnCode 0x22A = some (.branch .bne a6 x0 0xFFFFFFBC, 4) := by decide
theorem hf_at_22e : fetchRel sha384FnCode 0x22E = some (.aluImm .add a0 sp 0x1A0, 2) := by decide
theorem hf_at_230 : fetchRel sha384FnCode 0x230 = some (.aluImm .add a1 sp 0x1D0, 2) := by decide
theorem hf_at_232 : fetchRel sha384FnCode 0x232 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem hf_at_236 : fetchRel sha384FnCode 0x236 = some (.auipc ra 0xF000, 4) := by decide
theorem hf_at_23a : fetchRel sha384FnCode 0x23A = some (.jalr ra ra 0x7CA, 4) := by decide
theorem hf_at_23e : fetchRel sha384FnCode 0x23E = some (.aluImm .add a1 sp 0x1A0, 2) := by decide
theorem hf_at_240 : fetchRel sha384FnCode 0x240 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem hf_at_244 : fetchRel sha384FnCode 0x244 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem hf_at_246 : fetchRel sha384FnCode 0x246 = some (.auipc ra 0xF000, 4) := by decide
theorem hf_at_24a : fetchRel sha384FnCode 0x24A = some (.jalr ra ra 0x7BA, 4) := by decide
theorem hf_at_24e : fetchRel sha384FnCode 0x24E = some (.aluImm .add a0 sp 0x200, 2) := by decide
theorem hf_at_250 : fetchRel sha384FnCode 0x250 = some (.load .lw ra a0 0x3C, 4) := by decide
theorem hf_at_254 : fetchRel sha384FnCode 0x254 = some (.load .lw (8 : Fin 32) a0 0x38, 2) := by decide
theorem hf_at_256 : fetchRel sha384FnCode 0x256 = some (.load .lw (9 : Fin 32) a0 0x34, 2) := by decide
theorem hf_at_258 : fetchRel sha384FnCode 0x258 = some (.load .lw (18 : Fin 32) a0 0x30, 4) := by decide
theorem hf_at_25c : fetchRel sha384FnCode 0x25C = some (.load .lw (19 : Fin 32) a0 0x2C, 4) := by decide
theorem hf_at_260 : fetchRel sha384FnCode 0x260 = some (.load .lw (20 : Fin 32) a0 0x28, 4) := by decide
theorem hf_at_264 : fetchRel sha384FnCode 0x264 = some (.load .lw (21 : Fin 32) a0 0x24, 4) := by decide
theorem hf_at_268 : fetchRel sha384FnCode 0x268 = some (.load .lw (22 : Fin 32) a0 0x20, 4) := by decide
theorem hf_at_26c : fetchRel sha384FnCode 0x26C = some (.load .lw (23 : Fin 32) a0 0x1C, 4) := by decide
theorem hf_at_270 : fetchRel sha384FnCode 0x270 = some (.load .lw (24 : Fin 32) a0 0x18, 4) := by decide
theorem hf_at_274 : fetchRel sha384FnCode 0x274 = some (.load .lw (25 : Fin 32) a0 0x14, 4) := by decide
theorem hf_at_278 : fetchRel sha384FnCode 0x278 = some (.load .lw (26 : Fin 32) a0 0x10, 4) := by decide
theorem hf_at_27c : fetchRel sha384FnCode 0x27C = some (.aluImm .add sp sp 0x240, 4) := by decide
theorem hf_at_280 : fetchRel sha384FnCode 0x280 = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev HF : Word := BitVec.ofNat 32 sha384FnAddress

/-- The base of the stack `sha384` and its callees write. -/
abbrev hfG (F : Word) : Word := F + 0xFFFFFBE0

/-- The code `sha384` runs, its callees', and the constants they read. -/
structure HfEnv (M : Word → BitVec 8) : Prop where
  cod : CodeIn M HF sha384FnCode
  blk : CodeIn M (BitVec.ofNat 32 sha384UpdateBlocksAddress) sha384UpdateBlocksCode
  cmp : CodeIn M (BitVec.ofNat 32 sha512CompressAddress) sha512CompressCode
  rfi : CodeIn M (BitVec.ofNat 32 rangeFromIndexAddress) rangeFromIndexCode
  fb : CodeIn M (BitVec.ofNat 32 sha512FinBlockAddress) sha512FinBlockCode
  za48 : CodeIn M (BitVec.ofNat 32 zeroArray48Address) zeroArray48Code
  za64 : CodeIn M (BitVec.ofNat 32 zeroArray64Address) zeroArray64Code
  mcs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  mcb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  mset : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  k : CodeIn M (BitVec.ofNat 32 sha512KAddress) sha512KData
  iv : CodeIn M (BitVec.ofNat 32 sha384IVAddress) sha384IVData

/-- Where `sha384` runs: its frame at `F`, 16-aligned, with the 0x420
bytes below it, all below 0x40000000 and apart from the read-only data at
`roWindowAddress`, the `len` input bytes at `p`, and the 48-byte output at
`out`. -/
structure HfCtx (M0 : Word → BitVec 8) (F out p : Word) (len : Nat) : Prop where
  env : HfEnv M0
  hF : F.toNat % 16 = 0
  hlo : 0x420 ≤ F.toNat
  hhi : F.toNat + 0x240 ≤ 0x40000000
  sRo : Sep (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize) (hfG F) 0x660
  sP : Sep p len (hfG F) 0x660
  sOut : Sep out 48 (hfG F) 0x660
  hp : p.toNat + len ≤ 0x40000000
  hout : out.toNat + 48 ≤ 0x40000000

/-- Between calls: `sp` at `F`, `gp` and `tp` as in `r0`, memory outside
the stack as `M0`, and the saved registers' slots as `Ms`. -/
structure HfSt (M0 Ms : Word → BitVec 8) (F : Word) (r0 : Fin 32 → Word) (M : Word → BitVec 8) (n : Machine)
    (off : Nat) : Prop where
  st : St M HF n off (reg n)
  hsp : reg n sp = F
  gp : reg n 3 = r0 3
  tp : reg n 4 = r0 4
  agree : ∀ x, Sep (hfG F) 0x660 x 1 → M x = M0 x
  slots : ∀ c, 0x210 ≤ c → c < 0x240 → M (F + BitVec.ofNat 32 c) = Ms (F + BitVec.ofNat 32 c)

theorem hf_len : sha384FnCode.length = 642 := by decide +kernel

section Ctx
variable {M0 : Word → BitVec 8} {F out p : Word} {len : Nat}

theorem hfF_G (F : Word) (c : Nat) : F + BitVec.ofNat 32 c = hfG F + BitVec.ofNat 32 (0x420 + c) := by
  rw [hfG, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFBE0 : Word).toNat = 2 ^ 32 - 0x420 from rfl]
  omega

theorem hfZ_G (F z : Word) {S : Nat} (hz : z.toNat = 2 ^ 32 - S) (hS : S ≤ 0x420) :
    F + z = hfG F + BitVec.ofNat 32 (0x420 - S) := by
  rw [hfG, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, hz, show (0xFFFFFBE0 : Word).toNat = 2 ^ 32 - 0x420 from rfl]
  omega

theorem HfCtx.gN (C : HfCtx M0 F out p len) : (hfG F).toNat = F.toNat - 0x420 := by
  have := C.hlo
  rw [hfG, BitVec.toNat_add, show (0xFFFFFBE0 : Word).toNat = 2 ^ 32 - 0x420 from rfl]; omega

theorem HfCtx.fN (C : HfCtx M0 F out p len) {c : Nat} (h : c ≤ 0x240) :
    (F + BitVec.ofNat 32 c).toNat = F.toNat + c := by
  have := C.hhi; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem HfCtx.al (C : HfCtx M0 F out p len) {c : Nat} (h : c % 4 = 0) : (F + BitVec.ofNat 32 c).toNat % 4 = 0 :=
  aligned_add (by have := C.hF; omega) h

theorem HfCtx.offs (_ : HfCtx M0 F out p len) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 0x240)
    (hd : d + k ≤ 0x240) : Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 d) k :=
  sep_offsets F h (by omega) (by omega)

theorem HfCtx.inG (_ : HfCtx M0 F out p len) {c l : Nat} (h : c + l ≤ 0x240) {x : Word}
    (hx : Sep (hfG F) 0x660 x 1) : Sep (F + BitVec.ofNat 32 c) l x 1 := by
  rw [hfF_G]; exact (hx.symm.subR (by omega)).symm

/-- The callees' stack is apart from the frame. -/
theorem HfCtx.zF (_ : HfCtx M0 F out p len) {c l : Nat} (h : c + l ≤ 0x240) :
    Sep (hfG F) 0x420 (F + BitVec.ofNat 32 c) l := by
  rw [hfF_G]
  have := sep_offsets (hfG F) (c := 0) (n := 0x420) (d := 0x420 + c) (k := l) (Or.inl (by omega)) (by omega) (by omega)
  rwa [add_ofNat_zero] at this

theorem HfCtx.zG (_ : HfCtx M0 F out p len) {x : Word} (hx : Sep (hfG F) 0x660 x 1) : Sep (hfG F) 0x420 x 1 := by
  have := hx.sub (c := 0) (l := 0x420) (by omega); rwa [add_ofNat_zero] at this

theorem HfCtx.hiG (C : HfCtx M0 F out p len) {b : Word} {k : Nat} (h1 : 0x40000000 ≤ b.toNat)
    (h2 : b.toNat + k ≤ 2 ^ 32) : Sep (hfG F) 0x660 b k :=
  sep_of_le (by rw [C.gN]; have := C.hhi; omega) h2

/-- A read-only datum is apart from the stack. -/
theorem HfCtx.ro (C : HfCtx M0 F out p len) {a k : Nat} (h1 : (img% roWindowAddress) ≤ a) (h2 : a + k ≤ 0x3FCC5400) :
    Sep (BitVec.ofNat 32 a) k (hfG F) 0x660 := by
  have := C.sRo.sub (c := a - (img% roWindowAddress)) (l := k) (by omega)
  rwa [BitVec.ofNat_add_ofNat, show (img% roWindowAddress) + (a - (img% roWindowAddress)) = a by omega] at this

/-- A range apart from the stack is apart from a callee's frame of `S`
bytes below `F`. -/
theorem HfCtx.zone (_ : HfCtx M0 F out p len) {x z : Word} {k S : Nat} (hz : z.toNat = 2 ^ 32 - S)
    (hS : S ≤ 0x420) (h : Sep x k (hfG F) 0x660) : Sep x k (F + z) S := by
  have e := hfZ_G F z hz hS
  rw [e]; exact h.subR (by omega)

/-- The frame is apart from a callee's frame below `F`. -/
theorem HfCtx.zoneF (_ : HfCtx M0 F out p len) {z : Word} {c l S : Nat} (hz : z.toNat = 2 ^ 32 - S)
    (hS : S ≤ 0x420) (h : c + l ≤ 0x240) : Sep (F + BitVec.ofNat 32 c) l (F + z) S := by
  have e := hfZ_G F z hz hS
  rw [e, hfF_G]; exact sep_offsets (hfG F) (Or.inr (by omega)) (by omega) (by omega)

/-- Memory a callee with a frame of `S` bytes below `F` may write lies in
the callees' stack. -/
theorem HfCtx.zoneIn (_ : HfCtx M0 F out p len) {x z : Word} {S : Nat} (hz : z.toNat = 2 ^ 32 - S)
    (hS : S ≤ 0x420) (h : Sep (hfG F) 0x420 x 1) : Sep (F + z) S x 1 := by
  rw [hfZ_G F z hz hS]; exact h.sub (by omega)

theorem HfCtx.zS (_ : HfCtx M0 F out p len) {q : Word} {k : Nat} (h : Sep q k (hfG F) 0x660) :
    Sep q k (hfG F) 0x420 := by
  have := h.subR (c := 0) (l := 0x420) (by omega); rwa [add_ofNat_zero] at this

theorem HfCtx.fS (_ : HfCtx M0 F out p len) {q : Word} {k c l : Nat} (h : Sep q k (hfG F) 0x660)
    (hc : c + l ≤ 0x240) : Sep (F + BitVec.ofNat 32 c) l q k := by
  rw [hfF_G]; exact (h.subR (by omega)).symm

theorem HfCtx.codeF (C : HfCtx M0 F out p len) {c l : Nat} (h : c + l ≤ 0x240) {b : Word} {k : Nat}
    (h1 : 0x40000000 ≤ b.toNat) (h2 : b.toNat + k ≤ 2 ^ 32) : Sep (F + BitVec.ofNat 32 c) l b k :=
  sep_of_le (by rw [C.fN (by omega)]; have := C.hhi; omega) h2

theorem HfCtx.f16 (C : HfCtx M0 F out p len) {z : Word} {S : Nat} (hz : z.toNat = 2 ^ 32 - S) (hS : S ≤ 0x420) :
    (F + z).toNat = F.toNat - S := by
  have := C.hlo; rw [BitVec.toNat_add, hz]; omega

end Ctx

section St
variable {M0 Ms : Word → BitVec 8} {F out p : Word} {len : Nat} {r0 : Fin 32 → Word} {M : Word → BitVec 8}
  {n : Machine} {off : Nat}

theorem HfSt.hiM (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) :
    ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x :=
  fun x hx => D.agree x (C.hiG hx (by have := x.isLt; omega))

theorem HfSt.roM (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {a k : Nat}
    (h1 : (img% roWindowAddress) ≤ a) (h2 : a + k ≤ 0x3FCC5400) :
    ∀ i, i < k → M (BitVec.ofNat 32 a + BitVec.ofNat 32 i) = M0 (BitVec.ofNat 32 a + BitVec.ofNat 32 i) :=
  fun i hi => D.agree _ ((C.ro h1 h2).sub (c := i) (l := 1) (by omega)).symm

theorem HfSt.bytesOut (D : HfSt M0 Ms F r0 M n off) {q : Word} {k : Nat} (h : Sep q k (hfG F) 0x660) :
    memBytes M q k = memBytes M0 q k :=
  memBytes_congr fun i hi => D.agree _ (h.sub (c := i) (l := 1) hi).symm

theorem HfSt.code (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) : CodeIn M HF sha384FnCode :=
  C.env.cod.hi (D.hiM C) (by decide) (by rw [hf_len]; decide)

theorem HfSt.codeRo (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {a : Nat} {code : List Nat}
    (h : CodeIn M0 (BitVec.ofNat 32 a) code) (h1 : (img% roWindowAddress) ≤ a) (h2 : a + code.length ≤ 0x3FCC5400) :
    CodeIn M (BitVec.ofNat 32 a) code :=
  fun i hi => by rw [D.roM C h1 h2 i hi]; exact h i hi

theorem HfSt.jmp (D : HfSt M0 Ms F r0 M n off) {n1 : Machine} {off' : Nat} (u : St M HF n1 off' (reg n)) :
    HfSt M0 Ms F r0 M n1 off' :=
  ⟨u.self, by rw [u.regs, D.hsp], by rw [u.regs, D.gp], by rw [u.regs, D.tp], D.agree, D.slots⟩

theorem HfSt.regs (D : HfSt M0 Ms F r0 M n off) {n1 : Machine} {off' : Nat} (u : St M HF n1 off' (reg n1))
    (h : ∀ q, q = sp ∨ q = (3 : Fin 32) ∨ q = (4 : Fin 32) → reg n1 q = reg n q) : HfSt M0 Ms F r0 M n1 off' :=
  ⟨u, by rw [h sp (Or.inl rfl), D.hsp], by rw [h 3 (Or.inr (Or.inl rfl)), D.gp],
    by rw [h 4 (Or.inr (Or.inr rfl)), D.tp], D.agree, D.slots⟩

/-- After a call that returned to `off'` with `sp`, `gp`, and `tp` kept,
having written only the callees' stack below `F` and the `k` bytes at
`F + d`, below the slots. -/
theorem HfSt.ret (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {n' : Machine} {d k off' : Nat}
    (hpc : n'.pc = HF + BitVec.ofNat 32 off') (hsp : reg n' sp = F) (h3 : reg n' 3 = reg n 3)
    (h4 : reg n' 4 = reg n 4) (hd : d + k ≤ 0x210)
    (hfr : ∀ x, Sep (hfG F) 0x420 x 1 → Sep (F + BitVec.ofNat 32 d) k x 1 → n'.mem x = M x) :
    HfSt M0 Ms F r0 n'.mem n' off' :=
  ⟨⟨hpc, rfl, fun _ => rfl⟩, hsp, by rw [h3, D.gp], by rw [h4, D.tp],
    fun x hx => by rw [hfr x (C.zG hx) (C.inG (by omega) hx), D.agree x hx],
    fun c h1 h2 => by
      rw [hfr _ (C.zF (by omega)) (C.offs (Or.inl (by omega)) (by omega) (by omega)), D.slots c h1 h2]⟩

/-- After a store of `k` bytes at `F + d`, below the slots. -/
theorem HfSt.store (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {M' : Word → BitVec 8} {n1 : Machine}
    {d k off' : Nat} (u : St M' HF n1 off' (reg n1)) (hsp : reg n1 sp = F) (h3 : reg n1 3 = reg n 3)
    (h4 : reg n1 4 = reg n 4) (hd : d + k ≤ 0x210)
    (hfr : ∀ x, Sep (F + BitVec.ofNat 32 d) k x 1 → M' x = M x) : HfSt M0 Ms F r0 M' n1 off' :=
  ⟨u, hsp, by rw [h3, D.gp], by rw [h4, D.tp],
    fun x hx => by rw [hfr x (C.inG (by omega) hx), D.agree x hx],
    fun c h1 h2 => by rw [hfr _ (C.offs (Or.inl (by omega)) (by omega) (by omega)), D.slots c h1 h2]⟩

/-- A block of register operations that leaves `sp`, `gp`, `tp`, and
memory alone. -/
theorem HfSt.block (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) (blk : List BInstr) {off' : Nat}
    (he : blockEnd sha384FnCode off blk = some off')
    (hok : BlockOk HF sha384FnCode.length blk (M, reg n)) (hm : (runBlock blk (M, reg n)).1 = M)
    (hk : ∀ q : Fin 32, q = sp ∨ q = (3 : Fin 32) ∨ q = (4 : Fin 32) → (runBlock blk (M, reg n)).2 q = reg n q) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 M n' off' ∧ ∀ q, reg n' q = (runBlock blk (M, reg n)).2 q := by
  obtain ⟨n', c, u⟩ := St.block blk D.st (D.code C) he hok
  rw [hm] at u
  exact ⟨n', c, D.regs ⟨u.pc, u.mem, fun _ => rfl⟩ (fun q hq => by rw [u.regs]; exact hk q hq), u.regs⟩

/-- A word store into the frame below the slots. -/
theorem HfSt.sw (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {rs1 rs2 : Fin 32} {imm len' : Word}
    {off' c : Nat} (hf : fetchRel sha384FnCode off = some (.store .sw rs1 rs2 imm, len'))
    (hn : BitVec.ofNat 32 off + len' = BitVec.ofNat 32 off') (ha : reg n rs1 + imm = F + BitVec.ofNat 32 c)
    (hc4 : c % 4 = 0) (hc : c + 4 ≤ 0x210) :
    ∃ n1, step n = some n1 ∧ HfSt M0 Ms F r0 (memStore32 M (F + BitVec.ofNat 32 c) (reg n rs2)) n1 off' ∧
      ∀ q, reg n1 q = reg n q := by
  obtain ⟨n1, d1, u1⟩ := D.st.sw (D.code C) hf hn (by rw [ha]; exact C.al hc4)
  rw [ha] at u1
  exact ⟨n1, d1, D.store C (d := c) (k := 4) u1.self (by rw [u1.regs, D.hsp]) (by rw [u1.regs]) (by rw [u1.regs]) hc
    (fun x hx => st32_frame hx), u1.regs⟩

/-- A byte store into the frame below the slots. -/
theorem HfSt.sb (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {rs1 rs2 : Fin 32} {imm len' : Word}
    {off' c : Nat} (hf : fetchRel sha384FnCode off = some (.store .sb rs1 rs2 imm, len'))
    (hn : BitVec.ofNat 32 off + len' = BitVec.ofNat 32 off') (ha : reg n rs1 + imm = F + BitVec.ofNat 32 c)
    (hc : c + 1 ≤ 0x210) :
    ∃ n1, step n = some n1 ∧
      HfSt M0 Ms F r0 (memStore8 M (F + BitVec.ofNat 32 c) ((reg n rs2).extractLsb' 0 8)) n1 off' ∧
      ∀ q, reg n1 q = reg n q := by
  obtain ⟨n1, d1, u1⟩ := D.st.sb (D.code C) hf hn
  rw [ha] at u1
  exact ⟨n1, d1, D.store C (d := c) (k := 1) u1.self (by rw [u1.regs, D.hsp]) (by rw [u1.regs]) (by rw [u1.regs]) hc
    (fun x hx => st8_frame hx), u1.regs⟩

end St

/-! ## Calls -/

section
variable {M0 Ms : Word → BitVec 8} {F out p : Word} {len : Nat} {r0 : Fin 32 → Word}
  {M : Word → BitVec 8} {n : Machine} {off : Nat}

/-- A call's return address. -/
theorem hf_ra {off : Nat} {f : Fin 32 → Word} :
    upd f ra (HF + BitVec.ofNat 32 (off + 8)) ra = HF + BitVec.ofNat 32 (off + 8) := by simp +decide [upd]

theorem hfKeep {q : Fin 32} (hq : q.val ∈ evKeep) :
    q ≠ ra ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧
      q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ (31 : Fin 32) ∧
      q ≠ sp := by
  revert hq; revert q; decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `memcpy(F + d, s, N)`. -/
theorem HfSt.memcpy (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {imm o s : Word} {d N : Nat}
    (h1 : fetchRel sha384FnCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sha384FnCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : HF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memcpyStubAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = s) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hd : d + N ≤ 0x210) (sS : Sep s N (hfG F) 0x420) (hsep : Sep (F + BitVec.ofNat 32 d) N s N)
    (hsw : s.toNat + N < 2 ^ 32) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ∀ x, Sep (hfG F) 0x420 x 1 → n'.mem x = copyBytes M (F + BitVec.ofNat 32 d) s N x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have sp1 : reg n1 sp = F := by rw [r1 _ (by decide), D.hsp]
  have hz : (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 := rfl
  have hi := D.hiM C
  have E : McEnv n1.mem (BitVec.ofNat 32 memcpyStubAddress + 8) (F + BitVec.ofNat 32 d) s (reg n1 sp + 0xFFFFFFF0) N := by
    rw [mem1, sp1]
    exact { code := C.env.mcb.hi hi (by decide) (by decide)
            hDC := C.codeF (by omega) (by decide) (by decide)
            hFC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            hdF := C.zoneF hz (by decide) (by omega)
            hsF := by rw [hfZ_G F _ hz (by decide)]; exact sS.subR (by decide)
            hsep := hsep
            hF := by rw [C.f16 hz (by decide)]; have := C.hF; have := C.hlo; omega
            hFw := by rw [C.f16 hz (by decide)]; have := C.hhi; omega
            hdw := by rw [C.fN (by omega)]; have := C.hhi; omega
            hsw := hsw }
  obtain ⟨n2, c2, pc2, sp2, _, f2, k2⟩ := memcpy_correct n1 (BitVec.ofNat 32 memcpyStubAddress)
    (HF + BitVec.ofNat 32 (off + 8)) (F + BitVec.ofNat 32 d) s N
    (fun i hi' => by rw [mem1]; exact C.env.mcs.hi hi (by decide) (by decide) i hi') (by decide)
    pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [r1 _ (by decide), ha2])
    (by rw [regs1]; exact hf_ra) (even_clear _ (even_at HF (by decide) (off + 8) hoff)) E
  rw [mem1, sp1] at f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    obtain ⟨e1, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hfKeep hq
    rw [k2 q e7 e8 e9 e10 e11 e12 e13 e3 e4 e5 e14 e15 e16 e18, r1 q e1]
  have fz : ∀ x, Sep (hfG F) 0x420 x 1 → n2.mem x = copyBytes M (F + BitVec.ofNat 32 d) s N x :=
    fun x hx => f2 x (C.zoneIn hz (by decide) hx)
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := N) pc2 (by rw [sp2, sp1]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd
    (fun x hx hs => by rw [fz x hx, copyBytes_sep hs (Nat.le_refl _)]), k2', fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `memset(F + d, b, N)`. -/
theorem HfSt.memset (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {imm o b : Word} {d N : Nat}
    (h1 : fetchRel sha384FnCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sha384FnCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : HF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memsetAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = b) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hd : d + N ≤ 0x210) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 (fillBytes M (F + BitVec.ofNat 32 d) (b.extractLsb' 0 8) N) n' (off + 8) ∧
      ∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 memsetAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  obtain ⟨n2, c2, pc2, mem2, _, k2⟩ := memset_correct n1 (BitVec.ofNat 32 memsetAddress)
    (HF + BitVec.ofNat 32 (off + 8)) (F + BitVec.ofNat 32 d) b N
    (fun i hi => by rw [mem1]; exact C.env.mset.hi (D.hiM C) (by decide) (by decide) i hi) (by decide)
    pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [r1 _ (by decide), ha2])
    (by rw [regs1]; exact hf_ra) (even_clear _ (even_at HF (by decide) (off + 8) hoff))
    (by rw [C.fN (by omega)]; have := C.hhi; omega) (C.codeF (by omega) (by decide) (by decide))
  rw [mem1] at mem2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    obtain ⟨e1, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hfKeep hq
    rw [k2 q e8 e9 e10 e11 e12, r1 q e1]
  have D2 := D.ret C (d := d) (k := N) (n' := n2) pc2
    (by rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide), r1 _ (by decide), D.hsp])
    (k2' 3 (by decide)) (k2' 4 (by decide)) hd (fun x _ hs => by rw [mem2, fillBytes_sep hs (Nat.le_refl _)])
  rw [mem2] at D2
  exact ⟨n2, c1.trans c2, D2, k2'⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of the closure that compresses the 128 bytes at `F + b` into
the hash value at `F + a`. -/
theorem HfSt.finBlock (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {imm o : Word} {a b : Nat}
    (h1 : fetchRel sha384FnCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sha384FnCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : HF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha512FinBlockAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 a) (ha1 : reg n a1 = F + BitVec.ofNat 32 b)
    (ha : a + 64 ≤ 0x210) (ha4 : a % 4 = 0) (hbb : b + 128 ≤ 0x240) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (s5Hv n'.mem (F + BitVec.ofNat 32 a)).toList =
        Sha512.compress (s5Hv M (F + BitVec.ofNat 32 a)).toList (memBytes M (F + BitVec.ofNat 32 b) 128) ∧
      ∀ x, Sep (hfG F) 0x420 x 1 → Sep (F + BitVec.ofNat 32 a) 64 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 sha512FinBlockAddress) hc h1 h2 hb
    (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFBE0 : Word).toNat = 2 ^ 32 - 0x420 := rfl
  have hi := D.hiM C
  have E : FB5Env n1.mem (F + BitVec.ofNat 32 a) (F + BitVec.ofNat 32 b) F := by
    rw [mem1]
    exact { cF := C.env.fb.hi hi (by decide) (by decide)
            cC := C.env.cmp.hi hi (by decide) (by decide)
            cI := C.env.rfi.hi hi (by decide) (by decide)
            cMS := C.env.mcs.hi hi (by decide) (by decide)
            cMB := C.env.mcb.hi hi (by decide) (by decide)
            cZ := C.env.mset.hi hi (by decide) (by decide)
            cK := D.codeRo C C.env.k (by decide) (by decide)
            hsp := C.hF
            hspl := by have := C.hlo; omega
            hspw := by have := C.hhi; omega
            hst := C.al ha4
            hstw := by rw [C.fN (by omega)]; have := C.hhi; omega
            hblkw := by rw [C.fN (by omega)]; have := C.hhi; omega
            sStF := C.zoneF hz (by decide) (by omega)
            sBF := C.zoneF hz (by decide) hbb
            sKF := C.zone hz (by decide) (C.ro (by decide) (by decide))
            sStK := C.fS (C.ro (by decide) (by decide)) (by omega) }
  obtain ⟨n2, c2, pc2, sp2, k2, h2', fr2⟩ := sha512FinBlock_correct n1 E pc1 (by rw [r1 _ (by decide), ha0])
    (by rw [r1 _ (by decide), ha1]) (by rw [regs1]; exact hf_ra) (even_clear _ (even_at HF (by decide) (off + 8) hoff))
    (by rw [r1 _ (by decide), D.hsp])
  rw [mem1] at h2' fr2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (hfG F) 0x420 x 1 → Sep (F + BitVec.ofNat 32 a) 64 x 1 → n2.mem x = M x :=
    fun x hx ho => fr2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := a) (k := 64) pc2 sp2 (k2' 3 (by decide)) (k2' 4 (by decide)) ha fz,
    k2', h2', fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `hybrid_array`'s `from_fn` that zeroes the 64 bytes at
`F + d`. -/
theorem HfSt.zero64 (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {imm o : Word} {d : Nat}
    (h1 : fetchRel sha384FnCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sha384FnCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : HF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 zeroArray64Address) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (hd : d + 64 ≤ 0x210) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ∀ x, Sep (hfG F) 0x420 x 1 → n'.mem x = fillBytes M (F + BitVec.ofNat 32 d) 0 64 x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 zeroArray64Address) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFFA0 : Word).toNat = 2 ^ 32 - 0x60 := rfl
  have hi := D.hiM C
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := zeroArray64_correct n1
    (by rw [mem1]; exact C.env.za64.hi hi (by decide) (by decide)) (by rw [mem1]; exact C.env.mcs.hi hi (by decide) (by decide))
    (by rw [mem1]; exact C.env.mcb.hi hi (by decide) (by decide)) pc1 (by rw [r1 _ (by decide), ha0]) (by rw [regs1]; exact hf_ra)
    (even_clear _ (even_at HF (by decide) (off + 8) hoff)) (by rw [r1 _ (by decide), D.hsp]) C.hF
    (by have := C.hlo; omega) (by have := C.hhi; omega) (by rw [C.fN (by omega)]; have := C.hhi; omega)
    (C.zoneF hz (by decide) (by omega))
  rw [mem1] at f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    obtain ⟨e1, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hfKeep hq
    rw [k2 q e7 e8 e9 e10 e11 e12 e13 e3 e4 e5 e14 e15 e16, r1 q e1]
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 64) (n' := n2) pc2 sp2 (k2' 3 (by decide)) (k2' 4 (by decide)) hd
    (fun x hx hs => by rw [f2 x (C.zoneIn hz (by decide) hx), fillBytes_sep hs (Nat.le_refl _)]), k2',
    fun x hx => f2 x (C.zoneIn hz (by decide) hx)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `hybrid_array`'s `from_fn` that zeroes the 48 bytes at
`F + d`. -/
theorem HfSt.zero48 (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {imm o : Word} {d : Nat}
    (h1 : fetchRel sha384FnCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sha384FnCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : HF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 zeroArray48Address) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (hd : d + 48 ≤ 0x210) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ∀ x, Sep (hfG F) 0x420 x 1 → n'.mem x = fillBytes M (F + BitVec.ofNat 32 d) 0 48 x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 zeroArray48Address) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFFB0 : Word).toNat = 2 ^ 32 - 0x50 := rfl
  have hi := D.hiM C
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := zeroArray48_correct n1
    (by rw [mem1]; exact C.env.za48.hi hi (by decide) (by decide)) (by rw [mem1]; exact C.env.mcs.hi hi (by decide) (by decide))
    (by rw [mem1]; exact C.env.mcb.hi hi (by decide) (by decide)) pc1 (by rw [r1 _ (by decide), ha0]) (by rw [regs1]; exact hf_ra)
    (even_clear _ (even_at HF (by decide) (off + 8) hoff)) (by rw [r1 _ (by decide), D.hsp]) C.hF
    (by have := C.hlo; omega) (by have := C.hhi; omega) (by rw [C.fN (by omega)]; have := C.hhi; omega)
    (C.zoneF hz (by decide) (by omega))
  rw [mem1] at f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    obtain ⟨e1, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hfKeep hq
    rw [k2 q e7 e8 e9 e10 e11 e12 e13 e3 e4 e5 e14 e15 e16, r1 q e1]
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 48) (n' := n2) pc2 sp2 (k2' 3 (by decide)) (k2' 4 (by decide)) hd
    (fun x hx hs => by rw [f2 x (C.zoneIn hz (by decide) hx), fillBytes_sep hs (Nat.le_refl _)]), k2',
    fun x hx => f2 x (C.zoneIn hz (by decide) hx)⟩

theorem hf40 (F : Word) (s : Nat) : F + BitVec.ofNat 32 s + 0x40 = F + BitVec.ofNat 32 (s + 0x40) := by
  rw [show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `sha384UpdateBlocks` on `nb` blocks at `bp`, outside the
stack, with the state at `F + s`. -/
theorem HfSt.blocks (C : HfCtx M0 F out p len) (D : HfSt M0 Ms F r0 M n off) {imm o bp : Word} {s nb : Nat}
    (h1 : fetchRel sha384FnCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sha384FnCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : HF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha384UpdateBlocksAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 s) (ha1 : reg n a1 = bp) (ha2 : reg n a2 = BitVec.ofNat 32 nb)
    (hs : s + 0x50 ≤ 0x210) (hs4 : s % 4 = 0)
    (hcnt : (memLoad32 M (F + BitVec.ofNat 32 s + 0x40)).toNat + nb < 2 ^ 32)
    (sB : Sep bp (128 * nb) (hfG F) 0x660) (hbw : bp.toNat + 128 * nb < 2 ^ 32) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (s5Hv n'.mem (F + BitVec.ofNat 32 s)).toList =
        (blockList128 M bp nb).foldl Sha512.compress (s5Hv M (F + BitVec.ofNat 32 s)).toList ∧
      memLoad32 n'.mem (F + BitVec.ofNat 32 s + 0x40) = memLoad32 M (F + BitVec.ofNat 32 s + 0x40) + BitVec.ofNat 32 nb ∧
      memLoad32 n'.mem (F + BitVec.ofNat 32 s + 0x44) = memLoad32 M (F + BitVec.ofNat 32 s + 0x44) ∧
      memLoad32 n'.mem (F + BitVec.ofNat 32 s + 0x48) = memLoad32 M (F + BitVec.ofNat 32 s + 0x48) ∧
      memLoad32 n'.mem (F + BitVec.ofNat 32 s + 0x4C) = memLoad32 M (F + BitVec.ofNat 32 s + 0x4C) ∧
      ∀ x, Sep (hfG F) 0x420 x 1 → Sep (F + BitVec.ofNat 32 s) 0x50 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 sha384UpdateBlocksAddress) hc h1 h2 hb
    (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFC70 : Word).toNat = 2 ^ 32 - 0x390 := rfl
  have hi := D.hiM C
  have sH : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep (F + 0xFFFFFC70) 0x390 b k :=
    fun h1 h2 => (C.zone hz (by decide) (C.hiG h1 h2).symm).symm
  have env : S5Env M (BitVec.ofNat 32 sha512CompressAddress) F (F + BitVec.ofNat 32 s) bp nb :=
    { hP := by decide
      code := C.env.cmp.hi hi (by decide) (by decide)
      idx := by rw [show (BitVec.ofNat 32 sha512CompressAddress + 0xFFFFFFEA : Word) =
                  BitVec.ofNat 32 rangeFromIndexAddress by decide]; exact C.env.rfi.hi hi (by decide) (by decide)
      stub := by rw [show (BitVec.ofNat 32 sha512CompressAddress + 0x5AC : Word) =
                  BitVec.ofNat 32 memcpyStubAddress by decide]; exact C.env.mcs.hi hi (by decide) (by decide)
      body := by rw [show (BitVec.ofNat 32 sha512CompressAddress + 0x5B4 : Word) =
                  BitVec.ofNat 32 memcpyStubAddress + 8 by decide]; exact C.env.mcb.hi hi (by decide) (by decide)
      mset := by rw [show (BitVec.ofNat 32 sha512CompressAddress + 0x544 : Word) =
                  BitVec.ofNat 32 memsetAddress by decide]; exact C.env.mset.hi hi (by decide) (by decide)
      kdata := D.codeRo C C.env.k (by decide) (by decide)
      hsp := by have := C.hF; omega
      hS := by have := C.hlo; omega
      hstp := C.al hs4
      hwbp := hbw
      sC := sH (by decide) (by decide)
      sI := sH (by decide) (by decide)
      sU := sH (by decide) (by decide)
      sB := sH (by decide) (by decide)
      sZ := sH (by decide) (by decide)
      sK := (C.zone hz (by decide) (C.ro (by decide) (by decide))).symm
      stC := C.codeF (by omega) (by decide) (by decide)
      stI := C.codeF (by omega) (by decide) (by decide)
      stU := C.codeF (by omega) (by decide) (by decide)
      stB := C.codeF (by omega) (by decide) (by decide)
      stZ := C.codeF (by omega) (by decide) (by decide)
      stK := C.fS (C.ro (by decide) (by decide)) (by omega)
      stF := C.zoneF hz (by decide) (by omega)
      bF := C.zone hz (by decide) sB
      bSt := (C.fS sB (by omega)).symm }
  obtain ⟨n2, c2, pc2, sp2, k2, hv, cnt0, cnt1, cnt2, cnt3, f2⟩ := sha384UpdateBlocks_correct n1
    (by rw [mem1]; exact C.env.blk.hi hi (by decide) (by decide)) pc1 (by rw [mem1]; exact env)
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; exact hf_ra) (even_clear _ (even_at HF (by decide) (off + 8) hoff)) (by rw [r1 sp (by decide), D.hsp])
    (by rw [mem1]; exact hcnt)
    (by rw [hf40]; exact C.codeF (by omega) (by decide) (by decide))
    (by rw [hf40]; exact C.codeF (by omega) (by decide) (by decide))
    (by rw [hf40]; exact C.codeF (by omega) (by decide) (by decide))
    (by rw [hf40]; exact C.codeF (by omega) (by decide) (by decide))
    (by rw [hf40]; exact C.codeF (by omega) (by decide) (by decide))
    (by rw [hf40]; exact C.fS (C.ro (by decide) (by decide)) (by omega))
    (by rw [hf40]; exact C.zoneF hz (by decide) (by omega))
    (by rw [hf40]; exact (C.fS sB (by omega)).symm)
    (by rw [hf40]; exact C.codeF (by omega) (by decide) (by decide))
  rw [mem1] at hv cnt0 cnt1 cnt2 cnt3 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    obtain ⟨e1, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hfKeep hq
    rw [k2 q e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17, r1 q e1]
  have fz : ∀ x, Sep (hfG F) 0x420 x 1 → Sep (F + BitVec.ofNat 32 s) 0x50 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := s) (k := 0x50) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hs fz,
    k2', hv, cnt0, cnt1, cnt2, cnt3, fz⟩

end

/-! ## Prologue and epilogue -/

/-- The registers the prologue saves, at their offsets from `F + 0x200`. -/
abbrev hfPs : List (Fin 32 × Word) :=
  [(ra, BitVec.ofNat 32 0x3C), ((8 : Fin 32), BitVec.ofNat 32 0x38), ((9 : Fin 32), BitVec.ofNat 32 0x34),
    ((18 : Fin 32), BitVec.ofNat 32 0x30), ((19 : Fin 32), BitVec.ofNat 32 0x2C), ((20 : Fin 32), BitVec.ofNat 32 0x28),
    ((21 : Fin 32), BitVec.ofNat 32 0x24), ((22 : Fin 32), BitVec.ofNat 32 0x20), ((23 : Fin 32), BitVec.ofNat 32 0x1C),
    ((24 : Fin 32), BitVec.ofNat 32 0x18), ((25 : Fin 32), BitVec.ofNat 32 0x14), ((26 : Fin 32), BitVec.ofNat 32 0x10)]

section
set_option maxRecDepth 20000
theorem hfSave_end : blockEnd sha384FnCode 0x6 (saveBlockR a3 hfPs) = some 0x32 :=
  blockEnd_cons' hf_at_6 rfl (blockEnd_cons' hf_at_a rfl (blockEnd_cons' hf_at_c rfl (blockEnd_cons' hf_at_e rfl
    (blockEnd_cons' hf_at_12 rfl (blockEnd_cons' hf_at_16 rfl (blockEnd_cons' hf_at_1a rfl (blockEnd_cons' hf_at_1e rfl
    (blockEnd_cons' hf_at_22 rfl (blockEnd_cons' hf_at_26 rfl (blockEnd_cons' hf_at_2a rfl (blockEnd_cons' hf_at_2e rfl
    rfl)))))))))))
theorem hfRestore_end : blockEnd sha384FnCode 0x250 (restoreBlockR a0 hfPs) = some 0x27C :=
  blockEnd_cons' hf_at_250 rfl (blockEnd_cons' hf_at_254 rfl (blockEnd_cons' hf_at_256 rfl (blockEnd_cons' hf_at_258 rfl
    (blockEnd_cons' hf_at_25c rfl (blockEnd_cons' hf_at_260 rfl (blockEnd_cons' hf_at_264 rfl (blockEnd_cons' hf_at_268 rfl
    (blockEnd_cons' hf_at_26c rfl (blockEnd_cons' hf_at_270 rfl (blockEnd_cons' hf_at_274 rfl (blockEnd_cons' hf_at_278 rfl
    rfl)))))))))))
theorem hfPs_a0 : ∀ q ∈ hfPs, q.1 ≠ a0 := by decide
end

theorem hfSl (F o : Word) (_ : o.toNat < 0x40) : F + BitVec.ofNat 32 0x200 + o = F + BitVec.ofNat 32 (0x200 + o.toNat) := by
  rw [BitVec.add_assoc]; congr 1

theorem hfPs_mem {r : Fin 32} {o : Word} (h : (r, o) ∈ hfPs) :
    r ≠ sp ∧ r ≠ a3 ∧ r ≠ a0 ∧ r.val ≠ 0 ∧ o.toNat % 4 = 0 ∧ 0x10 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x40 := by
  simp only [hfPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hfPs_slot {r : Fin 32} {o : Word} (h : (r, o) ∈ hfPs) :
    ∀ p ∈ hfPs, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
      p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32) := by
  simp only [hfPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hfPs_restore (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) :
    ∀ r o, (r, o) ∈ hfPs → restoreRegs M G f hfPs r = memLoad32 M (G + o) := by
  intro r o hm
  simp only [hfPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp +decide only [restoreRegs, upd, ↓reduceIte]

theorem HfSt.slotW {M0 Ms : Word → BitVec 8} {F : Word} {r0 : Fin 32 → Word} {M : Word → BitVec 8} {n : Machine}
    {off : Nat} (D : HfSt M0 Ms F r0 M n off) {c : Nat} (h1 : 0x210 ≤ c) (h2 : c + 4 ≤ 0x240) :
    memLoad32 M (F + BitVec.ofNat 32 c) = memLoad32 Ms (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact D.slots _ (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From the entry to offset 0x32: the twelve registers saved at
`F + 0x200` and `sp` at `F`. -/
theorem hf_pro (m : Machine) {F out p : Word} {len : Nat} (C : HfCtx m.mem F out p len) (hpc : m.pc = HF)
    (hsp : reg m sp = F + BitVec.ofNat 32 0x240) :
    ∃ n Ms, Steps m n ∧ HfSt m.mem Ms F (reg m) Ms n 0x32 ∧
      (∀ r o, (r, o) ∈ hfPs → memLoad32 Ms (F + BitVec.ofNat 32 0x200 + o) = reg m r) ∧
      (∀ q, q ≠ sp → q ≠ a3 → reg n q = reg m q) := by
  have hc := C.env.cod
  have s0 : St m.mem HF m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨m1, d1, u1⟩ := s0.aluImm hc hf_at_0 (off' := 4) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.self.aluImm hc hf_at_4 (off' := 6) (by decide)
  have sp1 : reg m1 sp = F := by
    rw [u1.upd_eq (by decide), hsp]
    exact (show aluEval .add (F + BitVec.ofNat 32 0x240) 0xFFFFFDC0 = F + BitVec.ofNat 32 0 from
      add_spm F (by decide)).trans (add_ofNat_zero F)
  have a32 : reg m2 a3 = F + BitVec.ofNat 32 0x200 := by rw [u2.upd_eq (by decide), sp1]; rfl
  have r2 : ∀ q, q ≠ sp → q ≠ a3 → reg m2 q = reg m q := fun q h1 h2 => by
    rw [u2.upd_ne u1.self.zero q h2, u1.upd_ne s0.zero q h1]
  have sp2 : reg m2 sp = F := by rw [u2.upd_ne u1.self.zero sp (by decide), sp1]
  obtain ⟨m3, c3, u3⟩ := St.block (saveBlockR a3 hfPs) u2.self hc hfSave_end (saveBlockR_ok a3 _ hfPs _ fun p hp => by
    have hr := hfPs_mem (r := p.1) (o := p.2) hp
    rw [a32, hfSl F p.2 (by omega)]
    exact ⟨C.al (by omega), C.codeF (by omega) (by decide) (by rw [hf_len]; decide)⟩)
  rw [saveBlockR_run, a32] at u3
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem (F + BitVec.ofNat 32 0x200) (reg m2) hfPs = Ms := ⟨_, rfl⟩
  rw [hMs] at u3
  dsimp only at u3
  have r3 : ∀ q, reg m3 q = reg m2 q := fun q => by rw [u3.regs]
  refine ⟨m3, Ms, .cons d1 (.cons d2 c3), ⟨u3.self, by rw [r3, sp2], by rw [r3, r2 _ (by decide) (by decide)],
      by rw [r3, r2 _ (by decide) (by decide)], fun x hx => ?_, fun _ _ _ => rfl⟩,
    fun r o hm => ?_, fun q h1 h2 => by rw [r3, r2 q h1 h2]⟩
  · rw [← hMs]; exact saveMem_outside hfPs fun p hp => by
      have hr := hfPs_mem (r := p.1) (o := p.2) hp
      rw [hfSl F p.2 (by omega)]; exact C.inG (by omega) hx
  · have hr := hfPs_mem hm
    rw [← hMs, saveMem_slot hfPs _ hm (hfPs_slot hm), r2 r hr.1 hr.2.1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From offset 0x24E: the epilogue, with the slots at `F + 0x200`
holding `rM`'s saved registers. -/
theorem hf_fin {M : Word → BitVec 8} {F : Word} {n : Machine} (hc : CodeIn M HF sha384FnCode)
    (s : St M HF n 0x24E (reg n)) (hsp : reg n sp = F) (hF : F.toNat % 16 = 0)
    {rM : Fin 32 → Word} (hsl : ∀ r o, (r, o) ∈ hfPs → memLoad32 M (F + BitVec.ofNat 32 0x200 + o) = rM r)
    (hret : rM ra &&& ~~~1 = rM ra) :
    ∃ m', Steps n m' ∧ m'.pc = rM ra ∧ reg m' sp = F + BitVec.ofNat 32 0x240 ∧
      (∀ r o, (r, o) ∈ hfPs → reg m' r = rM r) ∧
      (∀ q : Fin 32, q ≠ sp → q ≠ a0 → q.val ≠ 0 → (∀ p ∈ hfPs, p.1 ≠ q) → reg m' q = reg n q) ∧ m'.mem = M := by
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc hf_at_24e (off' := 0x250) (by decide)
  have a01 : reg n1 a0 = F + BitVec.ofNat 32 0x200 := by rw [u1.upd_eq (by decide), hsp]; rfl
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q h => u1.upd_ne s.zero q h
  have sp1 : reg n1 sp = F := by rw [r1 _ (by decide), hsp]
  have hal : ∀ p ∈ hfPs, (F + BitVec.ofNat 32 0x200 + p.2).toNat % 4 = 0 := fun p hp => by
    have hr := hfPs_mem (r := p.1) (o := p.2) hp
    rw [hfSl F p.2 (by omega)]; exact aligned_add (by omega) (by omega)
  obtain ⟨n2, c2, u2⟩ := St.block (restoreBlockR a0 hfPs) u1.self hc hfRestore_end
    (restoreBlockR_ok _ (F + BitVec.ofNat 32 0x200) a0 (by decide) hfPs _ a01 hfPs_a0 hal)
  rw [restoreBlockR_run _ (F + BitVec.ofNat 32 0x200) a0 (by decide) hfPs _ a01 hfPs_a0] at u2
  dsimp only at u2
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc hf_at_27c (off' := 0x280) (by decide)
  obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.self.jalr hc hf_at_280
  have spR : restoreRegs M (F + BitVec.ofNat 32 0x200) (reg n1) hfPs sp = F := by
    rw [restoreRegs_other _ _ hfPs _ sp (by decide) (by decide), sp1]
  refine ⟨n4, .cons d1 (c2.trans (.cons d3 (.single d4))), ?_, ?_, fun r o hm => ?_, fun q hq h0 hz hps => ?_,
    by rw [mem4]⟩
  · rw [pc4, u3.regs, upd_ne (by decide) (by decide), hfPs_restore _ _ _ ra (BitVec.ofNat 32 0x3C) (by decide),
      hsl ra _ (by decide), add_lit_zero, hret]
  · rw [regs4, u3.regs]; simp only [upd_app, ↓reduceIte]; rw [spR]; rfl
  · have hr := hfPs_mem hm
    rw [regs4, u3.regs, upd_ne hr.2.2.2.1 hr.1, hfPs_restore _ _ _ r o hm, hsl r o hm]
  · rw [regs4, u3.regs, upd_ne hz hq, restoreRegs_other _ _ hfPs _ q hz hps, r1 q h0]

end C3.RV32
