import C3BootProofs.Proofs.ReaderArray
import C3BootProofs.Image.Bootloader
import C3BootProofs.Image.BootloaderData3

/-!
# Fetch lemmas for `c3_verify::trusted_root::read_chain`

One `fetchRel` lemma for each instruction of `trustedRootReadChainCode`.
The keys `validFor`, `certChain`, `certificates`, and `rawBytes`, and
`SECP384R1`, sit in read-only data that the image extraction doesn't name,
so their addresses are offsets from the nearest named item.
-/

namespace C3.RV32

open C3.Image

set_option maxRecDepth 20000

theorem trc_at_0 : fetchRel trustedRootReadChainCode 0x0 = some (.aluImm .add sp sp 0xFFFFFE80, 2) := by decide
theorem trc_at_2 : fetchRel trustedRootReadChainCode 0x2 = some (.aluImm .add a4 sp 0x100, 2) := by decide
theorem trc_at_4 : fetchRel trustedRootReadChainCode 0x4 = some (.store .sw a4 ra 0x7C, 4) := by decide
theorem trc_at_8 : fetchRel trustedRootReadChainCode 0x8 = some (.store .sw a4 (8 : Fin 32) 0x78, 2) := by decide
theorem trc_at_a : fetchRel trustedRootReadChainCode 0xA = some (.store .sw a4 (9 : Fin 32) 0x74, 2) := by decide
theorem trc_at_c : fetchRel trustedRootReadChainCode 0xC = some (.store .sw a4 (18 : Fin 32) 0x70, 4) := by decide
theorem trc_at_10 : fetchRel trustedRootReadChainCode 0x10 = some (.store .sw a4 (19 : Fin 32) 0x6C, 4) := by decide
theorem trc_at_14 : fetchRel trustedRootReadChainCode 0x14 = some (.store .sw a4 (20 : Fin 32) 0x68, 4) := by decide
theorem trc_at_18 : fetchRel trustedRootReadChainCode 0x18 = some (.store .sw a4 (21 : Fin 32) 0x64, 4) := by decide
theorem trc_at_1c : fetchRel trustedRootReadChainCode 0x1C = some (.store .sw a4 (22 : Fin 32) 0x60, 4) := by decide
theorem trc_at_20 : fetchRel trustedRootReadChainCode 0x20 = some (.store .sw a4 (23 : Fin 32) 0x5C, 4) := by decide
theorem trc_at_24 : fetchRel trustedRootReadChainCode 0x24 = some (.store .sw a4 (24 : Fin 32) 0x58, 4) := by decide
theorem trc_at_28 : fetchRel trustedRootReadChainCode 0x28 = some (.store .sw a4 (25 : Fin 32) 0x54, 4) := by decide
theorem trc_at_2c : fetchRel trustedRootReadChainCode 0x2C = some (.store .sw a4 (26 : Fin 32) 0x50, 4) := by decide
theorem trc_at_30 : fetchRel trustedRootReadChainCode 0x30 = some (.store .sw a4 (27 : Fin 32) 0x4C, 4) := by decide
theorem trc_at_34 : fetchRel trustedRootReadChainCode 0x34 = some (.alu .add (25 : Fin 32) x0 a3, 2) := by decide
theorem trc_at_36 : fetchRel trustedRootReadChainCode 0x36 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem trc_at_38 : fetchRel trustedRootReadChainCode 0x38 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem trc_at_3a : fetchRel trustedRootReadChainCode 0x3A = some (.alu .add (26 : Fin 32) x0 a0, 2) := by decide
theorem trc_at_3c : fetchRel trustedRootReadChainCode 0x3C = some (.lui a3 (img% hi20 (b64AlphabetAddress + 0x48)), 4) := by decide
theorem trc_at_40 : fetchRel trustedRootReadChainCode 0x40 = some (.aluImm .add a3 a3 (img% lo12 (b64AlphabetAddress + 0x48)), 4) := by decide
theorem trc_at_44 : fetchRel trustedRootReadChainCode 0x44 = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem trc_at_46 : fetchRel trustedRootReadChainCode 0x46 = some (.aluImm .add a4 x0 0x8, 2) := by decide
theorem trc_at_48 : fetchRel trustedRootReadChainCode 0x48 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem trc_at_4c : fetchRel trustedRootReadChainCode 0x4C = some (.jalr ra ra 0xFFFFFE8A, 4) := by decide
theorem trc_at_50 : fetchRel trustedRootReadChainCode 0x50 = some (.load .lw a1 sp 0x60, 2) := by decide
theorem trc_at_52 : fetchRel trustedRootReadChainCode 0x52 = some (.branch .beq a1 x0 0x42E, 4) := by decide
theorem trc_at_56 : fetchRel trustedRootReadChainCode 0x56 = some (.load .lw a2 sp 0x64, 2) := by decide
theorem trc_at_58 : fetchRel trustedRootReadChainCode 0x58 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_5a : fetchRel trustedRootReadChainCode 0x5A = some (.auipc ra 0x0, 4) := by decide
theorem trc_at_5e : fetchRel trustedRootReadChainCode 0x5E = some (.jalr ra ra 0x554, 4) := by decide
theorem trc_at_62 : fetchRel trustedRootReadChainCode 0x62 = some (.load .lbu a0 sp 0xE0, 4) := by decide
theorem trc_at_66 : fetchRel trustedRootReadChainCode 0x66 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem trc_at_68 : fetchRel trustedRootReadChainCode 0x68 = some (.load .lbu a0 sp 0xE1, 4) := by decide
theorem trc_at_6c : fetchRel trustedRootReadChainCode 0x6C = some (.jal x0 0x418, 2) := by decide
theorem trc_at_6e : fetchRel trustedRootReadChainCode 0x6E = some (.load .lw (19 : Fin 32) sp 0xE8, 2) := by decide
theorem trc_at_70 : fetchRel trustedRootReadChainCode 0x70 = some (.load .lw (21 : Fin 32) sp 0xEC, 2) := by decide
theorem trc_at_72 : fetchRel trustedRootReadChainCode 0x72 = some (.load .lw (27 : Fin 32) sp 0xF0, 2) := by decide
theorem trc_at_74 : fetchRel trustedRootReadChainCode 0x74 = some (.load .lw (24 : Fin 32) sp 0xF4, 2) := by decide
theorem trc_at_76 : fetchRel trustedRootReadChainCode 0x76 = some (.lui a3 (img% hi20 (svOidPrime256v1Address + 0x3D)), 4) := by decide
theorem trc_at_7a : fetchRel trustedRootReadChainCode 0x7A = some (.aluImm .add a3 a3 (img% lo12 (svOidPrime256v1Address + 0x3D)), 4) := by decide
theorem trc_at_7e : fetchRel trustedRootReadChainCode 0x7E = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem trc_at_80 : fetchRel trustedRootReadChainCode 0x80 = some (.aluImm .add a4 x0 0x9, 2) := by decide
theorem trc_at_82 : fetchRel trustedRootReadChainCode 0x82 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem trc_at_84 : fetchRel trustedRootReadChainCode 0x84 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem trc_at_86 : fetchRel trustedRootReadChainCode 0x86 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem trc_at_8a : fetchRel trustedRootReadChainCode 0x8A = some (.jalr ra ra 0xFFFFFE4C, 4) := by decide
theorem trc_at_8e : fetchRel trustedRootReadChainCode 0x8E = some (.load .lw a1 sp 0x60, 2) := by decide
theorem trc_at_90 : fetchRel trustedRootReadChainCode 0x90 = some (.branch .beq a1 x0 0x3F0, 4) := by decide
theorem trc_at_94 : fetchRel trustedRootReadChainCode 0x94 = some (.load .lw a2 sp 0x64, 2) := by decide
theorem trc_at_96 : fetchRel trustedRootReadChainCode 0x96 = some (.lui a3 (img% hi20 (svOidPrime256v1Address + 0x46)), 4) := by decide
theorem trc_at_9a : fetchRel trustedRootReadChainCode 0x9A = some (.aluImm .add a3 a3 (img% lo12 (svOidPrime256v1Address + 0x46)), 4) := by decide
theorem trc_at_9e : fetchRel trustedRootReadChainCode 0x9E = some (.aluImm .add a0 sp 0xD0, 2) := by decide
theorem trc_at_a0 : fetchRel trustedRootReadChainCode 0xA0 = some (.aluImm .add a4 x0 0xC, 2) := by decide
theorem trc_at_a2 : fetchRel trustedRootReadChainCode 0xA2 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem trc_at_a6 : fetchRel trustedRootReadChainCode 0xA6 = some (.jalr ra ra 0xFFFFFE30, 4) := by decide
theorem trc_at_aa : fetchRel trustedRootReadChainCode 0xAA = some (.load .lw a1 sp 0xD0, 2) := by decide
theorem trc_at_ac : fetchRel trustedRootReadChainCode 0xAC = some (.branch .beq a1 x0 0x416, 4) := by decide
theorem trc_at_b0 : fetchRel trustedRootReadChainCode 0xB0 = some (.load .lw a2 sp 0xD4, 2) := by decide
theorem trc_at_b2 : fetchRel trustedRootReadChainCode 0xB2 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_b4 : fetchRel trustedRootReadChainCode 0xB4 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem trc_at_b8 : fetchRel trustedRootReadChainCode 0xB8 = some (.jalr ra ra 0xFFFFFD76, 4) := by decide
theorem trc_at_bc : fetchRel trustedRootReadChainCode 0xBC = some (.load .lw (9 : Fin 32) sp 0xE0, 2) := by decide
theorem trc_at_be : fetchRel trustedRootReadChainCode 0xBE = some (.load .lbu (8 : Fin 32) sp 0xE4, 4) := by decide
theorem trc_at_c2 : fetchRel trustedRootReadChainCode 0xC2 = some (.branch .beq (9 : Fin 32) x0 0x406, 4) := by decide
theorem trc_at_c6 : fetchRel trustedRootReadChainCode 0xC6 = some (.aluImm .add a1 sp 0xE5, 4) := by decide
theorem trc_at_ca : fetchRel trustedRootReadChainCode 0xCA = some (.aluImm .add a0 sp 0x29, 4) := by decide
theorem trc_at_ce : fetchRel trustedRootReadChainCode 0xCE = some (.aluImm .add a2 x0 0x7, 2) := by decide
theorem trc_at_d0 : fetchRel trustedRootReadChainCode 0xD0 = some (.auipc ra 0xB000, 4) := by decide
theorem trc_at_d4 : fetchRel trustedRootReadChainCode 0xD4 = some (.jalr ra ra 0xFFFFFF48, 4) := by decide
theorem trc_at_d8 : fetchRel trustedRootReadChainCode 0xD8 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem trc_at_da : fetchRel trustedRootReadChainCode 0xDA = some (.store .sb sp (8 : Fin 32) 0x28, 4) := by decide
theorem trc_at_de : fetchRel trustedRootReadChainCode 0xDE = some (.store .sw sp x0 0x30, 2) := by decide
theorem trc_at_e0 : fetchRel trustedRootReadChainCode 0xE0 = some (.aluImm .add (20 : Fin 32) sp 0xE5, 4) := by decide
theorem trc_at_e4 : fetchRel trustedRootReadChainCode 0xE4 = some (.aluImm .add (9 : Fin 32) sp 0xA5, 4) := by decide
theorem trc_at_e8 : fetchRel trustedRootReadChainCode 0xE8 = some (.aluImm .add (23 : Fin 32) sp 0xE5, 4) := by decide
theorem trc_at_ec : fetchRel trustedRootReadChainCode 0xEC = some (.lui (8 : Fin 32) (img% hi20 (u2MaxAddress + 0x8)), 4) := by decide
theorem trc_at_f0 : fetchRel trustedRootReadChainCode 0xF0 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) (img% lo12 (u2MaxAddress + 0x8)), 4) := by decide
theorem trc_at_f4 : fetchRel trustedRootReadChainCode 0xF4 = some (.aluImm .add (22 : Fin 32) x0 0x4, 2) := by decide
theorem trc_at_f6 : fetchRel trustedRootReadChainCode 0xF6 = some (.branch .beq (22 : Fin 32) x0 0x3E2, 4) := by decide
theorem trc_at_fa : fetchRel trustedRootReadChainCode 0xFA = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_fc : fetchRel trustedRootReadChainCode 0xFC = some (.aluImm .add a1 sp 0x24, 2) := by decide
theorem trc_at_fe : fetchRel trustedRootReadChainCode 0xFE = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem trc_at_102 : fetchRel trustedRootReadChainCode 0x102 = some (.jalr ra ra 0xFFFFFD76, 4) := by decide
theorem trc_at_106 : fetchRel trustedRootReadChainCode 0x106 = some (.load .lbu a0 sp 0xE0, 4) := by decide
theorem trc_at_10a : fetchRel trustedRootReadChainCode 0x10A = some (.branch .bne a0 x0 0xFFFFFF5E, 2) := by decide
theorem trc_at_10c : fetchRel trustedRootReadChainCode 0x10C = some (.load .lw a1 sp 0xE4, 2) := by decide
theorem trc_at_10e : fetchRel trustedRootReadChainCode 0x10E = some (.branch .beq a1 x0 0x3CA, 4) := by decide
theorem trc_at_112 : fetchRel trustedRootReadChainCode 0x112 = some (.load .lw a2 sp 0xE8, 2) := by decide
theorem trc_at_114 : fetchRel trustedRootReadChainCode 0x114 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_116 : fetchRel trustedRootReadChainCode 0x116 = some (.aluImm .add a4 x0 0x8, 2) := by decide
theorem trc_at_118 : fetchRel trustedRootReadChainCode 0x118 = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem trc_at_11a : fetchRel trustedRootReadChainCode 0x11A = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem trc_at_11e : fetchRel trustedRootReadChainCode 0x11E = some (.jalr ra ra 0xFFFFFDB8, 4) := by decide
theorem trc_at_122 : fetchRel trustedRootReadChainCode 0x122 = some (.load .lw a1 sp 0xE0, 2) := by decide
theorem trc_at_124 : fetchRel trustedRootReadChainCode 0x124 = some (.branch .beq a1 x0 0x3D8, 4) := by decide
theorem trc_at_128 : fetchRel trustedRootReadChainCode 0x128 = some (.load .lw a2 sp 0xE4, 2) := by decide
theorem trc_at_12a : fetchRel trustedRootReadChainCode 0x12A = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem trc_at_12c : fetchRel trustedRootReadChainCode 0x12C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem trc_at_130 : fetchRel trustedRootReadChainCode 0x130 = some (.jalr ra ra 0xFFFFFDE2, 4) := by decide
theorem trc_at_134 : fetchRel trustedRootReadChainCode 0x134 = some (.load .lw a1 sp 0x60, 2) := by decide
theorem trc_at_136 : fetchRel trustedRootReadChainCode 0x136 = some (.branch .beq a1 x0 0x34A, 4) := by decide
theorem trc_at_13a : fetchRel trustedRootReadChainCode 0x13A = some (.load .lw a2 sp 0x64, 2) := by decide
theorem trc_at_13c : fetchRel trustedRootReadChainCode 0x13C = some (.aluImm .add a0 sp 0xD0, 2) := by decide
theorem trc_at_13e : fetchRel trustedRootReadChainCode 0x13E = some (.alu .add a3 x0 (25 : Fin 32), 2) := by decide
theorem trc_at_140 : fetchRel trustedRootReadChainCode 0x140 = some (.auipc ra 0x0, 4) := by decide
theorem trc_at_144 : fetchRel trustedRootReadChainCode 0x144 = some (.jalr ra ra 0x404, 4) := by decide
theorem trc_at_148 : fetchRel trustedRootReadChainCode 0x148 = some (.load .lw a0 sp 0xD0, 2) := by decide
theorem trc_at_14a : fetchRel trustedRootReadChainCode 0x14A = some (.branch .beq a0 x0 0x378, 4) := by decide
theorem trc_at_14e : fetchRel trustedRootReadChainCode 0x14E = some (.load .lw a1 sp 0xD4, 2) := by decide
theorem trc_at_150 : fetchRel trustedRootReadChainCode 0x150 = some (.store .sw sp a0 0x90, 2) := by decide
theorem trc_at_152 : fetchRel trustedRootReadChainCode 0x152 = some (.store .sw sp a1 0x94, 2) := by decide
theorem trc_at_154 : fetchRel trustedRootReadChainCode 0x154 = some (.store .sw sp a0 0x98, 2) := by decide
theorem trc_at_156 : fetchRel trustedRootReadChainCode 0x156 = some (.store .sw sp a1 0x9C, 2) := by decide
theorem trc_at_158 : fetchRel trustedRootReadChainCode 0x158 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_15a : fetchRel trustedRootReadChainCode 0x15A = some (.aluImm .add a1 sp 0x90, 2) := by decide
theorem trc_at_15c : fetchRel trustedRootReadChainCode 0x15C = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_160 : fetchRel trustedRootReadChainCode 0x160 = some (.jalr ra ra 0xFFFFFBC6, 4) := by decide
theorem trc_at_164 : fetchRel trustedRootReadChainCode 0x164 = some (.load .lw (8 : Fin 32) sp 0xE0, 2) := by decide
theorem trc_at_166 : fetchRel trustedRootReadChainCode 0x166 = some (.load .lbu (18 : Fin 32) sp 0xE4, 4) := by decide
theorem trc_at_16a : fetchRel trustedRootReadChainCode 0x16A = some (.branch .beq (8 : Fin 32) x0 0x39A, 4) := by decide
theorem trc_at_16e : fetchRel trustedRootReadChainCode 0x16E = some (.aluImm .add a2 x0 0xB, 2) := by decide
theorem trc_at_170 : fetchRel trustedRootReadChainCode 0x170 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem trc_at_172 : fetchRel trustedRootReadChainCode 0x172 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem trc_at_174 : fetchRel trustedRootReadChainCode 0x174 = some (.auipc ra 0xB000, 4) := by decide
theorem trc_at_178 : fetchRel trustedRootReadChainCode 0x178 = some (.jalr ra ra 0xFFFFFEA4, 4) := by decide
theorem trc_at_17c : fetchRel trustedRootReadChainCode 0x17C = some (.load .lw a0 sp 0x9C, 2) := by decide
theorem trc_at_17e : fetchRel trustedRootReadChainCode 0x17E = some (.store .sw sp (8 : Fin 32) 0xA0, 2) := by decide
theorem trc_at_180 : fetchRel trustedRootReadChainCode 0x180 = some (.store .sb sp (18 : Fin 32) 0xA4, 4) := by decide
theorem trc_at_184 : fetchRel trustedRootReadChainCode 0x184 = some (.aluImm .add (18 : Fin 32) x0 0x1, 2) := by decide
theorem trc_at_186 : fetchRel trustedRootReadChainCode 0x186 = some (.branch .bne a0 x0 0x37E, 4) := by decide
theorem trc_at_18a : fetchRel trustedRootReadChainCode 0x18A = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_18c : fetchRel trustedRootReadChainCode 0x18C = some (.aluImm .add a1 sp 0xA0, 2) := by decide
theorem trc_at_18e : fetchRel trustedRootReadChainCode 0x18E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem trc_at_192 : fetchRel trustedRootReadChainCode 0x192 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_196 : fetchRel trustedRootReadChainCode 0x196 = some (.jalr ra ra 0xFFFFFD28, 4) := by decide
theorem trc_at_19a : fetchRel trustedRootReadChainCode 0x19A = some (.load .lw (9 : Fin 32) sp 0xE0, 2) := by decide
theorem trc_at_19c : fetchRel trustedRootReadChainCode 0x19C = some (.branch .beq (9 : Fin 32) x0 0x336, 4) := by decide
theorem trc_at_1a0 : fetchRel trustedRootReadChainCode 0x1A0 = some (.load .lw (8 : Fin 32) sp 0xE4, 2) := by decide
theorem trc_at_1a2 : fetchRel trustedRootReadChainCode 0x1A2 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_1a4 : fetchRel trustedRootReadChainCode 0x1A4 = some (.aluImm .add a1 sp 0xA0, 2) := by decide
theorem trc_at_1a6 : fetchRel trustedRootReadChainCode 0x1A6 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem trc_at_1aa : fetchRel trustedRootReadChainCode 0x1AA = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_1ae : fetchRel trustedRootReadChainCode 0x1AE = some (.jalr ra ra 0xFFFFFD10, 4) := by decide
theorem trc_at_1b2 : fetchRel trustedRootReadChainCode 0x1B2 = some (.load .lw a0 sp 0xE0, 2) := by decide
theorem trc_at_1b4 : fetchRel trustedRootReadChainCode 0x1B4 = some (.branch .beq a0 x0 0x31E, 4) := by decide
theorem trc_at_1b8 : fetchRel trustedRootReadChainCode 0x1B8 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_1ba : fetchRel trustedRootReadChainCode 0x1BA = some (.aluImm .add a1 sp 0xA0, 2) := by decide
theorem trc_at_1bc : fetchRel trustedRootReadChainCode 0x1BC = some (.auipc ra 0x1000, 4) := by decide
theorem trc_at_1c0 : fetchRel trustedRootReadChainCode 0x1C0 = some (.jalr ra ra 0xFFFFF95E, 4) := by decide
theorem trc_at_1c4 : fetchRel trustedRootReadChainCode 0x1C4 = some (.load .lw a0 sp 0xE0, 2) := by decide
theorem trc_at_1c6 : fetchRel trustedRootReadChainCode 0x1C6 = some (.branch .beq a0 x0 0x30C, 4) := by decide
theorem trc_at_1ca : fetchRel trustedRootReadChainCode 0x1CA = some (.load .lw a0 sp 0xAC, 2) := by decide
theorem trc_at_1cc : fetchRel trustedRootReadChainCode 0x1CC = some (.branch .bne a0 x0 0x338, 4) := by decide
theorem trc_at_1d0 : fetchRel trustedRootReadChainCode 0x1D0 = some (.store .sw sp (9 : Fin 32) 0xB0, 2) := by decide
theorem trc_at_1d2 : fetchRel trustedRootReadChainCode 0x1D2 = some (.store .sw sp (8 : Fin 32) 0xB4, 2) := by decide
theorem trc_at_1d4 : fetchRel trustedRootReadChainCode 0x1D4 = some (.store .sw sp (9 : Fin 32) 0xB8, 2) := by decide
theorem trc_at_1d6 : fetchRel trustedRootReadChainCode 0x1D6 = some (.store .sw sp (8 : Fin 32) 0xBC, 2) := by decide
theorem trc_at_1d8 : fetchRel trustedRootReadChainCode 0x1D8 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_1da : fetchRel trustedRootReadChainCode 0x1DA = some (.aluImm .add a1 sp 0xB0, 2) := by decide
theorem trc_at_1dc : fetchRel trustedRootReadChainCode 0x1DC = some (.aluImm .add a2 x0 0xA0, 4) := by decide
theorem trc_at_1e0 : fetchRel trustedRootReadChainCode 0x1E0 = some (.auipc ra 0x1000, 4) := by decide
theorem trc_at_1e4 : fetchRel trustedRootReadChainCode 0x1E4 = some (.jalr ra ra 0xFFFFF97E, 4) := by decide
theorem trc_at_1e8 : fetchRel trustedRootReadChainCode 0x1E8 = some (.load .lbu a0 sp 0xE0, 4) := by decide
theorem trc_at_1ec : fetchRel trustedRootReadChainCode 0x1EC = some (.branch .bne a0 x0 0x30A, 4) := by decide
theorem trc_at_1f0 : fetchRel trustedRootReadChainCode 0x1F0 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_1f2 : fetchRel trustedRootReadChainCode 0x1F2 = some (.aluImm .add a1 sp 0xB0, 2) := by decide
theorem trc_at_1f4 : fetchRel trustedRootReadChainCode 0x1F4 = some (.aluImm .add a2 x0 0x2, 2) := by decide
theorem trc_at_1f6 : fetchRel trustedRootReadChainCode 0x1F6 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_1fa : fetchRel trustedRootReadChainCode 0x1FA = some (.jalr ra ra 0xFFFFFCC4, 4) := by decide
theorem trc_at_1fe : fetchRel trustedRootReadChainCode 0x1FE = some (.load .lw a0 sp 0xE0, 2) := by decide
theorem trc_at_200 : fetchRel trustedRootReadChainCode 0x200 = some (.branch .beq a0 x0 0x2D2, 4) := by decide
theorem trc_at_204 : fetchRel trustedRootReadChainCode 0x204 = some (.store .sw sp (22 : Fin 32) 0x20, 2) := by decide
theorem trc_at_206 : fetchRel trustedRootReadChainCode 0x206 = some (.load .lw (20 : Fin 32) sp 0xE8, 2) := by decide
theorem trc_at_208 : fetchRel trustedRootReadChainCode 0x208 = some (.load .lw (22 : Fin 32) sp 0xEC, 2) := by decide
theorem trc_at_20a : fetchRel trustedRootReadChainCode 0x20A = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_20c : fetchRel trustedRootReadChainCode 0x20C = some (.aluImm .add a1 sp 0xB0, 2) := by decide
theorem trc_at_20e : fetchRel trustedRootReadChainCode 0x20E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem trc_at_212 : fetchRel trustedRootReadChainCode 0x212 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_216 : fetchRel trustedRootReadChainCode 0x216 = some (.jalr ra ra 0xFFFFFCA8, 4) := by decide
theorem trc_at_21a : fetchRel trustedRootReadChainCode 0x21A = some (.load .lw a0 sp 0xE0, 2) := by decide
theorem trc_at_21c : fetchRel trustedRootReadChainCode 0x21C = some (.branch .beq a0 x0 0x2B6, 4) := by decide
theorem trc_at_220 : fetchRel trustedRootReadChainCode 0x220 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_222 : fetchRel trustedRootReadChainCode 0x222 = some (.aluImm .add a1 sp 0xB0, 2) := by decide
theorem trc_at_224 : fetchRel trustedRootReadChainCode 0x224 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem trc_at_228 : fetchRel trustedRootReadChainCode 0x228 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_22c : fetchRel trustedRootReadChainCode 0x22C = some (.jalr ra ra 0xFFFFFC92, 4) := by decide
theorem trc_at_230 : fetchRel trustedRootReadChainCode 0x230 = some (.load .lw a0 sp 0xE0, 2) := by decide
theorem trc_at_232 : fetchRel trustedRootReadChainCode 0x232 = some (.branch .beq a0 x0 0x2A0, 4) := by decide
theorem trc_at_236 : fetchRel trustedRootReadChainCode 0x236 = some (.load .lw (9 : Fin 32) sp 0xE8, 2) := by decide
theorem trc_at_238 : fetchRel trustedRootReadChainCode 0x238 = some (.load .lw a0 sp 0xEC, 2) := by decide
theorem trc_at_23a : fetchRel trustedRootReadChainCode 0x23A = some (.store .sw sp a0 0x1C, 2) := by decide
theorem trc_at_23c : fetchRel trustedRootReadChainCode 0x23C = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_23e : fetchRel trustedRootReadChainCode 0x23E = some (.aluImm .add a1 sp 0xB0, 2) := by decide
theorem trc_at_240 : fetchRel trustedRootReadChainCode 0x240 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_244 : fetchRel trustedRootReadChainCode 0x244 = some (.jalr ra ra 0xFFFFFAE2, 4) := by decide
theorem trc_at_248 : fetchRel trustedRootReadChainCode 0x248 = some (.load .lw (8 : Fin 32) sp 0xE0, 2) := by decide
theorem trc_at_24a : fetchRel trustedRootReadChainCode 0x24A = some (.load .lbu (18 : Fin 32) sp 0xE4, 4) := by decide
theorem trc_at_24e : fetchRel trustedRootReadChainCode 0x24E = some (.branch .beq (8 : Fin 32) x0 0x2B6, 4) := by decide
theorem trc_at_252 : fetchRel trustedRootReadChainCode 0x252 = some (.aluImm .add a2 x0 0xB, 2) := by decide
theorem trc_at_254 : fetchRel trustedRootReadChainCode 0x254 = some (.aluImm .add a0 sp 0xC5, 4) := by decide
theorem trc_at_258 : fetchRel trustedRootReadChainCode 0x258 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem trc_at_25a : fetchRel trustedRootReadChainCode 0x25A = some (.auipc ra 0xB000, 4) := by decide
theorem trc_at_25e : fetchRel trustedRootReadChainCode 0x25E = some (.jalr ra ra 0xFFFFFDBE, 4) := by decide
theorem trc_at_262 : fetchRel trustedRootReadChainCode 0x262 = some (.store .sw sp (8 : Fin 32) 0xC0, 2) := by decide
theorem trc_at_264 : fetchRel trustedRootReadChainCode 0x264 = some (.store .sb sp (18 : Fin 32) 0xC4, 4) := by decide
theorem trc_at_268 : fetchRel trustedRootReadChainCode 0x268 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_26a : fetchRel trustedRootReadChainCode 0x26A = some (.aluImm .add a1 sp 0xC0, 2) := by decide
theorem trc_at_26c : fetchRel trustedRootReadChainCode 0x26C = some (.auipc ra 0x1000, 4) := by decide
theorem trc_at_270 : fetchRel trustedRootReadChainCode 0x270 = some (.jalr ra ra 0xFFFFF94A, 4) := by decide
theorem trc_at_274 : fetchRel trustedRootReadChainCode 0x274 = some (.load .lbu a0 sp 0xE0, 4) := by decide
theorem trc_at_278 : fetchRel trustedRootReadChainCode 0x278 = some (.branch .bne a0 x0 0x27E, 4) := by decide
theorem trc_at_27c : fetchRel trustedRootReadChainCode 0x27C = some (.store .sw sp (9 : Fin 32) 0x18, 2) := by decide
theorem trc_at_27e : fetchRel trustedRootReadChainCode 0x27E = some (.load .lw (9 : Fin 32) sp 0xE8, 2) := by decide
theorem trc_at_280 : fetchRel trustedRootReadChainCode 0x280 = some (.load .lw (8 : Fin 32) sp 0xEC, 2) := by decide
theorem trc_at_282 : fetchRel trustedRootReadChainCode 0x282 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_284 : fetchRel trustedRootReadChainCode 0x284 = some (.aluImm .add a1 sp 0xC0, 2) := by decide
theorem trc_at_286 : fetchRel trustedRootReadChainCode 0x286 = some (.auipc ra 0x1000, 4) := by decide
theorem trc_at_28a : fetchRel trustedRootReadChainCode 0x28A = some (.jalr ra ra 0xFFFFF930, 4) := by decide
theorem trc_at_28e : fetchRel trustedRootReadChainCode 0x28E = some (.load .lbu a0 sp 0xE0, 4) := by decide
theorem trc_at_292 : fetchRel trustedRootReadChainCode 0x292 = some (.branch .bne a0 x0 0x264, 4) := by decide
theorem trc_at_296 : fetchRel trustedRootReadChainCode 0x296 = some (.load .lw a0 sp 0xCC, 2) := by decide
theorem trc_at_298 : fetchRel trustedRootReadChainCode 0x298 = some (.branch .bne a0 x0 0x26A, 4) := by decide
theorem trc_at_29c : fetchRel trustedRootReadChainCode 0x29C = some (.load .lw (23 : Fin 32) sp 0xE8, 2) := by decide
theorem trc_at_29e : fetchRel trustedRootReadChainCode 0x29E = some (.load .lw (18 : Fin 32) sp 0xEC, 2) := by decide
theorem trc_at_2a0 : fetchRel trustedRootReadChainCode 0x2A0 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_2a2 : fetchRel trustedRootReadChainCode 0x2A2 = some (.aluImm .add a1 sp 0xB0, 2) := by decide
theorem trc_at_2a4 : fetchRel trustedRootReadChainCode 0x2A4 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem trc_at_2a8 : fetchRel trustedRootReadChainCode 0x2A8 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_2ac : fetchRel trustedRootReadChainCode 0x2AC = some (.jalr ra ra 0xFFFFFC12, 4) := by decide
theorem trc_at_2b0 : fetchRel trustedRootReadChainCode 0x2B0 = some (.load .lw a0 sp 0xE0, 2) := by decide
theorem trc_at_2b2 : fetchRel trustedRootReadChainCode 0x2B2 = some (.branch .beq a0 x0 0x220, 4) := by decide
theorem trc_at_2b6 : fetchRel trustedRootReadChainCode 0x2B6 = some (.load .lw a0 sp 0xE8, 2) := by decide
theorem trc_at_2b8 : fetchRel trustedRootReadChainCode 0x2B8 = some (.store .sw sp a0 0x10, 2) := by decide
theorem trc_at_2ba : fetchRel trustedRootReadChainCode 0x2BA = some (.load .lw a0 sp 0xEC, 2) := by decide
theorem trc_at_2bc : fetchRel trustedRootReadChainCode 0x2BC = some (.store .sw sp a0 0x14, 2) := by decide
theorem trc_at_2be : fetchRel trustedRootReadChainCode 0x2BE = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_2c0 : fetchRel trustedRootReadChainCode 0x2C0 = some (.aluImm .add a1 sp 0xB0, 2) := by decide
theorem trc_at_2c2 : fetchRel trustedRootReadChainCode 0x2C2 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem trc_at_2c6 : fetchRel trustedRootReadChainCode 0x2C6 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_2ca : fetchRel trustedRootReadChainCode 0x2CA = some (.jalr ra ra 0xFFFFFBF4, 4) := by decide
theorem trc_at_2ce : fetchRel trustedRootReadChainCode 0x2CE = some (.load .lw a0 sp 0xE0, 2) := by decide
theorem trc_at_2d0 : fetchRel trustedRootReadChainCode 0x2D0 = some (.branch .beq a0 x0 0x202, 4) := by decide
theorem trc_at_2d4 : fetchRel trustedRootReadChainCode 0x2D4 = some (.load .lw a0 sp 0xE8, 2) := by decide
theorem trc_at_2d6 : fetchRel trustedRootReadChainCode 0x2D6 = some (.load .lw a1 sp 0xEC, 2) := by decide
theorem trc_at_2d8 : fetchRel trustedRootReadChainCode 0x2D8 = some (.store .sw sp a0 0xD0, 2) := by decide
theorem trc_at_2da : fetchRel trustedRootReadChainCode 0x2DA = some (.store .sw sp a1 0xD4, 2) := by decide
theorem trc_at_2dc : fetchRel trustedRootReadChainCode 0x2DC = some (.store .sw sp a0 0xD8, 2) := by decide
theorem trc_at_2de : fetchRel trustedRootReadChainCode 0x2DE = some (.store .sw sp a1 0xDC, 2) := by decide
theorem trc_at_2e0 : fetchRel trustedRootReadChainCode 0x2E0 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_2e2 : fetchRel trustedRootReadChainCode 0x2E2 = some (.aluImm .add a1 sp 0xD0, 2) := by decide
theorem trc_at_2e4 : fetchRel trustedRootReadChainCode 0x2E4 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem trc_at_2e8 : fetchRel trustedRootReadChainCode 0x2E8 = some (.jalr ra ra 0xFFFFFA3E, 4) := by decide
theorem trc_at_2ec : fetchRel trustedRootReadChainCode 0x2EC = some (.load .lw a0 sp 0xE0, 2) := by decide
theorem trc_at_2ee : fetchRel trustedRootReadChainCode 0x2EE = some (.branch .beq a0 x0 0x18, 2) := by decide
theorem trc_at_2f0 : fetchRel trustedRootReadChainCode 0x2F0 = some (.aluImm .add a3 sp 0xE4, 2) := by decide
theorem trc_at_2f2 : fetchRel trustedRootReadChainCode 0x2F2 = some (.load .lw a1 a3 0x0, 2) := by decide
theorem trc_at_2f4 : fetchRel trustedRootReadChainCode 0x2F4 = some (.load .lw a2 a3 0x4, 2) := by decide
theorem trc_at_2f6 : fetchRel trustedRootReadChainCode 0x2F6 = some (.load .lw a3 a3 0x8, 2) := by decide
theorem trc_at_2f8 : fetchRel trustedRootReadChainCode 0x2F8 = some (.load .lw a4 sp 0xDC, 2) := by decide
theorem trc_at_2fa : fetchRel trustedRootReadChainCode 0x2FA = some (.aluImm .add a5 sp 0x64, 2) := by decide
theorem trc_at_2fc : fetchRel trustedRootReadChainCode 0x2FC = some (.store .sw a5 a1 0x0, 2) := by decide
theorem trc_at_2fe : fetchRel trustedRootReadChainCode 0x2FE = some (.store .sw a5 a2 0x4, 2) := by decide
theorem trc_at_300 : fetchRel trustedRootReadChainCode 0x300 = some (.store .sw a5 a3 0x8, 2) := by decide
theorem trc_at_302 : fetchRel trustedRootReadChainCode 0x302 = some (.store .sw sp a0 0x60, 2) := by decide
theorem trc_at_304 : fetchRel trustedRootReadChainCode 0x304 = some (.branch .beq a4 x0 0xCA, 2) := by decide
theorem trc_at_306 : fetchRel trustedRootReadChainCode 0x306 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem trc_at_308 : fetchRel trustedRootReadChainCode 0x308 = some (.branch .beq (8 : Fin 32) (21 : Fin 32) 0xE, 4) := by decide
theorem trc_at_30c : fetchRel trustedRootReadChainCode 0x30C = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem trc_at_30e : fetchRel trustedRootReadChainCode 0x30E = some (.alu .add a3 x0 (21 : Fin 32), 2) := by decide
theorem trc_at_310 : fetchRel trustedRootReadChainCode 0x310 = some (.alu .sltu a0 (21 : Fin 32) (8 : Fin 32), 4) := by decide
theorem trc_at_314 : fetchRel trustedRootReadChainCode 0x314 = some (.jal x0 0xA, 2) := by decide
theorem trc_at_316 : fetchRel trustedRootReadChainCode 0x316 = some (.alu .add a3 x0 (21 : Fin 32), 2) := by decide
theorem trc_at_318 : fetchRel trustedRootReadChainCode 0x318 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem trc_at_31a : fetchRel trustedRootReadChainCode 0x31A = some (.alu .sltu a0 (19 : Fin 32) (9 : Fin 32), 4) := by decide
theorem trc_at_31e : fetchRel trustedRootReadChainCode 0x31E = some (.alu .add (21 : Fin 32) x0 (8 : Fin 32), 2) := by decide
theorem trc_at_320 : fetchRel trustedRootReadChainCode 0x320 = some (.alu .add (19 : Fin 32) x0 (9 : Fin 32), 2) := by decide
theorem trc_at_322 : fetchRel trustedRootReadChainCode 0x322 = some (.branch .bne a0 x0 0x6, 2) := by decide
theorem trc_at_324 : fetchRel trustedRootReadChainCode 0x324 = some (.alu .add (21 : Fin 32) x0 a3, 2) := by decide
theorem trc_at_326 : fetchRel trustedRootReadChainCode 0x326 = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem trc_at_328 : fetchRel trustedRootReadChainCode 0x328 = some (.branch .beq (18 : Fin 32) (24 : Fin 32) 0xE, 4) := by decide
theorem trc_at_32c : fetchRel trustedRootReadChainCode 0x32C = some (.alu .add a2 x0 (27 : Fin 32), 2) := by decide
theorem trc_at_32e : fetchRel trustedRootReadChainCode 0x32E = some (.alu .add a3 x0 (24 : Fin 32), 2) := by decide
theorem trc_at_330 : fetchRel trustedRootReadChainCode 0x330 = some (.alu .sltu a0 (18 : Fin 32) (24 : Fin 32), 4) := by decide
theorem trc_at_334 : fetchRel trustedRootReadChainCode 0x334 = some (.jal x0 0xA, 2) := by decide
theorem trc_at_336 : fetchRel trustedRootReadChainCode 0x336 = some (.alu .add a3 x0 (24 : Fin 32), 2) := by decide
theorem trc_at_338 : fetchRel trustedRootReadChainCode 0x338 = some (.alu .add a2 x0 (27 : Fin 32), 2) := by decide
theorem trc_at_33a : fetchRel trustedRootReadChainCode 0x33A = some (.alu .sltu a0 (23 : Fin 32) (27 : Fin 32), 4) := by decide
theorem trc_at_33e : fetchRel trustedRootReadChainCode 0x33E = some (.alu .add (24 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem trc_at_340 : fetchRel trustedRootReadChainCode 0x340 = some (.alu .add (27 : Fin 32) x0 (23 : Fin 32), 2) := by decide
theorem trc_at_342 : fetchRel trustedRootReadChainCode 0x342 = some (.branch .bne a0 x0 0x6, 2) := by decide
theorem trc_at_344 : fetchRel trustedRootReadChainCode 0x344 = some (.alu .add (24 : Fin 32) x0 a3, 2) := by decide
theorem trc_at_346 : fetchRel trustedRootReadChainCode 0x346 = some (.alu .add (27 : Fin 32) x0 a2, 2) := by decide
theorem trc_at_348 : fetchRel trustedRootReadChainCode 0x348 = some (.aluImm .srl a0 (22 : Fin 32) 0x8, 4) := by decide
theorem trc_at_34c : fetchRel trustedRootReadChainCode 0x34C = some (.aluImm .srl a2 (22 : Fin 32) 0x10, 4) := by decide
theorem trc_at_350 : fetchRel trustedRootReadChainCode 0x350 = some (.aluImm .srl a3 (22 : Fin 32) 0x18, 4) := by decide
theorem trc_at_354 : fetchRel trustedRootReadChainCode 0x354 = some (.store .sw sp (20 : Fin 32) 0xE0, 2) := by decide
theorem trc_at_356 : fetchRel trustedRootReadChainCode 0x356 = some (.store .sb sp (22 : Fin 32) 0xE4, 4) := by decide
theorem trc_at_35a : fetchRel trustedRootReadChainCode 0x35A = some (.store .sb sp a0 0xE5, 4) := by decide
theorem trc_at_35e : fetchRel trustedRootReadChainCode 0x35E = some (.store .sb sp a2 0xE6, 4) := by decide
theorem trc_at_362 : fetchRel trustedRootReadChainCode 0x362 = some (.store .sb sp a3 0xE7, 4) := by decide
theorem trc_at_366 : fetchRel trustedRootReadChainCode 0x366 = some (.load .lw a0 sp 0x18, 2) := by decide
theorem trc_at_368 : fetchRel trustedRootReadChainCode 0x368 = some (.store .sw sp a0 0xE8, 2) := by decide
theorem trc_at_36a : fetchRel trustedRootReadChainCode 0x36A = some (.load .lw a0 sp 0x1C, 2) := by decide
theorem trc_at_36c : fetchRel trustedRootReadChainCode 0x36C = some (.store .sw sp a0 0xEC, 2) := by decide
theorem trc_at_36e : fetchRel trustedRootReadChainCode 0x36E = some (.load .lw a0 sp 0x10, 2) := by decide
theorem trc_at_370 : fetchRel trustedRootReadChainCode 0x370 = some (.store .sw sp a0 0xF0, 2) := by decide
theorem trc_at_372 : fetchRel trustedRootReadChainCode 0x372 = some (.load .lw a0 sp 0x30, 2) := by decide
theorem trc_at_374 : fetchRel trustedRootReadChainCode 0x374 = some (.load .lw a2 sp 0x14, 2) := by decide
theorem trc_at_376 : fetchRel trustedRootReadChainCode 0x376 = some (.store .sw sp a2 0xF4, 2) := by decide
theorem trc_at_378 : fetchRel trustedRootReadChainCode 0x378 = some (.store .sw sp (9 : Fin 32) 0xF8, 2) := by decide
theorem trc_at_37a : fetchRel trustedRootReadChainCode 0x37A = some (.store .sw sp (8 : Fin 32) 0xFC, 2) := by decide
theorem trc_at_37c : fetchRel trustedRootReadChainCode 0x37C = some (.aluImm .add a2 sp 0x100, 2) := by decide
theorem trc_at_37e : fetchRel trustedRootReadChainCode 0x37E = some (.store .sw a2 (23 : Fin 32) 0x0, 4) := by decide
theorem trc_at_382 : fetchRel trustedRootReadChainCode 0x382 = some (.store .sw a2 (18 : Fin 32) 0x4, 4) := by decide
theorem trc_at_386 : fetchRel trustedRootReadChainCode 0x386 = some (.store .sw a2 a1 0x8, 2) := by decide
theorem trc_at_388 : fetchRel trustedRootReadChainCode 0x388 = some (.store .sw a2 x0 0xC, 4) := by decide
theorem trc_at_38c : fetchRel trustedRootReadChainCode 0x38C = some (.aluImm .add a1 sp 0xE0, 2) := by decide
theorem trc_at_38e : fetchRel trustedRootReadChainCode 0x38E = some (.branch .beq a0 x0 0x4, 2) := by decide
theorem trc_at_390 : fetchRel trustedRootReadChainCode 0x390 = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem trc_at_392 : fetchRel trustedRootReadChainCode 0x392 = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem trc_at_394 : fetchRel trustedRootReadChainCode 0x394 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem trc_at_398 : fetchRel trustedRootReadChainCode 0x398 = some (.auipc ra 0xB000, 4) := by decide
theorem trc_at_39c : fetchRel trustedRootReadChainCode 0x39C = some (.jalr ra ra 0xFFFFFC80, 4) := by decide
theorem trc_at_3a0 : fetchRel trustedRootReadChainCode 0x3A0 = some (.aluImm .add a0 sp 0x30, 2) := by decide
theorem trc_at_3a2 : fetchRel trustedRootReadChainCode 0x3A2 = some (.aluImm .add a1 sp 0x60, 2) := by decide
theorem trc_at_3a4 : fetchRel trustedRootReadChainCode 0x3A4 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem trc_at_3a8 : fetchRel trustedRootReadChainCode 0x3A8 = some (.auipc ra 0xB000, 4) := by decide
theorem trc_at_3ac : fetchRel trustedRootReadChainCode 0x3AC = some (.jalr ra ra 0xFFFFFC70, 4) := by decide
theorem trc_at_3b0 : fetchRel trustedRootReadChainCode 0x3B0 = some (.load .lw (22 : Fin 32) sp 0x20, 2) := by decide
theorem trc_at_3b2 : fetchRel trustedRootReadChainCode 0x3B2 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem trc_at_3b4 : fetchRel trustedRootReadChainCode 0x3B4 = some (.aluImm .add (20 : Fin 32) sp 0xE5, 4) := by decide
theorem trc_at_3b8 : fetchRel trustedRootReadChainCode 0x3B8 = some (.aluImm .add (9 : Fin 32) sp 0xA5, 4) := by decide
theorem trc_at_3bc : fetchRel trustedRootReadChainCode 0x3BC = some (.aluImm .add (23 : Fin 32) sp 0xE5, 4) := by decide
theorem trc_at_3c0 : fetchRel trustedRootReadChainCode 0x3C0 = some (.lui (8 : Fin 32) (img% hi20 (u2MaxAddress + 0x8)), 4) := by decide
theorem trc_at_3c4 : fetchRel trustedRootReadChainCode 0x3C4 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) (img% lo12 (u2MaxAddress + 0x8)), 4) := by decide
theorem trc_at_3c8 : fetchRel trustedRootReadChainCode 0x3C8 = some (.branch .bne (22 : Fin 32) x0 0xFFFFFD32, 4) := by decide
theorem trc_at_3cc : fetchRel trustedRootReadChainCode 0x3CC = some (.jal x0 0x10C, 2) := by decide
theorem trc_at_3ce : fetchRel trustedRootReadChainCode 0x3CE = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_3d0 : fetchRel trustedRootReadChainCode 0x3D0 = some (.aluImm .add a1 sp 0x60, 2) := by decide
theorem trc_at_3d2 : fetchRel trustedRootReadChainCode 0x3D2 = some (.auipc ra 0x1000, 4) := by decide
theorem trc_at_3d6 : fetchRel trustedRootReadChainCode 0x3D6 = some (.jalr ra ra 0xFFFFF8D0, 4) := by decide
theorem trc_at_3da : fetchRel trustedRootReadChainCode 0x3DA = some (.load .lw a4 sp 0xE0, 2) := by decide
theorem trc_at_3dc : fetchRel trustedRootReadChainCode 0x3DC = some (.branch .beq a4 x0 0xFFFFFF2A, 2) := by decide
theorem trc_at_3de : fetchRel trustedRootReadChainCode 0x3DE = some (.store .sw sp (21 : Fin 32) 0xC, 2) := by decide
theorem trc_at_3e0 : fetchRel trustedRootReadChainCode 0x3E0 = some (.store .sw sp (19 : Fin 32) 0x8, 2) := by decide
theorem trc_at_3e2 : fetchRel trustedRootReadChainCode 0x3E2 = some (.load .lw a0 sp 0xE8, 2) := by decide
theorem trc_at_3e4 : fetchRel trustedRootReadChainCode 0x3E4 = some (.load .lw (21 : Fin 32) sp 0xE4, 2) := by decide
theorem trc_at_3e6 : fetchRel trustedRootReadChainCode 0x3E6 = some (.aluImm .add (19 : Fin 32) x0 0x1, 2) := by decide
theorem trc_at_3e8 : fetchRel trustedRootReadChainCode 0x3E8 = some (.branch .beq a0 x0 0x28, 2) := by decide
theorem trc_at_3ea : fetchRel trustedRootReadChainCode 0x3EA = some (.load .lbu a1 sp 0xF8, 4) := by decide
theorem trc_at_3ee : fetchRel trustedRootReadChainCode 0x3EE = some (.aluImm .add a2 x0 0x6, 2) := by decide
theorem trc_at_3f0 : fetchRel trustedRootReadChainCode 0x3F0 = some (.branch .bne a1 a2 0x20, 4) := by decide
theorem trc_at_3f4 : fetchRel trustedRootReadChainCode 0x3F4 = some (.load .lw a1 sp 0xEC, 2) := by decide
theorem trc_at_3f6 : fetchRel trustedRootReadChainCode 0x3F6 = some (.aluImm .add a3 x0 0x5, 2) := by decide
theorem trc_at_3f8 : fetchRel trustedRootReadChainCode 0x3F8 = some (.lui a2 (img% hi20 (b64AlphabetAddress + 0x40)), 4) := by decide
theorem trc_at_3fc : fetchRel trustedRootReadChainCode 0x3FC = some (.aluImm .add a2 a2 (img% lo12 (b64AlphabetAddress + 0x40)), 4) := by decide
theorem trc_at_400 : fetchRel trustedRootReadChainCode 0x400 = some (.alu .add (19 : Fin 32) x0 a4, 2) := by decide
theorem trc_at_402 : fetchRel trustedRootReadChainCode 0x402 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem trc_at_406 : fetchRel trustedRootReadChainCode 0x406 = some (.jalr ra ra 0xFFFFFC26, 4) := by decide
theorem trc_at_40a : fetchRel trustedRootReadChainCode 0x40A = some (.alu .add a4 x0 (19 : Fin 32), 2) := by decide
theorem trc_at_40c : fetchRel trustedRootReadChainCode 0x40C = some (.aluImm .xor (19 : Fin 32) a0 0x1, 4) := by decide
theorem trc_at_410 : fetchRel trustedRootReadChainCode 0x410 = some (.aluImm .add a3 x0 0x7, 2) := by decide
theorem trc_at_412 : fetchRel trustedRootReadChainCode 0x412 = some (.alu .add a0 x0 a4, 2) := by decide
theorem trc_at_414 : fetchRel trustedRootReadChainCode 0x414 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem trc_at_416 : fetchRel trustedRootReadChainCode 0x416 = some (.lui a2 (img% hi20 (svOidEcPublicKeyAddress)), 4) := by decide
theorem trc_at_41a : fetchRel trustedRootReadChainCode 0x41A = some (.aluImm .add a2 a2 (img% lo12 (svOidEcPublicKeyAddress)), 4) := by decide
theorem trc_at_41e : fetchRel trustedRootReadChainCode 0x41E = some (.auipc ra 0x0, 4) := by decide
theorem trc_at_422 : fetchRel trustedRootReadChainCode 0x422 = some (.jalr ra ra 0xFFFFF898, 4) := by decide
theorem trc_at_426 : fetchRel trustedRootReadChainCode 0x426 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem trc_at_428 : fetchRel trustedRootReadChainCode 0x428 = some (.branch .bne (19 : Fin 32) x0 0x52, 4) := by decide
theorem trc_at_42c : fetchRel trustedRootReadChainCode 0x42C = some (.load .lw (19 : Fin 32) sp 0x8, 2) := by decide
theorem trc_at_42e : fetchRel trustedRootReadChainCode 0x42E = some (.load .lw (21 : Fin 32) sp 0xC, 2) := by decide
theorem trc_at_430 : fetchRel trustedRootReadChainCode 0x430 = some (.branch .bne a0 x0 0xFFFFFED8, 4) := by decide
theorem trc_at_434 : fetchRel trustedRootReadChainCode 0x434 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_436 : fetchRel trustedRootReadChainCode 0x436 = some (.aluImm .add a1 sp 0x60, 2) := by decide
theorem trc_at_438 : fetchRel trustedRootReadChainCode 0x438 = some (.auipc ra 0x0, 4) := by decide
theorem trc_at_43c : fetchRel trustedRootReadChainCode 0x43C = some (.jalr ra ra 0x6E2, 4) := by decide
theorem trc_at_440 : fetchRel trustedRootReadChainCode 0x440 = some (.load .lw a2 sp 0xE0, 2) := by decide
theorem trc_at_442 : fetchRel trustedRootReadChainCode 0x442 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem trc_at_444 : fetchRel trustedRootReadChainCode 0x444 = some (.branch .beq a2 x0 0xFFFFFEC4, 4) := by decide
theorem trc_at_448 : fetchRel trustedRootReadChainCode 0x448 = some (.load .lw a0 sp 0xE4, 2) := by decide
theorem trc_at_44a : fetchRel trustedRootReadChainCode 0x44A = some (.aluImm .add a0 a0 0xFFFFFF9F, 4) := by decide
theorem trc_at_44e : fetchRel trustedRootReadChainCode 0x44E = some (.branch .bne a0 x0 0xFFFFFEBA, 4) := by decide
theorem trc_at_452 : fetchRel trustedRootReadChainCode 0x452 = some (.load .lw a0 sp 0x6C, 2) := by decide
theorem trc_at_454 : fetchRel trustedRootReadChainCode 0x454 = some (.branch .bne a0 x0 0xFFFFFEB4, 4) := by decide
theorem trc_at_458 : fetchRel trustedRootReadChainCode 0x458 = some (.load .lbu a0 a2 0x0, 4) := by decide
theorem trc_at_45c : fetchRel trustedRootReadChainCode 0x45C = some (.aluImm .add a1 x0 0x4, 2) := by decide
theorem trc_at_45e : fetchRel trustedRootReadChainCode 0x45E = some (.branch .bne a0 a1 0xFFFFFEA8, 4) := by decide
theorem trc_at_462 : fetchRel trustedRootReadChainCode 0x462 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_464 : fetchRel trustedRootReadChainCode 0x464 = some (.alu .add a1 x0 a2, 2) := by decide
theorem trc_at_466 : fetchRel trustedRootReadChainCode 0x466 = some (.store .sw sp a2 0x4, 2) := by decide
theorem trc_at_468 : fetchRel trustedRootReadChainCode 0x468 = some (.auipc ra 0xFFFF9000, 4) := by decide
theorem trc_at_46c : fetchRel trustedRootReadChainCode 0x46C = some (.jalr ra ra 0x2AC, 4) := by decide
theorem trc_at_470 : fetchRel trustedRootReadChainCode 0x470 = some (.load .lw a0 sp 0xE0, 2) := by decide
theorem trc_at_472 : fetchRel trustedRootReadChainCode 0x472 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem trc_at_474 : fetchRel trustedRootReadChainCode 0x474 = some (.load .lw a1 sp 0x4, 2) := by decide
theorem trc_at_476 : fetchRel trustedRootReadChainCode 0x476 = some (.alu .and a1 a1 a0, 2) := by decide
theorem trc_at_478 : fetchRel trustedRootReadChainCode 0x478 = some (.jal x0 0xFFFFFE90, 2) := by decide
theorem trc_at_47a : fetchRel trustedRootReadChainCode 0x47A = some (.load .lw (19 : Fin 32) sp 0x8, 2) := by decide
theorem trc_at_47c : fetchRel trustedRootReadChainCode 0x47C = some (.load .lw (21 : Fin 32) sp 0xC, 2) := by decide
theorem trc_at_47e : fetchRel trustedRootReadChainCode 0x47E = some (.jal x0 0xFFFFFE8A, 2) := by decide
theorem trc_at_480 : fetchRel trustedRootReadChainCode 0x480 = some (.load .lbu a0 sp 0x64, 4) := by decide
theorem trc_at_484 : fetchRel trustedRootReadChainCode 0x484 = some (.store .sw (26 : Fin 32) x0 0x0, 4) := by decide
theorem trc_at_488 : fetchRel trustedRootReadChainCode 0x488 = some (.store .sb (26 : Fin 32) a0 0x4, 4) := by decide
theorem trc_at_48c : fetchRel trustedRootReadChainCode 0x48C = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem trc_at_48e : fetchRel trustedRootReadChainCode 0x48E = some (.load .lw ra a0 0x7C, 4) := by decide
theorem trc_at_492 : fetchRel trustedRootReadChainCode 0x492 = some (.load .lw (8 : Fin 32) a0 0x78, 2) := by decide
theorem trc_at_494 : fetchRel trustedRootReadChainCode 0x494 = some (.load .lw (9 : Fin 32) a0 0x74, 2) := by decide
theorem trc_at_496 : fetchRel trustedRootReadChainCode 0x496 = some (.load .lw (18 : Fin 32) a0 0x70, 4) := by decide
theorem trc_at_49a : fetchRel trustedRootReadChainCode 0x49A = some (.load .lw (19 : Fin 32) a0 0x6C, 4) := by decide
theorem trc_at_49e : fetchRel trustedRootReadChainCode 0x49E = some (.load .lw (20 : Fin 32) a0 0x68, 4) := by decide
theorem trc_at_4a2 : fetchRel trustedRootReadChainCode 0x4A2 = some (.load .lw (21 : Fin 32) a0 0x64, 4) := by decide
theorem trc_at_4a6 : fetchRel trustedRootReadChainCode 0x4A6 = some (.load .lw (22 : Fin 32) a0 0x60, 4) := by decide
theorem trc_at_4aa : fetchRel trustedRootReadChainCode 0x4AA = some (.load .lw (23 : Fin 32) a0 0x5C, 4) := by decide
theorem trc_at_4ae : fetchRel trustedRootReadChainCode 0x4AE = some (.load .lw (24 : Fin 32) a0 0x58, 4) := by decide
theorem trc_at_4b2 : fetchRel trustedRootReadChainCode 0x4B2 = some (.load .lw (25 : Fin 32) a0 0x54, 4) := by decide
theorem trc_at_4b6 : fetchRel trustedRootReadChainCode 0x4B6 = some (.load .lw (26 : Fin 32) a0 0x50, 4) := by decide
theorem trc_at_4ba : fetchRel trustedRootReadChainCode 0x4BA = some (.load .lw (27 : Fin 32) a0 0x4C, 4) := by decide
theorem trc_at_4be : fetchRel trustedRootReadChainCode 0x4BE = some (.aluImm .add sp sp 0x180, 2) := by decide
theorem trc_at_4c0 : fetchRel trustedRootReadChainCode 0x4C0 = some (.jalr x0 ra 0x0, 2) := by decide
theorem trc_at_4c2 : fetchRel trustedRootReadChainCode 0x4C2 = some (.load .lbu a0 sp 0xD4, 4) := by decide
theorem trc_at_4c6 : fetchRel trustedRootReadChainCode 0x4C6 = some (.jal x0 0xFFFFFFBE, 2) := by decide
theorem trc_at_4c8 : fetchRel trustedRootReadChainCode 0x4C8 = some (.store .sw (26 : Fin 32) x0 0x0, 4) := by decide
theorem trc_at_4cc : fetchRel trustedRootReadChainCode 0x4CC = some (.store .sb (26 : Fin 32) (8 : Fin 32) 0x4, 4) := by decide
theorem trc_at_4d0 : fetchRel trustedRootReadChainCode 0x4D0 = some (.jal x0 0xFFFFFFBC, 2) := by decide
theorem trc_at_4d2 : fetchRel trustedRootReadChainCode 0x4D2 = some (.load .lbu (18 : Fin 32) sp 0xE4, 4) := by decide
theorem trc_at_4d6 : fetchRel trustedRootReadChainCode 0x4D6 = some (.jal x0 0x2E, 2) := by decide
theorem trc_at_4d8 : fetchRel trustedRootReadChainCode 0x4D8 = some (.aluImm .add a0 sp 0xE0, 2) := by decide
theorem trc_at_4da : fetchRel trustedRootReadChainCode 0x4DA = some (.aluImm .add a1 sp 0x24, 2) := by decide
theorem trc_at_4dc : fetchRel trustedRootReadChainCode 0x4DC = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem trc_at_4e0 : fetchRel trustedRootReadChainCode 0x4E0 = some (.jalr ra ra 0xFFFFF998, 4) := by decide
theorem trc_at_4e4 : fetchRel trustedRootReadChainCode 0x4E4 = some (.load .lbu a0 sp 0xE0, 4) := by decide
theorem trc_at_4e8 : fetchRel trustedRootReadChainCode 0x4E8 = some (.branch .bne a0 x0 0xFFFFFB80, 4) := by decide
theorem trc_at_4ec : fetchRel trustedRootReadChainCode 0x4EC = some (.load .lw a0 sp 0xE4, 2) := by decide
theorem trc_at_4ee : fetchRel trustedRootReadChainCode 0x4EE = some (.branch .beq a0 x0 0x20, 2) := by decide
theorem trc_at_4f0 : fetchRel trustedRootReadChainCode 0x4F0 = some (.aluImm .add a0 x0 0x21, 4) := by decide
theorem trc_at_4f4 : fetchRel trustedRootReadChainCode 0x4F4 = some (.jal x0 0xFFFFFF90, 2) := by decide
theorem trc_at_4f6 : fetchRel trustedRootReadChainCode 0x4F6 = some (.load .lbu (18 : Fin 32) sp 0xE1, 4) := by decide
theorem trc_at_4fa : fetchRel trustedRootReadChainCode 0x4FA = some (.jal x0 0xA, 2) := by decide
theorem trc_at_4fc : fetchRel trustedRootReadChainCode 0x4FC = some (.load .lbu a0 sp 0xE4, 4) := by decide
theorem trc_at_500 : fetchRel trustedRootReadChainCode 0x500 = some (.jal x0 0xFFFFFF84, 2) := by decide
theorem trc_at_502 : fetchRel trustedRootReadChainCode 0x502 = some (.aluImm .add (18 : Fin 32) x0 0x1, 2) := by decide
theorem trc_at_504 : fetchRel trustedRootReadChainCode 0x504 = some (.store .sw (26 : Fin 32) x0 0x0, 4) := by decide
theorem trc_at_508 : fetchRel trustedRootReadChainCode 0x508 = some (.store .sb (26 : Fin 32) (18 : Fin 32) 0x4, 4) := by decide
theorem trc_at_50c : fetchRel trustedRootReadChainCode 0x50C = some (.jal x0 0xFFFFFF80, 2) := by decide
theorem trc_at_50e : fetchRel trustedRootReadChainCode 0x50E = some (.load .lw (8 : Fin 32) sp 0x30, 2) := by decide
theorem trc_at_510 : fetchRel trustedRootReadChainCode 0x510 = some (.branch .beq (8 : Fin 32) x0 0xFFFFFFE0, 2) := by decide
theorem trc_at_512 : fetchRel trustedRootReadChainCode 0x512 = some (.load .lbu (9 : Fin 32) sp 0x34, 4) := by decide
theorem trc_at_516 : fetchRel trustedRootReadChainCode 0x516 = some (.aluImm .add a1 sp 0x35, 4) := by decide
theorem trc_at_51a : fetchRel trustedRootReadChainCode 0x51A = some (.aluImm .add a0 (26 : Fin 32) 0x5, 4) := by decide
theorem trc_at_51e : fetchRel trustedRootReadChainCode 0x51E = some (.aluImm .add a2 x0 0x2B, 4) := by decide
theorem trc_at_522 : fetchRel trustedRootReadChainCode 0x522 = some (.auipc ra 0xB000, 4) := by decide
theorem trc_at_526 : fetchRel trustedRootReadChainCode 0x526 = some (.jalr ra ra 0xFFFFFAF6, 4) := by decide
theorem trc_at_52a : fetchRel trustedRootReadChainCode 0x52A = some (.store .sw (26 : Fin 32) (8 : Fin 32) 0x0, 4) := by decide
theorem trc_at_52e : fetchRel trustedRootReadChainCode 0x52E = some (.store .sb (26 : Fin 32) (9 : Fin 32) 0x4, 4) := by decide
theorem trc_at_532 : fetchRel trustedRootReadChainCode 0x532 = some (.store .sw (26 : Fin 32) (19 : Fin 32) 0x30, 4) := by decide
theorem trc_at_536 : fetchRel trustedRootReadChainCode 0x536 = some (.store .sw (26 : Fin 32) (21 : Fin 32) 0x34, 4) := by decide
theorem trc_at_53a : fetchRel trustedRootReadChainCode 0x53A = some (.store .sw (26 : Fin 32) (27 : Fin 32) 0x38, 4) := by decide
theorem trc_at_53e : fetchRel trustedRootReadChainCode 0x53E = some (.store .sw (26 : Fin 32) (24 : Fin 32) 0x3C, 4) := by decide
theorem trc_at_542 : fetchRel trustedRootReadChainCode 0x542 = some (.jal x0 0xFFFFFF4A, 2) := by decide

end C3.RV32
