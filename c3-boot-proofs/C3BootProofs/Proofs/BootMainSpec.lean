import C3BootProofs.Proofs.BootMainContract
import C3BootProofs.Proofs.BootMainRecord
import C3BootProofs.Proofs.BootLevel

/-!
# `boot_main`'s code, layout, and assumptions

`boot_main` at 0x403b6df6 reads both copies of the boot-state record,
decides which slot to try, checks slots with its first closure, writes the
record with its second closure, and calls `boot`. This file holds the decode
lemmas and straight-line blocks of its code, the stack layout, and
`BmEnv`, what the proof of `boot_main` assumes of memory at its entry.

The frame: `boot_main` moves `sp` down 0x100 bytes for its register saves,
then 0xBD80 bytes more, to `F = top - 0xBE80`. From `F`:

* +0x10 and +0x30: the two 32-byte record copies that `flash::read` fills.
* +0x50: `Buffers` (0xB954 bytes), after the second copy's decoded state.
* `s4 = F + 0xB9A8`: the first copy's decoded state, and from
  `s4 + 0x128` the plan and then the `Accepted` passed to `boot`.
* `s4 + 0x248` and `s4 + 0x378`: the results of the two calls of the first
  closure.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

/-- `boot_main`'s entry. -/
abbrev BM : Word := BitVec.ofNat 32 bootMainAddress

set_option maxRecDepth 20000
theorem bm_at_0 : fetchRel bootMainCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF00, 2) := by decide
theorem bm_at_2 : fetchRel bootMainCode 0x2 = some (.store .sw sp ra 0xFC, 2) := by decide
theorem bm_at_4 : fetchRel bootMainCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xF8, 2) := by decide
theorem bm_at_6 : fetchRel bootMainCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xF4, 2) := by decide
theorem bm_at_8 : fetchRel bootMainCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xF0, 2) := by decide
theorem bm_at_a : fetchRel bootMainCode 0xA = some (.store .sw sp (19 : Fin 32) 0xEC, 2) := by decide
theorem bm_at_c : fetchRel bootMainCode 0xC = some (.store .sw sp (20 : Fin 32) 0xE8, 2) := by decide
theorem bm_at_e : fetchRel bootMainCode 0xE = some (.store .sw sp (21 : Fin 32) 0xE4, 2) := by decide
theorem bm_at_10 : fetchRel bootMainCode 0x10 = some (.store .sw sp (22 : Fin 32) 0xE0, 2) := by decide
theorem bm_at_12 : fetchRel bootMainCode 0x12 = some (.store .sw sp (23 : Fin 32) 0xDC, 2) := by decide
theorem bm_at_14 : fetchRel bootMainCode 0x14 = some (.store .sw sp (24 : Fin 32) 0xD8, 2) := by decide
theorem bm_at_16 : fetchRel bootMainCode 0x16 = some (.store .sw sp (25 : Fin 32) 0xD4, 2) := by decide
theorem bm_at_18 : fetchRel bootMainCode 0x18 = some (.store .sw sp (26 : Fin 32) 0xD0, 2) := by decide
theorem bm_at_1a : fetchRel bootMainCode 0x1A = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_1c : fetchRel bootMainCode 0x1C = some (.aluImm .add a0 a0 0xFFFFFD80, 4) := by decide
theorem bm_at_20 : fetchRel bootMainCode 0x20 = some (.alu .sub sp sp a0, 4) := by decide
theorem bm_at_24 : fetchRel bootMainCode 0x24 = some (.lui a0 0x3FCC6000, 4) := by decide
theorem bm_at_28 : fetchRel bootMainCode 0x28 = some (.aluImm .add a0 a0 0x706, 4) := by decide
theorem bm_at_2c : fetchRel bootMainCode 0x2C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bm_at_2e : fetchRel bootMainCode 0x2E = some (.auipc ra 0xFFC49000, 4) := by decide
theorem bm_at_32 : fetchRel bootMainCode 0x32 = some (.jalr ra ra 0x21C, 4) := by decide
theorem bm_at_36 : fetchRel bootMainCode 0x36 = some (.lui a0 0x3FCE0000, 4) := by decide
theorem bm_at_3a : fetchRel bootMainCode 0x3A = some (.load .lw a0 a0 0xFFFFFFF0, 4) := by decide
theorem bm_at_3e : fetchRel bootMainCode 0x3E = some (.lui a1 0x400000, 4) := by decide
theorem bm_at_42 : fetchRel bootMainCode 0x42 = some (.store .sw a0 a1 0x4, 2) := by decide
theorem bm_at_44 : fetchRel bootMainCode 0x44 = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem bm_at_46 : fetchRel bootMainCode 0x46 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bm_at_4a : fetchRel bootMainCode 0x4A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bm_at_4c : fetchRel bootMainCode 0x4C = some (.auipc ra 0x0, 4) := by decide
theorem bm_at_50 : fetchRel bootMainCode 0x50 = some (.jalr ra ra 0xFFFFF912, 4) := by decide
theorem bm_at_54 : fetchRel bootMainCode 0x54 = some (.aluImm .add a0 sp 0x30, 2) := by decide
theorem bm_at_56 : fetchRel bootMainCode 0x56 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bm_at_5a : fetchRel bootMainCode 0x5A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bm_at_5c : fetchRel bootMainCode 0x5C = some (.auipc ra 0x0, 4) := by decide
theorem bm_at_60 : fetchRel bootMainCode 0x60 = some (.jalr ra ra 0xFFFFF902, 4) := by decide
theorem bm_at_64 : fetchRel bootMainCode 0x64 = some (.lui a0 0x28000, 4) := by decide
theorem bm_at_68 : fetchRel bootMainCode 0x68 = some (.aluImm .add a1 sp 0x10, 2) := by decide
theorem bm_at_6a : fetchRel bootMainCode 0x6A = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bm_at_6e : fetchRel bootMainCode 0x6E = some (.auipc ra 0x0, 4) := by decide
theorem bm_at_72 : fetchRel bootMainCode 0x72 = some (.jalr ra ra 0xFFFFFE16, 4) := by decide
theorem bm_at_76 : fetchRel bootMainCode 0x76 = some (.branch .beq a0 x0 0x5C, 2) := by decide
theorem bm_at_78 : fetchRel bootMainCode 0x78 = some (.lui a0 0x29000, 4) := by decide
theorem bm_at_7c : fetchRel bootMainCode 0x7C = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem bm_at_7e : fetchRel bootMainCode 0x7E = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bm_at_82 : fetchRel bootMainCode 0x82 = some (.auipc ra 0x0, 4) := by decide
theorem bm_at_86 : fetchRel bootMainCode 0x86 = some (.jalr ra ra 0xFFFFFE02, 4) := by decide
theorem bm_at_8a : fetchRel bootMainCode 0x8A = some (.branch .beq a0 x0 0x48, 2) := by decide
theorem bm_at_8c : fetchRel bootMainCode 0x8C = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_8e : fetchRel bootMainCode 0x8E = some (.aluImm .add a0 a0 0xFFFFF9A8, 4) := by decide
theorem bm_at_92 : fetchRel bootMainCode 0x92 = some (.alu .add (20 : Fin 32) sp a0, 4) := by decide
theorem bm_at_96 : fetchRel bootMainCode 0x96 = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_98 : fetchRel bootMainCode 0x98 = some (.aluImm .add a0 a0 0xFFFFF9A8, 4) := by decide
theorem bm_at_9c : fetchRel bootMainCode 0x9C = some (.alu .add a0 a0 sp, 2) := by decide
theorem bm_at_9e : fetchRel bootMainCode 0x9E = some (.aluImm .add a1 sp 0x10, 2) := by decide
theorem bm_at_a0 : fetchRel bootMainCode 0xA0 = some (.auipc ra 0xFFFF8000, 4) := by decide
theorem bm_at_a4 : fetchRel bootMainCode 0xA4 = some (.jalr ra ra 0x132, 4) := by decide
theorem bm_at_a8 : fetchRel bootMainCode 0xA8 = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem bm_at_aa : fetchRel bootMainCode 0xAA = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem bm_at_ac : fetchRel bootMainCode 0xAC = some (.auipc ra 0xFFFF8000, 4) := by decide
theorem bm_at_b0 : fetchRel bootMainCode 0xB0 = some (.jalr ra ra 0x126, 4) := by decide
theorem bm_at_b4 : fetchRel bootMainCode 0xB4 = some (.load .lbu a1 (20 : Fin 32) 0x7, 4) := by decide
theorem bm_at_b8 : fetchRel bootMainCode 0xB8 = some (.load .lbu a0 sp 0x57, 4) := by decide
theorem bm_at_bc : fetchRel bootMainCode 0xBC = some (.aluImm .add (9 : Fin 32) x0 0x2, 2) := by decide
theorem bm_at_be : fetchRel bootMainCode 0xBE = some (.branch .bne a1 (9 : Fin 32) 0x20, 4) := by decide
theorem bm_at_c2 : fetchRel bootMainCode 0xC2 = some (.branch .bne a0 (9 : Fin 32) 0x2A, 4) := by decide
theorem bm_at_c6 : fetchRel bootMainCode 0xC6 = some (.aluImm .add (24 : Fin 32) x0 0x0, 2) := by decide
theorem bm_at_c8 : fetchRel bootMainCode 0xC8 = some (.aluImm .add (22 : Fin 32) x0 0x0, 2) := by decide
theorem bm_at_ca : fetchRel bootMainCode 0xCA = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem bm_at_cc : fetchRel bootMainCode 0xCC = some (.aluImm .add (21 : Fin 32) x0 0x0, 2) := by decide
theorem bm_at_ce : fetchRel bootMainCode 0xCE = some (.aluImm .add (18 : Fin 32) x0 0x2, 2) := by decide
theorem bm_at_d0 : fetchRel bootMainCode 0xD0 = some (.jal x0 0x46, 2) := by decide
theorem bm_at_d2 : fetchRel bootMainCode 0xD2 = some (.aluImm .add a0 x0 0xE4, 4) := by decide
theorem bm_at_d6 : fetchRel bootMainCode 0xD6 = some (.auipc ra 0x0, 4) := by decide
theorem bm_at_da : fetchRel bootMainCode 0xDA = some (.jalr ra ra 0xFFFFFD7A, 4) := by decide
theorem bm_at_de : fetchRel bootMainCode 0xDE = some (.branch .beq a0 (9 : Fin 32) 0x22, 4) := by decide
theorem bm_at_e2 : fetchRel bootMainCode 0xE2 = some (.load .lw a0 sp 0x50, 2) := by decide
theorem bm_at_e4 : fetchRel bootMainCode 0xE4 = some (.load .lw a1 (20 : Fin 32) 0x0, 4) := by decide
theorem bm_at_e8 : fetchRel bootMainCode 0xE8 = some (.branch .bgeu a1 a0 0x18, 4) := by decide
theorem bm_at_ec : fetchRel bootMainCode 0xEC = some (.load .lw (9 : Fin 32) sp 0x54, 2) := by decide
theorem bm_at_ee : fetchRel bootMainCode 0xEE = some (.load .lw (24 : Fin 32) sp 0x50, 2) := by decide
theorem bm_at_f0 : fetchRel bootMainCode 0xF0 = some (.aluImm .srl (22 : Fin 32) (9 : Fin 32) 0x8, 4) := by decide
theorem bm_at_f4 : fetchRel bootMainCode 0xF4 = some (.aluImm .srl (19 : Fin 32) (9 : Fin 32) 0x10, 4) := by decide
theorem bm_at_f8 : fetchRel bootMainCode 0xF8 = some (.aluImm .srl (21 : Fin 32) (9 : Fin 32) 0x18, 4) := by decide
theorem bm_at_fc : fetchRel bootMainCode 0xFC = some (.aluImm .add (18 : Fin 32) x0 0x1, 2) := by decide
theorem bm_at_fe : fetchRel bootMainCode 0xFE = some (.jal x0 0x18, 2) := by decide
theorem bm_at_100 : fetchRel bootMainCode 0x100 = some (.aluImm .add (18 : Fin 32) x0 0x0, 2) := by decide
theorem bm_at_102 : fetchRel bootMainCode 0x102 = some (.load .lw (9 : Fin 32) (20 : Fin 32) 0x4, 4) := by decide
theorem bm_at_106 : fetchRel bootMainCode 0x106 = some (.load .lw (24 : Fin 32) (20 : Fin 32) 0x0, 4) := by decide
theorem bm_at_10a : fetchRel bootMainCode 0x10A = some (.aluImm .srl (22 : Fin 32) (9 : Fin 32) 0x8, 4) := by decide
theorem bm_at_10e : fetchRel bootMainCode 0x10E = some (.aluImm .srl (19 : Fin 32) (9 : Fin 32) 0x10, 4) := by decide
theorem bm_at_112 : fetchRel bootMainCode 0x112 = some (.aluImm .srl (21 : Fin 32) (9 : Fin 32) 0x18, 4) := by decide
theorem bm_at_116 : fetchRel bootMainCode 0x116 = some (.lui a0 0x60009000, 4) := by decide
theorem bm_at_11a : fetchRel bootMainCode 0x11A = some (.load .lw a0 a0 0xFFFFF83C, 4) := by decide
theorem bm_at_11e : fetchRel bootMainCode 0x11E = some (.lui a1 0x5000, 2) := by decide
theorem bm_at_120 : fetchRel bootMainCode 0x120 = some (.aluImm .srl a2 a0 0xF, 4) := by decide
theorem bm_at_124 : fetchRel bootMainCode 0x124 = some (.aluImm .add a1 a1 0x555, 4) := by decide
theorem bm_at_128 : fetchRel bootMainCode 0x128 = some (.aluImm .srl a0 a0 0xE, 2) := by decide
theorem bm_at_12a : fetchRel bootMainCode 0x12A = some (.alu .and a1 a1 a2, 2) := by decide
theorem bm_at_12c : fetchRel bootMainCode 0x12C = some (.alu .sub a0 a0 a1, 2) := by decide
theorem bm_at_12e : fetchRel bootMainCode 0x12E = some (.lui a1 0x3000, 2) := by decide
theorem bm_at_130 : fetchRel bootMainCode 0x130 = some (.aluImm .add a1 a1 0x333, 4) := by decide
theorem bm_at_134 : fetchRel bootMainCode 0x134 = some (.aluImm .srl a2 a0 0x2, 4) := by decide
theorem bm_at_138 : fetchRel bootMainCode 0x138 = some (.alu .and a0 a0 a1, 2) := by decide
theorem bm_at_13a : fetchRel bootMainCode 0x13A = some (.alu .and a1 a1 a2, 2) := by decide
theorem bm_at_13c : fetchRel bootMainCode 0x13C = some (.alu .add a0 a0 a1, 2) := by decide
theorem bm_at_13e : fetchRel bootMainCode 0x13E = some (.aluImm .srl a1 a0 0x4, 4) := by decide
theorem bm_at_142 : fetchRel bootMainCode 0x142 = some (.alu .add a0 a0 a1, 2) := by decide
theorem bm_at_144 : fetchRel bootMainCode 0x144 = some (.aluImm .sll a1 a0 0x14, 4) := by decide
theorem bm_at_148 : fetchRel bootMainCode 0x148 = some (.aluImm .and a0 a0 0xF, 2) := by decide
theorem bm_at_14a : fetchRel bootMainCode 0x14A = some (.aluImm .srl a1 a1 0x1C, 2) := by decide
theorem bm_at_14c : fetchRel bootMainCode 0x14C = some (.alu .add (23 : Fin 32) a0 a1, 4) := by decide
theorem bm_at_150 : fetchRel bootMainCode 0x150 = some (.lui a0 0x3FCC6000, 4) := by decide
theorem bm_at_154 : fetchRel bootMainCode 0x154 = some (.aluImm .add a0 a0 0x719, 4) := by decide
theorem bm_at_158 : fetchRel bootMainCode 0x158 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem bm_at_15a : fetchRel bootMainCode 0x15A = some (.auipc ra 0xFFC49000, 4) := by decide
theorem bm_at_15e : fetchRel bootMainCode 0x15E = some (.jalr ra ra 0xF0, 4) := by decide
theorem bm_at_162 : fetchRel bootMainCode 0x162 = some (.lui a2 0xC000, 2) := by decide
theorem bm_at_164 : fetchRel bootMainCode 0x164 = some (.aluImm .add a2 a2 0xFFFFF954, 4) := by decide
theorem bm_at_168 : fetchRel bootMainCode 0x168 = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem bm_at_16a : fetchRel bootMainCode 0x16A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bm_at_16c : fetchRel bootMainCode 0x16C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem bm_at_170 : fetchRel bootMainCode 0x170 = some (.jalr ra ra 0x7F2, 4) := by decide
theorem bm_at_174 : fetchRel bootMainCode 0x174 = some (.aluImm .and a1 (9 : Fin 32) 0xFF, 4) := by decide
theorem bm_at_178 : fetchRel bootMainCode 0x178 = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem bm_at_17a : fetchRel bootMainCode 0x17A = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x1, 2) := by decide
theorem bm_at_17c : fetchRel bootMainCode 0x17C = some (.branch .bne a1 a0 0x16, 4) := by decide
theorem bm_at_180 : fetchRel bootMainCode 0x180 = some (.aluImm .add (25 : Fin 32) x0 0x0, 2) := by decide
theorem bm_at_182 : fetchRel bootMainCode 0x182 = some (.store .sb (20 : Fin 32) a0 0x12F, 4) := by decide
theorem bm_at_186 : fetchRel bootMainCode 0x186 = some (.store .sb (20 : Fin 32) (21 : Fin 32) 0x130, 4) := by decide
theorem bm_at_18a : fetchRel bootMainCode 0x18A = some (.store .sb (20 : Fin 32) x0 0x131, 4) := by decide
theorem bm_at_18e : fetchRel bootMainCode 0x18E = some (.alu .add (8 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem bm_at_190 : fetchRel bootMainCode 0x190 = some (.jal x0 0x64, 2) := by decide
theorem bm_at_192 : fetchRel bootMainCode 0x192 = some (.aluImm .and a0 (22 : Fin 32) 0xFF, 4) := by decide
theorem bm_at_196 : fetchRel bootMainCode 0x196 = some (.branch .bne a0 x0 0x4C, 2) := by decide
theorem bm_at_198 : fetchRel bootMainCode 0x198 = some (.aluImm .add (25 : Fin 32) x0 0x0, 2) := by decide
theorem bm_at_19a : fetchRel bootMainCode 0x19A = some (.alu .sltu a0 x0 (24 : Fin 32), 4) := by decide
theorem bm_at_19e : fetchRel bootMainCode 0x19E = some (.aluImm .and a1 (19 : Fin 32) 0xFF, 4) := by decide
theorem bm_at_1a2 : fetchRel bootMainCode 0x1A2 = some (.aluImm .sll a2 (21 : Fin 32) 0x18, 4) := by decide
theorem bm_at_1a6 : fetchRel bootMainCode 0x1A6 = some (.aluImm .sll a1 a1 0x10, 2) := by decide
theorem bm_at_1a8 : fetchRel bootMainCode 0x1A8 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem bm_at_1aa : fetchRel bootMainCode 0x1AA = some (.alu .or a1 a1 a2, 2) := by decide
theorem bm_at_1ac : fetchRel bootMainCode 0x1AC = some (.alu .or a0 a0 (24 : Fin 32), 4) := by decide
theorem bm_at_1b0 : fetchRel bootMainCode 0x1B0 = some (.aluImm .add a1 a1 0x2, 2) := by decide
theorem bm_at_1b2 : fetchRel bootMainCode 0x1B2 = some (.aluImm .add a2 x0 0x2, 2) := by decide
theorem bm_at_1b4 : fetchRel bootMainCode 0x1B4 = some (.store .sw (20 : Fin 32) a0 0x128, 4) := by decide
theorem bm_at_1b8 : fetchRel bootMainCode 0x1B8 = some (.store .sw (20 : Fin 32) a1 0x12C, 4) := by decide
theorem bm_at_1bc : fetchRel bootMainCode 0x1BC = some (.store .sb (20 : Fin 32) (21 : Fin 32) 0x130, 4) := by decide
theorem bm_at_1c0 : fetchRel bootMainCode 0x1C0 = some (.store .sb (20 : Fin 32) x0 0x131, 4) := by decide
theorem bm_at_1c4 : fetchRel bootMainCode 0x1C4 = some (.alu .add (8 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem bm_at_1c6 : fetchRel bootMainCode 0x1C6 = some (.branch .beq (21 : Fin 32) a2 0x2E, 4) := by decide
theorem bm_at_1ca : fetchRel bootMainCode 0x1CA = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_1cc : fetchRel bootMainCode 0x1CC = some (.aluImm .add a0 a0 0xFFFFFAD0, 4) := by decide
theorem bm_at_1d0 : fetchRel bootMainCode 0x1D0 = some (.alu .add a1 sp a0, 4) := by decide
theorem bm_at_1d4 : fetchRel bootMainCode 0x1D4 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem bm_at_1d6 : fetchRel bootMainCode 0x1D6 = some (.auipc ra 0xFFFEB000, 4) := by decide
theorem bm_at_1da : fetchRel bootMainCode 0x1DA = some (.jalr ra ra 0xFFFFFBDA, 4) := by decide
theorem bm_at_1de : fetchRel bootMainCode 0x1DE = some (.aluImm .add (25 : Fin 32) x0 0x0, 2) := by decide
theorem bm_at_1e0 : fetchRel bootMainCode 0x1E0 = some (.jal x0 0xFFFFFFAE, 2) := by decide
theorem bm_at_1e2 : fetchRel bootMainCode 0x1E2 = some (.aluImm .add (25 : Fin 32) x0 0x1, 2) := by decide
theorem bm_at_1e4 : fetchRel bootMainCode 0x1E4 = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem bm_at_1e6 : fetchRel bootMainCode 0x1E6 = some (.store .sb (20 : Fin 32) a0 0x12F, 4) := by decide
theorem bm_at_1ea : fetchRel bootMainCode 0x1EA = some (.store .sb (20 : Fin 32) (9 : Fin 32) 0x130, 4) := by decide
theorem bm_at_1ee : fetchRel bootMainCode 0x1EE = some (.store .sb (20 : Fin 32) (25 : Fin 32) 0x131, 4) := by decide
theorem bm_at_1f2 : fetchRel bootMainCode 0x1F2 = some (.alu .add (8 : Fin 32) x0 (9 : Fin 32), 2) := by decide
theorem bm_at_1f4 : fetchRel bootMainCode 0x1F4 = some (.aluImm .and a3 (8 : Fin 32) 0x1, 4) := by decide
theorem bm_at_1f8 : fetchRel bootMainCode 0x1F8 = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_1fa : fetchRel bootMainCode 0x1FA = some (.aluImm .add a0 a0 0xFFFFFBF0, 4) := by decide
theorem bm_at_1fe : fetchRel bootMainCode 0x1FE = some (.alu .add a0 a0 sp, 2) := by decide
theorem bm_at_200 : fetchRel bootMainCode 0x200 = some (.aluImm .add a2 sp 0x50, 2) := by decide
theorem bm_at_202 : fetchRel bootMainCode 0x202 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem bm_at_204 : fetchRel bootMainCode 0x204 = some (.auipc ra 0xFFFE9000, 4) := by decide
theorem bm_at_208 : fetchRel bootMainCode 0x208 = some (.jalr ra ra 0xAC, 4) := by decide
theorem bm_at_20c : fetchRel bootMainCode 0x20C = some (.load .lbu a0 (20 : Fin 32) 0x254, 4) := by decide
theorem bm_at_210 : fetchRel bootMainCode 0x210 = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem bm_at_214 : fetchRel bootMainCode 0x214 = some (.branch .bne a0 x0 0x68, 2) := by decide
theorem bm_at_216 : fetchRel bootMainCode 0x216 = some (.branch .beq (25 : Fin 32) x0 0x34, 4) := by decide
theorem bm_at_21a : fetchRel bootMainCode 0x21A = some (.alu .sltu a0 x0 (24 : Fin 32), 4) := by decide
theorem bm_at_21e : fetchRel bootMainCode 0x21E = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem bm_at_220 : fetchRel bootMainCode 0x220 = some (.alu .or a0 a0 (24 : Fin 32), 4) := by decide
theorem bm_at_224 : fetchRel bootMainCode 0x224 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem bm_at_226 : fetchRel bootMainCode 0x226 = some (.store .sw (20 : Fin 32) a0 0x0, 4) := by decide
theorem bm_at_22a : fetchRel bootMainCode 0x22A = some (.store .sb (20 : Fin 32) a1 0x4, 4) := by decide
theorem bm_at_22e : fetchRel bootMainCode 0x22E = some (.store .sb (20 : Fin 32) (19 : Fin 32) 0x6, 4) := by decide
theorem bm_at_232 : fetchRel bootMainCode 0x232 = some (.store .sb (20 : Fin 32) (21 : Fin 32) 0x7, 4) := by decide
theorem bm_at_236 : fetchRel bootMainCode 0x236 = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_238 : fetchRel bootMainCode 0x238 = some (.aluImm .add a0 a0 0xFFFFF9A8, 4) := by decide
theorem bm_at_23c : fetchRel bootMainCode 0x23C = some (.alu .add a1 sp a0, 4) := by decide
theorem bm_at_240 : fetchRel bootMainCode 0x240 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem bm_at_242 : fetchRel bootMainCode 0x242 = some (.auipc ra 0xFFFEB000, 4) := by decide
theorem bm_at_246 : fetchRel bootMainCode 0x246 = some (.jalr ra ra 0xFFFFFB6E, 4) := by decide
theorem bm_at_24a : fetchRel bootMainCode 0x24A = some (.aluImm .xor (9 : Fin 32) (8 : Fin 32) 0x1, 4) := by decide
theorem bm_at_24e : fetchRel bootMainCode 0x24E = some (.aluImm .and a3 (9 : Fin 32) 0x1, 4) := by decide
theorem bm_at_252 : fetchRel bootMainCode 0x252 = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_254 : fetchRel bootMainCode 0x254 = some (.aluImm .add a0 a0 0xFFFFFD20, 4) := by decide
theorem bm_at_258 : fetchRel bootMainCode 0x258 = some (.alu .add a0 a0 sp, 2) := by decide
theorem bm_at_25a : fetchRel bootMainCode 0x25A = some (.aluImm .add a2 sp 0x50, 2) := by decide
theorem bm_at_25c : fetchRel bootMainCode 0x25C = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem bm_at_25e : fetchRel bootMainCode 0x25E = some (.auipc ra 0xFFFE9000, 4) := by decide
theorem bm_at_262 : fetchRel bootMainCode 0x262 = some (.jalr ra ra 0x52, 4) := by decide
theorem bm_at_266 : fetchRel bootMainCode 0x266 = some (.load .lbu a0 (20 : Fin 32) 0x384, 4) := by decide
theorem bm_at_26a : fetchRel bootMainCode 0x26A = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem bm_at_26e : fetchRel bootMainCode 0x26E = some (.branch .bne a0 x0 0x96, 2) := by decide
theorem bm_at_270 : fetchRel bootMainCode 0x270 = some (.aluImm .add a0 x0 0xE5, 4) := by decide
theorem bm_at_274 : fetchRel bootMainCode 0x274 = some (.auipc ra 0x0, 4) := by decide
theorem bm_at_278 : fetchRel bootMainCode 0x278 = some (.jalr ra ra 0xFFFFFBDC, 4) := by decide
theorem bm_at_27c : fetchRel bootMainCode 0x27C = some (.load .lbu (26 : Fin 32) (20 : Fin 32) 0x370, 4) := by decide
theorem bm_at_280 : fetchRel bootMainCode 0x280 = some (.branch .beq (25 : Fin 32) x0 0x42, 4) := by decide
theorem bm_at_284 : fetchRel bootMainCode 0x284 = some (.aluImm .and a0 (22 : Fin 32) 0xFF, 4) := by decide
theorem bm_at_288 : fetchRel bootMainCode 0x288 = some (.alu .sltu a1 x0 (24 : Fin 32), 4) := by decide
theorem bm_at_28c : fetchRel bootMainCode 0x28C = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem bm_at_290 : fetchRel bootMainCode 0x290 = some (.alu .sub a0 (22 : Fin 32) a0, 4) := by decide
theorem bm_at_294 : fetchRel bootMainCode 0x294 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem bm_at_296 : fetchRel bootMainCode 0x296 = some (.alu .or a1 a1 (24 : Fin 32), 4) := by decide
theorem bm_at_29a : fetchRel bootMainCode 0x29A = some (.store .sb (20 : Fin 32) (21 : Fin 32) 0x7, 4) := by decide
theorem bm_at_29e : fetchRel bootMainCode 0x29E = some (.store .sw (20 : Fin 32) a1 0x0, 4) := by decide
theorem bm_at_2a2 : fetchRel bootMainCode 0x2A2 = some (.store .sb (20 : Fin 32) (9 : Fin 32) 0x4, 4) := by decide
theorem bm_at_2a6 : fetchRel bootMainCode 0x2A6 = some (.store .sb (20 : Fin 32) a0 0x5, 4) := by decide
theorem bm_at_2aa : fetchRel bootMainCode 0x2AA = some (.store .sb (20 : Fin 32) (19 : Fin 32) 0x6, 4) := by decide
theorem bm_at_2ae : fetchRel bootMainCode 0x2AE = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_2b0 : fetchRel bootMainCode 0x2B0 = some (.aluImm .add a0 a0 0xFFFFF9A8, 4) := by decide
theorem bm_at_2b4 : fetchRel bootMainCode 0x2B4 = some (.alu .add a1 sp a0, 4) := by decide
theorem bm_at_2b8 : fetchRel bootMainCode 0x2B8 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem bm_at_2ba : fetchRel bootMainCode 0x2BA = some (.auipc ra 0xFFFEB000, 4) := by decide
theorem bm_at_2be : fetchRel bootMainCode 0x2BE = some (.jalr ra ra 0xFFFFFAF6, 4) := by decide
theorem bm_at_2c2 : fetchRel bootMainCode 0x2C2 = some (.aluImm .add a0 (8 : Fin 32) 0x1, 4) := by decide
theorem bm_at_2c6 : fetchRel bootMainCode 0x2C6 = some (.alu .and a0 (19 : Fin 32) a0, 4) := by decide
theorem bm_at_2ca : fetchRel bootMainCode 0x2CA = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bm_at_2ce : fetchRel bootMainCode 0x2CE = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem bm_at_2d2 : fetchRel bootMainCode 0x2D2 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem bm_at_2d4 : fetchRel bootMainCode 0x2D4 = some (.alu .and a0 a0 (26 : Fin 32), 4) := by decide
theorem bm_at_2d8 : fetchRel bootMainCode 0x2D8 = some (.alu .add (19 : Fin 32) x0 (23 : Fin 32), 2) := by decide
theorem bm_at_2da : fetchRel bootMainCode 0x2DA = some (.branch .bltu a0 (23 : Fin 32) 0x6, 4) := by decide
theorem bm_at_2de : fetchRel bootMainCode 0x2DE = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem bm_at_2e0 : fetchRel bootMainCode 0x2E0 = some (.load .lw (18 : Fin 32) (20 : Fin 32) 0x368, 4) := by decide
theorem bm_at_2e4 : fetchRel bootMainCode 0x2E4 = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_2e6 : fetchRel bootMainCode 0x2E6 = some (.aluImm .add a0 a0 0xFFFFF9AD, 4) := by decide
theorem bm_at_2ea : fetchRel bootMainCode 0x2EA = some (.alu .add a0 a0 sp, 2) := by decide
theorem bm_at_2ec : fetchRel bootMainCode 0x2EC = some (.lui a1 0xC000, 2) := by decide
theorem bm_at_2ee : fetchRel bootMainCode 0x2EE = some (.aluImm .add a1 a1 0xFFFFFBF0, 4) := by decide
theorem bm_at_2f2 : fetchRel bootMainCode 0x2F2 = some (.alu .add a1 a1 sp, 2) := by decide
theorem bm_at_2f4 : fetchRel bootMainCode 0x2F4 = some (.aluImm .add a2 x0 0x120, 4) := by decide
theorem bm_at_2f8 : fetchRel bootMainCode 0x2F8 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem bm_at_2fc : fetchRel bootMainCode 0x2FC = some (.jalr ra ra 0x6CE, 4) := by decide
theorem bm_at_300 : fetchRel bootMainCode 0x300 = some (.alu .add (9 : Fin 32) x0 (8 : Fin 32), 2) := by decide
theorem bm_at_302 : fetchRel bootMainCode 0x302 = some (.jal x0 0x46, 2) := by decide
theorem bm_at_304 : fetchRel bootMainCode 0x304 = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem bm_at_306 : fetchRel bootMainCode 0x306 = some (.alu .sub a0 a0 (8 : Fin 32), 2) := by decide
theorem bm_at_308 : fetchRel bootMainCode 0x308 = some (.load .lbu a1 (20 : Fin 32) 0x4A0, 4) := by decide
theorem bm_at_30c : fetchRel bootMainCode 0x30C = some (.alu .and a0 (19 : Fin 32) a0, 4) := by decide
theorem bm_at_310 : fetchRel bootMainCode 0x310 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bm_at_314 : fetchRel bootMainCode 0x314 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem bm_at_318 : fetchRel bootMainCode 0x318 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem bm_at_31a : fetchRel bootMainCode 0x31A = some (.alu .and a0 a0 a1, 2) := by decide
theorem bm_at_31c : fetchRel bootMainCode 0x31C = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bm_at_320 : fetchRel bootMainCode 0x320 = some (.alu .add (19 : Fin 32) x0 (23 : Fin 32), 2) := by decide
theorem bm_at_322 : fetchRel bootMainCode 0x322 = some (.branch .bltu a0 (23 : Fin 32) 0x6, 4) := by decide
theorem bm_at_326 : fetchRel bootMainCode 0x326 = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem bm_at_328 : fetchRel bootMainCode 0x328 = some (.load .lw (18 : Fin 32) (20 : Fin 32) 0x498, 4) := by decide
theorem bm_at_32c : fetchRel bootMainCode 0x32C = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_32e : fetchRel bootMainCode 0x32E = some (.aluImm .add a0 a0 0xFFFFF9AD, 4) := by decide
theorem bm_at_332 : fetchRel bootMainCode 0x332 = some (.alu .add a0 a0 sp, 2) := by decide
theorem bm_at_334 : fetchRel bootMainCode 0x334 = some (.lui a1 0xC000, 2) := by decide
theorem bm_at_336 : fetchRel bootMainCode 0x336 = some (.aluImm .add a1 a1 0xFFFFFD20, 4) := by decide
theorem bm_at_33a : fetchRel bootMainCode 0x33A = some (.alu .add a1 a1 sp, 2) := by decide
theorem bm_at_33c : fetchRel bootMainCode 0x33C = some (.aluImm .add a2 x0 0x120, 4) := by decide
theorem bm_at_340 : fetchRel bootMainCode 0x340 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem bm_at_344 : fetchRel bootMainCode 0x344 = some (.jalr ra ra 0x686, 4) := by decide
theorem bm_at_348 : fetchRel bootMainCode 0x348 = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_34a : fetchRel bootMainCode 0x34A = some (.aluImm .add a0 a0 0xFFFFF9AD, 4) := by decide
theorem bm_at_34e : fetchRel bootMainCode 0x34E = some (.alu .add a1 sp a0, 4) := by decide
theorem bm_at_352 : fetchRel bootMainCode 0x352 = some (.lui a0 0xC000, 2) := by decide
theorem bm_at_354 : fetchRel bootMainCode 0x354 = some (.aluImm .add a0 a0 0xFFFFFAD0, 4) := by decide
theorem bm_at_358 : fetchRel bootMainCode 0x358 = some (.alu .add a0 a0 sp, 2) := by decide
theorem bm_at_35a : fetchRel bootMainCode 0x35A = some (.aluImm .add a2 x0 0x120, 4) := by decide
theorem bm_at_35e : fetchRel bootMainCode 0x35E = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem bm_at_362 : fetchRel bootMainCode 0x362 = some (.jalr ra ra 0x668, 4) := by decide
theorem bm_at_366 : fetchRel bootMainCode 0x366 = some (.aluImm .and a0 (9 : Fin 32) 0x1, 4) := by decide
theorem bm_at_36a : fetchRel bootMainCode 0x36A = some (.aluImm .and a3 (19 : Fin 32) 0xFF, 4) := by decide
theorem bm_at_36e : fetchRel bootMainCode 0x36E = some (.lui a1 0xC000, 2) := by decide
theorem bm_at_370 : fetchRel bootMainCode 0x370 = some (.aluImm .add a1 a1 0xFFFFFAD0, 4) := by decide
theorem bm_at_374 : fetchRel bootMainCode 0x374 = some (.alu .add a1 a1 sp, 2) := by decide
theorem bm_at_376 : fetchRel bootMainCode 0x376 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem bm_at_378 : fetchRel bootMainCode 0x378 = some (.alu .add a4 x0 (23 : Fin 32), 2) := by decide
theorem bm_at_37a : fetchRel bootMainCode 0x37A = some (.auipc ra 0x0, 4) := by decide
theorem bm_at_37e : fetchRel bootMainCode 0x37E = some (.jalr ra ra 0xFFFFF82E, 4) := by decide

def bmB0 : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFF00, .sw sp ra 0xFC, .sw sp (8 : Fin 32) 0xF8, .sw sp (9 : Fin 32) 0xF4, .sw sp (18 : Fin 32) 0xF0, .sw sp (19 : Fin 32) 0xEC, .sw sp (20 : Fin 32) 0xE8, .sw sp (21 : Fin 32) 0xE4, .sw sp (22 : Fin 32) 0xE0, .sw sp (23 : Fin 32) 0xDC, .sw sp (24 : Fin 32) 0xD8, .sw sp (25 : Fin 32) 0xD4, .sw sp (26 : Fin 32) 0xD0, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFFD80, .alu .sub sp sp a0, .lui a0 0x3FCC6000, .aluImm .add a0 a0 0x706, .aluImm .add a1 x0 0x0]

theorem bmB0_end : blockEnd bootMainCode 0x0 bmB0 = some 0x2E :=
  (blockEnd_cons' (off' := 0x2) bm_at_0 rfl (blockEnd_cons' (off' := 0x4) bm_at_2 rfl (blockEnd_cons' (off' := 0x6) bm_at_4 rfl (blockEnd_cons' (off' := 0x8) bm_at_6 rfl (blockEnd_cons' (off' := 0xA) bm_at_8 rfl (blockEnd_cons' (off' := 0xC) bm_at_a rfl (blockEnd_cons' (off' := 0xE) bm_at_c rfl (blockEnd_cons' (off' := 0x10) bm_at_e rfl (blockEnd_cons' (off' := 0x12) bm_at_10 rfl (blockEnd_cons' (off' := 0x14) bm_at_12 rfl (blockEnd_cons' (off' := 0x16) bm_at_14 rfl (blockEnd_cons' (off' := 0x18) bm_at_16 rfl (blockEnd_cons' (off' := 0x1A) bm_at_18 rfl (blockEnd_cons' (off' := 0x1C) bm_at_1a rfl (blockEnd_cons' (off' := 0x20) bm_at_1c rfl (blockEnd_cons' (off' := 0x24) bm_at_20 rfl (blockEnd_cons' (off' := 0x28) bm_at_24 rfl (blockEnd_cons' (off' := 0x2C) bm_at_28 rfl (blockEnd_cons' (off' := 0x2E) bm_at_2c rfl rfl)))))))))))))))))))

def bmB1 : List BInstr :=
  [.lui a0 0x3FCE0000, .lw a0 a0 0xFFFFFFF0, .lui a1 0x400000, .sw a0 a1 0x4, .aluImm .add a0 sp 0x10, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]

theorem bmB1_end : blockEnd bootMainCode 0x36 bmB1 = some 0x4C :=
  (blockEnd_cons' (off' := 0x3A) bm_at_36 rfl (blockEnd_cons' (off' := 0x3E) bm_at_3a rfl (blockEnd_cons' (off' := 0x42) bm_at_3e rfl (blockEnd_cons' (off' := 0x44) bm_at_42 rfl (blockEnd_cons' (off' := 0x46) bm_at_44 rfl (blockEnd_cons' (off' := 0x4A) bm_at_46 rfl (blockEnd_cons' (off' := 0x4C) bm_at_4a rfl rfl)))))))

def bmB2 : List BInstr :=
  [.aluImm .add a0 sp 0x30, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]

theorem bmB2_end : blockEnd bootMainCode 0x54 bmB2 = some 0x5C :=
  (blockEnd_cons' (off' := 0x56) bm_at_54 rfl (blockEnd_cons' (off' := 0x5A) bm_at_56 rfl (blockEnd_cons' (off' := 0x5C) bm_at_5a rfl rfl)))

def bmB3 : List BInstr :=
  [.lui a0 0x28000, .aluImm .add a1 sp 0x10, .aluImm .add a2 x0 0x20]

theorem bmB3_end : blockEnd bootMainCode 0x64 bmB3 = some 0x6E :=
  (blockEnd_cons' (off' := 0x68) bm_at_64 rfl (blockEnd_cons' (off' := 0x6A) bm_at_68 rfl (blockEnd_cons' (off' := 0x6E) bm_at_6a rfl rfl)))

def bmB4 : List BInstr :=
  [.lui a0 0x29000, .aluImm .add a1 sp 0x30, .aluImm .add a2 x0 0x20]

theorem bmB4_end : blockEnd bootMainCode 0x78 bmB4 = some 0x82 :=
  (blockEnd_cons' (off' := 0x7C) bm_at_78 rfl (blockEnd_cons' (off' := 0x7E) bm_at_7c rfl (blockEnd_cons' (off' := 0x82) bm_at_7e rfl rfl)))

def bmB5 : List BInstr :=
  [.lui a0 0xC000, .aluImm .add a0 a0 0xFFFFF9A8, .alu .add (20 : Fin 32) sp a0, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFF9A8, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x10]

theorem bmB5_end : blockEnd bootMainCode 0x8C bmB5 = some 0xA0 :=
  (blockEnd_cons' (off' := 0x8E) bm_at_8c rfl (blockEnd_cons' (off' := 0x92) bm_at_8e rfl (blockEnd_cons' (off' := 0x96) bm_at_92 rfl (blockEnd_cons' (off' := 0x98) bm_at_96 rfl (blockEnd_cons' (off' := 0x9C) bm_at_98 rfl (blockEnd_cons' (off' := 0x9E) bm_at_9c rfl (blockEnd_cons' (off' := 0xA0) bm_at_9e rfl rfl)))))))

def bmB6 : List BInstr :=
  [.aluImm .add a0 sp 0x50, .aluImm .add a1 sp 0x30]

theorem bmB6_end : blockEnd bootMainCode 0xA8 bmB6 = some 0xAC :=
  (blockEnd_cons' (off' := 0xAA) bm_at_a8 rfl (blockEnd_cons' (off' := 0xAC) bm_at_aa rfl rfl))

def bmB7 : List BInstr :=
  [.lbu a1 (20 : Fin 32) 0x7, .lbu a0 sp 0x57, .aluImm .add (9 : Fin 32) x0 0x2]

theorem bmB7_end : blockEnd bootMainCode 0xB4 bmB7 = some 0xBE :=
  (blockEnd_cons' (off' := 0xB8) bm_at_b4 rfl (blockEnd_cons' (off' := 0xBC) bm_at_b8 rfl (blockEnd_cons' (off' := 0xBE) bm_at_bc rfl rfl)))

def bmB8 : List BInstr :=
  [.aluImm .add (24 : Fin 32) x0 0x0, .aluImm .add (22 : Fin 32) x0 0x0, .aluImm .add (19 : Fin 32) x0 0x0, .aluImm .add (21 : Fin 32) x0 0x0, .aluImm .add (18 : Fin 32) x0 0x2]

theorem bmB8_end : blockEnd bootMainCode 0xC6 bmB8 = some 0xD0 :=
  (blockEnd_cons' (off' := 0xC8) bm_at_c6 rfl (blockEnd_cons' (off' := 0xCA) bm_at_c8 rfl (blockEnd_cons' (off' := 0xCC) bm_at_ca rfl (blockEnd_cons' (off' := 0xCE) bm_at_cc rfl (blockEnd_cons' (off' := 0xD0) bm_at_ce rfl rfl)))))

def bmB9 : List BInstr :=
  [.aluImm .add a0 x0 0xE4]

theorem bmB9_end : blockEnd bootMainCode 0xD2 bmB9 = some 0xD6 :=
  (blockEnd_cons' (off' := 0xD6) bm_at_d2 rfl rfl)

def bmB10 : List BInstr :=
  [.lw a0 sp 0x50, .lw a1 (20 : Fin 32) 0x0]

theorem bmB10_end : blockEnd bootMainCode 0xE2 bmB10 = some 0xE8 :=
  (blockEnd_cons' (off' := 0xE4) bm_at_e2 rfl (blockEnd_cons' (off' := 0xE8) bm_at_e4 rfl rfl))

def bmB11 : List BInstr :=
  [.lw (9 : Fin 32) sp 0x54, .lw (24 : Fin 32) sp 0x50, .aluImm .srl (22 : Fin 32) (9 : Fin 32) 0x8, .aluImm .srl (19 : Fin 32) (9 : Fin 32) 0x10, .aluImm .srl (21 : Fin 32) (9 : Fin 32) 0x18, .aluImm .add (18 : Fin 32) x0 0x1]

theorem bmB11_end : blockEnd bootMainCode 0xEC bmB11 = some 0xFE :=
  (blockEnd_cons' (off' := 0xEE) bm_at_ec rfl (blockEnd_cons' (off' := 0xF0) bm_at_ee rfl (blockEnd_cons' (off' := 0xF4) bm_at_f0 rfl (blockEnd_cons' (off' := 0xF8) bm_at_f4 rfl (blockEnd_cons' (off' := 0xFC) bm_at_f8 rfl (blockEnd_cons' (off' := 0xFE) bm_at_fc rfl rfl))))))

def bmB12 : List BInstr :=
  [.aluImm .add (18 : Fin 32) x0 0x0, .lw (9 : Fin 32) (20 : Fin 32) 0x4, .lw (24 : Fin 32) (20 : Fin 32) 0x0, .aluImm .srl (22 : Fin 32) (9 : Fin 32) 0x8, .aluImm .srl (19 : Fin 32) (9 : Fin 32) 0x10, .aluImm .srl (21 : Fin 32) (9 : Fin 32) 0x18]

theorem bmB12_end : blockEnd bootMainCode 0x100 bmB12 = some 0x116 :=
  (blockEnd_cons' (off' := 0x102) bm_at_100 rfl (blockEnd_cons' (off' := 0x106) bm_at_102 rfl (blockEnd_cons' (off' := 0x10A) bm_at_106 rfl (blockEnd_cons' (off' := 0x10E) bm_at_10a rfl (blockEnd_cons' (off' := 0x112) bm_at_10e rfl (blockEnd_cons' (off' := 0x116) bm_at_112 rfl rfl))))))

def bmB13 : List BInstr :=
  [.lui a0 0x60009000, .lw a0 a0 0xFFFFF83C, .lui a1 0x5000, .aluImm .srl a2 a0 0xF, .aluImm .add a1 a1 0x555, .aluImm .srl a0 a0 0xE, .alu .and a1 a1 a2, .alu .sub a0 a0 a1, .lui a1 0x3000, .aluImm .add a1 a1 0x333, .aluImm .srl a2 a0 0x2, .alu .and a0 a0 a1, .alu .and a1 a1 a2, .alu .add a0 a0 a1, .aluImm .srl a1 a0 0x4, .alu .add a0 a0 a1, .aluImm .sll a1 a0 0x14, .aluImm .and a0 a0 0xF, .aluImm .srl a1 a1 0x1C, .alu .add (23 : Fin 32) a0 a1, .lui a0 0x3FCC6000, .aluImm .add a0 a0 0x719, .alu .add a1 x0 (23 : Fin 32)]

theorem bmB13_end : blockEnd bootMainCode 0x116 bmB13 = some 0x15A :=
  (blockEnd_cons' (off' := 0x11A) bm_at_116 rfl (blockEnd_cons' (off' := 0x11E) bm_at_11a rfl (blockEnd_cons' (off' := 0x120) bm_at_11e rfl (blockEnd_cons' (off' := 0x124) bm_at_120 rfl (blockEnd_cons' (off' := 0x128) bm_at_124 rfl (blockEnd_cons' (off' := 0x12A) bm_at_128 rfl (blockEnd_cons' (off' := 0x12C) bm_at_12a rfl (blockEnd_cons' (off' := 0x12E) bm_at_12c rfl (blockEnd_cons' (off' := 0x130) bm_at_12e rfl (blockEnd_cons' (off' := 0x134) bm_at_130 rfl (blockEnd_cons' (off' := 0x138) bm_at_134 rfl (blockEnd_cons' (off' := 0x13A) bm_at_138 rfl (blockEnd_cons' (off' := 0x13C) bm_at_13a rfl (blockEnd_cons' (off' := 0x13E) bm_at_13c rfl (blockEnd_cons' (off' := 0x142) bm_at_13e rfl (blockEnd_cons' (off' := 0x144) bm_at_142 rfl (blockEnd_cons' (off' := 0x148) bm_at_144 rfl (blockEnd_cons' (off' := 0x14A) bm_at_148 rfl (blockEnd_cons' (off' := 0x14C) bm_at_14a rfl (blockEnd_cons' (off' := 0x150) bm_at_14c rfl (blockEnd_cons' (off' := 0x154) bm_at_150 rfl (blockEnd_cons' (off' := 0x158) bm_at_154 rfl (blockEnd_cons' (off' := 0x15A) bm_at_158 rfl rfl)))))))))))))))))))))))

def bmB14 : List BInstr :=
  [.lui a2 0xC000, .aluImm .add a2 a2 0xFFFFF954, .aluImm .add a0 sp 0x50, .aluImm .add a1 x0 0x0]

theorem bmB14_end : blockEnd bootMainCode 0x162 bmB14 = some 0x16C :=
  (blockEnd_cons' (off' := 0x164) bm_at_162 rfl (blockEnd_cons' (off' := 0x168) bm_at_164 rfl (blockEnd_cons' (off' := 0x16A) bm_at_168 rfl (blockEnd_cons' (off' := 0x16C) bm_at_16a rfl rfl))))

def bmB15 : List BInstr :=
  [.aluImm .and a1 (9 : Fin 32) 0xFF, .aluImm .add a0 x0 0x2, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x1]

theorem bmB15_end : blockEnd bootMainCode 0x174 bmB15 = some 0x17C :=
  (blockEnd_cons' (off' := 0x178) bm_at_174 rfl (blockEnd_cons' (off' := 0x17A) bm_at_178 rfl (blockEnd_cons' (off' := 0x17C) bm_at_17a rfl rfl)))

def bmB16 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x0, .sb (20 : Fin 32) a0 0x12F, .sb (20 : Fin 32) (21 : Fin 32) 0x130, .sb (20 : Fin 32) x0 0x131, .alu .add (8 : Fin 32) x0 (21 : Fin 32)]

theorem bmB16_end : blockEnd bootMainCode 0x180 bmB16 = some 0x190 :=
  (blockEnd_cons' (off' := 0x182) bm_at_180 rfl (blockEnd_cons' (off' := 0x186) bm_at_182 rfl (blockEnd_cons' (off' := 0x18A) bm_at_186 rfl (blockEnd_cons' (off' := 0x18E) bm_at_18a rfl (blockEnd_cons' (off' := 0x190) bm_at_18e rfl rfl)))))

def bmB17 : List BInstr :=
  [.aluImm .and a0 (22 : Fin 32) 0xFF]

theorem bmB17_end : blockEnd bootMainCode 0x192 bmB17 = some 0x196 :=
  (blockEnd_cons' (off' := 0x196) bm_at_192 rfl rfl)

def bmB18 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x0, .alu .sltu a0 x0 (24 : Fin 32), .aluImm .and a1 (19 : Fin 32) 0xFF, .aluImm .sll a2 (21 : Fin 32) 0x18, .aluImm .sll a1 a1 0x10, .aluImm .add a0 a0 0xFFFFFFFF, .alu .or a1 a1 a2, .alu .or a0 a0 (24 : Fin 32), .aluImm .add a1 a1 0x2, .aluImm .add a2 x0 0x2, .sw (20 : Fin 32) a0 0x128, .sw (20 : Fin 32) a1 0x12C, .sb (20 : Fin 32) (21 : Fin 32) 0x130, .sb (20 : Fin 32) x0 0x131, .alu .add (8 : Fin 32) x0 (21 : Fin 32)]

theorem bmB18_end : blockEnd bootMainCode 0x198 bmB18 = some 0x1C6 :=
  (blockEnd_cons' (off' := 0x19A) bm_at_198 rfl (blockEnd_cons' (off' := 0x19E) bm_at_19a rfl (blockEnd_cons' (off' := 0x1A2) bm_at_19e rfl (blockEnd_cons' (off' := 0x1A6) bm_at_1a2 rfl (blockEnd_cons' (off' := 0x1A8) bm_at_1a6 rfl (blockEnd_cons' (off' := 0x1AA) bm_at_1a8 rfl (blockEnd_cons' (off' := 0x1AC) bm_at_1aa rfl (blockEnd_cons' (off' := 0x1B0) bm_at_1ac rfl (blockEnd_cons' (off' := 0x1B2) bm_at_1b0 rfl (blockEnd_cons' (off' := 0x1B4) bm_at_1b2 rfl (blockEnd_cons' (off' := 0x1B8) bm_at_1b4 rfl (blockEnd_cons' (off' := 0x1BC) bm_at_1b8 rfl (blockEnd_cons' (off' := 0x1C0) bm_at_1bc rfl (blockEnd_cons' (off' := 0x1C4) bm_at_1c0 rfl (blockEnd_cons' (off' := 0x1C6) bm_at_1c4 rfl rfl)))))))))))))))

def bmB19 : List BInstr :=
  [.lui a0 0xC000, .aluImm .add a0 a0 0xFFFFFAD0, .alu .add a1 sp a0, .alu .add a0 x0 (18 : Fin 32)]

theorem bmB19_end : blockEnd bootMainCode 0x1CA bmB19 = some 0x1D6 :=
  (blockEnd_cons' (off' := 0x1CC) bm_at_1ca rfl (blockEnd_cons' (off' := 0x1D0) bm_at_1cc rfl (blockEnd_cons' (off' := 0x1D4) bm_at_1d0 rfl (blockEnd_cons' (off' := 0x1D6) bm_at_1d4 rfl rfl))))

def bmB19b : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x0]

theorem bmB19b_end : blockEnd bootMainCode 0x1DE bmB19b = some 0x1E0 :=
  (blockEnd_cons' (off' := 0x1E0) bm_at_1de rfl rfl)

def bmB19c : List BInstr :=
  [.alu .add (8 : Fin 32) x0 (21 : Fin 32)]

theorem bmB19c_end : blockEnd bootMainCode 0x18E bmB19c = some 0x190 :=
  (blockEnd_cons' (off' := 0x190) bm_at_18e rfl rfl)

def bmB20 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x1, .aluImm .add a0 x0 0x2, .sb (20 : Fin 32) a0 0x12F, .sb (20 : Fin 32) (9 : Fin 32) 0x130, .sb (20 : Fin 32) (25 : Fin 32) 0x131, .alu .add (8 : Fin 32) x0 (9 : Fin 32)]

theorem bmB20_end : blockEnd bootMainCode 0x1E2 bmB20 = some 0x1F4 :=
  (blockEnd_cons' (off' := 0x1E4) bm_at_1e2 rfl (blockEnd_cons' (off' := 0x1E6) bm_at_1e4 rfl (blockEnd_cons' (off' := 0x1EA) bm_at_1e6 rfl (blockEnd_cons' (off' := 0x1EE) bm_at_1ea rfl (blockEnd_cons' (off' := 0x1F2) bm_at_1ee rfl (blockEnd_cons' (off' := 0x1F4) bm_at_1f2 rfl rfl))))))

def bmB21 : List BInstr :=
  [.aluImm .and a3 (8 : Fin 32) 0x1, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFFBF0, .alu .add a0 a0 sp, .aluImm .add a2 sp 0x50, .alu .add a1 x0 (23 : Fin 32)]

theorem bmB21_end : blockEnd bootMainCode 0x1F4 bmB21 = some 0x204 :=
  (blockEnd_cons' (off' := 0x1F8) bm_at_1f4 rfl (blockEnd_cons' (off' := 0x1FA) bm_at_1f8 rfl (blockEnd_cons' (off' := 0x1FE) bm_at_1fa rfl (blockEnd_cons' (off' := 0x200) bm_at_1fe rfl (blockEnd_cons' (off' := 0x202) bm_at_200 rfl (blockEnd_cons' (off' := 0x204) bm_at_202 rfl rfl))))))

def bmB22 : List BInstr :=
  [.lbu a0 (20 : Fin 32) 0x254, .aluImm .add a0 a0 0xFFFFFF01]

theorem bmB22_end : blockEnd bootMainCode 0x20C bmB22 = some 0x214 :=
  (blockEnd_cons' (off' := 0x210) bm_at_20c rfl (blockEnd_cons' (off' := 0x214) bm_at_210 rfl rfl))

def bmB23 : List BInstr :=
  [.alu .sltu a0 x0 (24 : Fin 32), .aluImm .add a0 a0 0xFFFFFFFF, .alu .or a0 a0 (24 : Fin 32), .aluImm .add a1 x0 0x2, .sw (20 : Fin 32) a0 0x0, .sb (20 : Fin 32) a1 0x4, .sb (20 : Fin 32) (19 : Fin 32) 0x6, .sb (20 : Fin 32) (21 : Fin 32) 0x7, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFF9A8, .alu .add a1 sp a0, .alu .add a0 x0 (18 : Fin 32)]

theorem bmB23_end : blockEnd bootMainCode 0x21A bmB23 = some 0x242 :=
  (blockEnd_cons' (off' := 0x21E) bm_at_21a rfl (blockEnd_cons' (off' := 0x220) bm_at_21e rfl (blockEnd_cons' (off' := 0x224) bm_at_220 rfl (blockEnd_cons' (off' := 0x226) bm_at_224 rfl (blockEnd_cons' (off' := 0x22A) bm_at_226 rfl (blockEnd_cons' (off' := 0x22E) bm_at_22a rfl (blockEnd_cons' (off' := 0x232) bm_at_22e rfl (blockEnd_cons' (off' := 0x236) bm_at_232 rfl (blockEnd_cons' (off' := 0x238) bm_at_236 rfl (blockEnd_cons' (off' := 0x23C) bm_at_238 rfl (blockEnd_cons' (off' := 0x240) bm_at_23c rfl (blockEnd_cons' (off' := 0x242) bm_at_240 rfl rfl))))))))))))

def bmB24 : List BInstr :=
  [.aluImm .xor (9 : Fin 32) (8 : Fin 32) 0x1, .aluImm .and a3 (9 : Fin 32) 0x1, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFFD20, .alu .add a0 a0 sp, .aluImm .add a2 sp 0x50, .alu .add a1 x0 (23 : Fin 32)]

theorem bmB24_end : blockEnd bootMainCode 0x24A bmB24 = some 0x25E :=
  (blockEnd_cons' (off' := 0x24E) bm_at_24a rfl (blockEnd_cons' (off' := 0x252) bm_at_24e rfl (blockEnd_cons' (off' := 0x254) bm_at_252 rfl (blockEnd_cons' (off' := 0x258) bm_at_254 rfl (blockEnd_cons' (off' := 0x25A) bm_at_258 rfl (blockEnd_cons' (off' := 0x25C) bm_at_25a rfl (blockEnd_cons' (off' := 0x25E) bm_at_25c rfl rfl)))))))

def bmB25 : List BInstr :=
  [.lbu a0 (20 : Fin 32) 0x384, .aluImm .add a0 a0 0xFFFFFF01]

theorem bmB25_end : blockEnd bootMainCode 0x266 bmB25 = some 0x26E :=
  (blockEnd_cons' (off' := 0x26A) bm_at_266 rfl (blockEnd_cons' (off' := 0x26E) bm_at_26a rfl rfl))

def bmB26 : List BInstr :=
  [.aluImm .add a0 x0 0xE5]

theorem bmB26_end : blockEnd bootMainCode 0x270 bmB26 = some 0x274 :=
  (blockEnd_cons' (off' := 0x274) bm_at_270 rfl rfl)

def bmB27 : List BInstr :=
  [.lbu (26 : Fin 32) (20 : Fin 32) 0x370]

theorem bmB27_end : blockEnd bootMainCode 0x27C bmB27 = some 0x280 :=
  (blockEnd_cons' (off' := 0x280) bm_at_27c rfl rfl)

def bmB28 : List BInstr :=
  [.aluImm .and a0 (22 : Fin 32) 0xFF, .alu .sltu a1 x0 (24 : Fin 32), .alu .sltu a0 x0 a0, .alu .sub a0 (22 : Fin 32) a0, .aluImm .add a1 a1 0xFFFFFFFF, .alu .or a1 a1 (24 : Fin 32), .sb (20 : Fin 32) (21 : Fin 32) 0x7, .sw (20 : Fin 32) a1 0x0, .sb (20 : Fin 32) (9 : Fin 32) 0x4, .sb (20 : Fin 32) a0 0x5, .sb (20 : Fin 32) (19 : Fin 32) 0x6, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFF9A8, .alu .add a1 sp a0, .alu .add a0 x0 (18 : Fin 32)]

theorem bmB28_end : blockEnd bootMainCode 0x284 bmB28 = some 0x2BA :=
  (blockEnd_cons' (off' := 0x288) bm_at_284 rfl (blockEnd_cons' (off' := 0x28C) bm_at_288 rfl (blockEnd_cons' (off' := 0x290) bm_at_28c rfl (blockEnd_cons' (off' := 0x294) bm_at_290 rfl (blockEnd_cons' (off' := 0x296) bm_at_294 rfl (blockEnd_cons' (off' := 0x29A) bm_at_296 rfl (blockEnd_cons' (off' := 0x29E) bm_at_29a rfl (blockEnd_cons' (off' := 0x2A2) bm_at_29e rfl (blockEnd_cons' (off' := 0x2A6) bm_at_2a2 rfl (blockEnd_cons' (off' := 0x2AA) bm_at_2a6 rfl (blockEnd_cons' (off' := 0x2AE) bm_at_2aa rfl (blockEnd_cons' (off' := 0x2B0) bm_at_2ae rfl (blockEnd_cons' (off' := 0x2B4) bm_at_2b0 rfl (blockEnd_cons' (off' := 0x2B8) bm_at_2b4 rfl (blockEnd_cons' (off' := 0x2BA) bm_at_2b8 rfl rfl)))))))))))))))

def bmB29 : List BInstr :=
  [.aluImm .add a0 (8 : Fin 32) 0x1, .alu .and a0 (19 : Fin 32) a0, .aluImm .and a0 a0 0xFF, .aluImm .sltu a0 a0 0x1, .aluImm .add a0 a0 0xFFFFFFFF, .alu .and a0 a0 (26 : Fin 32), .alu .add (19 : Fin 32) x0 (23 : Fin 32)]

theorem bmB29_end : blockEnd bootMainCode 0x2C2 bmB29 = some 0x2DA :=
  (blockEnd_cons' (off' := 0x2C6) bm_at_2c2 rfl (blockEnd_cons' (off' := 0x2CA) bm_at_2c6 rfl (blockEnd_cons' (off' := 0x2CE) bm_at_2ca rfl (blockEnd_cons' (off' := 0x2D2) bm_at_2ce rfl (blockEnd_cons' (off' := 0x2D4) bm_at_2d2 rfl (blockEnd_cons' (off' := 0x2D8) bm_at_2d4 rfl (blockEnd_cons' (off' := 0x2DA) bm_at_2d8 rfl rfl)))))))

def bmB30 : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a0]

theorem bmB30_end : blockEnd bootMainCode 0x2DE bmB30 = some 0x2E0 :=
  (blockEnd_cons' (off' := 0x2E0) bm_at_2de rfl rfl)

def bmB31 : List BInstr :=
  [.lw (18 : Fin 32) (20 : Fin 32) 0x368, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFF9AD, .alu .add a0 a0 sp, .lui a1 0xC000, .aluImm .add a1 a1 0xFFFFFBF0, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x120]

theorem bmB31_end : blockEnd bootMainCode 0x2E0 bmB31 = some 0x2F8 :=
  (blockEnd_cons' (off' := 0x2E4) bm_at_2e0 rfl (blockEnd_cons' (off' := 0x2E6) bm_at_2e4 rfl (blockEnd_cons' (off' := 0x2EA) bm_at_2e6 rfl (blockEnd_cons' (off' := 0x2EC) bm_at_2ea rfl (blockEnd_cons' (off' := 0x2EE) bm_at_2ec rfl (blockEnd_cons' (off' := 0x2F2) bm_at_2ee rfl (blockEnd_cons' (off' := 0x2F4) bm_at_2f2 rfl (blockEnd_cons' (off' := 0x2F8) bm_at_2f4 rfl rfl))))))))

def bmB32 : List BInstr :=
  [.alu .add (9 : Fin 32) x0 (8 : Fin 32)]

theorem bmB32_end : blockEnd bootMainCode 0x300 bmB32 = some 0x302 :=
  (blockEnd_cons' (off' := 0x302) bm_at_300 rfl rfl)

def bmB33 : List BInstr :=
  [.aluImm .add a0 x0 0x2, .alu .sub a0 a0 (8 : Fin 32), .lbu a1 (20 : Fin 32) 0x4A0, .alu .and a0 (19 : Fin 32) a0, .aluImm .and a0 a0 0xFF, .aluImm .sltu a0 a0 0x1, .aluImm .add a0 a0 0xFFFFFFFF, .alu .and a0 a0 a1, .aluImm .and a0 a0 0xFF, .alu .add (19 : Fin 32) x0 (23 : Fin 32)]

theorem bmB33_end : blockEnd bootMainCode 0x304 bmB33 = some 0x322 :=
  (blockEnd_cons' (off' := 0x306) bm_at_304 rfl (blockEnd_cons' (off' := 0x308) bm_at_306 rfl (blockEnd_cons' (off' := 0x30C) bm_at_308 rfl (blockEnd_cons' (off' := 0x310) bm_at_30c rfl (blockEnd_cons' (off' := 0x314) bm_at_310 rfl (blockEnd_cons' (off' := 0x318) bm_at_314 rfl (blockEnd_cons' (off' := 0x31A) bm_at_318 rfl (blockEnd_cons' (off' := 0x31C) bm_at_31a rfl (blockEnd_cons' (off' := 0x320) bm_at_31c rfl (blockEnd_cons' (off' := 0x322) bm_at_320 rfl rfl))))))))))

def bmB34 : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a0]

theorem bmB34_end : blockEnd bootMainCode 0x326 bmB34 = some 0x328 :=
  (blockEnd_cons' (off' := 0x328) bm_at_326 rfl rfl)

def bmB35 : List BInstr :=
  [.lw (18 : Fin 32) (20 : Fin 32) 0x498, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFF9AD, .alu .add a0 a0 sp, .lui a1 0xC000, .aluImm .add a1 a1 0xFFFFFD20, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x120]

theorem bmB35_end : blockEnd bootMainCode 0x328 bmB35 = some 0x340 :=
  (blockEnd_cons' (off' := 0x32C) bm_at_328 rfl (blockEnd_cons' (off' := 0x32E) bm_at_32c rfl (blockEnd_cons' (off' := 0x332) bm_at_32e rfl (blockEnd_cons' (off' := 0x334) bm_at_332 rfl (blockEnd_cons' (off' := 0x336) bm_at_334 rfl (blockEnd_cons' (off' := 0x33A) bm_at_336 rfl (blockEnd_cons' (off' := 0x33C) bm_at_33a rfl (blockEnd_cons' (off' := 0x340) bm_at_33c rfl rfl))))))))

def bmB36 : List BInstr :=
  [.lui a0 0xC000, .aluImm .add a0 a0 0xFFFFF9AD, .alu .add a1 sp a0, .lui a0 0xC000, .aluImm .add a0 a0 0xFFFFFAD0, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x120]

theorem bmB36_end : blockEnd bootMainCode 0x348 bmB36 = some 0x35E :=
  (blockEnd_cons' (off' := 0x34A) bm_at_348 rfl (blockEnd_cons' (off' := 0x34E) bm_at_34a rfl (blockEnd_cons' (off' := 0x352) bm_at_34e rfl (blockEnd_cons' (off' := 0x354) bm_at_352 rfl (blockEnd_cons' (off' := 0x358) bm_at_354 rfl (blockEnd_cons' (off' := 0x35A) bm_at_358 rfl (blockEnd_cons' (off' := 0x35E) bm_at_35a rfl rfl)))))))

def bmB37 : List BInstr :=
  [.aluImm .and a0 (9 : Fin 32) 0x1, .aluImm .and a3 (19 : Fin 32) 0xFF, .lui a1 0xC000, .aluImm .add a1 a1 0xFFFFFAD0, .alu .add a1 a1 sp, .alu .add a2 x0 (18 : Fin 32), .alu .add a4 x0 (23 : Fin 32)]

theorem bmB37_end : blockEnd bootMainCode 0x366 bmB37 = some 0x37A :=
  (blockEnd_cons' (off' := 0x36A) bm_at_366 rfl (blockEnd_cons' (off' := 0x36E) bm_at_36a rfl (blockEnd_cons' (off' := 0x370) bm_at_36e rfl (blockEnd_cons' (off' := 0x374) bm_at_370 rfl (blockEnd_cons' (off' := 0x376) bm_at_374 rfl (blockEnd_cons' (off' := 0x378) bm_at_376 rfl (blockEnd_cons' (off' := 0x37A) bm_at_378 rfl rfl)))))))

/-! ## The stack and what `boot_main` assumes -/

/-- The stack that `boot_main` and its callees use below `top`: its own
0xBE80 bytes, then room for the deepest callee, which needs at most
`0x150 + R + romStack + stack0` bytes. -/
def bmK (R romStack stack0 : Nat) : Nat := 0xBE80 + 0x150 + R + romStack + stack0

/-- Where the ROM keeps its pointer to the flash chip's description, whose
size word `rom::set_flash_size` writes at +4. -/
abbrev bmPtr : Word := 0x3FCDFFF0

/-- `M` agrees with `M0` outside the `K` bytes of stack at `W` and the
word that `rom::set_flash_size` writes, at the ROM's pointer in `M0` plus 4. -/
def BmKeep (M0 M : Word → BitVec 8) (W : Word) (K : Nat) : Prop :=
  ∀ x, Sep W K x 1 → Sep (memLoad32 M0 bmPtr + 4) 4 x 1 → M x = M0 x

theorem BmKeep.refl (M0 : Word → BitVec 8) (W : Word) (K : Nat) : BmKeep M0 M0 W K := fun _ _ _ => rfl

theorem BmKeep.step {M0 M M' : Word → BitVec 8} {W : Word} {K : Nat} (h : BmKeep M0 M W K)
    (h' : ∀ x, Sep W K x 1 → M' x = M x) : BmKeep M0 M' W K :=
  fun x h1 h2 => (h' x h1).trans (h x h1 h2)

/-- What `boot_main`'s proof assumes of memory `M0` at its entry, with the
stack pointer at `top`: the code of `boot_main` and every function it
calls, with an `efuse_program_run` that meets the eFuse controller's
contract `EfuseCtl` (`eprAt_of_code` gives one from the pinned image's
code when the controller's registers are plain memory), the stack in data RAM above the image's read-only data, and the
ROM's flash-chip pointer word-aligned, apart from the read-only data, and
below the ROM. -/
structure BmEnv (M0 : Word → BitVec 8) (top : Word) (R romStack stack0 : Nat) (romBase : Word)
    (romCode : List Nat) : Prop where
  code : CodeIn M0 BM bootMainCode
  memset : CodeIn M0 (BitVec.ofNat 32 memsetAddress) memsetCode
  stub : CodeIn M0 (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  body : CodeIn M0 (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  frd : CodeIn M0 (img% flashReadAddress) flashReadCode
  rfw : CodeIn M0 (BitVec.ofNat 32 romFlashReadWordsAddress) romFlashReadWordsCode
  bs : BSCode M0
  bw : BWCode M0
  c0 : CodeIn M0 (BitVec.ofNat 32 bootMainClosure0Address) bootMainClosure0Code
  bt : CodeIn M0 BT bootFnCode
  epr : EprAt M0
  panic : PanicCode M0
  rom : CodeIn M0 romBase romCode
  hrb : 0x40000000 ≤ romBase.toNat
  hrl : romBase.toNat + romCode.length ≤ 0x60000000
  hsp : top.toNat % 16 = 0
  hlo : 0x3FCC8000 + bmK R romStack stack0 ≤ top.toNat
  hhi : top.toNat ≤ bmPtr.toNat
  hR : R % 4 = 0
  hrs : 16 ≤ romStack
  hrs4 : romStack % 4 = 0
  hpa : (memLoad32 M0 bmPtr).toNat % 4 = 0
  hpl : 0x3FCC8000 ≤ (memLoad32 M0 bmPtr).toNat + 4
  hph : (memLoad32 M0 bmPtr).toNat + 8 ≤ 0x40000000

/-- Outside the stack and the flash-chip word: below the read-only data's
end at 0x3FCC8000, or at or above 0x40000000. -/
theorem BmKeep.out {M0 M : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word}
    {romCode : List Nat} (C : BmEnv M0 top R romStack stack0 romBase romCode)
    (h : BmKeep M0 M (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0)) (x : Word)
    (hx : x.toNat < 0x3FCC8000 ∨ 0x40000000 ≤ x.toNat) : M x = M0 x := by
  have hlo := C.hlo; have hhi := C.hhi; have hpl := C.hpl; have hph := C.hph
  have hb : bmPtr.toNat = 0x3FCDFFF0 := rfl
  have hW : (top - BitVec.ofNat 32 (bmK R romStack stack0)).toNat = top.toNat - bmK R romStack stack0 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hP : (memLoad32 M0 bmPtr + 4).toNat = (memLoad32 M0 bmPtr).toNat + 4 := by
    rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; omega
  rcases hx with hx | hx
  · exact h x (sep_of_le (by omega) (by omega)).symm (sep_of_le (by omega) (by omega)).symm
  · exact h x (sep_of_le (by omega) (by have := x.isLt; omega)) (sep_of_le (by omega) (by have := x.isLt; omega))

theorem BmKeep.hiOf {M0 M : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word}
    {romCode : List Nat} (C : BmEnv M0 top R romStack stack0 romBase romCode)
    (h : BmKeep M0 M (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0)) :
    ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => h.out C x (.inr hx)

/-- `CodeIn` carries over to memory that keeps `M0`, for code below
0x3FCC8000 or at or above 0x40000000. -/
theorem BmKeep.codeIn {M0 M : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word}
    {romCode : List Nat} (C : BmEnv M0 top R romStack stack0 romBase romCode)
    (h : BmKeep M0 M (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {b : Word} {code : List Nat} (hc : CodeIn M0 b code)
    (hb : b.toNat + code.length ≤ 0x3FCC8000 ∨ (0x40000000 ≤ b.toNat ∧ b.toNat + code.length ≤ 2 ^ 32)) :
    CodeIn M b code := fun i hi => by
  have e : (b + BitVec.ofNat 32 i).toNat = b.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := b.isLt; omega
  rw [h.out C _ (by rw [e]; omega)]; exact hc i hi

/-! ## The boot-state records and the registers that hold the state -/

/-- The state and the copy that `bootstate::read` returns for the records
in flash at 0x28000 and 0x29000. -/
def bmRecs (flash : Nat → BitVec 8) : State × Option Slot :=
  readRecords (bmcFlash flash 0x28000 32) (bmcFlash flash 0x29000 32)

/-- A slot's number in the record and in `a3`: 0 for A and 1 for B. -/
def bmSlotNum : Slot → Nat
  | .a => 0
  | .b => 1

/-- The trial byte and the boots byte of a state, as `boot_main` keeps them:
2 and 0 when there is no trial. -/
def bmTrialBytes : Option Trial → Nat × Nat
  | none => (2, 0)
  | some t => (bmSlotNum t.slot, t.bootsLeft)

/-- The word at +4 of a decoded state: the trial byte, the boots byte, the
confirmed bits, and the preferred slot. -/
def bmWord (s : State) : Word :=
  BitVec.ofNat 32 ((bmTrialBytes s.trial).1 + 256 * (bmTrialBytes s.trial).2 + 65536 * s.confirmed +
    16777216 * bmSlotNum s.preferred)

/-- The copy `boot_main` passes to the second closure: 0 for A, 1 for B,
and 2 when neither copy decodes. -/
def bmCopy : Option Slot → Word
  | some .a => 0
  | some .b => 1
  | none => 2

/-! ## Calls -/

/-- A call from `boot_main` to a ROM routine, with the stack pointer at `S`. -/
theorem bm_romcall {romBase : Word} {romCode : List Nat} {romStack : Nat} (Fn : Word) {n : Machine}
    {g : Fin 32 → Word} {off : Nat} {imm o S : Word}
    (hF : RomFn romBase romCode Fn romStack fun _ => True) (s : St n.mem BM n off g) (hgs : g sp = S)
    (hc : CodeIn n.mem BM bootMainCode) (hr : CodeIn n.mem romBase romCode) (hS : romStack ≤ S.toNat)
    (h1 : fetchRel bootMainCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BM + BitVec.ofNat 32 off + imm + o = Fn) (he : Fn.toNat % 2 = 0)
    (he8 : (BM + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem BM n' (off + 8) (reg n') ∧
      (∀ x, Sep (S - BitVec.ofNat 32 romStack) romStack x 1 → n'.mem x = n.mem x) ∧
      ∀ q, romKeep q = true → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb he
  have sp1 : reg n1 sp = S := by rw [regs1, updz s.zero (by decide)]; exact hgs
  obtain ⟨n2, c2, pc2, keep2, mem2⟩ := hF n1 (by rw [mem1]; exact hr) pc1 trivial (by rw [sp1]; exact hS)
  refine ⟨n2, c1.trans c2, ⟨?_, rfl, fun _ => rfl⟩, fun x hx => by rw [mem2 x (by rw [sp1]; exact hx), mem1],
    fun q hq => ?_⟩
  · rw [pc2, regs1]; simp +decide only [upd, ite_true, ite_false]; exact even_clear _ he8
  · rw [keep2 q hq, regs1]; exact updz s.zero (by rintro rfl; exact absurd hq (by decide))

end C3.RV32.Cur
