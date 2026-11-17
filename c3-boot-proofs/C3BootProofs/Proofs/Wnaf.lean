import C3BootProofs.Proofs.IncrementLimb
import C3BootProofs.Proofs.Panic
import C3BootProofs.Proofs.Ashldi3
import C3BootProofs.Proofs.CtInto

/-!
# `wnaf::wnaf_form::<&[u8]>`, as compiled

The image has one copy of `wnaf_form`, with the window fixed at 5. It reads
the scalar's bytes through `LimbBuffer` as 64-bit limbs and writes the
window-5 NAF digits of the little-endian number they encode. The
specification, `wnafSpec`, is the Rust source's loop over that number.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem wf_at_0 : fetchRel wnafFormCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF90, 2) := by decide
theorem wf_at_2 : fetchRel wnafFormCode 0x2 = some (.store .sw sp ra 0x6C, 2) := by decide
theorem wf_at_4 : fetchRel wnafFormCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x68, 2) := by decide
theorem wf_at_6 : fetchRel wnafFormCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x64, 2) := by decide
theorem wf_at_8 : fetchRel wnafFormCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x60, 2) := by decide
theorem wf_at_a : fetchRel wnafFormCode 0xA = some (.store .sw sp (19 : Fin 32) 0x5C, 2) := by decide
theorem wf_at_c : fetchRel wnafFormCode 0xC = some (.store .sw sp (20 : Fin 32) 0x58, 2) := by decide
theorem wf_at_e : fetchRel wnafFormCode 0xE = some (.store .sw sp (21 : Fin 32) 0x54, 2) := by decide
theorem wf_at_10 : fetchRel wnafFormCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x50, 2) := by decide
theorem wf_at_12 : fetchRel wnafFormCode 0x12 = some (.store .sw sp (23 : Fin 32) 0x4C, 2) := by decide
theorem wf_at_14 : fetchRel wnafFormCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x48, 2) := by decide
theorem wf_at_16 : fetchRel wnafFormCode 0x16 = some (.store .sw sp (25 : Fin 32) 0x44, 2) := by decide
theorem wf_at_18 : fetchRel wnafFormCode 0x18 = some (.store .sw sp (26 : Fin 32) 0x40, 2) := by decide
theorem wf_at_1a : fetchRel wnafFormCode 0x1A = some (.store .sw sp (27 : Fin 32) 0x3C, 2) := by decide
theorem wf_at_1c : fetchRel wnafFormCode 0x1C = some (.alu .add (18 : Fin 32) x0 a4, 2) := by decide
theorem wf_at_1e : fetchRel wnafFormCode 0x1E = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem wf_at_20 : fetchRel wnafFormCode 0x20 = some (.alu .add (25 : Fin 32) x0 a0, 2) := by decide
theorem wf_at_22 : fetchRel wnafFormCode 0x22 = some (.store .sw sp a2 0x10, 2) := by decide
theorem wf_at_24 : fetchRel wnafFormCode 0x24 = some (.store .sw sp a3 0x14, 2) := by decide
theorem wf_at_26 : fetchRel wnafFormCode 0x26 = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem wf_at_28 : fetchRel wnafFormCode 0x28 = some (.aluImm .add a2 x0 0x14, 2) := by decide
theorem wf_at_2a : fetchRel wnafFormCode 0x2A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem wf_at_2c : fetchRel wnafFormCode 0x2C = some (.auipc ra 0x12000, 4) := by decide
theorem wf_at_30 : fetchRel wnafFormCode 0x30 = some (.jalr ra ra 0xFFFFFE76, 4) := by decide
theorem wf_at_34 : fetchRel wnafFormCode 0x34 = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem wf_at_36 : fetchRel wnafFormCode 0x36 = some (.auipc ra 0x12000, 4) := by decide
theorem wf_at_3a : fetchRel wnafFormCode 0x3A = some (.jalr ra ra 0xFFFFFDAC, 4) := by decide
theorem wf_at_3e : fetchRel wnafFormCode 0x3E = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem wf_at_40 : fetchRel wnafFormCode 0x40 = some (.auipc ra 0x12000, 4) := by decide
theorem wf_at_44 : fetchRel wnafFormCode 0x44 = some (.jalr ra ra 0xFFFFFDA2, 4) := by decide
theorem wf_at_48 : fetchRel wnafFormCode 0x48 = some (.aluImm .add (26 : Fin 32) x0 0x0, 2) := by decide
theorem wf_at_4a : fetchRel wnafFormCode 0x4A = some (.store .sw sp x0 0xC, 2) := by decide
theorem wf_at_4c : fetchRel wnafFormCode 0x4C = some (.aluImm .add (23 : Fin 32) x0 0x0, 2) := by decide
theorem wf_at_4e : fetchRel wnafFormCode 0x4E = some (.aluImm .add (21 : Fin 32) x0 0x0, 2) := by decide
theorem wf_at_50 : fetchRel wnafFormCode 0x50 = some (.store .sw sp x0 0x28, 2) := by decide
theorem wf_at_52 : fetchRel wnafFormCode 0x52 = some (.aluImm .add (24 : Fin 32) x0 0x3B, 4) := by decide
theorem wf_at_56 : fetchRel wnafFormCode 0x56 = some (.alu .add (22 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem wf_at_58 : fetchRel wnafFormCode 0x58 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x1, 2) := by decide
theorem wf_at_5a : fetchRel wnafFormCode 0x5A = some (.alu .sub (27 : Fin 32) (18 : Fin 32) (23 : Fin 32), 4) := by decide
theorem wf_at_5e : fetchRel wnafFormCode 0x5E = some (.alu .add (20 : Fin 32) (25 : Fin 32) (22 : Fin 32), 4) := by decide
theorem wf_at_62 : fetchRel wnafFormCode 0x62 = some (.branch .bgeu (23 : Fin 32) (18 : Fin 32) 0x108, 4) := by decide
theorem wf_at_66 : fetchRel wnafFormCode 0x66 = some (.load .lw a0 sp 0x28, 2) := by decide
theorem wf_at_68 : fetchRel wnafFormCode 0x68 = some (.aluImm .srl a1 (23 : Fin 32) 0x6, 4) := by decide
theorem wf_at_6c : fetchRel wnafFormCode 0x6C = some (.aluImm .and (9 : Fin 32) (23 : Fin 32) 0x3F, 4) := by decide
theorem wf_at_70 : fetchRel wnafFormCode 0x70 = some (.aluImm .add a2 a0 0x1, 4) := by decide
theorem wf_at_74 : fetchRel wnafFormCode 0x74 = some (.store .sw sp a0 0x34, 2) := by decide
theorem wf_at_76 : fetchRel wnafFormCode 0x76 = some (.store .sw sp a2 0x38, 2) := by decide
theorem wf_at_78 : fetchRel wnafFormCode 0x78 = some (.aluImm .add a2 sp 0x34, 2) := by decide
theorem wf_at_7a : fetchRel wnafFormCode 0x7A = some (.aluImm .add a3 x0 0x8, 2) := by decide
theorem wf_at_7c : fetchRel wnafFormCode 0x7C = some (.branch .beq a3 x0 0x122, 4) := by decide
theorem wf_at_80 : fetchRel wnafFormCode 0x80 = some (.load .lw a4 a2 0x0, 2) := by decide
theorem wf_at_82 : fetchRel wnafFormCode 0x82 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem wf_at_84 : fetchRel wnafFormCode 0x84 = some (.aluImm .add a3 a3 0xFFFFFFFC, 2) := by decide
theorem wf_at_86 : fetchRel wnafFormCode 0x86 = some (.branch .bne a4 a1 0xFFFFFFF6, 4) := by decide
theorem wf_at_8a : fetchRel wnafFormCode 0x8A = some (.branch .bgeu a0 a1 0xE, 4) := by decide
theorem wf_at_8e : fetchRel wnafFormCode 0x8E = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem wf_at_90 : fetchRel wnafFormCode 0x90 = some (.auipc ra 0x12000, 4) := by decide
theorem wf_at_94 : fetchRel wnafFormCode 0x94 = some (.jalr ra ra 0xFFFFFD52, 4) := by decide
theorem wf_at_98 : fetchRel wnafFormCode 0x98 = some (.load .lw a0 sp 0x18, 2) := by decide
theorem wf_at_9a : fetchRel wnafFormCode 0x9A = some (.load .lw a1 sp 0x1C, 2) := by decide
theorem wf_at_9c : fetchRel wnafFormCode 0x9C = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem wf_at_9e : fetchRel wnafFormCode 0x9E = some (.auipc ra 0x12000, 4) := by decide
theorem wf_at_a2 : fetchRel wnafFormCode 0xA2 = some (.jalr ra ra 0x1E, 4) := by decide
theorem wf_at_a6 : fetchRel wnafFormCode 0xA6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem wf_at_a8 : fetchRel wnafFormCode 0xA8 = some (.branch .bltu (9 : Fin 32) (24 : Fin 32) 0x1A, 4) := by decide
theorem wf_at_ac : fetchRel wnafFormCode 0xAC = some (.load .lw a0 sp 0x20, 2) := by decide
theorem wf_at_ae : fetchRel wnafFormCode 0xAE = some (.load .lw a1 sp 0x24, 2) := by decide
theorem wf_at_b0 : fetchRel wnafFormCode 0xB0 = some (.alu .sub a2 x0 (23 : Fin 32), 4) := by decide
theorem wf_at_b4 : fetchRel wnafFormCode 0xB4 = some (.aluImm .and a2 a2 0x3F, 4) := by decide
theorem wf_at_b8 : fetchRel wnafFormCode 0xB8 = some (.auipc ra 0x12000, 4) := by decide
theorem wf_at_bc : fetchRel wnafFormCode 0xBC = some (.jalr ra ra 0xFFFFFFE0, 4) := by decide
theorem wf_at_c0 : fetchRel wnafFormCode 0xC0 = some (.alu .or (8 : Fin 32) (8 : Fin 32) a0, 2) := by decide
theorem wf_at_c2 : fetchRel wnafFormCode 0xC2 = some (.aluImm .and (8 : Fin 32) (8 : Fin 32) 0x1F, 2) := by decide
theorem wf_at_c4 : fetchRel wnafFormCode 0xC4 = some (.alu .add a0 (8 : Fin 32) (26 : Fin 32), 4) := by decide
theorem wf_at_c8 : fetchRel wnafFormCode 0xC8 = some (.aluImm .and a1 a0 0x1, 4) := by decide
theorem wf_at_cc : fetchRel wnafFormCode 0xCC = some (.branch .bne a1 x0 0x14, 2) := by decide
theorem wf_at_ce : fetchRel wnafFormCode 0xCE = some (.branch .bgeu (22 : Fin 32) (19 : Fin 32) 0xD8, 4) := by decide
theorem wf_at_d2 : fetchRel wnafFormCode 0xD2 = some (.store .sb (20 : Fin 32) x0 0x0, 4) := by decide
theorem wf_at_d6 : fetchRel wnafFormCode 0xD6 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x1, 2) := by decide
theorem wf_at_d8 : fetchRel wnafFormCode 0xD8 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x1, 2) := by decide
theorem wf_at_da : fetchRel wnafFormCode 0xDA = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x1, 2) := by decide
theorem wf_at_dc : fetchRel wnafFormCode 0xDC = some (.aluImm .add (27 : Fin 32) (27 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem wf_at_de : fetchRel wnafFormCode 0xDE = some (.jal x0 0xFFFFFF80, 2) := by decide
theorem wf_at_e0 : fetchRel wnafFormCode 0xE0 = some (.branch .bgeu (22 : Fin 32) (19 : Fin 32) 0xC6, 4) := by decide
theorem wf_at_e4 : fetchRel wnafFormCode 0xE4 = some (.alu .sltu a1 a0 (8 : Fin 32), 4) := by decide
theorem wf_at_e8 : fetchRel wnafFormCode 0xE8 = some (.load .lw a2 sp 0xC, 2) := by decide
theorem wf_at_ea : fetchRel wnafFormCode 0xEA = some (.alu .add a1 a1 a2, 2) := by decide
theorem wf_at_ec : fetchRel wnafFormCode 0xEC = some (.aluImm .sltu a2 a0 0x10, 4) := by decide
theorem wf_at_f0 : fetchRel wnafFormCode 0xF0 = some (.aluImm .xor a2 a2 0x1, 4) := by decide
theorem wf_at_f4 : fetchRel wnafFormCode 0xF4 = some (.alu .sltu a1 x0 a1, 4) := by decide
theorem wf_at_f8 : fetchRel wnafFormCode 0xF8 = some (.alu .or (26 : Fin 32) a2 a1, 4) := by decide
theorem wf_at_fc : fetchRel wnafFormCode 0xFC = some (.alu .sub a1 x0 (26 : Fin 32), 4) := by decide
theorem wf_at_100 : fetchRel wnafFormCode 0x100 = some (.aluImm .and a1 a1 0xE0, 4) := by decide
theorem wf_at_104 : fetchRel wnafFormCode 0x104 = some (.alu .add a0 a0 a1, 2) := by decide
theorem wf_at_106 : fetchRel wnafFormCode 0x106 = some (.store .sb (20 : Fin 32) a0 0x0, 4) := by decide
theorem wf_at_10a : fetchRel wnafFormCode 0x10A = some (.store .sb sp x0 0x34, 4) := by decide
theorem wf_at_10e : fetchRel wnafFormCode 0x10E = some (.store .sw sp (26 : Fin 32) 0x38, 2) := by decide
theorem wf_at_110 : fetchRel wnafFormCode 0x110 = some (.aluImm .add a0 sp 0x34, 2) := by decide
theorem wf_at_112 : fetchRel wnafFormCode 0x112 = some (.auipc ra 0x0, 4) := by decide
theorem wf_at_116 : fetchRel wnafFormCode 0x116 = some (.jalr ra ra 0xA4, 4) := by decide
theorem wf_at_11a : fetchRel wnafFormCode 0x11A = some (.aluImm .add a2 x0 0x5, 2) := by decide
theorem wf_at_11c : fetchRel wnafFormCode 0x11C = some (.alu .sub a1 (18 : Fin 32) a0, 4) := by decide
theorem wf_at_120 : fetchRel wnafFormCode 0x120 = some (.alu .sltu a3 (18 : Fin 32) a1, 4) := by decide
theorem wf_at_124 : fetchRel wnafFormCode 0x124 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem wf_at_126 : fetchRel wnafFormCode 0x126 = some (.alu .and a1 a1 a3, 2) := by decide
theorem wf_at_128 : fetchRel wnafFormCode 0x128 = some (.alu .sub a1 a1 (23 : Fin 32), 4) := by decide
theorem wf_at_12c : fetchRel wnafFormCode 0x12C = some (.branch .bltu a1 a2 0x6, 4) := by decide
theorem wf_at_130 : fetchRel wnafFormCode 0x130 = some (.aluImm .add a1 x0 0x5, 2) := by decide
theorem wf_at_132 : fetchRel wnafFormCode 0x132 = some (.branch .bltu a0 (18 : Fin 32) 0x6, 4) := by decide
theorem wf_at_136 : fetchRel wnafFormCode 0x136 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem wf_at_138 : fetchRel wnafFormCode 0x138 = some (.alu .sub a0 (27 : Fin 32) a0, 4) := by decide
theorem wf_at_13c : fetchRel wnafFormCode 0x13C = some (.branch .bltu a0 a2 0x6, 4) := by decide
theorem wf_at_140 : fetchRel wnafFormCode 0x140 = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem wf_at_142 : fetchRel wnafFormCode 0x142 = some (.aluImm .sltu a2 a0 0x2, 4) := by decide
theorem wf_at_146 : fetchRel wnafFormCode 0x146 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem wf_at_148 : fetchRel wnafFormCode 0x148 = some (.alu .sub a0 a3 a0, 4) := by decide
theorem wf_at_14c : fetchRel wnafFormCode 0x14C = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem wf_at_14e : fetchRel wnafFormCode 0x14E = some (.alu .and a0 a0 a2, 2) := by decide
theorem wf_at_150 : fetchRel wnafFormCode 0x150 = some (.branch .beq a0 x0 0x14, 2) := by decide
theorem wf_at_152 : fetchRel wnafFormCode 0x152 = some (.branch .beq (19 : Fin 32) (21 : Fin 32) 0x58, 4) := by decide
theorem wf_at_156 : fetchRel wnafFormCode 0x156 = some (.alu .add a2 (25 : Fin 32) (21 : Fin 32), 4) := by decide
theorem wf_at_15a : fetchRel wnafFormCode 0x15A = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x1, 2) := by decide
theorem wf_at_15c : fetchRel wnafFormCode 0x15C = some (.store .sb a2 x0 0x0, 4) := by decide
theorem wf_at_160 : fetchRel wnafFormCode 0x160 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem wf_at_162 : fetchRel wnafFormCode 0x162 = some (.branch .bne a0 x0 0xFFFFFFF0, 2) := by decide
theorem wf_at_164 : fetchRel wnafFormCode 0x164 = some (.store .sw sp x0 0xC, 2) := by decide
theorem wf_at_166 : fetchRel wnafFormCode 0x166 = some (.alu .add (23 : Fin 32) (23 : Fin 32) a1, 2) := by decide
theorem wf_at_168 : fetchRel wnafFormCode 0x168 = some (.jal x0 0xFFFFFEEE, 2) := by decide
theorem wf_at_16a : fetchRel wnafFormCode 0x16A = some (.load .lw a0 sp 0xC, 2) := by decide
theorem wf_at_16c : fetchRel wnafFormCode 0x16C = some (.alu .or a0 (26 : Fin 32) a0, 4) := by decide
theorem wf_at_170 : fetchRel wnafFormCode 0x170 = some (.branch .beq a0 x0 0xE, 2) := by decide
theorem wf_at_172 : fetchRel wnafFormCode 0x172 = some (.branch .bgeu (22 : Fin 32) (19 : Fin 32) 0x34, 4) := by decide
theorem wf_at_176 : fetchRel wnafFormCode 0x176 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem wf_at_178 : fetchRel wnafFormCode 0x178 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x1, 2) := by decide
theorem wf_at_17a : fetchRel wnafFormCode 0x17A = some (.store .sb (20 : Fin 32) a0 0x0, 4) := by decide
theorem wf_at_17e : fetchRel wnafFormCode 0x17E = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem wf_at_180 : fetchRel wnafFormCode 0x180 = some (.load .lw ra sp 0x6C, 2) := by decide
theorem wf_at_182 : fetchRel wnafFormCode 0x182 = some (.load .lw (8 : Fin 32) sp 0x68, 2) := by decide
theorem wf_at_184 : fetchRel wnafFormCode 0x184 = some (.load .lw (9 : Fin 32) sp 0x64, 2) := by decide
theorem wf_at_186 : fetchRel wnafFormCode 0x186 = some (.load .lw (18 : Fin 32) sp 0x60, 2) := by decide
theorem wf_at_188 : fetchRel wnafFormCode 0x188 = some (.load .lw (19 : Fin 32) sp 0x5C, 2) := by decide
theorem wf_at_18a : fetchRel wnafFormCode 0x18A = some (.load .lw (20 : Fin 32) sp 0x58, 2) := by decide
theorem wf_at_18c : fetchRel wnafFormCode 0x18C = some (.load .lw (21 : Fin 32) sp 0x54, 2) := by decide
theorem wf_at_18e : fetchRel wnafFormCode 0x18E = some (.load .lw (22 : Fin 32) sp 0x50, 2) := by decide
theorem wf_at_190 : fetchRel wnafFormCode 0x190 = some (.load .lw (23 : Fin 32) sp 0x4C, 2) := by decide
theorem wf_at_192 : fetchRel wnafFormCode 0x192 = some (.load .lw (24 : Fin 32) sp 0x48, 2) := by decide
theorem wf_at_194 : fetchRel wnafFormCode 0x194 = some (.load .lw (25 : Fin 32) sp 0x44, 2) := by decide
theorem wf_at_196 : fetchRel wnafFormCode 0x196 = some (.load .lw (26 : Fin 32) sp 0x40, 2) := by decide
theorem wf_at_198 : fetchRel wnafFormCode 0x198 = some (.load .lw (27 : Fin 32) sp 0x3C, 2) := by decide
theorem wf_at_19a : fetchRel wnafFormCode 0x19A = some (.aluImm .add sp sp 0x70, 2) := by decide
theorem wf_at_19c : fetchRel wnafFormCode 0x19C = some (.jalr x0 ra 0x0, 2) := by decide
theorem wf_at_19e : fetchRel wnafFormCode 0x19E = some (.auipc ra 0xA000, 4) := by decide
theorem wf_at_1a2 : fetchRel wnafFormCode 0x1A2 = some (.jalr ra ra 0x7B6, 4) := by decide
theorem wf_at_1a6 : fetchRel wnafFormCode 0x1A6 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem wf_at_1a8 : fetchRel wnafFormCode 0x1A8 = some (.jal x0 0x4, 2) := by decide
theorem wf_at_1aa : fetchRel wnafFormCode 0x1AA = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem wf_at_1ac : fetchRel wnafFormCode 0x1AC = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem wf_at_1ae : fetchRel wnafFormCode 0x1AE = some (.auipc ra 0xA000, 4) := by decide
theorem wf_at_1b2 : fetchRel wnafFormCode 0x1B2 = some (.jalr ra ra 0x7B6, 4) := by decide
end

abbrev WF : Word := BitVec.ofNat 32 wnafFormAddress

/-- The little-endian number of a byte list. -/
def leN : List Nat → Nat
  | [] => 0
  | b :: l => b + 256 * leN l

/-- The Rust loop, from bit `pos` with `carry`, on the number `N` of `L`
bits. Each step consumes at least one bit when `N < 2 ^ L`, so `L + 1`
steps of fuel are enough. -/
def wnafGo (N L : Nat) : Nat → Nat → Nat → List Int
  | 0, _, _ => []
  | fuel + 1, pos, carry =>
    if pos < L then
      if (carry + N / 2 ^ pos % 32) % 2 = 0 then 0 :: wnafGo N L fuel (pos + 1) carry
      else
        let w := carry + N / 2 ^ pos % 32
        let c' := if w < 16 then 0 else 1
        let skip := min 5 (L - c' - pos)
        ((if w < 16 then (w : Int) else (w : Int) - 32) :: List.replicate (skip - 1) 0) ++
          wnafGo N L fuel (pos + skip) c'
    else if carry = 0 then [] else [(carry : Int)]

/-- `wnaf_form`'s digits for the bytes `c` and the bit length `L`. -/
def wnafSpec (c : List Nat) (L : Nat) : List Int := wnafGo (leN c) L (L + 1) 0 0

theorem leN_split : ∀ (l : List Nat) (s : Nat), leN l = leN (l.take s) + 256 ^ s * leN (l.drop s)
  | [], s => by simp [leN]
  | b :: l, 0 => by simp [leN]
  | b :: l, s + 1 => by
    simp only [List.take_succ_cons, List.drop_succ_cons, leN]
    rw [leN_split l s, Nat.pow_succ, Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ s)]

theorem leN_lt : ∀ (l : List Nat), (∀ b ∈ l, b < 256) → leN l < 256 ^ l.length
  | [], _ => by simp [leN]
  | b :: l, h => by
    have hb := h b List.mem_cons_self
    have := leN_lt l fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [leN, List.length_cons, Nat.pow_succ]; omega

/-- Limb `j` of the bytes, as `LimbBuffer` reads it: bytes `8j` to `8j + 7`,
zero past the end. -/
def lmb (c : List Nat) (j : Nat) : Nat := leN ((c.drop (8 * j)).take 8)

theorem leN_take_lt {l : List Nat} (h : ∀ b ∈ l, b < 256) (s : Nat) : leN (l.take s) < 256 ^ s := by
  have := leN_lt (l.take s) fun b hb => h b (List.mem_of_mem_take hb)
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by rw [List.length_take]; exact Nat.min_le_left _ _))

theorem leN_div {l : List Nat} (h : ∀ b ∈ l, b < 256) (s : Nat) : leN l / 256 ^ s = leN (l.drop s) := by
  rw [leN_split l s, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt (leN_take_lt h s), Nat.zero_add]

theorem lmb_lt {c : List Nat} (h : ∀ b ∈ c, b < 256) (j : Nat) : lmb c j < 2 ^ 64 :=
  leN_take_lt (fun b hb => h b (List.mem_of_mem_drop hb)) 8

theorem leN_drop_succ {c : List Nat} (j : Nat) :
    leN (c.drop (8 * j)) = lmb c j + 2 ^ 64 * leN (c.drop (8 * (j + 1))) := by
  rw [leN_split (c.drop (8 * j)) 8, List.drop_drop, show 8 * j + 8 = 8 * (j + 1) by omega]; rfl

theorem leN_shift {c : List Nat} (h : ∀ b ∈ c, b < 256) (j : Nat) :
    leN c / 2 ^ (64 * j) = leN (c.drop (8 * j)) := by
  rw [show 2 ^ (64 * j) = 256 ^ (8 * j) by rw [Nat.pow_mul, Nat.pow_mul]]; exact leN_div h _

theorem lmb_mod {c : List Nat} (h : ∀ b ∈ c, b < 256) (j : Nat) :
    leN (c.drop (8 * j)) % 2 ^ 64 = lmb c j := by
  rw [leN_drop_succ, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (lmb_lt h j)

/-- The window at bit `64 j + b`, for `b < 59`, is in limb `j`. -/
theorem win_lo {c : List Nat} (h : ∀ b ∈ c, b < 256) {j b : Nat} (hb : b < 59) :
    leN c / 2 ^ (64 * j + b) % 32 = lmb c j / 2 ^ b % 32 := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, leN_shift h, leN_drop_succ,
    show 2 ^ 64 = 2 ^ b * (32 * 2 ^ (59 - b)) by
      rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega,
    Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.mul_assoc,
    Nat.add_mul_mod_self_left]

/-- The window at bit `64 j + b`, for `59 ≤ b < 64`, spans limbs `j` and
`j + 1`. -/
theorem win_hi {c : List Nat} (h : ∀ b ∈ c, b < 256) {j b : Nat} (hb1 : 59 ≤ b) (hb2 : b < 64) :
    leN c / 2 ^ (64 * j + b) % 32 = (lmb c j / 2 ^ b + lmb c (j + 1) * 2 ^ (64 - b)) % 32 := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, leN_shift h, leN_drop_succ,
    show 2 ^ 64 = 2 ^ b * 2 ^ (64 - b) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), ← lmb_mod h (j + 1)]
  generalize leN (List.drop (8 * (j + 1)) c) = T
  generalize lmb c j / 2 ^ b = x
  have e : 2 ^ (64 - b) * T = 2 ^ (64 - b) * (T % 2 ^ 64) + 32 * (2 ^ (64 - b) * 2 ^ 59 * (T / 2 ^ 64)) := by
    rw [Nat.mul_assoc (2 ^ (64 - b)), Nat.mul_left_comm 32, ← Nat.mul_assoc 32,
      show (32 : Nat) * 2 ^ 59 = 2 ^ 64 from rfl, ← Nat.mul_add, Nat.mod_add_div]
  rw [e, ← Nat.add_assoc, Nat.add_mul_mod_self_left, Nat.mul_comm (2 ^ (64 - b))]

theorem leN_take_succ : ∀ (l : List Nat) (k : Nat), leN (l.take (k + 1)) = l.getD 0 0 + 256 * leN ((l.drop 1).take k)
  | [], k => by simp [leN]
  | a :: l, k => by simp [leN]

theorem getD_drop1 : ∀ (l : List Nat) (i : Nat), (l.drop 1).getD i 0 = l.getD (i + 1) 0
  | [], i => by simp
  | a :: l, i => by simp

theorem getD_dropK : ∀ (k : Nat) (l : List Nat) (i : Nat), (l.drop k).getD i 0 = l.getD (i + k) 0
  | 0, l, i => rfl
  | k + 1, [], i => by simp
  | k + 1, a :: l, i => by
    rw [List.drop_succ_cons, getD_dropK k l i, show i + (k + 1) = (i + k) + 1 by omega]; simp

theorem getD_memBytes' (M : Word → BitVec 8) (p : Word) {n j : Nat} (h : j < n) :
    (memBytes M p n).getD j 0 = (M (p + BitVec.ofNat 32 j)).toNat := by
  unfold memBytes; rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl

theorem leN_take8 (l : List Nat) : leN (l.take 8) = l.getD 0 0 + 256 * (l.getD 1 0 + 256 * (l.getD 2 0 + 256 *
    (l.getD 3 0 + 256 * (l.getD 4 0 + 256 * (l.getD 5 0 + 256 * (l.getD 6 0 + 256 * (l.getD 7 0 + 256 * 0))))))) := by
  have t0 : ∀ l : List Nat, leN (l.take 0) = 0 := fun l => by simp [leN]
  rw [leN_take_succ, leN_take_succ, leN_take_succ, leN_take_succ, leN_take_succ, leN_take_succ, leN_take_succ,
    leN_take_succ, t0]
  simp only [List.drop_drop, getD_dropK]

theorem memBytes_lt (M : Word → BitVec 8) (p : Word) (n : Nat) : ∀ b ∈ memBytes M p n, b < 256 := by
  intro b hb
  unfold memBytes at hb
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
  exact (M _).isLt

theorem ilByte_getD (M : Word → BitVec 8) (p : Word) (n k : Nat) :
    (ilByte M p n k).toNat = (memBytes M p n).getD k 0 := by
  unfold ilByte
  by_cases hk : k < n
  · simp only [hk, ↓reduceIte, getD_memBytes' M p hk]
  · simp only [hk, ↓reduceIte]
    unfold memBytes
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl

/-- The `u64` `increment_limb` reads, from its two words. -/
theorem ilWord_leN (M : Word → BitVec 8) (p : Word) (n : Nat) :
    (ilWord M p n 0).toNat + 2 ^ 32 * (ilWord M p n 1).toNat = leN ((memBytes M p n).take 8) := by
  rw [ilWord_toNat, ilWord_toNat, leN_take8]
  simp only [ilByte_getD]
  show _ = (memBytes M p n).getD 0 0 + 256 * ((memBytes M p n).getD 1 0 + 256 * ((memBytes M p n).getD 2 0 + 256 *
    ((memBytes M p n).getD 3 0 + 256 * ((memBytes M p n).getD 4 0 + 256 * ((memBytes M p n).getD 5 0 + 256 *
    ((memBytes M p n).getD 6 0 + 256 * ((memBytes M p n).getD 7 0 + 256 * 0)))))))
  unfold le32
  simp only [Nat.reduceMul, Nat.reduceAdd]
  omega

theorem memBytes_drop8 (M : Word → BitVec 8) (p : Word) {n : Nat} (h : 8 ≤ n) :
    memBytes M (p + 8) (n - 8) = (memBytes M p n).drop 8 := by
  apply List.ext_getElem (by simp [memBytes_length])
  intro i h1 h2
  rw [memBytes_length] at h1
  rw [List.getElem_drop]
  simp only [memBytes, List.getElem_map, List.getElem_range]
  rw [show p + 8 + BitVec.ofNat 32 i = p + BitVec.ofNat 32 (8 + i) from add_ofNat_assoc p 8 i]

theorem memBytes_drop8_short (M : Word → BitVec 8) (p q : Word) {n : Nat} (h : n < 8) :
    memBytes M q 0 = (memBytes M p n).drop 8 := by
  rw [List.drop_eq_nil_of_le (by rw [memBytes_length]; omega)]; rfl

theorem PanicCode.hi {M M' : Word → BitVec 8} (h : PanicCode M) (hx : ∀ x : Word, dramEnd ≤ x.toNat → M' x = M x) :
    PanicCode M' := fun p hp i hi => by
  have hb := panicFns_hi p hp
  rw [hx _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.1) (by omega),
    Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
  exact h p hp i hi

/-- The byte `wnaf_form` stores for a digit. -/
def digB (d : Int) : Nat := (d % 256).toNat

/-- Where `wnaf_form` runs: the code it and its callees run, its stack frame
`F` with `increment_limb`'s 0x20 bytes below it, the `wl`-byte digit buffer
at `wp`, and the `cn` scalar bytes at `cp`. -/
structure WfCtx (M0 : Word → BitVec 8) (F wp cp : Word) (wl cn L : Nat) : Prop where
  cod : CodeIn M0 WF wnafFormCode
  mset : CodeIn M0 (BitVec.ofNat 32 memsetAddress) memsetCode
  il : CodeIn M0 (BitVec.ofNat 32 incrementLimbAddress) incrementLimbCode
  mcs : CodeIn M0 (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  mcb : CodeIn M0 (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  lsh : CodeIn M0 (BitVec.ofNat 32 lshrdi3Address) lshrdi3Code
  ash : CodeIn M0 (BitVec.ofNat 32 ashldi3Address) ashldi3Code
  exu : CodeIn M0 (BitVec.ofNat 32 expectUsizeAddress) expectUsizeCode
  pan : PanicCode M0
  room : Room F 48
  hFd : F.toNat + 0x70 ≤ dramEnd
  hL : L < wl
  hLw : wl < 2 ^ 31
  hwl : wp.toNat + wl ≤ dramEnd
  sWR : Sep wp wl (F + 0xFFFFFFE0) 0x90
  hcw : cp.toNat + cn < 2 ^ 32
  sCR : Sep cp cn (F + 0xFFFFFFE0) 0x90
  sCW : Sep cp cn wp wl
  hN : leN (memBytes M0 cp cn) < 2 ^ L

/-- The slice `LimbBuffer` has left after reading limbs up to `k - 1`:
empty once the bytes run out, else the bytes from `8 k`. -/
def RestAt (M : Word → BitVec 8) (s cp : Word) (cn k : Nat) : Prop :=
  (memLoad32 M (s + 4) = 0 ∧ cn ≤ 8 * k) ∨
    (memLoad32 M s = cp + BitVec.ofNat 32 (8 * k) ∧ (memLoad32 M (s + 4)).toNat = cn - 8 * k ∧ 8 * k < cn)

/-- `wnaf_form` at `off` in the loop (0x5E is the head), after `pos` bits with
`carry`, the digits `D` written, and `LimbBuffer` at limb `j`. -/
structure WfSt (M0 Ms : Word → BitVec 8) (F wp cp : Word) (wl cn L : Nat) (r0 : Fin 32 → Word)
    (M : Word → BitVec 8) (n : Machine) (off pos carry j : Nat) (D : List Int) : Prop where
  st : St M WF n off (reg n)
  hsp : reg n sp = F
  s2 : reg n (18 : Fin 32) = BitVec.ofNat 32 L
  s3 : reg n (19 : Fin 32) = BitVec.ofNat 32 wl
  s9 : reg n (25 : Fin 32) = wp
  s8 : reg n (24 : Fin 32) = BitVec.ofNat 32 59
  s5 : reg n (21 : Fin 32) = BitVec.ofNat 32 (pos + 1)
  s6 : reg n (22 : Fin 32) = BitVec.ofNat 32 pos
  s7 : reg n (23 : Fin 32) = BitVec.ofNat 32 pos
  s11 : reg n (27 : Fin 32) = BitVec.ofNat 32 (L - pos)
  s10 : reg n (26 : Fin 32) = BitVec.ofNat 32 carry
  gp : reg n (3 : Fin 32) = r0 3
  tp : reg n (4 : Fin 32) = r0 4
  hpos : pos ≤ L
  hc : carry ≤ 1
  chi : memLoad32 M (F + BitVec.ofNat 32 0xC) = 0
  idx : memLoad32 M (F + BitVec.ofNat 32 0x28) = BitVec.ofNat 32 j
  hj : j ≤ pos / 64 ∧ pos / 64 ≤ j + 1
  cur : (memLoad32 M (F + BitVec.ofNat 32 0x18)).toNat + 2 ^ 32 * (memLoad32 M (F + BitVec.ofNat 32 0x1C)).toNat =
    lmb (memBytes M0 cp cn) j
  nxt : (memLoad32 M (F + BitVec.ofNat 32 0x20)).toNat + 2 ^ 32 * (memLoad32 M (F + BitVec.ofNat 32 0x24)).toNat =
    lmb (memBytes M0 cp cn) (j + 1)
  rest : RestAt M (F + BitVec.ofNat 32 0x10) cp cn (j + 2)
  len : D.length = pos
  out : ∀ i, i < pos → M (wp + BitVec.ofNat 32 i) = BitVec.ofNat 8 (digB (D.getD i 0))
  spec : ∃ f, L - pos + 1 ≤ f ∧ D ++ wnafGo (leN (memBytes M0 cp cn)) L f pos carry = wnafSpec (memBytes M0 cp cn) L
  agree : ∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → Sep wp wl x 1 → M x = M0 x
  slots : ∀ k, 0x3C ≤ k → k < 0x70 → M (F + BitVec.ofNat 32 k) = Ms (F + BitVec.ofNat 32 k)

theorem memBytes_dropK (M : Word → BitVec 8) (p : Word) {n k : Nat} (h : k ≤ n) :
    memBytes M (p + BitVec.ofNat 32 k) (n - k) = (memBytes M p n).drop k := by
  apply List.ext_getElem (by simp [memBytes_length])
  intro i h1 h2
  rw [memBytes_length] at h1
  rw [List.getElem_drop]
  simp only [memBytes, List.getElem_map, List.getElem_range]
  rw [add_ofNat_assoc]

theorem ofNat_inj32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem wbr_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    branchTaken .beq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (a = b) := by
  show (BitVec.ofNat 32 a == BitVec.ofNat 32 b) = _
  by_cases h : a = b
  · subst h; rw [decide_eq_true rfl]; exact decide_eq_true rfl
  · rw [decide_eq_false h]; exact decide_eq_false (fun e => h (ofNat_inj32 ha hb e))

theorem wbr_bne {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    branchTaken .bne (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = !decide (a = b) := by
  rw [← wbr_beq ha hb]; rfl

theorem wbr_bltu {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    branchTaken .bltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (a < b) := by
  show decide ((BitVec.ofNat 32 a).toNat < (BitVec.ofNat 32 b).toNat) = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem wbr_bgeu {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    branchTaken .bgeu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (b ≤ a) := by
  show (!decide ((BitVec.ofNat 32 a).toNat < (BitVec.ofNat 32 b).toNat)) = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem wf_tb_pow : ∀ (n i : Nat), (2 ^ n - 1).testBit i = decide (i < n)
  | 0, i => by
    rw [show 2 ^ 0 - 1 = 0 from rfl, Nat.zero_testBit]; exact (decide_eq_false (Nat.not_lt_zero i)).symm
  | n + 1, 0 => by
    have e : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      have := Nat.one_le_two_pow (n := n); rw [Nat.pow_succ]; omega
    rw [e, Nat.testBit_zero, decide_eq_true (show (2 * (2 ^ n - 1) + 1) % 2 = 1 by omega),
      decide_eq_true (Nat.succ_pos n)]
  | n + 1, i + 1 => by
    have e : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      have := Nat.one_le_two_pow (n := n); rw [Nat.pow_succ]; omega
    have h : (2 * (2 ^ n - 1) + 1) / 2 = 2 ^ n - 1 := by omega
    rw [e, Nat.testBit_succ, h, wf_tb_pow n i]
    exact decide_eq_decide.mpr Nat.succ_lt_succ_iff.symm

/-- ANDing with `2^n - 1` keeps the low `n` bits. Core's
`Nat.and_two_pow_sub_one_eq_mod` depends on `Classical.choice`. -/
theorem wf_and_pow (x n : Nat) : x &&& (2 ^ n - 1) = x % 2 ^ n :=
  Nat.eq_of_testBit_eq fun i => by
    rw [Nat.testBit_and, wf_tb_pow, Nat.testBit_mod_two_pow, Bool.and_comm]

theorem wv_and (x : Word) (k : Nat) (hk : k ≤ 32) :
    (aluEval .and x (BitVec.ofNat 32 (2 ^ k - 1))).toNat = x.toNat % 2 ^ k := by
  show (x &&& BitVec.ofNat 32 (2 ^ k - 1)).toNat = _
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.pow_le_pow_right (n := 2) (by decide) hk; omega),
    wf_and_pow]

theorem wv_srl (x : Word) (k : Nat) (hk : k < 32) : (aluEval .srl x (BitVec.ofNat 32 k)).toNat = x.toNat / 2 ^ k := by
  show (x >>> ((BitVec.ofNat 32 k).toNat % 32)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega), Nat.mod_eq_of_lt hk, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

theorem sep1_out {a x : Word} {n : Nat} (h : Sep a n x 1) (hw : a.toNat + n ≤ 2 ^ 32) :
    x.toNat < a.toNat ∨ a.toNat + n ≤ x.toNat := by
  rcases Nat.lt_or_ge x.toNat a.toNat with h1 | h1
  · exact Or.inl h1
  · rcases Nat.lt_or_ge x.toNat (a.toNat + n) with h2 | h2
    · exfalso
      refine h (x.toNat - a.toNat) (by omega) 0 (by decide) ?_
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := x.isLt; have := a.isLt
      rw [Nat.mod_eq_of_lt (a := x.toNat - a.toNat) (by omega), Nat.mod_eq_of_lt (a := 0) (by decide),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · exact Or.inr h2

section Calls
variable {M0 Ms M : Word → BitVec 8} {F wp cp : Word} {wl cn L : Nat}

theorem WfCtx.hi (C : WfCtx M0 F wp cp wl cn L) {M : Word → BitVec 8}
    (hag : ∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → Sep wp wl x 1 → M x = M0 x) :
    ∀ x : Word, dramEnd ≤ x.toNat → M x = M0 x := fun x hx => by
  have hF := C.hFd; have hR := C.room.2.1; have hw := C.hwl; unfold dramEnd at *
  apply hag x
  · exact sep_of_le (by rw [BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 2 ^ 32 - 0x20 from rfl]; omega)
      (by have := x.isLt; omega)
  · exact sep_of_le (by omega) (by have := x.isLt; omega)

theorem WfCtx.code (C : WfCtx M0 F wp cp wl cn L) {M : Word → BitVec 8}
    (hag : ∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → Sep wp wl x 1 → M x = M0 x) {b : Word} {code : List Nat}
    (hc : CodeIn M0 b code) (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + code.length ≤ 2 ^ 32) : CodeIn M b code :=
  CodeIn.hi hc (fun x hx => C.hi hag x (by unfold dramEnd; omega)) hb hbl

theorem WfCtx.cbytes (C : WfCtx M0 F wp cp wl cn L) {M : Word → BitVec 8}
    (hag : ∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → Sep wp wl x 1 → M x = M0 x) :
    ∀ i, i < cn → M (cp + BitVec.ofNat 32 i) = M0 (cp + BitVec.ofNat 32 i) := fun i hi =>
  hag _ (C.sCR.sub (c := i) (l := 1) hi).symm (C.sCW.sub (c := i) (l := 1) hi).symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- A call of `increment_limb` on the `LimbBuffer` at `F + 0x10`, when its
slice is the bytes from `8 k`: the old next limb becomes the current one,
and the next one is limb `k`. -/
theorem wf_inc (C : WfCtx M0 F wp cp wl cn L) {n : Machine} {off : Nat} (s : St M WF n off (reg n)) {imm o : Word}
    (hag : ∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → Sep wp wl x 1 → M x = M0 x)
    (h1 : fetchRel wnafFormCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel wnafFormCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : WF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 incrementLimbAddress) (hev : off % 2 = 0)
    (hsp : reg n sp = F) (ha0 : reg n a0 = F + BitVec.ofNat 32 0x10) {k : Nat} (hR : RestAt M (F + BitVec.ofNat 32 0x10) cp cn k) :
    ∃ n', Steps n n' ∧ St n'.mem WF n' (off + 8) (reg n') ∧ reg n' sp = F ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      memLoad32 n'.mem (F + BitVec.ofNat 32 0x18) = memLoad32 M (F + BitVec.ofNat 32 0x20) ∧
      memLoad32 n'.mem (F + BitVec.ofNat 32 0x1C) = memLoad32 M (F + BitVec.ofNat 32 0x24) ∧
      memLoad32 n'.mem (F + BitVec.ofNat 32 0x28) = memLoad32 M (F + BitVec.ofNat 32 0x28) + 1 ∧
      (memLoad32 n'.mem (F + BitVec.ofNat 32 0x20)).toNat + 2 ^ 32 * (memLoad32 n'.mem (F + BitVec.ofNat 32 0x24)).toNat =
        lmb (memBytes M0 cp cn) k ∧
      RestAt n'.mem (F + BitVec.ofNat 32 0x10) cp cn (k + 1) ∧
      ∀ x, Sep (F + 0xFFFFFFE0) 0x20 x 1 → Sep (F + BitVec.ofNat 32 0x10) 28 x 1 → n'.mem x = M x := by
  have hc : CodeIn M WF wnafFormCode := C.code hag C.cod (by decide) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := BitVec.ofNat 32 incrementLimbAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have room := C.room; have hFd := C.hFd
  obtain ⟨hFa, hF1, hF2⟩ := room
  unfold dramEnd at hFd hF2
  have hFc : ∀ c, c ≤ 0x70 → (F + BitVec.ofNat 32 c).toNat = F.toNat + c := fun c hc' => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hG : (F + 0xFFFFFFE0 : Word).toNat = F.toNat - 0x20 := by
    rw [BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 2 ^ 32 - 0x20 from rfl]; omega
  have hiF : ∀ {a : Word} {l : Nat} {b : Word} {k : Nat}, a.toNat + l ≤ 0x3FCE0000 → 0x40000000 ≤ b.toNat →
      b.toNat + k ≤ 2 ^ 32 → Sep a l b k := fun h1 h2 h3 => sep_of_le (by omega) h3
  -- the slice `increment_limb` reads
  obtain ⟨P, hP⟩ : ∃ P, memLoad32 M (F + BitVec.ofNat 32 0x10) = P := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, memLoad32 M (F + BitVec.ofNat 32 0x10 + 4) = N := ⟨_, rfl⟩
  have hmin : N.toNat = 0 ∨ (P = cp + BitVec.ofNat 32 (8 * k) ∧ N.toNat = cn - 8 * k ∧ 8 * k < cn) := by
    rcases hR with ⟨h0, -⟩ | ⟨h0, h1, h2⟩
    · left; rw [← hN, h0]; rfl
    · right; exact ⟨hP ▸ h0, hN ▸ h1, h2⟩
  have sPX : ∀ {b : Word} {l : Nat}, Sep cp cn b l → Sep P (min N.toNat 8) b l := fun {b l} h => by
    rcases hmin with h0 | ⟨rfl, h1, h2⟩
    · rw [h0]; intro i hi; omega
    · exact (h.sub (c := 8 * k) (l := min N.toNat 8) (by omega))
  have sCR := C.sCR
  have env : ILEnv n1.mem (BitVec.ofNat 32 incrementLimbAddress) (reg n1 sp) (reg n1 a0) P N := by
    rw [mem1, r1 sp (by decide), r1 a0 (by decide), hsp, ha0]
    exact { hP := by decide
            cod := C.code hag C.il (by decide) (by decide)
            mcS := by rw [show (BitVec.ofNat 32 incrementLimbAddress : Word) + 0x128 = BitVec.ofNat 32 memcpyStubAddress by decide]
                      exact C.code hag C.mcs (by decide) (by decide)
            mcB := by rw [show (BitVec.ofNat 32 incrementLimbAddress : Word) + 0x128 + 8 =
                        BitVec.ofNat 32 memcpyStubAddress + 8 by decide]; exact C.code hag C.mcb (by decide) (by decide)
            hp := hP
            hn := hN
            hsa := hFa
            hS := by omega
            hs := aligned_add hFa (by decide)
            sGC := hiF (by rw [hG]; omega) (by decide) (by decide)
            sGS := hiF (by rw [hG]; omega) (by decide) (by decide)
            sGB := hiF (by rw [hG]; omega) (by decide) (by decide)
            sSC := hiF (by rw [hFc _ (by decide)]; omega) (by decide) (by decide)
            sSS := hiF (by rw [hFc _ (by decide)]; omega) (by decide) (by decide)
            sSB := hiF (by rw [hFc _ (by decide)]; omega) (by decide) (by decide)
            sSG := by
              have := sep_offsets (F + 0xFFFFFFE0) (c := 0x30) (n := 28) (d := 0) (k := 0x20) (Or.inr (by decide))
                (by decide) (by decide)
              rwa [add_ofNat_zero, show F + 0xFFFFFFE0 + BitVec.ofNat 32 0x30 = F + BitVec.ofNat 32 0x10 by
                rw [BitVec.add_assoc]; rfl] at this
            sPG := sPX (sCR.subR (c := 0) (l := 0x20) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
            sPS := sPX (by
              have := sCR.subR (c := 0x30) (l := 28) (by decide)
              rwa [show F + 0xFFFFFFE0 + BitVec.ofNat 32 0x30 = F + BitVec.ofNat 32 0x10 by
                rw [BitVec.add_assoc]; rfl] at this)
            hpw := by
              rcases hmin with h0 | ⟨rfl, h1, h2⟩
              · rw [h0, Nat.min_eq_left (by decide), Nat.add_zero]; exact P.isLt
              · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := C.hcw; omega }
  obtain ⟨n2, c2, pc2, sp2, k2, e8, eC, e18, e10, e14, e0, e4, f2⟩ := incrementLimb_correct n1 env pc1 rfl rfl
    (by rw [regs1]; simp +decide [upd]) (even_clear _ (even_at WF (by decide) (off + 8) (by omega)))
  rw [mem1, r1 a0 (by decide), ha0] at e8 eC e18 e10 e14
  rw [r1 a0 (by decide), ha0] at e0 e4
  rw [mem1, r1 sp (by decide), r1 a0 (by decide), hsp, ha0] at f2
  rw [mem1] at env
  have A : ∀ k : Nat, F + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 k = F + BitVec.ofNat 32 (0x10 + k) :=
    fun k => add_ofNat_assoc ..
  rw [show F + BitVec.ofNat 32 0x10 + (8 : Word) = F + BitVec.ofNat 32 0x18 from A 8,
    show F + BitVec.ofNat 32 0x10 + (0x10 : Word) = F + BitVec.ofNat 32 0x20 from A 0x10] at e8
  rw [show F + BitVec.ofNat 32 0x10 + (0xC : Word) = F + BitVec.ofNat 32 0x1C from A 0xC,
    show F + BitVec.ofNat 32 0x10 + (0x14 : Word) = F + BitVec.ofNat 32 0x24 from A 0x14] at eC
  rw [show F + BitVec.ofNat 32 0x10 + (0x18 : Word) = F + BitVec.ofNat 32 0x28 from A 0x18] at e18
  rw [show F + BitVec.ofNat 32 0x10 + (0x10 : Word) = F + BitVec.ofNat 32 0x20 from A 0x10] at e10
  rw [show F + BitVec.ofNat 32 0x10 + (0x14 : Word) = F + BitVec.ofNat 32 0x24 from A 0x14] at e14
  rw [add_lit_zero] at e0
  have hbytes : memBytes M P N.toNat = (memBytes M0 cp cn).drop (8 * k) := by
    rcases hR with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
    · rw [List.drop_eq_nil_of_le (by rw [memBytes_length]; exact h1),
        show N.toNat = 0 by rw [← hN, h0]; rfl]; rfl
    · rw [← hP, h0, ← hN, h1, ← memBytes_dropK M0 cp (Nat.le_of_lt h2)]
      exact memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact C.cbytes hag _ (by omega)
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, r1 sp (by decide), hsp],
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    e8, eC, e18, ?_, ?_, fun x h1 h2 => f2 x h1 h2⟩
  · rw [e10, e14, ilWord_leN, hbytes]; rfl
  · have e4' : memLoad32 n2.mem (F + BitVec.ofNat 32 0x10 + 4) = if N.toNat < 8 then 0 else N - 8 := e4
    rcases hR with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
    · have hN0 : N.toNat = 0 := by rw [← hN, h0]; rfl
      left; exact ⟨by rw [e4', if_pos (by omega)], by omega⟩
    · have hNv : N.toNat = cn - 8 * k := hN ▸ h1
      by_cases h8 : N.toNat < 8
      · left; exact ⟨by rw [e4', if_pos h8], by omega⟩
      · by_cases hz : cn - 8 * k = 8
        · left
          refine ⟨by rw [e4', if_neg h8]; exact BitVec.eq_of_toNat_eq (by
            rw [BitVec.toNat_sub, hNv, hz]; rfl), by omega⟩
        · right
          have hN0 : ¬ N = 0 := fun e => by rw [e] at hNv; simp at hNv; omega
          have := N.isLt
          refine ⟨by rw [e0, if_neg hN0, if_neg h8, ← hP, h0,
              show cp + BitVec.ofNat 32 (8 * k) + (8 : Word) = cp + BitVec.ofNat 32 (8 * k + 8) from add_ofNat_assoc ..,
              show 8 * k + 8 = 8 * (k + 1) by omega],
            by rw [e4', if_neg h8, BitVec.toNat_sub, show (8 : Word).toNat = 8 from rfl]; omega, by omega⟩

end Calls

section Steps
variable {M0 Ms M : Word → BitVec 8} {F wp cp : Word} {wl cn L : Nat} {r0 : Fin 32 → Word} {n : Machine}
  {off pos carry j : Nat} {D : List Int}

theorem WfSt.step (S : WfSt M0 Ms F wp cp wl cn L r0 M n off pos carry j D) {n' : Machine} {off' : Nat} {rd : Fin 32}
    {v : Word} (u : St M WF n' off' (upd (reg n) rd v))
    (hrd : rd.val ∉ [2, 3, 4, 18, 19, 21, 22, 23, 24, 25, 26, 27]) :
    WfSt M0 Ms F wp cp wl cn L r0 M n' off' pos carry j D := by
  have k : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := fun q hq =>
    u.upd_ne S.st.zero q (fun e => hrd (by rw [← e]; exact hq))
  exact ⟨u.self, by rw [k sp (by decide), S.hsp], by rw [k _ (by decide), S.s2], by rw [k _ (by decide), S.s3],
    by rw [k _ (by decide), S.s9], by rw [k _ (by decide), S.s8], by rw [k _ (by decide), S.s5],
    by rw [k _ (by decide), S.s6], by rw [k _ (by decide), S.s7], by rw [k _ (by decide), S.s11],
    by rw [k _ (by decide), S.s10], by rw [k _ (by decide), S.gp], by rw [k _ (by decide), S.tp], S.hpos, S.hc,
    S.chi, S.idx, S.hj, S.cur, S.nxt, S.rest, S.len, S.out, S.spec, S.agree, S.slots⟩

theorem WfSt.jmp (S : WfSt M0 Ms F wp cp wl cn L r0 M n off pos carry j D) {n' : Machine} {off' : Nat}
    (u : St M WF n' off' (reg n)) : WfSt M0 Ms F wp cp wl cn L r0 M n' off' pos carry j D :=
  ⟨u.self, by rw [u.regs, S.hsp], by rw [u.regs, S.s2], by rw [u.regs, S.s3], by rw [u.regs, S.s9],
    by rw [u.regs, S.s8], by rw [u.regs, S.s5], by rw [u.regs, S.s6], by rw [u.regs, S.s7], by rw [u.regs, S.s11],
    by rw [u.regs, S.s10], by rw [u.regs, S.gp], by rw [u.regs, S.tp], S.hpos, S.hc, S.chi, S.idx, S.hj, S.cur, S.nxt,
    S.rest, S.len, S.out, S.spec, S.agree, S.slots⟩

/-- A word stored in the scratch words at `F + 0x34` or `F + 0x38` keeps
the invariant. -/
theorem WfSt.scratch (C : WfCtx M0 F wp cp wl cn L) (S : WfSt M0 Ms F wp cp wl cn L r0 M n off pos carry j D)
    {n' : Machine} {off' k : Nat} {v : Word} (hk : k = 0x34 ∨ k = 0x38)
    (u : St (memStore32 M (F + BitVec.ofNat 32 k) v) WF n' off' (reg n)) :
    WfSt M0 Ms F wp cp wl cn L r0 (memStore32 M (F + BitVec.ofNat 32 k) v) n' off' pos carry j D := by
  have hk4 : k + 4 ≤ 0x3C ∧ 0x34 ≤ k := by rcases hk with rfl | rfl <;> decide
  have sO : ∀ c l, c + l ≤ 0x34 ∨ 0x3C ≤ c → c + l ≤ 0x70 → Sep (F + BitVec.ofNat 32 k) 4 (F + BitVec.ofNat 32 c) l :=
    fun c l h h2 => sep_offsets F (by omega) (by omega) (by omega)
  have L0 : ∀ c, c + 4 ≤ 0x34 → memLoad32 (memStore32 M (F + BitVec.ofNat 32 k) v) (F + BitVec.ofNat 32 c) =
      memLoad32 M (F + BitVec.ofNat 32 c) := fun c h => memLoad32_store32_sep (sO c 4 (Or.inl h) (by omega))
  have room := C.room; have hFd := C.hFd; unfold dramEnd at hFd
  have sR : ∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → Sep (F + BitVec.ofNat 32 k) 4 x 1 := fun x hx => by
    have := hx.symm.subR (c := 0x20 + k) (l := 4) (by omega)
    rw [show F + 0xFFFFFFE0 + BitVec.ofNat 32 (0x20 + k) = F + BitVec.ofNat 32 k by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this
    exact this.symm
  have sW : ∀ i, i < wl → Sep (F + BitVec.ofNat 32 k) 4 (wp + BitVec.ofNat 32 i) 1 := fun i hi =>
    sR _ (C.sWR.sub (c := i) (l := 1) hi).symm
  have hRest : RestAt (memStore32 M (F + BitVec.ofNat 32 k) v) (F + BitVec.ofNat 32 0x10) cp cn (j + 2) := by
    have e4 : F + BitVec.ofNat 32 0x10 + 4 = F + BitVec.ofNat 32 0x14 := add_ofNat_assoc F 0x10 4
    have hr := S.rest
    unfold RestAt at hr ⊢
    rw [e4, L0 0x10 (by decide), L0 0x14 (by decide)]; rw [e4] at hr; exact hr
  exact ⟨u.self, by rw [u.regs, S.hsp], by rw [u.regs, S.s2], by rw [u.regs, S.s3], by rw [u.regs, S.s9],
    by rw [u.regs, S.s8], by rw [u.regs, S.s5], by rw [u.regs, S.s6], by rw [u.regs, S.s7], by rw [u.regs, S.s11],
    by rw [u.regs, S.s10], by rw [u.regs, S.gp], by rw [u.regs, S.tp], S.hpos, S.hc,
    by rw [L0 _ (by decide), S.chi], by rw [L0 _ (by decide), S.idx], S.hj,
    by rw [L0 _ (by decide), L0 _ (by decide), S.cur], by rw [L0 _ (by decide), L0 _ (by decide), S.nxt], hRest, S.len,
    fun i hi => by rw [memStore32_get_sep (sW i (by have := C.hL; have := S.hpos; omega)), S.out i hi], S.spec,
    fun x h1 h2 => by rw [memStore32_get_sep (sR x h1), S.agree x h1 h2],
    fun c c1 c2 => by rw [memStore32_get_sep (sO c 1 (Or.inr c1) (by omega)), S.slots c c1 c2]⟩

/-- The invariant after `increment_limb`, which moves `LimbBuffer` from limb
`j` to `j + 1`. -/
theorem WfSt.inc (C : WfCtx M0 F wp cp wl cn L) (S : WfSt M0 Ms F wp cp wl cn L r0 M n off pos carry j D)
    {n' : Machine} {off' : Nat} (hj1 : j + 1 ≤ pos / 64) (u : St n'.mem WF n' off' (reg n')) (hsp : reg n' sp = F)
    (hk : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q)
    (e18 : memLoad32 n'.mem (F + BitVec.ofNat 32 0x18) = memLoad32 M (F + BitVec.ofNat 32 0x20))
    (e1C : memLoad32 n'.mem (F + BitVec.ofNat 32 0x1C) = memLoad32 M (F + BitVec.ofNat 32 0x24))
    (e28 : memLoad32 n'.mem (F + BitVec.ofNat 32 0x28) = memLoad32 M (F + BitVec.ofNat 32 0x28) + 1)
    (enx : (memLoad32 n'.mem (F + BitVec.ofNat 32 0x20)).toNat + 2 ^ 32 * (memLoad32 n'.mem (F + BitVec.ofNat 32 0x24)).toNat =
      lmb (memBytes M0 cp cn) (j + 2))
    (er : RestAt n'.mem (F + BitVec.ofNat 32 0x10) cp cn (j + 2 + 1))
    (fr : ∀ x, Sep (F + 0xFFFFFFE0) 0x20 x 1 → Sep (F + BitVec.ofNat 32 0x10) 28 x 1 → n'.mem x = M x) :
    WfSt M0 Ms F wp cp wl cn L r0 n'.mem n' off' pos carry (j + 1) D := by
  have room := C.room; have hFd := C.hFd; unfold dramEnd at hFd
  have hG : (F + 0xFFFFFFE0 : Word).toNat = F.toNat - 0x20 := by
    rw [BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 2 ^ 32 - 0x20 from rfl]; have := room.2.1; omega
  have hFc : ∀ c, c ≤ 0x70 → (F + BitVec.ofNat 32 c).toNat = F.toNat + c := fun c hc' => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- every byte apart from `increment_limb`'s frame and the buffer struct keeps its value
  have K : ∀ x : Word, (x.toNat + 1 ≤ F.toNat - 0x20 ∨ F.toNat + 0x2C ≤ x.toNat ∨ (F.toNat ≤ x.toNat ∧ x.toNat + 1 ≤ F.toNat + 0x10)) →
      n'.mem x = M x := fun x hx => by
    have := x.isLt
    have hGF : F.toNat - 0x20 + 0x20 = F.toNat := by have := room.2.1; omega
    apply fr x
    · rcases hx with h | h | h
      · exact (sep_of_le (by rw [hG]; omega) (by rw [hG]; omega)).symm
      · exact sep_of_le (by rw [hG]; omega) (by omega)
      · exact sep_of_le (by rw [hG]; omega) (by omega)
    · rcases hx with h | h | h
      · exact (sep_of_le (by rw [hFc _ (by decide)]; omega) (by rw [hFc _ (by decide)]; omega)).symm
      · exact sep_of_le (by rw [hFc _ (by decide)]; omega) (by omega)
      · exact (sep_of_le (by rw [hFc _ (by decide)]; omega) (by rw [hFc _ (by decide)]; omega)).symm
  have KF : ∀ c, (c + 1 ≤ 0x10 ∨ 0x2C ≤ c) → c ≤ 0x70 → n'.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => K _ (by rw [hFc _ h2]; omega)
  have hw := C.hwl; have sWR := C.sWR
  have KW : ∀ i, i < wl → n'.mem (wp + BitVec.ofNat 32 i) = M (wp + BitVec.ofNat 32 i) := fun i hi =>
    fr _ (((sWR.sub (c := i) (l := 1) hi).subR (c := 0) (l := 0x20) (by decide)) |> fun h => by
      rw [add_ofNat_zero] at h; exact h.symm)
      ((sWR.sub (c := i) (l := 1) hi).subR (c := 0x30) (l := 28) (by decide) |> fun h => by
        rw [show F + 0xFFFFFFE0 + BitVec.ofNat 32 0x30 = F + BitVec.ofNat 32 0x10 by
          rw [BitVec.add_assoc]; rfl] at h; exact h.symm)
  have hjj := S.hj
  have eC : memLoad32 n'.mem (F + BitVec.ofNat 32 0xC) = memLoad32 M (F + BitVec.ofNat 32 0xC) :=
    memLoad32_congr fun q hq => by rw [add_ofNat_assoc]; exact KF _ (by omega) (by omega)
  have eI : memLoad32 n'.mem (F + BitVec.ofNat 32 0x28) = BitVec.ofNat 32 (j + 1) := by
    rw [e28, S.idx]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega
  refine ⟨u, hsp, by rw [hk _ (by decide), S.s2], by rw [hk _ (by decide), S.s3], by rw [hk _ (by decide), S.s9],
    by rw [hk _ (by decide), S.s8], by rw [hk _ (by decide), S.s5], by rw [hk _ (by decide), S.s6],
    by rw [hk _ (by decide), S.s7], by rw [hk _ (by decide), S.s11], by rw [hk _ (by decide), S.s10],
    by rw [hk _ (by decide), S.gp], by rw [hk _ (by decide), S.tp], S.hpos, S.hc,
    by rw [eC, S.chi], eI, ⟨by omega, by omega⟩,
    by rw [e18, e1C, S.nxt], by rw [show j + 1 + 1 = j + 2 by omega]; exact enx, by rw [show j + 1 + 2 = j + 2 + 1 by omega]; exact er,
    S.len, fun i hi => by rw [KW i (by have := C.hL; have := S.hpos; omega), S.out i hi], S.spec,
    fun x h1 h2 => ?_, fun c c1 c2 => by rw [KF c (Or.inr (by omega)) (by omega), S.slots c c1 c2]⟩
  have hb := sep1_out h1 (by rw [hG]; have := room.2.1; omega)
  rw [hG] at hb
  rw [K x (by omega), S.agree x h1 h2]

end Steps

end C3.RV32
