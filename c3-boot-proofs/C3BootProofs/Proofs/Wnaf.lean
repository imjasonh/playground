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

theorem or5 : ∀ x y : Fin 32, ∀ k : Fin 6, x.val < 2 ^ k.val → y.val % 2 ^ k.val = 0 → x.val ||| y.val = x.val + y.val := by
  decide

theorem or_win {x y k : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ 5) (hx : x < 2 ^ k) (hy : y % 2 ^ k = 0) :
    (x ||| y) % 32 = (x + y) % 32 := by
  have hk32 : 2 ^ k ∣ 32 := by
    rw [show (32 : Nat) = 2 ^ k * 2 ^ (5 - k) by rw [← Nat.pow_add, show k + (5 - k) = 5 by omega]]
    exact Nat.dvd_mul_right _ _
  have hx32 : x < 32 := Nat.lt_of_lt_of_le hx (by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hk2; exact this)
  have hy' : y % 32 % 2 ^ k = 0 := by rw [Nat.mod_mod_of_dvd _ hk32]; exact hy
  have e1 : (x ||| y) % 32 = x ||| y % 32 := by
    have := Nat.or_mod_two_pow (a := x) (b := y) (n := 5)
    rw [show (2 : Nat) ^ 5 = 32 from rfl, Nat.mod_eq_of_lt hx32] at this; exact this
  have e2 := or5 ⟨x, hx32⟩ ⟨y % 32, Nat.mod_lt _ (by decide)⟩ ⟨k, Nat.lt_succ_of_le hk2⟩ hx hy'
  simp only at e2
  rw [e1, e2]; omega

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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the loop head, with `pos < L`, to offset 0x98: `LimbBuffer::get`
leaves limb `pos / 64` current, `s1` holds `pos % 64`, and `s4` the digit's
address. -/
theorem wf_get (C : WfCtx M0 F wp cp wl cn L) (S : WfSt M0 Ms F wp cp wl cn L r0 M n 0x5E pos carry j D) (hlt : pos < L) :
    ∃ n', Steps n n' ∧ WfSt M0 Ms F wp cp wl cn L r0 n'.mem n' 0x98 pos carry (pos / 64) D ∧
      reg n' (9 : Fin 32) = BitVec.ofNat 32 (pos % 64) ∧ reg n' (20 : Fin 32) = wp + BitVec.ofNat 32 pos := by
  have hLw := C.hLw; have hL := C.hL; have hjj := S.hj
  have hc : CodeIn M WF wnafFormCode := C.code S.agree C.cod (by decide) (by decide)
  have hFa := C.room.1
  obtain ⟨n1, d1, u1⟩ := S.st.alu hc wf_at_5e (off' := 0x62) (by decide)
  have S1 := S.step u1 (by decide)
  have s4 : reg n1 (20 : Fin 32) = wp + BitVec.ofNat 32 pos := by rw [u1.upd_eq (by decide), S.s9, S.s6]; rfl
  obtain ⟨n2, d2, u2⟩ := S1.st.notTaken hc 0x66 wf_at_62 (by decide)
    (by rw [S1.s7, S1.s2, wbr_bgeu (by omega) (by omega)]; exact decide_eq_false (by omega))
  have S2 := S1.jmp u2
  obtain ⟨n3, d3, u3⟩ := S2.st.lw hc wf_at_66 (off' := 0x68) (by decide)
    (by rw [S2.hsp]; exact aligned_add hFa (k := 0x28) (by decide))
  have S3 := S2.step u3 (by decide)
  have a0_3 : reg n3 a0 = BitVec.ofNat 32 j := by rw [u3.upd_eq (by decide), S2.hsp]; exact S.idx
  obtain ⟨n4, d4, u4⟩ := S3.st.aluImm hc wf_at_68 (off' := 0x6C) (by decide)
  have S4 := S3.step u4 (by decide)
  have a1_4 : reg n4 a1 = BitVec.ofNat 32 (pos / 64) := by
    rw [u4.upd_eq (by decide), S3.s7]; apply BitVec.eq_of_toNat_eq
    rw [show (6 : Word) = BitVec.ofNat 32 6 from rfl, wv_srl _ 6 (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  obtain ⟨n5, d5, u5⟩ := S4.st.aluImm hc wf_at_6c (off' := 0x70) (by decide)
  have S5 := S4.step u5 (by decide)
  have s1_5 : reg n5 (9 : Fin 32) = BitVec.ofNat 32 (pos % 64) := by
    rw [u5.upd_eq (by decide), u4.upd_ne S3.st.zero _ (by decide), S3.s7]; apply BitVec.eq_of_toNat_eq
    rw [show (0x3F : Word) = BitVec.ofNat 32 (2 ^ 6 - 1) from rfl, wv_and _ 6 (by decide), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega
  obtain ⟨n6, d6, u6⟩ := S5.st.aluImm hc wf_at_70 (off' := 0x74) (by decide)
  have S6 := S5.step u6 (by decide)
  have a2_6 : reg n6 a2 = BitVec.ofNat 32 (j + 1) := by
    rw [u6.upd_eq (by decide), u5.upd_ne S4.st.zero _ (by decide), u4.upd_ne S3.st.zero _ (by decide), a0_3]
    apply BitVec.eq_of_toNat_eq
    rw [show aluEval .add (BitVec.ofNat 32 j) 1 = BitVec.ofNat 32 j + 1 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega
  have a0_6 : reg n6 a0 = BitVec.ofNat 32 j := by
    rw [u6.upd_ne S5.st.zero _ (by decide), u5.upd_ne S4.st.zero _ (by decide), u4.upd_ne S3.st.zero _ (by decide), a0_3]
  have a1_6 : reg n6 a1 = BitVec.ofNat 32 (pos / 64) := by
    rw [u6.upd_ne S5.st.zero _ (by decide), u5.upd_ne S4.st.zero _ (by decide), a1_4]
  obtain ⟨n7, d7, u7⟩ := S6.st.sw hc wf_at_74 (off' := 0x76) (by decide)
    (by rw [S6.hsp]; exact aligned_add hFa (k := 0x34) (by decide))
  rw [S6.hsp, a0_6] at u7
  have S7 := S6.scratch C (k := 0x34) (Or.inl rfl) u7
  obtain ⟨n8, d8, u8⟩ := S7.st.sw (C.code S7.agree C.cod (by decide) (by decide)) wf_at_76 (off' := 0x78) (by decide)
    (by rw [S7.hsp]; exact aligned_add hFa (k := 0x38) (by decide))
  rw [S7.hsp, u7.regs, a2_6] at u8
  have S8 := S7.scratch C (k := 0x38) (Or.inr rfl) u8
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 (memStore32 M (F + BitVec.ofNat 32 0x34) (BitVec.ofNat 32 j)) (F + BitVec.ofNat 32 0x38)
      (BitVec.ofNat 32 (j + 1)) = M2 := ⟨_, rfl⟩
  rw [hM2] at S8
  have hc2 : CodeIn M2 WF wnafFormCode := C.code S8.agree C.cod (by decide) (by decide)
  have m34 : memLoad32 M2 (F + BitVec.ofNat 32 0x34 + 0) = BitVec.ofNat 32 j := by
    rw [add_lit_zero, ← hM2, memLoad32_store32_sep (sep_offsets F (Or.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  have m38 : memLoad32 M2 (F + BitVec.ofNat 32 0x38 + 0) = BitVec.ofNat 32 (j + 1) := by
    rw [add_lit_zero, ← hM2, memLoad32_store32_same]
  obtain ⟨n9, d9, u9⟩ := S8.st.aluImm hc2 wf_at_78 (off' := 0x7A) (by decide)
  have S9 := S8.step u9 (by decide)
  obtain ⟨n10, d10, u10⟩ := S9.st.aluImm hc2 wf_at_7a (off' := 0x7C) (by decide)
  have S10 := S9.step u10 (by decide)
  have r10 : ∀ q, q ≠ a2 → q ≠ a3 → reg n10 q = reg n8 q := fun q h2 h3 => by
    rw [u10.upd_ne S9.st.zero q h3, u9.upd_ne S8.st.zero q h2, u8.regs, u7.regs]
  obtain ⟨n11, d11, u11⟩ := S10.st.notTaken hc2 0x80 wf_at_7c (by decide)
    (by rw [u10.upd_eq (by decide), S9.st.zero, S10.st.zero]; decide)
  have S11 := S10.jmp u11
  obtain ⟨n12, d12, u12⟩ := S11.st.lw hc2 wf_at_80 (off' := 0x82) (by decide)
    (by rw [u11.regs, u10.upd_ne S9.st.zero _ (by decide), u9.upd_eq (by decide), u8.regs, u7.regs, S6.hsp, add_lit_zero]
        exact aligned_add hFa (k := 0x34) (by decide))
  have S12 := S11.step u12 (by decide)
  have a2_10 : reg n10 a2 = F + BitVec.ofNat 32 0x34 := by
    rw [u10.upd_ne S9.st.zero _ (by decide), u9.upd_eq (by decide), u8.regs, u7.regs, S6.hsp]; rfl
  have a4_12 : reg n12 a4 = BitVec.ofNat 32 j := by rw [u12.upd_eq (by decide), u11.regs, a2_10]; exact m34
  obtain ⟨n13, d13, u13⟩ := S12.st.aluImm hc2 wf_at_82 (off' := 0x84) (by decide)
  have S13 := S12.step u13 (by decide)
  obtain ⟨n14, d14, u14⟩ := S13.st.aluImm hc2 wf_at_84 (off' := 0x86) (by decide)
  have S14 := S13.step u14 (by decide)
  have r14 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → reg n14 q = reg n8 q := fun q h2 h3 h4 => by
    rw [u14.upd_ne S13.st.zero q h3, u13.upd_ne S12.st.zero q h2, u12.upd_ne S11.st.zero q h4, u11.regs, r10 q h2 h3]
  have a1_8 : reg n8 a1 = BitVec.ofNat 32 (pos / 64) := by rw [u8.regs, u7.regs, a1_6]
  have a0_8 : reg n8 a0 = BitVec.ofNat 32 j := by rw [u8.regs, u7.regs, a0_6]
  have s1_8 : reg n8 (9 : Fin 32) = BitVec.ofNat 32 (pos % 64) := by rw [u8.regs, u7.regs,
    u6.upd_ne S5.st.zero _ (by decide), s1_5]
  have s4_8 : reg n8 (20 : Fin 32) = wp + BitVec.ofNat 32 pos := by
    rw [u8.regs, u7.regs, u6.upd_ne S5.st.zero _ (by decide), u5.upd_ne S4.st.zero _ (by decide),
      u4.upd_ne S3.st.zero _ (by decide), u3.upd_ne S2.st.zero _ (by decide), u2.regs, s4]
  by_cases hjp : j = pos / 64
  · -- `pos / 64` is the current limb
    obtain ⟨n15, d15, u15⟩ := S14.st.notTaken hc2 0x8A wf_at_86 (by decide)
      (by rw [u14.upd_ne S13.st.zero _ (by decide), u13.upd_ne S12.st.zero _ (by decide), a4_12, r14 _ (by decide)
          (by decide) (by decide), a1_8, wbr_bne (by omega) (by omega), decide_eq_true hjp]; rfl)
    have S15 := S14.jmp u15
    obtain ⟨n16, d16, u16⟩ := S15.st.taken hc2 0x98 wf_at_8a (by decide)
      (by rw [u15.regs, u15.regs, r14 _ (by decide) (by decide) (by decide), r14 _ (by decide) (by decide) (by decide), a0_8, a1_8,
          wbr_bgeu (by omega) (by omega)]; exact decide_eq_true (by omega))
    refine ⟨n16, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
      (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.single d16))))))))))))))), ?_, ?_, ?_⟩
    · rw [u16.mem, ← hjp]; exact S15.jmp u16
    · rw [u16.regs, u15.regs, r14 _ (by decide) (by decide) (by decide), s1_8]
    · rw [u16.regs, u15.regs, r14 _ (by decide) (by decide) (by decide), s4_8]
  · -- `pos / 64` is the next limb
    have hj1 : pos / 64 = j + 1 := by omega
    obtain ⟨n15, d15, u15⟩ := S14.st.taken hc2 0x7C wf_at_86 (by decide)
      (by rw [u14.upd_ne S13.st.zero _ (by decide), u13.upd_ne S12.st.zero _ (by decide), a4_12, r14 _ (by decide)
          (by decide) (by decide), a1_8, wbr_bne (by omega) (by omega), decide_eq_false hjp]; rfl)
    have S15 := S14.jmp u15
    have a3_14 : reg n14 a3 = 4 := by
      rw [u14.upd_eq (by decide), u13.upd_ne S12.st.zero _ (by decide), u12.upd_ne S11.st.zero _ (by decide), u11.regs,
        u10.upd_eq (by decide), S9.st.zero]; rfl
    have a2_14 : reg n14 a2 = F + BitVec.ofNat 32 0x38 := by
      rw [u14.upd_ne S13.st.zero _ (by decide), u13.upd_eq (by decide), u12.upd_ne S11.st.zero _ (by decide), u11.regs,
        a2_10]; exact add_ofNat_assoc F 0x34 4
    obtain ⟨n16, d16, u16⟩ := S15.st.notTaken hc2 0x80 wf_at_7c (by decide)
      (by rw [u15.regs, u15.regs, a3_14, S14.st.zero]; decide)
    have S16 := S15.jmp u16
    obtain ⟨n17, d17, u17⟩ := S16.st.lw hc2 wf_at_80 (off' := 0x82) (by decide)
      (by rw [u16.regs, u15.regs, a2_14, add_lit_zero]; exact aligned_add hFa (k := 0x38) (by decide))
    have S17 := S16.step u17 (by decide)
    have a4_17 : reg n17 a4 = BitVec.ofNat 32 (j + 1) := by rw [u17.upd_eq (by decide), u16.regs, u15.regs, a2_14]; exact m38
    obtain ⟨n18, d18, u18⟩ := S17.st.aluImm hc2 wf_at_82 (off' := 0x84) (by decide)
    have S18 := S17.step u18 (by decide)
    obtain ⟨n19, d19, u19⟩ := S18.st.aluImm hc2 wf_at_84 (off' := 0x86) (by decide)
    have S19 := S18.step u19 (by decide)
    have r19 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → reg n19 q = reg n8 q := fun q h2 h3 h4 => by
      rw [u19.upd_ne S18.st.zero q h3, u18.upd_ne S17.st.zero q h2, u17.upd_ne S16.st.zero q h4, u16.regs, u15.regs,
        r14 q h2 h3 h4]
    obtain ⟨n20, d20, u20⟩ := S19.st.notTaken hc2 0x8A wf_at_86 (by decide)
      (by rw [u19.upd_ne S18.st.zero _ (by decide), u18.upd_ne S17.st.zero _ (by decide), a4_17,
          r19 _ (by decide) (by decide) (by decide), a1_8, wbr_bne (by omega) (by omega), decide_eq_true hj1.symm]; rfl)
    have S20 := S19.jmp u20
    obtain ⟨n21, d21, u21⟩ := S20.st.notTaken hc2 0x8E wf_at_8a (by decide)
      (by rw [u20.regs, u20.regs, r19 _ (by decide) (by decide) (by decide), r19 _ (by decide) (by decide) (by decide),
          a0_8, a1_8, wbr_bgeu (by omega) (by omega)]; exact decide_eq_false (by omega))
    have S21 := S20.jmp u21
    obtain ⟨n22, d22, u22⟩ := S21.st.aluImm hc2 wf_at_8e (off' := 0x90) (by decide)
    have S22 := S21.step u22 (by decide)
    obtain ⟨n23, c23, u23, sp23, k23, e18, e1C, e28, enx, er, fr⟩ := wf_inc C S22.st S22.agree wf_at_90 wf_at_94
      (by decide) (by decide) S22.hsp (by rw [u22.upd_eq (by decide), u21.regs, u20.regs, r19 _ (by decide) (by decide)
        (by decide), u8.regs, u7.regs, S6.hsp]; rfl) (k := j + 2) S22.rest
    have S23 := S22.inc C (by omega) u23 sp23 k23 e18 e1C e28 enx er fr
    refine ⟨n23, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
      (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20
      (.cons d21 (.cons d22 c23))))))))))))))))))))), by rw [hj1]; exact S23, ?_, ?_⟩
    · rw [k23 _ (by decide), u22.upd_ne S21.st.zero _ (by decide), u21.regs, u20.regs,
        r19 _ (by decide) (by decide) (by decide), s1_8]
    · rw [k23 _ (by decide), u22.upd_ne S21.st.zero _ (by decide), u21.regs, u20.regs,
        r19 _ (by decide) (by decide) (by decide), s4_8]

theorem WfSt.keep (S : WfSt M0 Ms F wp cp wl cn L r0 M n off pos carry j D) {n' : Machine} {off' : Nat}
    (u : St M WF n' off' (reg n'))
    (hk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) :
    WfSt M0 Ms F wp cp wl cn L r0 M n' off' pos carry j D :=
  ⟨u, by rw [hk sp (by decide), S.hsp], by rw [hk _ (by decide), S.s2], by rw [hk _ (by decide), S.s3],
    by rw [hk _ (by decide), S.s9], by rw [hk _ (by decide), S.s8], by rw [hk _ (by decide), S.s5],
    by rw [hk _ (by decide), S.s6], by rw [hk _ (by decide), S.s7], by rw [hk _ (by decide), S.s11],
    by rw [hk _ (by decide), S.s10], by rw [hk _ (by decide), S.gp], by rw [hk _ (by decide), S.tp], S.hpos, S.hc,
    S.chi, S.idx, S.hj, S.cur, S.nxt, S.rest, S.len, S.out, S.spec, S.agree, S.slots⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From offset 0x98 to 0xC4: the window, `s0 = (N / 2^pos) % 32`, through
`__lshrdi3` and, when the window crosses a limb, `__ashldi3`. -/
theorem wf_win (C : WfCtx M0 F wp cp wl cn L) (S : WfSt M0 Ms F wp cp wl cn L r0 M n 0x98 pos carry (pos / 64) D)
    (hlt : pos < L) (hs1 : reg n (9 : Fin 32) = BitVec.ofNat 32 (pos % 64)) :
    ∃ n', Steps n n' ∧ WfSt M0 Ms F wp cp wl cn L r0 M n' 0xC4 pos carry (pos / 64) D ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (leN (memBytes M0 cp cn) / 2 ^ pos % 32) ∧
      (∀ q : Fin 32, q.val = 20 → reg n' q = reg n q) := by
  have hLw := C.hLw; have hL := C.hL
  have hc : CodeIn M WF wnafFormCode := C.code S.agree C.cod (by decide) (by decide)
  have hFa := C.room.1
  have hcb := memBytes_lt M0 cp cn
  have hpos : pos = 64 * (pos / 64) + pos % 64 := by omega
  obtain ⟨n1, d1, u1⟩ := S.st.lw hc wf_at_98 (off' := 0x9A) (by decide) (by rw [S.hsp]; exact aligned_add hFa (k := 0x18) (by decide))
  have S1 := S.step u1 (by decide)
  obtain ⟨n2, d2, u2⟩ := S1.st.lw hc wf_at_9a (off' := 0x9C) (by decide) (by rw [S1.hsp]; exact aligned_add hFa (k := 0x1C) (by decide))
  have S2 := S1.step u2 (by decide)
  obtain ⟨n3, d3, u3⟩ := S2.st.alu hc wf_at_9c (off' := 0x9E) (by decide)
  have S3 := S2.step u3 (by decide)
  have r3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n3 q = reg n q := fun q h0 h1 h2 => by
    rw [u3.upd_ne S2.st.zero q h2, u2.upd_ne S1.st.zero q h1, u1.upd_ne S.st.zero q h0]
  obtain ⟨n4, c4, pc4, mem4, regs4⟩ := S3.st.callRa (cb := BitVec.ofNat 32 lshrdi3Address) hc wf_at_9e wf_at_a2
    (by decide) (by decide)
  have r4 := PEnv.reg1 regs4 S3.st.zero
  obtain ⟨n5, c5, pc5, v5, k5, mem5⟩ := lshrdi3_correct n4 (s := pos % 64)
    (by rw [mem4]; exact C.code S3.agree C.lsh (by decide) (by decide)) pc4
    (by rw [r4 _ (by decide), u3.upd_ne S2.st.zero _ (by decide), u2.upd_ne S1.st.zero _ (by decide), u1.upd_eq (by decide)])
    (by rw [r4 _ (by decide), u3.upd_ne S2.st.zero _ (by decide), u2.upd_eq (by decide)])
    (by rw [r4 _ (by decide), u3.upd_eq (by decide), S2.st.zero, u2.upd_ne S1.st.zero _ (by decide),
      u1.upd_ne S.st.zero _ (by decide), hs1]; exact BitVec.zero_add _) (by omega)
    (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at WF (by decide) (0x9E + 8) (by decide)))
  rw [mem4] at mem5
  rw [S.hsp, S1.hsp] at v5
  have hcur : (memLoad32 M (F + 24)).toNat + 2 ^ 32 * (memLoad32 M (F + 28)).toNat = lmb (memBytes M0 cp cn) (pos / 64) :=
    S.cur
  rw [hcur] at v5
  have hV : (reg n5 a0).toNat = lmb (memBytes M0 cp cn) (pos / 64) / 2 ^ (pos % 64) % 2 ^ 32 := by
    have := (reg n5 a1).isLt; have := (reg n5 a0).isLt; omega
  have hk5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n q := fun q hq => by
    rw [k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      r4 q (by revert hq; revert q; decide), r3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide)]
  have S5 := S3.keep (n' := n5) (off' := 0xA6) ⟨by rw [pc5], mem5, fun _ => rfl⟩ (fun q hq => by
    rw [hk5 q (by revert hq; revert q; decide), ← r3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)])
  obtain ⟨n6, d6, u6⟩ := S5.st.alu hc wf_at_a6 (off' := 0xA8) (by decide)
  have S6 := S5.step u6 (by decide)
  have s0_6 : (reg n6 (8 : Fin 32)).toNat = lmb (memBytes M0 cp cn) (pos / 64) / 2 ^ (pos % 64) % 2 ^ 32 := by
    rw [u6.upd_eq (by decide), S5.st.zero, show aluEval .add 0 (reg n5 a0) = reg n5 a0 from BitVec.zero_add _]; exact hV
  have s1_6 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 (pos % 64) := by
    rw [u6.upd_ne S5.st.zero _ (by decide), hk5 _ (by decide), hs1]
  have s4_6 : reg n6 (20 : Fin 32) = reg n (20 : Fin 32) := by
    rw [u6.upd_ne S5.st.zero _ (by decide), hk5 _ (by decide)]
  -- both paths meet at 0xC2, where `andi` keeps the window's five bits
  have fin : ∀ {n' : Machine}, Steps n n' → WfSt M0 Ms F wp cp wl cn L r0 M n' 0xC2 pos carry (pos / 64) D →
      (reg n' (8 : Fin 32)).toNat % 32 = leN (memBytes M0 cp cn) / 2 ^ pos % 32 → reg n' (20 : Fin 32) = reg n 20 →
      ∃ n'', Steps n n'' ∧ WfSt M0 Ms F wp cp wl cn L r0 M n'' 0xC4 pos carry (pos / 64) D ∧
        reg n'' (8 : Fin 32) = BitVec.ofNat 32 (leN (memBytes M0 cp cn) / 2 ^ pos % 32) ∧
        (∀ q : Fin 32, q.val = 20 → reg n'' q = reg n q) := fun {n'} cs S' h8 h20 => by
    obtain ⟨n7, d7, u7⟩ := S'.st.aluImm hc wf_at_c2 (off' := 0xC4) (by decide)
    refine ⟨n7, cs.trans (.single d7), S'.step u7 (by decide), ?_, fun q hq => ?_⟩
    · rw [u7.upd_eq (by decide)]; apply BitVec.eq_of_toNat_eq
      rw [show (0x1F : Word) = BitVec.ofNat 32 (2 ^ 5 - 1) from rfl, wv_and _ 5 (by decide), BitVec.toNat_ofNat,
        show (2 : Nat) ^ 5 = 32 from rfl, h8]
      omega
    · obtain rfl : q = 20 := Fin.ext hq
      rw [u7.upd_ne S'.st.zero _ (by decide), h20]
  have cs6 : Steps n n6 := .cons d1 (.cons d2 (.cons d3 (c4.trans (c5.trans (.single d6)))))
  have hlmb := lmb_lt hcb (pos / 64)
  by_cases hb : pos % 64 < 59
  · obtain ⟨n7, d7, u7⟩ := S6.st.taken hc 0xC2 wf_at_a8 (by decide)
      (by rw [s1_6, S6.s8, wbr_bltu (by omega) (by decide)]; exact decide_eq_true hb)
    refine fin (cs6.trans (.single d7)) (S6.jmp u7) ?_ (by rw [u7.regs, s4_6])
    rw [u7.regs, s0_6, Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 32)]
    have := win_lo hcb (j := pos / 64) (b := pos % 64) hb
    rw [← hpos] at this; exact this.symm
  · obtain ⟨n7, d7, u7⟩ := S6.st.notTaken hc 0xAC wf_at_a8 (by decide)
      (by rw [s1_6, S6.s8, wbr_bltu (by omega) (by decide)]; exact decide_eq_false hb)
    have S7 := S6.jmp u7
    obtain ⟨n8, d8, u8⟩ := S7.st.lw hc wf_at_ac (off' := 0xAE) (by decide)
      (by rw [S7.hsp]; exact aligned_add hFa (k := 0x20) (by decide))
    have S8 := S7.step u8 (by decide)
    obtain ⟨n9, d9, u9⟩ := S8.st.lw hc wf_at_ae (off' := 0xB0) (by decide)
      (by rw [S8.hsp]; exact aligned_add hFa (k := 0x24) (by decide))
    have S9 := S8.step u9 (by decide)
    obtain ⟨n10, d10, u10⟩ := S9.st.alu hc wf_at_b0 (off' := 0xB4) (by decide)
    have S10 := S9.step u10 (by decide)
    obtain ⟨n11, d11, u11⟩ := S10.st.aluImm hc wf_at_b4 (off' := 0xB8) (by decide)
    have S11 := S10.step u11 (by decide)
    have a2_11 : reg n11 a2 = BitVec.ofNat 32 (64 - pos % 64) := by
      rw [u11.upd_eq (by decide), u10.upd_eq (by decide), S9.st.zero, S9.s7]; apply BitVec.eq_of_toNat_eq
      rw [show (0x3F : Word) = BitVec.ofNat 32 (2 ^ 6 - 1) from rfl, wv_and _ 6 (by decide),
        show aluEval .sub 0 (BitVec.ofNat 32 pos) = 0 - BitVec.ofNat 32 pos from rfl, BitVec.toNat_sub, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl]
      omega
    have r11 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n11 q = reg n7 q := fun q h0 h1 h2 => by
      rw [u11.upd_ne S10.st.zero q h2, u10.upd_ne S9.st.zero q h2, u9.upd_ne S8.st.zero q h1, u8.upd_ne S7.st.zero q h0]
    obtain ⟨n12, c12, pc12, mem12, regs12⟩ := S11.st.callRa (cb := BitVec.ofNat 32 ashldi3Address) hc wf_at_b8 wf_at_bc
      (by decide) (by decide)
    have r12 := PEnv.reg1 regs12 S11.st.zero
    obtain ⟨n13, c13, pc13, v13, k13, mem13⟩ := ashldi3_correct n12 (s := 64 - pos % 64)
      (by rw [mem12]; exact C.code S11.agree C.ash (by decide) (by decide)) pc12
      (by rw [r12 _ (by decide), u11.upd_ne S10.st.zero _ (by decide), u10.upd_ne S9.st.zero _ (by decide),
        u9.upd_ne S8.st.zero _ (by decide), u8.upd_eq (by decide)])
      (by rw [r12 _ (by decide), u11.upd_ne S10.st.zero _ (by decide), u10.upd_ne S9.st.zero _ (by decide),
        u9.upd_eq (by decide)])
      (by rw [r12 _ (by decide), a2_11]) (by omega)
      (by rw [regs12]; simp +decide [upd]) (even_clear _ (even_at WF (by decide) (0xB8 + 8) (by decide)))
    rw [mem12] at mem13
    rw [S7.hsp, S8.hsp] at v13
    have hnx : (memLoad32 M (F + 32)).toNat + 2 ^ 32 * (memLoad32 M (F + 36)).toNat =
        lmb (memBytes M0 cp cn) (pos / 64 + 1) := S.nxt
    rw [hnx] at v13
    have hW : (reg n13 a0).toNat = lmb (memBytes M0 cp cn) (pos / 64 + 1) * 2 ^ (64 - pos % 64) % 2 ^ 64 % 2 ^ 32 := by
      have := (reg n13 a1).isLt; have := (reg n13 a0).isLt; omega
    have hk13 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n13 q = reg n6 q := fun q hq => by
      rw [k13 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
        r12 q (by revert hq; revert q; decide), r11 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide), u7.regs]
    have S13 := S11.keep (n' := n13) (off' := 0xC0) ⟨by rw [pc13], mem13, fun _ => rfl⟩ (fun q hq => by
      rw [hk13 q (by revert hq; revert q; decide), ← u7.regs, ← r11 q (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide)])
    obtain ⟨n14, d14, u14⟩ := S13.st.alu hc wf_at_c0 (off' := 0xC2) (by decide)
    refine fin (cs6.trans (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (c12.trans (c13.trans (.single d14)))))))))
      (S13.step u14 (by decide)) ?_ (by rw [u14.upd_ne S13.st.zero _ (by decide), hk13 _ (by decide), s4_6])
    rw [u14.upd_eq (by decide), hk13 _ (by decide)]
    show (reg n6 (8 : Fin 32) ||| reg n13 a0).toNat % 32 = _
    rw [BitVec.toNat_or, s0_6, hW]
    have hk1 : 1 ≤ 64 - pos % 64 := by omega
    have hk2 : 64 - pos % 64 ≤ 5 := by omega
    have hVlt : lmb (memBytes M0 cp cn) (pos / 64) / 2 ^ (pos % 64) < 2 ^ (64 - pos % 64) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add, show 64 - pos % 64 + pos % 64 = 64 by omega]
      exact hlmb
    have hV32 : lmb (memBytes M0 cp cn) (pos / 64) / 2 ^ (pos % 64) % 2 ^ 32 = lmb (memBytes M0 cp cn) (pos / 64) / 2 ^ (pos % 64) :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hVlt (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hV32, or_win hk1 hk2 hVlt (by
      rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 64 - pos % 64 ≤ 32)),
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 64 - pos % 64 ≤ 64)), Nat.mul_mod_left])]
    have := win_hi hcb (j := pos / 64) (b := pos % 64) (by omega) (by omega)
    rw [← hpos] at this; rw [this]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 32), Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 64),
      ← Nat.add_mod]

theorem wst8 {M : Word → BitVec 8} {a x : Word} {v : BitVec 8} (h : Sep a 1 x 1) : memStore8 M a v x = M x := by
  have ne : ¬ x = a := fun e => h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])
  simp only [memStore8, ne, ↓reduceIte]

theorem wst8_same {M : Word → BitVec 8} {a : Word} {v : BitVec 8} : memStore8 M a v a = v := by
  simp only [memStore8, ↓reduceIte]

theorem getD_app_l {l₁ l₂ : List Int} {i : Nat} (h : i < l₁.length) : (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_r {l₁ l₂ : List Int} {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- `M` with digit `d` stored at index `pos` of the digit buffer. -/
abbrev wput (M : Word → BitVec 8) (wp : Word) (pos : Nat) (d : Int) : Word → BitVec 8 :=
  memStore8 M (wp + BitVec.ofNat 32 pos) (BitVec.ofNat 8 (digB d))

/-- The memory half of `WfSt`, with `k` digits written. -/
structure WfMem (M0 Ms : Word → BitVec 8) (F wp cp : Word) (wl cn : Nat) (M : Word → BitVec 8) (j k : Nat)
    (D : List Int) : Prop where
  idx : memLoad32 M (F + BitVec.ofNat 32 0x28) = BitVec.ofNat 32 j
  cur : (memLoad32 M (F + BitVec.ofNat 32 0x18)).toNat + 2 ^ 32 * (memLoad32 M (F + BitVec.ofNat 32 0x1C)).toNat =
    lmb (memBytes M0 cp cn) j
  nxt : (memLoad32 M (F + BitVec.ofNat 32 0x20)).toNat + 2 ^ 32 * (memLoad32 M (F + BitVec.ofNat 32 0x24)).toNat =
    lmb (memBytes M0 cp cn) (j + 1)
  rest : RestAt M (F + BitVec.ofNat 32 0x10) cp cn (j + 2)
  len : D.length = k
  out : ∀ i, i < k → M (wp + BitVec.ofNat 32 i) = BitVec.ofNat 8 (digB (D.getD i 0))
  agree : ∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → Sep wp wl x 1 → M x = M0 x
  slots : ∀ k, 0x3C ≤ k → k < 0x70 → M (F + BitVec.ofNat 32 k) = Ms (F + BitVec.ofNat 32 k)

theorem WfSt.mem (S : WfSt M0 Ms F wp cp wl cn L r0 M n off pos carry j D) : WfMem M0 Ms F wp cp wl cn M j pos D :=
  ⟨S.idx, S.cur, S.nxt, S.rest, S.len, S.out, S.agree, S.slots⟩

/-- Ranges apart from a store at `F + c` of `l` bytes inside the frame. -/
theorem WfCtx.fsep (C : WfCtx M0 F wp cp wl cn L) {c l : Nat} (hc : c + l ≤ 0x70) :
    (∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → Sep (F + BitVec.ofNat 32 c) l x 1) ∧
    (∀ i, i < wl → Sep (F + BitVec.ofNat 32 c) l (wp + BitVec.ofNat 32 i) 1) ∧
    (∀ d, d < 0x70 → (c + l ≤ d ∨ d + 1 ≤ c) → Sep (F + BitVec.ofNat 32 c) l (F + BitVec.ofNat 32 d) 1) := by
  have room := C.room; have hFd := C.hFd; unfold dramEnd at hFd
  have sR : ∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → Sep (F + BitVec.ofNat 32 c) l x 1 := fun x hx => by
    have := hx.symm.subR (c := 0x20 + c) (l := l) (by omega)
    rw [show F + 0xFFFFFFE0 + BitVec.ofNat 32 (0x20 + c) = F + BitVec.ofNat 32 c by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this
    exact this.symm
  exact ⟨sR, fun i hi => sR _ (C.sWR.sub (c := i) (l := 1) hi).symm,
    fun d hd h => sep_offsets F (by omega) (by omega) (by omega)⟩

theorem WfMem.frame (W : WfMem M0 Ms F wp cp wl cn M j k D) {M' : Word → BitVec 8} (hk : k ≤ wl)
    (hF : ∀ c, 0x10 ≤ c → c < 0x2C → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c))
    (hW : ∀ i, i < wl → M' (wp + BitVec.ofNat 32 i) = M (wp + BitVec.ofNat 32 i))
    (hA : ∀ x, Sep (F + 0xFFFFFFE0) 0x90 x 1 → M' x = M x)
    (hS : ∀ c, 0x3C ≤ c → c < 0x70 → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)) :
    WfMem M0 Ms F wp cp wl cn M' j k D := by
  have L : ∀ c, 0x10 ≤ c → c + 4 ≤ 0x2C → memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun q hq => by rw [add_ofNat_assoc]; exact hF _ (by omega) (by omega)
  have e4 : F + BitVec.ofNat 32 0x10 + 4 = F + BitVec.ofNat 32 0x14 := add_ofNat_assoc F 0x10 4
  have hRest : RestAt M' (F + BitVec.ofNat 32 0x10) cp cn (j + 2) := by
    have hr := W.rest
    unfold RestAt at hr ⊢
    rw [e4, L 0x10 (by decide) (by decide), L 0x14 (by decide) (by decide)]; rw [e4] at hr; exact hr
  exact ⟨by rw [L _ (by decide) (by decide), W.idx],
    by rw [L _ (by decide) (by decide), L _ (by decide) (by decide), W.cur],
    by rw [L _ (by decide) (by decide), L _ (by decide) (by decide), W.nxt], hRest, W.len,
    fun i hi => by rw [hW i (by omega), W.out i hi], fun x h1 h2 => by rw [hA x h1, W.agree x h1 h2],
    fun c c1 c2 => by rw [hS c c1 c2, W.slots c c1 c2]⟩

theorem WfMem.st32 (C : WfCtx M0 F wp cp wl cn L) (W : WfMem M0 Ms F wp cp wl cn M j k D) (hk : k ≤ wl) {c : Nat}
    (hc : c + 4 ≤ 0x10 ∨ (0x2C ≤ c ∧ c + 4 ≤ 0x3C)) (v : Word) :
    WfMem M0 Ms F wp cp wl cn (memStore32 M (F + BitVec.ofNat 32 c) v) j k D := by
  obtain ⟨sA, sW, sF⟩ := C.fsep (c := c) (l := 4) (by omega)
  exact W.frame hk (fun d h1 h2 => memStore32_get_sep (sF d (by omega) (by omega)))
    (fun i hi => memStore32_get_sep (sW i hi)) (fun x hx => memStore32_get_sep (sA x hx))
    (fun d h1 h2 => memStore32_get_sep (sF d h2 (by omega)))

theorem WfMem.st8 (C : WfCtx M0 F wp cp wl cn L) (W : WfMem M0 Ms F wp cp wl cn M j k D) (hk : k ≤ wl) {c : Nat}
    (hc : c + 1 ≤ 0x10 ∨ (0x2C ≤ c ∧ c + 1 ≤ 0x3C)) (v : BitVec 8) :
    WfMem M0 Ms F wp cp wl cn (memStore8 M (F + BitVec.ofNat 32 c) v) j k D := by
  obtain ⟨sA, sW, sF⟩ := C.fsep (c := c) (l := 1) (by omega)
  exact W.frame hk (fun d h1 h2 => wst8 (sF d (by omega) (by omega)))
    (fun i hi => wst8 (sW i hi)) (fun x hx => wst8 (sA x hx)) (fun d h1 h2 => wst8 (sF d h2 (by omega)))

/-- Storing digit `d` at index `k` of the digit buffer. -/
theorem WfMem.put (C : WfCtx M0 F wp cp wl cn L) (W : WfMem M0 Ms F wp cp wl cn M j k D) (hp : k < wl) (d : Int) :
    WfMem M0 Ms F wp cp wl cn (wput M wp k d) j (k + 1) (D ++ [d]) ∧
    ∀ c, c + 4 ≤ 0x70 → memLoad32 (wput M wp k d) (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) := by
  unfold wput
  have room := C.room; have hFd := C.hFd; unfold dramEnd at hFd
  have sWR := C.sWR
  have sPF : ∀ c, c < 0x70 → Sep (wp + BitVec.ofNat 32 k) 1 (F + BitVec.ofNat 32 c) 1 := fun c hc' => by
    have := (sWR.sub (c := k) (l := 1) hp).subR (c := 0x20 + c) (l := 1) (by omega)
    rwa [show F + 0xFFFFFFE0 + BitVec.ofNat 32 (0x20 + c) = F + BitVec.ofNat 32 c by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this
  have LF : ∀ c, c + 4 ≤ 0x70 → memLoad32 (memStore8 M (wp + BitVec.ofNat 32 k) (BitVec.ofNat 8 (digB d)))
      (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) := fun c hc' =>
    memLoad32_congr fun q hq => by rw [add_ofNat_assoc]; exact wst8 (sPF _ (by omega))
  have hlen := W.len
  have hLw := C.hLw
  have e4 : F + BitVec.ofNat 32 0x10 + 4 = F + BitVec.ofNat 32 0x14 := add_ofNat_assoc F 0x10 4
  have hRest : RestAt (memStore8 M (wp + BitVec.ofNat 32 k) (BitVec.ofNat 8 (digB d))) (F + BitVec.ofNat 32 0x10)
      cp cn (j + 2) := by
    have hr := W.rest
    unfold RestAt at hr ⊢
    rw [e4, LF 0x10 (by decide), LF 0x14 (by decide)]; rw [e4] at hr; exact hr
  refine ⟨⟨by rw [LF _ (by decide), W.idx], by rw [LF _ (by decide), LF _ (by decide), W.cur],
    by rw [LF _ (by decide), LF _ (by decide), W.nxt], hRest, by simp [hlen], fun i hi => ?_, fun x h1 h2 => ?_,
    fun c c1 c2 => ?_⟩, LF⟩
  · rcases Nat.lt_or_ge i k with h | h
    · rw [wst8 (sep_offsets wp (c := k) (n := 1) (d := i) (k := 1) (Or.inr (by omega)) (by omega) (by omega)),
        W.out i h, getD_app_l (by omega)]
    · obtain rfl : i = k := by omega
      rw [wst8_same, getD_app_r (by omega), hlen, Nat.sub_self]; rfl
  · rw [wst8 ((h2.symm.subR (c := k) (l := 1) hp).symm), W.agree x h1 h2]
  · rw [wst8 (sPF c (by omega)), W.slots c c1 c2]

theorem wadd1 (k : Nat) : aluEval .add (BitVec.ofNat 32 k) 1 = BitVec.ofNat 32 (k + 1) := by
  show BitVec.ofNat 32 k + BitVec.ofNat 32 1 = _; rw [BitVec.ofNat_add_ofNat]

theorem wsub1 {k : Nat} (hk : 1 ≤ k) (hk2 : k < 2 ^ 32) :
    aluEval .add (BitVec.ofNat 32 k) 0xFFFFFFFF = BitVec.ofNat 32 (k - 1) := by
  show BitVec.ofNat 32 k + BitVec.ofNat 32 0xFFFFFFFF = _; rw [BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem wnafGo_even {N L f pos carry : Nat} (hlt : pos < L) (h : (carry + N / 2 ^ pos % 32) % 2 = 0) :
    wnafGo N L (f + 1) pos carry = 0 :: wnafGo N L f (pos + 1) carry := by
  simp only [wnafGo, if_pos hlt, if_pos h]

/-- The window `carry + bits` as the value of `a0` at 0xC8. -/
theorem wf_a0 {s0 s10 : Word} {w c : Nat} (h0 : s0 = BitVec.ofNat 32 w) (h1 : s10 = BitVec.ofNat 32 c) :
    aluEval .add s0 s10 = BitVec.ofNat 32 (c + w) := by
  rw [h0, h1]; show BitVec.ofNat 32 w + BitVec.ofNat 32 c = _; rw [BitVec.ofNat_add_ofNat, Nat.add_comm]

theorem wf_par {w : Nat} (hw : w < 2 ^ 32) : (aluEval .and (BitVec.ofNat 32 w) 0x1).toNat = w % 2 := by
  rw [show (0x1 : Word) = BitVec.ofNat 32 (2 ^ 1 - 1) from rfl, wv_and _ 1 (by decide), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hw]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- An even window: digit 0 at `pos`, then back to the loop head at `pos + 1`. -/
theorem wf_even (C : WfCtx M0 F wp cp wl cn L) (S : WfSt M0 Ms F wp cp wl cn L r0 M n 0xC4 pos carry (pos / 64) D)
    (hlt : pos < L) (h8 : reg n (8 : Fin 32) = BitVec.ofNat 32 (leN (memBytes M0 cp cn) / 2 ^ pos % 32))
    (h20 : reg n (20 : Fin 32) = wp + BitVec.ofNat 32 pos)
    (hev : (carry + leN (memBytes M0 cp cn) / 2 ^ pos % 32) % 2 = 0) :
    ∃ n', Steps n n' ∧
      WfSt M0 Ms F wp cp wl cn L r0 (wput M wp pos 0) n' 0x5E (pos + 1) carry (pos / 64) (D ++ [0]) := by
  have hLw := C.hLw; have hL := C.hL; have hcar := S.hc
  have hc : CodeIn M WF wnafFormCode := C.code S.agree C.cod (by decide) (by decide)
  have hw : leN (memBytes M0 cp cn) / 2 ^ pos % 32 < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨n1, d1, u1⟩ := S.st.alu hc wf_at_c4 (off' := 0xC8) (by decide)
  have S1 := S.step u1 (by decide)
  have a0_1 := u1.upd_eq (by decide); rw [wf_a0 h8 S.s10] at a0_1
  obtain ⟨n2, d2, u2⟩ := S1.st.aluImm hc wf_at_c8 (off' := 0xCC) (by decide)
  have S2 := S1.step u2 (by decide)
  have a1_2 : reg n2 a1 = 0 := by
    rw [u2.upd_eq (by decide), a0_1]; apply BitVec.eq_of_toNat_eq
    rw [wf_par (by omega), hev]; rfl
  obtain ⟨n3, d3, u3⟩ := S2.st.notTaken hc 0xCE wf_at_cc (by decide) (by rw [a1_2, S2.st.zero]; rfl)
  have S3 := S2.jmp u3
  obtain ⟨n4, d4, u4⟩ := S3.st.notTaken hc 0xD2 wf_at_ce (by decide)
    (by rw [S3.s6, S3.s3, wbr_bgeu (by omega) (by omega)]; exact decide_eq_false (by omega))
  have S4 := S3.jmp u4
  obtain ⟨n5, d5, u5⟩ := S4.st.sb hc wf_at_d2 (off' := 0xD6) (by decide)
  have r4 : ∀ q, q ≠ a0 → q ≠ a1 → reg n4 q = reg n q := fun q h0 h1 => by
    rw [u4.regs, u3.regs, u2.upd_ne S1.st.zero q h1, u1.upd_ne S.st.zero q h0]
  have e5 : memStore8 M (reg n4 (20 : Fin 32) + 0) ((reg n4 0).extractLsb' 0 8) = wput M wp pos 0 := by
    rw [r4 _ (by decide) (by decide), h20, add_lit_zero, S4.st.zero]; rfl
  rw [e5] at u5
  have W := (S.mem.put C (by omega) 0).1
  have hc5 : CodeIn (wput M wp pos 0) WF wnafFormCode := C.code W.agree C.cod (by decide) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.aluImm hc5 wf_at_d6 (off' := 0xD8) (by decide)
  obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hc5 wf_at_d8 (off' := 0xDA) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.self.aluImm hc5 wf_at_da (off' := 0xDC) (by decide)
  obtain ⟨n9, d9, u9⟩ := u8.self.aluImm hc5 wf_at_dc (off' := 0xDE) (by decide)
  obtain ⟨n10, d10, u10⟩ := u9.self.jump hc5 wf_at_de (off' := 0x5E) (by decide) (by rw [u9.self.pc]; decide)
  have K : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ (21 : Fin 32) → q ≠ (22 : Fin 32) → q ≠ (23 : Fin 32) →
      q ≠ (27 : Fin 32) → reg n10 q = reg n q := fun q h0 h1 h21 h22 h23 h27 => by
    rw [u10.regs, u9.upd_ne u8.self.zero q h27, u8.upd_ne u7.self.zero q h21, u7.upd_ne u6.self.zero q h23,
      u6.upd_ne u5.zero q h22, r4 q h0 h1]
  have spec : ∃ f, L - (pos + 1) + 1 ≤ f ∧
      (D ++ [0]) ++ wnafGo (leN (memBytes M0 cp cn)) L f (pos + 1) carry = wnafSpec (memBytes M0 cp cn) L := by
    obtain ⟨f, hf, e⟩ := S.spec
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    refine ⟨f', by omega, ?_⟩
    rw [wnafGo_even hlt hev] at e; rw [← e]; simp
  refine ⟨n10, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.single d10))))))))), ⟨u10.self, by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), S.hsp],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), S.s2],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), S.s3],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), S.s9],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), S.s8], ?_, ?_, ?_, ?_,
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), S.s10],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), S.gp],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), S.tp], by omega, hcar,
    by rw [(S.mem.put C (by omega) 0).2 _ (by decide), S.chi], W.idx, ⟨by omega, by omega⟩, W.cur, W.nxt, W.rest,
    W.len, W.out, spec, W.agree, W.slots⟩⟩
  · rw [u10.regs, u9.upd_ne u8.self.zero _ (by decide), u8.upd_eq (by decide), u7.upd_ne u6.self.zero _ (by decide),
      u6.upd_ne u5.zero _ (by decide), r4 _ (by decide) (by decide), S.s5, wadd1]
  · rw [u10.regs, u9.upd_ne u8.self.zero _ (by decide), u8.upd_ne u7.self.zero _ (by decide),
      u7.upd_ne u6.self.zero _ (by decide), u6.upd_eq (by decide), r4 _ (by decide) (by decide), S.s6, wadd1]
  · rw [u10.regs, u9.upd_ne u8.self.zero _ (by decide), u8.upd_ne u7.self.zero _ (by decide),
      u7.upd_eq (by decide), u6.upd_ne u5.zero _ (by decide), r4 _ (by decide) (by decide), S.s7, wadd1]
  · rw [u10.regs, u9.upd_eq (by decide), u8.upd_ne u7.self.zero _ (by decide),
      u7.upd_ne u6.self.zero _ (by decide), u6.upd_ne u5.zero _ (by decide), r4 _ (by decide) (by decide), S.s11,
      wsub1 (by omega) (by omega), Nat.sub_sub]

/-- The carry out of an odd window `w`. -/
def wc (w : Nat) : Nat := if w < 16 then 0 else 1

/-- The signed digit of an odd window `w`. -/
def wd (w : Nat) : Int := if w < 16 then (w : Int) else (w : Int) - 32

/-- The positions an odd window at `pos` covers. -/
def wskip (L pos w : Nat) : Nat := min 5 (L - wc w - pos)

theorem wnafGo_odd {N L f pos carry : Nat} (hlt : pos < L) (h : (carry + N / 2 ^ pos % 32) % 2 = 1) :
    wnafGo N L (f + 1) pos carry =
      (wd (carry + N / 2 ^ pos % 32) :: List.replicate (wskip L pos (carry + N / 2 ^ pos % 32) - 1) 0) ++
        wnafGo N L f (pos + wskip L pos (carry + N / 2 ^ pos % 32)) (wc (carry + N / 2 ^ pos % 32)) := by
  simp only [wnafGo, if_pos hlt, h, wd, wc, wskip]; rfl

/-- A carry out leaves at least four bits above `pos`, so an odd window always
moves `pos`. -/
theorem wc_room {N L pos carry : Nat} (hN : N < 2 ^ L) (hc : carry ≤ 1) (hlt : pos < L)
    (h : wc (carry + N / 2 ^ pos % 32) = 1) : pos + 2 ≤ L := by
  unfold wc at h
  split at h
  · exact absurd h (by decide)
  · rename_i h1
    have h14 : 15 ≤ N / 2 ^ pos % 32 := by omega
    have h15 : 15 ≤ N / 2 ^ pos := Nat.le_trans h14 (Nat.mod_le _ _)
    have h2 := (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).1 h15
    refine Nat.not_lt.1 fun h3 => ?_
    have : 2 ^ L ≤ 2 ^ (pos + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at this
    omega

theorem wskip_pos {N L pos carry : Nat} (hN : N < 2 ^ L) (hc : carry ≤ 1) (hlt : pos < L) :
    1 ≤ wskip L pos (carry + N / 2 ^ pos % 32) := by
  unfold wskip
  have : wc (carry + N / 2 ^ pos % 32) ≤ 1 := by unfold wc; split <;> decide
  rcases Nat.lt_or_ge (wc (carry + N / 2 ^ pos % 32)) 1 with h | h
  · omega
  · have := wc_room hN hc hlt (by omega); omega

theorem wsltu {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    aluEval .sltu (BitVec.ofNat 32 x) (BitVec.ofNat 32 y) = if x < y then 1 else 0 := by
  show (if (BitVec.ofNat 32 x).ult (BitVec.ofNat 32 y) then 1 else 0) = _
  have : (BitVec.ofNat 32 x).ult (BitVec.ofNat 32 y) = decide (x < y) := by
    simp [BitVec.ult, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rw [this]; by_cases h : x < y <;> simp [h]

/-- The byte the odd branch stores for window `w`. -/
theorem wd_byte : ∀ w : Fin 33, (BitVec.ofNat 32 w.val + ((0 - BitVec.ofNat 32 (wc w.val)) &&& 0xE0)).extractLsb' 0 8 =
    BitVec.ofNat 8 (digB (wd w.val)) := by decide

theorem wc_xor : ∀ w : Fin 33, ((if w.val < 16 then (1 : Word) else 0) ^^^ 1) = BitVec.ofNat 32 (wc w.val) := by decide

/-- The registers the loop never writes. -/
structure WfR (F wp : Word) (wl L : Nat) (r0 : Fin 32 → Word) (n : Machine) : Prop where
  hsp : reg n sp = F
  s2 : reg n (18 : Fin 32) = BitVec.ofNat 32 L
  s3 : reg n (19 : Fin 32) = BitVec.ofNat 32 wl
  s9 : reg n (25 : Fin 32) = wp
  s8 : reg n (24 : Fin 32) = BitVec.ofNat 32 59
  gp : reg n (3 : Fin 32) = r0 3
  tp : reg n (4 : Fin 32) = r0 4

theorem WfSt.r (S : WfSt M0 Ms F wp cp wl cn L r0 M n off pos carry j D) : WfR F wp wl L r0 n :=
  ⟨S.hsp, S.s2, S.s3, S.s9, S.s8, S.gp, S.tp⟩

theorem WfR.keep (R : WfR F wp wl L r0 n) {n' : Machine}
    (hk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 24, 25] → reg n' q = reg n q) : WfR F wp wl L r0 n' :=
  ⟨by rw [hk _ (by decide), R.hsp], by rw [hk _ (by decide), R.s2], by rw [hk _ (by decide), R.s3],
    by rw [hk _ (by decide), R.s9], by rw [hk _ (by decide), R.s8], by rw [hk _ (by decide), R.gp],
    by rw [hk _ (by decide), R.tp]⟩

theorem WfR.upd (R : WfR F wp wl L r0 n) {M : Word → BitVec 8} {n' : Machine} {off : Nat} {rd : Fin 32} {v : Word}
    (u : St M WF n' off (upd (reg n) rd v)) (hz : reg n 0 = 0) (hrd : rd.val ∉ [2, 3, 4, 18, 19, 24, 25]) :
    WfR F wp wl L r0 n' :=
  R.keep fun q hq => u.upd_ne hz q (fun e => hrd (by rw [← e]; exact hq))

theorem WfR.jmp (R : WfR F wp wl L r0 n) {M : Word → BitVec 8} {n' : Machine} {off : Nat}
    (u : St M WF n' off (reg n)) : WfR F wp wl L r0 n' :=
  R.keep fun q _ => u.regs q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- An odd window, from 0xC4 to the return from `expect` at 0x11A: the digit
stored at `pos`, and the carry out in `s10` and `a0`. -/
theorem wf_odd1 (C : WfCtx M0 F wp cp wl cn L) (S : WfSt M0 Ms F wp cp wl cn L r0 M n 0xC4 pos carry (pos / 64) D)
    (hlt : pos < L) {b : Nat} (hb32 : b < 32) (h8 : reg n (8 : Fin 32) = BitVec.ofNat 32 b)
    (h20 : reg n (20 : Fin 32) = wp + BitVec.ofNat 32 pos) (hodd : (carry + b) % 2 = 1) :
    ∃ n' M1, Steps n n' ∧ St M1 WF n' 0x11A (reg n') ∧ WfR F wp wl L r0 n' ∧
      WfMem M0 Ms F wp cp wl cn M1 (pos / 64) (pos + 1) (D ++ [wd (carry + b)]) ∧
      memLoad32 M1 (F + BitVec.ofNat 32 0xC) = 0 ∧
      reg n' a0 = BitVec.ofNat 32 (wc (carry + b)) ∧ reg n' (26 : Fin 32) = BitVec.ofNat 32 (wc (carry + b)) ∧
      reg n' (21 : Fin 32) = BitVec.ofNat 32 (pos + 1) ∧ reg n' (22 : Fin 32) = BitVec.ofNat 32 pos ∧
      reg n' (23 : Fin 32) = BitVec.ofNat 32 pos ∧ reg n' (27 : Fin 32) = BitVec.ofNat 32 (L - pos) := by
  have hLw := C.hLw; have hL := C.hL; have hcar := S.hc; have hFa := C.room.1
  have hc : CodeIn M WF wnafFormCode := C.code S.agree C.cod (by decide) (by decide)
  obtain ⟨n1, d1, u1⟩ := S.st.alu hc wf_at_c4 (off' := 0xC8) (by decide)
  have S1 := S.step u1 (by decide)
  have a0_1 : reg n1 a0 = BitVec.ofNat 32 (carry + b) := by have := u1.upd_eq (by decide); rwa [wf_a0 h8 S.s10] at this
  obtain ⟨n2, d2, u2⟩ := S1.st.aluImm hc wf_at_c8 (off' := 0xCC) (by decide)
  have S2 := S1.step u2 (by decide)
  have a1_2 : reg n2 a1 = 1 := by
    rw [u2.upd_eq (by decide), a0_1]; apply BitVec.eq_of_toNat_eq; rw [wf_par (by omega), hodd]; rfl
  obtain ⟨n3, d3, u3⟩ := S2.st.taken hc 0xE0 wf_at_cc (by decide) (by rw [a1_2, S2.st.zero]; rfl)
  have S3 := S2.jmp u3
  obtain ⟨n4, d4, u4⟩ := S3.st.notTaken hc 0xE4 wf_at_e0 (by decide)
    (by rw [S3.s6, S3.s3, wbr_bgeu (by omega) (by omega)]; exact decide_eq_false (by omega))
  have S4 := S3.jmp u4
  have r4 : ∀ q, q ≠ a0 → q ≠ a1 → reg n4 q = reg n q := fun q h0 h1 => by
    rw [u4.regs, u3.regs, u2.upd_ne S1.st.zero q h1, u1.upd_ne S.st.zero q h0]
  have a0_4 : reg n4 a0 = BitVec.ofNat 32 (carry + b) := by
    rw [u4.regs, u3.regs, u2.upd_ne S1.st.zero _ (by decide), a0_1]
  obtain ⟨n5, d5, u5⟩ := S4.st.alu hc wf_at_e4 (off' := 0xE8) (by decide)
  have S5 := S4.step u5 (by decide)
  have a1_5 : reg n5 a1 = 0 := by
    rw [u5.upd_eq (by decide), a0_4, r4 _ (by decide) (by decide), h8, wsltu (by omega) (by omega)]
    simp only [show ¬ (carry + b < b) by omega, ↓reduceIte]
  obtain ⟨n6, d6, u6⟩ := S5.st.lw hc wf_at_e8 (off' := 0xEA) (by decide)
    (by rw [S5.hsp]; exact aligned_add hFa (k := 0xC) (by decide))
  have S6 := S5.step u6 (by decide)
  have a2_6 : reg n6 a2 = 0 := by rw [u6.upd_eq (by decide), S5.hsp]; exact S.chi
  obtain ⟨n7, d7, u7⟩ := S6.st.alu hc wf_at_ea (off' := 0xEC) (by decide)
  have S7 := S6.step u7 (by decide)
  have a1_7 : reg n7 a1 = 0 := by rw [u7.upd_eq (by decide), u6.upd_ne S5.st.zero _ (by decide), a1_5, a2_6]; rfl
  obtain ⟨n8, d8, u8⟩ := S7.st.aluImm hc wf_at_ec (off' := 0xF0) (by decide)
  have S8 := S7.step u8 (by decide)
  have a0_7 : reg n7 a0 = BitVec.ofNat 32 (carry + b) := by
    rw [u7.upd_ne S6.st.zero _ (by decide), u6.upd_ne S5.st.zero _ (by decide), u5.upd_ne S4.st.zero _ (by decide), a0_4]
  have a2_8 : reg n8 a2 = if carry + b < 16 then 1 else 0 := by
    rw [u8.upd_eq (by decide), a0_7, show (0x10 : Word) = BitVec.ofNat 32 16 from rfl, wsltu (by omega) (by decide)]
  obtain ⟨n9, d9, u9⟩ := S8.st.aluImm hc wf_at_f0 (off' := 0xF4) (by decide)
  have S9 := S8.step u9 (by decide)
  have a2_9 : reg n9 a2 = BitVec.ofNat 32 (wc (carry + b)) := by
    rw [u9.upd_eq (by decide), a2_8]; exact wc_xor ⟨carry + b, by omega⟩
  obtain ⟨n10, d10, u10⟩ := S9.st.alu hc wf_at_f4 (off' := 0xF8) (by decide)
  have S10 := S9.step u10 (by decide)
  have a1_10 : reg n10 a1 = 0 := by
    rw [u10.upd_eq (by decide), S9.st.zero, u9.upd_ne S8.st.zero _ (by decide), u8.upd_ne S7.st.zero _ (by decide), a1_7]
    rfl
  have a0_10 : reg n10 a0 = BitVec.ofNat 32 (carry + b) := by
    rw [u10.upd_ne S9.st.zero _ (by decide), u9.upd_ne S8.st.zero _ (by decide), u8.upd_ne S7.st.zero _ (by decide), a0_7]
  have a2_10 : reg n10 a2 = BitVec.ofNat 32 (wc (carry + b)) := by rw [u10.upd_ne S9.st.zero _ (by decide), a2_9]
  obtain ⟨n11, d11, u11⟩ := S10.st.alu hc wf_at_f8 (off' := 0xFC) (by decide)
  obtain ⟨n12, d12, u12⟩ := u11.self.alu hc wf_at_fc (off' := 0x100) (by decide)
  obtain ⟨n13, d13, u13⟩ := u12.self.aluImm hc wf_at_100 (off' := 0x104) (by decide)
  obtain ⟨n14, d14, u14⟩ := u13.self.alu hc wf_at_104 (off' := 0x106) (by decide)
  have K14 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ (26 : Fin 32) → reg n14 q = reg n10 q := fun q h0 h1 h26 => by
    rw [u14.upd_ne u13.self.zero q h0, u13.upd_ne u12.self.zero q h1, u12.upd_ne u11.self.zero q h1,
      u11.upd_ne S10.st.zero q h26]
  have R14 : WfR F wp wl L r0 n14 := S10.r.keep fun q hq => K14 q (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have s10_14 : reg n14 (26 : Fin 32) = BitVec.ofNat 32 (wc (carry + b)) := by
    rw [u14.upd_ne u13.self.zero _ (by decide), u13.upd_ne u12.self.zero _ (by decide),
      u12.upd_ne u11.self.zero _ (by decide), u11.upd_eq (by decide), a2_10, a1_10]; exact BitVec.or_zero
  have a0_14 : reg n14 a0 = BitVec.ofNat 32 (carry + b) + ((0 - BitVec.ofNat 32 (wc (carry + b))) &&& 0xE0) := by
    rw [u14.upd_eq (by decide), u13.upd_ne u12.self.zero _ (by decide), u12.upd_ne u11.self.zero _ (by decide),
      u11.upd_ne S10.st.zero _ (by decide), a0_10, u13.upd_eq (by decide), u12.upd_eq (by decide), u11.self.zero,
      u11.upd_eq (by decide), a2_10, a1_10, show aluEval .or (BitVec.ofNat 32 (wc (carry + b))) 0 =
        BitVec.ofNat 32 (wc (carry + b)) from BitVec.or_zero]; rfl
  have r14 : reg n14 (20 : Fin 32) = wp + BitVec.ofNat 32 pos := by
    rw [K14 _ (by decide) (by decide) (by decide), u10.upd_ne S9.st.zero _ (by decide),
      u9.upd_ne S8.st.zero _ (by decide), u8.upd_ne S7.st.zero _ (by decide), u7.upd_ne S6.st.zero _ (by decide),
      u6.upd_ne S5.st.zero _ (by decide), u5.upd_ne S4.st.zero _ (by decide), r4 _ (by decide) (by decide), h20]
  obtain ⟨n15, d15, u15⟩ := u14.self.sb hc wf_at_106 (off' := 0x10A) (by decide)
  have hbyte : (BitVec.ofNat 32 (carry + b) + ((0 - BitVec.ofNat 32 (wc (carry + b))) &&& 0xE0)).extractLsb' 0 8 =
      BitVec.ofNat 8 (digB (wd (carry + b))) := wd_byte ⟨carry + b, by omega⟩
  rw [r14, add_lit_zero, a0_14, hbyte,
    show memStore8 M (wp + BitVec.ofNat 32 pos) (BitVec.ofNat 8 (digB (wd (carry + b)))) = wput M wp pos (wd (carry + b))
      from rfl] at u15
  have P1 := S.mem.put C (by omega) (wd (carry + b))
  have W1 := P1.1
  have hc15 : CodeIn (wput M wp pos (wd (carry + b))) WF wnafFormCode := C.code W1.agree C.cod (by decide) (by decide)
  obtain ⟨n16, d16, u16⟩ := u15.sb hc15 wf_at_10a (off' := 0x10E) (by decide)
  rw [R14.hsp, u14.self.zero, show (F + 0x34 : Word) = F + BitVec.ofNat 32 0x34 from rfl] at u16
  have W2 := W1.st8 C (by omega) (c := 0x34) (Or.inr ⟨by decide, by decide⟩) ((0 : Word).extractLsb' 0 8)
  have hc16 := C.code W2.agree C.cod (by decide) (by decide)
  obtain ⟨n17, d17, u17⟩ := u16.sw hc16 wf_at_10e (off' := 0x110) (by decide)
    (by rw [R14.hsp]; exact aligned_add hFa (k := 0x38) (by decide))
  rw [R14.hsp, s10_14, show (F + 0x38 : Word) = F + BitVec.ofNat 32 0x38 from rfl] at u17
  have W3 := W2.st32 C (by omega) (c := 0x38) (Or.inr ⟨by decide, by decide⟩) (BitVec.ofNat 32 (wc (carry + b)))
  have hc17 := C.code W3.agree C.cod (by decide) (by decide)
  obtain ⟨n18, d18, u18⟩ := u17.aluImm hc17 wf_at_110 (off' := 0x112) (by decide)
  obtain ⟨n19, c19, pc19, mem19, regs19⟩ := u18.self.callRa (cb := BitVec.ofNat 32 expectUsizeAddress) hc17 wf_at_112
    wf_at_116 (by decide) (by decide)
  have r19 := PEnv.reg1 regs19 u18.self.zero
  have sp18 : reg n18 sp = F := by rw [u18.upd_ne u15.zero _ (by decide), R14.hsp]
  have e34 : (memStore32 (memStore8 (wput M wp pos (wd (carry + b))) (F + BitVec.ofNat 32 0x34)
      ((0 : Word).extractLsb' 0 8)) (F + BitVec.ofNat 32 0x38) (BitVec.ofNat 32 (wc (carry + b))))
      (F + BitVec.ofNat 32 0x34) = 0 := by
    rw [memStore32_get_sep (sep_offsets F (c := 0x38) (n := 4) (d := 0x34) (k := 1) (Or.inr (by decide)) (by decide)
      (by decide)), wst8_same]; rfl
  obtain ⟨n20, c20, pc20, a0_20, mem20, K20⟩ := (expectUsize_correct n19 (p := F + BitVec.ofNat 32 0x34)
    (retAddr := WF + BitVec.ofNat 32 (0x112 + 8)) (by rw [mem19]; exact C.pan.hi (C.hi W3.agree))
    (by rw [mem19]; exact C.code W3.agree C.exu (by decide) (by decide)) pc19
    (by rw [r19 a0 (by decide), u18.upd_eq (by decide), R14.hsp]; rfl) (aligned_add hFa (k := 0x34) (by decide))
    (by rw [regs19]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at WF (by decide) _ (by decide)))
    (by rw [r19 sp (by decide), sp18]; exact C.room)).1 (by rw [mem19]; exact e34)
  rw [mem19] at a0_20 mem20
  have K : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ ra → reg n20 q = reg n14 q := fun q h0 h1 hr => by
    rw [K20 q h0 h1, r19 q hr, u18.upd_ne u15.zero q h0]
  have K10 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ ra → q ≠ (26 : Fin 32) → reg n20 q = reg n10 q := fun q h0 h1 hr h26 => by
    rw [K q h0 h1 hr, K14 q h0 h1 h26]
  refine ⟨n20, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (c19.trans c20)))))))))))))))))),
    ⟨by rw [pc20], mem20, fun _ => rfl⟩, R14.keep fun q hq => K q (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), W3, ?_, ?_,
    by rw [K _ (by decide) (by decide) (by decide), s10_14],
    by rw [K10 _ (by decide) (by decide) (by decide) (by decide), S10.s5],
    by rw [K10 _ (by decide) (by decide) (by decide) (by decide), S10.s6],
    by rw [K10 _ (by decide) (by decide) (by decide) (by decide), S10.s7],
    by rw [K10 _ (by decide) (by decide) (by decide) (by decide), S10.s11]⟩
  · rw [memLoad32_store32_sep (sep_offsets F (c := 0x38) (n := 4) (d := 0xC) (k := 4) (Or.inr (by decide)) (by decide)
      (by decide)), memLoad32_store8_sep (sep_offsets F (c := 0x34) (n := 1) (d := 0xC) (k := 4) (Or.inr (by decide))
      (by decide) (by decide)), P1.2 _ (by decide), S.chi]
  · rw [a0_20, show F + BitVec.ofNat 32 0x34 + 4 = F + BitVec.ofNat 32 0x38 from add_ofNat_assoc F 0x34 4,
      memLoad32_store32_same]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The loop at 0x152 that writes `r` zero digits from index `k`; `a0` counts
up from `-r`. -/
theorem wf_zl (C : WfCtx M0 F wp cp wl cn L) : ∀ (r : Nat) {n : Machine} {M : Word → BitVec 8} {k : Nat} {D' : List Int},
    1 ≤ r → St M WF n 0x152 (reg n) → WfR F wp wl L r0 n → WfMem M0 Ms F wp cp wl cn M j k D' →
    reg n (21 : Fin 32) = BitVec.ofNat 32 k → reg n a0 = BitVec.ofNat 32 (2 ^ 32 - r) → k + r ≤ L →
    ∃ n' M', Steps n n' ∧ St M' WF n' 0x164 (reg n') ∧ WfR F wp wl L r0 n' ∧
      WfMem M0 Ms F wp cp wl cn M' j (k + r) (D' ++ List.replicate r 0) ∧
      reg n' (21 : Fin 32) = BitVec.ofNat 32 (k + r) ∧
      ∀ q, q ≠ a0 → q ≠ a2 → q ≠ (21 : Fin 32) → reg n' q = reg n q := by
  intro r
  induction r with
  | zero => intro _ _ _ _ h; exact absurd h (by decide)
  | succ r ih =>
    intro n M k D' _ s R W h21 ha0 hkr
    have hLw := C.hLw; have hL := C.hL
    have hc : CodeIn M WF wnafFormCode := C.code W.agree C.cod (by decide) (by decide)
    obtain ⟨n1, d1, u1⟩ := s.notTaken hc 0x156 wf_at_152 (by decide)
      (by rw [R.s3, h21, wbr_beq (by omega) (by omega)]; exact decide_eq_false (by omega))
    obtain ⟨n2, d2, u2⟩ := u1.alu hc wf_at_156 (off' := 0x15A) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc wf_at_15a (off' := 0x15C) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.self.sb hc wf_at_15c (off' := 0x160) (by decide)
    have a2_3 : reg n3 a2 = wp + BitVec.ofNat 32 k := by
      rw [u3.upd_ne u2.self.zero _ (by decide), u2.upd_eq (by decide), R.s9, h21]; rfl
    rw [a2_3, add_lit_zero, u3.self.zero, show memStore8 M (wp + BitVec.ofNat 32 k) ((0 : Word).extractLsb' 0 8) =
      wput M wp k 0 from rfl] at u4
    have W' := (W.put C (by omega) 0).1
    have hc4 : CodeIn (wput M wp k 0) WF wnafFormCode := C.code W'.agree C.cod (by decide) (by decide)
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hc4 wf_at_160 (off' := 0x162) (by decide)
    have K5 : ∀ q, q ≠ a0 → q ≠ a2 → q ≠ (21 : Fin 32) → reg n5 q = reg n q := fun q h0 h2 h21 => by
      rw [u5.upd_ne u3.self.zero q h0, u3.upd_ne u2.self.zero q h21, u2.upd_ne u1.zero q h2]
    have R5 : WfR F wp wl L r0 n5 := R.keep fun q hq => K5 q (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    have s5_5 : reg n5 (21 : Fin 32) = BitVec.ofNat 32 (k + 1) := by
      rw [u5.upd_ne u3.self.zero _ (by decide), u3.upd_eq (by decide), u2.upd_ne u1.zero _ (by decide), h21,
        wadd1]
    have a0_5 : reg n5 a0 = BitVec.ofNat 32 (2 ^ 32 - r) := by
      rw [u5.upd_eq (by decide), u3.upd_ne u2.self.zero _ (by decide), u2.upd_ne u1.zero _ (by decide), ha0,
        wadd1]; congr 1; omega
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc4 0x164 wf_at_162 (by decide)
        (by rw [a0_5, u5.self.zero]; decide)
      refine ⟨n6, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), u6.self, R5.jmp u6, W',
        by rw [u6.regs, s5_5], fun q h0 h2 h21 => by rw [u6.regs, K5 q h0 h2 h21]⟩
    · obtain ⟨n6, d6, u6⟩ := u5.self.taken hc4 0x152 wf_at_162 (by decide)
        (by rw [a0_5, u5.self.zero, show (0 : Word) = BitVec.ofNat 32 0 from rfl, wbr_bne (by omega) (by decide)]
            simp only [Bool.not_eq_true']; exact decide_eq_false (by omega))
      obtain ⟨n7, M7, c7, s7, R7, W7, h7, K7⟩ := ih (n := n6) (k := k + 1) (D' := D' ++ [0]) hr u6.self (R5.jmp u6) W'
        (by rw [u6.regs, s5_5]) (by rw [u6.regs, a0_5]) (by omega)
      refine ⟨n7, M7, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c7))))), s7, R7, ?_, ?_,
        fun q h0 h2 h21 => by rw [K7 q h0 h2 h21, u6.regs, K5 q h0 h2 h21]⟩
      · have e : D' ++ List.replicate (r + 1) 0 = D' ++ [0] ++ List.replicate r 0 := by simp [List.replicate_succ]
        rw [show k + (r + 1) = k + 1 + r by omega, e]; exact W7
      · rw [h7]; congr 1; omega

theorem wsub {a b : Nat} (ha : a < 2 ^ 32) (hb : b ≤ a) :
    aluEval .sub (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = BitVec.ofNat 32 (a - b) := by
  show BitVec.ofNat 32 a - BitVec.ofNat 32 b = _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- `if rd < 5 skip; rd = 5`, at 0x12C and 0x13C. -/
theorem wf_min5 {M : Word → BitVec 8} {n : Machine} {off : Nat} {rd : Fin 32} (s : St M WF n off (reg n))
    (hc : CodeIn M WF wnafFormCode) {x : Nat} (hx : x < 2 ^ 32)
    (hb : fetchRel wnafFormCode off = some (.branch .bltu rd a2 0x6, 4))
    (hi : fetchRel wnafFormCode (off + 4) = some (.aluImm .add rd x0 0x5, 2))
    (hrd : rd.val ≠ 0) (h1 : reg n rd = BitVec.ofNat 32 x) (h2 : reg n a2 = 5) :
    ∃ n', Steps n n' ∧ St M WF n' (off + 6) (reg n') ∧ reg n' rd = BitVec.ofNat 32 (min 5 x) ∧
      ∀ q, q ≠ rd → reg n' q = reg n q := by
  by_cases h : x < 5
  · obtain ⟨n1, d1, u1⟩ := s.taken hc (off + 6) hb
      (by rw [show (0x6 : Word) = BitVec.ofNat 32 6 from rfl, BitVec.ofNat_add_ofNat])
      (by rw [h1, h2, show (5 : Word) = BitVec.ofNat 32 5 from rfl, wbr_bltu hx (by decide)]; exact decide_eq_true h)
    exact ⟨n1, .single d1, u1.self, by rw [u1.regs, h1, Nat.min_eq_right (by omega)], fun q _ => u1.regs q⟩
  · obtain ⟨n1, d1, u1⟩ := s.notTaken hc (off + 4) hb
      (by rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, BitVec.ofNat_add_ofNat])
      (by rw [h1, h2, show (5 : Word) = BitVec.ofNat 32 5 from rfl, wbr_bltu hx (by decide)]; exact decide_eq_false h)
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc hi (off' := off + 6)
      (by rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, BitVec.ofNat_add_ofNat])
    refine ⟨n2, .cons d1 (.single d2), u2.self, ?_, fun q hq => by rw [u2.upd_ne u1.zero q hq]⟩
    rw [u2.upd_eq hrd, u1.zero, Nat.min_eq_left (by omega)]; rfl

theorem wf_cnt : ∀ s : Fin 6, 1 ≤ s.val →
    aluEval .and (aluEval .sub 1 (BitVec.ofNat 32 s.val)) (aluEval .add (if s.val < 2 then 1 else 0) 0xFFFFFFFF) =
      if s.val < 2 then 0 else BitVec.ofNat 32 (2 ^ 32 - (s.val - 1)) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From 0x164 back to the loop head, `pos` moved to `k`. -/
theorem wf_tail (C : WfCtx M0 F wp cp wl cn L) {n : Machine} {M : Word → BitVec 8} {k c' : Nat}
    (s : St M WF n 0x164 (reg n)) (R : WfR F wp wl L r0 n) (W : WfMem M0 Ms F wp cp wl cn M j k D)
    (h21 : reg n (21 : Fin 32) = BitVec.ofNat 32 k) (h23 : reg n (23 : Fin 32) = BitVec.ofNat 32 pos)
    (ha1 : reg n a1 = BitVec.ofNat 32 (k - pos)) (h26 : reg n (26 : Fin 32) = BitVec.ofNat 32 c')
    (hk : pos ≤ k) (hkL : k ≤ L) (hc' : c' ≤ 1) (hj : j ≤ k / 64 ∧ k / 64 ≤ j + 1)
    (hspec : ∃ f, L - k + 1 ≤ f ∧ D ++ wnafGo (leN (memBytes M0 cp cn)) L f k c' = wnafSpec (memBytes M0 cp cn) L) :
    ∃ n' M', Steps n n' ∧ WfSt M0 Ms F wp cp wl cn L r0 M' n' 0x5E k c' j D := by
  have hLw := C.hLw; have hL := C.hL; have hFa := C.room.1
  have hc : CodeIn M WF wnafFormCode := C.code W.agree C.cod (by decide) (by decide)
  obtain ⟨n1, d1, u1⟩ := s.sw hc wf_at_164 (off' := 0x166) (by decide)
    (by rw [R.hsp]; exact aligned_add hFa (k := 0xC) (by decide))
  rw [R.hsp, s.zero, show (F + 0xC : Word) = F + BitVec.ofNat 32 0xC from rfl] at u1
  have W1 := W.st32 C (by omega) (c := 0xC) (Or.inl (by decide)) 0
  have hc1 := C.code W1.agree C.cod (by decide) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.alu hc1 wf_at_166 (off' := 0x168) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.jump hc1 wf_at_168 (off' := 0x56) (by decide) (by rw [u2.self.pc]; decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.alu hc1 wf_at_56 (off' := 0x58) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc1 wf_at_58 (off' := 0x5A) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.alu hc1 wf_at_5a (off' := 0x5E) (by decide)
  have K6 : ∀ q, q ≠ (21 : Fin 32) → q ≠ (22 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (27 : Fin 32) →
      reg n6 q = reg n q := fun q h21 h22 h23 h27 => by
    rw [u6.upd_ne u5.self.zero q h27, u5.upd_ne u4.self.zero q h21, u4.upd_ne u3.self.zero q h22, u3.regs,
      u2.upd_ne u1.zero q h23]
  have R6 : WfR F wp wl L r0 n6 := R.keep fun q hq => K6 q (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have s7_2 : reg n2 (23 : Fin 32) = BitVec.ofNat 32 k := by
    rw [u2.upd_eq (by decide), h23, ha1]
    show BitVec.ofNat 32 pos + BitVec.ofNat 32 (k - pos) = _; rw [BitVec.ofNat_add_ofNat]; congr 1; omega
  have s5_3 : reg n3 (21 : Fin 32) = BitVec.ofNat 32 k := by
    rw [u3.regs, u2.upd_ne u1.zero _ (by decide), h21]
  refine ⟨n6, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), ⟨u6.self, R6.hsp, R6.s2, R6.s3,
    R6.s9, R6.s8, ?_, ?_, ?_, ?_, by rw [K6 _ (by decide) (by decide) (by decide) (by decide), h26], R6.gp, R6.tp,
    hkL, hc', memLoad32_store32_same _ _ _, W1.idx, hj, W1.cur, W1.nxt, W1.rest, W1.len, W1.out, hspec, W1.agree,
    W1.slots⟩⟩
  · rw [u6.upd_ne u5.self.zero _ (by decide), u5.upd_eq (by decide), u4.upd_ne u3.self.zero _ (by decide), s5_3, wadd1]
  · rw [u6.upd_ne u5.self.zero _ (by decide), u5.upd_ne u4.self.zero _ (by decide), u4.upd_eq (by decide), u3.self.zero,
      s5_3]; exact BitVec.zero_add _
  · rw [u6.upd_ne u5.self.zero _ (by decide), u5.upd_ne u4.self.zero _ (by decide),
      u4.upd_ne u3.self.zero _ (by decide), u3.regs, s7_2]
  · rw [u6.upd_eq (by decide), u5.upd_ne u4.self.zero _ (by decide), u4.upd_ne u3.self.zero _ (by decide), u3.regs,
      u5.upd_ne u4.self.zero _ (by decide), u4.upd_ne u3.self.zero _ (by decide), u3.regs, s7_2,
      u2.upd_ne u1.zero _ (by decide), R.s2, wsub (by omega) hkL]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- An odd window, from the return of `expect` at 0x11A to the loop head:
`sk - 1` zero digits after the digit, and `pos` moved by `sk`. -/
theorem wf_odd2 (C : WfCtx M0 F wp cp wl cn L) {n : Machine} {M : Word → BitVec 8} {c' sk : Nat}
    (s : St M WF n 0x11A (reg n)) (R : WfR F wp wl L r0 n) (W : WfMem M0 Ms F wp cp wl cn M j (pos + 1) D)
    (hc' : c' ≤ 1) (hsk : sk = min 5 (L - c' - pos)) (hsk1 : 1 ≤ sk) (hcL : c' < L)
    (ha0 : reg n a0 = BitVec.ofNat 32 c') (h26 : reg n (26 : Fin 32) = BitVec.ofNat 32 c')
    (h21 : reg n (21 : Fin 32) = BitVec.ofNat 32 (pos + 1)) (h23 : reg n (23 : Fin 32) = BitVec.ofNat 32 pos)
    (h27 : reg n (27 : Fin 32) = BitVec.ofNat 32 (L - pos)) (hj : j ≤ (pos + sk) / 64 ∧ (pos + sk) / 64 ≤ j + 1)
    (hspec : ∃ f, L - (pos + sk) + 1 ≤ f ∧ (D ++ List.replicate (sk - 1) 0) ++
      wnafGo (leN (memBytes M0 cp cn)) L f (pos + sk) c' = wnafSpec (memBytes M0 cp cn) L) :
    ∃ n' M', Steps n n' ∧ WfSt M0 Ms F wp cp wl cn L r0 M' n' 0x5E (pos + sk) c' j (D ++ List.replicate (sk - 1) 0) := by
  have hLw := C.hLw; have hL := C.hL
  have hc : CodeIn M WF wnafFormCode := C.code W.agree C.cod (by decide) (by decide)
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc wf_at_11a (off' := 0x11C) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.alu hc wf_at_11c (off' := 0x120) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.alu hc wf_at_120 (off' := 0x124) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc wf_at_124 (off' := 0x126) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.self.alu hc wf_at_126 (off' := 0x128) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.alu hc wf_at_128 (off' := 0x12C) (by decide)
  have K6 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n6 q = reg n q := fun q h1 h2 h3 => by
    rw [u6.upd_ne u5.self.zero q h1, u5.upd_ne u4.self.zero q h1, u4.upd_ne u3.self.zero q h3,
      u3.upd_ne u2.self.zero q h3, u2.upd_ne u1.self.zero q h1, u1.upd_ne s.zero q h2]
  have a1_2 : reg n2 a1 = BitVec.ofNat 32 (L - c') := by
    rw [u2.upd_eq (by decide), u1.upd_ne s.zero _ (by decide), u1.upd_ne s.zero _ (by decide), R.s2, ha0,
      wsub (by omega) (by omega)]
  have a3_4 : reg n4 a3 = 0xFFFFFFFF := by
    rw [u4.upd_eq (by decide), u3.upd_eq (by decide), u2.upd_ne u1.self.zero _ (by decide), u1.upd_ne s.zero _ (by decide),
      R.s2, a1_2, wsltu (by omega) (by omega)]
    simp only [show ¬ (L < L - c') by omega, ↓reduceIte]; rfl
  have a1_6 : reg n6 a1 = BitVec.ofNat 32 (L - c' - pos) := by
    rw [u6.upd_eq (by decide), u5.upd_eq (by decide), u4.upd_ne u3.self.zero _ (by decide),
      u3.upd_ne u2.self.zero _ (by decide), a1_2, a3_4, u5.upd_ne u4.self.zero _ (by decide),
      u4.upd_ne u3.self.zero _ (by decide), u3.upd_ne u2.self.zero _ (by decide), u2.upd_ne u1.self.zero _ (by decide),
      u1.upd_ne s.zero _ (by decide), h23, show aluEval .and (BitVec.ofNat 32 (L - c')) 0xFFFFFFFF = BitVec.ofNat 32 (L - c')
        from BitVec.and_allOnes, wsub (by omega) (by omega)]
  have a2_6 : reg n6 a2 = 5 := by
    rw [u6.upd_ne u5.self.zero _ (by decide), u5.upd_ne u4.self.zero _ (by decide), u4.upd_ne u3.self.zero _ (by decide),
      u3.upd_ne u2.self.zero _ (by decide), u2.upd_ne u1.self.zero _ (by decide), u1.upd_eq (by decide), s.zero]; rfl
  obtain ⟨n7, c7, s7, a1_7, K7⟩ := wf_min5 u6.self hc (x := L - c' - pos) (by omega) wf_at_12c wf_at_130 (by decide)
    a1_6 a2_6
  have s7' : St M WF n7 0x132 (reg n7) := s7
  have a0_7 : reg n7 a0 = BitVec.ofNat 32 c' := by rw [K7 _ (by decide), K6 _ (by decide) (by decide) (by decide), ha0]
  obtain ⟨n8, d8, u8⟩ := s7'.taken hc 0x138 wf_at_132 (by decide)
    (by rw [a0_7, K7 _ (by decide), K6 _ (by decide) (by decide) (by decide), R.s2, wbr_bltu (by omega) (by omega)]
        exact decide_eq_true hcL)
  obtain ⟨n9, d9, u9⟩ := u8.self.alu hc wf_at_138 (off' := 0x13C) (by decide)
  have a0_9 : reg n9 a0 = BitVec.ofNat 32 (L - pos - c') := by
    rw [u9.upd_eq (by decide), u8.regs, u8.regs, a0_7, K7 _ (by decide), K6 _ (by decide) (by decide) (by decide), h27,
      wsub (by omega) (by omega)]
  have a2_9 : reg n9 a2 = 5 := by rw [u9.upd_ne u8.self.zero _ (by decide), u8.regs, K7 _ (by decide), a2_6]
  obtain ⟨n10, c10, s10, a0_10, K10⟩ := wf_min5 u9.self hc (x := L - pos - c') (by omega) wf_at_13c wf_at_140 (by decide)
    a0_9 a2_9
  have s10' : St M WF n10 0x142 (reg n10) := s10
  rw [show min 5 (L - pos - c') = sk by omega] at a0_10
  obtain ⟨n11, d11, u11⟩ := s10'.aluImm hc wf_at_142 (off' := 0x146) (by decide)
  obtain ⟨n12, d12, u12⟩ := u11.self.aluImm hc wf_at_146 (off' := 0x148) (by decide)
  obtain ⟨n13, d13, u13⟩ := u12.self.alu hc wf_at_148 (off' := 0x14C) (by decide)
  obtain ⟨n14, d14, u14⟩ := u13.self.aluImm hc wf_at_14c (off' := 0x14E) (by decide)
  obtain ⟨n15, d15, u15⟩ := u14.self.alu hc wf_at_14e (off' := 0x150) (by decide)
  have K15 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n15 q = reg n q := fun q h0 h1 h2 h3 => by
    rw [u15.upd_ne u14.self.zero q h0, u14.upd_ne u13.self.zero q h2, u13.upd_ne u12.self.zero q h0,
      u12.upd_ne u11.self.zero q h3, u11.upd_ne s10'.zero q h2, K10 q h0, u9.upd_ne u8.self.zero q h0, u8.regs, K7 q h1,
      K6 q h1 h2 h3]
  have a1_15 : reg n15 a1 = BitVec.ofNat 32 sk := by
    rw [u15.upd_ne u14.self.zero _ (by decide), u14.upd_ne u13.self.zero _ (by decide),
      u13.upd_ne u12.self.zero _ (by decide), u12.upd_ne u11.self.zero _ (by decide), u11.upd_ne s10'.zero _ (by decide),
      K10 _ (by decide), u9.upd_ne u8.self.zero _ (by decide), u8.regs, a1_7, ← hsk]
  have a0_12 : reg n12 a0 = BitVec.ofNat 32 sk := by
    rw [u12.upd_ne u11.self.zero _ (by decide), u11.upd_ne s10'.zero _ (by decide), a0_10]
  have a3_12 : reg n12 a3 = 1 := by rw [u12.upd_eq (by decide), u11.self.zero]; rfl
  have a2_13 : reg n13 a2 = if sk < 2 then 1 else 0 := by
    rw [u13.upd_ne u12.self.zero _ (by decide), u12.upd_ne u11.self.zero _ (by decide), u11.upd_eq (by decide), a0_10,
      show (0x2 : Word) = BitVec.ofNat 32 2 from rfl, wsltu (by omega) (by decide)]
  have a0_15 : reg n15 a0 = if sk < 2 then 0 else BitVec.ofNat 32 (2 ^ 32 - (sk - 1)) := by
    rw [u15.upd_eq (by decide), u14.upd_ne u13.self.zero _ (by decide), u13.upd_eq (by decide), a3_12, a0_12,
      u14.upd_eq (by decide), a2_13]
    exact wf_cnt ⟨sk, by omega⟩ hsk1
  have R15 : WfR F wp wl L r0 n15 := R.keep fun q hq => K15 q (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have cs15 : Steps n n15 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (c7.trans (.cons d8 (.cons d9
    (c10.trans (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.single d15))))))))))))))
  by_cases h2 : sk < 2
  · obtain rfl : sk = 1 := by omega
    obtain ⟨n16, d16, u16⟩ := u15.self.taken hc 0x164 wf_at_150 (by decide)
      (by rw [a0_15, u15.self.zero]; simp only [h2, ↓reduceIte]; rfl)
    obtain ⟨n17, M17, c17, S17⟩ := wf_tail C (k := pos + 1) u16.self (R15.jmp u16) W
      (by rw [u16.regs, K15 _ (by decide) (by decide) (by decide) (by decide), h21])
      (by rw [u16.regs, K15 _ (by decide) (by decide) (by decide) (by decide), h23])
      (by rw [u16.regs, a1_15]; congr 1; omega)
      (by rw [u16.regs, K15 _ (by decide) (by decide) (by decide) (by decide), h26]) (by omega) (by omega) hc' hj
      (by simpa using hspec)
    exact ⟨n17, M17, cs15.trans (.cons d16 c17), by simpa using S17⟩
  · obtain ⟨n16, d16, u16⟩ := u15.self.notTaken hc 0x152 wf_at_150 (by decide)
      (by rw [a0_15, u15.self.zero]; simp only [h2, ↓reduceIte]
          rw [show (0 : Word) = BitVec.ofNat 32 0 from rfl, wbr_beq (by omega) (by decide)]
          exact decide_eq_false (by omega))
    obtain ⟨n17, M17, c17, s17, R17, W17, h17, K17⟩ := wf_zl C (sk - 1) (by omega) u16.self (R15.jmp u16) W
      (by rw [u16.regs, K15 _ (by decide) (by decide) (by decide) (by decide), h21])
      (by rw [u16.regs, a0_15]; simp only [h2, ↓reduceIte]) (by omega)
    rw [show pos + 1 + (sk - 1) = pos + sk by omega] at W17 h17
    obtain ⟨n18, M18, c18, S18⟩ := wf_tail C (k := pos + sk) s17 R17 W17 h17
      (by rw [K17 _ (by decide) (by decide) (by decide), u16.regs, K15 _ (by decide) (by decide) (by decide) (by decide),
        h23])
      (by rw [K17 _ (by decide) (by decide) (by decide), u16.regs, a1_15]; congr 1; omega)
      (by rw [K17 _ (by decide) (by decide) (by decide), u16.regs, K15 _ (by decide) (by decide) (by decide) (by decide),
        h26]) (by omega) (by omega) hc' hj hspec
    exact ⟨n18, M18, cs15.trans (.cons d16 (c17.trans c18)), S18⟩

/-- One trip around the loop from the head, with `pos < L`. -/
theorem wf_iter (C : WfCtx M0 F wp cp wl cn L) (S : WfSt M0 Ms F wp cp wl cn L r0 M n 0x5E pos carry j D)
    (hlt : pos < L) :
    ∃ n' M' pos' carry' j' D', Steps n n' ∧ WfSt M0 Ms F wp cp wl cn L r0 M' n' 0x5E pos' carry' j' D' ∧
      pos < pos' := by
  obtain ⟨n1, c1, S1, hs1, hs4⟩ := wf_get C S hlt
  obtain ⟨n2, c2, S2, h8, k20⟩ := wf_win C S1 hlt hs1
  have h20 : reg n2 (20 : Fin 32) = wp + BitVec.ofNat 32 pos := by rw [k20 _ rfl, hs4]
  have hcar := S.hc
  have hN := C.hN
  rcases Nat.mod_two_eq_zero_or_one (carry + leN (memBytes M0 cp cn) / 2 ^ pos % 32) with hev | hodd
  · obtain ⟨n3, c3, S3⟩ := wf_even C S2 hlt h8 h20 hev
    exact ⟨n3, _, _, _, _, _, c1.trans (c2.trans c3), S3, by omega⟩
  · obtain ⟨n3, M1, c3, s3, R3, W3, chi3, a03, s103, s53, s63, s73, s113⟩ :=
      wf_odd1 C S2 hlt (Nat.mod_lt _ (by decide)) h8 h20 hodd
    have hsk1 := wskip_pos hN hcar hlt
    have hwc : wc (carry + leN (memBytes M0 cp cn) / 2 ^ pos % 32) ≤ 1 := by unfold wc; split <;> decide
    have hcL : wc (carry + leN (memBytes M0 cp cn) / 2 ^ pos % 32) < L := by
      rcases Nat.lt_or_ge (wc (carry + leN (memBytes M0 cp cn) / 2 ^ pos % 32)) 1 with h | h
      · omega
      · have := wc_room hN hcar hlt (by omega); omega
    have hsk5 : wskip L pos (carry + leN (memBytes M0 cp cn) / 2 ^ pos % 32) ≤ 5 := by unfold wskip; omega
    have hskL : pos + wskip L pos (carry + leN (memBytes M0 cp cn) / 2 ^ pos % 32) ≤ L := by unfold wskip; omega
    obtain ⟨n4, M4, c4, S4⟩ := wf_odd2 C s3 R3 W3 (sk := wskip L pos (carry + leN (memBytes M0 cp cn) / 2 ^ pos % 32)) hwc rfl hsk1 hcL a03 s103 s53 s73 s113 ⟨by omega, by omega⟩ (by
      obtain ⟨f, hf, e⟩ := S2.spec
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      refine ⟨f', by omega, ?_⟩
      rw [wnafGo_odd hlt hodd] at e; rw [← e]; simp)
    exact ⟨n4, _, _, _, _, _, c1.trans (c2.trans (c3.trans c4)), S4, by omega⟩

/-- The loop runs until `pos = L`. -/
theorem wf_loop (C : WfCtx M0 F wp cp wl cn L) : ∀ (fuel : Nat) {n : Machine} {M : Word → BitVec 8} {pos carry j : Nat}
    {D : List Int}, L - pos ≤ fuel → WfSt M0 Ms F wp cp wl cn L r0 M n 0x5E pos carry j D →
    ∃ n' M' carry' j' D', Steps n n' ∧ WfSt M0 Ms F wp cp wl cn L r0 M' n' 0x5E L carry' j' D' := by
  intro fuel
  induction fuel with
  | zero =>
    intro n M pos carry j D h S
    have := S.hpos
    obtain rfl : pos = L := by omega
    exact ⟨n, M, carry, j, D, .refl _, S⟩
  | succ fuel ih =>
    intro n M pos carry j D h S
    rcases Nat.lt_or_ge pos L with hlt | hge
    · obtain ⟨n1, M1, pos1, c1, j1, D1, cs, S1, hp⟩ := wf_iter C S hlt
      obtain ⟨n2, M2, c2, j2, D2, cs2, S2⟩ := ih (by omega) S1
      exact ⟨n2, M2, c2, j2, D2, cs.trans cs2, S2⟩
    · have := S.hpos
      obtain rfl : pos = L := by omega
      exact ⟨n, M, carry, j, D, .refl _, S⟩

theorem wnafGo_end {N L f carry : Nat} (hc : carry ≤ 1) :
    wnafGo N L (f + 1) L carry = if carry = 0 then [] else [(1 : Int)] := by
  simp only [wnafGo, Nat.lt_irrefl, ↓reduceIte]
  by_cases h : carry = 0
  · simp [h]
  · obtain rfl : carry = 1 := by omega
    simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the loop head with `pos = L` to 0x180: the last carry, if any, as a
digit, and the digit count in `a0`. -/
theorem wf_exit (C : WfCtx M0 F wp cp wl cn L) (S : WfSt M0 Ms F wp cp wl cn L r0 M n 0x5E L carry j D) :
    ∃ n' M', Steps n n' ∧ St M' WF n' 0x180 (reg n') ∧ WfR F wp wl L r0 n' ∧
      WfMem M0 Ms F wp cp wl cn M' j (wnafSpec (memBytes M0 cp cn) L).length (wnafSpec (memBytes M0 cp cn) L) ∧
      reg n' a0 = BitVec.ofNat 32 (wnafSpec (memBytes M0 cp cn) L).length := by
  have hLw := C.hLw; have hL := C.hL; have hFa := C.room.1; have hcar := S.hc
  have hc : CodeIn M WF wnafFormCode := C.code S.agree C.cod (by decide) (by decide)
  have hE : wnafSpec (memBytes M0 cp cn) L = D ++ (if carry = 0 then [] else [(1 : Int)]) := by
    obtain ⟨f, hf, e⟩ := S.spec
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [← e, wnafGo_end hcar]
  rw [hE]
  have hlen := S.len
  obtain ⟨n1, d1, u1⟩ := S.st.alu hc wf_at_5e (off' := 0x62) (by decide)
  have S1 := S.step u1 (by decide)
  have s4 : reg n1 (20 : Fin 32) = wp + BitVec.ofNat 32 L := by rw [u1.upd_eq (by decide), S.s9, S.s6]; rfl
  obtain ⟨n2, d2, u2⟩ := S1.st.taken hc 0x16A wf_at_62 (by decide)
    (by rw [S1.s7, S1.s2, wbr_bgeu (by omega) (by omega)]; exact decide_eq_true (Nat.le_refl _))
  have S2 := S1.jmp u2
  obtain ⟨n3, d3, u3⟩ := S2.st.lw hc wf_at_16a (off' := 0x16C) (by decide)
    (by rw [S2.hsp]; exact aligned_add hFa (k := 0xC) (by decide))
  have S3 := S2.step u3 (by decide)
  obtain ⟨n4, d4, u4⟩ := S3.st.alu hc wf_at_16c (off' := 0x170) (by decide)
  have S4 := S3.step u4 (by decide)
  have a0_4 : reg n4 a0 = BitVec.ofNat 32 carry := by
    rw [u4.upd_eq (by decide), u3.upd_eq (by decide), S2.hsp, S3.s10]
    rw [show memLoad32 M (F + 0xC) = 0 from S.chi]; exact BitVec.or_zero
  have R4 := S4.r
  have r4 : reg n4 (20 : Fin 32) = wp + BitVec.ofNat 32 L := by
    rw [u4.upd_ne S3.st.zero _ (by decide), u3.upd_ne S2.st.zero _ (by decide), u2.regs, s4]
  by_cases h0 : carry = 0
  · subst h0
    obtain ⟨n5, d5, u5⟩ := S4.st.taken hc 0x17E wf_at_170 (by decide) (by rw [a0_4, S4.st.zero]; rfl)
    obtain ⟨n6, d6, u6⟩ := u5.self.alu hc wf_at_17e (off' := 0x180) (by decide)
    refine ⟨n6, M, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), u6.self,
      (R4.jmp u5).upd u6 u5.self.zero (by decide), ?_, ?_⟩
    · simp only [↓reduceIte, List.append_nil]; rw [hlen]; exact S.mem
    · simp only [↓reduceIte, List.append_nil]
      rw [u6.upd_eq (by decide), u5.self.zero, u5.regs, S4.s6, hlen]; exact BitVec.zero_add _
  · obtain rfl : carry = 1 := by omega
    obtain ⟨n5, d5, u5⟩ := S4.st.notTaken hc 0x172 wf_at_170 (by decide) (by rw [a0_4, S4.st.zero]; rfl)
    have S5 := S4.jmp u5
    obtain ⟨n6, d6, u6⟩ := S5.st.notTaken hc 0x176 wf_at_172 (by decide)
      (by rw [S5.s6, S5.s3, wbr_bgeu (by omega) (by omega)]; exact decide_eq_false (by omega))
    have S6 := S5.jmp u6
    obtain ⟨n7, d7, u7⟩ := S6.st.aluImm hc wf_at_176 (off' := 0x178) (by decide)
    have S7 := S6.step u7 (by decide)
    obtain ⟨n8, d8, u8⟩ := S7.st.aluImm hc wf_at_178 (off' := 0x17A) (by decide)
    obtain ⟨n9, d9, u9⟩ := u8.self.sb hc wf_at_17a (off' := 0x17E) (by decide)
    have r8 : ∀ q, q ≠ (22 : Fin 32) → q ≠ a0 → reg n8 q = reg n4 q := fun q h22 h0 => by
      rw [u8.upd_ne S7.st.zero q h22, u7.upd_ne S6.st.zero q h0, u6.regs, u5.regs]
    rw [r8 _ (by decide) (by decide), r4, add_lit_zero, u8.upd_ne S7.st.zero _ (by decide), u7.upd_eq (by decide),
      S6.st.zero, show memStore8 M (wp + BitVec.ofNat 32 L) ((aluEval .add 0 1).extractLsb' 0 8) = wput M wp L 1 from rfl]
      at u9
    have P := S.mem.put C (by omega) 1
    have hc9 := C.code P.1.agree C.cod (by decide) (by decide)
    obtain ⟨n10, d10, u10⟩ := u9.alu hc9 wf_at_17e (off' := 0x180) (by decide)
    have s6_8 : reg n8 (22 : Fin 32) = BitVec.ofNat 32 (L + 1) := by
      rw [u8.upd_eq (by decide), S7.s6, wadd1]
    refine ⟨n10, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
      (.single d10))))))))), u10.self, ?_, ?_, ?_⟩
    · exact (S7.r.upd u8 S7.st.zero (by decide)).upd u10 u9.zero (by decide)
    · simp only [Nat.one_ne_zero, ↓reduceIte, List.length_append, List.length_singleton]; rw [hlen]; exact P.1
    · simp only [Nat.one_ne_zero, ↓reduceIte, List.length_append, List.length_singleton]
      rw [u10.upd_eq (by decide), u9.zero, s6_8, hlen]; exact BitVec.zero_add _

end Steps

end C3.RV32
