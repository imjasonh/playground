import C3BootProofs.Proofs.Base64Decode
import C3BootProofs.Proofs.Sha2Update
import C3BootProofs.Proofs.Sha2OneShot

/-!
# `base64::encode_to::<Sha256>`, as compiled

`c3_verify::base64::encode_to` writes the padded base64 of its bytes into a
SHA-256 hasher four characters at a time: each group of three bytes becomes
four characters looked up in the alphabet, and a last group of one or two
bytes ends in `=`. `base64EncodeTo_correct` shows the hasher ends up holding
`base64Encode` of the bytes after what it held.
-/

namespace C3

theorem b64Char_mod (v : Nat) : b64Char (v % 64) = b64Char v := by
  simp only [b64Char, Nat.mod_mod]

theorem b64Char_lt (v : Nat) : b64Char v < 256 := by
  unfold b64Char
  have h := Nat.mod_lt v (by decide : 0 < 64)
  generalize v % 64 = w at h ⊢
  by_cases h1 : w < 26
  · rw [if_pos h1]; omega
  rw [if_neg h1]
  by_cases h2 : w < 52
  · rw [if_pos h2]; omega
  rw [if_neg h2]
  by_cases h3 : w < 62
  · rw [if_pos h3]; omega
  rw [if_neg h3]
  by_cases h4 : w = 62
  · rw [if_pos h4]; decide
  · rw [if_neg h4]; decide

theorem base64Encode_append : ∀ xs ys : Bytes, xs.length % 3 = 0 →
    base64Encode (xs ++ ys) = base64Encode xs ++ base64Encode ys
  | [], ys, _ => by simp only [List.nil_append, base64Encode]
  | [_], _, h => absurd h (by simp only [List.length_cons, List.length_nil]; decide)
  | [_, _], _, h => absurd h (by simp only [List.length_cons, List.length_nil]; decide)
  | a :: b :: c :: xs, ys, h => by
    have ih := base64Encode_append xs ys (by simp only [List.length_cons] at h; omega)
    show base64Encode (a :: b :: c :: (xs ++ ys)) = _
    simp only [base64Encode]
    rw [ih, List.append_assoc]

end C3

namespace C3.RV32

open C3.Image

abbrev BEE : Word := BitVec.ofNat 32 base64EncodeToAddress
abbrev BAL : Word := BitVec.ofNat 32 b64AlphabetAddress

section
set_option maxRecDepth 20000
theorem bee_at_0 : fetchRel base64EncodeToCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem bee_at_2 : fetchRel base64EncodeToCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem bee_at_4 : fetchRel base64EncodeToCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem bee_at_6 : fetchRel base64EncodeToCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem bee_at_8 : fetchRel base64EncodeToCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem bee_at_a : fetchRel base64EncodeToCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem bee_at_c : fetchRel base64EncodeToCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem bee_at_e : fetchRel base64EncodeToCode 0xE = some (.store .sw sp (21 : Fin 32) 0x14, 2) := by decide
theorem bee_at_10 : fetchRel base64EncodeToCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x10, 2) := by decide
theorem bee_at_12 : fetchRel base64EncodeToCode 0x12 = some (.store .sw sp (23 : Fin 32) 0xC, 2) := by decide
theorem bee_at_14 : fetchRel base64EncodeToCode 0x14 = some (.alu .add (22 : Fin 32) x0 a2, 2) := by decide
theorem bee_at_16 : fetchRel base64EncodeToCode 0x16 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem bee_at_18 : fetchRel base64EncodeToCode 0x18 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem bee_at_1a : fetchRel base64EncodeToCode 0x1A = some (.aluImm .add a0 x0 0x3, 2) := by decide
theorem bee_at_1c : fetchRel base64EncodeToCode 0x1C = some (.alu .divu (20 : Fin 32) a1 a0, 4) := by decide
theorem bee_at_20 : fetchRel base64EncodeToCode 0x20 = some (.aluImm .sll (21 : Fin 32) (20 : Fin 32) 0x1, 4) := by decide
theorem bee_at_24 : fetchRel base64EncodeToCode 0x24 = some (.alu .add (8 : Fin 32) (21 : Fin 32) (20 : Fin 32), 4) := by decide
theorem bee_at_28 : fetchRel base64EncodeToCode 0x28 = some (.lui (23 : Fin 32) 0x3FCC4000, 4) := by decide
theorem bee_at_2c : fetchRel base64EncodeToCode 0x2C = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x7D8, 4) := by decide
theorem bee_at_30 : fetchRel base64EncodeToCode 0x30 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem bee_at_32 : fetchRel base64EncodeToCode 0x32 = some (.branch .beq (8 : Fin 32) x0 0x66, 2) := by decide
theorem bee_at_34 : fetchRel base64EncodeToCode 0x34 = some (.load .lbu a1 a0 0x0, 4) := by decide
theorem bee_at_38 : fetchRel base64EncodeToCode 0x38 = some (.load .lbu a2 a0 0x1, 4) := by decide
theorem bee_at_3c : fetchRel base64EncodeToCode 0x3C = some (.load .lbu a3 a0 0x2, 4) := by decide
theorem bee_at_40 : fetchRel base64EncodeToCode 0x40 = some (.aluImm .sll a4 a1 0x10, 4) := by decide
theorem bee_at_44 : fetchRel base64EncodeToCode 0x44 = some (.aluImm .sll a2 a2 0x8, 2) := by decide
theorem bee_at_46 : fetchRel base64EncodeToCode 0x46 = some (.aluImm .srl a1 a1 0x2, 2) := by decide
theorem bee_at_48 : fetchRel base64EncodeToCode 0x48 = some (.aluImm .and a5 a3 0x3F, 4) := by decide
theorem bee_at_4c : fetchRel base64EncodeToCode 0x4C = some (.alu .or a3 a3 a2, 2) := by decide
theorem bee_at_4e : fetchRel base64EncodeToCode 0x4E = some (.alu .or a2 a2 a4, 2) := by decide
theorem bee_at_50 : fetchRel base64EncodeToCode 0x50 = some (.alu .add a1 a1 (23 : Fin 32), 2) := by decide
theorem bee_at_52 : fetchRel base64EncodeToCode 0x52 = some (.alu .add a5 a5 (23 : Fin 32), 2) := by decide
theorem bee_at_54 : fetchRel base64EncodeToCode 0x54 = some (.aluImm .sll a2 a2 0xE, 2) := by decide
theorem bee_at_56 : fetchRel base64EncodeToCode 0x56 = some (.aluImm .sll a3 a3 0x14, 2) := by decide
theorem bee_at_58 : fetchRel base64EncodeToCode 0x58 = some (.aluImm .srl a2 a2 0x1A, 2) := by decide
theorem bee_at_5a : fetchRel base64EncodeToCode 0x5A = some (.aluImm .srl a3 a3 0x1A, 2) := by decide
theorem bee_at_5c : fetchRel base64EncodeToCode 0x5C = some (.alu .add a2 a2 (23 : Fin 32), 2) := by decide
theorem bee_at_5e : fetchRel base64EncodeToCode 0x5E = some (.alu .add a3 a3 (23 : Fin 32), 2) := by decide
theorem bee_at_60 : fetchRel base64EncodeToCode 0x60 = some (.load .lbu a1 a1 0x0, 4) := by decide
theorem bee_at_64 : fetchRel base64EncodeToCode 0x64 = some (.load .lbu a2 a2 0x0, 4) := by decide
theorem bee_at_68 : fetchRel base64EncodeToCode 0x68 = some (.load .lbu a3 a3 0x0, 4) := by decide
theorem bee_at_6c : fetchRel base64EncodeToCode 0x6C = some (.load .lbu a4 a5 0x0, 4) := by decide
theorem bee_at_70 : fetchRel base64EncodeToCode 0x70 = some (.aluImm .add (9 : Fin 32) a0 0x3, 4) := by decide
theorem bee_at_74 : fetchRel base64EncodeToCode 0x74 = some (.store .sb sp a1 0x0, 4) := by decide
theorem bee_at_78 : fetchRel base64EncodeToCode 0x78 = some (.store .sb sp a2 0x1, 4) := by decide
theorem bee_at_7c : fetchRel base64EncodeToCode 0x7C = some (.store .sb sp a3 0x2, 4) := by decide
theorem bee_at_80 : fetchRel base64EncodeToCode 0x80 = some (.store .sb sp a4 0x3, 4) := by decide
theorem bee_at_84 : fetchRel base64EncodeToCode 0x84 = some (.alu .add a1 x0 sp, 2) := by decide
theorem bee_at_86 : fetchRel base64EncodeToCode 0x86 = some (.aluImm .add a2 x0 0x4, 2) := by decide
theorem bee_at_88 : fetchRel base64EncodeToCode 0x88 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem bee_at_8a : fetchRel base64EncodeToCode 0x8A = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem bee_at_8e : fetchRel base64EncodeToCode 0x8E = some (.jalr ra ra 0x6FA, 4) := by decide
theorem bee_at_92 : fetchRel base64EncodeToCode 0x92 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFD, 2) := by decide
theorem bee_at_94 : fetchRel base64EncodeToCode 0x94 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem bee_at_96 : fetchRel base64EncodeToCode 0x96 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFF9E, 2) := by decide
theorem bee_at_98 : fetchRel base64EncodeToCode 0x98 = some (.alu .add (20 : Fin 32) (20 : Fin 32) (21 : Fin 32), 2) := by decide
theorem bee_at_9a : fetchRel base64EncodeToCode 0x9A = some (.alu .sub a0 (19 : Fin 32) (20 : Fin 32), 4) := by decide
theorem bee_at_9e : fetchRel base64EncodeToCode 0x9E = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem bee_at_a0 : fetchRel base64EncodeToCode 0xA0 = some (.alu .add (18 : Fin 32) (18 : Fin 32) (20 : Fin 32), 2) := by decide
theorem bee_at_a2 : fetchRel base64EncodeToCode 0xA2 = some (.branch .beq a0 a1 0x3A, 4) := by decide
theorem bee_at_a6 : fetchRel base64EncodeToCode 0xA6 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem bee_at_a8 : fetchRel base64EncodeToCode 0xA8 = some (.branch .bne a0 a1 0x84, 4) := by decide
theorem bee_at_ac : fetchRel base64EncodeToCode 0xAC = some (.load .lbu a0 (18 : Fin 32) 0x0, 4) := by decide
theorem bee_at_b0 : fetchRel base64EncodeToCode 0xB0 = some (.aluImm .sll a1 a0 0x1E, 4) := by decide
theorem bee_at_b4 : fetchRel base64EncodeToCode 0xB4 = some (.aluImm .srl a0 a0 0x2, 2) := by decide
theorem bee_at_b6 : fetchRel base64EncodeToCode 0xB6 = some (.aluImm .srl a1 a1 0x1A, 2) := by decide
theorem bee_at_b8 : fetchRel base64EncodeToCode 0xB8 = some (.alu .add a0 a0 (23 : Fin 32), 2) := by decide
theorem bee_at_ba : fetchRel base64EncodeToCode 0xBA = some (.alu .add a1 a1 (23 : Fin 32), 2) := by decide
theorem bee_at_bc : fetchRel base64EncodeToCode 0xBC = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem bee_at_c0 : fetchRel base64EncodeToCode 0xC0 = some (.load .lbu a1 a1 0x0, 4) := by decide
theorem bee_at_c4 : fetchRel base64EncodeToCode 0xC4 = some (.aluImm .add a2 x0 0x3D, 4) := by decide
theorem bee_at_c8 : fetchRel base64EncodeToCode 0xC8 = some (.store .sb sp a0 0x4, 4) := by decide
theorem bee_at_cc : fetchRel base64EncodeToCode 0xCC = some (.store .sb sp a1 0x5, 4) := by decide
theorem bee_at_d0 : fetchRel base64EncodeToCode 0xD0 = some (.store .sb sp a2 0x6, 4) := by decide
theorem bee_at_d4 : fetchRel base64EncodeToCode 0xD4 = some (.store .sb sp a2 0x7, 4) := by decide
theorem bee_at_d8 : fetchRel base64EncodeToCode 0xD8 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem bee_at_da : fetchRel base64EncodeToCode 0xDA = some (.jal x0 0x46, 2) := by decide
theorem bee_at_dc : fetchRel base64EncodeToCode 0xDC = some (.load .lbu a0 (18 : Fin 32) 0x0, 4) := by decide
theorem bee_at_e0 : fetchRel base64EncodeToCode 0xE0 = some (.load .lbu a1 (18 : Fin 32) 0x1, 4) := by decide
theorem bee_at_e4 : fetchRel base64EncodeToCode 0xE4 = some (.aluImm .sll a2 a0 0x10, 4) := by decide
theorem bee_at_e8 : fetchRel base64EncodeToCode 0xE8 = some (.aluImm .sll a3 a1 0x8, 4) := by decide
theorem bee_at_ec : fetchRel base64EncodeToCode 0xEC = some (.aluImm .srl a0 a0 0x2, 2) := by decide
theorem bee_at_ee : fetchRel base64EncodeToCode 0xEE = some (.aluImm .sll a1 a1 0x1C, 2) := by decide
theorem bee_at_f0 : fetchRel base64EncodeToCode 0xF0 = some (.alu .or a2 a2 a3, 2) := by decide
theorem bee_at_f2 : fetchRel base64EncodeToCode 0xF2 = some (.alu .add a0 a0 (23 : Fin 32), 2) := by decide
theorem bee_at_f4 : fetchRel base64EncodeToCode 0xF4 = some (.aluImm .sll a2 a2 0xE, 2) := by decide
theorem bee_at_f6 : fetchRel base64EncodeToCode 0xF6 = some (.aluImm .srl a1 a1 0x1A, 2) := by decide
theorem bee_at_f8 : fetchRel base64EncodeToCode 0xF8 = some (.aluImm .srl a2 a2 0x1A, 2) := by decide
theorem bee_at_fa : fetchRel base64EncodeToCode 0xFA = some (.alu .add a1 a1 (23 : Fin 32), 2) := by decide
theorem bee_at_fc : fetchRel base64EncodeToCode 0xFC = some (.alu .add a2 a2 (23 : Fin 32), 2) := by decide
theorem bee_at_fe : fetchRel base64EncodeToCode 0xFE = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem bee_at_102 : fetchRel base64EncodeToCode 0x102 = some (.load .lbu a2 a2 0x0, 4) := by decide
theorem bee_at_106 : fetchRel base64EncodeToCode 0x106 = some (.load .lbu a1 a1 0x0, 4) := by decide
theorem bee_at_10a : fetchRel base64EncodeToCode 0x10A = some (.aluImm .add a3 x0 0x3D, 4) := by decide
theorem bee_at_10e : fetchRel base64EncodeToCode 0x10E = some (.store .sb sp a0 0x8, 4) := by decide
theorem bee_at_112 : fetchRel base64EncodeToCode 0x112 = some (.store .sb sp a2 0x9, 4) := by decide
theorem bee_at_116 : fetchRel base64EncodeToCode 0x116 = some (.store .sb sp a1 0xA, 4) := by decide
theorem bee_at_11a : fetchRel base64EncodeToCode 0x11A = some (.store .sb sp a3 0xB, 4) := by decide
theorem bee_at_11e : fetchRel base64EncodeToCode 0x11E = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem bee_at_120 : fetchRel base64EncodeToCode 0x120 = some (.aluImm .add a2 x0 0x4, 2) := by decide
theorem bee_at_122 : fetchRel base64EncodeToCode 0x122 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem bee_at_124 : fetchRel base64EncodeToCode 0x124 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem bee_at_128 : fetchRel base64EncodeToCode 0x128 = some (.jalr ra ra 0x660, 4) := by decide
theorem bee_at_12c : fetchRel base64EncodeToCode 0x12C = some (.load .lw ra sp 0x2C, 2) := by decide
theorem bee_at_12e : fetchRel base64EncodeToCode 0x12E = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem bee_at_130 : fetchRel base64EncodeToCode 0x130 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem bee_at_132 : fetchRel base64EncodeToCode 0x132 = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem bee_at_134 : fetchRel base64EncodeToCode 0x134 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem bee_at_136 : fetchRel base64EncodeToCode 0x136 = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem bee_at_138 : fetchRel base64EncodeToCode 0x138 = some (.load .lw (21 : Fin 32) sp 0x14, 2) := by decide
theorem bee_at_13a : fetchRel base64EncodeToCode 0x13A = some (.load .lw (22 : Fin 32) sp 0x10, 2) := by decide
theorem bee_at_13c : fetchRel base64EncodeToCode 0x13C = some (.load .lw (23 : Fin 32) sp 0xC, 2) := by decide
theorem bee_at_13e : fetchRel base64EncodeToCode 0x13E = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem bee_at_140 : fetchRel base64EncodeToCode 0x140 = some (.jalr x0 ra 0x0, 2) := by decide
end

def beeI : List BInstr :=
  [.alu .add (22 : Fin 32) x0 a2, .alu .add (19 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 x0 0x3, .alu .divu (20 : Fin 32) a1 a0, .aluImm .sll (21 : Fin 32) (20 : Fin 32) 0x1, .alu .add (8 : Fin 32) (21 : Fin 32) (20 : Fin 32), .lui (23 : Fin 32) 0x3FCC4000, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x7D8, .alu .add a0 x0 (18 : Fin 32)]
def beeG : List BInstr :=
  [.lbu a1 a0 0x0, .lbu a2 a0 0x1, .lbu a3 a0 0x2, .aluImm .sll a4 a1 0x10, .aluImm .sll a2 a2 0x8, .aluImm .srl a1 a1 0x2, .aluImm .and a5 a3 0x3F, .alu .or a3 a3 a2, .alu .or a2 a2 a4, .alu .add a1 a1 (23 : Fin 32), .alu .add a5 a5 (23 : Fin 32), .aluImm .sll a2 a2 0xE, .aluImm .sll a3 a3 0x14, .aluImm .srl a2 a2 0x1A, .aluImm .srl a3 a3 0x1A, .alu .add a2 a2 (23 : Fin 32), .alu .add a3 a3 (23 : Fin 32), .lbu a1 a1 0x0, .lbu a2 a2 0x0, .lbu a3 a3 0x0, .lbu a4 a5 0x0, .aluImm .add (9 : Fin 32) a0 0x3, .sb sp a1 0x0, .sb sp a2 0x1, .sb sp a3 0x2, .sb sp a4 0x3, .alu .add a1 x0 sp, .aluImm .add a2 x0 0x4, .alu .add a0 x0 (22 : Fin 32)]
def beeT : List BInstr :=
  [.alu .add (20 : Fin 32) (20 : Fin 32) (21 : Fin 32), .alu .sub a0 (19 : Fin 32) (20 : Fin 32), .aluImm .add a1 x0 0x2, .alu .add (18 : Fin 32) (18 : Fin 32) (20 : Fin 32)]
def beeR1 : List BInstr :=
  [.lbu a0 (18 : Fin 32) 0x0, .aluImm .sll a1 a0 0x1E, .aluImm .srl a0 a0 0x2, .aluImm .srl a1 a1 0x1A, .alu .add a0 a0 (23 : Fin 32), .alu .add a1 a1 (23 : Fin 32), .lbu a0 a0 0x0, .lbu a1 a1 0x0, .aluImm .add a2 x0 0x3D, .sb sp a0 0x4, .sb sp a1 0x5, .sb sp a2 0x6, .sb sp a2 0x7, .aluImm .add a1 sp 0x4]
def beeR2 : List BInstr :=
  [.lbu a0 (18 : Fin 32) 0x0, .lbu a1 (18 : Fin 32) 0x1, .aluImm .sll a2 a0 0x10, .aluImm .sll a3 a1 0x8, .aluImm .srl a0 a0 0x2, .aluImm .sll a1 a1 0x1C, .alu .or a2 a2 a3, .alu .add a0 a0 (23 : Fin 32), .aluImm .sll a2 a2 0xE, .aluImm .srl a1 a1 0x1A, .aluImm .srl a2 a2 0x1A, .alu .add a1 a1 (23 : Fin 32), .alu .add a2 a2 (23 : Fin 32), .lbu a0 a0 0x0, .lbu a2 a2 0x0, .lbu a1 a1 0x0, .aluImm .add a3 x0 0x3D, .sb sp a0 0x8, .sb sp a2 0x9, .sb sp a1 0xA, .sb sp a3 0xB, .aluImm .add a1 sp 0x8]
def beeC : List BInstr :=
  [.aluImm .add a2 x0 0x4, .alu .add a0 x0 (22 : Fin 32)]
def beeL : List BInstr :=
  [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFD, .alu .add a0 x0 (9 : Fin 32)]

section
set_option maxRecDepth 20000
theorem beeI_end : blockEnd base64EncodeToCode 0x14 beeI = some 0x32 := by decide
theorem beeG_end : blockEnd base64EncodeToCode 0x34 beeG = some 0x8A := by decide
theorem beeT_end : blockEnd base64EncodeToCode 0x98 beeT = some 0xA2 := by decide
theorem beeR1_end : blockEnd base64EncodeToCode 0xAC beeR1 = some 0xDA := by decide
theorem beeR2_end : blockEnd base64EncodeToCode 0xDC beeR2 = some 0x120 := by decide
theorem beeC_end : blockEnd base64EncodeToCode 0x120 beeC = some 0x124 := by decide
theorem beeL_end : blockEnd base64EncodeToCode 0x92 beeL = some 0x96 := by decide
end

theorem bee_alpha : ∀ k, k < 64 → byteAt b64AlphabetData k = BitVec.ofNat 8 (b64Char k) := by decide

theorem bee_zx (b : BitVec 8) : (b.zeroExtend 32).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide))

theorem bee_i1 (a : BitVec 8) : aluEval .srl (a.zeroExtend 32) 0x2 = BitVec.ofNat 32 (a.toNat * 2 ^ 16 / 2 ^ 18) := by
  apply BitVec.eq_of_toNat_eq
  rw [dn_srl, bee_zx, BitVec.toNat_ofNat, show (0x2 : Word).toNat % 32 = 2 from rfl]
  have := a.isLt; omega

theorem bee_i4 (c : BitVec 8) : aluEval .and (c.zeroExtend 32) 0x3F = BitVec.ofNat 32 (c.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [show aluEval .and (c.zeroExtend 32) 0x3F = c.zeroExtend 32 &&& 0x3F from rfl,
    and_low (k := 6) (by decide) (by decide), bee_zx, BitVec.toNat_ofNat]
  have := c.isLt; omega

theorem bee_i2 (a b : BitVec 8) :
    aluEval .srl (aluEval .sll (aluEval .or (aluEval .sll (b.zeroExtend 32) 0x8) (aluEval .sll (a.zeroExtend 32) 0x10)) 0xE) 0x1A =
      BitVec.ofNat 32 ((a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8) / 2 ^ 12 % 64) := by
  have ha := a.isLt
  have hb := b.isLt
  have e1 : (aluEval .sll (b.zeroExtend 32) 0x8).toNat = b.toNat * 2 ^ 8 := by
    rw [dn_sll, bee_zx, show (0x8 : Word).toNat % 32 = 8 from rfl]; omega
  have e2 : (aluEval .sll (a.zeroExtend 32) 0x10).toNat = a.toNat * 2 ^ 16 := by
    rw [dn_sll, bee_zx, show (0x10 : Word).toNat % 32 = 16 from rfl]; omega
  have e3 := tn_or (j := 16) rfl (by rw [e1]; omega) (by rw [e2]; omega)
  rw [e1, e2] at e3
  apply BitVec.eq_of_toNat_eq
  rw [dn_srl, dn_sll, e3, BitVec.toNat_ofNat, show (0xE : Word).toNat % 32 = 14 from rfl,
    show (0x1A : Word).toNat % 32 = 26 from rfl]
  omega

theorem bee_i3 (b c : BitVec 8) :
    aluEval .srl (aluEval .sll (aluEval .or (c.zeroExtend 32) (aluEval .sll (b.zeroExtend 32) 0x8)) 0x14) 0x1A =
      BitVec.ofNat 32 ((b.toNat * 2 ^ 8 + c.toNat) / 2 ^ 6 % 64) := by
  have hb := b.isLt
  have hc := c.isLt
  have e1 : (aluEval .sll (b.zeroExtend 32) 0x8).toNat = b.toNat * 2 ^ 8 := by
    rw [dn_sll, bee_zx, show (0x8 : Word).toNat % 32 = 8 from rfl]; omega
  have e3 := tn_or (j := 8) rfl (by rw [bee_zx]; omega) (by rw [e1]; omega)
  rw [e1, bee_zx] at e3
  apply BitVec.eq_of_toNat_eq
  rw [dn_srl, dn_sll, e3, BitVec.toNat_ofNat, show (0x14 : Word).toNat % 32 = 20 from rfl,
    show (0x1A : Word).toNat % 32 = 26 from rfl]
  omega

theorem bee_i2' (a b : BitVec 8) :
    aluEval .srl (aluEval .sll (aluEval .or (aluEval .sll (a.zeroExtend 32) 0x10) (aluEval .sll (b.zeroExtend 32) 0x8)) 0xE) 0x1A =
      BitVec.ofNat 32 ((a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8) / 2 ^ 12 % 64) := by
  rw [← bee_i2]; congr 2; exact BitVec.or_comm _ _

theorem bee_r1 (a : BitVec 8) :
    aluEval .srl (aluEval .sll (a.zeroExtend 32) 0x1E) 0x1A = BitVec.ofNat 32 (a.toNat * 2 ^ 16 / 2 ^ 12 % 64) := by
  have := a.isLt
  apply BitVec.eq_of_toNat_eq
  rw [dn_srl, dn_sll, bee_zx, BitVec.toNat_ofNat, show (0x1E : Word).toNat % 32 = 30 from rfl,
    show (0x1A : Word).toNat % 32 = 26 from rfl]
  omega

theorem bee_r2 (a b : BitVec 8) :
    aluEval .srl (aluEval .sll (b.zeroExtend 32) 0x1C) 0x1A =
      BitVec.ofNat 32 ((a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8) / 2 ^ 6 % 64) := by
  have := a.isLt
  have := b.isLt
  apply BitVec.eq_of_toNat_eq
  rw [dn_srl, dn_sll, bee_zx, BitVec.toNat_ofNat, show (0x1C : Word).toNat % 32 = 28 from rfl,
    show (0x1A : Word).toNat % 32 = 26 from rfl]
  omega


theorem bee_mb4 (M : Word → BitVec 8) (F : Word) (v1 v2 v3 v4 : BitVec 8) :
    memBytes (memStore8 (memStore8 (memStore8 (memStore8 M (F + 0x0) v1) (F + 0x1) v2) (F + 0x2) v3) (F + 0x3) v4) F 4 =
      [v1.toNat, v2.toNat, v3.toNat, v4.toNat] := by
  have ne : ∀ c d : Nat, c < 4 → d < 4 → c ≠ d → F + BitVec.ofNat 32 c ≠ F + BitVec.ofNat 32 d :=
    fun c d hc hd h => add_ofNat_ne F (by omega) (by omega) h
  show [(memStore8 (memStore8 (memStore8 (memStore8 M (F + BitVec.ofNat 32 0) v1) (F + BitVec.ofNat 32 1) v2)
      (F + BitVec.ofNat 32 2) v3) (F + BitVec.ofNat 32 3) v4 (F + BitVec.ofNat 32 0)).toNat,
    (memStore8 (memStore8 (memStore8 (memStore8 M (F + BitVec.ofNat 32 0) v1) (F + BitVec.ofNat 32 1) v2)
      (F + BitVec.ofNat 32 2) v3) (F + BitVec.ofNat 32 3) v4 (F + BitVec.ofNat 32 1)).toNat,
    (memStore8 (memStore8 (memStore8 (memStore8 M (F + BitVec.ofNat 32 0) v1) (F + BitVec.ofNat 32 1) v2)
      (F + BitVec.ofNat 32 2) v3) (F + BitVec.ofNat 32 3) v4 (F + BitVec.ofNat 32 2)).toNat,
    (memStore8 (memStore8 (memStore8 (memStore8 M (F + BitVec.ofNat 32 0) v1) (F + BitVec.ofNat 32 1) v2)
      (F + BitVec.ofNat 32 2) v3) (F + BitVec.ofNat 32 3) v4 (F + BitVec.ofNat 32 3)).toNat] = _
  rw [memStore8_ne (ne 0 3 (by decide) (by decide) (by decide)), memStore8_ne (ne 0 2 (by decide) (by decide) (by decide)),
    memStore8_ne (ne 0 1 (by decide) (by decide) (by decide)), memStore8_same,
    memStore8_ne (ne 1 3 (by decide) (by decide) (by decide)), memStore8_ne (ne 1 2 (by decide) (by decide) (by decide)),
    memStore8_same, memStore8_ne (ne 2 3 (by decide) (by decide) (by decide)), memStore8_same, memStore8_same]

/-- The memory the hasher and the stack frame may change: outside them,
memory is `M0`'s. -/
def BeeFrame (M M0 : Word → BitVec 8) (S R : Word) : Prop :=
  ∀ x, Sep S 0x68 x 1 → Sep R 0x130 x 1 → M x = M0 x

/-- What `encode_to`'s calls need of memory that agrees with `M0` outside
the hasher and the stack. -/
structure BeeEnv (M0 : Word → BitVec 8) (S D sp0 : Word) (n : Nat) : Prop where
  cE : CodeIn M0 BEE base64EncodeToCode
  cA : CodeIn M0 BAL b64AlphabetData
  cU : CodeIn M0 (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode
  cBlk : CodeIn M0 (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode
  cC : CodeIn M0 (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M0 (BitVec.ofNat 32 sha256CompressAddress + 0x25A) rangeFromIndexCode
  cK : CodeIn M0 (BitVec.ofNat 32 shaKAddress) shaKData
  cMS : CodeIn M0 (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M0 (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  hS : S.toNat % 4 = 0
  hSw : S.toNat + 0x68 ≤ 0x40000000
  hsp : sp0.toNat % 16 = 0
  hspl : 0x130 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hDw : D.toNat + n ≤ 0x40000000
  sDS : Sep D n S 0x68
  sDF : Sep D n (sp0 + 0xFFFFFED0) 0x130
  sSF : Sep S 0x68 (sp0 + 0xFFFFFED0) 0x130
  sKS : Sep (BitVec.ofNat 32 shaKAddress) 256 S 0x68
  sKF : Sep (BitVec.ofNat 32 shaKAddress) 256 (sp0 + 0xFFFFFED0) 0x130
  sAS : Sep BAL 64 S 0x68
  sAF : Sep BAL 64 (sp0 + 0xFFFFFED0) 0x130


set_option maxRecDepth 20000 in
/-- Memory that agrees with `M0` outside the hasher and the stack still holds
the code and data, and `update` can run with its input `o` bytes into the
frame. -/
theorem bee_upd {M0 M : Word → BitVec 8} {S D sp0 : Word} {n : Nat} (E : BeeEnv M0 S D sp0 n)
    (fr : BeeFrame M M0 S (sp0 + 0xFFFFFED0)) {o : Nat} (ho : o ≤ 8) :
    UpdEnv M S (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 o) (sp0 + 0xFFFFFFD0) 4 ∧
      CodeIn M BEE base64EncodeToCode ∧ CodeIn M BAL b64AlphabetData := by
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFFED0 = R := ⟨_, rfl⟩
  have sSF := E.sSF
  have sKF := E.sKF
  have sAF := E.sAF
  rw [hR] at fr sSF sKF sAF
  have hRn : R.toNat = sp0.toNat - 0x130 := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFED0 : Word).toNat = 2 ^ 32 - 0x130 from rfl]; have := E.hspl; omega
  have hspw := E.hspw
  have hSw := E.hSw
  have keep : ∀ {A : Word} {code : List Nat}, CodeIn M0 A code → Sep A code.length S 0x68 →
      Sep A code.length R 0x130 → CodeIn M A code := fun hc h1 h2 i hi => by
    rw [fr _ (h1.sub (c := i) (l := 1) (by omega)).symm (h2.sub (c := i) (l := 1) (by omega)).symm]; exact hc i hi
  have hiC : ∀ {A : Word} {code : List Nat}, CodeIn M0 A code → 0x40000000 ≤ A.toNat → A.toNat + code.length ≤ 2 ^ 32 →
      CodeIn M A code := fun hc h1 h2 =>
    keep hc (data_code hSw h1 h2).symm (data_code (by rw [hRn]; omega) h1 h2).symm
  have eFR : sp0 + 0xFFFFFFD0 + 0xFFFFFF00 = R := by rw [← hR, BitVec.add_assoc]; rfl
  have eFo : ∀ c, sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x100 + c) := fun c => by
    have e : (0xFFFFFFD0 : Word) + BitVec.ofNat 32 c = 0xFFFFFED0 + BitVec.ofNat 32 (0x100 + c) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (0xFFFFFFD0 : Word).toNat = 2 ^ 32 - 0x30 from rfl, show (0xFFFFFED0 : Word).toNat = 2 ^ 32 - 0x130 from rfl]
      omega
    rw [← hR, BitVec.add_assoc, e, ← BitVec.add_assoc]
  have hFn : (sp0 + 0xFFFFFFD0).toNat = sp0.toNat - 0x30 := by
    rw [BitVec.toNat_add, show (0xFFFFFFD0 : Word).toNat = 2 ^ 32 - 0x30 from rfl]; have := E.hspl; omega
  have hsp := E.hsp
  have hspl := E.hspl
  have U : UpdEnv M S (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 o) (sp0 + 0xFFFFFFD0) 4 :=
    ⟨hiC E.cU (by decide) (by decide), hiC E.cBlk (by decide) (by decide), hiC E.cC (by decide) (by decide),
      hiC E.cI (by decide) (by decide), keep E.cK E.sKS sKF, hiC E.cMS (by decide) (by decide),
      hiC E.cMB (by decide) (by decide), E.hS, hSw, by rw [hFn]; omega, by rw [hFn]; omega, by rw [hFn]; omega,
      by rw [eFo, BitVec.toNat_add, BitVec.toNat_ofNat, hRn]; omega,
      by rw [eFo]; exact (sSF.symm.sub (c := 0x100 + o) (l := 4) (by omega)),
      by
        rw [eFo, eFR]
        have := sep_offsets R (c := 0x100 + o) (n := 4) (d := 0) (k := 0x100) (Or.inr (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this,
      by rw [eFR]; have := sSF.subR (c := 0) (l := 0x100) (by decide); rwa [add_ofNat_zero] at this,
      E.sKS,
      by rw [eFR]; have := sKF.subR (c := 0) (l := 0x100) (by decide); rwa [add_ofNat_zero] at this⟩
  refine ⟨U,
    hiC E.cE (by decide) (by decide), keep E.cA E.sAS sAF⟩


set_option maxRecDepth 20000 in
/-- A call of `update` from `encode_to` on the 4 characters at `sp + o`. -/
theorem bee_call {M0 M : Word → BitVec 8} {S D sp0 : Word} {n : Nat} (E : BeeEnv M0 S D sp0 n)
    (fr : BeeFrame M M0 S (sp0 + 0xFFFFFED0)) {nn : Machine} {off o : Nat} {imm : Word} {msg : Bytes} (ho : o ≤ 8) (hoff : off % 2 = 0)
    (st : St M BEE nn off (reg nn)) (h1 : fetchRel base64EncodeToCode off = some (.auipc ra 0xFFFFE000, 4))
    (h2 : fetchRel base64EncodeToCode (off + 4) = some (.jalr ra ra imm, 4))
    (hb : BEE + BitVec.ofNat 32 off + 0xFFFFE000 + imm = BitVec.ofNat 32 shaUpdateAddress)
    (ra0 : reg nn a0 = S) (ra1 : reg nn a1 = sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 o) (ra2 : reg nn a2 = BitVec.ofNat 32 4)
    (rsp : reg nn sp = sp0 + 0xFFFFFFD0) (H : HasherAt M S msg) (hlen : msg.length + 4 < 2 ^ 32) :
    ∃ nn', Steps nn nn' ∧ St nn'.mem BEE nn' (off + 8) (reg nn') ∧ BeeFrame nn'.mem M0 S (sp0 + 0xFFFFFED0) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFD0 + 0xFFFFFF00) 0x100 x 1 → Sep S 0x68 x 1 → nn'.mem x = M x) ∧
      HasherAt nn'.mem S (msg ++ memBytes M (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 o) 4) ∧
      reg nn' sp = sp0 + 0xFFFFFFD0 ∧
      ∀ r, r.val ∈ [4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' r = reg nn r := by
  obtain ⟨U, hcE, -⟩ := bee_upd E fr ho
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := st.callRa hcE h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg m1 r = reg nn r := fun r hr => by rw [regs1, upd_ne' hr st.zero]
  obtain ⟨m2, c2, pc2, sp2, K2, H2, fr2⟩ := shaUpdate_correct m1 (retAddr := BEE + BitVec.ofNat 32 (off + 8))
    (by rw [mem1]; exact U) pc1 (by rw [r1 a0 (by decide), ra0]) (by rw [r1 a1 (by decide), ra1])
    (by rw [r1 a2 (by decide), ra2]) (by rw [regs1]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at _ (by decide) _ (by omega)))
    (by rw [r1 sp (by decide), rsp]) (by rw [mem1]; exact H) (by decide) hlen
  rw [mem1] at H2 fr2
  have hF : (sp0 + 0xFFFFFFD0 + 0xFFFFFF00 : Word) = sp0 + 0xFFFFFED0 + BitVec.ofNat 32 0 := by
    rw [add_ofNat_zero, BitVec.add_assoc]; rfl
  refine ⟨m2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, fun x hS hR => ?_, fr2, H2, sp2, fun r hr => ?_⟩
  · rw [fr2 x (by rw [hF]; exact (hR.symm.subR (c := 0) (l := 0x100) (by decide)).symm) hS, fr x hS hR]
  · rw [K2 r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide),
      r1 r (by revert hr; revert r; decide)]

#print axioms bee_call

theorem bee_lk {M : Word → BitVec 8} (hA : CodeIn M BAL b64AlphabetData) {k : Nat} (hk : k < 64) :
    ((M (aluEval .add (BitVec.ofNat 32 k) BAL + 0)).zeroExtend 32).extractLsb' 0 8 = BitVec.ofNat 8 (b64Char k) := by
  rw [dt_zext8, add_lit_zero, show aluEval .add (BitVec.ofNat 32 k) BAL = BAL + BitVec.ofNat 32 k from BitVec.add_comm _ _,
    hA k (by rw [show b64AlphabetData.length = 64 from rfl]; exact hk), bee_alpha k hk]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- A group's characters, from 0x34: four lookups in the alphabet stored at
`sp`. -/
theorem bee_blockG (M : Word → BitVec 8) (f : Fin 32 → Word) (hz : f 0 = 0) {p F : Word} (ra0 : f a0 = p)
    (r23 : f 23 = BAL) (rsp : f sp = F) (hA : CodeIn M BAL b64AlphabetData) :
    (runBlock beeG (M, f)).1 =
      memStore8 (memStore8 (memStore8 (memStore8 M (F + 0x0)
        (BitVec.ofNat 8 (b64Char ((M (p + 0)).toNat * 2 ^ 16 / 2 ^ 18)))) (F + 0x1)
        (BitVec.ofNat 8 (b64Char (((M (p + 0)).toNat * 2 ^ 16 + (M (p + 1)).toNat * 2 ^ 8) / 2 ^ 12 % 64)))) (F + 0x2)
        (BitVec.ofNat 8 (b64Char (((M (p + 1)).toNat * 2 ^ 8 + (M (p + 2)).toNat) / 2 ^ 6 % 64)))) (F + 0x3)
        (BitVec.ofNat 8 (b64Char ((M (p + 2)).toNat % 64))) := by
  simp +decide only [runBlock, BInstr.run, beeG, upd_app, ↓reduceIte]
  rw [ra0, r23, rsp, bee_i1, bee_i2, bee_i3, bee_i4]
  have := (M (p + 0)).isLt
  rw [bee_lk hA (by omega), bee_lk hA (Nat.mod_lt _ (by decide)), bee_lk hA (Nat.mod_lt _ (by decide)),
    bee_lk hA (Nat.mod_lt _ (by decide))]

#print axioms bee_blockG

theorem bee_enc3 {a b c : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    base64Encode [a, b, c] = [b64Char (a * 2 ^ 16 / 2 ^ 18), b64Char ((a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 12 % 64),
      b64Char ((b * 2 ^ 8 + c) / 2 ^ 6 % 64), b64Char (c % 64)] := by
  have e1 : (a * 2 ^ 16 + b * 2 ^ 8 + c) / 2 ^ 18 = a * 2 ^ 16 / 2 ^ 18 := by omega
  have e2 : (a * 2 ^ 16 + b * 2 ^ 8 + c) / 2 ^ 12 % 64 = (a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 12 % 64 := by omega
  have e3 : (a * 2 ^ 16 + b * 2 ^ 8 + c) / 2 ^ 6 % 64 = (b * 2 ^ 8 + c) / 2 ^ 6 % 64 := by omega
  have e4 : (a * 2 ^ 16 + b * 2 ^ 8 + c) % 64 = c % 64 := by omega
  show [b64Char ((a * 2 ^ 16 + b * 2 ^ 8 + c) / 2 ^ 18), b64Char ((a * 2 ^ 16 + b * 2 ^ 8 + c) / 2 ^ 12),
    b64Char ((a * 2 ^ 16 + b * 2 ^ 8 + c) / 2 ^ 6), b64Char (a * 2 ^ 16 + b * 2 ^ 8 + c)] ++ base64Encode [] = _
  rw [show base64Encode [] = [] by simp only [base64Encode], List.append_nil, e1,
    ← b64Char_mod ((a * 2 ^ 16 + b * 2 ^ 8 + c) / 2 ^ 12), e2, ← b64Char_mod ((a * 2 ^ 16 + b * 2 ^ 8 + c) / 2 ^ 6), e3,
    ← b64Char_mod (a * 2 ^ 16 + b * 2 ^ 8 + c), e4]

theorem bee_enc1 {a : Nat} (ha : a < 256) :
    base64Encode [a] = [b64Char (a * 2 ^ 16 / 2 ^ 18), b64Char (a * 2 ^ 16 / 2 ^ 12 % 64), 61, 61] := by
  show [b64Char (a * 2 ^ 16 / 2 ^ 18), b64Char (a * 2 ^ 16 / 2 ^ 12), b64Pad, b64Pad] = _
  rw [← b64Char_mod (a * 2 ^ 16 / 2 ^ 12)]; rfl

theorem bee_enc2 {a b : Nat} (ha : a < 256) (hb : b < 256) :
    base64Encode [a, b] = [b64Char (a * 2 ^ 16 / 2 ^ 18), b64Char ((a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 12 % 64),
      b64Char ((a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 6 % 64), 61] := by
  have e1 : (a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 18 = a * 2 ^ 16 / 2 ^ 18 := by omega
  show [b64Char ((a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 18), b64Char ((a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 12),
    b64Char ((a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 6), b64Pad] = _
  rw [e1, ← b64Char_mod ((a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 12), ← b64Char_mod ((a * 2 ^ 16 + b * 2 ^ 8) / 2 ^ 6)]; rfl

theorem bee_st4 (M : Word → BitVec 8) (x a1 a2 a3 a4 : Word) (v1 v2 v3 v4 : BitVec 8) (h1 : x ≠ a1) (h2 : x ≠ a2)
    (h3 : x ≠ a3) (h4 : x ≠ a4) : memStore8 (memStore8 (memStore8 (memStore8 M a1 v1) a2 v2) a3 v3) a4 v4 x = M x := by
  rw [memStore8_ne h4, memStore8_ne h3, memStore8_ne h2, memStore8_ne h1]

theorem bee_ne {R F x : Word} {c w : Nat} (hc : c + 0xC ≤ w) (hw : w ≤ 0x130) (eF : F = R + BitVec.ofNat 32 c)
    (hx : Sep R w x 1) : ∀ k, k < 0xC → x ≠ F + BitVec.ofNat 32 k := fun k hk e => by
  have := hx.symm.subR (c := c + k) (l := 1) (by omega)
  rw [e, eF, add_ofNat_assoc] at this
  exact this 0 (by decide) 0 (by decide) rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- One group, from 0x34 to 0x96: the four characters of the three bytes at
`p` go into the hasher. -/
theorem bee_group {M0 M : Word → BitVec 8} {S D sp0 : Word} {n : Nat} (E : BeeEnv M0 S D sp0 n)
    (fr : BeeFrame M M0 S (sp0 + 0xFFFFFED0)) {nn : Machine} {p : Word} {msg : Bytes}
    (st : St M BEE nn 0x34 (reg nn)) (ra0 : reg nn a0 = p) (r23 : reg nn 23 = BAL) (r22 : reg nn 22 = S)
    (rsp : reg nn sp = sp0 + 0xFFFFFFD0) (H : HasherAt M S msg) (hlen : msg.length + 4 < 2 ^ 32) :
    ∃ nn', Steps nn nn' ∧ St nn'.mem BEE nn' 0x96 (reg nn') ∧ BeeFrame nn'.mem M0 S (sp0 + 0xFFFFFED0) ∧
      (∀ x, Sep (sp0 + 0xFFFFFED0) 0x10C x 1 → Sep S 0x68 x 1 → nn'.mem x = M x) ∧
      HasherAt nn'.mem S (msg ++ base64Encode [(M (p + 0)).toNat, (M (p + 1)).toNat, (M (p + 2)).toNat]) ∧
      reg nn' sp = sp0 + 0xFFFFFFD0 ∧ reg nn' a0 = p + 3 ∧ reg nn' 8 = aluEval .add (reg nn 8) 0xFFFFFFFD ∧
      ∀ r, r.val ∈ [4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' r = reg nn r := by
  have hz := st.zero
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFFED0 = R := ⟨_, rfl⟩
  have eF : sp0 + 0xFFFFFFD0 = R + BitVec.ofNat 32 0x100 := by rw [← hR, BitVec.add_assoc]; rfl
  obtain ⟨-, hcE, hcA⟩ := bee_upd E fr (o := 0) (by decide)
  have hRn : R.toNat = sp0.toNat - 0x130 := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFED0 : Word).toNat = 2 ^ 32 - 0x130 from rfl]; have := E.hspl; omega
  have hspw := E.hspw
  have sFC : ∀ k, k < 0xC → Sep (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 k) 1 BEE base64EncodeToCode.length := fun k hk => by
    rw [eF, add_ofNat_assoc]
    exact data_code (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, hRn]; omega) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := St.block beeG st hcE beeG_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, beeG, upd_app, ↓reduceIte, and_true, true_and]
    rw [rsp]
    exact ⟨by rw [add_lit_zero]; have := sFC 0 (by decide); rwa [add_ofNat_zero] at this, sFC 1 (by decide),
      sFC 2 (by decide), sFC 3 (by decide)⟩)
  have R1 : ∀ r, reg n1 r = (runBlock beeG (M, reg nn)).2 r := u1.regs
  obtain ⟨M1, hM1⟩ : ∃ M1, (runBlock beeG (M, reg nn)).1 = M1 := ⟨_, rfl⟩
  have hM1' := bee_blockG M (reg nn) hz ra0 r23 rsp hcA
  rw [hM1] at u1 hM1'
  have K1 : ∀ q, q.val ∉ [9, 10, 11, 12, 13, 14, 15] → reg n1 q = reg nn q := fun q hq => by
    have hd : q ∉ beeG.filterMap BInstr.dst := by
      simp only [beeG, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R1, runBlock_reg _ _ _ q hz hd]
  have M1y : ∀ {w : Nat} (x : Word), 0x10C ≤ w → w ≤ 0x130 → Sep R w x 1 → M1 x = M x := fun {w} x hw1 hw2 hx => by
    rw [hM1']
    exact bee_st4 _ _ _ _ _ _ _ _ _ _
      (by rw [add_lit_zero]; have := bee_ne (by omega) hw2 eF hx 0 (by decide); rwa [add_ofNat_zero] at this)
      (bee_ne (by omega) hw2 eF hx 1 (by decide)) (bee_ne (by omega) hw2 eF hx 2 (by decide))
      (bee_ne (by omega) hw2 eF hx 3 (by decide))
  have M1x : ∀ x, Sep R 0x130 x 1 → M1 x = M x := fun x hx => M1y x (by decide) (by decide) hx
  have fr1 : BeeFrame M1 M0 S (sp0 + 0xFFFFFED0) := fun x hS hx => by
    rw [hR] at hx; rw [M1x x hx, fr x hS (by rw [hR]; exact hx)]
  have sSF := E.sSF
  rw [hR] at sSF
  have H1 : HasherAt M1 S msg := H.copy fun i hi => M1x _ (sSF.sub (c := i) (l := 1) (by omega)).symm
  have v11 : reg n1 a1 = sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 0 := by
    rw [R1, add_ofNat_zero]; simp +decide only [runBlock, BInstr.run, beeG, upd_app, ↓reduceIte]
    all_goals (try rw [hz]); all_goals (try rw [dn_z]); rw [rsp]
  have v12 : reg n1 a2 = BitVec.ofNat 32 4 := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, beeG, upd_app, ↓reduceIte]
    all_goals (try rw [hz]); all_goals rfl
  have v10 : reg n1 a0 = S := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, beeG, upd_app, ↓reduceIte]
    all_goals (try rw [hz]); all_goals (try rw [dn_z]); rw [r22]
  have v9 : reg n1 9 = p + 3 := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, beeG, upd_app, ↓reduceIte]; rw [ra0]; rfl
  obtain ⟨n2, c2, u2, fr2, frM, H2, sp2, K2⟩ := bee_call E fr1 (o := 0) (off := 0x8A) (by decide) (by decide) u1.self
    bee_at_8a bee_at_8e (by decide) v10 v11 v12 (by rw [K1 sp (by decide), rsp]) H1 hlen
  obtain ⟨n3, c3, u3⟩ := St.block beeL u2 (bee_upd E fr2 (o := 0) (by decide)).2.1 beeL_end
    (by simp only [BlockOk, BInstr.ok, beeL, and_self])
  have R3 : ∀ r, reg n3 r = (runBlock beeL (n2.mem, reg n2)).2 r := u3.regs
  have mem3 : n3.mem = n2.mem := by rw [u3.mem]; simp +decide only [runBlock, BInstr.run, beeL]
  have K3 : ∀ q, q.val ∉ [8, 10] → reg n3 q = reg n2 q := fun q hq => by
    have hd : q ∉ beeL.filterMap BInstr.dst := by
      simp only [beeL, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R3, runBlock_reg _ _ _ q u2.zero hd]
  have hb := (M (p + 0)).isLt
  have hb1 := (M (p + 1)).isLt
  have hb2 := (M (p + 2)).isLt
  have eRF : sp0 + 0xFFFFFFD0 + 0xFFFFFF00 = R + BitVec.ofNat 32 0 := by rw [add_ofNat_zero, ← hR, BitVec.add_assoc]; rfl
  refine ⟨n3, c1.trans (c2.trans c3), ⟨u3.pc, rfl, fun _ => rfl⟩, by rw [mem3]; exact fr2, fun x hx hS => ?_, ?_,
    by rw [K3 sp (by decide), sp2], ?_, ?_, fun r hr => ?_⟩
  · rw [hR] at hx
    rw [mem3, frM x (by rw [eRF]; exact (hx.symm.subR (c := 0) (l := 0x100) (by decide)).symm) hS,
      M1y x (by decide) (by decide) hx]
  · rw [mem3, bee_enc3 hb hb1 hb2]
    rw [add_ofNat_zero, hM1', bee_mb4] at H2
    have l : ∀ v, (BitVec.ofNat 8 (b64Char v)).toNat = b64Char v := fun v => by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (b64Char_lt v)
    rw [l, l, l, l] at H2
    exact H2
  · rw [R3]; simp +decide only [runBlock, BInstr.run, beeL, upd_app, ↓reduceIte]
    rw [dn_z, K2 9 (by decide), v9]
  · rw [R3]; simp +decide only [runBlock, BInstr.run, beeL, upd_app, ↓reduceIte]
    rw [K2 8 (by decide), K1 8 (by decide)]
  · rw [K3 r (by revert hr; revert r; decide), K2 r (by revert hr; revert r; decide),
      K1 r (by revert hr; revert r; decide)]

#print axioms bee_group

end C3.RV32
