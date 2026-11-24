import C3BootProofs.Proofs.X509ReadTime
import C3BootProofs.Proofs.CtAssign
import C3BootProofs.Proofs.CtInto
import C3BootProofs.Spec.Base64

/-!
# `base64::decode_into`, as compiled

`c3_verify::base64::decode_into` decodes canonical base64 text four
characters at a time: each group's 6-bit values become 24 bits, the bytes
the padding drops must be zero, and the bytes it keeps go out through
`copy_from_slice`. `base64DecodeInto_correct` matches it to `Spec.Base64`'s
`base64Decode`.
-/

namespace C3

/-- The character values of a group folded into its bits, most significant
first. -/
def bdiFold (val : Nat → Option Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, acc => some acc
  | r + 1, j, acc => (val j).bind fun v => bdiFold val r (j + 1) (acc * 64 + v)

/-- The padding `decode_into` counts in a group: only the last group may end
in `=`. -/
def bdiPad (last : Bool) (c2 c3 : Nat) : Nat :=
  if last = true ∧ c3 = 61 then (if c2 = 61 then 2 else 1) else 0

/-- The bytes a group's bits hold, or `none` when the bytes the padding
drops aren't zero. -/
def bdiBytes (bits pad : Nat) : Option Bytes := do
  let bytes := [bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256]
  require ((bytes.drop (3 - pad)).all (· == 0))
  pure (bytes.take (3 - pad))

theorem bdiPad_le (last : Bool) (c2 c3 : Nat) : bdiPad last c2 c3 ≤ 2 := by
  unfold bdiPad
  by_cases h : last = true ∧ c3 = 61
  · rw [if_pos h]; by_cases h2 : c2 = 61
    · rw [if_pos h2]; exact Nat.le_refl 2
    · rw [if_neg h2]; exact Nat.le_succ 1
  · rw [if_neg h]; exact Nat.zero_le 2

theorem b64Value_lt {c v : Nat} (h : b64Value c = some v) : v < 64 := by
  unfold b64Value at h
  by_cases h1 : 65 ≤ c ∧ c ≤ 90
  · rw [if_pos h1] at h; cases h; omega
  rw [if_neg h1] at h
  by_cases h2 : 97 ≤ c ∧ c ≤ 122
  · rw [if_pos h2] at h; cases h; omega
  rw [if_neg h2] at h
  by_cases h3 : 48 ≤ c ∧ c ≤ 57
  · rw [if_pos h3] at h; cases h; omega
  rw [if_neg h3] at h
  by_cases h4 : c = 43
  · rw [if_pos h4] at h; cases h; decide
  rw [if_neg h4] at h
  by_cases h5 : c = 47
  · rw [if_pos h5] at h; cases h; decide
  rw [if_neg h5] at h; cases h

theorem b64Group_fold (c : Nat → Nat) (pad : Nat) (hp : pad ≤ 2) :
    b64Group (c 0) (c 1) (c 2) (c 3) pad =
      (bdiFold (fun j => if 4 - pad ≤ j then some 0 else b64Value (c j)) 4 0 0).bind fun bits => bdiBytes bits pad := by
  obtain rfl | rfl | rfl : pad = 0 ∨ pad = 1 ∨ pad = 2 := by omega
  all_goals
    unfold b64Group bdiFold bdiFold bdiFold bdiFold bdiFold bdiBytes
    cases b64Value (c 0) <;> cases b64Value (c 1) <;> cases b64Value (c 2) <;> cases b64Value (c 3) <;> (try simp only [Nat.zero_mul, Nat.zero_add]) <;> rfl

theorem bind_none {α β : Type} (x : Option α) : (x.bind fun _ => (none : Option β)) = none := by
  cases x <;> rfl

theorem b64_cons (c0 c1 c2 c3 : Nat) (rest : Bytes) :
    base64Decode (c0 :: c1 :: c2 :: c3 :: rest) =
      (b64Group c0 c1 c2 c3 (bdiPad rest.isEmpty c2 c3)).bind fun g => (base64Decode rest).map (g ++ ·) := by
  cases rest with
  | nil =>
    have hp : bdiPad ([] : Bytes).isEmpty c2 c3 = if c2 = b64Pad ∧ c3 = b64Pad then 2 else if c3 = b64Pad then 1 else 0 := by
      unfold bdiPad b64Pad
      by_cases h3 : c3 = 61
      · by_cases h2 : c2 = 61
        · rw [if_pos ⟨rfl, h3⟩, if_pos h2, if_pos ⟨h2, h3⟩]
        · rw [if_pos ⟨rfl, h3⟩, if_neg h2, if_neg (fun h => h2 h.1), if_pos h3]
      · rw [if_neg (fun h => h3 h.2), if_neg (fun h => h3 h.2), if_neg h3]
    rw [hp]
    simp only [base64Decode]
    cases b64Group c0 c1 c2 c3 _ <;> simp only [Option.bind, Option.map, List.append_nil]
  | cons r rs =>
    have hp : bdiPad (r :: rs).isEmpty c2 c3 = 0 := rfl
    rw [hp]
    cases h1 : b64Group c0 c1 c2 c3 0 <;> cases h2 : base64Decode (r :: rs) <;> simp only [base64Decode, h1, h2] <;> rfl

theorem b64_len : ∀ xs : Bytes, xs.length % 4 ≠ 0 → base64Decode xs = none
  | [] => fun h => (h rfl).elim
  | [_] => fun _ => by simp only [base64Decode]
  | [_, _] => fun _ => by simp only [base64Decode]
  | [_, _, _] => fun _ => by simp only [base64Decode]
  | [_, _, _, _] => fun h => absurd (by simp only [List.length_cons, List.length_nil]) h
  | c0 :: c1 :: c2 :: c3 :: r :: rs => fun h => by
    rw [b64_cons, b64_len (r :: rs) (by simp only [List.length_cons] at h ⊢; omega)]
    exact bind_none _

end C3

namespace C3.RV32

open C3.Image

abbrev BDI : Word := BitVec.ofNat 32 base64DecodeIntoAddress

section
set_option maxRecDepth 20000
theorem bdi_at_0 : fetchRel base64DecodeIntoCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem bdi_at_2 : fetchRel base64DecodeIntoCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem bdi_at_4 : fetchRel base64DecodeIntoCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem bdi_at_6 : fetchRel base64DecodeIntoCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem bdi_at_8 : fetchRel base64DecodeIntoCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem bdi_at_a : fetchRel base64DecodeIntoCode 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem bdi_at_c : fetchRel base64DecodeIntoCode 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem bdi_at_e : fetchRel base64DecodeIntoCode 0xE = some (.store .sw sp (21 : Fin 32) 0x24, 2) := by decide
theorem bdi_at_10 : fetchRel base64DecodeIntoCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x20, 2) := by decide
theorem bdi_at_12 : fetchRel base64DecodeIntoCode 0x12 = some (.store .sw sp (23 : Fin 32) 0x1C, 2) := by decide
theorem bdi_at_14 : fetchRel base64DecodeIntoCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x18, 2) := by decide
theorem bdi_at_16 : fetchRel base64DecodeIntoCode 0x16 = some (.store .sw sp (25 : Fin 32) 0x14, 2) := by decide
theorem bdi_at_18 : fetchRel base64DecodeIntoCode 0x18 = some (.store .sw sp (26 : Fin 32) 0x10, 2) := by decide
theorem bdi_at_1a : fetchRel base64DecodeIntoCode 0x1A = some (.store .sw sp (27 : Fin 32) 0xC, 2) := by decide
theorem bdi_at_1c : fetchRel base64DecodeIntoCode 0x1C = some (.alu .add (23 : Fin 32) x0 a3, 2) := by decide
theorem bdi_at_1e : fetchRel base64DecodeIntoCode 0x1E = some (.aluImm .and a3 a2 0x3, 4) := by decide
theorem bdi_at_22 : fetchRel base64DecodeIntoCode 0x22 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem bdi_at_24 : fetchRel base64DecodeIntoCode 0x24 = some (.branch .beq a3 x0 0xE, 2) := by decide
theorem bdi_at_26 : fetchRel base64DecodeIntoCode 0x26 = some (.lui a0 0x2000, 2) := by decide
theorem bdi_at_28 : fetchRel base64DecodeIntoCode 0x28 = some (.aluImm .add a0 a0 0xFFFFFC01, 4) := by decide
theorem bdi_at_2c : fetchRel base64DecodeIntoCode 0x2C = some (.store .sh (18 : Fin 32) a0 0x0, 4) := by decide
theorem bdi_at_30 : fetchRel base64DecodeIntoCode 0x30 = some (.jal x0 0x14A, 2) := by decide
theorem bdi_at_32 : fetchRel base64DecodeIntoCode 0x32 = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem bdi_at_34 : fetchRel base64DecodeIntoCode 0x34 = some (.aluImm .add a6 x0 0x0, 2) := by decide
theorem bdi_at_36 : fetchRel base64DecodeIntoCode 0x36 = some (.aluImm .srl a0 a2 0x2, 4) := by decide
theorem bdi_at_3a : fetchRel base64DecodeIntoCode 0x3A = some (.aluImm .add (17 : Fin 32) a0 0xFFFFFFFF, 4) := by decide
theorem bdi_at_3e : fetchRel base64DecodeIntoCode 0x3E = some (.alu .add (22 : Fin 32) a1 a2, 4) := by decide
theorem bdi_at_42 : fetchRel base64DecodeIntoCode 0x42 = some (.aluImm .add (6 : Fin 32) sp 0x9, 4) := by decide
theorem bdi_at_46 : fetchRel base64DecodeIntoCode 0x46 = some (.alu .sltu (26 : Fin 32) x0 a2, 4) := by decide
theorem bdi_at_4a : fetchRel base64DecodeIntoCode 0x4A = some (.lui a0 0x10000, 2) := by decide
theorem bdi_at_4c : fetchRel base64DecodeIntoCode 0x4C = some (.aluImm .add (21 : Fin 32) x0 0x4, 2) := by decide
theorem bdi_at_4e : fetchRel base64DecodeIntoCode 0x4E = some (.aluImm .add (25 : Fin 32) a0 0xFFFFFF00, 4) := by decide
theorem bdi_at_52 : fetchRel base64DecodeIntoCode 0x52 = some (.aluImm .add (20 : Fin 32) x0 0x1A, 2) := by decide
theorem bdi_at_54 : fetchRel base64DecodeIntoCode 0x54 = some (.aluImm .add (30 : Fin 32) x0 0xA, 2) := by decide
theorem bdi_at_56 : fetchRel base64DecodeIntoCode 0x56 = some (.branch .beq a1 (22 : Fin 32) 0x10E, 4) := by decide
theorem bdi_at_5a : fetchRel base64DecodeIntoCode 0x5A = some (.aluImm .add a5 x0 0x0, 2) := by decide
theorem bdi_at_5c : fetchRel base64DecodeIntoCode 0x5C = some (.aluImm .add a3 x0 0x0, 2) := by decide
theorem bdi_at_5e : fetchRel base64DecodeIntoCode 0x5E = some (.load .lbu a0 a1 0x3, 4) := by decide
theorem bdi_at_62 : fetchRel base64DecodeIntoCode 0x62 = some (.load .lbu a2 a1 0x2, 4) := by decide
theorem bdi_at_66 : fetchRel base64DecodeIntoCode 0x66 = some (.alu .xor (9 : Fin 32) (19 : Fin 32) (17 : Fin 32), 4) := by decide
theorem bdi_at_6a : fetchRel base64DecodeIntoCode 0x6A = some (.aluImm .xor a0 a0 0x3D, 4) := by decide
theorem bdi_at_6e : fetchRel base64DecodeIntoCode 0x6E = some (.alu .or a0 a0 (9 : Fin 32), 2) := by decide
theorem bdi_at_70 : fetchRel base64DecodeIntoCode 0x70 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem bdi_at_74 : fetchRel base64DecodeIntoCode 0x74 = some (.aluImm .add a2 a2 0xFFFFFFC3, 4) := by decide
theorem bdi_at_78 : fetchRel base64DecodeIntoCode 0x78 = some (.aluImm .sltu a2 a2 0x1, 4) := by decide
theorem bdi_at_7c : fetchRel base64DecodeIntoCode 0x7C = some (.alu .and a0 a0 (26 : Fin 32), 4) := by decide
theorem bdi_at_80 : fetchRel base64DecodeIntoCode 0x80 = some (.aluImm .add (24 : Fin 32) a1 0x4, 4) := by decide
theorem bdi_at_84 : fetchRel base64DecodeIntoCode 0x84 = some (.alu .sll a2 a0 a2, 4) := by decide
theorem bdi_at_88 : fetchRel base64DecodeIntoCode 0x88 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x1, 2) := by decide
theorem bdi_at_8a : fetchRel base64DecodeIntoCode 0x8A = some (.alu .sub (28 : Fin 32) (21 : Fin 32) a2, 4) := by decide
theorem bdi_at_8e : fetchRel base64DecodeIntoCode 0x8E = some (.branch .beq (21 : Fin 32) x0 0x6A, 4) := by decide
theorem bdi_at_92 : fetchRel base64DecodeIntoCode 0x92 = some (.branch .bgeu a5 (28 : Fin 32) 0x2A, 4) := by decide
theorem bdi_at_96 : fetchRel base64DecodeIntoCode 0x96 = some (.alu .add a0 a1 a5, 4) := by decide
theorem bdi_at_9a : fetchRel base64DecodeIntoCode 0x9A = some (.load .lbu (8 : Fin 32) a0 0x0, 4) := by decide
theorem bdi_at_9e : fetchRel base64DecodeIntoCode 0x9E = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFFBF, 4) := by decide
theorem bdi_at_a2 : fetchRel base64DecodeIntoCode 0xA2 = some (.aluImm .and (9 : Fin 32) a0 0xFF, 4) := by decide
theorem bdi_at_a6 : fetchRel base64DecodeIntoCode 0xA6 = some (.branch .bltu (9 : Fin 32) (20 : Fin 32) 0x18, 4) := by decide
theorem bdi_at_aa : fetchRel base64DecodeIntoCode 0xAA = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFF9F, 4) := by decide
theorem bdi_at_ae : fetchRel base64DecodeIntoCode 0xAE = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bdi_at_b2 : fetchRel base64DecodeIntoCode 0xB2 = some (.branch .bgeu a0 (20 : Fin 32) 0x1C, 4) := by decide
theorem bdi_at_b6 : fetchRel base64DecodeIntoCode 0xB6 = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFFB9, 4) := by decide
theorem bdi_at_ba : fetchRel base64DecodeIntoCode 0xBA = some (.jal x0 0x4, 2) := by decide
theorem bdi_at_bc : fetchRel base64DecodeIntoCode 0xBC = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem bdi_at_be : fetchRel base64DecodeIntoCode 0xBE = some (.aluImm .sll a3 a3 0x6, 2) := by decide
theorem bdi_at_c0 : fetchRel base64DecodeIntoCode 0xC0 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bdi_at_c4 : fetchRel base64DecodeIntoCode 0xC4 = some (.alu .or a3 a3 a0, 2) := by decide
theorem bdi_at_c6 : fetchRel base64DecodeIntoCode 0xC6 = some (.aluImm .add a5 a5 0x1, 2) := by decide
theorem bdi_at_c8 : fetchRel base64DecodeIntoCode 0xC8 = some (.branch .beq a5 (21 : Fin 32) 0x30, 4) := by decide
theorem bdi_at_cc : fetchRel base64DecodeIntoCode 0xCC = some (.jal x0 0xFFFFFFC6, 2) := by decide
theorem bdi_at_ce : fetchRel base64DecodeIntoCode 0xCE = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFFD0, 4) := by decide
theorem bdi_at_d2 : fetchRel base64DecodeIntoCode 0xD2 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bdi_at_d6 : fetchRel base64DecodeIntoCode 0xD6 = some (.branch .bgeu a0 (30 : Fin 32) 0xA, 4) := by decide
theorem bdi_at_da : fetchRel base64DecodeIntoCode 0xDA = some (.aluImm .add a0 (8 : Fin 32) 0x4, 4) := by decide
theorem bdi_at_de : fetchRel base64DecodeIntoCode 0xDE = some (.jal x0 0xFFFFFFE0, 2) := by decide
theorem bdi_at_e0 : fetchRel base64DecodeIntoCode 0xE0 = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFFD5, 4) := by decide
theorem bdi_at_e4 : fetchRel base64DecodeIntoCode 0xE4 = some (.branch .beq a0 x0 0xE, 2) := by decide
theorem bdi_at_e6 : fetchRel base64DecodeIntoCode 0xE6 = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFFD1, 4) := by decide
theorem bdi_at_ea : fetchRel base64DecodeIntoCode 0xEA = some (.branch .bne a0 x0 0xFFFFFF3C, 2) := by decide
theorem bdi_at_ec : fetchRel base64DecodeIntoCode 0xEC = some (.aluImm .add a0 x0 0x3F, 4) := by decide
theorem bdi_at_f0 : fetchRel base64DecodeIntoCode 0xF0 = some (.jal x0 0xFFFFFFCE, 2) := by decide
theorem bdi_at_f2 : fetchRel base64DecodeIntoCode 0xF2 = some (.aluImm .add a0 x0 0x3E, 4) := by decide
theorem bdi_at_f6 : fetchRel base64DecodeIntoCode 0xF6 = some (.jal x0 0xFFFFFFC8, 2) := by decide
theorem bdi_at_f8 : fetchRel base64DecodeIntoCode 0xF8 = some (.aluImm .srl a0 a3 0x8, 4) := by decide
theorem bdi_at_fc : fetchRel base64DecodeIntoCode 0xFC = some (.aluImm .srl a1 a3 0x18, 4) := by decide
theorem bdi_at_100 : fetchRel base64DecodeIntoCode 0x100 = some (.alu .and a5 a3 (25 : Fin 32), 4) := by decide
theorem bdi_at_104 : fetchRel base64DecodeIntoCode 0x104 = some (.alu .and a0 a0 (25 : Fin 32), 4) := by decide
theorem bdi_at_108 : fetchRel base64DecodeIntoCode 0x108 = some (.aluImm .sll a5 a5 0x8, 2) := by decide
theorem bdi_at_10a : fetchRel base64DecodeIntoCode 0x10A = some (.aluImm .sll a3 a3 0x18, 2) := by decide
theorem bdi_at_10c : fetchRel base64DecodeIntoCode 0x10C = some (.alu .or a0 a0 a1, 2) := by decide
theorem bdi_at_10e : fetchRel base64DecodeIntoCode 0x10E = some (.alu .or a3 a3 a5, 2) := by decide
theorem bdi_at_110 : fetchRel base64DecodeIntoCode 0x110 = some (.alu .or a0 a0 a3, 2) := by decide
theorem bdi_at_112 : fetchRel base64DecodeIntoCode 0x112 = some (.aluImm .xor a1 a2 0x3, 4) := by decide
theorem bdi_at_116 : fetchRel base64DecodeIntoCode 0x116 = some (.store .sw sp a0 0x8, 2) := by decide
theorem bdi_at_118 : fetchRel base64DecodeIntoCode 0x118 = some (.alu .add a0 (6 : Fin 32) a1, 4) := by decide
theorem bdi_at_11c : fetchRel base64DecodeIntoCode 0x11C = some (.branch .beq a2 x0 0xE, 2) := by decide
theorem bdi_at_11e : fetchRel base64DecodeIntoCode 0x11E = some (.load .lbu a3 a0 0x0, 4) := by decide
theorem bdi_at_122 : fetchRel base64DecodeIntoCode 0x122 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem bdi_at_124 : fetchRel base64DecodeIntoCode 0x124 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem bdi_at_126 : fetchRel base64DecodeIntoCode 0x126 = some (.branch .beq a3 x0 0xFFFFFFF6, 2) := by decide
theorem bdi_at_128 : fetchRel base64DecodeIntoCode 0x128 = some (.jal x0 0x46, 2) := by decide
theorem bdi_at_12a : fetchRel base64DecodeIntoCode 0x12A = some (.alu .add (8 : Fin 32) a1 a6, 4) := by decide
theorem bdi_at_12e : fetchRel base64DecodeIntoCode 0x12E = some (.branch .bltu (8 : Fin 32) a1 0x6A, 4) := by decide
theorem bdi_at_132 : fetchRel base64DecodeIntoCode 0x132 = some (.branch .bltu a4 (8 : Fin 32) 0x6A, 4) := by decide
theorem bdi_at_136 : fetchRel base64DecodeIntoCode 0x136 = some (.alu .add a0 (23 : Fin 32) a6, 4) := by decide
theorem bdi_at_13a : fetchRel base64DecodeIntoCode 0x13A = some (.alu .add a2 x0 (6 : Fin 32), 2) := by decide
theorem bdi_at_13c : fetchRel base64DecodeIntoCode 0x13C = some (.alu .add a3 x0 a1, 2) := by decide
theorem bdi_at_13e : fetchRel base64DecodeIntoCode 0x13E = some (.alu .add (9 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem bdi_at_140 : fetchRel base64DecodeIntoCode 0x140 = some (.store .sw sp (19 : Fin 32) 0x4, 2) := by decide
theorem bdi_at_142 : fetchRel base64DecodeIntoCode 0x142 = some (.alu .add (19 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem bdi_at_144 : fetchRel base64DecodeIntoCode 0x144 = some (.alu .add (18 : Fin 32) x0 (6 : Fin 32), 2) := by decide
theorem bdi_at_146 : fetchRel base64DecodeIntoCode 0x146 = some (.alu .add (27 : Fin 32) x0 a4, 2) := by decide
theorem bdi_at_148 : fetchRel base64DecodeIntoCode 0x148 = some (.auipc ra 0x5000, 4) := by decide
theorem bdi_at_14c : fetchRel base64DecodeIntoCode 0x14C = some (.jalr ra ra 0xFFFFFC6A, 4) := by decide
theorem bdi_at_150 : fetchRel base64DecodeIntoCode 0x150 = some (.aluImm .add (30 : Fin 32) x0 0xA, 2) := by decide
theorem bdi_at_152 : fetchRel base64DecodeIntoCode 0x152 = some (.alu .add a4 x0 (27 : Fin 32), 2) := by decide
theorem bdi_at_154 : fetchRel base64DecodeIntoCode 0x154 = some (.alu .add (6 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem bdi_at_156 : fetchRel base64DecodeIntoCode 0x156 = some (.alu .add (18 : Fin 32) x0 (19 : Fin 32), 2) := by decide
theorem bdi_at_158 : fetchRel base64DecodeIntoCode 0x158 = some (.alu .add (17 : Fin 32) x0 (9 : Fin 32), 2) := by decide
theorem bdi_at_15a : fetchRel base64DecodeIntoCode 0x15A = some (.load .lw (19 : Fin 32) sp 0x4, 2) := by decide
theorem bdi_at_15c : fetchRel base64DecodeIntoCode 0x15C = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem bdi_at_15e : fetchRel base64DecodeIntoCode 0x15E = some (.alu .add a6 x0 (8 : Fin 32), 2) := by decide
theorem bdi_at_160 : fetchRel base64DecodeIntoCode 0x160 = some (.branch .bne (24 : Fin 32) (22 : Fin 32) 0xFFFFFEFA, 4) := by decide
theorem bdi_at_164 : fetchRel base64DecodeIntoCode 0x164 = some (.store .sb (18 : Fin 32) x0 0x0, 4) := by decide
theorem bdi_at_168 : fetchRel base64DecodeIntoCode 0x168 = some (.store .sw (18 : Fin 32) a6 0x4, 4) := by decide
theorem bdi_at_16c : fetchRel base64DecodeIntoCode 0x16C = some (.jal x0 0xE, 2) := by decide
theorem bdi_at_16e : fetchRel base64DecodeIntoCode 0x16E = some (.aluImm .add a0 x0 0x1C, 2) := by decide
theorem bdi_at_170 : fetchRel base64DecodeIntoCode 0x170 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem bdi_at_172 : fetchRel base64DecodeIntoCode 0x172 = some (.store .sb (18 : Fin 32) a1 0x0, 4) := by decide
theorem bdi_at_176 : fetchRel base64DecodeIntoCode 0x176 = some (.store .sb (18 : Fin 32) a0 0x1, 4) := by decide
theorem bdi_at_17a : fetchRel base64DecodeIntoCode 0x17A = some (.load .lw ra sp 0x3C, 2) := by decide
theorem bdi_at_17c : fetchRel base64DecodeIntoCode 0x17C = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem bdi_at_17e : fetchRel base64DecodeIntoCode 0x17E = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem bdi_at_180 : fetchRel base64DecodeIntoCode 0x180 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem bdi_at_182 : fetchRel base64DecodeIntoCode 0x182 = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem bdi_at_184 : fetchRel base64DecodeIntoCode 0x184 = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem bdi_at_186 : fetchRel base64DecodeIntoCode 0x186 = some (.load .lw (21 : Fin 32) sp 0x24, 2) := by decide
theorem bdi_at_188 : fetchRel base64DecodeIntoCode 0x188 = some (.load .lw (22 : Fin 32) sp 0x20, 2) := by decide
theorem bdi_at_18a : fetchRel base64DecodeIntoCode 0x18A = some (.load .lw (23 : Fin 32) sp 0x1C, 2) := by decide
theorem bdi_at_18c : fetchRel base64DecodeIntoCode 0x18C = some (.load .lw (24 : Fin 32) sp 0x18, 2) := by decide
theorem bdi_at_18e : fetchRel base64DecodeIntoCode 0x18E = some (.load .lw (25 : Fin 32) sp 0x14, 2) := by decide
theorem bdi_at_190 : fetchRel base64DecodeIntoCode 0x190 = some (.load .lw (26 : Fin 32) sp 0x10, 2) := by decide
theorem bdi_at_192 : fetchRel base64DecodeIntoCode 0x192 = some (.load .lw (27 : Fin 32) sp 0xC, 2) := by decide
theorem bdi_at_194 : fetchRel base64DecodeIntoCode 0x194 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem bdi_at_196 : fetchRel base64DecodeIntoCode 0x196 = some (.jalr x0 ra 0x0, 2) := by decide
theorem bdi_at_198 : fetchRel base64DecodeIntoCode 0x198 = some (.aluImm .add a0 x0 0x6, 2) := by decide
theorem bdi_at_19a : fetchRel base64DecodeIntoCode 0x19A = some (.jal x0 0xFFFFFFD6, 2) := by decide
theorem bdi_at_19c : fetchRel base64DecodeIntoCode 0x19C = some (.aluImm .add a0 x0 0x13, 2) := by decide
theorem bdi_at_19e : fetchRel base64DecodeIntoCode 0x19E = some (.jal x0 0xFFFFFFD2, 2) := by decide
end

def bdiR : List BInstr :=
  [.alu .add a0 a1 a5, .lbu (8 : Fin 32) a0 0x0, .aluImm .add a0 (8 : Fin 32) 0xFFFFFFBF, .aluImm .and (9 : Fin 32) a0 0xFF]
def bdiR2 : List BInstr :=
  [.aluImm .add a0 (8 : Fin 32) 0xFFFFFF9F, .aluImm .and a0 a0 0xFF]
def bdiR3 : List BInstr :=
  [.aluImm .add a0 (8 : Fin 32) 0xFFFFFFD0, .aluImm .and a0 a0 0xFF]

section
set_option maxRecDepth 20000
theorem bdiR_end : blockEnd base64DecodeIntoCode 0x96 bdiR = some 0xA6 := by decide
theorem bdiR2_end : blockEnd base64DecodeIntoCode 0xAA bdiR2 = some 0xB2 := by decide
theorem bdiR3_end : blockEnd base64DecodeIntoCode 0xCE bdiR3 = some 0xD6 := by decide
end

def bdiI : List BInstr :=
  [.aluImm .add (19 : Fin 32) x0 0x0, .aluImm .add a6 x0 0x0, .aluImm .srl a0 a2 0x2, .aluImm .add (17 : Fin 32) a0 0xFFFFFFFF, .alu .add (22 : Fin 32) a1 a2, .aluImm .add (6 : Fin 32) sp 0x9, .alu .sltu (26 : Fin 32) x0 a2, .lui a0 0x10000, .aluImm .add (21 : Fin 32) x0 0x4, .aluImm .add (25 : Fin 32) a0 0xFFFFFF00, .aluImm .add (20 : Fin 32) x0 0x1A, .aluImm .add (30 : Fin 32) x0 0xA]
def bdiP : List BInstr :=
  [.aluImm .add a5 x0 0x0, .aluImm .add a3 x0 0x0, .lbu a0 a1 0x3, .lbu a2 a1 0x2, .alu .xor (9 : Fin 32) (19 : Fin 32) (17 : Fin 32), .aluImm .xor a0 a0 0x3D, .alu .or a0 a0 (9 : Fin 32), .aluImm .sltu a0 a0 0x1, .aluImm .add a2 a2 0xFFFFFFC3, .aluImm .sltu a2 a2 0x1, .alu .and a0 a0 (26 : Fin 32), .aluImm .add (24 : Fin 32) a1 0x4, .alu .sll a2 a0 a2, .aluImm .add (19 : Fin 32) (19 : Fin 32) 0x1, .alu .sub (28 : Fin 32) (21 : Fin 32) a2]
def bdiS : List BInstr :=
  [.aluImm .srl a0 a3 0x8, .aluImm .srl a1 a3 0x18, .alu .and a5 a3 (25 : Fin 32), .alu .and a0 a0 (25 : Fin 32), .aluImm .sll a5 a5 0x8, .aluImm .sll a3 a3 0x18, .alu .or a0 a0 a1, .alu .or a3 a3 a5, .alu .or a0 a0 a3, .aluImm .xor a1 a2 0x3, .sw sp a0 0x8, .alu .add a0 (6 : Fin 32) a1]
def bdiC1 : List BInstr :=
  [.alu .add a0 (23 : Fin 32) a6, .alu .add a2 x0 (6 : Fin 32), .alu .add a3 x0 a1, .alu .add (9 : Fin 32) x0 (17 : Fin 32), .sw sp (19 : Fin 32) 0x4, .alu .add (19 : Fin 32) x0 (18 : Fin 32), .alu .add (18 : Fin 32) x0 (6 : Fin 32), .alu .add (27 : Fin 32) x0 a4]
def bdiC2 : List BInstr :=
  [.aluImm .add (30 : Fin 32) x0 0xA, .alu .add a4 x0 (27 : Fin 32), .alu .add (6 : Fin 32) x0 (18 : Fin 32), .alu .add (18 : Fin 32) x0 (19 : Fin 32), .alu .add (17 : Fin 32) x0 (9 : Fin 32), .lw (19 : Fin 32) sp 0x4, .alu .add a1 x0 (24 : Fin 32), .alu .add a6 x0 (8 : Fin 32)]

section
set_option maxRecDepth 20000
theorem bdiI_end : blockEnd base64DecodeIntoCode 0x32 bdiI = some 0x56 := by decide
theorem bdiP_end : blockEnd base64DecodeIntoCode 0x5A bdiP = some 0x8E := by decide
theorem bdiS_end : blockEnd base64DecodeIntoCode 0xF8 bdiS = some 0x11C := by decide
theorem bdiC1_end : blockEnd base64DecodeIntoCode 0x136 bdiC1 = some 0x148 := by decide
theorem bdiC2_end : blockEnd base64DecodeIntoCode 0x150 bdiC2 = some 0x160 := by decide
end

theorem bdi_c1 : ∀ b : BitVec 8, branchTaken .bltu (aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFBF) 0xFF)
    (BitVec.ofNat 32 26) = decide (65 ≤ b.toNat ∧ b.toNat ≤ 90) := by decide
theorem bdi_c2 : ∀ b : BitVec 8, branchTaken .bgeu (aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFF9F) 0xFF)
    (BitVec.ofNat 32 26) = !decide (97 ≤ b.toNat ∧ b.toNat ≤ 122) := by decide
theorem bdi_c3 : ∀ b : BitVec 8, branchTaken .bgeu (aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 0xFF)
    (BitVec.ofNat 32 10) = !decide (48 ≤ b.toNat ∧ b.toNat ≤ 57) := by decide
theorem bdi_c4 : ∀ b : BitVec 8, branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFD5) 0 = decide (b.toNat = 43) := by
  decide
theorem bdi_c5 : ∀ b : BitVec 8, branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFD1) 0 = !decide (b.toNat = 47) := by
  decide
theorem bdi_v1 : ∀ b : BitVec 8, 65 ≤ b.toNat ∧ b.toNat ≤ 90 →
    aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFBF) 0xFF = BitVec.ofNat 32 (b.toNat - 65) := by decide
theorem bdi_v2 : ∀ b : BitVec 8, 97 ≤ b.toNat ∧ b.toNat ≤ 122 →
    aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFB9) 0xFF = BitVec.ofNat 32 (b.toNat - 71) := by decide
theorem bdi_v3 : ∀ b : BitVec 8, 48 ≤ b.toNat ∧ b.toNat ≤ 57 →
    aluEval .and (aluEval .add (b.zeroExtend 32) 0x4) 0xFF = BitVec.ofNat 32 (b.toNat + 4) := by decide

set_option maxRecDepth 20000 in
/-- From 0xBE, with the character's value `v` in `a0`'s low byte: shift it
into the group's bits and step `j`. -/
theorem bdi_tail {M : Word → BitVec 8} (hc : CodeIn M BDI base64DecodeIntoCode) {nn : Machine} {j acc v : Nat}
    {w : Word} (st : St M BDI nn 0xBE (reg nn)) (hj : j < 4) (hacc : acc < 2 ^ 18) (hv : v < 64)
    (r10 : aluEval .and w 0xFF = BitVec.ofNat 32 v) (ra0 : reg nn a0 = w) (r13 : reg nn a3 = BitVec.ofNat 32 acc)
    (r15 : reg nn a5 = BitVec.ofNat 32 j) (r21 : reg nn 21 = BitVec.ofNat 32 4) :
    ∃ nn', Steps nn nn' ∧ St M BDI nn' (if j + 1 = 4 then 0xF8 else 0x92) (reg nn') ∧
      reg nn' a3 = BitVec.ofNat 32 (acc * 64 + v) ∧ reg nn' a5 = BitVec.ofNat 32 (j + 1) ∧
      ∀ r, r.val ∉ [10, 13, 15] → reg nn' r = reg nn r := by
  have hz := st.zero
  obtain ⟨n1, d1, u1⟩ := st.aluImm hc bdi_at_be (off' := 0xC0) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc bdi_at_c0 (off' := 0xC4) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.alu hc bdi_at_c4 (off' := 0xC6) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc bdi_at_c6 (off' := 0xC8) (by decide)
  have K4 : ∀ r, r.val ∉ [10, 13, 15] → reg n4 r = reg nn r := fun r hr => by
    rw [u4.regs, upd_ne' (by intro e; apply hr; rw [e]; decide) u3.self.zero, u3.regs,
      upd_ne' (by intro e; apply hr; rw [e]; decide) u2.self.zero, u2.regs,
      upd_ne' (by intro e; apply hr; rw [e]; decide) u1.self.zero, u1.regs,
      upd_ne' (by intro e; apply hr; rw [e]; decide) hz]
  have v1 : reg n1 a3 = aluEval .sll (BitVec.ofNat 32 acc) 6 := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r13]
  have v1a0 : reg n1 a0 = w := by rw [u1.regs, upd_ne' (by decide) hz, ra0]
  have v2a0 : reg n2 a0 = BitVec.ofNat 32 v := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v1a0, r10]
  have v2a3 : reg n2 a3 = aluEval .sll (BitVec.ofNat 32 acc) 6 := by rw [u2.regs, upd_ne' (by decide) u1.self.zero, v1]
  have v3a3 : reg n3 a3 = BitVec.ofNat 32 (acc * 64 + v) := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v2a3, v2a0]
    have hs : (aluEval .sll (BitVec.ofNat 32 acc) 6).toNat = acc * 64 := by
      rw [dn_sll, BitVec.toNat_ofNat, show (6 : Word).toNat % 32 = 6 from rfl]; omega
    apply BitVec.eq_of_toNat_eq
    rw [tn_or' (j := 6) rfl (by rw [BitVec.toNat_ofNat]; omega) (by rw [hs]; omega), hs, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega
  have a313 : reg n4 a3 = BitVec.ofNat 32 (acc * 64 + v) := by rw [u4.regs, upd_ne' (by decide) u3.self.zero, v3a3]
  have a515 : reg n4 a5 = BitVec.ofNat 32 (j + 1) := by
    rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u3.regs, upd_ne' (by decide) u2.self.zero, u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs,
      upd_ne' (by decide) hz, r15]
    exact BitVec.eq_of_toNat_eq (by rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega)
  have r21' : reg n4 21 = BitVec.ofNat 32 4 := by rw [K4 _ (by decide), r21]
  by_cases h4 : j + 1 = 4
  · obtain ⟨n5, d5, u5⟩ := u4.self.taken hc 0xF8 bdi_at_c8 (by decide) (by rw [a515, r21', h4]; rfl)
    refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), by rw [if_pos h4]; exact u5.self,
      by rw [u5.regs, a313], by rw [u5.regs, a515], fun r hr => by rw [u5.regs, K4 r hr]⟩
  · obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hc 0xCC bdi_at_c8 (by decide) (by
      rw [a515, r21']; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
      intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega)
    obtain ⟨n6, d6, u6⟩ := u5.self.jump hc bdi_at_cc (off' := 0x92) (by decide) (by rw [u5.pc]; decide)
    refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), by rw [if_neg h4]; exact u6.self,
      by rw [u6.regs, u5.regs, a313], by rw [u6.regs, u5.regs, a515], fun r hr => by rw [u6.regs, u5.regs, K4 r hr]⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- One character of a group, from 0x92: its 6-bit value shifted into the
group's bits, or the `BadBase64` exit at 0x26 when it isn't in the alphabet.
Characters at `kp` and past are padding and count as 0. -/
theorem bdi_inner {M : Word → BitVec 8} (hc : CodeIn M BDI base64DecodeIntoCode) {nn : Machine} {j acc kp : Nat}
    {g : Word} (st : St M BDI nn 0x92 (reg nn)) (hj : j < 4) (hacc : acc < 2 ^ 18) (hkp : kp ≤ 4)
    (r15 : reg nn a5 = BitVec.ofNat 32 j) (r13 : reg nn a3 = BitVec.ofNat 32 acc) (r28 : reg nn 28 = BitVec.ofNat 32 kp)
    (r11 : reg nn a1 = g) (r20 : reg nn 20 = BitVec.ofNat 32 26) (r30 : reg nn 30 = BitVec.ofNat 32 10)
    (r21 : reg nn 21 = BitVec.ofNat 32 4) :
    ((if kp ≤ j then some 0 else b64Value (M (g + BitVec.ofNat 32 j)).toNat) = none →
      ∃ nn', Steps nn nn' ∧ St M BDI nn' 0x26 (reg nn') ∧ ∀ r, r.val ∉ [8, 9, 10] → reg nn' r = reg nn r) ∧
    (∀ v, (if kp ≤ j then some 0 else b64Value (M (g + BitVec.ofNat 32 j)).toNat) = some v →
      ∃ nn', Steps nn nn' ∧ St M BDI nn' (if j + 1 = 4 then 0xF8 else 0x92) (reg nn') ∧
        reg nn' a3 = BitVec.ofNat 32 (acc * 64 + v) ∧ reg nn' a5 = BitVec.ofNat 32 (j + 1) ∧
        ∀ r, r.val ∉ [8, 9, 10, 13, 15] → reg nn' r = reg nn r) := by
  have hz := st.zero
  by_cases hk : kp ≤ j
  · rw [if_pos hk]
    refine ⟨(fun h => by cases h), fun v hv => ?_⟩
    cases hv
    obtain ⟨n1, d1, u1⟩ := st.taken hc 0xBC bdi_at_92 (by decide) (by
      rw [r15, r28]; simp only [branchTaken, BitVec.ult, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 32), Nat.mod_eq_of_lt (by omega : kp < 2 ^ 32)]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega)
    obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc bdi_at_bc (off' := 0xBE) (by decide)
    have K2 : ∀ r, r ≠ a0 → reg n2 r = reg nn r := fun r hr => by rw [u2.regs, upd_ne' hr u1.self.zero, u1.regs]
    obtain ⟨n3, c3, u3, a33, a53, K3⟩ := bdi_tail hc (v := 0) (w := aluEval .add (reg n1 0) 0) u2.self hj hacc
      (by decide) (by rw [u1.self.zero]; rfl) (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte])
      (by rw [K2 a3 (by decide), r13]) (by rw [K2 a5 (by decide), r15]) (by rw [K2 21 (by decide), r21])
    exact ⟨n3, .cons d1 (.cons d2 c3), u3, a33, a53, fun r hr => by
      rw [K3 r (by revert hr; revert r; decide), K2 r (by intro e; apply hr; rw [e]; decide)]⟩
  rw [if_neg hk]
  obtain ⟨n1, d1, u1⟩ := st.notTaken hc 0x96 bdi_at_92 (by decide) (by
    rw [r15, r28]; simp only [branchTaken, BitVec.ult, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 32), Nat.mod_eq_of_lt (by omega : kp < 2 ^ 32)]
    simp only [Bool.not_eq_false', decide_eq_true_eq]; omega)
  obtain ⟨n2, c2, u2⟩ := St.block bdiR u1.self hc bdiR_end (by simp only [BlockOk, BInstr.ok, bdiR, and_self])
  have R2 : ∀ r, reg n2 r = (runBlock bdiR (M, reg n1)).2 r := u2.regs
  have u2' : St M BDI n2 0xA6 (reg n2) := ⟨u2.pc, by rw [u2.mem]; rfl, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, M (g + BitVec.ofNat 32 j) = b := ⟨_, rfl⟩
  rw [hb]
  have v2 : reg n2 8 = b.zeroExtend 32 ∧ reg n2 9 = aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFBF) 0xFF ∧
      reg n2 a0 = aluEval .add (b.zeroExtend 32) 0xFFFFFFBF := by
    simp +decide only [R2, runBlock, BInstr.run, bdiR, upd_app, ↓reduceIte]
    rw [u1.regs, r11, u1.regs, r15, add_lit_zero, ev_add, hb]; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨v28, v29, v2a0⟩ := v2
  have K2 : ∀ r, r.val ∉ [8, 9, 10] → reg n2 r = reg nn r := fun r hr => by
    have hd : r ∉ bdiR.filterMap BInstr.dst := by
      simp only [bdiR, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
    rw [R2, runBlock_reg _ _ _ r u1.self.zero hd, u1.regs]
  have pre2 : Steps nn n2 := .cons d1 c2
  -- the rest of the step, from 0xBE with the value in `a0`
  have fin : ∀ {n3 : Machine} {w : Word} {v : Nat}, Steps nn n3 → St M BDI n3 0xBE (reg n3) → v < 64 →
      aluEval .and w 0xFF = BitVec.ofNat 32 v → reg n3 a0 = w → (∀ r, r.val ∉ [8, 9, 10] → reg n3 r = reg nn r) →
      ∃ nn', Steps nn nn' ∧ St M BDI nn' (if j + 1 = 4 then 0xF8 else 0x92) (reg nn') ∧
        reg nn' a3 = BitVec.ofNat 32 (acc * 64 + v) ∧ reg nn' a5 = BitVec.ofNat 32 (j + 1) ∧
        ∀ r, r.val ∉ [8, 9, 10, 13, 15] → reg nn' r = reg nn r := fun pre3 u3 hv hw ra0 K3 => by
    obtain ⟨n4, c4, u4, a34, a54, K4⟩ := bdi_tail hc u3 hj hacc hv hw ra0 (by rw [K3 a3 (by decide), r13])
      (by rw [K3 a5 (by decide), r15]) (by rw [K3 21 (by decide), r21])
    exact ⟨n4, pre3.trans c4, u4, a34, a54, fun r hr => by
      rw [K4 r (by revert hr; revert r; decide), K3 r (by revert hr; revert r; decide)]⟩
  by_cases h1 : 65 ≤ b.toNat ∧ b.toNat ≤ 90
  · have hv : b64Value b.toNat = some (b.toNat - 65) := by unfold b64Value; rw [if_pos h1]
    rw [hv]
    refine ⟨(fun h => by cases h), fun v hv' => ?_⟩
    cases hv'
    obtain ⟨n3, d3, u3⟩ := u2'.taken hc 0xBE bdi_at_a6 (by decide) (by
      rw [v29, K2 20 (by decide), r20, bdi_c1, decide_eq_true h1])
    exact fin (pre2.trans (.single d3)) u3.self (by omega) (bdi_v1 b h1) (by rw [u3.regs, v2a0])
      (fun r hr => by rw [u3.regs, K2 r hr])
  obtain ⟨n3, d3, u3⟩ := u2'.notTaken hc 0xAA bdi_at_a6 (by decide) (by
    rw [v29, K2 20 (by decide), r20, bdi_c1, decide_eq_false h1])
  obtain ⟨n4, c4, u4⟩ := St.block bdiR2 u3.self hc bdiR2_end (by simp only [BlockOk, BInstr.ok, bdiR2, and_self])
  have u4' : St M BDI n4 0xB2 (reg n4) := ⟨u4.pc, by rw [u4.mem]; rfl, fun _ => rfl⟩
  have K4 : ∀ r, r ≠ a0 → reg n4 r = reg n2 r := fun r hr => by
    have hd : r ∉ bdiR2.filterMap BInstr.dst := by
      simp only [bdiR2, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
        or_false, or_self]; exact hr
    rw [u4.regs, runBlock_reg _ _ _ r u3.self.zero hd, u3.regs]
  have v4 : reg n4 a0 = aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFF9F) 0xFF := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, bdiR2, upd_app, ↓reduceIte]; rw [u3.regs, v28]
  have pre4 : Steps nn n4 := pre2.trans (.cons d3 c4)
  by_cases h2 : 97 ≤ b.toNat ∧ b.toNat ≤ 122
  · have hv : b64Value b.toNat = some (b.toNat - 71) := by unfold b64Value; rw [if_neg h1, if_pos h2]
    rw [hv]
    refine ⟨(fun h => by cases h), fun v hv' => ?_⟩
    cases hv'
    obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc 0xB6 bdi_at_b2 (by decide) (by
      rw [v4, K4 20 (by decide), K2 20 (by decide), r20, bdi_c2, decide_eq_true h2]; rfl)
    obtain ⟨n6, d6, u6⟩ := u5.self.aluImm hc bdi_at_b6 (off' := 0xBA) (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.self.jump hc bdi_at_ba (off' := 0xBE) (by decide) (by rw [u6.pc]; decide)
    exact fin (pre4.trans (.cons d5 (.cons d6 (.single d7)))) u7.self (by omega) (bdi_v2 b h2)
      (by rw [u7.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u5.regs, K4 8 (by decide), v28])
      (fun r hr => by rw [u7.regs, u6.regs, upd_ne' (by intro e; apply hr; rw [e]; decide) u5.self.zero, u5.regs,
        K4 r (by intro e; apply hr; rw [e]; decide), K2 r hr])
  obtain ⟨n5, d5, u5⟩ := u4'.taken hc 0xCE bdi_at_b2 (by decide) (by
    rw [v4, K4 20 (by decide), K2 20 (by decide), r20, bdi_c2, decide_eq_false h2]; rfl)
  obtain ⟨n6, c6, u6⟩ := St.block bdiR3 u5.self hc bdiR3_end (by simp only [BlockOk, BInstr.ok, bdiR3, and_self])
  have u6' : St M BDI n6 0xD6 (reg n6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
  have K6 : ∀ r, r ≠ a0 → reg n6 r = reg n2 r := fun r hr => by
    have hd : r ∉ bdiR3.filterMap BInstr.dst := by
      simp only [bdiR3, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
        or_false, or_self]; exact hr
    rw [u6.regs, runBlock_reg _ _ _ r u5.self.zero hd, u5.regs, K4 r hr]
  have v6 : reg n6 a0 = aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 0xFF := by
    rw [u6.regs]; simp +decide only [runBlock, BInstr.run, bdiR3, upd_app, ↓reduceIte]; rw [u5.regs, K4 8 (by decide), v28]
  have pre6 : Steps nn n6 := pre4.trans (.cons d5 c6)
  by_cases h3 : 48 ≤ b.toNat ∧ b.toNat ≤ 57
  · have hv : b64Value b.toNat = some (b.toNat + 4) := by unfold b64Value; rw [if_neg h1, if_neg h2, if_pos h3]
    rw [hv]
    refine ⟨(fun h => by cases h), fun v hv' => ?_⟩
    cases hv'
    obtain ⟨n7, d7, u7⟩ := u6'.notTaken hc 0xDA bdi_at_d6 (by decide) (by
      rw [v6, K6 30 (by decide), K2 30 (by decide), r30, bdi_c3, decide_eq_true h3]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.self.aluImm hc bdi_at_da (off' := 0xDE) (by decide)
    obtain ⟨n9, d9, u9⟩ := u8.self.jump hc bdi_at_de (off' := 0xBE) (by decide) (by rw [u8.pc]; decide)
    exact fin (pre6.trans (.cons d7 (.cons d8 (.single d9)))) u9.self (by omega) (bdi_v3 b h3)
      (by rw [u9.regs, u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u7.regs, K6 8 (by decide), v28])
      (fun r hr => by rw [u9.regs, u8.regs, upd_ne' (by intro e; apply hr; rw [e]; decide) u7.self.zero, u7.regs,
        K6 r (by intro e; apply hr; rw [e]; decide), K2 r hr])
  obtain ⟨n7, d7, u7⟩ := u6'.taken hc 0xE0 bdi_at_d6 (by decide) (by
    rw [v6, K6 30 (by decide), K2 30 (by decide), r30, bdi_c3, decide_eq_false h3]; rfl)
  obtain ⟨n8, d8, u8⟩ := u7.self.aluImm hc bdi_at_e0 (off' := 0xE4) (by decide)
  have v8 : reg n8 a0 = aluEval .add (b.zeroExtend 32) 0xFFFFFFD5 := by
    rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u7.regs, K6 8 (by decide), v28]
  have K8 : ∀ r, r ≠ a0 → reg n8 r = reg n2 r := fun r hr => by
    rw [u8.regs, upd_ne' hr u7.self.zero, u7.regs, K6 r hr]
  have pre8 : Steps nn n8 := pre6.trans (.cons d7 (.single d8))
  by_cases h4 : b.toNat = 43
  · have hv : b64Value b.toNat = some 62 := by unfold b64Value; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    rw [hv]
    refine ⟨(fun h => by cases h), fun v hv' => ?_⟩
    cases hv'
    obtain ⟨n9, d9, u9⟩ := u8.self.taken hc 0xF2 bdi_at_e4 (by decide) (by
      rw [v8, u8.self.zero, bdi_c4, decide_eq_true h4])
    obtain ⟨n10, d10, u10⟩ := u9.self.aluImm hc bdi_at_f2 (off' := 0xF6) (by decide)
    obtain ⟨n11, d11, u11⟩ := u10.self.jump hc bdi_at_f6 (off' := 0xBE) (by decide) (by rw [u10.pc]; decide)
    exact fin (w := aluEval .add (reg n9 0) 0x3E) (pre8.trans (.cons d9 (.cons d10 (.single d11)))) u11.self (by omega) (by
      rw [u9.self.zero]; rfl) (by rw [u11.regs, u10.regs]; simp +decide only [upd_app, ↓reduceIte])
      (fun r hr => by rw [u11.regs, u10.regs, upd_ne' (by intro e; apply hr; rw [e]; decide) u9.self.zero, u9.regs,
        K8 r (by intro e; apply hr; rw [e]; decide), K2 r hr])
  obtain ⟨n9, d9, u9⟩ := u8.self.notTaken hc 0xE6 bdi_at_e4 (by decide) (by
    rw [v8, u8.self.zero, bdi_c4, decide_eq_false h4])
  obtain ⟨n10, d10, u10⟩ := u9.self.aluImm hc bdi_at_e6 (off' := 0xEA) (by decide)
  have v10 : reg n10 a0 = aluEval .add (b.zeroExtend 32) 0xFFFFFFD1 := by
    rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u9.regs, K8 8 (by decide), v28]
  have K10 : ∀ r, r ≠ a0 → reg n10 r = reg n2 r := fun r hr => by
    rw [u10.regs, upd_ne' hr u9.self.zero, u9.regs, K8 r hr]
  have pre10 : Steps nn n10 := pre8.trans (.cons d9 (.single d10))
  by_cases h5 : b.toNat = 47
  · have hv : b64Value b.toNat = some 63 := by
      unfold b64Value; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    rw [hv]
    refine ⟨(fun h => by cases h), fun v hv' => ?_⟩
    cases hv'
    obtain ⟨n11, d11, u11⟩ := u10.self.notTaken hc 0xEC bdi_at_ea (by decide) (by
      rw [v10, u10.self.zero, bdi_c5, decide_eq_true h5]; rfl)
    obtain ⟨n12, d12, u12⟩ := u11.self.aluImm hc bdi_at_ec (off' := 0xF0) (by decide)
    obtain ⟨n13, d13, u13⟩ := u12.self.jump hc bdi_at_f0 (off' := 0xBE) (by decide) (by rw [u12.pc]; decide)
    exact fin (w := aluEval .add (reg n11 0) 0x3F) (pre10.trans (.cons d11 (.cons d12 (.single d13)))) u13.self (by omega) (by
      rw [u11.self.zero]; rfl) (by rw [u13.regs, u12.regs]; simp +decide only [upd_app, ↓reduceIte])
      (fun r hr => by rw [u13.regs, u12.regs, upd_ne' (by intro e; apply hr; rw [e]; decide) u11.self.zero, u11.regs,
        K10 r (by intro e; apply hr; rw [e]; decide), K2 r hr])
  have hv : b64Value b.toNat = none := by
    unfold b64Value; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  rw [hv]
  refine ⟨fun _ => ?_, fun v hv' => by cases hv'⟩
  obtain ⟨n11, d11, u11⟩ := u10.self.taken hc 0x26 bdi_at_ea (by decide) (by
    rw [v10, u10.self.zero, bdi_c5, decide_eq_false h5]; rfl)
  exact ⟨n11, pre10.trans (.single d11), u11.self, fun r hr => by
    rw [u11.regs, K10 r (by intro e; apply hr; rw [e]; decide), K2 r hr]⟩

set_option maxRecDepth 20000 in
/-- The rest of a group's characters, from 0x92 with `j` of them done: their
bits, at 0xF8, or the `BadBase64` exit at 0x26. -/
theorem bdi_fold {M : Word → BitVec 8} (hc : CodeIn M BDI base64DecodeIntoCode) {kp : Nat} {g : Word}
    (hkp : kp ≤ 4) : ∀ (r j acc : Nat) (nn : Machine), j + r = 4 → acc < 64 ^ j →
    St M BDI nn (if j = 4 then 0xF8 else 0x92) (reg nn) → reg nn a5 = BitVec.ofNat 32 j →
    reg nn a3 = BitVec.ofNat 32 acc → reg nn 28 = BitVec.ofNat 32 kp → reg nn a1 = g →
    reg nn 20 = BitVec.ofNat 32 26 → reg nn 30 = BitVec.ofNat 32 10 → reg nn 21 = BitVec.ofNat 32 4 →
    (bdiFold (fun j => if kp ≤ j then some 0 else b64Value (M (g + BitVec.ofNat 32 j)).toNat) r j acc = none →
      ∃ nn', Steps nn nn' ∧ St M BDI nn' 0x26 (reg nn') ∧ ∀ q, q.val ∉ [8, 9, 10, 13, 15] → reg nn' q = reg nn q) ∧
    (∀ bits, bdiFold (fun j => if kp ≤ j then some 0 else b64Value (M (g + BitVec.ofNat 32 j)).toNat) r j acc =
        some bits → bits < 2 ^ 24 ∧ ∃ nn', Steps nn nn' ∧ St M BDI nn' 0xF8 (reg nn') ∧
        reg nn' a3 = BitVec.ofNat 32 bits ∧ ∀ q, q.val ∉ [8, 9, 10, 13, 15] → reg nn' q = reg nn q)
  | 0, j, acc, nn, hj, hacc, st, _, _, _, _, _, _, _ => by
    obtain rfl : j = 4 := by omega
    rw [if_pos rfl] at st
    refine ⟨(fun h => by cases h), fun bits hb => ?_⟩
    cases hb
    exact ⟨hacc, nn, .refl _, st, by assumption, fun _ _ => rfl⟩
  | r + 1, j, acc, nn, hj, hacc, st, r15, r13, r28, r11, r20, r30, r21 => by
    have hj4 : j < 4 := by omega
    rw [if_neg (by omega)] at st
    have h18 : acc < 2 ^ 18 := by
      have : 64 ^ j ≤ 64 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
      have e : (64 : Nat) ^ 3 = 2 ^ 18 := rfl
      omega
    obtain ⟨E, O⟩ := bdi_inner hc st hj4 h18 hkp r15 r13 r28 r11 r20 r30 r21
    have keep : ∀ {nn' : Machine}, (∀ q, q.val ∉ [8, 9, 10, 13, 15] → reg nn' q = reg nn q) →
        ∀ q, q.val ∉ [8, 9, 10, 13, 15] → reg nn' q = reg nn q := fun h => h
    simp only [bdiFold]
    cases hv : (if kp ≤ j then some 0 else b64Value (M (g + BitVec.ofNat 32 j)).toNat) with
    | none =>
      obtain ⟨n1, c1, u1, K1⟩ := E hv
      refine ⟨fun _ => ⟨n1, c1, u1, fun q hq => K1 q (by revert hq; revert q; decide)⟩, fun bits hb => by cases hb⟩
    | some v =>
      have hv64 : v < 64 := by
        by_cases hk : kp ≤ j
        · rw [if_pos hk] at hv; cases hv; decide
        · rw [if_neg hk] at hv; exact b64Value_lt hv
      obtain ⟨n1, c1, u1, a31, a51, K1⟩ := O v hv
      have hacc' : acc * 64 + v < 64 ^ (j + 1) := by rw [Nat.pow_succ]; omega
      obtain ⟨E', O'⟩ := bdi_fold hc hkp r (j + 1) (acc * 64 + v) n1 (by omega) hacc' u1 a51 a31
        (by rw [K1 28 (by decide), r28]) (by rw [K1 a1 (by decide), r11]) (by rw [K1 20 (by decide), r20])
        (by rw [K1 30 (by decide), r30]) (by rw [K1 21 (by decide), r21])
      refine ⟨fun h => ?_, fun bits hb => ?_⟩
      · obtain ⟨n2, c2, u2, K2⟩ := E' h
        exact ⟨n2, c1.trans c2, u2, fun q hq => by rw [K2 q hq, K1 q hq]⟩
      · obtain ⟨hb24, n2, c2, u2, a32, K2⟩ := O' bits hb
        exact ⟨hb24, n2, c1.trans c2, u2, a32, fun q hq => by rw [K2 q hq, K1 q hq]⟩

theorem bdi_sltu1 (v : Word) : aluEval .sltu v 1 = if v = 0 then 1 else 0 := by
  by_cases h : v = 0
  · rw [if_pos h]; subst h; rfl
  · rw [if_neg h]
    have hv : v.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    have hu : v.ult 1 = false := by
      unfold BitVec.ult; exact decide_eq_false (by rw [show (1 : Word).toNat = 1 from rfl]; omega)
    show (if v.ult 1 = true then 1 else 0) = 0
    rw [hu]; rfl

theorem bdi_padv (b2 b3 : BitVec 8) (x y : Word) :
    aluEval .sll (aluEval .and (aluEval .sltu (aluEval .or (aluEval .xor (b3.zeroExtend 32) 0x3D) (aluEval .xor x y)) 1) 1)
      (aluEval .sltu (aluEval .add (b2.zeroExtend 32) 0xFFFFFFC3) 1) =
      BitVec.ofNat 32 (bdiPad (x == y) b2.toNat b3.toNat) := by
  have p3 : ∀ b : BitVec 8, aluEval .xor (b.zeroExtend 32) 0x3D = 0 ↔ b.toNat = 61 := by decide
  have p2 : ∀ b : BitVec 8, aluEval .sltu (aluEval .add (b.zeroExtend 32) 0xFFFFFFC3) 1 =
      if b.toNat = 61 then 1 else 0 := by decide
  have hV : aluEval .or (aluEval .xor (b3.zeroExtend 32) 0x3D) (aluEval .xor x y) = 0 ↔ b3.toNat = 61 ∧ x = y :=
    BitVec.or_eq_zero_iff.trans (and_congr (p3 _) BitVec.xor_eq_zero_iff)
  have hb : (x == y) = true ↔ x = y := beq_iff_eq
  rw [p2, bdi_sltu1]
  unfold bdiPad
  by_cases hc : b3.toNat = 61 ∧ x = y
  · rw [if_pos (hV.mpr hc), if_pos (show (x == y) = true ∧ b3.toNat = 61 from ⟨hb.mpr hc.2, hc.1⟩)]
    by_cases h2 : b2.toNat = 61
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]; rfl
  · rw [if_neg (fun h => hc (hV.mp h)),
      if_neg (show ¬((x == y) = true ∧ b3.toNat = 61) from fun h => hc ⟨h.2, hb.mp h.1⟩)]
    by_cases h2 : b2.toNat = 61
    · rw [if_pos h2]; rfl
    · rw [if_neg h2]; rfl

set_option maxRecDepth 20000 in
/-- A group's padding, from 0x5A to 0x92: `a2` is the padding and `t3` the
characters it decodes. -/
theorem bdi_pad {M : Word → BitVec 8} (hc : CodeIn M BDI base64DecodeIntoCode) {nn : Machine} {g x y : Word}
    (st : St M BDI nn 0x5A (reg nn)) (r11 : reg nn a1 = g) (r19 : reg nn 19 = x) (r17 : reg nn 17 = y)
    (r26 : reg nn 26 = 1) (r21 : reg nn 21 = BitVec.ofNat 32 4) :
    ∃ nn', Steps nn nn' ∧ St M BDI nn' 0x92 (reg nn') ∧ reg nn' a5 = 0 ∧ reg nn' a3 = 0 ∧
      reg nn' a2 = BitVec.ofNat 32 (bdiPad (x == y) (M (g + 2)).toNat (M (g + 3)).toNat) ∧
      reg nn' 28 = BitVec.ofNat 32 (4 - bdiPad (x == y) (M (g + 2)).toNat (M (g + 3)).toNat) ∧
      reg nn' 24 = g + 4 ∧ reg nn' 19 = x + 1 ∧
      ∀ q, q.val ∉ [9, 10, 12, 13, 15, 19, 24, 28] → reg nn' q = reg nn q := by
  have hz := st.zero
  obtain ⟨n1, c1, u1⟩ := St.block bdiP st hc bdiP_end (by simp only [BlockOk, BInstr.ok, bdiP, and_self])
  have R1 : ∀ r, reg n1 r = (runBlock bdiP (M, reg nn)).2 r := u1.regs
  have u1' : St M BDI n1 0x8E (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
  have K1 : ∀ q, q.val ∉ [9, 10, 12, 13, 15, 19, 24, 28] → reg n1 q = reg nn q := fun q hq => by
    have hd : q ∉ bdiP.filterMap BInstr.dst := by
      simp only [bdiP, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R1, runBlock_reg _ _ _ q hz hd]
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc 0x92 bdi_at_8e (by decide) (by
    rw [K1 21 (by decide), r21, u1'.zero]; rfl)
  have hp := bdi_padv (M (g + 2)) (M (g + 3)) x y
  have hpl := bdiPad_le (x == y) (M (g + 2)).toNat (M (g + 3)).toNat
  have va2 : reg n1 a2 = BitVec.ofNat 32 (bdiPad (x == y) (M (g + 2)).toNat (M (g + 3)).toNat) := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, bdiP, upd_app, ↓reduceIte]
    rw [r11, r19, r17, r26]; exact hp
  refine ⟨n2, c1.trans (.single d2), u2.self, ?_, ?_, by rw [u2.regs, va2], ?_, ?_, ?_,
    fun q hq => by rw [u2.regs, K1 q hq]⟩
  · rw [u2.regs, R1]; simp +decide only [runBlock, BInstr.run, bdiP, upd_app, ↓reduceIte]
    all_goals (try rw [hz]); all_goals rfl
  · rw [u2.regs, R1]; simp +decide only [runBlock, BInstr.run, bdiP, upd_app, ↓reduceIte]
    all_goals (try rw [hz]); all_goals rfl
  · rw [u2.regs, R1]; simp +decide only [runBlock, BInstr.run, bdiP, upd_app, ↓reduceIte]
    rw [r11, r19, r17, r26, hp, r21]
    generalize bdiPad (x == y) (M (g + 2)).toNat (M (g + 3)).toNat = p at hpl ⊢
    obtain rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    all_goals rfl
  · rw [u2.regs, R1]; simp +decide only [runBlock, BInstr.run, bdiP, upd_app, ↓reduceIte]; rw [r11]; rfl
  · rw [u2.regs, R1]; simp +decide only [runBlock, BInstr.run, bdiP, upd_app, ↓reduceIte]; rw [r19]; rfl

theorem bdi_bswap (a : Word) (k : Nat) (hk : k < 3) :
    (aluEval .or (aluEval .or (aluEval .and (aluEval .srl a 0x8) 0xFF00) (aluEval .srl a 0x18))
      (aluEval .or (aluEval .sll a 0x18) (aluEval .sll (aluEval .and a 0xFF00) 0x8))).extractLsb' (8 * (k + 1)) 8 =
      a.extractLsb' (16 - 8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e8 : (0x8 : Word).toNat % 32 = 8 := rfl
  have e18 : (0x18 : Word).toNat % 32 = 24 := rfl
  simp only [aluEval, e8, e18, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  have hF : ∀ j, BitVec.getLsbD (65280 : Word) j = (decide (8 ≤ j) && decide (j < 16)) := fun j => by
    by_cases hj : j < 32
    · revert j; decide
    · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
      rw [show decide (j < 16) = false from decide_eq_false (by omega), Bool.and_false]
  simp only [hF]
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals
    obtain _ | _ | _ | _ | _ | _ | _ | _ | i := i
    all_goals first
      | (exfalso; omega)
      | simp +decide only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Bool.and_true, Bool.and_false,
          Bool.true_and, Bool.false_and, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true, decide_false, Bool.or_self, Bool.and_self,
          BitVec.getLsbD_of_ge]

theorem bdi_st32 (M : Word → BitVec 8) (a v : Word) (j : Nat) (h1 : 1 ≤ j) (h4 : j < 4) :
    memStore32 M a v (a + BitVec.ofNat 32 j) = v.extractLsb' (8 * j) 8 := by
  have ne : ∀ c d : Nat, c < 4 → d < 4 → c ≠ d → a + BitVec.ofNat 32 c ≠ a + BitVec.ofNat 32 d :=
    fun c d hc hd h => add_ofNat_ne a (by omega) (by omega) h
  unfold memStore32
  obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · rw [memStore8_ne (show a + BitVec.ofNat 32 1 ≠ a + 3 from ne 1 3 (by decide) (by decide) (by decide)),
      memStore8_ne (show a + BitVec.ofNat 32 1 ≠ a + 2 from ne 1 2 (by decide) (by decide) (by decide))]
    exact memStore8_same _ _ _
  · rw [memStore8_ne (show a + BitVec.ofNat 32 2 ≠ a + 3 from ne 2 3 (by decide) (by decide) (by decide))]
    exact memStore8_same _ _ _
  · exact memStore8_same _ _ _

set_option maxRecDepth 20000 in
/-- The pad bytes check, from 0x11C: `c` bytes at `p` must be zero. -/
theorem bdi_zero {M : Word → BitVec 8} (hc : CodeIn M BDI base64DecodeIntoCode) :
    ∀ (c : Nat) (p : Word) (nn : Machine), c ≤ 2 → St M BDI nn 0x11C (reg nn) → reg nn a2 = BitVec.ofNat 32 c →
    reg nn a0 = p →
    ((∀ t, t < c → M (p + BitVec.ofNat 32 t) = 0) →
      ∃ nn', Steps nn nn' ∧ St M BDI nn' 0x12A (reg nn') ∧ ∀ q, q.val ∉ [10, 12, 13] → reg nn' q = reg nn q) ∧
    (¬(∀ t, t < c → M (p + BitVec.ofNat 32 t) = 0) →
      ∃ nn', Steps nn nn' ∧ St M BDI nn' 0x16E (reg nn') ∧ ∀ q, q.val ∉ [10, 12, 13] → reg nn' q = reg nn q)
  | 0, p, nn, _, st, r12, _ => by
    refine ⟨fun _ => ?_, fun h => absurd (fun t ht => absurd ht (Nat.not_lt_zero t)) h⟩
    obtain ⟨n1, d1, u1⟩ := st.taken hc 0x12A bdi_at_11c (by decide) (by rw [r12, st.zero]; rfl)
    exact ⟨n1, .single d1, u1.self, fun q _ => by rw [u1.regs]⟩
  | c + 1, p, nn, hc2, st, r12, r10 => by
    have hz := st.zero
    obtain ⟨n1, d1, u1⟩ := st.notTaken hc 0x11E bdi_at_11c (by decide) (by
      rw [r12, hz]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
      exact fun e => absurd (congrArg BitVec.toNat e) (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.succ_ne_zero c))
    obtain ⟨n2, d2, u2⟩ := u1.self.lbu hc bdi_at_11e (off' := 0x122) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc bdi_at_122 (off' := 0x124) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc bdi_at_124 (off' := 0x126) (by decide)
    have K4 : ∀ q, q.val ∉ [10, 12, 13] → reg n4 q = reg nn q := fun q hq => by
      rw [u4.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) u3.self.zero, u3.regs,
        upd_ne' (by intro e; apply hq; rw [e]; decide) u2.self.zero, u2.regs,
        upd_ne' (by intro e; apply hq; rw [e]; decide) u1.self.zero, u1.regs]
    have v13 : reg n4 a3 = (M p).zeroExtend 32 := by
      rw [u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs, upd_ne' (by decide) u2.self.zero, u2.regs]
      simp +decide only [upd_app, ↓reduceIte]; rw [u1.regs, r10, add_lit_zero]
    have v10 : reg n4 a0 = p + 1 := by
      rw [u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs, r10]; rfl
    have v12 : reg n4 a2 = BitVec.ofNat 32 c := by
      rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u3.regs, upd_ne' (by decide) u2.self.zero, u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs, r12]
      exact BitVec.eq_of_toNat_eq (by
        rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
        omega)
    have z8 : ∀ b : BitVec 8, (b.zeroExtend 32 = 0) ↔ b = 0 := by decide
    have hsh : ∀ t, p + 1 + BitVec.ofNat 32 t = p + BitVec.ofNat 32 (t + 1) := fun t => by
      rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, Nat.add_comm]
    by_cases h0 : M p = 0
    · obtain ⟨n5, d5, u5⟩ := u4.self.taken hc 0x11C bdi_at_126 (by decide) (by
        rw [v13, u4.self.zero, (z8 _).mpr h0]; rfl)
      obtain ⟨E, O⟩ := bdi_zero hc c (p + 1) n5 (by omega) u5.self (by rw [u5.regs, v12]) (by rw [u5.regs, v10])
      have iff : (∀ t, t < c + 1 → M (p + BitVec.ofNat 32 t) = 0) ↔ ∀ t, t < c → M (p + 1 + BitVec.ofNat 32 t) = 0 :=
        ⟨fun h t ht => by rw [hsh]; exact h _ (by omega), fun h t ht => by
          cases t with
          | zero => rw [add_ofNat_zero]; exact h0
          | succ t => rw [← hsh]; exact h t (by omega)⟩
      have pre : Steps nn n5 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5))))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨n6, c6, u6, K6⟩ := E (iff.mp h)
        exact ⟨n6, pre.trans c6, u6, fun q hq => by rw [K6 q hq, u5.regs, K4 q hq]⟩
      · obtain ⟨n6, c6, u6, K6⟩ := O (fun h' => h (iff.mpr h'))
        exact ⟨n6, pre.trans c6, u6, fun q hq => by rw [K6 q hq, u5.regs, K4 q hq]⟩
    · obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hc 0x128 bdi_at_126 (by decide) (by
        rw [v13, u4.self.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
        exact fun e => h0 ((z8 _).mp e))
      obtain ⟨n6, d6, u6⟩ := u5.self.jump hc bdi_at_128 (off' := 0x16E) (by decide) (by rw [u5.pc]; decide)
      refine ⟨fun h => absurd (by have := h 0 (by omega); rwa [add_ofNat_zero] at this) h0, fun _ => ?_⟩
      exact ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), u6.self,
        fun q hq => by rw [u6.regs, u5.regs, K4 q hq]⟩

theorem bdi_b8 (b : BitVec 8) (c : Nat) (h : b.toNat = c) : (b = 0) = (c = 0) := by
  subst h; apply propext; constructor
  · intro e; subst e; rfl
  · intro e; exact BitVec.eq_of_toNat_eq (by rw [e]; rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- A group's bytes, from 0xF8: the bits go to `sp + 9` big-endian, and the
bytes the padding drops must be zero. -/
theorem bdi_bytes {M : Word → BitVec 8} (hc : CodeIn M BDI base64DecodeIntoCode) {nn : Machine} {F : Word}
    {bits pad : Nat} (st : St M BDI nn 0xF8 (reg nn)) (hb : bits < 2 ^ 24) (hp : pad ≤ 2)
    (r13 : reg nn a3 = BitVec.ofNat 32 bits) (r12 : reg nn a2 = BitVec.ofNat 32 pad) (r25 : reg nn 25 = 0xFF00)
    (r6 : reg nn 6 = F + 9) (rsp : reg nn sp = F) (hFa : (F + 8).toNat % 4 = 0)
    (sFC : Sep (F + 8) 4 BDI base64DecodeIntoCode.length) :
    ∃ Ms : Word → BitVec 8, (∀ x, Sep (F + 8) 4 x 1 → Ms x = M x) ∧ CodeIn Ms BDI base64DecodeIntoCode ∧
      (bdiBytes bits pad = none → ∃ nn', Steps nn nn' ∧ St Ms BDI nn' 0x16E (reg nn') ∧
        ∀ q, q.val ∉ [10, 11, 12, 13, 15] → reg nn' q = reg nn q) ∧
      (∀ bs, bdiBytes bits pad = some bs → bs = memBytes Ms (F + 9) (3 - pad) ∧ ∃ nn', Steps nn nn' ∧
        St Ms BDI nn' 0x12A (reg nn') ∧ reg nn' a1 = BitVec.ofNat 32 (3 - pad) ∧
        ∀ q, q.val ∉ [10, 11, 12, 13, 15] → reg nn' q = reg nn q) := by
  have hz := st.zero
  obtain ⟨n1, c1, u1⟩ := St.block bdiS st hc bdiS_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, bdiS, upd_app, ↓reduceIte, and_true, true_and]
    rw [rsp]; exact ⟨hFa, sFC⟩)
  obtain ⟨W, hW⟩ : ∃ W, aluEval .or (aluEval .or (aluEval .and (aluEval .srl (BitVec.ofNat 32 bits) 0x8) 0xFF00)
      (aluEval .srl (BitVec.ofNat 32 bits) 0x18)) (aluEval .or (aluEval .sll (BitVec.ofNat 32 bits) 0x18)
      (aluEval .sll (aluEval .and (BitVec.ofNat 32 bits) 0xFF00) 0x8)) = W := ⟨_, rfl⟩
  have eM : (runBlock bdiS (M, reg nn)).1 = memStore32 M (F + 8) W := by
    simp +decide only [runBlock, BInstr.run, bdiS, upd_app, ↓reduceIte]; rw [rsp, r13, r25, hW]
  rw [eM] at u1
  refine ⟨memStore32 M (F + 8) W, fun x hx => memStore32_get_sep hx, CodeIn.store32 hc sFC, ?_⟩
  have R1 : ∀ r, reg n1 r = (runBlock bdiS (M, reg nn)).2 r := u1.regs
  have u1' : St (memStore32 M (F + 8) W) BDI n1 0x11C (reg n1) := u1.self
  have K1 : ∀ q, q.val ∉ [10, 11, 13, 15] → reg n1 q = reg nn q := fun q hq => by
    have hd : q ∉ bdiS.filterMap BInstr.dst := by
      simp only [bdiS, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R1, runBlock_reg _ _ _ q hz hd]
  have v11 : reg n1 a1 = BitVec.ofNat 32 (3 - pad) := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, bdiS, upd_app, ↓reduceIte]; rw [r12]
    obtain rfl | rfl | rfl : pad = 0 ∨ pad = 1 ∨ pad = 2 := by omega
    all_goals rfl
  have v10 : reg n1 a0 = F + 9 + BitVec.ofNat 32 (3 - pad) := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, bdiS, upd_app, ↓reduceIte]; rw [r12, r6]
    obtain rfl | rfl | rfl : pad = 0 ∨ pad = 1 ∨ pad = 2 := by omega
    all_goals rfl
  have v12 : reg n1 a2 = BitVec.ofNat 32 pad := by rw [K1 a2 (by decide), r12]
  have hB : ∀ k, k < 3 → ((memStore32 M (F + 8) W) (F + 9 + BitVec.ofNat 32 k)).toNat =
      [bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].getD k 0 :=
    fun k hk => by
      have e : F + 9 + BitVec.ofNat 32 k = F + 8 + BitVec.ofNat 32 (k + 1) := by
        rw [show (9 : Word) = BitVec.ofNat 32 (8 + 1) from rfl, ← add_ofNat_assoc, add_ofNat_assoc,
          Nat.add_comm 1 k]; rfl
      rw [e, bdi_st32 _ _ _ _ (by omega) (by omega), ← hW, bdi_bswap _ _ hk, BitVec.extractLsb'_toNat,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show bits < 2 ^ 32 by omega), Nat.shiftRight_eq_div_pow]
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      · rfl
      · rfl
      · rw [show 16 - 8 * 2 = 0 from rfl, Nat.pow_zero, Nat.div_one]; rfl
  obtain ⟨E, O⟩ := bdi_zero (CodeIn.store32 hc sFC) pad _ n1 hp u1' v12 v10
  have mb : memBytes (memStore32 M (F + 8) W) (F + 9) (3 - pad) =
      ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].take (3 - pad)) := by
    have m3 : memBytes (memStore32 M (F + 8) W) (F + 9) 3 = [bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256] := by
      show [(memStore32 M (F + 8) W (F + 9 + BitVec.ofNat 32 0)).toNat, (memStore32 M (F + 8) W (F + 9 + BitVec.ofNat 32 1)).toNat, (memStore32 M (F + 8) W (F + 9 + BitVec.ofNat 32 2)).toNat] = _
      rw [hB 0 (by decide), hB 1 (by decide), hB 2 (by decide)]; rfl
    obtain rfl | rfl | rfl : pad = 0 ∨ pad = 1 ∨ pad = 2 := by omega
    · exact m3
    · show [(memStore32 M (F + 8) W (F + 9 + BitVec.ofNat 32 0)).toNat, (memStore32 M (F + 8) W (F + 9 + BitVec.ofNat 32 1)).toNat] = _; rw [hB 0 (by decide), hB 1 (by decide)]; rfl
    · show [(memStore32 M (F + 8) W (F + 9 + BitVec.ofNat 32 0)).toNat] = _; rw [hB 0 (by decide)]; rfl
  have zc : (∀ t, t < pad → memStore32 M (F + 8) W (F + 9 + BitVec.ofNat 32 (3 - pad) + BitVec.ofNat 32 t) = 0) ↔
      ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].drop (3 - pad)).all (· == 0) = true := by
    have hz' : ∀ t, t < pad → (memStore32 M (F + 8) W (F + 9 + BitVec.ofNat 32 (3 - pad) + BitVec.ofNat 32 t) = 0) =
        ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].getD (3 - pad + t) 0 = 0) := fun t ht => by
      rw [add_ofNat_assoc]; exact bdi_b8 _ _ (hB _ (by omega))
    obtain rfl | rfl | rfl : pad = 0 ∨ pad = 1 ∨ pad = 2 := by omega
    · exact ⟨fun _ => rfl, fun _ t ht => absurd ht (Nat.not_lt_zero t)⟩
    · show _ ↔ ((bits % 256 == 0) && true) = true
      rw [Bool.and_true, beq_iff_eq]
      constructor
      · intro h; have := hz' 0 (by decide); rw [h 0 (by decide)] at this; exact cast this rfl
      · intro h t ht; obtain rfl : t = 0 := by omega
        rw [hz' 0 (by decide)]; exact h
    · show _ ↔ ((bits / 2 ^ 8 % 256 == 0) && ((bits % 256 == 0) && true)) = true
      rw [Bool.and_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      constructor
      · intro h
        have e0 := hz' 0 (by decide); rw [h 0 (by decide)] at e0
        have e1 := hz' 1 (by decide); rw [h 1 (by decide)] at e1
        exact ⟨cast e0 rfl, cast e1 rfl⟩
      · intro h t ht
        obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
        · rw [hz' 0 (by decide)]; exact h.1
        · rw [hz' 1 (by decide)]; exact h.2
  have hbB : bdiBytes bits pad = if ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].drop (3 - pad)).all (· == 0)
      then some ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].take (3 - pad)) else none := by
    unfold bdiBytes require
    show Option.bind (if (([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].drop (3 - pad)).all fun x => x == 0) = true then some () else none)
      (fun _ => some ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].take (3 - pad))) = _
    cases ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].drop (3 - pad)).all (· == 0) <;> rfl
  rw [hbB]
  refine ⟨fun h => ?_, fun bs h => ?_⟩
  · have hn : ¬ ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].drop (3 - pad)).all (· == 0) = true := by
      intro e; rw [if_pos e] at h; cases h
    obtain ⟨n2, c2, u2, K2⟩ := O (fun h' => hn (zc.mp h'))
    exact ⟨n2, c1.trans c2, u2, fun q hq => by
      rw [K2 q (by revert hq; revert q; decide), K1 q (by revert hq; revert q; decide)]⟩
  · have hy : ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].drop (3 - pad)).all (· == 0) = true := by
      cases e : ([bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256].drop (3 - pad)).all (· == 0) with
      | true => rfl
      | false => rw [e, if_neg Bool.false_ne_true] at h; cases h
    rw [if_pos hy] at h; cases h
    obtain ⟨n2, c2, u2, K2⟩ := E (zc.mpr hy)
    exact ⟨mb.symm, n2, c1.trans c2, u2, by rw [K2 a1 (by decide), v11], fun q hq => by
      rw [K2 q (by revert hq; revert q; decide), K1 q (by revert hq; revert q; decide)]⟩

abbrev BCW : Word := BitVec.ofNat 32 copyFromSliceU8Address
abbrev BMS : Word := BitVec.ofNat 32 memcpyStubAddress
abbrev BMB : Word := BitVec.ofNat 32 memcpyBodyAddress

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A group's bytes out, from 0x12A: the length checks, then
`copy_from_slice` of the `keep` bytes at `sp + 9` to `out + written`. -/
theorem bdi_copy {Ms : Word → BitVec 8} (hc : CodeIn Ms BDI base64DecodeIntoCode)
    (hcW : CodeIn Ms BCW copyFromSliceU8Code) (hcS : CodeIn Ms BMS memcpyStubCode)
    (hcB : CodeIn Ms BMB memcpyBodyCode) {nn : Machine} {F out : Word} {keep w L : Nat}
    (st : St Ms BDI nn 0x12A (reg nn)) (hk : keep ≤ 3) (hwL : w ≤ L) (hFr : 16 ≤ F.toNat) (hFa : F.toNat % 4 = 0)
    (hF4 : F.toNat + 0x40 ≤ 0x40000000) (hdw : out.toNat + L ≤ 0x40000000) (sOF : Sep out L (F + 0xFFFFFFF0) 0x50)
    (r11 : reg nn a1 = BitVec.ofNat 32 keep) (r16 : reg nn a6 = BitVec.ofNat 32 w)
    (r14 : reg nn a4 = BitVec.ofNat 32 L) (r23 : reg nn 23 = out) (r6 : reg nn 6 = F + 9) (rsp : reg nn sp = F) :
    (L < w + keep → ∃ nn', Steps nn nn' ∧ St Ms BDI nn' 0x19C (reg nn') ∧ ∀ q, q.val ≠ 8 → reg nn' q = reg nn q) ∧
    (w + keep ≤ L → ∃ nn', Steps nn nn' ∧ St nn'.mem BDI nn' 0x160 (reg nn') ∧
      (∀ x, 0x40000000 ≤ x.toNat → nn'.mem x = Ms x) ∧
      (∀ x, Sep (F + 0xFFFFFFF0) 0x18 x 1 → Sep (out + BitVec.ofNat 32 w) keep x 1 → nn'.mem x = Ms x) ∧
      (∀ j, j < keep → nn'.mem (out + BitVec.ofNat 32 w + BitVec.ofNat 32 j) = Ms (F + 9 + BitVec.ofNat 32 j)) ∧
      reg nn' sp = F ∧ reg nn' a1 = reg nn 24 ∧ reg nn' a6 = BitVec.ofNat 32 (w + keep) ∧
      reg nn' 30 = BitVec.ofNat 32 10 ∧
      ∀ q, q.val ∈ [3, 4, 6, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] → reg nn' q = reg nn q) := by
  have hz := st.zero
  have hL : L ≤ 2 ^ 30 := by omega
  obtain ⟨n1, d1, u1⟩ := st.alu hc bdi_at_12a (off' := 0x12E) (by decide)
  have v8 : reg n1 8 = BitVec.ofNat 32 (w + keep) := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r11, r16]
    show BitVec.ofNat 32 keep + BitVec.ofNat 32 w = _; rw [BitVec.ofNat_add_ofNat, Nat.add_comm]
  have K1 : ∀ q, q.val ≠ 8 → reg n1 q = reg nn q := fun q hq => by
    rw [u1.regs, upd_ne' (fun e => hq (by rw [e]; rfl)) hz]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x132 bdi_at_12e (by decide) (by
    rw [v8, K1 a1 (by decide), r11]; simp only [branchTaken, BitVec.ult, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : w + keep < 2 ^ 32), Nat.mod_eq_of_lt (by omega : keep < 2 ^ 32)]
    exact decide_eq_false (by omega))
  have K2 : ∀ q, q.val ≠ 8 → reg n2 q = reg nn q := fun q hq => by rw [u2.regs, K1 q hq]
  have v28 : reg n2 8 = BitVec.ofNat 32 (w + keep) := by rw [u2.regs, v8]
  have bt : branchTaken .bltu (reg n2 a4) (reg n2 8) = decide (L < w + keep) := by
    rw [v28, K2 a4 (by decide), r14]; simp only [branchTaken, BitVec.ult, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : L < 2 ^ 32), Nat.mod_eq_of_lt (by omega : w + keep < 2 ^ 32)]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x19C bdi_at_132 (by decide) (by rw [bt]; exact decide_eq_true h)
    exact ⟨n3, .cons d1 (.cons d2 (.single d3)), u3.self, fun q hq => by rw [u3.regs, K2 q hq]⟩
  obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x136 bdi_at_132 (by decide) (by
    rw [bt]; exact decide_eq_false (by omega))
  have K3 : ∀ q, q.val ≠ 8 → reg n3 q = reg nn q := fun q hq => by rw [u3.regs, K2 q hq]
  have z3 := u3.self.zero
  have rsp3 : reg n3 sp = F := by rw [K3 sp (by decide), rsp]
  have hBn : BDI.toNat = (img% base64DecodeIntoAddress) := by decide
  have hBl : base64DecodeIntoCode.length = 0x1A0 := by decide
  have eF4 : (F + 4).toNat = F.toNat + 4 := by rw [BitVec.toNat_add]; rw [show (4 : Word).toNat = 4 from rfl]; omega
  have sF4C : Sep (F + 4) 4 BDI base64DecodeIntoCode.length :=
    sep_of_le (by rw [eF4, hBn]; omega) (by rw [hBn, hBl]; decide)
  obtain ⟨n4, c4, u4⟩ := St.block bdiC1 u3.self hc bdiC1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, bdiC1, upd_app, ↓reduceIte, and_true, true_and]
    rw [rsp3]; exact ⟨by rw [eF4]; omega, sF4C⟩)
  have eM4 : (runBlock bdiC1 (Ms, reg n3)).1 = memStore32 Ms (F + 4) (reg nn 19) := by
    simp +decide only [runBlock, BInstr.run, bdiC1, upd_app, ↓reduceIte]; rw [rsp3, K3 19 (by decide)]
  obtain ⟨f4, hf4⟩ : ∃ f4, (runBlock bdiC1 (Ms, reg n3)).2 = f4 := ⟨_, rfl⟩
  rw [eM4, hf4] at u4
  have F4' : ∀ q, q.val ∉ [10, 12, 13, 9, 19, 18, 27] → f4 q = reg n3 q := fun q hq => by
    have hd : q ∉ bdiC1.filterMap BInstr.dst := by
      simp only [bdiC1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [← hf4, runBlock_reg _ _ _ q z3 hd]
  have F4 : ∀ q, q.val ∉ [8, 10, 12, 13, 9, 19, 18, 27] → f4 q = reg nn q := fun q hq => by
    rw [F4' q (by revert hq; revert q; decide), K3 q (by revert hq; revert q; decide)]
  have f48 : f4 8 = BitVec.ofNat 32 (w + keep) := by rw [F4' 8 (by decide), u3.regs, v28]
  have fv : ∀ q : Fin 32, ∀ v, (q, v) ∈ [((10 : Fin 32), out + BitVec.ofNat 32 w), (12, F + 9), (13, BitVec.ofNat 32 keep),
      (9, reg nn 17), (19, reg nn 18), (18, F + 9), (27, BitVec.ofNat 32 L)] → f4 q = v := by
    intro q v hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rw [← hf4]
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp +decide only [runBlock, BInstr.run, bdiC1, upd_app, ↓reduceIte] <;> (try rw [z3]) <;> (try rw [dn_z])
    · rw [K3 23 (by decide), K3 a6 (by decide), r23, r16]; rfl
    · rw [K3 6 (by decide), r6]
    · rw [K3 a1 (by decide), r11]
    · rw [K3 17 (by decide)]
    · rw [K3 18 (by decide)]
    · rw [K3 6 (by decide), r6]
    · rw [K3 a4 (by decide), r14]
  have hc4 : CodeIn (memStore32 Ms (F + 4) (reg nn 19)) BDI base64DecodeIntoCode := CodeIn.store32 hc sF4C
  obtain ⟨m5, c5, pc5, mem5, regs5⟩ := u4.callRa hc4 bdi_at_148 bdi_at_14c (cb := BCW) (by decide) (by decide)
  -- the stack below `sp`
  obtain ⟨R, hR⟩ : ∃ R, F + 0xFFFFFFF0 = R := ⟨_, rfl⟩
  rw [hR] at sOF
  have hRn : R.toNat = F.toNat - 16 := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x50 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc' => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eF9 : F + 9 = R + BitVec.ofNat 32 25 := by rw [← hR, BitVec.add_assoc]; rfl
  have eF4' : F + 4 = R + BitVec.ofNat 32 20 := by rw [← hR, BitVec.add_assoc]; rfl
  have eD : (out + BitVec.ofNat 32 w).toNat = out.toNat + w := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hBMB : BMB.toNat = (img% memcpyBodyAddress) := by decide
  have hBMl : memcpyBodyCode.length ≤ 0x1000 := by decide
  have sR0 : Sep (out + BitVec.ofNat 32 w) keep R 16 := by
    have := (sOF.sub (c := w) (l := keep) (by omega)).subR (c := 0) (l := 16) (by decide)
    rwa [add_ofNat_zero] at this
  have sDS : Sep (out + BitVec.ofNat 32 w) keep (F + 9) keep := by
    rw [eF9]; exact (sOF.sub (c := w) (l := keep) (by omega)).subR (c := 25) (l := keep) (by omega)
  have sF4x : ∀ x : Word, Sep R 0x18 x 1 → Sep (F + 4) 4 x 1 := fun x hx => by
    rw [eF4']; exact (hx.symm.subR (c := 20) (l := 4) (by decide)).symm
  have hiM : ∀ x : Word, 0x40000000 ≤ x.toNat → memStore32 Ms (F + 4) (reg nn 19) x = Ms x := fun x hx =>
    memStore32_get_sep (sep_of_le (by rw [eF4]; omega) (by have := x.isLt; omega))
  have E : McEnv m5.mem (BCW + 0x761E + 8) (out + BitVec.ofNat 32 w) (F + 9) (reg m5 sp + 0xFFFFFFF0) keep := by
    have sp5 : reg m5 sp = F := by rw [regs5, upd_ne' (by decide) u4.zero, F4 sp (by decide), rsp]
    rw [sp5, hR, mem5, show BCW + 0x761E + 8 = BMB from by decide]
    exact {
      code := CodeIn.hi hcB hiM (by rw [hBMB]; decide) (by rw [hBMB]; omega)
      hDC := sep_of_le (by rw [eD, hBMB]; omega) (by rw [hBMB]; omega)
      hFC := sep_of_le (by rw [hRn, hBMB]; omega) (by rw [hBMB]; omega)
      hdF := sR0
      hsF := by
        rw [eF9]; have := sep_offsets R (c := 25) (n := keep) (d := 0) (k := 16) (Or.inr (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      hsep := sDS
      hF := by rw [hRn]; omega
      hFw := by rw [hRn]; omega
      hdw := by rw [eD]; omega
      hsw := by rw [eF9, hRc _ (by decide), hRn]; omega }
  have ha5 : ∀ q, q ≠ ra → reg m5 q = f4 q := fun q hq => by rw [regs5, upd_ne' hq u4.zero]
  obtain ⟨m6, c6, pc6, sp6, a06, mem6, K6⟩ := copyFromSliceU8_correct m5 (W := BCW) (retAddr := BDI + BitVec.ofNat 32 0x150)
    (by decide) (by rw [mem5]; exact CodeIn.hi hcW hiM (by decide) (by decide))
    (by rw [mem5, show BCW + 0x761E = BMS from by decide]; exact CodeIn.hi hcS hiM (by decide) (by decide)) pc5
    (by rw [ha5 a0 (by decide)]; exact fv 10 _ (by simp only [List.mem_cons, true_or, or_true]))
    (by rw [ha5 a1 (by decide), F4 a1 (by decide), r11])
    (by rw [ha5 a2 (by decide)]; exact fv 12 _ (by simp only [List.mem_cons, true_or, or_true]))
    (by rw [ha5 a3 (by decide)]; exact fv 13 _ (by simp only [List.mem_cons, true_or, or_true]))
    (by rw [regs5]; simp +decide only [upd_app, ↓reduceIte]) (by decide) E
  have sp5 : reg m5 sp = F := by rw [ha5 sp (by decide), F4 sp (by decide), rsp]
  have M6 : ∀ x, Sep R 16 x 1 →
      m6.mem x = copyBytes (memStore32 Ms (F + 4) (reg nn 19)) (out + BitVec.ofNat 32 w) (F + 9) keep x := by
    intro x hx; rw [mem6 x (by rw [sp5, hR]; exact hx), mem5]
  have hi6 : ∀ x : Word, 0x40000000 ≤ x.toNat → m6.mem x = Ms x := fun x hx => by
    rw [M6 x (sep_of_le (by rw [hRn]; omega) (by have := x.isLt; omega)),
      copyBytes_sep (sep_of_le (by rw [eD]; omega) (by have := x.isLt; omega)) (Nat.le_refl _), hiM x hx]
  have hc6 : CodeIn m6.mem BDI base64DecodeIntoCode :=
    CodeIn.hi hc hi6 (by rw [hBn]; decide) (by rw [hBn, hBl]; decide)
  have st6 : St m6.mem BDI m6 0x150 (reg m6) := ⟨pc6, rfl, fun _ => rfl⟩
  have rsp6 : reg m6 sp = F := by rw [sp6, sp5]
  obtain ⟨n7, c7, u7⟩ := St.block bdiC2 st6 hc6 bdiC2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, bdiC2, upd_app, ↓reduceIte, and_true, true_and]
    rw [rsp6, eF4]; omega)
  have mem7 : n7.mem = m6.mem := by
    rw [u7.mem]; simp +decide only [runBlock, BInstr.run, bdiC2]
  have R7 : ∀ q, reg n7 q = (runBlock bdiC2 (m6.mem, reg m6)).2 q := u7.regs
  have z6 := st6.zero
  have K6' : ∀ r : Fin 32, r.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m6 r = reg m5 r :=
    fun r hr => K6 r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide)
  have K7 : ∀ q, q.val ∉ [30, 14, 6, 18, 17, 19, 11, 16] → reg n7 q = reg m6 q := fun q hq => by
    have hd : q ∉ bdiC2.filterMap BInstr.dst := by
      simp only [bdiC2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R7, runBlock_reg _ _ _ q z6 hd]
  have sub16 : ∀ {x : Word}, Sep R 0x18 x 1 → Sep R 16 x 1 := fun hx => by
    have := hx.sub (c := 0) (l := 16) (by decide); rwa [add_ofNat_zero] at this
  have ld4 : memLoad32 m6.mem (F + 4) = reg nn 19 := by
    rw [← memLoad32_store32_same Ms (F + 4) (reg nn 19)]
    apply memLoad32_congr; intro j hj
    have ex : F + 4 + BitVec.ofNat 32 j = R + BitVec.ofNat 32 (20 + j) := by rw [eF4', add_ofNat_assoc]
    have hx : Sep R 16 (R + BitVec.ofNat 32 (20 + j)) 1 := by
      have := sep_offsets R (c := 0) (n := 16) (d := 20 + j) (k := 1) (by omega) (by decide) (by omega)
      rwa [add_ofNat_zero] at this
    rw [ex, M6 _ hx, copyBytes_sep ((sOF.sub (c := w) (l := keep) (by omega)).subR (c := 20 + j) (l := 1) (by omega))
      (Nat.le_refl _)]
  have F4s : ∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26] → reg n7 q = reg nn q := fun q hq => by
    rw [K7 q (by revert hq; revert q; decide), K6' q (by revert hq; revert q; decide),
      ha5 q (by revert hq; revert q; decide), F4 q (by revert hq; revert q; decide)]
  have v7 : ∀ q r, (q, r) ∈ [((6 : Fin 32), (18 : Fin 32)), (14, 27), (17, 9), (18, 19), (11, 24), (16, 8)] →
      reg n7 q = reg m6 r := by
    intro q r hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (rw [R7]; simp +decide only [runBlock, BInstr.run, bdiC2, upd_app, ↓reduceIte]) <;> (try rw [z6]) <;>
      (try rw [dn_z])
  have g6 : ∀ r, r.val ∈ [8, 9, 18, 19, 24, 27] → reg m6 r = f4 r := fun r hr => by
    rw [K6' r (by revert hr; revert r; decide), ha5 r (by revert hr; revert r; decide)]
  refine ⟨n7, (Steps.cons d1 (.cons d2 (.cons d3 c4))).trans (c5.trans (c6.trans c7)), ⟨u7.pc, rfl, fun _ => rfl⟩,
    fun x hx => by rw [mem7, hi6 x hx], fun x hx hd => ?_, fun j hj => ?_, by rw [K7 sp (by decide), rsp6], ?_, ?_,
    ?_, fun q hq => ?_⟩
  · rw [hR] at hx
    rw [mem7, M6 x (sub16 hx), copyBytes_sep hd (Nat.le_refl _), memStore32_get_sep (sF4x x hx)]
  · have hx : Sep R 16 (out + BitVec.ofNat 32 w + BitVec.ofNat 32 j) 1 := (sR0.sub (c := j) (l := 1) (by omega)).symm
    rw [mem7, M6 _ hx]; unfold copyBytes
    rw [BitVec.add_comm (out + BitVec.ofNat 32 w), BitVec.add_sub_cancel, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : j < 2 ^ 32), if_pos hj]
    apply memStore32_get_sep
    rw [eF4', eF9, add_ofNat_assoc]
    exact sep_offsets R (c := 20) (n := 4) (d := 25 + j) (k := 1) (Or.inl (by omega)) (by decide) (by omega)
  · rw [v7 11 24 (by simp only [List.mem_cons, true_or, or_true]), g6 24 (by decide), F4 24 (by decide)]
  · rw [v7 16 8 (by simp only [List.mem_cons, true_or, or_true]), g6 8 (by decide), f48]
  · rw [R7]; simp +decide only [runBlock, BInstr.run, bdiC2, upd_app, ↓reduceIte]; rw [z6]; rfl
  · rcases (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 6, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] →
        q = 6 ∨ q = 14 ∨ q = 17 ∨ q = 18 ∨ q = 19 ∨ q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26]) q hq with
      rfl | rfl | rfl | rfl | rfl | hL
    · rw [v7 6 18 (by simp only [List.mem_cons, true_or, or_true]), g6 18 (by decide),
        fv 18 (F + 9) (by simp only [List.mem_cons, true_or, or_true]), r6]
    · rw [v7 14 27 (by simp only [List.mem_cons, true_or, or_true]), g6 27 (by decide),
        fv 27 (BitVec.ofNat 32 L) (by simp only [List.mem_cons, true_or, or_true]), r14]
    · rw [v7 17 9 (by simp only [List.mem_cons, true_or, or_true]), g6 9 (by decide),
        fv 9 (reg nn 17) (by simp only [List.mem_cons, true_or, or_true])]
    · rw [v7 18 19 (by simp only [List.mem_cons, true_or, or_true]), g6 19 (by decide),
        fv 19 (reg nn 18) (by simp only [List.mem_cons, true_or, or_true])]
    · rw [R7]; simp +decide only [runBlock, BInstr.run, bdiC2, upd_app, ↓reduceIte]; rw [rsp6, ld4]
    · exact F4s q hL

abbrev bdiPs : List (Fin 32 × Word) :=
  [(ra, 0x3C), ((8 : Fin 32), 0x38), ((9 : Fin 32), 0x34), ((18 : Fin 32), 0x30), ((19 : Fin 32), 0x2C),
    ((20 : Fin 32), 0x28), ((21 : Fin 32), 0x24), ((22 : Fin 32), 0x20), ((23 : Fin 32), 0x1C), ((24 : Fin 32), 0x18),
    ((25 : Fin 32), 0x14), ((26 : Fin 32), 0x10), ((27 : Fin 32), 0xC)]

section
set_option maxRecDepth 20000
theorem bdiSave_end : blockEnd base64DecodeIntoCode 2 (saveBlock bdiPs) = some 0x1C := by decide
theorem bdiRestore_end : blockEnd base64DecodeIntoCode 0x17A (restoreBlock bdiPs) = some 0x194 := by decide
end

set_option maxRecDepth 20000 in
/-- The epilogue, from 0x17A: the saved registers come back from the frame
and `decode_into` returns. -/
theorem bdi_epi {Mt : Word → BitVec 8} (hc : CodeIn Mt BDI base64DecodeIntoCode) {nn : Machine} {F : Word}
    {v : Fin 32 → Word} (st : St Mt BDI nn 0x17A (reg nn)) (rsp : reg nn sp = F) (hFa : F.toNat % 4 = 0)
    (hs : ∀ r o, (r, o) ∈ bdiPs → memLoad32 Mt (F + o) = v r) (hret : v ra &&& ~~~1 = v ra) :
    ∃ nn', Steps nn nn' ∧ nn'.pc = v ra ∧ reg nn' sp = F + 0x40 ∧ nn'.mem = Mt ∧
      (∀ r o, (r, o) ∈ bdiPs → reg nn' r = v r) ∧ ∀ q, q.val ∈ [3, 4] → reg nn' q = reg nn q := by
  have hpsp : ∀ p ∈ bdiPs, p.1 ≠ sp := by decide
  obtain ⟨n2, c2, u2⟩ := St.block (restoreBlock bdiPs) st hc bdiRestore_end
    (restoreBlock_ok Mt F bdiPs (reg nn) rsp hpsp fun q hq => by
      simp only [bdiPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact aligned_add hFa (by decide))
  simp only [restoreBlock_run Mt F bdiPs (reg nn) rsp hpsp] at u2
  have rsp' : restoreRegs Mt F (reg nn) bdiPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc bdi_at_194 (off' := 0x196) (by decide)
  obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc bdi_at_196
  have hslot : ∀ r o, (r, o) ∈ bdiPs → reg n4 r = v r := fun r o hm => by
    rw [regs4]
    have hr : r ≠ sp := hpsp (r, o) hm
    have hr0 : r.val ≠ 0 := by
      simp only [bdiPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [upd_ne hr0 hr, ← hs r o hm]
    simp only [bdiPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; (try rw [rsp])
  refine ⟨n4, c2.trans (.cons d3 (.single d4)), ?_, ?_, ?_, hslot, fun q hq => ?_⟩
  · rw [pc4, ← regs4, hslot ra 0x3C (by decide), add_lit_zero, hret]
  · rw [regs4]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [rsp']
  · rw [mem4]
  · obtain ⟨hv, hs', hps⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ bdiPs, p.1 ≠ q) := by revert hq; revert q; decide
    rw [regs4, upd_ne hv hs', restoreRegs_ne _ _ _ _ q st.zero hps]

/-- The facts every exit gives: the state at 0x17A over memory `Mt'`, the
tag at `res`, and nothing else written but `res`'s 8 bytes. -/
def BdiOut (Mt : Word → BitVec 8) (nn : Machine) (res : Word) (tag : BitVec 8) (nn' : Machine)
    (Mt' : Word → BitVec 8) : Prop :=
  Steps nn nn' ∧ St Mt' BDI nn' 0x17A (reg nn') ∧ CodeIn Mt' BDI base64DecodeIntoCode ∧ Mt' res = tag ∧
    (∀ x, Sep res 8 x 1 → Mt' x = Mt x) ∧ ∀ q, q.val ∉ [10, 11] → reg nn' q = reg nn q

theorem bdi_r01 (res : Word) : res + 1 ≠ res := by
  have := add_ofNat_ne res (c := 1) (d := 0) (by decide) (by decide) (by decide)
  rwa [add_ofNat_zero] at this

theorem bdi_sx {res x : Word} {c : Nat} (h : Sep res 8 x 1) (hc : c < 8) : x ≠ res + BitVec.ofNat 32 c :=
  fun e => h c hc 0 (by decide) (by rw [add_ofNat_zero, e])

set_option maxRecDepth 20000 in
theorem bdi_ex170 {Mt : Word → BitVec 8} (hc : CodeIn Mt BDI base64DecodeIntoCode) {nn : Machine} {res : Word}
    (st : St Mt BDI nn 0x170 (reg nn)) (r18 : reg nn 18 = res) (sRC : Sep res 8 BDI base64DecodeIntoCode.length) :
    ∃ nn' Mt', BdiOut Mt nn res 1 nn' Mt' := by
  have hz := st.zero
  obtain ⟨n1, d1, u1⟩ := st.aluImm hc bdi_at_170 (off' := 0x172) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.sb hc bdi_at_172 (off' := 0x176) (by decide)
  have e1 : reg n1 18 = res := by rw [u1.regs, upd_ne' (by decide) hz, r18]
  rw [e1, add_lit_zero] at u2
  have s0 : Sep res 1 BDI base64DecodeIntoCode.length := by
    have := sRC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  have hc2 := CodeIn.store8 (v := (reg n1 a1).extractLsb' 0 8) hc s0
  obtain ⟨n3, d3, u3⟩ := u2.self.sb hc2 bdi_at_176 (off' := 0x17A) (by decide)
  rw [u2.regs, e1] at u3
  refine ⟨n3, _, .cons d1 (.cons d2 (.single d3)), u3.self,
    CodeIn.store8 hc2 (show Sep (res + 1) 1 BDI base64DecodeIntoCode.length from sRC.sub (c := 1) (l := 1) (by decide)),
    ?_, fun x hx => ?_, fun q hq => ?_⟩
  · rw [memStore8_ne (bdi_r01 res).symm, memStore8_same, u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [hz]; rfl
  · rw [memStore8_ne (show x ≠ res + 1 from bdi_sx hx (c := 1) (by decide)), memStore8_ne (by
      have := bdi_sx hx (c := 0) (by decide); rwa [add_ofNat_zero] at this)]
  · rw [u3.regs, u2.regs, u1.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) hz]

set_option maxRecDepth 20000 in
theorem bdi_ex16E {Mt : Word → BitVec 8} (hc : CodeIn Mt BDI base64DecodeIntoCode) {nn : Machine} {res : Word}
    (st : St Mt BDI nn 0x16E (reg nn)) (r18 : reg nn 18 = res) (sRC : Sep res 8 BDI base64DecodeIntoCode.length) :
    ∃ nn' Mt', BdiOut Mt nn res 1 nn' Mt' := by
  obtain ⟨n1, d1, u1⟩ := st.aluImm hc bdi_at_16e (off' := 0x170) (by decide)
  obtain ⟨n2, Mt', c2, u2, hc2, h1, hf, K⟩ := bdi_ex170 hc u1.self (by rw [u1.regs, upd_ne' (by decide) st.zero, r18]) sRC
  exact ⟨n2, Mt', .cons d1 c2, u2, hc2, h1, hf, fun q hq => by
    rw [K q hq, u1.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) st.zero]⟩

set_option maxRecDepth 20000 in
theorem bdi_ex19C {Mt : Word → BitVec 8} (hc : CodeIn Mt BDI base64DecodeIntoCode) {nn : Machine} {res : Word}
    (st : St Mt BDI nn 0x19C (reg nn)) (r18 : reg nn 18 = res) (sRC : Sep res 8 BDI base64DecodeIntoCode.length) :
    ∃ nn' Mt', BdiOut Mt nn res 1 nn' Mt' := by
  obtain ⟨n1, d1, u1⟩ := st.aluImm hc bdi_at_19c (off' := 0x19E) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.jump hc bdi_at_19e (off' := 0x170) (by decide) (by rw [u1.pc]; decide)
  obtain ⟨n3, Mt', c3, u3, hc3, h1, hf, K⟩ := bdi_ex170 hc u2.self
    (by rw [u2.regs, u1.regs, upd_ne' (by decide) st.zero, r18]) sRC
  exact ⟨n3, Mt', .cons d1 (.cons d2 c3), u3, hc3, h1, hf, fun q hq => by
    rw [K q hq, u2.regs, u1.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) st.zero]⟩

set_option maxRecDepth 20000 in
theorem bdi_ex26 {Mt : Word → BitVec 8} (hc : CodeIn Mt BDI base64DecodeIntoCode) {nn : Machine} {res : Word}
    (st : St Mt BDI nn 0x26 (reg nn)) (r18 : reg nn 18 = res) (sRC : Sep res 8 BDI base64DecodeIntoCode.length)
    (hra : res.toNat % 4 = 0) : ∃ nn' Mt', BdiOut Mt nn res 1 nn' Mt' := by
  have hz := st.zero
  obtain ⟨n1, d1, u1⟩ := st.lui hc bdi_at_26 (off' := 0x28) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc bdi_at_28 (off' := 0x2C) (by decide)
  have e2 : reg n2 18 = res := by
    rw [u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs, upd_ne' (by decide) hz, r18]
  have v2 : reg n2 a0 = 0x1C01 := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
  obtain ⟨n3, d3, u3⟩ := u2.self.sh hc bdi_at_2c (off' := 0x30) (by decide) (by rw [e2, add_lit_zero]; omega)
  rw [e2, add_lit_zero, v2] at u3
  have s0 : Sep res 1 BDI base64DecodeIntoCode.length := by
    have := sRC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  have hc3 := (CodeIn.store8 (v := (0x1C01 : Word).extractLsb' 0 8) hc s0).store8
    (v := (0x1C01 : Word).extractLsb' 8 8) (sRC.sub (c := 1) (l := 1) (by decide))
  obtain ⟨n4, d4, u4⟩ := u3.jump hc3 bdi_at_30 (off' := 0x17A) (by decide) (by rw [u3.pc]; decide)
  refine ⟨n4, _, .cons d1 (.cons d2 (.cons d3 (.single d4))), u4.self, hc3, ?_, fun x hx => ?_, fun q hq => ?_⟩
  · rw [memStore8_ne (bdi_r01 res).symm, memStore8_same]; rfl
  · rw [memStore8_ne (show x ≠ res + 1 from bdi_sx hx (c := 1) (by decide)), memStore8_ne (by
      have := bdi_sx hx (c := 0) (by decide); rwa [add_ofNat_zero] at this)]
  · rw [u4.regs, u2.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) u1.self.zero, u1.regs,
      upd_ne' (by intro e; apply hq; rw [e]; decide) hz]

set_option maxRecDepth 20000 in
theorem bdi_ex164 {Mt : Word → BitVec 8} (hc : CodeIn Mt BDI base64DecodeIntoCode) {nn : Machine} {res : Word}
    (st : St Mt BDI nn 0x164 (reg nn)) (r18 : reg nn 18 = res) (sRC : Sep res 8 BDI base64DecodeIntoCode.length)
    (hra : res.toNat % 4 = 0) : ∃ nn' Mt', BdiOut Mt nn res 0 nn' Mt' ∧ memLoad32 Mt' (res + 4) = reg nn a6 := by
  have hz := st.zero
  obtain ⟨n1, d1, u1⟩ := st.sb hc bdi_at_164 (off' := 0x168) (by decide)
  rw [r18, add_lit_zero, hz] at u1
  have s0 : Sep res 1 BDI base64DecodeIntoCode.length := by
    have := sRC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  have hc1 := CodeIn.store8 (v := (0 : Word).extractLsb' 0 8) hc s0
  have hr4 : (res + 4).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; have := res.isLt; omega
  obtain ⟨n2, d2, u2⟩ := u1.sw hc1 bdi_at_168 (off' := 0x16C) (by decide) (by rw [r18]; exact hr4)
  rw [r18] at u2
  have hc2 := CodeIn.store32 (v := reg nn a6) hc1 (sRC.sub (c := 4) (l := 4) (by decide))
  obtain ⟨n3, d3, u3⟩ := u2.jump hc2 bdi_at_16c (off' := 0x17A) (by decide) (by rw [u2.pc]; decide)
  have n04 : ∀ i, i < 4 → res ≠ res + 4 + BitVec.ofNat 32 i := fun i hi e => by
    have := add_ofNat_ne res (c := 0) (d := 4 + i) (by decide) (by omega) (by omega)
    rw [add_ofNat_zero, ← add_ofNat_assoc] at this; exact this e
  refine ⟨n3, _, ⟨.cons d1 (.cons d2 (.single d3)), u3.self, hc2, ?_, fun x hx => ?_, fun q hq => ?_⟩, ?_⟩
  · rw [memStore32_ne n04, memStore8_same]; rfl
  · rw [memStore32_ne (fun i hi => by
      have := bdi_sx hx (c := 4 + i) (by omega); rwa [← add_ofNat_assoc] at this), memStore8_ne (by
      have := bdi_sx hx (c := 0) (by decide); rwa [add_ofNat_zero] at this)]
  · rw [u3.regs]
  · exact memLoad32_store32_same _ _ _

/-- The loop's state between groups: `i` groups decoded into `P`, at offset
`off` (0x5A before a group, 0x164 after the last). `Ms0` is memory after the
prologue, `F` the frame pointer. -/
structure BdiInv (m : Machine) (Ms0 : Word → BitVec 8) (res t out F : Word) (n L G i : Nat) (P : Bytes) (off : Nat)
    (nn : Machine) : Prop where
  st : St nn.mem BDI nn off (reg nn)
  frame : ∀ x, Sep out L x 1 → Sep (F + 0xFFFFFFF0) 0x1C x 1 → nn.mem x = Ms0 x
  outb : memBytes nn.mem out P.length = P
  hw : P.length ≤ L
  spec : base64Decode (memBytes m.mem t n) =
    (base64Decode (memBytes m.mem (t + BitVec.ofNat 32 (4 * i)) (n - 4 * i))).map (P ++ ·)
  rsp : reg nn sp = F
  r11 : reg nn a1 = t + BitVec.ofNat 32 (4 * i)
  r19 : reg nn 19 = BitVec.ofNat 32 i
  r16 : reg nn a6 = BitVec.ofNat 32 P.length
  r17 : 0 < G → reg nn 17 = BitVec.ofNat 32 (G - 1)
  r22 : reg nn 22 = t + BitVec.ofNat 32 n
  r6 : reg nn 6 = F + 9
  r26 : 0 < G → reg nn 26 = 1
  r25 : reg nn 25 = 0xFF00
  r21 : reg nn 21 = BitVec.ofNat 32 4
  r20 : reg nn 20 = BitVec.ofNat 32 26
  r30 : reg nn 30 = BitVec.ofNat 32 10
  r18 : reg nn 18 = res
  r23 : reg nn 23 = out
  r14 : reg nn a4 = BitVec.ofNat 32 L
  r3 : reg nn 3 = reg m 3
  r4 : reg nn 4 = reg m 4

/-- The facts about `decode_into`'s arguments that hold through the loop. -/
structure BdiEnv (m : Machine) (Ms0 : Word → BitVec 8) (res t out F : Word) (n L G : Nat) : Prop where
  hc : CodeIn m.mem BDI base64DecodeIntoCode
  hcW : CodeIn m.mem BCW copyFromSliceU8Code
  hcS : CodeIn m.mem BMS memcpyStubCode
  hcB : CodeIn m.mem BMB memcpyBodyCode
  hMs0 : ∀ x, Sep (F + 0xFFFFFFF0) 0x50 x 1 → Ms0 x = m.mem x
  hFr : 16 ≤ F.toNat
  hFa : F.toNat % 4 = 0
  hF4 : F.toNat + 0x40 ≤ 0x40000000
  hdw : out.toNat + L ≤ 0x40000000
  htw : t.toNat + n ≤ 0x40000000
  sOF : Sep out L (F + 0xFFFFFFF0) 0x50
  sTO : Sep t n out L
  sTF : Sep t n (F + 0xFFFFFFF0) 0x50
  sRC : Sep res 8 BDI base64DecodeIntoCode.length
  hra : res.toNat % 4 = 0

/-- How a group can end in an error: at 0x17A with the tag 1 written, and
memory changed only in the output, the scratch frame, and `res`. -/
def BdiErr (m : Machine) (Ms0 : Word → BitVec 8) (res out F : Word) (L : Nat) (nn nn' : Machine)
    (Mt : Word → BitVec 8) : Prop :=
  Steps nn nn' ∧ St Mt BDI nn' 0x17A (reg nn') ∧ CodeIn Mt BDI base64DecodeIntoCode ∧ Mt res = 1 ∧
    (∀ x, Sep out L x 1 → Sep (F + 0xFFFFFFF0) 0x1C x 1 → Sep res 8 x 1 → Mt x = Ms0 x) ∧
    reg nn' sp = F ∧ reg nn' 3 = reg m 3 ∧ reg nn' 4 = reg m 4

theorem bdi_hi {m : Machine} {Ms0 : Word → BitVec 8} {res t out F : Word} {n L G : Nat}
    (env : BdiEnv m Ms0 res t out F n L G) {M : Word → BitVec 8}
    (h : ∀ x, Sep out L x 1 → Sep (F + 0xFFFFFFF0) 0x1C x 1 → M x = Ms0 x) :
    ∀ x : Word, 0x40000000 ≤ x.toNat → M x = m.mem x := fun x hx => by
  have hR : (F + 0xFFFFFFF0).toNat = F.toNat - 16 := by
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; have := env.hFr; omega
  have := env.hF4
  rw [h x (sep_of_le (by have := env.hdw; omega) (by have := x.isLt; omega))
    (sep_of_le (by rw [hR]; omega) (by have := x.isLt; omega)),
    env.hMs0 x (sep_of_le (by rw [hR]; omega) (by have := x.isLt; omega))]

set_option maxRecDepth 20000 in
/-- The code `decode_into` runs, in any memory that keeps `m`'s above
`0x40000000`. -/
theorem bdi_codes {m : Machine} {M : Word → BitVec 8} (hc : CodeIn m.mem BDI base64DecodeIntoCode)
    (hcW : CodeIn m.mem BCW copyFromSliceU8Code) (hcS : CodeIn m.mem BMS memcpyStubCode)
    (hcB : CodeIn m.mem BMB memcpyBodyCode) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = m.mem x) :
    CodeIn M BDI base64DecodeIntoCode ∧ CodeIn M BCW copyFromSliceU8Code ∧ CodeIn M BMS memcpyStubCode ∧
      CodeIn M BMB memcpyBodyCode :=
  ⟨CodeIn.hi hc h (by decide) (by decide), CodeIn.hi hcW h (by decide) (by decide),
    CodeIn.hi hcS h (by decide) (by decide), CodeIn.hi hcB h (by decide) (by decide)⟩

theorem bdi_rest (M : Word → BitVec 8) (t : Word) {i n : Nat} (h : 4 * i + 4 ≤ n) :
    memBytes M (t + BitVec.ofNat 32 (4 * i)) (n - 4 * i) =
      (M (t + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)).toNat ::
      (M (t + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 1)).toNat ::
      (M (t + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 2)).toNat ::
      (M (t + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 3)).toNat ::
      memBytes M (t + BitVec.ofNat 32 (4 * (i + 1))) (n - 4 * (i + 1)) := by
  rw [show n - 4 * i = 4 + (n - 4 * (i + 1)) by omega, memBytes_split, add_ofNat_assoc,
    show 4 * i + 4 = 4 * (i + 1) by omega]
  rfl

theorem bdi_pad_last {i G : Nat} (hi : i < G) (hG : 4 * G < 2 ^ 32) (M : Word → BitVec 8) (p : Word) :
    (BitVec.ofNat 32 i == BitVec.ofNat 32 (G - 1)) = (memBytes M p (4 * G - 4 * (i + 1))).isEmpty := by
  by_cases h : i + 1 = G
  · have e : BitVec.ofNat 32 i = BitVec.ofNat 32 (G - 1) := by rw [show G - 1 = i by omega]
    rw [show 4 * G - 4 * (i + 1) = 0 by omega, memBytes_zero]; exact beq_iff_eq.mpr e
  · have e : BitVec.ofNat 32 i ≠ BitVec.ofNat 32 (G - 1) := fun e => h (by
      have := ofNat_inj (by omega) (by omega) e; omega)
    rw [show 4 * G - 4 * (i + 1) = (4 * G - 4 * (i + 1) - 1) + 1 by omega, memBytes_succ]
    exact (beq_eq_false_iff_ne.mpr e).trans rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- One group, from 0x5A: either an error exit, with no decoding that fits in
`L` bytes, or the next group's state. -/
theorem bdi_group {m : Machine} {Ms0 : Word → BitVec 8} {res t out F : Word} {n L G : Nat}
    (env : BdiEnv m Ms0 res t out F n L G) (hn : n = 4 * G) {i : Nat} {P : Bytes} {nn : Machine}
    (I : BdiInv m Ms0 res t out F n L G i P 0x5A nn) (hi : i < G) :
    (∃ nn' Mt, BdiErr m Ms0 res out F L nn nn' Mt ∧
      ∀ bs, base64Decode (memBytes m.mem t n) = some bs → L < bs.length) ∨
    (∃ g nn', Steps nn nn' ∧ BdiInv m Ms0 res t out F n L G (i + 1) (P ++ g) (if i + 1 = G then 0x164 else 0x5A) nn') := by
  obtain ⟨st, frame, outb, hw, spec, rsp, r11, r19, r16, r17, r22, r6, r26, r25, r21, r20, r30, r18, r23, r14, r3, r4⟩ := I
  have hiM := bdi_hi env frame
  obtain ⟨hc, hcW, hcS, hcB⟩ := bdi_codes env.hc env.hcW env.hcS env.hcB hiM
  obtain ⟨M, hM⟩ : ∃ M, nn.mem = M := ⟨_, rfl⟩
  rw [hM] at st frame outb hiM hc hcW hcS hcB
  have htw := env.htw
  obtain ⟨R, hR⟩ : ∃ R, F + 0xFFFFFFF0 = R := ⟨_, rfl⟩
  have sOF := env.sOF
  have sTF := env.sTF
  rw [hR] at frame sOF sTF
  have hRn : R.toNat = F.toNat - 16 := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; have := env.hFr; omega
  have hFr := env.hFr
  have hF4 := env.hF4
  have hFa := env.hFa
  have hdw := env.hdw
  have sub1C : ∀ {x : Word}, Sep R 0x50 x 1 → Sep R 0x1C x 1 := fun hx => by
    have := hx.sub (c := 0) (l := 0x1C) (by decide); rwa [add_ofNat_zero] at this
  -- the group's text
  obtain ⟨g, hg⟩ : ∃ g, t + BitVec.ofNat 32 (4 * i) = g := ⟨_, rfl⟩
  have txt : ∀ j, j < 4 → M (g + BitVec.ofNat 32 j) = m.mem (g + BitVec.ofNat 32 j) := fun j hj => by
    have e : g + BitVec.ofNat 32 j = t + BitVec.ofNat 32 (4 * i + j) := by rw [← hg, add_ofNat_assoc]
    rw [e, frame _ ((env.sTO.sub (c := 4 * i + j) (l := 1) (by omega)).symm)
      (sub1C ((sTF.sub (c := 4 * i + j) (l := 1) (by omega)).symm)),
      env.hMs0 _ (by rw [hR]; exact (sTF.sub (c := 4 * i + j) (l := 1) (by omega)).symm)]
  obtain ⟨c, hcd⟩ : ∃ c : Nat → Nat, c = fun j => (M (g + BitVec.ofNat 32 j)).toNat := ⟨_, rfl⟩
  have hrest := bdi_rest m.mem t (i := i) (n := n) (by omega)
  rw [hg, ← txt 0 (by decide), ← txt 1 (by decide), ← txt 2 (by decide), ← txt 3 (by decide)] at hrest
  obtain ⟨rest', hr'⟩ : ∃ r, memBytes m.mem (t + BitVec.ofNat 32 (4 * (i + 1))) (n - 4 * (i + 1)) = r := ⟨_, rfl⟩
  rw [hr'] at hrest
  have hpl : (BitVec.ofNat 32 i == BitVec.ofNat 32 (G - 1)) = rest'.isEmpty := by
    rw [← hr', hn]; exact bdi_pad_last hi (by omega) _ _
  -- padding
  obtain ⟨n1, c1, u1, a51, a31, a21, r281, r241, r191, K1⟩ := bdi_pad hc st (by rw [r11, hg]) r19 (r17 (by omega)) (r26 (by omega)) r21
  obtain ⟨pad, hpad⟩ : ∃ pad, bdiPad (BitVec.ofNat 32 i == BitVec.ofNat 32 (G - 1)) (c 2) (c 3) = pad := ⟨_, rfl⟩
  have hpad' : bdiPad (BitVec.ofNat 32 i == BitVec.ofNat 32 (G - 1)) (M (g + 2)).toNat (M (g + 3)).toNat = pad := by
    rw [← hpad, hcd]; rfl
  rw [hpad'] at a21 r281
  have hp2 : pad ≤ 2 := by rw [← hpad]; exact bdiPad_le _ _ _
  have hspec : base64Decode (memBytes m.mem t n) =
      (((bdiFold (fun j => if 4 - pad ≤ j then some 0 else b64Value (M (g + BitVec.ofNat 32 j)).toNat) 4 0 0).bind
        fun bits => bdiBytes bits pad).bind fun g' => (base64Decode rest').map (g' ++ ·)).map (P ++ ·) := by
    rw [spec, hg, hrest, b64_cons, ← hpl]
    have := b64Group_fold c pad hp2
    rw [← hpad] at this ⊢
    subst hcd
    dsimp only at this
    rw [this]
  have mkErr : ∀ {nn' : Machine} {Mt : Word → BitVec 8}, Steps nn nn' → St Mt BDI nn' 0x17A (reg nn') →
      CodeIn Mt BDI base64DecodeIntoCode → Mt res = 1 → (∀ x, Sep R 0x1C x 1 → Sep res 8 x 1 → Mt x = M x) →
      reg nn' sp = reg nn sp → reg nn' 3 = reg nn 3 → reg nn' 4 = reg nn 4 →
      (∀ bs, base64Decode (memBytes m.mem t n) = some bs → L < bs.length) →
      ∃ nn' Mt, BdiErr m Ms0 res out F L nn nn' Mt ∧
        ∀ bs, base64Decode (memBytes m.mem t n) = some bs → L < bs.length :=
    fun c u hc' h1 hf hsp h3 h4 hs => ⟨_, _, ⟨c, u, hc', h1, fun x hx1 hx2 hx3 => by
      rw [hR] at hx2; rw [hf x hx2 hx3, frame x hx1 hx2], by rw [hsp, rsp], by rw [h3, r3], by rw [h4, r4]⟩, hs⟩
  obtain ⟨EF, OF⟩ := bdi_fold hc (kp := 4 - pad) (g := g) (by omega) 4 0 0 n1 rfl (by decide)
    (by rw [if_neg (by decide)]; exact u1) a51 (by rw [a31]; rfl) r281
    (by rw [K1 a1 (by decide), r11, hg]) (by rw [K1 20 (by decide), r20]) (by rw [K1 30 (by decide), r30])
    (by rw [K1 21 (by decide), r21])
  cases hf : bdiFold (fun j => if 4 - pad ≤ j then some 0 else b64Value (M (g + BitVec.ofNat 32 j)).toNat) 4 0 0 with
  | none =>
    obtain ⟨n2, c2, u2, K2⟩ := EF hf
    obtain ⟨n3, Mt, c3, u3, hc3, h1, hf3, K3⟩ :=
      bdi_ex26 hc u2 (by rw [K2 18 (by decide), K1 18 (by decide), r18]) env.sRC env.hra
    refine Or.inl (mkErr (c1.trans (c2.trans c3)) u3 hc3 h1 (fun x _ hx => hf3 x hx)
      (by rw [K3 sp (by decide), K2 sp (by decide), K1 sp (by decide)])
      (by rw [K3 3 (by decide), K2 3 (by decide), K1 3 (by decide)])
      (by rw [K3 4 (by decide), K2 4 (by decide), K1 4 (by decide)]) fun bs h => ?_)
    rw [hspec, hf] at h
    have h' : (none : Option Bytes) = some bs := h
    cases h'
  | some bits =>
    obtain ⟨hb24, n2, c2, u2, a32, K2⟩ := OF bits hf
    have K12 : ∀ q, q.val ∉ [8, 9, 10, 12, 13, 15, 19, 24, 28] → reg n2 q = reg nn q := fun q hq => by
      rw [K2 q (by revert hq; revert q; decide), K1 q (by revert hq; revert q; decide)]
    have eF8 : F + 8 = R + BitVec.ofNat 32 0x18 := by rw [← hR, BitVec.add_assoc]; rfl
    have hRc : ∀ c, c ≤ 0x50 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc' => by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hBn : BDI.toNat = (img% base64DecodeIntoAddress) := by decide
    have hBl : base64DecodeIntoCode.length = 0x1A0 := by decide
    obtain ⟨Ms, hMs, hcMs, EB, OB⟩ := bdi_bytes hc u2 hb24 hp2 a32 (by rw [K2 a2 (by decide), a21])
      (by rw [K12 25 (by decide), r25]) (by rw [K12 6 (by decide), r6]) (by rw [K12 sp (by decide), rsp])
      (by rw [eF8, hRc _ (by decide), hRn]; omega)
      (sep_of_le (by rw [eF8, hRc _ (by decide), hRn, hBn]; omega) (by rw [hBn, hBl]; decide))
    have hMsF : ∀ x, Sep R 0x1C x 1 → Ms x = M x := fun x hx =>
      hMs x (by rw [eF8]; exact hx.sub (c := 0x18) (l := 4) (by decide))
    have hiMs : ∀ x : Word, 0x40000000 ≤ x.toNat → Ms x = m.mem x := fun x hx => by
      rw [hMs x (sep_of_le (by rw [eF8, hRc _ (by decide), hRn]; omega) (by have := x.isLt; omega)), hiM x hx]
    have hsb : (some bits).bind (fun bits => bdiBytes bits pad) = bdiBytes bits pad := rfl
    cases hb : bdiBytes bits pad with
    | none =>
      obtain ⟨n3, c3, u3, K3⟩ := EB hb
      obtain ⟨n4, Mt, c4, u4, hc4, h1, hf4, K4⟩ :=
        bdi_ex16E hcMs u3 (by rw [K3 18 (by decide), K12 18 (by decide), r18]) env.sRC
      refine Or.inl (mkErr (c1.trans (c2.trans (c3.trans c4))) u4 hc4 h1
        (fun x hx hx' => by rw [hf4 x hx', hMsF x hx])
        (by rw [K4 sp (by decide), K3 sp (by decide), K12 sp (by decide)])
        (by rw [K4 3 (by decide), K3 3 (by decide), K12 3 (by decide)])
        (by rw [K4 4 (by decide), K3 4 (by decide), K12 4 (by decide)]) fun bs h => ?_)
      rw [hspec, hf, hsb, hb] at h
      have h' : (none : Option Bytes) = some bs := h
      cases h'
    | some bs =>
      obtain ⟨hbs, n3, c3, u3, a13, K3⟩ := OB bs hb
      have K123 : ∀ q, q.val ∉ [8, 9, 10, 11, 12, 13, 15, 19, 24, 28] → reg n3 q = reg nn q := fun q hq => by
        rw [K3 q (by revert hq; revert q; decide), K12 q (by revert hq; revert q; decide)]
      have hbl : bs.length = 3 - pad := by rw [hbs, memBytes_length]
      obtain ⟨_, hcWs, hcSs, hcBs⟩ := bdi_codes env.hc env.hcW env.hcS env.hcB hiMs
      obtain ⟨CE, CO⟩ := bdi_copy hcMs hcWs hcSs hcBs u3 (keep := 3 - pad) (w := P.length) (by omega) hw hFr hFa hF4
        env.hdw env.sOF a13 (by rw [K123 a6 (by decide), r16]) (by rw [K123 a4 (by decide), r14])
        (by rw [K123 23 (by decide), r23]) (by rw [K123 6 (by decide), r6]) (by rw [K123 sp (by decide), rsp])
      have hsp2 : base64Decode (memBytes m.mem t n) = (base64Decode rest').map ((P ++ bs) ++ ·) := by
        rw [hspec, hf, hsb, hb]
        show Option.map (P ++ ·) (Option.map (bs ++ ·) (base64Decode rest')) = _
        cases base64Decode rest' <;> simp only [Option.map, List.append_assoc]
      by_cases hL : L < P.length + (3 - pad)
      · obtain ⟨n4, c4, u4, K4⟩ := CE hL
        obtain ⟨n5, Mt, c5, u5, hc5, h1, hf5, K5⟩ :=
          bdi_ex19C hcMs u4 (by rw [K4 18 (by decide), K123 18 (by decide), r18]) env.sRC
        refine Or.inl (mkErr (c1.trans (c2.trans (c3.trans (c4.trans c5)))) u5 hc5 h1
          (fun x hx hx' => by rw [hf5 x hx', hMsF x hx])
          (by rw [K5 sp (by decide), K4 sp (by decide), K123 sp (by decide)])
          (by rw [K5 3 (by decide), K4 3 (by decide), K123 3 (by decide)])
          (by rw [K5 4 (by decide), K4 4 (by decide), K123 4 (by decide)]) fun bs' h => ?_)
        rw [hsp2] at h
        cases hr : base64Decode rest' with
        | none => rw [hr] at h; have h' : (none : Option Bytes) = some bs' := h; cases h'
        | some r =>
          rw [hr] at h
          have h' : some (P ++ bs ++ r) = some bs' := h
          cases h'
          rw [List.length_append, List.length_append, hbl]; omega
      obtain ⟨n4, c4, st4, hi4, fr4, by4, sp4, a14, a64, r304, K4⟩ := CO (by omega)
      have KK : ∀ q, q.val ∈ [3, 4, 6, 14, 17, 18, 20, 21, 22, 23, 25, 26] → reg n4 q = reg nn q := fun q hq => by
        rw [K4 q (by revert hq; revert q; decide), K123 q (by revert hq; revert q; decide)]
      have v324 : reg n3 24 = t + BitVec.ofNat 32 (4 * (i + 1)) := by
        rw [K3 24 (by decide), K2 24 (by decide), r241, ← hg, show (4 : Word) = BitVec.ofNat 32 4 from rfl,
          add_ofNat_assoc, show 4 * i + 4 = 4 * (i + 1) by omega]
      have v24 : reg n4 24 = t + BitVec.ofNat 32 (4 * (i + 1)) := by rw [K4 24 (by decide), v324]
      have v19 : reg n4 19 = BitVec.ofNat 32 (i + 1) := by
        rw [K4 19 (by decide), K3 19 (by decide), K2 19 (by decide), r191]; exact BitVec.ofNat_add_ofNat ..
      have v22 : reg n4 22 = t + BitVec.ofNat 32 n := by rw [KK 22 (by decide), r22]
      have heq : t + BitVec.ofNat 32 (4 * (i + 1)) = t + BitVec.ofNat 32 n ↔ i + 1 = G := by
        constructor
        · intro e
          exact Decidable.byContradiction fun hne =>
            add_ofNat_ne t (c := 4 * (i + 1)) (d := n) (by omega) (by omega) (by omega) e
        · intro e; rw [show 4 * (i + 1) = n by omega]
      have hi4' : ∀ x : Word, 0x40000000 ≤ x.toNat → n4.mem x = m.mem x := fun x hx => by rw [hi4 x hx, hiMs x hx]
      have hcm4 : CodeIn n4.mem BDI base64DecodeIntoCode := (bdi_codes env.hc env.hcW env.hcS env.hcB hi4').1
      have mkInv : ∀ {n5 : Machine} {off : Nat}, Steps nn n5 → St n4.mem BDI n5 off (reg n4) →
          BdiInv m Ms0 res t out F n L G (i + 1) (P ++ bs) off n5 := fun {n5} {off} _ u5 => by
        have mem5 : n5.mem = n4.mem := u5.mem
        refine ⟨⟨u5.pc, rfl, fun _ => rfl⟩, fun x hx1 hx2 => ?_, ?_, by rw [List.length_append, hbl]; omega, ?_,
          by rw [u5.regs, sp4], by rw [u5.regs, a14, v324], by rw [u5.regs, v19],
          by rw [u5.regs, a64, List.length_append, hbl], fun _ => by rw [u5.regs, KK 17 (by decide), r17 (by omega)],
          by rw [u5.regs, v22], by rw [u5.regs, KK 6 (by decide), r6], fun _ => by rw [u5.regs, KK 26 (by decide), r26 (by omega)],
          by rw [u5.regs, KK 25 (by decide), r25], by rw [u5.regs, KK 21 (by decide), r21],
          by rw [u5.regs, KK 20 (by decide), r20], by rw [u5.regs, r304], by rw [u5.regs, KK 18 (by decide), r18],
          by rw [u5.regs, KK 23 (by decide), r23], by rw [u5.regs, KK 14 (by decide), r14],
          by rw [u5.regs, KK 3 (by decide), r3], by rw [u5.regs, KK 4 (by decide), r4]⟩
        · have h18 : Sep (F + 0xFFFFFFF0) 0x18 x 1 := by
            have := hx2.sub (c := 0) (l := 0x18) (by decide); rwa [add_ofNat_zero] at this
          rw [mem5, fr4 x h18 (hx1.sub (c := P.length) (l := 3 - pad) (by omega))]
          rw [hR] at hx2; rw [hMsF x hx2, frame x hx1 hx2]
        · rw [mem5, List.length_append, memBytes_split, hbl]
          congr 1
          · refine (memBytes_congr fun j hj => ?_).trans outb
            have h1 : Sep (F + 0xFFFFFFF0) 0x18 (out + BitVec.ofNat 32 j) 1 := by
              have := (env.sOF.sub (c := j) (l := 1) (by omega)).symm.sub (c := 0) (l := 0x18) (by decide)
              rwa [add_ofNat_zero] at this
            have h2 : Sep (out + BitVec.ofNat 32 P.length) (3 - pad) (out + BitVec.ofNat 32 j) 1 :=
              sep_offsets out (Or.inr (by omega)) (by omega) (by omega)
            rw [fr4 _ h1 h2, hMsF _ (sub1C (sOF.sub (c := j) (l := 1) (by omega)).symm)]
          · rw [hbs]; unfold memBytes; apply List.map_congr_left; intro j hj
            rw [List.mem_range] at hj; rw [by4 j hj]
        · rw [hsp2, hr']
      by_cases hlast : i + 1 = G
      · obtain ⟨n5, d5, u5⟩ := st4.notTaken hcm4 0x164 bdi_at_160 (by decide) (by
          rw [v24, v22, (heq.mpr hlast)]; exact bne_self_eq_false _)
        refine Or.inr ⟨bs, n5, c1.trans (c2.trans (c3.trans (c4.trans (.single d5)))), ?_⟩
        rw [if_pos hlast]; exact mkInv (c1.trans (c2.trans (c3.trans (c4.trans (.single d5))))) u5
      · obtain ⟨n5, d5, u5⟩ := st4.taken hcm4 0x5A bdi_at_160 (by decide) (by
          rw [v24, v22]; exact bne_iff_ne.mpr (fun e => hlast (heq.mp e)))
        refine Or.inr ⟨bs, n5, c1.trans (c2.trans (c3.trans (c4.trans (.single d5)))), ?_⟩
        rw [if_neg hlast]; exact mkInv (c1.trans (c2.trans (c3.trans (c4.trans (.single d5))))) u5

/-- Every group from the `i`th: an error exit, or the state after the last
group. -/
theorem bdi_loop {m : Machine} {Ms0 : Word → BitVec 8} {res t out F : Word} {n L G : Nat}
    (env : BdiEnv m Ms0 res t out F n L G) (hn : n = 4 * G) :
    ∀ k i P nn, G - i = k → i < G → BdiInv m Ms0 res t out F n L G i P 0x5A nn →
      (∃ nn' Mt, BdiErr m Ms0 res out F L nn nn' Mt ∧
        ∀ bs, base64Decode (memBytes m.mem t n) = some bs → L < bs.length) ∨
      (∃ P' nn', Steps nn nn' ∧ BdiInv m Ms0 res t out F n L G G P' 0x164 nn')
  | 0, i, _, _, hk, hi, _ => absurd hk (by omega)
  | k + 1, i, P, nn, hk, hi, I => by
    rcases bdi_group env hn I hi with hE | ⟨g, nn1, c1, I1⟩
    · exact Or.inl hE
    by_cases hl : i + 1 = G
    · rw [if_pos hl] at I1
      rw [hl] at I1
      exact Or.inr ⟨P ++ g, nn1, c1, I1⟩
    · rw [if_neg hl] at I1
      rcases bdi_loop env hn k (i + 1) (P ++ g) nn1 (by omega) (by omega) I1 with
        ⟨nn', Mt, ⟨c2, rest⟩, hs⟩ | ⟨P', nn', c2, I2⟩
      · exact Or.inl ⟨nn', Mt, ⟨c1.trans c2, rest⟩, hs⟩
      · exact Or.inr ⟨P', nn', c1.trans c2, I2⟩

/-- What `decode_into` leaves when it returns: the callee-saved registers,
`Ok(len)` with the bytes in `out` when the text decodes to at most `L` bytes,
`Err` when no decoding fits, and memory outside the stack frame, `out`, and
`res` untouched. -/
def BdiResult (m : Machine) (sp0 res t out retAddr : Word) (n L : Nat) (m' : Machine) : Prop :=
  m'.pc = retAddr ∧ reg m' sp = sp0 ∧
    (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
    (∀ bs, base64Decode (memBytes m.mem t n) = some bs → bs.length ≤ L →
      m'.mem res = 0 ∧ memLoad32 m'.mem (res + 4) = BitVec.ofNat 32 bs.length ∧ memBytes m'.mem out bs.length = bs) ∧
    ((∀ bs, base64Decode (memBytes m.mem t n) = some bs → L < bs.length) → m'.mem res = 1) ∧
    ∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → Sep out L x 1 → Sep res 8 x 1 → m'.mem x = m.mem x

theorem bdi_slots {m : Machine} {Ms0 Mt : Word → BitVec 8} {res t out F : Word} {n L G : Nat}
    (env : BdiEnv m Ms0 res t out F n L G) (sRG : Sep res 8 (F + 0xFFFFFFF0) 0x50)
    (slots : ∀ r o, (r, o) ∈ bdiPs → memLoad32 Ms0 (F + o) = reg m r)
    (fr : ∀ x, Sep out L x 1 → Sep (F + 0xFFFFFFF0) 0x1C x 1 → Sep res 8 x 1 → Mt x = Ms0 x) :
    ∀ r o, (r, o) ∈ bdiPs → memLoad32 Mt (F + o) = reg m r := fun r o hm => by
  obtain ⟨R, hR⟩ : ∃ R, F + 0xFFFFFFF0 = R := ⟨_, rfl⟩
  have eF : F = R + BitVec.ofNat 32 0x10 := by rw [← hR, BitVec.add_assoc]; exact (BitVec.add_zero F).symm
  have ho : 0xC ≤ o.toNat ∧ o.toNat ≤ 0x3C := by
    simp only [bdiPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, by decide⟩
  rw [← slots r o hm]
  apply memLoad32_congr; intro j hj
  have e : F + o + BitVec.ofNat 32 j = R + BitVec.ofNat 32 (0x10 + o.toNat + j) := by
    rw [eF, add_ofNat_assoc', add_ofNat_assoc, ← Nat.add_assoc]
  rw [hR] at sRG fr
  have sOF := env.sOF
  rw [hR] at sOF
  rw [e]
  exact fr _ (sOF.subR (c := 0x10 + o.toNat + j) (l := 1) (by omega))
    (by have := sep_offsets R (c := 0) (n := 0x1C) (d := 0x10 + o.toNat + j) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega); rwa [add_ofNat_zero] at this)
    (sRG.subR (c := 0x10 + o.toNat + j) (l := 1) (by omega))

theorem bdi_ps_mem : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
    q.val ∈ [3, 4] ∨ ∃ o, (q, o) ∈ bdiPs := by
  intro q hq
  rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
      q.val ∈ [3, 4] ∨ q = ra ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨ q = 24 ∨
        q = 25 ∨ q = 26 ∨ q = 27) q hq with h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl h
  · exact Or.inr ⟨0x3C, by decide⟩
  · exact Or.inr ⟨0x38, by decide⟩
  · exact Or.inr ⟨0x34, by decide⟩
  · exact Or.inr ⟨0x30, by decide⟩
  · exact Or.inr ⟨0x2C, by decide⟩
  · exact Or.inr ⟨0x28, by decide⟩
  · exact Or.inr ⟨0x24, by decide⟩
  · exact Or.inr ⟨0x20, by decide⟩
  · exact Or.inr ⟨0x1C, by decide⟩
  · exact Or.inr ⟨0x18, by decide⟩
  · exact Or.inr ⟨0x14, by decide⟩
  · exact Or.inr ⟨0x10, by decide⟩
  · exact Or.inr ⟨0xC, by decide⟩

set_option maxRecDepth 20000 in
theorem bdi_fin_err {m : Machine} {Ms0 : Word → BitVec 8} {res t out F : Word} {n L G : Nat}
    (env : BdiEnv m Ms0 res t out F n L G) {sp0 retAddr : Word} (hFS : F + 0x40 = sp0)
    (hRS : F + 0xFFFFFFF0 = sp0 + 0xFFFFFFB0) (sRG : Sep res 8 (F + 0xFFFFFFF0) 0x50)
    (slots : ∀ r o, (r, o) ∈ bdiPs → memLoad32 Ms0 (F + o) = reg m r) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) {nn nn' : Machine} {Mt : Word → BitVec 8}
    (E : BdiErr m Ms0 res out F L nn nn' Mt) (hs : ∀ bs, base64Decode (memBytes m.mem t n) = some bs → L < bs.length) :
    ∃ m', Steps nn m' ∧ BdiResult m sp0 res t out retAddr n L m' := by
  obtain ⟨c, u, hc', h1, fr, sp', r3', r4'⟩ := E
  obtain ⟨n2, c2, pc2, sp2, mem2, Ks, K34⟩ := bdi_epi hc' u sp' env.hFa (bdi_slots env sRG slots fr)
    (by rw [hra, hret])
  refine ⟨n2, c.trans c2, by rw [pc2, hra], by rw [sp2, hFS], fun q hq => ?_,
    fun bs h hl => absurd (hs bs h) (by omega), fun _ => by rw [mem2, h1], fun x hx hx1 hx2 => ?_⟩
  · rcases bdi_ps_mem q hq with h34 | ⟨o, ho⟩
    · rw [K34 q h34]
      rcases (by decide : ∀ q : Fin 32, q.val ∈ [3, 4] → q = 3 ∨ q = 4) q h34 with rfl | rfl
      · exact r3'
      · exact r4'
    · exact Ks q o ho
  · rw [← hRS] at hx
    rw [mem2, fr x hx1 (by have := hx.sub (c := 0) (l := 0x1C) (by decide); rwa [add_ofNat_zero] at this) hx2,
      env.hMs0 x hx]

set_option maxRecDepth 20000 in
theorem bdi_fin_ok {m : Machine} {Ms0 : Word → BitVec 8} {res t out F : Word} {n L G : Nat}
    (env : BdiEnv m Ms0 res t out F n L G) (hn : n = 4 * G) {sp0 retAddr : Word} (hFS : F + 0x40 = sp0)
    (hRS : F + 0xFFFFFFF0 = sp0 + 0xFFFFFFB0) (sRG : Sep res 8 (F + 0xFFFFFFF0) 0x50) (sRO : Sep res 8 out L)
    (slots : ∀ r o, (r, o) ∈ bdiPs → memLoad32 Ms0 (F + o) = reg m r) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) {P : Bytes} {nn : Machine}
    (I : BdiInv m Ms0 res t out F n L G G P 0x164 nn) :
    ∃ m', Steps nn m' ∧ BdiResult m sp0 res t out retAddr n L m' := by
  obtain ⟨st, frame, outb, hw, spec, rsp, -, -, r16, -, -, -, -, -, -, -, -, r18, -, -, r3, r4⟩ := I
  have hiM := bdi_hi env frame
  have hc := (bdi_codes env.hc env.hcW env.hcS env.hcB hiM).1
  obtain ⟨n1, Mt, ⟨c1, u1, hc1, h0, hf1, K1⟩, hcnt⟩ := bdi_ex164 hc st r18 env.sRC env.hra
  have fr : ∀ x, Sep out L x 1 → Sep (F + 0xFFFFFFF0) 0x1C x 1 → Sep res 8 x 1 → Mt x = Ms0 x :=
    fun x h1 h2 h3 => by rw [hf1 x h3, frame x h1 h2]
  obtain ⟨n2, c2, pc2, sp2, mem2, Ks, K34⟩ := bdi_epi hc1 u1 (by rw [K1 sp (by decide), rsp]) env.hFa
    (bdi_slots env sRG slots fr) (by rw [hra, hret])
  have hsp : base64Decode (memBytes m.mem t n) = some P := by
    rw [spec, show n - 4 * G = 0 by omega, memBytes_zero]
    simp only [base64Decode, Option.map, List.append_nil]
  refine ⟨n2, c1.trans c2, by rw [pc2, hra], by rw [sp2, hFS], fun q hq => ?_, fun bs h _ => ?_,
    fun h => absurd (h P hsp) (by omega), fun x hx hx1 hx2 => ?_⟩
  · rcases bdi_ps_mem q hq with h34 | ⟨o, ho⟩
    · rw [K34 q h34]
      rcases (by decide : ∀ q : Fin 32, q.val ∈ [3, 4] → q = 3 ∨ q = 4) q h34 with rfl | rfl
      · rw [K1 3 (by decide), r3]
      · rw [K1 4 (by decide), r4]
    · exact Ks q o ho
  · rw [hsp] at h; cases h
    refine ⟨by rw [mem2, h0], by rw [mem2, hcnt, r16], ?_⟩
    rw [mem2]; refine (memBytes_congr fun j hj => ?_).trans outb
    exact hf1 _ (sRO.subR (c := j) (l := 1) (by omega))
  · rw [← hRS] at hx
    rw [mem2, fr x hx1 (by have := hx.sub (c := 0) (l := 0x1C) (by decide); rwa [add_ofNat_zero] at this) hx2,
      env.hMs0 x hx]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `base64::decode_into` is correct.** Called with `res` in
`a0`, the `n` bytes of text at `t`, and the `L`-byte buffer at `out`, it
returns `Ok(len)` with the decoded bytes at `out` when `base64Decode` accepts
the text and its bytes fit in `L`, and `Err` when no decoding fits. -/
theorem base64DecodeInto_correct (m : Machine) {sp0 res t out retAddr : Word} {n L : Nat}
    (hc : CodeIn m.mem BDI base64DecodeIntoCode) (hcW : CodeIn m.mem BCW copyFromSliceU8Code)
    (hcS : CodeIn m.mem BMS memcpyStubCode) (hcB : CodeIn m.mem BMB memcpyBodyCode)
    (hpc : m.pc = BDI) (ha0 : reg m a0 = res) (ha1 : reg m a1 = t) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (ha3 : reg m a3 = out) (ha4 : reg m a4 = BitVec.ofNat 32 L) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0) (hsl : 0x50 ≤ sp0.toNat)
    (hsw : sp0.toNat ≤ 0x40000000) (hres : res.toNat + 8 ≤ 0x40000000) (hra4 : res.toNat % 4 = 0)
    (hdw : out.toNat + L ≤ 0x40000000) (htw : t.toNat + n ≤ 0x40000000)
    (sOG : Sep out L (sp0 + 0xFFFFFFB0) 0x50) (sTG : Sep t n (sp0 + 0xFFFFFFB0) 0x50)
    (sRG : Sep res 8 (sp0 + 0xFFFFFFB0) 0x50) (sTO : Sep t n out L) (sRO : Sep res 8 out L) :
    ∃ m', Steps m m' ∧ BdiResult m sp0 res t out retAddr n L m' := by
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFC0 = F := ⟨_, rfl⟩
  have hFn : F.toNat = sp0.toNat - 0x40 := by
    rw [← hF, BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 2 ^ 32 - 0x40 from rfl]; omega
  have hRS : F + 0xFFFFFFF0 = sp0 + 0xFFFFFFB0 := by rw [← hF, BitVec.add_assoc]; rfl
  have hFS : F + 0x40 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  rw [← hRS] at sOG sTG sRG
  have hFa : F.toNat % 4 = 0 := by omega
  have hBn : BDI.toNat = (img% base64DecodeIntoAddress) := by decide
  have hBl : base64DecodeIntoCode.length = 0x1A0 := by decide
  have hps : ∀ p ∈ bdiPs, p.2.toNat ≤ 0x3C ∧ p.2.toNat % 4 = 0 ∧ 0xC ≤ p.2.toNat := by decide
  have hps0 : ∀ p ∈ bdiPs, p.1 ≠ sp ∧ p.1.val ≠ 0 := by decide
  have hdis : ∀ q ∈ bdiPs, ∀ p ∈ bdiPs, p = q ∨ ((p.2.toNat + 4 ≤ q.2.toNat ∨ q.2.toNat + 4 ≤ p.2.toNat) ∧
      p.2.toNat + 4 ≤ 2 ^ 32 ∧ q.2.toNat + 4 ≤ 2 ^ 32) := by decide
  have eFo : ∀ o : Word, o.toNat ≤ 0x3C → (F + o).toNat = F.toNat + o.toNat := fun o ho => by
    rw [BitVec.toNat_add]; omega
  have slotR : ∀ o : Word, F + o = (F + 0xFFFFFFF0) + BitVec.ofNat 32 (0x10 + o.toNat) := fun o => by
    have e : (0xFFFFFFF0 : Word) + BitVec.ofNat 32 (0x10 + o.toNat) = o := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]
      have := o.isLt; omega
    rw [BitVec.add_assoc, e]
  -- prologue
  have st0 : St m.mem BDI m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc bdi_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0) sp = F := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp, ← hF]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock bdiPs) u1 hc bdiSave_end (saveBlock_ok _ bdiPs _ fun q hq => by
    rw [sp1]
    obtain ⟨h1, h2, _⟩ := hps q hq
    exact ⟨by rw [eFo _ h1]; omega, sep_of_le (by rw [eFo _ h1, hBn]; omega) (by rw [hBn, hBl]; decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms0, hMs0⟩ : ∃ Ms0, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0)) bdiPs = Ms0 :=
    ⟨_, rfl⟩
  rw [hMs0] at u2
  have IMs : ∀ x, Sep (F + 0xFFFFFFF0) 0x50 x 1 → Ms0 x = m.mem x := fun x hx => by
    rw [← hMs0]; exact saveMem_outside bdiPs fun q hq => by
      rw [slotR]; exact (hx.symm.subR (c := 0x10 + q.2.toNat) (l := 4) (by have := (hps q hq).1; omega)).symm
  have slots : ∀ r o, (r, o) ∈ bdiPs → memLoad32 Ms0 (F + o) = reg m r := fun r o hm => by
    rw [← hMs0, saveMem_slot bdiPs _ hm (hdis _ hm), upd_ne (hps0 _ hm).2 (hps0 _ hm).1]
  have hR16 : (F + 0xFFFFFFF0).toNat = F.toNat - 16 := by
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega
  have hiMs : ∀ x : Word, 0x40000000 ≤ x.toNat → Ms0 x = m.mem x := fun x hx =>
    IMs x (sep_of_le (by rw [hR16]; omega) (by have := x.isLt; omega))
  obtain ⟨hc2, -, -, -⟩ := bdi_codes hc hcW hcS hcB hiMs
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have z2 := u2.self.zero
  have env : ∀ G, BdiEnv m Ms0 res t out F n L G := fun G =>
    { hc := hc, hcW := hcW, hcS := hcS, hcB := hcB, hMs0 := IMs, hFr := by omega, hFa := hFa,
      hF4 := by omega, hdw := hdw, htw := htw, sOF := sOG, sTO := sTO, sTF := sTG,
      sRC := sep_of_le (by rw [hBn]; omega) (by rw [hBn, hBl]; decide), hra := hra4 }
  -- the length check, 0x1C to 0x24
  obtain ⟨m3, d3, u3⟩ := u2.self.alu hc2 bdi_at_1c (off' := 0x1E) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.self.aluImm hc2 bdi_at_1e (off' := 0x22) (by decide)
  obtain ⟨m5, d5, u5⟩ := u4.self.alu hc2 bdi_at_22 (off' := 0x24) (by decide)
  have K5 : ∀ q, q.val ∉ [13, 18, 23] → reg m5 q = reg m2 q := fun q hq => by
    rw [u5.regs, upd_ne' (by intro e; apply hq; rw [e]; decide) u4.self.zero, u4.regs,
      upd_ne' (by intro e; apply hq; rw [e]; decide) u3.self.zero, u3.regs,
      upd_ne' (by intro e; apply hq; rw [e]; decide) z2]
  have v18 : reg m5 18 = res := by
    rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]
    all_goals (try rw [u4.self.zero]); all_goals (try rw [dn_z])
    rw [u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs, upd_ne' (by decide) z2, r2 a0 (by decide), ha0]
  have v23 : reg m5 23 = out := by
    rw [u5.regs, upd_ne' (by decide) u4.self.zero, u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs]
    simp +decide only [upd_app, ↓reduceIte]
    all_goals (try rw [z2]); all_goals (try rw [dn_z])
    rw [r2 a3 (by decide), ha3]
  have hn30 : n < 2 ^ 30 + 1 := by omega
  have v13 : reg m5 a3 = BitVec.ofNat 32 (n % 4) := by
    rw [u5.regs, upd_ne' (by decide) u4.self.zero, u4.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u3.regs, upd_ne' (by decide) z2, r2 a2 (by decide), ha2]
    apply BitVec.eq_of_toNat_eq
    rw [show aluEval .and (BitVec.ofNat 32 n) 3 = BitVec.ofNat 32 n &&& 3 from rfl,
      and_low (k := 2) (by decide) (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have pre5 : Steps m m5 := .cons d1 (c2.trans (.cons d3 (.cons d4 (.single d5))))
  have K5m : ∀ q, q.val ∉ [2, 13, 18, 23] → reg m5 q = reg m q := fun q hq => by
    rw [K5 q (by revert hq; revert q; decide), r2 q (by intro e; apply hq; rw [e]; decide)]
  by_cases h4 : n % 4 = 0
  rotate_left
  · obtain ⟨m6, d6, u6⟩ := u5.self.notTaken hc2 0x26 bdi_at_24 (by decide) (by
      rw [v13, u5.self.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
      intro e; apply h4; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this)
    obtain ⟨n7, Mt, c7, u7, hc7, h1, hf7, K7⟩ := bdi_ex26 hc2 u6.self (by rw [u6.regs, v18]) (env 0).sRC hra4
    have hnone : base64Decode (memBytes m.mem t n) = none := b64_len _ (by rw [memBytes_length]; exact h4)
    exact bdi_fin_err (env 0) hFS hRS sRG slots hra hret
      ⟨pre5.trans (.cons d6 c7), u7, hc7, h1, fun x _ _ hx => hf7 x hx,
        by rw [K7 sp (by decide), u6.regs, K5 sp (by decide), sp2],
        by rw [K7 3 (by decide), u6.regs, K5m 3 (by decide)], by rw [K7 4 (by decide), u6.regs, K5m 4 (by decide)]⟩
      fun bs h => by rw [hnone] at h; cases h
  obtain ⟨G, hG⟩ : ∃ G, n = 4 * G := ⟨n / 4, by omega⟩
  obtain ⟨m6, d6, u6⟩ := u5.self.taken hc2 0x32 bdi_at_24 (by decide) (by rw [v13, u5.self.zero, h4]; rfl)
  obtain ⟨m7, c7, u7⟩ := St.block bdiI u6.self hc2 bdiI_end (by simp only [BlockOk, BInstr.ok, bdiI, and_self])
  have R7 : ∀ q, reg m7 q = (runBlock bdiI (Ms0, reg m6)).2 q := u7.regs
  have u7' : St Ms0 BDI m7 0x56 (reg m7) := ⟨u7.pc, by rw [u7.mem]; rfl, fun _ => rfl⟩
  have z6 := u6.self.zero
  have K7 : ∀ q, q.val ∉ [19, 16, 10, 17, 22, 6, 26, 21, 25, 20, 30] → reg m7 q = reg m5 q := fun q hq => by
    have hd : q ∉ bdiI.filterMap BInstr.dst := by
      simp only [bdiI, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R7, runBlock_reg _ _ _ q z6 hd, u6.regs]
  have K7m : ∀ q, q.val ∈ [3, 4, 11, 14] → reg m7 q = reg m q := fun q hq => by
    rw [K7 q (by revert hq; revert q; decide), K5m q (by revert hq; revert q; decide)]
  have e6 : ∀ q, reg m6 q = reg m5 q := u6.regs
  have vI : ∀ q v, (q, v) ∈ [((19 : Fin 32), BitVec.ofNat 32 0), (16, BitVec.ofNat 32 0), (21, BitVec.ofNat 32 4),
      (25, 0xFF00), (20, BitVec.ofNat 32 26), (30, BitVec.ofNat 32 10), (22, t + BitVec.ofNat 32 n), (6, F + 9)] →
      reg m7 q = v := by
    intro q v hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;> (rw [R7]; simp +decide only [runBlock, BInstr.run, bdiI, upd_app, ↓reduceIte]) <;>
      (try simp only [e6, u5.self.zero]) <;>
      first | rfl | (rw [K5m a1 (by decide), K5m a2 (by decide), ha1, ha2]; rfl) | (rw [K5 sp (by decide), sp2]; rfl)
  have v17 : 0 < G → reg m7 17 = BitVec.ofNat 32 (G - 1) := fun hG0 => by
    rw [R7]; simp +decide only [runBlock, BInstr.run, bdiI, upd_app, ↓reduceIte]
    rw [e6, K5m a2 (by decide), ha2]
    apply BitVec.eq_of_toNat_eq
    rw [dn_add, dn_srl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl,
      show (0x2 : Word).toNat % 32 = 2 from rfl, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)]
    omega
  have v26 : 0 < G → reg m7 26 = 1 := fun hG0 => by
    rw [R7]; simp +decide only [runBlock, BInstr.run, bdiI, upd_app, ↓reduceIte]
    rw [e6, K5m a2 (by decide), ha2]
    apply BitVec.eq_of_toNat_eq
    rw [dn_sltu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), if_pos (by
      show (0 : Word).toNat < n; exact Nat.lt_of_lt_of_le (by decide : 0 < 4) (by omega))]
    rfl
  have mkI : ∀ {nn : Machine} {off : Nat}, St Ms0 BDI nn off (reg m7) →
      BdiInv m Ms0 res t out F n L G 0 [] off nn := fun {nn} {off} u => by
    have mem' : nn.mem = Ms0 := u.mem
    refine ⟨⟨u.pc, rfl, fun _ => rfl⟩, fun x _ _ => by rw [mem'], rfl, Nat.zero_le _, ?_,
      by rw [u.regs, K7 sp (by decide), K5 sp (by decide), sp2],
      by rw [u.regs, K7m a1 (by decide), ha1]; exact (add_ofNat_zero t).symm,
      by rw [u.regs]; exact vI 19 (BitVec.ofNat 32 0) (by simp only [List.mem_cons, true_or, or_true]),
      by rw [u.regs]; exact vI 16 (BitVec.ofNat 32 0) (by simp only [List.mem_cons, true_or, or_true]),
      fun h => by rw [u.regs]; exact v17 h,
      by rw [u.regs]; exact vI 22 (t + BitVec.ofNat 32 n) (by simp only [List.mem_cons, true_or, or_true]),
      by rw [u.regs]; exact vI 6 (F + 9) (by simp only [List.mem_cons, true_or, or_true]),
      fun h => by rw [u.regs]; exact v26 h,
      by rw [u.regs]; exact vI 25 0xFF00 (by simp only [List.mem_cons, true_or, or_true]),
      by rw [u.regs]; exact vI 21 (BitVec.ofNat 32 4) (by simp only [List.mem_cons, true_or, or_true]),
      by rw [u.regs]; exact vI 20 (BitVec.ofNat 32 26) (by simp only [List.mem_cons, true_or, or_true]),
      by rw [u.regs]; exact vI 30 (BitVec.ofNat 32 10) (by simp only [List.mem_cons, true_or, or_true]),
      by rw [u.regs, K7 18 (by decide), v18], by rw [u.regs, K7 23 (by decide), v23],
      by rw [u.regs, K7m a4 (by decide), ha4], by rw [u.regs, K7m 3 (by decide)], by rw [u.regs, K7m 4 (by decide)]⟩
    rw [show 4 * 0 = 0 from rfl, add_ofNat_zero, Nat.sub_zero]
    cases base64Decode (memBytes m.mem t n) <;> rfl
  have pre7 : Steps m m7 := pre5.trans (.cons d6 c7)
  have hcmp : (reg m7 a1 == reg m7 22) = decide (n = 0) := by
    rw [K7m a1 (by decide), ha1, vI 22 (t + BitVec.ofNat 32 n) (by simp only [List.mem_cons, true_or, or_true])]
    by_cases hn0 : n = 0
    · rw [hn0, add_ofNat_zero, decide_eq_true rfl]; exact beq_iff_eq.mpr rfl
    · rw [decide_eq_false hn0]
      apply beq_eq_false_iff_ne.mpr
      have := add_ofNat_ne t (c := 0) (d := n) (by decide) (by omega) (Ne.symm hn0)
      rwa [add_ofNat_zero] at this
  by_cases hn0 : n = 0
  · obtain ⟨m8, d8, u8⟩ := u7'.taken hc2 0x164 bdi_at_56 (by decide) (by
      show (reg m7 a1 == reg m7 22) = true; rw [hcmp]; exact decide_eq_true hn0)
    have hG0 : G = 0 := by omega
    obtain ⟨m', c', R'⟩ := bdi_fin_ok (env G) hG hFS hRS sRG sRO slots hra hret (P := [])
      (by have := mkI u8; rwa [hG0] at this ⊢)
    exact ⟨m', pre7.trans (.cons d8 c'), R'⟩
  · obtain ⟨m8, d8, u8⟩ := u7'.notTaken hc2 0x5A bdi_at_56 (by decide) (by
      show (reg m7 a1 == reg m7 22) = false; rw [hcmp]; exact decide_eq_false hn0)
    rcases bdi_loop (env G) hG G 0 [] m8 (by omega) (by omega) (mkI u8) with ⟨nn', Mt, E, hs⟩ | ⟨P', nn', c9, I9⟩
    · obtain ⟨m', c', R'⟩ := bdi_fin_err (env G) hFS hRS sRG slots hra hret E hs
      exact ⟨m', pre7.trans (.cons d8 c'), R'⟩
    · obtain ⟨m', c', R'⟩ := bdi_fin_ok (env G) hG hFS hRS sRG sRO slots hra hret I9
      exact ⟨m', pre7.trans (.cons d8 (c9.trans c')), R'⟩

end C3.RV32
