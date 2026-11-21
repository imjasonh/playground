import C3BootProofs.Proofs.P384Double
import C3BootProofs.Proofs.UintSelect2

/-!
# `safegcd`'s `conditional_negate_in_place_wide::<12, 2>`, as compiled

`crypto_bigint`'s Bernstein-Yang inversion keeps a 448-bit signed value as a
12-limb low part `lo` and a 2-limb high part `hi`. This function negates it
in two's complement when `flag` is set: `lo.carrying_neg()` gives `-lo` and a
carry that is 1 when `lo` is 0, `hi` becomes `!hi` plus that carry, and two
constant-time selects keep the old or the negated parts. The compiled code
negates `lo` limb by limb into a zeroed buffer, inverts `hi` in a loop, turns
the carry into a `Uint<2>` with `Uint<2>::select`, adds it in a loop, and
then calls `Uint<12>::select` and `Uint<2>::select`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem cn_at_0 : fetchRel condNeg12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF70, 2) := by decide
theorem cn_at_2 : fetchRel condNeg12Code 0x2 = some (.store .sw sp ra 0x8C, 2) := by decide
theorem cn_at_4 : fetchRel condNeg12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x88, 2) := by decide
theorem cn_at_6 : fetchRel condNeg12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x84, 2) := by decide
theorem cn_at_8 : fetchRel condNeg12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x80, 2) := by decide
theorem cn_at_a : fetchRel condNeg12Code 0xA = some (.store .sw sp (19 : Fin 32) 0x7C, 2) := by decide
theorem cn_at_c : fetchRel condNeg12Code 0xC = some (.store .sw sp (20 : Fin 32) 0x78, 2) := by decide
theorem cn_at_e : fetchRel condNeg12Code 0xE = some (.alu .add (18 : Fin 32) x0 a2, 2) := by decide
theorem cn_at_10 : fetchRel condNeg12Code 0x10 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem cn_at_12 : fetchRel condNeg12Code 0x12 = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem cn_at_14 : fetchRel condNeg12Code 0x14 = some (.aluImm .add a0 sp 0x48, 2) := by decide
theorem cn_at_16 : fetchRel condNeg12Code 0x16 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem cn_at_1a : fetchRel condNeg12Code 0x1A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem cn_at_1c : fetchRel condNeg12Code 0x1C = some (.aluImm .add (8 : Fin 32) sp 0x48, 2) := by decide
theorem cn_at_1e : fetchRel condNeg12Code 0x1E = some (.auipc ra 0x1000, 4) := by decide
theorem cn_at_22 : fetchRel condNeg12Code 0x22 = some (.jalr ra ra 0x408, 4) := by decide
theorem cn_at_26 : fetchRel condNeg12Code 0x26 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem cn_at_28 : fetchRel condNeg12Code 0x28 = some (.aluImm .add (9 : Fin 32) x0 0x1, 2) := by decide
theorem cn_at_2a : fetchRel condNeg12Code 0x2A = some (.aluImm .add a0 x0 0xC, 2) := by decide
theorem cn_at_2c : fetchRel condNeg12Code 0x2C = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem cn_at_2e : fetchRel condNeg12Code 0x2E = some (.branch .beq a0 x0 0x1C, 2) := by decide
theorem cn_at_30 : fetchRel condNeg12Code 0x30 = some (.load .lw a3 a1 0x0, 2) := by decide
theorem cn_at_32 : fetchRel condNeg12Code 0x32 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem cn_at_34 : fetchRel condNeg12Code 0x34 = some (.aluImm .xor a3 a3 0xFFFFFFFF, 4) := by decide
theorem cn_at_38 : fetchRel condNeg12Code 0x38 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem cn_at_3a : fetchRel condNeg12Code 0x3A = some (.alu .sltu (9 : Fin 32) a3 (9 : Fin 32), 4) := by decide
theorem cn_at_3e : fetchRel condNeg12Code 0x3E = some (.store .sw (8 : Fin 32) a3 0x0, 2) := by decide
theorem cn_at_40 : fetchRel condNeg12Code 0x40 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem cn_at_42 : fetchRel condNeg12Code 0x42 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem cn_at_44 : fetchRel condNeg12Code 0x44 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem cn_at_46 : fetchRel condNeg12Code 0x46 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem cn_at_48 : fetchRel condNeg12Code 0x48 = some (.branch .bne a0 x0 0xFFFFFFE8, 2) := by decide
theorem cn_at_4a : fetchRel condNeg12Code 0x4A = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem cn_at_4c : fetchRel condNeg12Code 0x4C = some (.aluImm .add a1 sp 0x48, 2) := by decide
theorem cn_at_4e : fetchRel condNeg12Code 0x4E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem cn_at_52 : fetchRel condNeg12Code 0x52 = some (.auipc ra 0x1000, 4) := by decide
theorem cn_at_56 : fetchRel condNeg12Code 0x56 = some (.jalr ra ra 0x43C, 4) := by decide
theorem cn_at_5a : fetchRel condNeg12Code 0x5A = some (.store .sb sp (9 : Fin 32) 0x34, 4) := by decide
theorem cn_at_5e : fetchRel condNeg12Code 0x5E = some (.store .sw sp x0 0x38, 2) := by decide
theorem cn_at_60 : fetchRel condNeg12Code 0x60 = some (.store .sw sp x0 0x3C, 2) := by decide
theorem cn_at_62 : fetchRel condNeg12Code 0x62 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem cn_at_64 : fetchRel condNeg12Code 0x64 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem cn_at_66 : fetchRel condNeg12Code 0x66 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem cn_at_68 : fetchRel condNeg12Code 0x68 = some (.branch .beq a1 x0 0x12, 2) := by decide
theorem cn_at_6a : fetchRel condNeg12Code 0x6A = some (.load .lw a3 a2 0x0, 2) := by decide
theorem cn_at_6c : fetchRel condNeg12Code 0x6C = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem cn_at_6e : fetchRel condNeg12Code 0x6E = some (.aluImm .xor a3 a3 0xFFFFFFFF, 4) := by decide
theorem cn_at_72 : fetchRel condNeg12Code 0x72 = some (.store .sw a0 a3 0x0, 2) := by decide
theorem cn_at_74 : fetchRel condNeg12Code 0x74 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem cn_at_76 : fetchRel condNeg12Code 0x76 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem cn_at_78 : fetchRel condNeg12Code 0x78 = some (.branch .bne a1 x0 0xFFFFFFF2, 2) := by decide
theorem cn_at_7a : fetchRel condNeg12Code 0x7A = some (.aluImm .and a3 (9 : Fin 32) 0xFF, 4) := by decide
theorem cn_at_7e : fetchRel condNeg12Code 0x7E = some (.lui a1 0x3FCC5000, 4) := by decide
theorem cn_at_82 : fetchRel condNeg12Code 0x82 = some (.aluImm .add a1 a1 0xFFFFF830, 4) := by decide
theorem cn_at_86 : fetchRel condNeg12Code 0x86 = some (.lui a2 0x3FCC5000, 4) := by decide
theorem cn_at_8a : fetchRel condNeg12Code 0x8A = some (.aluImm .add a2 a2 0xFFFFF828, 4) := by decide
theorem cn_at_8e : fetchRel condNeg12Code 0x8E = some (.aluImm .add a0 sp 0x48, 2) := by decide
theorem cn_at_90 : fetchRel condNeg12Code 0x90 = some (.aluImm .add (9 : Fin 32) sp 0x48, 2) := by decide
theorem cn_at_92 : fetchRel condNeg12Code 0x92 = some (.auipc ra 0x0, 4) := by decide
theorem cn_at_96 : fetchRel condNeg12Code 0x96 = some (.jalr ra ra 0x7E, 4) := by decide
theorem cn_at_9a : fetchRel condNeg12Code 0x9A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem cn_at_9c : fetchRel condNeg12Code 0x9C = some (.store .sw sp x0 0x40, 2) := by decide
theorem cn_at_9e : fetchRel condNeg12Code 0x9E = some (.store .sw sp x0 0x44, 2) := by decide
theorem cn_at_a0 : fetchRel condNeg12Code 0xA0 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem cn_at_a2 : fetchRel condNeg12Code 0xA2 = some (.aluImm .add a2 sp 0x40, 2) := by decide
theorem cn_at_a4 : fetchRel condNeg12Code 0xA4 = some (.aluImm .add a3 x0 0x2, 2) := by decide
theorem cn_at_a6 : fetchRel condNeg12Code 0xA6 = some (.branch .beq a3 x0 0x20, 2) := by decide
theorem cn_at_a8 : fetchRel condNeg12Code 0xA8 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem cn_at_aa : fetchRel condNeg12Code 0xAA = some (.load .lw a5 (9 : Fin 32) 0x0, 2) := by decide
theorem cn_at_ac : fetchRel condNeg12Code 0xAC = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem cn_at_ae : fetchRel condNeg12Code 0xAE = some (.alu .add a1 a1 a4, 2) := by decide
theorem cn_at_b0 : fetchRel condNeg12Code 0xB0 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem cn_at_b2 : fetchRel condNeg12Code 0xB2 = some (.alu .add a5 a5 a1, 2) := by decide
theorem cn_at_b4 : fetchRel condNeg12Code 0xB4 = some (.alu .sltu a4 a1 a4, 4) := by decide
theorem cn_at_b8 : fetchRel condNeg12Code 0xB8 = some (.alu .sltu a1 a5 a1, 4) := by decide
theorem cn_at_bc : fetchRel condNeg12Code 0xBC = some (.store .sw a2 a5 0x0, 2) := by decide
theorem cn_at_be : fetchRel condNeg12Code 0xBE = some (.alu .add a1 a1 a4, 2) := by decide
theorem cn_at_c0 : fetchRel condNeg12Code 0xC0 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem cn_at_c2 : fetchRel condNeg12Code 0xC2 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem cn_at_c4 : fetchRel condNeg12Code 0xC4 = some (.branch .bne a3 x0 0xFFFFFFE4, 2) := by decide
theorem cn_at_c6 : fetchRel condNeg12Code 0xC6 = some (.aluImm .add a0 sp 0x48, 2) := by decide
theorem cn_at_c8 : fetchRel condNeg12Code 0xC8 = some (.aluImm .add a2 sp 0x4, 2) := by decide
theorem cn_at_ca : fetchRel condNeg12Code 0xCA = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem cn_at_cc : fetchRel condNeg12Code 0xCC = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem cn_at_ce : fetchRel condNeg12Code 0xCE = some (.auipc ra 0x0, 4) := by decide
theorem cn_at_d2 : fetchRel condNeg12Code 0xD2 = some (.jalr ra ra 0xFFFFF9DA, 4) := by decide
theorem cn_at_d6 : fetchRel condNeg12Code 0xD6 = some (.aluImm .add a1 sp 0x48, 2) := by decide
theorem cn_at_d8 : fetchRel condNeg12Code 0xD8 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem cn_at_dc : fetchRel condNeg12Code 0xDC = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem cn_at_de : fetchRel condNeg12Code 0xDE = some (.auipc ra 0x1000, 4) := by decide
theorem cn_at_e2 : fetchRel condNeg12Code 0xE2 = some (.jalr ra ra 0x3B0, 4) := by decide
theorem cn_at_e6 : fetchRel condNeg12Code 0xE6 = some (.aluImm .add a0 sp 0x48, 2) := by decide
theorem cn_at_e8 : fetchRel condNeg12Code 0xE8 = some (.aluImm .add a2 sp 0x40, 2) := by decide
theorem cn_at_ea : fetchRel condNeg12Code 0xEA = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem cn_at_ec : fetchRel condNeg12Code 0xEC = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem cn_at_ee : fetchRel condNeg12Code 0xEE = some (.auipc ra 0x0, 4) := by decide
theorem cn_at_f2 : fetchRel condNeg12Code 0xF2 = some (.jalr ra ra 0x22, 4) := by decide
theorem cn_at_f6 : fetchRel condNeg12Code 0xF6 = some (.load .lw a0 sp 0x48, 2) := by decide
theorem cn_at_f8 : fetchRel condNeg12Code 0xF8 = some (.load .lw a1 sp 0x4C, 2) := by decide
theorem cn_at_fa : fetchRel condNeg12Code 0xFA = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem cn_at_fc : fetchRel condNeg12Code 0xFC = some (.store .sw a2 a0 0x0, 2) := by decide
theorem cn_at_fe : fetchRel condNeg12Code 0xFE = some (.store .sw a2 a1 0x4, 2) := by decide
theorem cn_at_100 : fetchRel condNeg12Code 0x100 = some (.load .lw ra sp 0x8C, 2) := by decide
theorem cn_at_102 : fetchRel condNeg12Code 0x102 = some (.load .lw (8 : Fin 32) sp 0x88, 2) := by decide
theorem cn_at_104 : fetchRel condNeg12Code 0x104 = some (.load .lw (9 : Fin 32) sp 0x84, 2) := by decide
theorem cn_at_106 : fetchRel condNeg12Code 0x106 = some (.load .lw (18 : Fin 32) sp 0x80, 2) := by decide
theorem cn_at_108 : fetchRel condNeg12Code 0x108 = some (.load .lw (19 : Fin 32) sp 0x7C, 2) := by decide
theorem cn_at_10a : fetchRel condNeg12Code 0x10A = some (.load .lw (20 : Fin 32) sp 0x78, 2) := by decide
theorem cn_at_10c : fetchRel condNeg12Code 0x10C = some (.aluImm .add sp sp 0x90, 2) := by decide
theorem cn_at_10e : fetchRel condNeg12Code 0x10E = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem nat_xor_ones : ∀ k a, a < 2 ^ k → (a ^^^ (2 ^ k - 1)) + a = 2 ^ k - 1
  | 0, a, h => by
    have : a = 0 := by simp at h; omega
    subst this; rfl
  | k + 1, a, h => by
    have hk := Nat.two_pow_pos k
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have ih := nat_xor_ones k (a / 2) (by omega)
    have hd : (a ^^^ (2 ^ (k + 1) - 1)) / 2 = a / 2 ^^^ (2 ^ k - 1) := by
      rw [Nat.xor_div_two]; congr 1; omega
    have m1 : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have t := Nat.testBit_xor a (2 ^ (k + 1) - 1) 0
    simp only [Nat.testBit_zero, m1] at t
    have hm : (a ^^^ (2 ^ (k + 1) - 1)) % 2 + a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one a with h0 | h0 <;>
        rcases Nat.mod_two_eq_zero_or_one (a ^^^ (2 ^ (k + 1) - 1)) with h1 | h1 <;>
        simp [h0, h1] at t ⊢
    have e1 := Nat.div_add_mod (a ^^^ (2 ^ (k + 1) - 1)) 2
    have e2 := Nat.div_add_mod a 2
    omega

theorem xor_ones_toNat (l : Word) : (aluEval .xor l 0xFFFFFFFF).toNat + l.toNat = 2 ^ 32 - 1 := by
  show (l ^^^ 0xFFFFFFFF).toNat + _ = _
  rw [BitVec.toNat_xor]
  exact nat_xor_ones 32 l.toNat l.isLt

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev cnPs : List (Fin 32 × Word) :=
  [(ra, 0x8C), ((8 : Fin 32), 0x88), ((9 : Fin 32), 0x84), ((18 : Fin 32), 0x80), ((19 : Fin 32), 0x7C),
   ((20 : Fin 32), 0x78)]

/-- From 0xE to 0x1E: keep the arguments, and `memset`'s arguments. -/
def cnPro : List BInstr :=
  [.alu .add (18 : Fin 32) x0 a2, .alu .add (20 : Fin 32) x0 a1, .alu .add (19 : Fin 32) x0 a0,
   .aluImm .add a0 sp 0x48, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0, .aluImm .add (8 : Fin 32) sp 0x48]

def cnInit : List BInstr :=
  [.aluImm .add a2 x0 0x0, .aluImm .add (9 : Fin 32) x0 0x1, .aluImm .add a0 x0 0xC, .alu .add a1 x0 (19 : Fin 32)]

/-- One limb of `lo.carrying_neg()`, from 0x30 to 0x48. -/
def cnNeg : List BInstr :=
  [.lw a3 a1 0x0, .aluImm .add a1 a1 0x4, .aluImm .xor a3 a3 0xFFFFFFFF, .alu .add a3 a3 (9 : Fin 32),
   .alu .sltu (9 : Fin 32) a3 (9 : Fin 32), .sw (8 : Fin 32) a3 0x0, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4,
   .alu .add (9 : Fin 32) (9 : Fin 32) a2, .aluImm .add a0 a0 0xFFFFFFFF, .aluImm .add a2 x0 0x0]

def cnCpyArgs : List BInstr := [.aluImm .add a0 sp 0x4, .aluImm .add a1 sp 0x48, .aluImm .add a2 x0 0x30]

/-- From 0x5A to 0x68: the carry byte, `!hi`'s buffer zeroed, and the loop's
pointers. -/
def cnHi : List BInstr :=
  [.sb sp (9 : Fin 32) 0x34, .sw sp x0 0x38, .sw sp x0 0x3C, .aluImm .add a0 sp 0x38, .aluImm .add a1 x0 0x2,
   .alu .add a2 x0 (20 : Fin 32)]

/-- One limb of `hi.not()`, from 0x6A to 0x78. -/
def cnNot : List BInstr :=
  [.lw a3 a2 0x0, .aluImm .add a2 a2 0x4, .aluImm .xor a3 a3 0xFFFFFFFF, .sw a0 a3 0x0, .aluImm .add a0 a0 0x4,
   .aluImm .add a1 a1 0xFFFFFFFF]

/-- From 0x7A to 0x92: `Uint<2>::select(ZERO, ONE, carry)`'s arguments. -/
def cnSel1 : List BInstr :=
  [.aluImm .and a3 (9 : Fin 32) 0xFF, .lui a1 0x3FCC5000, .aluImm .add a1 a1 0xFFFFF830, .lui a2 0x3FCC5000,
   .aluImm .add a2 a2 0xFFFFF828, .aluImm .add a0 sp 0x48, .aluImm .add (9 : Fin 32) sp 0x48]

def cnAddInit : List BInstr :=
  [.aluImm .add a1 x0 0x0, .sw sp x0 0x40, .sw sp x0 0x44, .aluImm .add a0 sp 0x38, .aluImm .add a2 sp 0x40,
   .aluImm .add a3 x0 0x2]

/-- One limb of `wrapping_add`, from 0xA8 to 0xC4. -/
def cnAdd : List BInstr :=
  [.lw a4 a0 0x0, .lw a5 (9 : Fin 32) 0x0, .aluImm .add a0 a0 0x4, .alu .add a1 a1 a4,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, .alu .add a5 a5 a1, .alu .sltu a4 a1 a4, .alu .sltu a1 a5 a1,
   .sw a2 a5 0x0, .alu .add a1 a1 a4, .aluImm .add a2 a2 0x4, .aluImm .add a3 a3 0xFFFFFFFF]

def cnSel12 : List BInstr :=
  [.aluImm .add a0 sp 0x48, .aluImm .add a2 sp 0x4, .alu .add a1 x0 (19 : Fin 32), .alu .add a3 x0 (18 : Fin 32)]

def cnCpy2 : List BInstr := [.aluImm .add a1 sp 0x48, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (19 : Fin 32)]

def cnSel2 : List BInstr :=
  [.aluImm .add a0 sp 0x48, .aluImm .add a2 sp 0x40, .alu .add a1 x0 (20 : Fin 32), .alu .add a3 x0 (18 : Fin 32)]

/-- From 0xF6 to 0x100: the selected high part to `hi`. -/
def cnStore : List BInstr :=
  [.lw a0 sp 0x48, .lw a1 sp 0x4C, .alu .add a2 x0 (20 : Fin 32), .sw a2 a0 0x0, .sw a2 a1 0x4]

section
set_option maxRecDepth 20000
theorem cnSave_end : blockEnd condNeg12Code 2 (saveBlock cnPs) = some 0xE := by decide
theorem cnPro_end : blockEnd condNeg12Code 0xE cnPro = some 0x1E := by decide
theorem cnInit_end : blockEnd condNeg12Code 0x26 cnInit = some 0x2E := by decide
theorem cnNeg_end : blockEnd condNeg12Code 0x30 cnNeg = some 0x48 := by decide
theorem cnCpyArgs_end : blockEnd condNeg12Code 0x4A cnCpyArgs = some 0x52 := by decide
theorem cnHi_end : blockEnd condNeg12Code 0x5A cnHi = some 0x68 := by decide
theorem cnNot_end : blockEnd condNeg12Code 0x6A cnNot = some 0x78 := by decide
theorem cnSel1_end : blockEnd condNeg12Code 0x7A cnSel1 = some 0x92 := by decide
theorem cnAddInit_end : blockEnd condNeg12Code 0x9A cnAddInit = some 0xA6 := by decide
theorem cnAdd_end : blockEnd condNeg12Code 0xA8 cnAdd = some 0xC4 := by decide
theorem cnSel12_end : blockEnd condNeg12Code 0xC6 cnSel12 = some 0xCE := by decide
theorem cnCpy2_end : blockEnd condNeg12Code 0xD6 cnCpy2 = some 0xDE := by decide
theorem cnSel2_end : blockEnd condNeg12Code 0xE6 cnSel2 = some 0xEE := by decide
theorem cnStore_end : blockEnd condNeg12Code 0xF6 cnStore = some 0x100 := by decide
theorem cnRestore_end : blockEnd condNeg12Code 0x100 (restoreBlock cnPs) = some 0x10C := by decide
end

/-- The function's frame: its `sp` while it runs. -/
abbrev cnF (sp0 : Word) : Word := sp0 + 0xFFFFFF70

/-- The bottom of the stack it and its callees may change: 0x90 bytes of
frame and `Uint<12>::select`'s 0x50 below. -/
abbrev cnR (sp0 : Word) : Word := sp0 + 0xFFFFFF20

theorem cnR_F (sp0 : Word) : cnR sp0 + BitVec.ofNat 32 0x50 = cnF sp0 := by rw [BitVec.add_assoc]; rfl

theorem cnR_w (sp0 : Word) (h : 0xE0 ≤ sp0.toNat) : (cnR sp0).toNat + 0xE0 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFF20 : Word).toNat = 4294967072 := rfl
  have := sp0.isLt
  omega

theorem cnin {sp0 x : Word} {c l : Nat} (h : c + l ≤ 0x90) (hx : Sep (cnR sp0) 0xE0 x 1) :
    Sep (cnF sp0 + BitVec.ofNat 32 c) l x 1 := by
  rw [← cnR_F, add_ofNat_assoc]; exact hx.sub (by omega)

theorem cnin' {sp0 b : Word} {c l k : Nat} (h : c + l ≤ 0x90) (hx : Sep (cnR sp0) 0xE0 b k) :
    Sep (cnF sp0 + BitVec.ofNat 32 c) l b k := by
  rw [← cnR_F, add_ofNat_assoc]; exact hx.sub (by omega)

set_option maxRecDepth 20000 in
theorem cnPs_range : ∀ p ∈ cnPs, p.2.toNat % 4 = 0 ∧ 0x78 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x90 := by decide

set_option maxRecDepth 20000 in
theorem cnPs_sp : ∀ p ∈ cnPs, p.1 ≠ sp := by decide

/-- Where `conditional_negate_in_place_wide::<12, 2>` runs: its code and its
callees' at their offsets, the constants `Uint<2>::ZERO` and `Uint<2>::ONE`,
its stack region `cnR`, and `lo` and `hi`, aligned and apart from what each
must not touch. -/
structure CNEnv (M : Word → BitVec 8) (P sp0 lo hi : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P condNeg12Code
  mset : CodeIn M (P + 0x1426) memsetCode
  stub : CodeIn M (P + 0x148E) memcpyStubCode
  body : CodeIn M (P + 0x1496) memcpyBodyCode
  sel2 : CodeIn M (P + 0x110) uintSelect2Code
  sel12 : CodeIn M (P + 0xFFFFFAA8) uintSelect12Code
  zero : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData
  one : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData
  hsp : sp0.toNat % 4 = 0
  hS : 0xE0 ≤ sp0.toNat
  hlo : lo.toNat % 4 = 0
  hhi : hi.toNat % 4 = 0
  hwl : lo.toNat + 48 < 2 ^ 32
  hwh : hi.toNat + 8 < 2 ^ 32
  sRC : Sep (cnR sp0) 0xE0 P condNeg12Code.length
  sRM : Sep (cnR sp0) 0xE0 (P + 0x1426) memsetCode.length
  sRU : Sep (cnR sp0) 0xE0 (P + 0x148E) memcpyStubCode.length
  sRB : Sep (cnR sp0) 0xE0 (P + 0x1496) memcpyBodyCode.length
  sR2 : Sep (cnR sp0) 0xE0 (P + 0x110) uintSelect2Code.length
  sRL : Sep (cnR sp0) 0xE0 (P + 0xFFFFFAA8) uintSelect12Code.length
  sRZ : Sep (cnR sp0) 0xE0 (BitVec.ofNat 32 u2ZeroAddress) 8
  sRO : Sep (cnR sp0) 0xE0 (BitVec.ofNat 32 u2OneAddress) 8
  sLR : Sep lo 48 (cnR sp0) 0xE0
  sHR : Sep hi 8 (cnR sp0) 0xE0
  sLH : Sep lo 48 hi 8
  sLC : Sep lo 48 P condNeg12Code.length
  sLB : Sep lo 48 (P + 0x1496) memcpyBodyCode.length
  sL2 : Sep lo 48 (P + 0x110) uintSelect2Code.length
  sHC : Sep hi 8 P condNeg12Code.length

/-- The registers the function leaves alone. -/
def cnKeep (q : Fin 32) : Bool := q.val ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The prologue, from entry to the negation loop at 0x30: save the
registers, keep the arguments, and zero the buffer at `F + 0x48`. -/
theorem cn_pro (m : Machine) {P sp0 lo hi : Word} (env : CNEnv m.mem P sp0 lo hi) (hpc : m.pc = P)
    (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x30 (reg n) ∧
      (∀ x, Sep (cnR sp0) 0xE0 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ cnPs → memLoad32 M (cnF sp0 + o) = reg m r) ∧
      reg n sp = cnF sp0 ∧ reg n 8 = cnF sp0 + BitVec.ofNat 32 0x48 + BitVec.ofNat 32 (4 * 0) ∧
      reg n a1 = reg m a0 + BitVec.ofNat 32 (4 * 0) ∧ reg n a0 = BitVec.ofNat 32 (12 - 0) ∧ reg n 9 = 1 ∧
      reg n a2 = 0 ∧ reg n 18 = reg m a2 ∧ reg n 19 = reg m a0 ∧ reg n 20 = reg m a1 ∧
      ∀ q, cnKeep q = true → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hRw := cnR_w sp0 env.hS
  have hFa : (cnF sp0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF70) (by decide)
  have hFw : (cnF sp0).toNat + 0x90 ≤ 2 ^ 32 := by
    rw [← cnR_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sFC : Sep (cnF sp0) 0x90 P condNeg12Code.length := by
    have := cnin' (c := 0) (l := 0x90) (by decide) env.sRC; rwa [add_ofNat_zero] at this
  have fF : ∀ x, Sep (cnR sp0) 0xE0 x 1 → Sep (cnF sp0) 0x90 x 1 := fun x hx => by
    have := cnin (c := 0) (l := 0x90) (by decide) hx; rwa [add_ofNat_zero] at this
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code cn_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF70) sp = cnF sp0 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock cnPs) u1 env.code cnSave_end (saveBlock_ok _ cnPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (cnPs_range p hp).1, frm_sep' sFC (by have := cnPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (cnF sp0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF70)) cnPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (cnR sp0) 0xE0 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside cnPs fun p hp => frm_sep' (fF x hx) (by have := cnPs_range p hp; omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (cnR sp0) 0xE0 b code.length →
      (∀ x, Sep (cnR sp0) 0xE0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have k2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q hq => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, hq]
  have sp2 : reg m2 sp = cnF sp0 := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block cnPro u2.self (cIn env.code env.sRC frSv) cnPro_end
    (by simp [BlockOk, BInstr.ok, cnPro])
  simp only [runBlock, BInstr.run, cnPro] at u3
  have g3 : ∀ q, reg m3 q = _ := u3.regs
  obtain ⟨m4, c4, u4, a04, k4⟩ := St.memsetW (B := P + 0x1426) (w := 12) (dst := cnF sp0 + BitVec.ofNat 32 0x48)
    (even_at P env.hP 0x1426 (by decide)) u3.self (cIn env.code env.sRC frSv) (cIn env.mset env.sRM frSv)
    cn_at_1e cn_at_22 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x1E + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (aligned_add hFa (by decide))
    (cnin' (by decide) env.sRM)
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval])
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords Msv (cnF sp0 + BitVec.ofNat 32 0x48) 0 12 = Mz := ⟨_, rfl⟩
  rw [hMz] at u4
  have frZ : ∀ x, Sep (cnR sp0) 0xE0 x 1 → Mz x = m.mem x := fun x hx => by
    rw [← hMz, fillWords_outside 12 (cnin (by decide) hx), frSv x hx]
  have cC := cIn env.code env.sRC frZ
  obtain ⟨m5, c5, u5⟩ := St.block cnInit u4 cC cnInit_end (by simp [BlockOk, BInstr.ok, cnInit])
  simp only [runBlock, BInstr.run, cnInit] at u5
  have x10 : reg m5 a0 = 0xC := by rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨m6, d6, u6⟩ := u5.self.notTaken cC 0x30 cn_at_2e (by decide) (by rw [x10, u5.self.zero]; decide)
  have k5 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (9 : Fin 32) → reg m6 q = reg m4 q := fun q h1 h2 h3 h4 => by
    rw [u6.regs, u5.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, u4.zero]
    · simp [upd, h0, h1, h2, h3, h4]
  have k3 : ∀ q, q.val ≠ 0 → q ≠ (18 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ a0 → q ≠ a2 →
      q ≠ a1 → q ≠ (8 : Fin 32) → reg m3 q = reg m2 q :=
    fun q h0 h18 h20 h19 h10 h12 h11 h8 => by
      rw [g3]; simp only [upd_app, h0, h18, h20, h19, h10, h12, h11, h8, ite_false]
  have k4' : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg m4 q = reg m3 q := k4
  have r3 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ (9 : Fin 32) →
      reg m6 q = reg m3 q := fun q h2 h3 h4 h5 h6 h7 h10 h11 h9 => by
    rw [k5 q h10 h11 h2 h9, k4' q h2 h3 h4 h5 h6 h7]
  have sp6 : reg m6 sp = cnF sp0 := by
    rw [r3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), k3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), sp2]
  refine ⟨m6, Mz, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.single d6))))), u6.self, frZ, ?_, sp6,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r o h
    obtain ⟨_, ho1, ho2⟩ := cnPs_range (r, o) h
    dsimp only at ho1 ho2
    have hs : Sep (cnF sp0 + BitVec.ofNat 32 0x48) (4 * 12) (cnF sp0 + o) 4 := by
      have := sep_offsets (cnF sp0) (c := 0x48) (n := 4 * 12) (d := o.toNat) (k := 4) (.inl (by omega))
        (by decide) (by omega)
      rwa [ofNat_toNat_self] at this
    rw [← hMz, fillWords_load_sep hs, ← hMsv]
    simp only [cnPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  · rw [r3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [sp2]; exact (add_ofNat_zero _).symm
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [k4' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a0 (by decide)]; show (0 : Word) + ((0 : Word) + reg m a0) = _
    rw [show (0 : Word) + ((0 : Word) + reg m a0) = reg m a0 from (BitVec.zero_add _).trans (BitVec.zero_add _)]
    exact (add_ofNat_zero _).symm
  · rw [u6.regs, x10]; rfl
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; try (rw [u4.zero]; try rfl)
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; try (rw [u4.zero]; try rfl)
  · rw [r3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a2 (by decide)]; exact BitVec.zero_add _
  · rw [r3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a0 (by decide)]; exact BitVec.zero_add _
  · rw [r3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a1 (by decide)]; exact BitVec.zero_add _
  · intro q hq
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u6.self.zero, s0.zero]
    have k := fun r (hr : cnKeep r = false) => pkeep_ne hq hr
    rw [r3 q (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k ra rfl) (k a0 rfl) (k a1 rfl) (k 9 rfl),
      k3 q h0 (k 18 rfl) (k 20 rfl) (k 19 rfl) (k a0 rfl) (k a2 rfl) (k a1 rfl) (k 8 rfl), k2 q (k sp rfl)]

/-- The registers one limb of the negation leaves alone. -/
def cnNegKeep (q : Fin 32) : Bool := q.val ∉ [0, 8, 9, 10, 11, 12, 13]

/-- The word one limb of the negation stores: `!l + c`. -/
abbrev negW (l c : Word) : Word := aluEval .add (aluEval .xor l 0xFFFFFFFF) c

set_option maxRecDepth 20000 in
theorem cnNeg_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock cnNeg (M, f)).1 = memStore32 M (f 8 + 0) (negW (memLoad32 M (f a1 + 0)) (f 9)) ∧
    (runBlock cnNeg (M, f)).2 9 = aluEval .add (aluEval .sltu (negW (memLoad32 M (f a1 + 0)) (f 9)) (f 9)) (f a2) ∧
    (runBlock cnNeg (M, f)).2 8 = f 8 + 4 ∧ (runBlock cnNeg (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock cnNeg (M, f)).2 a0 = f a0 + 0xFFFFFFFF ∧ (runBlock cnNeg (M, f)).2 a2 = 0 ∧
    ∀ q, cnNegKeep q = true → (runBlock cnNeg (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, cnNeg, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 6
  have h0 : q.val ≠ 0 := fun e => absurd (show cnNegKeep q = false by unfold cnNegKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a0) hq rfl,
    pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem cnNeg_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h11 : (f a1 + 0).toNat % 4 = 0) (h8 : (f 8 + 0).toNat % 4 = 0) (hs : Sep (f 8 + 0) 4 base len) :
    BlockOk base len cnNeg (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, cnNeg, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h11, h8, hs⟩

theorem neg_arith {A L K V c c' l X : Nat} (h1 : A + K * c + L = K) (h2 : V + 2 ^ 32 * c' = X + c)
    (h3 : X + l = 2 ^ 32 - 1) : A + V * K + K * 2 ^ 32 * c' + (L + l * K) = K * 2 ^ 32 := by
  have e : (V + 2 ^ 32 * c' + l) * K = V * K + K * 2 ^ 32 * c' + l * K := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm (2 ^ 32 * c') K, Nat.mul_assoc]
  have e2 : (V + 2 ^ 32 * c' + l) * K = (2 ^ 32 - 1) * K + c * K := by
    rw [h2, Nat.add_right_comm X c l, h3, Nat.add_mul]
  have e3 : (2 ^ 32 - 1) * K + K = 2 ^ 32 * K := by
    rw [Nat.sub_one_mul]; have : K ≤ 2 ^ 32 * K := Nat.le_mul_of_pos_left K (by decide); omega
  have e4 : K * c = c * K := Nat.mul_comm _ _
  have e5 : K * 2 ^ 32 = 2 ^ 32 * K := Nat.mul_comm _ _
  omega

theorem negW_carry (l c : Word) :
    (negW l c).toNat + 2 ^ 32 * (aluEval .sltu (negW l c) c).toNat = (aluEval .xor l 0xFFFFFFFF).toNat + c.toNat :=
  add_carry _ _

/-- **One limb of the negation**, from 0x30: store `!l + c` for limb `i` of
`lo` to the buffer at `T`, with its carry in `s1`. -/
theorem cn_neg_iter {M : Word → BitVec 8} {P T lo c : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x30 (reg n)) (hc : CodeIn M P condNeg12Code) (hi : i < 12) (hT : T.toNat % 4 = 0)
    (hlo : lo.toNat % 4 = 0) (sC : Sep (T + BitVec.ofNat 32 (4 * i)) 4 P condNeg12Code.length)
    (r8 : reg n 8 = T + BitVec.ofNat 32 (4 * i)) (r11 : reg n a1 = lo + BitVec.ofNat 32 (4 * i))
    (ra0 : reg n a0 = BitVec.ofNat 32 (12 - i)) (r9 : reg n 9 = c) (r12 : reg n a2 = 0) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (T + BitVec.ofNat 32 (4 * i)) (negW (memLoad32 M (lo + BitVec.ofNat 32 (4 * i))) c))
        P n' (if i + 1 < 12 then 0x30 else 0x4A) (reg n') ∧
      reg n' 9 = aluEval .sltu (negW (memLoad32 M (lo + BitVec.ofNat 32 (4 * i))) c) c ∧
      reg n' 8 = T + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a1 = lo + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧ reg n' a2 = 0 ∧
      ∀ q, cnNegKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E9, E8, E11, Ea0, Ea2, Ek⟩ := cnNeg_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block cnNeg s hc cnNeg_end
    (cnNeg_ok (by rw [r11, add_lit_zero]; exact aligned_add hlo (by omega))
      (by rw [r8, add_lit_zero]; exact aligned_add hT (by omega)) (by rw [r8, add_lit_zero]; exact sC))
  rw [E1, r8, r11, r9, add_lit_zero, add_lit_zero] at u1
  rw [r11, r9, r12, add_lit_zero] at E9
  have hc1 := CodeIn.store32 (v := negW (memLoad32 M (lo + BitVec.ofNat 32 (4 * i))) c) hc sC
  have ea0 : reg n1 a0 = BitVec.ofNat 32 (12 - (i + 1)) := by rw [u1.regs, Ea0, ra0, cnt12_dec i hi]
  have hb : branchTaken .bne (reg n1 a0) (reg n1 x0) = decide (i + 1 < 12) := by
    rw [ea0, u1.self.zero]; exact cnt12_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 9 = aluEval .sltu (negW (memLoad32 M (lo + BitVec.ofNat 32 (4 * i))) c) c ∧
      reg n2 8 = T + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a1 = lo + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧ reg n2 a2 = 0 ∧
      ∀ q, cnNegKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E9]; exact BitVec.add_zero _, by rw [h2, u1.regs, E8, r8, ptr4],
      by rw [h2, u1.regs, E11, r11, ptr4], by rw [h2, ea0], by rw [h2, u1.regs, Ea2],
      fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 12
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x30 cn_at_48 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x4A cn_at_48 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

set_option exponentiation.threshold 600 in
/-- **The negation loop**, from limb `i` to its exit at 0x4A: the buffer at
`T` and the carry in `s1` hold `2^384 - lo` for `lo` in `M1`. -/
theorem cn_neg_loop {P T lo : Word} {M1 : Word → BitVec 8} (hT : T.toNat % 4 = 0) (hlo : lo.toNat % 4 = 0)
    (hTw : T.toNat + 0x30 ≤ 2 ^ 32) (sC : Sep T 0x30 P condNeg12Code.length) (sL : Sep T 0x30 lo 48) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {c : Word},
      St M P n 0x30 (reg n) → CodeIn M P condNeg12Code → (∀ x, Sep T 0x30 x 1 → M x = M1 x) →
      c.toNat ≤ 1 → accV M T i + 2 ^ (32 * i) * c.toNat + accV M1 lo i = 2 ^ (32 * i) →
      reg n 8 = T + BitVec.ofNat 32 (4 * i) → reg n a1 = lo + BitVec.ofNat 32 (4 * i) →
      reg n a0 = BitVec.ofNat 32 (12 - i) → reg n 9 = c → reg n a2 = 0 →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x4A (reg n') ∧ CodeIn M' P condNeg12Code ∧
        (∀ x, Sep T 0x30 x 1 → M' x = M1 x) ∧ (reg n' 9).toNat ≤ 1 ∧
        accV M' T 12 + 2 ^ (32 * 12) * (reg n' 9).toNat + accV M1 lo 12 = 2 ^ (32 * 12) ∧
        ∀ q, cnNegKeep q = true → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {c : Word},
      St M P n 0x30 (reg n) → CodeIn M P condNeg12Code → (∀ x, Sep T 0x30 x 1 → M x = M1 x) →
      c.toNat ≤ 1 → accV M T i + 2 ^ (32 * i) * c.toNat + accV M1 lo i = 2 ^ (32 * i) →
      reg n 8 = T + BitVec.ofNat 32 (4 * i) → reg n a1 = lo + BitVec.ofNat 32 (4 * i) →
      reg n a0 = BitVec.ofNat 32 (12 - i) → reg n 9 = c → reg n a2 = 0 →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x30 else 0x4A) (reg n') ∧
        CodeIn M' P condNeg12Code ∧ (∀ x, Sep T 0x30 x 1 → M' x = M1 x) ∧ (reg n' 9).toNat ≤ 1 ∧
        accV M' T (i + 1) + 2 ^ (32 * (i + 1)) * (reg n' 9).toNat + accV M1 lo (i + 1) = 2 ^ (32 * (i + 1)) ∧
        reg n' 8 = T + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a1 = lo + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧ reg n' a2 = 0 ∧
        ∀ q, cnNegKeep q = true → reg n' q = reg n q := by
    intro i hi M n c s hc hfr hcb hv r8 r11 ra0 r9 r12
    have sCi : Sep (T + BitVec.ofNat 32 (4 * i)) 4 P condNeg12Code.length := sC.sub (by omega)
    obtain ⟨n1, c1, u1, e9, e8, e11, ea0, ea2, fr⟩ := cn_neg_iter s hc hi hT hlo sCi r8 r11 ra0 r9 r12
    have eL : memLoad32 M (lo + BitVec.ofNat 32 (4 * i)) = memLoad32 M1 (lo + BitVec.ofNat 32 (4 * i)) :=
      load_frame hfr (sL.subR (by omega))
    rw [eL] at u1 e9
    refine ⟨n1, _, c1, u1, hc.store32 sCi, fun x hx => ?_, by rw [e9]; exact sltu_le1 _ _, ?_, e8, e11, ea0, ea2, fr⟩
    · rw [memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), hfr x hx]
    · rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same, accV_succ1,
        pow32_succ, e9]
      exact neg_arith hv (negW_carry _ c) (xor_ones_toNat _)
  intro m
  induction m with
  | zero =>
    intro i hi M n c s hc hfr hcb hv r8 r11 ra0 r9 r12
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hfr hcb hv r8 r11 ra0 r9 r12
    exact ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, fr⟩
  | succ m ih =>
    intro i hi M n c s hc hfr hcb hv r8 r11 ra0 r9 r12
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, e8, e11, ea0, ea2, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hfr hcb hv r8 r11 ra0 r9 r12
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M'', c', u', hc', hf', hb', hv', fr'⟩ := ih (i + 1) (sel_succ hi) u1 hc1 hf1 hb1 hv1 e8 e11 ea0 rfl ea2
    exact ⟨n', M'', c1.trans c', u', hc', hf', hb', hv', fun q hq => by rw [fr' q hq, fr q hq]⟩

/-- What the buffers hold after the copy of `-lo` and `!hi`'s zeroed buffer. -/
abbrev cnMidMem (M : Word → BitVec 8) (F c : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore8 (copyWords M (F + BitVec.ofNat 32 4) (F + BitVec.ofNat 32 0x48) 12) (F + 0x34)
    (c.extractLsb' 0 8)) (F + 0x38) 0) (F + 0x3C) 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the negation loop's exit at 0x4A to the `!hi` loop at 0x6A: copy
`-lo` to `F + 4`, store the carry byte, and zero `!hi`'s buffer. -/
theorem cn_mid {M : Word → BitVec 8} {P F hi c : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x4A (reg n)) (hc : CodeIn M P condNeg12Code) (hst : CodeIn M (P + 0x148E) memcpyStubCode)
    (hbd : CodeIn M (P + 0x1496) memcpyBodyCode) (hF : F.toNat % 4 = 0) (hFw : F.toNat + 0x90 ≤ 2 ^ 32)
    (sFC : Sep F 0x90 P condNeg12Code.length) (sFB : Sep F 0x90 (P + 0x1496) memcpyBodyCode.length)
    (rsp : reg n sp = F) (r9 : reg n 9 = c) (r20 : reg n 20 = hi) :
    ∃ n', Steps n n' ∧ St (cnMidMem M F c) P n' 0x6A (reg n') ∧
      reg n' sp = F ∧ reg n' a0 = F + 0x38 + BitVec.ofNat 32 (4 * 0) ∧ reg n' a1 = BitVec.ofNat 32 (2 - 0) ∧
      reg n' a2 = hi + BitVec.ofNat 32 (4 * 0) ∧ reg n' 9 = c ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ ra →
        reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block cnCpyArgs s hc cnCpyArgs_end (by simp [BlockOk, BInstr.ok, cnCpyArgs])
  simp only [runBlock, BInstr.run, cnCpyArgs] at u1
  have e8 : P + 0x148E + 8 = P + 0x1496 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n2, c2, u2, a02, k2⟩ := St.memcpyW (B := P + 0x148E) (w := 12) (dst := F + BitVec.ofNat 32 4)
    (src := F + BitVec.ofNat 32 0x48) (even_at P hP 0x148E (by decide)) u1.self hc hst (by rw [e8]; exact hbd)
    cn_at_52 cn_at_56 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x52 + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (aligned_add hF (by decide))
    (aligned_add hF (by decide))
    (sep_offsets F (.inl (by decide)) (by decide) (by decide))
    (by rw [e8]; exact sFB.sub (by decide))
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  have hc2 : CodeIn (copyWords M (F + BitVec.ofNat 32 4) (F + BitVec.ofNat 32 0x48) 12) P condNeg12Code :=
    fun i hi => by rw [copyWords_outside 12 ((sFC.sub (c := 4) (l := 4 * 12) (by decide)).subR (c := i) (l := 1)
      (by omega))]; exact hc i hi
  have k1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n1 q = reg n q := fun q h0 h1 h2 h3 => by
    rw [u1.regs]; simp only [upd_app, h0, h1, h2, h3, ite_false]
  have k12 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ ra → reg n2 q = reg n q := fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => by
    rw [k2 q h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, k1 q h0 h1 h2 h3]
  have sp2 : reg n2 sp = F := by
    rw [k12 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), rsp]
  have s9 : reg n2 9 = c := by
    rw [k12 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), r9]
  have s20 : reg n2 20 = hi := by
    rw [k12 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), r20]
  have s34 : Sep (F + 0x34) 1 P condNeg12Code.length := sFC.sub (c := 0x34) (l := 1) (by decide)
  have s38 : Sep (F + 0x38) 4 P condNeg12Code.length := sFC.sub (c := 0x38) (l := 4) (by decide)
  have s3C : Sep (F + 0x3C) 4 P condNeg12Code.length := sFC.sub (c := 0x3C) (l := 4) (by decide)
  obtain ⟨n3, c3, u3⟩ := St.block cnHi u2 hc2 cnHi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, cnHi, and_true]
    rw [sp2]
    exact ⟨s34, ⟨aligned_add hF (k := 0x38) (by decide), s38⟩, aligned_add hF (k := 0x3C) (by decide), s3C⟩)
  simp only [runBlock, BInstr.run, cnHi] at u3
  rw [sp2, s9, u2.zero] at u3
  have hc3 : CodeIn (cnMidMem M F c) P condNeg12Code := ((hc2.store8 s34).store32 s38).store32 s3C
  have g3 : ∀ q, reg n3 q = _ := u3.regs
  have x11 : reg n3 a1 = 2 := by rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc3 0x6A cn_at_68 (by decide) (by rw [x11, u3.self.zero]; decide)
  have k3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n4 q = reg n2 q := fun q h0 h1 h2 h3 => by
    rw [u4.regs, g3]; simp only [upd_app, h0, h1, h2, h3, ite_false]
  refine ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), u4.self, ?_, ?_, ?_, ?_, ?_, fun q h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 => ?_⟩
  · rw [k3 sp (by decide) (by decide) (by decide) (by decide), sp2]
  · rw [u4.regs, g3]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm
  · rw [u4.regs, x11]; rfl
  · rw [u4.regs, g3]; simp +decide only [upd_app, ↓reduceIte]; rw [s20]
    exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [k3 9 (by decide) (by decide) (by decide) (by decide), s9]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u4.self.zero, s.zero]
    rw [k3 q h0 h1 h2 h3, k12 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]

def cnNotKeep (q : Fin 32) : Bool := q.val ∉ [0, 10, 11, 12, 13]

set_option maxRecDepth 20000 in
theorem cnNot_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock cnNot (M, f)).1 = memStore32 M (f a0 + 0) (aluEval .xor (memLoad32 M (f a2 + 0)) 0xFFFFFFFF) ∧
    (runBlock cnNot (M, f)).2 a2 = f a2 + 4 ∧ (runBlock cnNot (M, f)).2 a0 = f a0 + 4 ∧
    (runBlock cnNot (M, f)).2 a1 = f a1 + 0xFFFFFFFF ∧
    ∀ q, cnNotKeep q = true → (runBlock cnNot (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, cnNot, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 4
  have h0 : q.val ≠ 0 := fun e => absurd (show cnNotKeep q = false by unfold cnNotKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl,
    pkeep_ne (r := a3) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem cnNot_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h12 : (f a2 + 0).toNat % 4 = 0) (h10 : (f a0 + 0).toNat % 4 = 0) (hs : Sep (f a0 + 0) 4 base len) :
    BlockOk base len cnNot (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, cnNot, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h12, h10, hs⟩

/-- **One limb of `hi.not()`**, from 0x6A. -/
theorem cn_not_iter {M : Word → BitVec 8} {P B hi : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x6A (reg n)) (hc : CodeIn M P condNeg12Code) (hi2 : i < 2) (hB : B.toNat % 4 = 0)
    (hhi : hi.toNat % 4 = 0) (sC : Sep (B + BitVec.ofNat 32 (4 * i)) 4 P condNeg12Code.length)
    (r10 : reg n a0 = B + BitVec.ofNat 32 (4 * i)) (r12 : reg n a2 = hi + BitVec.ofNat 32 (4 * i))
    (r11 : reg n a1 = BitVec.ofNat 32 (2 - i)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (B + BitVec.ofNat 32 (4 * i))
          (aluEval .xor (memLoad32 M (hi + BitVec.ofNat 32 (4 * i))) 0xFFFFFFFF))
        P n' (if i + 1 < 2 then 0x6A else 0x7A) (reg n') ∧
      reg n' a0 = B + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = hi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a1 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, cnNotKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E12, E10, E11, Ek⟩ := cnNot_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block cnNot s hc cnNot_end
    (cnNot_ok (by rw [r12, add_lit_zero]; exact aligned_add hhi (by omega))
      (by rw [r10, add_lit_zero]; exact aligned_add hB (by omega)) (by rw [r10, add_lit_zero]; exact sC))
  rw [E1, r10, r12, add_lit_zero, add_lit_zero] at u1
  have hc1 := CodeIn.store32 (v := aluEval .xor (memLoad32 M (hi + BitVec.ofNat 32 (4 * i))) 0xFFFFFFFF) hc sC
  have ea1 : reg n1 a1 = BitVec.ofNat 32 (2 - (i + 1)) := by rw [u1.regs, E11, r11, cnt2_dec i hi2]
  have hb : branchTaken .bne (reg n1 a1) (reg n1 x0) = decide (i + 1 < 2) := by
    rw [ea1, u1.self.zero]; exact cnt2_ne i hi2
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a0 = B + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a2 = hi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 a1 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, cnNotKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E10, r10, ptr4], by rw [h2, u1.regs, E12, r12, ptr4], by rw [h2, ea1],
      fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 2
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x6A cn_at_78 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x7A cn_at_78 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- `!hi`'s two words in the buffer at `B`. -/
abbrev cnNotMem (M : Word → BitVec 8) (B hi : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 M B (aluEval .xor (memLoad32 M hi) 0xFFFFFFFF)) (B + 4)
    (aluEval .xor (memLoad32 M (hi + 4)) 0xFFFFFFFF)

/-- **`hi.not()`**, from 0x6A to 0x7A. -/
theorem cn_not {M : Word → BitVec 8} {P B hi : Word} {n : Machine}
    (s : St M P n 0x6A (reg n)) (hc : CodeIn M P condNeg12Code) (hB : B.toNat % 4 = 0) (hhi : hi.toNat % 4 = 0)
    (sC : Sep B 8 P condNeg12Code.length) (sH : Sep B 8 hi 8)
    (r10 : reg n a0 = B + BitVec.ofNat 32 (4 * 0)) (r12 : reg n a2 = hi + BitVec.ofNat 32 (4 * 0))
    (r11 : reg n a1 = BitVec.ofNat 32 (2 - 0)) :
    ∃ n', Steps n n' ∧ St (cnNotMem M B hi) P n' 0x7A (reg n') ∧ CodeIn (cnNotMem M B hi) P condNeg12Code ∧
      ∀ q, cnNotKeep q = true → reg n' q = reg n q := by
  have sC0 : Sep (B + BitVec.ofNat 32 (4 * 0)) 4 P condNeg12Code.length := sC.sub (by decide)
  obtain ⟨n1, c1, u1, e10, e12, e11, k1⟩ := cn_not_iter (i := 0) s hc (by decide) hB hhi sC0 r10 r12 r11
  rw [show (if 0 + 1 < 2 then 0x6A else 0x7A : Nat) = 0x6A from rfl] at u1
  have hc1 := CodeIn.store32 (v := aluEval .xor (memLoad32 M (hi + BitVec.ofNat 32 (4 * 0))) 0xFFFFFFFF) hc sC0
  have sC1 : Sep (B + BitVec.ofNat 32 (4 * 1)) 4 P condNeg12Code.length := sC.sub (by decide)
  obtain ⟨n2, c2, u2, -, -, -, k2⟩ := cn_not_iter (i := 1) u1 hc1 (by decide) hB hhi sC1 e10 e12 e11
  rw [show (if 1 + 1 < 2 then 0x6A else 0x7A : Nat) = 0x7A from rfl] at u2
  have hl1 : memLoad32 (memStore32 M (B + BitVec.ofNat 32 (4 * 0))
      (aluEval .xor (memLoad32 M (hi + BitVec.ofNat 32 (4 * 0))) 0xFFFFFFFF)) (hi + BitVec.ofNat 32 (4 * 1)) =
      memLoad32 M (hi + 4) :=
    memLoad32_store32_sep ((sH.sub (c := 0) (l := 4) (by decide)).subR (c := 4) (l := 4) (by decide))
  rw [hl1, u2_slot0, u2_slot0, u2_slot1'] at u2
  rw [u2_slot1'] at sC1
  rw [u2_slot0, u2_slot0] at hc1
  exact ⟨n2, c1.trans c2, u2, hc1.store32 (v := aluEval .xor (memLoad32 M (hi + 4)) 0xFFFFFFFF) sC1, fun q hq => by rw [k2 q hq, k1 q hq]⟩

/-- A call from the function to `Uint<2>::select` at `P + 0x110`. -/
theorem cn_callSel2 {M : Word → BitVec 8} {P F out ap bp c : Word} {n : Machine} {off : Nat} {imm o : Word}
    (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P condNeg12Code)
    (hs2 : CodeIn M (P + 0x110) uintSelect2Code)
    (h1 : fetchRel condNeg12Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel condNeg12Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x110) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = F) (r10 : reg n a0 = out) (r11 : reg n a1 = ap) (r12 : reg n a2 = bp) (r13 : reg n a3 = c)
    (hcc : c = 0 ∨ c = 1) (hF : F.toNat % 4 = 0) (h16 : 16 ≤ F.toNat) (hap : ap.toNat % 4 = 0)
    (hbp : bp.toNat % 4 = 0) (hout : out.toNat % 4 = 0)
    (sFC : Sep (F + 0xFFFFFFF0) 16 (P + 0x110) uintSelect2Code.length)
    (sOC : Sep out 8 (P + 0x110) uintSelect2Code.length)
    (sAF : Sep ap 8 (F + 0xFFFFFFF0) 16) (sBF : Sep bp 8 (F + 0xFFFFFFF0) 16) :
    ∃ n', Steps n n' ∧ St n'.mem P n' (off + 8) (reg n') ∧ reg n' sp = F ∧
      (∀ q, q.val ∉ [1, 5, 6, 7, 11, 12, 14, 15, 16, 17] → reg n' q = reg n q) ∧
      (∀ i, i < 2 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))) ∧
      ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep out 8 x 1 → n'.mem x = M x := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb (even_at P hP 0x110 (by decide))
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, sp2, k2, w2, f2⟩ := uintSelect2_correct m1 (by rw [mem1]; exact hs2) pc1
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), r10]) (by rw [r1 a1 (by decide), r11])
    (by rw [r1 a2 (by decide), r12]) (by rw [r1 a3 (by decide), r13]) hcc
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) hF h16 hap hbp hout sFC sOC sAF sBF
  rw [mem1] at w2 f2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, ?_, fun q hq => ?_, w2, f2⟩
  · exact sp2
  · have hr : q ≠ ra := fun e => hq (by rw [e]; decide)
    rw [k2 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)), r1 q hr]

theorem u2_data_word {M : Word → BitVec 8} {a : Nat} {d : List Nat} (h : CodeIn M (BitVec.ofNat 32 a) d)
    (ha : a + d.length < 2 ^ 32) (i : Nat) (hi : 4 * i + 4 ≤ d.length) :
    memLoad32 M (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i)) =
      memLoad32 (fun x => byteAt d (x - BitVec.ofNat 32 a).toNat) (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i)) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc, h _ (by omega), add_sub_toNat _ (by omega)]

/-- `Uint<2>::select(ZERO, ONE, c)`'s words, for `c` 0 or 1: `c`, then 0. -/
theorem u2_sel_words {M : Word → BitVec 8} (hz : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData)
    (ho : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData) {c : Word} (hcc : c = 0 ∨ c = 1) :
    (if c = 1 then memLoad32 M (BitVec.ofNat 32 u2OneAddress + BitVec.ofNat 32 (4 * 0))
      else memLoad32 M (BitVec.ofNat 32 u2ZeroAddress + BitVec.ofNat 32 (4 * 0))) = c ∧
    (if c = 1 then memLoad32 M (BitVec.ofNat 32 u2OneAddress + BitVec.ofNat 32 (4 * 1))
      else memLoad32 M (BitVec.ofNat 32 u2ZeroAddress + BitVec.ofNat 32 (4 * 1))) = 0 := by
  rw [u2_data_word hz (by decide) 0 (by decide), u2_data_word hz (by decide) 1 (by decide),
    u2_data_word ho (by decide) 0 (by decide), u2_data_word ho (by decide) 1 (by decide)]
  rcases hcc with rfl | rfl <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From 0x7A to 0x9A: `Uint<2>::select(ZERO, ONE, carry)` into `F + 0x48`,
so the buffer holds the carry as a `Uint<2>`. -/
theorem cn_sel1 {M : Word → BitVec 8} {P F c : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x7A (reg n)) (hc : CodeIn M P condNeg12Code) (hs2 : CodeIn M (P + 0x110) uintSelect2Code)
    (hz : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData) (ho : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData)
    (hcc : c = 0 ∨ c = 1) (hF : F.toNat % 4 = 0) (h16 : 16 ≤ F.toNat)
    (sFC : Sep (F + 0xFFFFFFF0) 16 (P + 0x110) uintSelect2Code.length)
    (sOC : Sep (F + 0x48) 8 (P + 0x110) uintSelect2Code.length)
    (sZF : Sep (BitVec.ofNat 32 u2ZeroAddress) 8 (F + 0xFFFFFFF0) 16)
    (sOF : Sep (BitVec.ofNat 32 u2OneAddress) 8 (F + 0xFFFFFFF0) 16)
    (rsp : reg n sp = F) (r9 : reg n 9 = c) :
    ∃ n', Steps n n' ∧ St n'.mem P n' 0x9A (reg n') ∧ reg n' sp = F ∧ reg n' 9 = F + 0x48 ∧
      memLoad32 n'.mem (F + 0x48) = c ∧ memLoad32 n'.mem (F + 0x48 + 4) = 0 ∧
      (∀ q, q.val ∉ [1, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17] → reg n' q = reg n q) ∧
      ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep (F + 0x48) 8 x 1 → n'.mem x = M x := by
  obtain ⟨n1, c1, u1⟩ := St.block cnSel1 s hc cnSel1_end (by simp [BlockOk, BInstr.ok, cnSel1])
  simp only [runBlock, BInstr.run, cnSel1] at u1
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  have hand : aluEval .and c 0xFF = c := by rcases hcc with rfl | rfl <;> rfl
  obtain ⟨n2, c2, u2, sp2, k2, w2, f2⟩ := cn_callSel2 (out := F + 0x48) (ap := BitVec.ofNat 32 u2ZeroAddress)
    (bp := BitVec.ofNat 32 u2OneAddress) (c := c) hP u1.self hc hs2 cn_at_92 cn_at_96
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x92 + 8) (by decide))
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; exact rsp)
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; try rfl)
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; try rfl)
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; rw [r9]; exact hand)
    hcc hF h16 (by decide) (by decide) (aligned_add hF (k := 0x48) (by decide)) sFC sOC sZF sOF
  obtain ⟨wc, w0⟩ := u2_sel_words hz ho hcc
  have k1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (9 : Fin 32) → reg n1 q = reg n q :=
    fun q h0 h1 h2 h3 h4 h5 => by rw [g1]; simp only [upd_app, h0, h1, h2, h3, h4, h5, ite_false]
  refine ⟨n2, c1.trans c2, u2, sp2, ?_, ?_, ?_, fun q hq => ?_, f2⟩
  · rw [k2 9 (by decide), g1]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl
  · have := w2 0 (by decide); rw [wc, u2_slot0] at this; exact this
  · have := w2 1 (by decide); rw [w0, u2_slot1'] at this; exact this
  · have hm : ∀ v, v ∈ [1, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17] → q.val ≠ v := fun v hv e => hq (e ▸ hv)
    have ne : ∀ v : Fin 32, v.val ∈ [1, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17] → q ≠ v :=
      fun v hv e => hm _ hv (e ▸ rfl)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u2.zero, s.zero]
    rw [k2 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)),
      k1 q h0 (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)) (ne 9 (by decide))]

def cnAddKeep (q : Fin 32) : Bool := q.val ∉ [0, 9, 10, 11, 12, 13, 14, 15]

/-- One limb of the add: the sum word and the carry out, for carry in `k`,
limbs `x` of `!hi` and `y` of the selected carry. -/
abbrev addT (k x : Word) : Word := aluEval .add k x
abbrev addV (k x y : Word) : Word := aluEval .add y (addT k x)
abbrev addK (k x y : Word) : Word :=
  aluEval .add (aluEval .sltu (addV k x y) (addT k x)) (aluEval .sltu (addT k x) x)

set_option maxRecDepth 20000 in
theorem cnAdd_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock cnAdd (M, f)).1 = memStore32 M (f a2 + 0)
      (addV (f a1) (memLoad32 M (f a0 + 0)) (memLoad32 M (f 9 + 0))) ∧
    (runBlock cnAdd (M, f)).2 a1 = addK (f a1) (memLoad32 M (f a0 + 0)) (memLoad32 M (f 9 + 0)) ∧
    (runBlock cnAdd (M, f)).2 a0 = f a0 + 4 ∧ (runBlock cnAdd (M, f)).2 9 = f 9 + 4 ∧
    (runBlock cnAdd (M, f)).2 a2 = f a2 + 4 ∧ (runBlock cnAdd (M, f)).2 a3 = f a3 + 0xFFFFFFFF ∧
    ∀ q, cnAddKeep q = true → (runBlock cnAdd (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, cnAdd, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 6
  have h0 : q.val ≠ 0 := fun e => absurd (show cnAddKeep q = false by unfold cnAddKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
    pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl, pkeep_ne (r := a4) hq rfl, pkeep_ne (r := a5) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem cnAdd_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h10 : (f a0 + 0).toNat % 4 = 0) (h9 : (f 9 + 0).toNat % 4 = 0) (h12 : (f a2 + 0).toNat % 4 = 0)
    (hs : Sep (f a2 + 0) 4 base len) : BlockOk base len cnAdd (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, cnAdd, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h10, h9, h12, hs⟩

theorem add_limb (k x y : Word) (hk : k.toNat ≤ 1) :
    (addV k x y).toNat + 2 ^ 32 * (addK k x y).toNat = x.toNat + y.toNat + k.toNat ∧ (addK k x y).toNat ≤ 1 := by
  show (aluEval .add y (aluEval .add k x)).toNat + 2 ^ 32 * (aluEval .add
      (aluEval .sltu (aluEval .add y (aluEval .add k x)) (aluEval .add k x)) (aluEval .sltu (aluEval .add k x) x)).toNat =
      _ ∧ (aluEval .add (aluEval .sltu (aluEval .add y (aluEval .add k x)) (aluEval .add k x))
        (aluEval .sltu (aluEval .add k x) x)).toNat ≤ 1
  have e1 := add_carry k x
  have e2 := add_carry y (aluEval .add k x)
  have l1 := sltu_le1 (aluEval .add k x) x
  have l2 := sltu_le1 (aluEval .add y (aluEval .add k x)) (aluEval .add k x)
  rw [add_small l2 l1]
  generalize aluEval .sltu (aluEval .add y (aluEval .add k x)) (aluEval .add k x) = c2 at e2 l2 ⊢
  generalize aluEval .sltu (aluEval .add k x) x = c1 at e1 l1 ⊢
  generalize aluEval .add y (aluEval .add k x) = v at e2 ⊢
  generalize aluEval .add k x = t at e1 e2 ⊢
  have hy := y.isLt
  have hx := x.isLt
  have hv := v.isLt
  have ht := t.isLt
  exact ⟨by omega, by omega⟩

/-- **One limb of `wrapping_add`**, from 0xA8: the sum of limb `i` of the
buffers at `N` and `S` and the carry `k`, to the buffer at `D`. -/
theorem cn_add_iter {M : Word → BitVec 8} {P N S D k : Word} {n : Machine} {i : Nat}
    (s : St M P n 0xA8 (reg n)) (hc : CodeIn M P condNeg12Code) (hi2 : i < 2) (hN : N.toNat % 4 = 0)
    (hS : S.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (sC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P condNeg12Code.length)
    (r10 : reg n a0 = N + BitVec.ofNat 32 (4 * i)) (r9 : reg n 9 = S + BitVec.ofNat 32 (4 * i))
    (r12 : reg n a2 = D + BitVec.ofNat 32 (4 * i)) (r13 : reg n a3 = BitVec.ofNat 32 (2 - i)) (r11 : reg n a1 = k) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (D + BitVec.ofNat 32 (4 * i))
          (addV k (memLoad32 M (N + BitVec.ofNat 32 (4 * i))) (memLoad32 M (S + BitVec.ofNat 32 (4 * i)))))
        P n' (if i + 1 < 2 then 0xA8 else 0xC6) (reg n') ∧
      reg n' a1 = addK k (memLoad32 M (N + BitVec.ofNat 32 (4 * i))) (memLoad32 M (S + BitVec.ofNat 32 (4 * i))) ∧
      reg n' a0 = N + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 9 = S + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a2 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a3 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, cnAddKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E11, E10, E9, E12, E13, Ek⟩ := cnAdd_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block cnAdd s hc cnAdd_end
    (cnAdd_ok (by rw [r10, add_lit_zero]; exact aligned_add hN (by omega))
      (by rw [r9, add_lit_zero]; exact aligned_add hS (by omega))
      (by rw [r12, add_lit_zero]; exact aligned_add hD (by omega)) (by rw [r12, add_lit_zero]; exact sC))
  rw [E1, r10, r9, r12, r11, add_lit_zero, add_lit_zero, add_lit_zero] at u1
  rw [r10, r9, r11, add_lit_zero, add_lit_zero] at E11
  have hc1 := CodeIn.store32 (v := addV k (memLoad32 M (N + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (S + BitVec.ofNat 32 (4 * i)))) hc sC
  have ea3 : reg n1 a3 = BitVec.ofNat 32 (2 - (i + 1)) := by rw [u1.regs, E13, r13, cnt2_dec i hi2]
  have hb : branchTaken .bne (reg n1 a3) (reg n1 x0) = decide (i + 1 < 2) := by
    rw [ea3, u1.self.zero]; exact cnt2_ne i hi2
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a1 = addK k (memLoad32 M (N + BitVec.ofNat 32 (4 * i))) (memLoad32 M (S + BitVec.ofNat 32 (4 * i))) ∧
      reg n2 a0 = N + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 9 = S + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 a2 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a3 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, cnAddKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E11], by rw [h2, u1.regs, E10, r10, ptr4], by rw [h2, u1.regs, E9, r9, ptr4],
      by rw [h2, u1.regs, E12, r12, ptr4], by rw [h2, ea3], fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 2
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0xA8 cn_at_c4 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0xC6 cn_at_c4 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From 0x9A to 0xC6: `!hi` at `F + 0x38` plus the selected carry at
`F + 0x48`, to `F + 0x40`. -/
theorem cn_add {M : Word → BitVec 8} {P F : Word} {n : Machine}
    (s : St M P n 0x9A (reg n)) (hc : CodeIn M P condNeg12Code) (hF : F.toNat % 4 = 0)
    (sFC : Sep F 0x90 P condNeg12Code.length)
    (rsp : reg n sp = F) (r9 : reg n 9 = F + 0x48) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0xC6 (reg n') ∧ CodeIn M' P condNeg12Code ∧
      (∀ x, Sep (F + 0x40) 8 x 1 → M' x = M x) ∧
      (memLoad32 M' (F + 0x40)).toNat + 2 ^ 32 * (memLoad32 M' (F + 0x40 + 4)).toNat + 2 ^ 64 * (reg n' a1).toNat =
        (memLoad32 M (F + 0x38)).toNat + 2 ^ 32 * (memLoad32 M (F + 0x38 + 4)).toNat +
          ((memLoad32 M (F + 0x48)).toNat + 2 ^ 32 * (memLoad32 M (F + 0x48 + 4)).toNat) ∧
      reg n' sp = F ∧ ∀ q, q.val ∉ [9, 10, 11, 12, 13, 14, 15] → reg n' q = reg n q := by
  have s40 : Sep (F + 0x40) 4 P condNeg12Code.length := sFC.sub (c := 0x40) (l := 4) (by decide)
  have s44 : Sep (F + 0x40 + 4) 4 P condNeg12Code.length := by
    rw [BitVec.add_assoc]; exact sFC.sub (c := 0x44) (l := 4) (by decide)
  have e44 : F + 0x44 = F + 0x40 + 4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n1, c1, u1⟩ := St.block cnAddInit s hc cnAddInit_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, cnAddInit, upd_app, ↓reduceIte, and_true, true_and]
    rw [rsp, e44]
    exact ⟨⟨aligned_add hF (k := 0x40) (by decide), s40⟩, aligned_add (aligned_add hF (k := 0x40) (by decide))
      (k := 4) (by decide), s44⟩)
  simp only [runBlock, BInstr.run, cnAddInit] at u1
  simp +decide only [upd_app, ↓reduceIte] at u1
  rw [rsp, e44] at u1
  obtain ⟨Mi, hMi⟩ : ∃ Mi, memStore32 (memStore32 M (F + 0x40) 0) (F + 0x40 + 4) 0 = Mi := ⟨_, rfl⟩
  rw [hMi] at u1
  have hc1 : CodeIn Mi P condNeg12Code := by rw [← hMi]; exact (hc.store32 s40).store32 s44
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  have x13 : reg n1 a3 = 2 := by rw [g1]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0xA8 cn_at_a6 (by decide) (by rw [x13, u1.self.zero]; decide)
  have k1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n2 q = reg n q := fun q h0 h1 h2 h3 h4 => by
    rw [u2.regs, g1]; simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  have hN : (F + 0x38).toNat % 4 = 0 := aligned_add hF (k := 0x38) (by decide)
  have hS : (F + 0x48).toNat % 4 = 0 := aligned_add hF (k := 0x48) (by decide)
  have hD : (F + 0x40).toNat % 4 = 0 := aligned_add hF (k := 0x40) (by decide)
  have sC0 : Sep (F + 0x40 + BitVec.ofNat 32 (4 * 0)) 4 P condNeg12Code.length := by rw [u2_slot0]; exact s40
  obtain ⟨n3, c3, u3, e11, e10, e9, e12, e13, k3⟩ := cn_add_iter (i := 0) (N := F + 0x38) (S := F + 0x48)
    (D := F + 0x40) (k := 0) u2.self hc1 (by decide) hN hS hD sC0
    (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm)
    (by rw [k1 9 (by decide) (by decide) (by decide) (by decide) (by decide), r9]; exact (add_ofNat_zero _).symm)
    (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm)
    (by rw [u2.regs, x13]; rfl)
    (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte, aluEval]; try rfl)
  rw [show (if 0 + 1 < 2 then 0xA8 else 0xC6 : Nat) = 0xA8 from rfl, u2_slot0, u2_slot0, u2_slot0] at u3
  rw [u2_slot0, u2_slot0] at e11
  have sC1 : Sep (F + 0x40 + BitVec.ofNat 32 (4 * 1)) 4 P condNeg12Code.length := s44
  have hc3 := hc1.store32 (v := addV 0 (memLoad32 Mi (F + 0x38)) (memLoad32 Mi (F + 0x48))) s40
  obtain ⟨n4, c4, u4, e11', -, -, -, -, k4⟩ := cn_add_iter (i := 1) u3 hc3 (by decide) hN hS hD sC1 e10 e9 e12 e13 e11
  rw [show (if 1 + 1 < 2 then 0xA8 else 0xC6 : Nat) = 0xC6 from rfl, u2_slot1', u2_slot1', u2_slot1'] at u4
  rw [u2_slot1', u2_slot1'] at e11'
  -- the stores to `F + 0x40` leave `F + 0x38` and `F + 0x48` alone
  have sp4 : ∀ (a b : Word) (ka kb : Nat), a = F + BitVec.ofNat 32 ka → b = F + BitVec.ofNat 32 kb →
      ka + 4 ≤ kb ∨ kb + 4 ≤ ka → ka + 4 ≤ 0x90 → kb + 4 ≤ 0x90 → Sep a 4 b 4 := fun a b ka kb ha hb h h1 h2 => by
    rw [ha, hb]; exact sep_offsets F h (by omega) (by omega)
  have lMi : ∀ (b : Word) (kb : Nat), b = F + BitVec.ofNat 32 kb → kb + 4 ≤ 0x40 ∨ 0x48 ≤ kb → kb + 4 ≤ 0x90 →
      memLoad32 Mi b = memLoad32 M b := fun b kb hb h h2 => by
    have hs1 : Sep (F + 0x40 + 4) 4 b 4 := sp4 _ _ 0x44 kb (by rw [BitVec.add_assoc]; rfl) hb (by omega)
      (by decide) h2
    have hs0 : Sep (F + 0x40) 4 b 4 := sp4 _ _ 0x40 kb rfl hb (by omega) (by decide) h2
    rw [← hMi, memLoad32_store32_sep hs1, memLoad32_store32_sep hs0]
  have st0 : ∀ (b : Word) (kb : Nat) (v : Word), b = F + BitVec.ofNat 32 kb → kb + 4 ≤ 0x40 ∨ 0x48 ≤ kb →
      kb + 4 ≤ 0x90 → memLoad32 (memStore32 Mi (F + 0x40) v) b = memLoad32 M b := fun b kb v hb h h2 => by
    have hs0 : Sep (F + 0x40) 4 b 4 := sp4 _ _ 0x40 kb rfl hb (by omega) (by decide) h2
    rw [memLoad32_store32_sep hs0, lMi b kb hb h h2]
  have l1 := st0 (F + 0x38 + 4) 0x3C (addV 0 (memLoad32 Mi (F + 0x38)) (memLoad32 Mi (F + 0x48)))
    (by rw [BitVec.add_assoc]; rfl) (by decide) (by decide)
  have l2 := st0 (F + 0x48 + 4) 0x4C (addV 0 (memLoad32 Mi (F + 0x38)) (memLoad32 Mi (F + 0x48)))
    (by rw [BitVec.add_assoc]; rfl) (by decide) (by decide)
  rw [l1, l2] at u4 e11'
  have l3 : memLoad32 Mi (F + 0x38) = memLoad32 M (F + 0x38) := lMi _ 0x38 rfl (by decide) (by decide)
  have l4 : memLoad32 Mi (F + 0x48) = memLoad32 M (F + 0x48) := lMi _ 0x48 rfl (by decide) (by decide)
  rw [l3, l4] at u4 e11 e11' hc3
  obtain ⟨a0v, a0k⟩ := add_limb 0 (memLoad32 M (F + 0x38)) (memLoad32 M (F + 0x48)) (by decide)
  obtain ⟨a1v, -⟩ := add_limb (addK 0 (memLoad32 M (F + 0x38)) (memLoad32 M (F + 0x48)))
    (memLoad32 M (F + 0x38 + 4)) (memLoad32 M (F + 0x48 + 4)) a0k
  have s0' : Sep (F + 0x40 + 4) 4 (F + 0x40) 4 := sp4 _ _ 0x44 0x40 (by rw [BitVec.add_assoc]; rfl) rfl
    (by decide) (by decide) (by decide)
  have z0 : (0 : Word).toNat = 0 := rfl
  refine ⟨n4, _, c1.trans (.cons d2 (c3.trans c4)), u4, hc3.store32 s44, fun x hx => ?_, ?_, ?_, fun q hq => ?_⟩
  · have h1 : Sep (F + 0x40 + 4) 4 x 1 := hx.sub (c := 4) (l := 4) (by decide)
    have h0 : Sep (F + 0x40) 4 x 1 := by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep h1, memStore32_get_sep h0, ← hMi, memStore32_get_sep h1, memStore32_get_sep h0]
  · rw [memLoad32_store32_sep s0', memLoad32_store32_same, memLoad32_store32_same, e11']
    rw [z0] at a0v
    omega
  · rw [k4 sp rfl, k3 sp rfl, k1 sp (by decide) (by decide) (by decide) (by decide) (by decide), rsp]
  · have hm : ∀ v, v ∈ [9, 10, 11, 12, 13, 14, 15] → q.val ≠ v := fun v hv e => hq (e ▸ hv)
    have ne : ∀ v : Fin 32, v.val ∈ [9, 10, 11, 12, 13, 14, 15] → q ≠ v := fun v hv e => hm _ hv (e ▸ rfl)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u4.zero, s.zero]
    have hk : cnAddKeep q = true := by
      unfold cnAddKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq ⊢; omega
    rw [k4 q hk, k3 q hk, k1 q h0 (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide))]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From 0xC6 to 0xD6: `Uint<12>::select(lo, -lo, flag)` into `F + 0x48`. -/
theorem cn_sel12 {M : Word → BitVec 8} {P F lo fl : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0xC6 (reg n)) (hc : CodeIn M P condNeg12Code)
    (hsel : CodeIn M (P + 0xFFFFFAA8) uintSelect12Code) (hms : CodeIn M (P + 0x1426) memsetCode)
    (hst : CodeIn M (P + 0x148E) memcpyStubCode) (hbd : CodeIn M (P + 0x1496) memcpyBodyCode)
    (hF : F.toNat % 4 = 0) (h50 : 0x50 ≤ F.toNat) (hFw : F.toNat + 0x90 ≤ 2 ^ 32) (hlo : lo.toNat % 4 = 0)
    (sRL : Sep (F + 0xFFFFFFB0) 0xE0 (P + 0xFFFFFAA8) uintSelect12Code.length)
    (sRM : Sep (F + 0xFFFFFFB0) 0xE0 (P + 0x1426) memsetCode.length)
    (sRU : Sep (F + 0xFFFFFFB0) 0xE0 (P + 0x148E) memcpyStubCode.length)
    (sRB : Sep (F + 0xFFFFFFB0) 0xE0 (P + 0x1496) memcpyBodyCode.length)
    (sLR : Sep lo 48 (F + 0xFFFFFFB0) 0xE0)
    (rsp : reg n sp = F) (r19 : reg n 19 = lo) (r18 : reg n 18 = fl) (hfl : fl = 0 ∨ fl = 1) :
    ∃ n', Steps n n' ∧ St n'.mem P n' 0xD6 (reg n') ∧ reg n' sp = F ∧
      (∀ i, i < 12 → memLoad32 n'.mem (F + 0x48 + BitVec.ofNat 32 (4 * i)) =
        if fl = 1 then memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * i)) else memLoad32 M (lo + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (F + 0xFFFFFFB0) 0x50 x 1 → Sep (F + 0x48) 48 x 1 → n'.mem x = M x) ∧
      ∀ q, q.val ∉ [1, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17] → reg n' q = reg n q := by
  have hRF : F + 0xFFFFFFB0 + BitVec.ofNat 32 0x50 = F := by rw [BitVec.add_assoc]; exact BitVec.add_zero F
  have toR : ∀ {b : Word} {k : Nat} {c l : Nat}, c + l ≤ 0x90 → Sep (F + 0xFFFFFFB0) 0xE0 b k →
      Sep (F + BitVec.ofNat 32 c) l b k := fun h hs => by
    rw [← hRF, add_ofNat_assoc]; exact hs.sub (by omega)
  have toS : ∀ {b : Word} {k : Nat}, Sep (F + 0xFFFFFFB0) 0xE0 b k → Sep (F + 0xFFFFFFB0) 0x50 b k := fun h => by
    have := h.sub (c := 0) (l := 0x50) (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨n1, c1, u1⟩ := St.block cnSel12 s hc cnSel12_end (by simp [BlockOk, BInstr.ok, cnSel12])
  simp only [runBlock, BInstr.run, cnSel12] at u1
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u1.self.callRa hc cn_at_ce cn_at_d2 (cb := P + 0xFFFFFAA8)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP 0xFFFFFAA8 (by decide))
  have r6 := PEnv.reg1 regs6 u1.self.zero
  have sp6 : reg m6 sp = F := by
    rw [r6 _ (by decide), g1]; simp +decide only [upd_app, ↓reduceIte]; exact rsp
  have eM : P + 0xFFFFFAA8 + 0x197E = P + 0x1426 := by rw [BitVec.add_assoc]; rfl
  have eU : P + 0xFFFFFAA8 + 0x19E6 = P + 0x148E := by rw [BitVec.add_assoc]; rfl
  have eB : P + 0xFFFFFAA8 + 0x19EE = P + 0x1496 := by rw [BitVec.add_assoc]; rfl
  have SE : SelEnv m6.mem (P + 0xFFFFFAA8) (reg m6 sp) (F + 0x48) lo (F + 4) := by
    rw [mem6, sp6]
    refine ⟨even_at P hP 0xFFFFFAA8 (by decide), hsel, by rw [eM]; exact hms, by rw [eU]; exact hst,
      by rw [eB]; exact hbd, hF, h50, aligned_add hF (k := 0x48) (by decide), hlo, aligned_add hF (k := 4) (by decide),
      by rw [BitVec.toNat_add]; have : (0x48 : Word).toNat = 0x48 := rfl; rw [this]; omega,
      toS sRL, by rw [eM]; exact toS sRM, by rw [eU]; exact toS sRU, by rw [eB]; exact toS sRB, ?_,
      (toR (c := 0x48) (l := 48) (by decide) sRL), by rw [eB]; exact toR (c := 0x48) (l := 48) (by decide) sRB,
      (toS sLR.symm).symm, ?_⟩
    · have := sep_offsets (F + 0xFFFFFFB0) (c := 0x98) (n := 48) (d := 0) (k := 0x50) (.inr (by decide)) (by decide)
        (by decide)
      have e1 : F + 0xFFFFFFB0 + BitVec.ofNat 32 0x98 = F + 0x48 := by rw [BitVec.add_assoc]; rfl
      rw [add_ofNat_zero, e1] at this; exact this
    · have := sep_offsets (F + 0xFFFFFFB0) (c := 0x54) (n := 48) (d := 0) (k := 0x50) (.inr (by decide)) (by decide)
        (by decide)
      have e1 : F + 0xFFFFFFB0 + BitVec.ofNat 32 0x54 = F + 4 := by rw [BitVec.add_assoc]; rfl
      rw [add_ofNat_zero, e1] at this; exact this
  obtain ⟨m7, c7, pc7, sp7, w7, mem7, k7⟩ := uintSelect12_correct m6 SE pc6
    (by rw [r6 _ (by decide), g1]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r6 _ (by decide), g1]; simp +decide only [upd_app, ↓reduceIte]; rw [r19]; exact BitVec.zero_add _)
    (by rw [r6 _ (by decide), g1]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r6 _ (by decide), g1]; simp +decide only [upd_app, ↓reduceIte]; rw [r18]; exact BitVec.zero_add _)
    hfl (by rw [regs6]; simp +decide [upd]) (even_clear _ (even_at P hP (0xCE + 8) (by decide)))
  rw [sp6] at mem7 sp7
  rw [mem6] at w7 mem7
  have k1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n1 q = reg n q := fun q h0 h1 h2 h3 h4 => by
    rw [g1]; simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  refine ⟨m7, c1.trans (c6.trans c7), ⟨pc7, rfl, fun _ => rfl⟩, sp7, ?_, mem7, fun q hq => ?_⟩
  · intro i hi; rw [w7 i hi]
  · have ne : ∀ v : Fin 32, v.val ∈ [1, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17] → q ≠ v :=
      fun v hv e => hq (e ▸ hv)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg m7 0 = 0 from rfl).trans (show reg n 0 = 0 from rfl).symm
    have hk : selKeep q = true := by
      unfold selKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq ⊢; omega
    rw [k7 q hk, r6 q (ne ra (by decide)), k1 q h0 (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide))
      (ne a3 (by decide))]

theorem add0_ev (x : Word) : aluEval .add 0 x = x := BitVec.zero_add x

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From 0xD6 to 0xE6: copy the selected low part to `lo`. -/
theorem cn_cpy2 {M : Word → BitVec 8} {P F lo : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0xD6 (reg n)) (hc : CodeIn M P condNeg12Code) (hst : CodeIn M (P + 0x148E) memcpyStubCode)
    (hbd : CodeIn M (P + 0x1496) memcpyBodyCode) (hF : F.toNat % 4 = 0) (hlo : lo.toNat % 4 = 0)
    (hwl : lo.toNat + 48 < 2 ^ 32) (sLF : Sep lo 48 (F + 0x48) 48) (sLB : Sep lo 48 (P + 0x1496) memcpyBodyCode.length)
    (sLC : Sep lo 48 P condNeg12Code.length) (rsp : reg n sp = F) (r19 : reg n 19 = lo) :
    ∃ n', Steps n n' ∧ St (copyWords M lo (F + 0x48) 12) P n' 0xE6 (reg n') ∧
      CodeIn (copyWords M lo (F + 0x48) 12) P condNeg12Code ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ ra →
        reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block cnCpy2 s hc cnCpy2_end (by simp [BlockOk, BInstr.ok, cnCpy2])
  simp only [runBlock, BInstr.run, cnCpy2] at u1
  have e8 : P + 0x148E + 8 = P + 0x1496 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n2, c2, u2, -, k2⟩ := St.memcpyW (B := P + 0x148E) (w := 12) (dst := lo) (src := F + 0x48)
    (even_at P hP 0x148E (by decide)) u1.self hc hst (by rw [e8]; exact hbd)
    cn_at_de cn_at_e2 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0xDE + 8) (by decide))
    (by decide) (by omega) (by decide) hlo (aligned_add hF (k := 0x48) (by decide)) sLF (by rw [e8]; exact sLB)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r19]; exact BitVec.zero_add _)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  have k1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n1 q = reg n q := fun q h0 h1 h2 h3 => by
    rw [u1.regs]; simp only [upd_app, h0, h1, h2, h3, ite_false]
  refine ⟨n2, c1.trans c2, u2, fun i hi => ?_, fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => ?_⟩
  · rw [copyWords_outside 12 (sLC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n2 0 = 0 from rfl).trans (show reg n 0 = 0 from rfl).symm
    rw [k2 q h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, k1 q h0 h1 h2 h3]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From 0xE6 to the return: `Uint<2>::select(hi, hi_neg, flag)` into
`F + 0x48`, those two words to `hi`, and the epilogue. -/
theorem cn_tail {M : Word → BitVec 8} {P F hi fl : Word} {v : Fin 32 → Word} {n : Machine}
    (hP : P.toNat % 2 = 0) (s : St M P n 0xE6 (reg n)) (hc : CodeIn M P condNeg12Code)
    (hs2 : CodeIn M (P + 0x110) uintSelect2Code) (hF : F.toNat % 4 = 0) (h16 : 16 ≤ F.toNat)
    (hhi : hi.toNat % 4 = 0)
    (sFC : Sep (F + 0xFFFFFFF0) 16 (P + 0x110) uintSelect2Code.length)
    (sOC : Sep (F + 0x48) 8 (P + 0x110) uintSelect2Code.length)
    (sFP : Sep (F + 0xFFFFFFF0) 16 P condNeg12Code.length)
    (sF0 : Sep F 0x90 P condNeg12Code.length)
    (sHF : Sep hi 8 (F + 0xFFFFFFF0) 0xA0) (sHC : Sep hi 8 P condNeg12Code.length)
    (hsl : ∀ r o, (r, o) ∈ cnPs → memLoad32 M (F + o) = v r)
    (rsp : reg n sp = F) (r20 : reg n 20 = hi) (r18 : reg n 18 = fl) (hfl : fl = 0 ∨ fl = 1) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧ reg n' sp = F + 0x90 ∧
      (∀ r o, (r, o) ∈ cnPs → reg n' r = v r) ∧
      (∀ q, q.val ∉ [1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → q ≠ sp → reg n' q = reg n q) ∧
      (∀ i, i < 2 → memLoad32 n'.mem (hi + BitVec.ofNat 32 (4 * i)) =
        if fl = 1 then memLoad32 M (F + 0x40 + BitVec.ofNat 32 (4 * i)) else memLoad32 M (hi + BitVec.ofNat 32 (4 * i))) ∧
      ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep (F + 0x48) 8 x 1 → Sep hi 8 x 1 → n'.mem x = M x := by
  have hF16 : F + 0xFFFFFFF0 + BitVec.ofNat 32 16 = F := by rw [BitVec.add_assoc]; exact BitVec.add_zero F
  obtain ⟨n1, c1, u1⟩ := St.block cnSel2 s hc cnSel2_end (by simp [BlockOk, BInstr.ok, cnSel2])
  simp only [runBlock, BInstr.run, cnSel2] at u1
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  have sHF16 : Sep hi 8 (F + 0xFFFFFFF0) 16 := sHF.subR (c := 0) (l := 16) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  have s40F : Sep (F + 0x40) 8 (F + 0xFFFFFFF0) 16 := by
    have := sep_offsets (F + 0xFFFFFFF0) (c := 0x50) (n := 8) (d := 0) (k := 16) (.inr (by decide)) (by decide)
      (by decide)
    have e1 : F + 0xFFFFFFF0 + BitVec.ofNat 32 0x50 = F + 0x40 := by rw [BitVec.add_assoc]; rfl
    rw [add_ofNat_zero, e1] at this; exact this
  obtain ⟨n2, c2, u2, sp2, k2, w2, f2⟩ := cn_callSel2 (out := F + 0x48) (ap := hi) (bp := F + 0x40) (c := fl)
    hP u1.self hc hs2 cn_at_ee cn_at_f2 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at P hP (0xEE + 8) (by decide))
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; exact rsp)
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; rw [r20]; exact BitVec.zero_add _)
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [g1]; simp +decide only [upd_app, ↓reduceIte]; rw [r18]; exact BitVec.zero_add _)
    hfl hF h16 hhi (aligned_add hF (k := 0x40) (by decide)) (aligned_add hF (k := 0x48) (by decide)) sFC sOC
    sHF16 s40F
  have k1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n1 q = reg n q := fun q h0 h1 h2 h3 h4 => by
    rw [g1]; simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  have k12 : ∀ q, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17] → reg n2 q = reg n q := fun q hq => by
    have ne : ∀ w : Fin 32, w.val ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17] → q ≠ w :=
      fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n2 0 = 0 from rfl).trans (show reg n 0 = 0 from rfl).symm
    rw [k2 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)),
      k1 q h0 (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide))]
  -- the memory after the select: the frame below `F` and `F + 0x48` change
  have frm2 : ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep (F + 0x48) 8 x 1 → n2.mem x = M x := f2
  have hc2 : CodeIn n2.mem P condNeg12Code := fun i hi => by
    rw [f2 _ (sFP.subR (c := i) (l := 1) (by omega)) ((sF0.sub (c := 0x48) (l := 8) (by decide)).subR (c := i)
      (l := 1) (by omega))]
    exact hc i hi
  have sp2' : reg n2 sp = F := sp2
  have r20' : reg n2 20 = hi := by rw [k12 20 (by decide), r20]
  have sH0 : Sep hi 4 P condNeg12Code.length := by
    have := sHC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have sH4 : Sep (hi + 4) 4 P condNeg12Code.length := sHC.sub (c := 4) (l := 4) (by decide)
  obtain ⟨n3, c3, u3⟩ := St.block cnStore u2 hc2 cnStore_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, cnStore, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp2', r20', add0_ev]
    exact ⟨aligned_add hF (k := 0x48) (by decide), aligned_add hF (k := 0x4C) (by decide),
      ⟨by rw [add_lit_zero]; exact hhi, by rw [add_lit_zero]; exact sH0⟩, aligned_add hhi (k := 4) (by decide), sH4⟩)
  simp only [runBlock, BInstr.run, cnStore] at u3
  simp +decide only [upd_app, ↓reduceIte] at u3
  rw [sp2', r20', add_lit_zero, add0_ev] at u3
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore32 n2.mem hi (memLoad32 n2.mem (F + 0x48))) (hi + 4)
      (memLoad32 n2.mem (F + 0x4C)) = M3 := ⟨_, rfl⟩
  rw [hM3] at u3
  have hc3 : CodeIn M3 P condNeg12Code := by rw [← hM3]; exact (hc2.store32 sH0).store32 sH4
  -- the saved registers, past the select's frame and `F + 0x48`, and apart from `hi`
  have hsl3 : ∀ r o, (r, o) ∈ cnPs → memLoad32 M3 (F + o) = v r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := cnPs_range (r, o) h
    dsimp only at ho1 ho2
    have e : F + o = F + BitVec.ofNat 32 o.toNat := by rw [ofNat_toNat_self]
    have e2 : F + o = F + 0xFFFFFFF0 + BitVec.ofNat 32 (16 + o.toNat) := by
      rw [← add_ofNat_assoc, hF16, ofNat_toNat_self]
    have sHo : Sep hi 8 (F + o) 4 := by
      rw [e2]; exact sHF.subR (by omega)
    have sFo : Sep (F + 0xFFFFFFF0) 16 (F + o) 4 := by
      rw [e2]
      have := sep_offsets (F + 0xFFFFFFF0) (c := 0) (n := 16) (d := 16 + o.toNat) (k := 4) (.inl (by omega))
        (by decide) (by omega)
      rwa [add_ofNat_zero] at this
    have s48o : Sep (F + 0x48) 8 (F + o) 4 := by
      rw [e]; exact sep_offsets F (c := 0x48) (.inl (by omega)) (by decide) (by omega)
    have sH4o : Sep (hi + 4) 4 (F + o) 4 := sHo.sub (c := 4) (l := 4) (by decide)
    have sH0o : Sep hi 4 (F + o) 4 := by
      have := sHo.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hM3, memLoad32_store32_sep sH4o, memLoad32_store32_sep sH0o,
      load_frame2 frm2 sFo s48o, hsl r o h]
  have r3sp : reg n3 sp = F := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp2'
  obtain ⟨n4, c4, u4⟩ := St.block (restoreBlock cnPs) u3.self hc3 cnRestore_end
    (restoreBlock_ok M3 _ cnPs (reg n3) r3sp cnPs_sp fun p hp => fr_al' hF (cnPs_range p hp).1)
  simp only [restoreBlock_run M3 _ cnPs (reg n3) r3sp cnPs_sp] at u4
  have rsp4 : restoreRegs M3 F (reg n3) cnPs sp = F := by rw [restoreRegs_sp _ _ _ _ cnPs_sp]; exact r3sp
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc3 cn_at_10c (off' := 0x10E) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc3 cn_at_10e
  have k3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n3 q = reg n2 q := fun q h0 h1 h2 h3 => by
    rw [u3.regs]; simp only [upd_app, h0, h1, h2, h3, ite_false]
  refine ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (.single d6))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, hsl3 ra 0x8C (by decide)]
  · rw [regs6]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp4]; try rfl
  · intro r o h
    rw [regs6]
    simp only [cnPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hsl3 _ _ (by decide)
  · intro q hq hs
    have ne : ∀ w : Fin 32, w.val ∈ [1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → q ≠ w :=
      fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n6 0 = 0 from rfl).trans (show reg n 0 = 0 from rfl).symm
    rw [regs6]
    simp only [upd_app, h0, hs, ite_false]
    simp only [restoreRegs]
    simp only [upd_app, h0, ne ra (by decide), ne 8 (by decide), ne 9 (by decide), ne 18 (by decide),
      ne 19 (by decide), ne 20 (by decide), ite_false]
    rw [k3 q h0 (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide)),
      k12 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega))]
  · intro i hi2
    rw [mem6, ← hM3]
    have sHH : Sep (hi + 4) 4 hi 4 := by
      have := sep_offsets hi (c := 4) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [u2_slot0, memLoad32_store32_sep sHH, memLoad32_store32_same]
      have := w2 0 (by decide); simp only [u2_slot0] at this ⊢; rw [this]
    · rw [u2_slot1', memLoad32_store32_same]
      have := w2 1 (by decide); simp only [u2_slot1'] at this ⊢
      rw [show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl, this]
  · intro x hx h48 hH
    have h4 : Sep (hi + 4) 4 x 1 := hH.sub (c := 4) (l := 4) (by decide)
    have h0 : Sep hi 4 x 1 := by have := hH.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [mem6, ← hM3, memStore32_get_sep h4, memStore32_get_sep h0, frm2 x hx h48]

theorem cnF16 (sp0 : Word) : cnF sp0 + 0xFFFFFFF0 = cnR sp0 + BitVec.ofNat 32 0x40 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem cnFR (sp0 : Word) : cnF sp0 + 0xFFFFFFB0 = cnR sp0 := by rw [BitVec.add_assoc]; rfl

theorem cnMidMem_out {M : Word → BitVec 8} {F c x : Word} (hx : Sep (F + BitVec.ofNat 32 4) 0x3C x 1) :
    cnMidMem M F c x = M x := by
  have e : ∀ k : Nat, 4 ≤ k → F + BitVec.ofNat 32 k = F + BitVec.ofNat 32 4 + BitVec.ofNat 32 (k - 4) := fun k hk => by
    rw [add_ofNat_assoc]; congr 2; omega
  have h3C : Sep (F + 0x3C) 4 x 1 := by
    have := hx.sub (c := 0x38) (l := 4) (by decide); rw [← e 0x3C (by decide)] at this; exact this
  have h38 : Sep (F + 0x38) 4 x 1 := by
    have := hx.sub (c := 0x34) (l := 4) (by decide); rw [← e 0x38 (by decide)] at this; exact this
  have h34 : x ≠ F + 0x34 := fun ex => by
    have := hx.point (i := 0x30) (j := 0) (by decide) (by decide)
    rw [add_ofNat_zero, add_ofNat_assoc] at this; exact this ex.symm
  have h48 : Sep (F + BitVec.ofNat 32 4) (4 * 12) x 1 := hx.sub (c := 0) (l := 48) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  simp only [cnMidMem]
  rw [memStore32_get_sep h3C, memStore32_get_sep h38, memStore8_ne h34, copyWords_outside 12 h48]

theorem cnNotMem_out {M : Word → BitVec 8} {B hi x : Word} (hx : Sep B 8 x 1) : cnNotMem M B hi x = M x := by
  have h4 : Sep (B + 4) 4 x 1 := hx.sub (c := 4) (l := 4) (by decide)
  have h0 : Sep B 4 x 1 := by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  simp only [cnNotMem]
  rw [memStore32_get_sep h4, memStore32_get_sep h0]

theorem load_frame3 {M M0 : Word → BitVec 8} {u v w b : Word} {n k l : Nat}
    (hf : ∀ x, Sep u n x 1 → Sep v k x 1 → Sep w l x 1 → M x = M0 x) (h1 : Sep u n b 4) (h2 : Sep v k b 4)
    (h3 : Sep w l b 4) : memLoad32 M b = memLoad32 M0 b :=
  memLoad32_congr fun q hq => hf _ (h1.subR (c := q) (l := 1) (by omega)) (h2.subR (c := q) (l := 1) (by omega))
    (h3.subR (c := q) (l := 1) (by omega))

/-- The registers the function keeps from its prologue's end to its
epilogue: all but `ra`, `t0` through `t2`, `s0`, `s1`, and `a0` through
`a7`. -/
def cnMidKeep (q : Fin 32) : Bool := q.val ∉ [0, 1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
set_option exponentiation.threshold 600 in
/-- **The compiled `safegcd::conditional_negate_in_place_wide::<12, 2>`**,
called with `lo` (12 limbs), `hi` (2 limbs), and `flag` 0 or 1. With `flag`
1 it stores the two's complement negation of the 448-bit value
`lo + 2^384 hi` back into `lo` and `hi`; with `flag` 0 it leaves the value as
it was. It returns with `sp` and every register but `t0` through `t2` and
`a0` through `a7` as they were, and changes no memory outside the 0xE0 bytes
of stack below `sp`, `lo`, and `hi`. -/
theorem condNeg12_correct (m : Machine) {P sp0 lo hi fl retAddr : Word}
    (env : CNEnv m.mem P sp0 lo hi) (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = lo)
    (ha1 : reg m a1 = hi) (ha2 : reg m a2 = fl) (hfl : fl = 0 ∨ fl = 1) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∉ [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17] → reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem lo 12) + 2 ^ 384 * limbVal (wordsAt m'.mem hi 2) =
        (if fl = 1 then
          (2 ^ 448 - (limbVal (wordsAt m.mem lo 12) + 2 ^ 384 * limbVal (wordsAt m.mem hi 2))) % 2 ^ 448
        else limbVal (wordsAt m.mem lo 12) + 2 ^ 384 * limbVal (wordsAt m.mem hi 2)) ∧
      ∀ x, Sep (cnR sp0) 0xE0 x 1 → Sep lo 48 x 1 → Sep hi 8 x 1 → m'.mem x = m.mem x := by
  have hRw := cnR_w sp0 env.hS
  have hwl := env.hwl
  have hwh := env.hwh
  have hF : (cnF sp0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF70) (by decide)
  have hFv : (cnF sp0).toNat = (cnR sp0).toNat + 0x50 := by
    rw [← cnR_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFw : (cnF sp0).toNat + 0x90 ≤ 2 ^ 32 := by omega
  have h50 : 0x50 ≤ (cnF sp0).toNat := by omega
  have h16 : 16 ≤ (cnF sp0).toNat := by omega
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (cnR sp0) 0xE0 b code.length → (∀ x, Sep (cnR sp0) 0xE0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have toF0 : ∀ {b : Word} {k : Nat}, Sep (cnR sp0) 0xE0 b k → Sep (cnF sp0) 0x90 b k := fun h => by
    have := cnin' (c := 0) (l := 0x90) (by decide) h; rwa [add_ofNat_zero] at this
  have toFm : ∀ {b : Word} {k : Nat}, Sep (cnR sp0) 0xE0 b k → Sep (cnF sp0 + 0xFFFFFFF0) 16 b k := fun h => by
    rw [cnF16]; exact h.sub (by decide)
  have inR : ∀ {x : Word} {c l : Nat}, c + l ≤ 0x90 → Sep (cnR sp0) 0xE0 x 1 → Sep (cnF sp0 + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => cnin h hx
  have inRm : ∀ {x : Word}, Sep (cnR sp0) 0xE0 x 1 → Sep (cnF sp0 + 0xFFFFFFF0) 16 x 1 := fun hx => by
    rw [cnF16]; exact hx.sub (by decide)
  have inR50 : ∀ {x : Word}, Sep (cnR sp0) 0xE0 x 1 → Sep (cnF sp0 + 0xFFFFFFB0) 0x50 x 1 := fun hx => by
    rw [cnFR]; have := hx.sub (c := 0) (l := 0x50) (by decide); rwa [add_ofNat_zero] at this
  -- the prologue
  obtain ⟨n1, M1, c1, s1, fr1, hsl1, sp1, r8_1, r11_1, ra0_1, r9_1, ra2_1, r18_1, r19_1, r20_1, k1⟩ :=
    cn_pro m env hpc hsp
  rw [ha0] at r11_1 r19_1
  rw [ha2] at r18_1
  rw [ha1] at r20_1
  -- `lo.carrying_neg()`
  have hT : (cnF sp0 + BitVec.ofNat 32 0x48).toNat % 4 = 0 := aligned_add hF (by decide)
  obtain ⟨n2, M2, c2, s2, cM2, fr2, hc2, hv2, k2⟩ := cn_neg_loop (M1 := M1) (P := P) hT env.hlo
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (cnin' (by decide) env.sRC)
    (cnin' (by decide) env.sLR.symm) 11 0 rfl s1 (cIn env.code env.sRC fr1) (fun _ _ => rfl)
    (by decide) (by simp [accV]) r8_1 r11_1 ra0_1 r9_1 ra2_1
  obtain ⟨c, hc⟩ : ∃ c, reg n2 9 = c := ⟨_, rfl⟩
  rw [hc] at hc2 hv2
  have hcc : c = 0 ∨ c = 1 := by
    rcases (by omega : c.toNat = 0 ∨ c.toNat = 1) with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  have frR2 : ∀ x, Sep (cnR sp0) 0xE0 x 1 → M2 x = m.mem x := fun x hx => by
    rw [fr2 x (inR (by decide) hx), fr1 x hx]
  have sp2 : reg n2 sp = cnF sp0 := by rw [k2 sp rfl, sp1]
  have r20_2 : reg n2 20 = hi := by rw [k2 20 rfl, r20_1]
  -- copy `-lo`, the carry byte, and `!hi`'s buffer
  obtain ⟨n3, c3, s3, sp3, ra0_3, ra1_3, ra2_3, r9_3, k3⟩ := cn_mid env.hP s2 cM2
    (cIn env.stub env.sRU frR2) (cIn env.body env.sRB frR2) hF hFw (toF0 env.sRC) (toF0 env.sRB) sp2 hc r20_2
  have frR3 : ∀ x, Sep (cnR sp0) 0xE0 x 1 → cnMidMem M2 (cnF sp0) c x = m.mem x := fun x hx => by
    rw [cnMidMem_out (inR (by decide) hx), frR2 x hx]
  -- `hi.not()`
  obtain ⟨n4, c4, s4, hc4, k4⟩ := cn_not (B := cnF sp0 + 0x38) s3 (cIn env.code env.sRC frR3) (aligned_add hF (k := 0x38) (by decide))
    env.hhi (cnin' (by decide) env.sRC) (cnin' (by decide) env.sHR.symm) ra0_3 ra2_3 ra1_3
  obtain ⟨M4, hM4⟩ : ∃ M4, cnNotMem (cnMidMem M2 (cnF sp0) c) (cnF sp0 + 0x38) hi = M4 := ⟨_, rfl⟩
  rw [hM4] at s4 hc4
  have frR4 : ∀ x, Sep (cnR sp0) 0xE0 x 1 → M4 x = m.mem x := fun x hx => by
    have h38 : Sep (cnF sp0 + 0x38) 8 x 1 := inR (c := 0x38) (by decide) hx
    rw [← hM4, cnNotMem_out h38, frR3 x hx]
  have sp4 : reg n4 sp = cnF sp0 := by rw [k4 sp rfl, sp3]
  have r9_4 : reg n4 9 = c := by rw [k4 9 rfl, r9_3]
  -- `Uint<2>::select(ZERO, ONE, carry)`
  obtain ⟨n5, c5, s5, sp5, r9_5, w5c, w50, k5, f5⟩ := cn_sel1 env.hP s4 hc4 (cIn env.sel2 env.sR2 frR4)
    (cIn env.zero env.sRZ frR4) (cIn env.one env.sRO frR4) hcc hF h16 (toFm env.sR2) (cnin' (by decide) env.sR2)
    (toFm env.sRZ).symm (toFm env.sRO).symm sp4 r9_4
  have frR5 : ∀ x, Sep (cnR sp0) 0xE0 x 1 → n5.mem x = m.mem x := fun x hx => by
    rw [f5 x (inRm hx) (inR (by decide) hx), frR4 x hx]
  -- `!hi + carry`
  obtain ⟨n6, M6, c6, s6, hc6, f6, hv6, sp6, k6⟩ := cn_add s5 (cIn env.code env.sRC frR5) hF (toF0 env.sRC) sp5 r9_5
  have frR6 : ∀ x, Sep (cnR sp0) 0xE0 x 1 → M6 x = m.mem x := fun x hx => by
    rw [f6 x (inR (by decide) hx), frR5 x hx]
  -- the registers that live through the middle
  have kM : ∀ q, cnMidKeep q = true → reg n6 q = reg n1 q := fun q hq => by
    have ne : ∀ w : Fin 32, cnMidKeep w = false → q ≠ w := fun w hw => pkeep_ne hq hw
    have h0 : q.val ≠ 0 := fun e => absurd (show cnMidKeep q = false by unfold cnMidKeep; simp [e]) (by rw [hq]; decide)
    have nl : ∀ (l : List Nat), (∀ v ∈ l, ∃ w : Fin 32, w.val = v ∧ cnMidKeep w = false) → q.val ∉ l :=
      fun l hl hm => by
        obtain ⟨w, hw, hwk⟩ := hl _ hm
        exact ne w hwk (Fin.ext hw.symm ▸ rfl) |>.elim
    have hq' := hq
    unfold cnMidKeep at hq'
    simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq'
    rw [k6 q (nl _ (by decide)), k5 q (nl _ (by decide)), k4 q (by
      unfold cnNotKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq]; omega),
      k3 q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne a5 rfl) (ne a6 rfl) (ne a7 rfl) (ne t0 rfl)
        (ne t1 rfl) (ne ra rfl), k2 q (by
      unfold cnNegKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq]; omega)]
  have r19_6 : reg n6 19 = lo := by rw [kM 19 rfl, r19_1]
  have r18_6 : reg n6 18 = fl := by rw [kM 18 rfl, r18_1]
  have r20_6 : reg n6 20 = hi := by rw [kM 20 rfl, r20_1]
  -- `Uint<12>::select(lo, -lo, flag)`
  obtain ⟨n7, c7, s7, sp7, w7, f7, k7⟩ := cn_sel12 env.hP s6 hc6 (cIn env.sel12 env.sRL frR6)
    (cIn env.mset env.sRM frR6) (cIn env.stub env.sRU frR6) (cIn env.body env.sRB frR6) hF h50 hFw env.hlo
    (by rw [cnFR]; exact env.sRL) (by rw [cnFR]; exact env.sRM) (by rw [cnFR]; exact env.sRU)
    (by rw [cnFR]; exact env.sRB) (by rw [cnFR]; exact env.sLR) sp6 r19_6 r18_6 hfl
  have frR7 : ∀ x, Sep (cnR sp0) 0xE0 x 1 → n7.mem x = m.mem x := fun x hx => by
    rw [f7 x (inR50 hx) (inR (c := 0x48) (by decide) hx), frR6 x hx]
  have k7' : ∀ q, q.val ∉ [1, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17] → reg n7 q = reg n6 q := k7
  -- copy the selected low part to `lo`
  obtain ⟨n8, c8, s8, hc8, k8⟩ := cn_cpy2 env.hP s7 (cIn env.code env.sRC frR7) (cIn env.stub env.sRU frR7)
    (cIn env.body env.sRB frR7) hF env.hlo env.hwl (cnin' (c := 0x48) (l := 48) (by decide) env.sLR.symm).symm
    env.sLB env.sLC sp7 (by rw [k7' 19 (by decide), r19_6])
  obtain ⟨M8, hM8⟩ : ∃ M8, copyWords n7.mem lo (cnF sp0 + 0x48) 12 = M8 := ⟨_, rfl⟩
  rw [hM8] at s8 hc8
  have frR8 : ∀ x, Sep (cnR sp0) 0xE0 x 1 → Sep lo 48 x 1 → M8 x = m.mem x := fun x hx hl => by
    rw [← hM8, copyWords_outside 12 hl, frR7 x hx]
  have k8' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ ra → reg n8 q = reg n7 q := k8
  have sp8 : reg n8 sp = cnF sp0 := by
    rw [k8' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), sp7]
  have r20_8 : reg n8 20 = hi := by
    rw [k8' 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), k7' 20 (by decide), r20_6]
  have r18_8 : reg n8 18 = fl := by
    rw [k8' 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), k7' 18 (by decide), r18_6]
  -- the saved registers survive to the epilogue
  have hsl8 : ∀ r o, (r, o) ∈ cnPs → memLoad32 M8 (cnF sp0 + o) = reg m r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := cnPs_range (r, o) h
    dsimp only at ho1 ho2
    have e : cnF sp0 + o = cnF sp0 + BitVec.ofNat 32 o.toNat := by rw [ofNat_toNat_self]
    have sF : ∀ c l, c + l ≤ o.toNat → Sep (cnF sp0 + BitVec.ofNat 32 c) l (cnF sp0 + o) 4 := fun c l hcl => by
      rw [e]; exact sep_offsets _ (.inl hcl) (by omega) (by omega)
    have eR : cnF sp0 + o = cnR sp0 + BitVec.ofNat 32 (0x50 + o.toNat) := by
      rw [e, ← cnR_F, add_ofNat_assoc]
    have sR : ∀ c l, c + l ≤ 0x50 + o.toNat → Sep (cnR sp0 + BitVec.ofNat 32 c) l (cnF sp0 + o) 4 :=
      fun c l hcl => by rw [eR]; exact sep_offsets _ (.inl hcl) (by omega) (by omega)
    have sL : Sep lo 48 (cnF sp0 + o) 4 := by rw [eR]; exact env.sLR.subR (by omega)
    have s50 : Sep (cnF sp0 + 0xFFFFFFB0) 0x50 (cnF sp0 + o) 4 := by
      rw [cnFR]; have := sR 0 0x50 (by omega); rwa [add_ofNat_zero] at this
    have s16 : Sep (cnF sp0 + 0xFFFFFFF0) 16 (cnF sp0 + o) 4 := by rw [cnF16]; exact sR 0x40 16 (by omega)
    have s38 : Sep (cnF sp0 + 0x38) 8 (cnF sp0 + o) 4 := sF 0x38 8 (by omega)
    rw [← hM8, copyWords_load_sep sL, load_frame2 f7 s50 (sF 0x48 48 (by omega)), load_frame f6 (sF 0x40 8 (by omega)),
      load_frame2 f5 s16 (sF 0x48 8 (by omega)), ← hM4,
      memLoad32_congr fun q hq => cnNotMem_out (s38.subR (c := q) (l := 1) (by omega)),
      memLoad32_congr fun q hq => cnMidMem_out ((sF 4 0x3C (by omega)).subR (c := q) (l := 1) (by omega)),
      load_frame fr2 (sF 0x48 0x30 (by omega)), hsl1 r o h]
  -- `Uint<2>::select(hi, hi_neg, flag)`, the store to `hi`, and the epilogue
  have hs8 : CodeIn M8 (P + 0x110) uintSelect2Code := fun i hi => by
    rw [frR8 _ (env.sR2.subR (c := i) (l := 1) (by omega)) (env.sL2.subR (c := i) (l := 1) (by omega))]
    exact env.sel2 i hi
  obtain ⟨n9, c9, pc9, sp9, sv9, k9, w9, f9⟩ := cn_tail (v := reg m) env.hP s8 hc8 hs8 hF h16 env.hhi
    (toFm env.sR2) (cnin' (c := 0x48) (l := 8) (by decide) env.sR2) (toFm env.sRC) (toF0 env.sRC)
    (by rw [cnF16]; exact env.sHR.subR (c := 0x40) (l := 0xA0) (by decide)) env.sHC hsl8 sp8 r20_8 r18_8 hfl
  refine ⟨n9, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans c9))))))), ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [pc9, hra, hret]
  · rw [sp9]; show sp0 + 0xFFFFFF70 + 0x90 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  · intro q hq
    by_cases hs : q = sp
    · subst hs; rw [sp9, hsp]; show sp0 + 0xFFFFFF70 + 0x90 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
    by_cases hp : q.val ∈ [1, 8, 9, 18, 19, 20]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with e | e | e | e | e | e
      · rw [show q = ra from Fin.ext e]; exact sv9 ra 0x8C (by decide)
      · rw [show q = 8 from Fin.ext e]; exact sv9 8 0x88 (by decide)
      · rw [show q = 9 from Fin.ext e]; exact sv9 9 0x84 (by decide)
      · rw [show q = 18 from Fin.ext e]; exact sv9 18 0x80 (by decide)
      · rw [show q = 19 from Fin.ext e]; exact sv9 19 0x7C (by decide)
      · rw [show q = 20 from Fin.ext e]; exact sv9 20 0x78 (by decide)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n9 0 = 0 from rfl).trans (show reg m 0 = 0 from rfl).symm
    have hq9 : q.val ∉ [1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp hq ⊢; omega
    have hmk : cnMidKeep q = true := by
      unfold cnMidKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq9 ⊢; omega
    have hck : cnKeep q = true := by
      unfold cnKeep
      simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq9 ⊢
      have : q.val ≠ 2 := fun e => hs (Fin.ext e)
      omega
    have ne : ∀ w : Fin 32, cnMidKeep w = false → q ≠ w := fun w hw => pkeep_ne hmk hw
    rw [k9 q hq9 hs, k8' q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne a5 rfl) (ne a6 rfl)
      (ne a7 rfl) (ne t0 rfl) (ne t1 rfl) (ne ra rfl),
      k7' q (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq9 ⊢; omega), kM q hmk, k1 q hck]
  · -- the low part
    have lw : ∀ i, i < 12 → memLoad32 n9.mem (lo + BitVec.ofNat 32 (4 * i)) =
        if fl = 1 then memLoad32 M2 (cnF sp0 + BitVec.ofNat 32 0x48 + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem (lo + BitVec.ofNat 32 (4 * i)) := fun i hi12 => by
      have sLi : Sep (cnR sp0) 0xE0 (lo + BitVec.ofNat 32 (4 * i)) 4 := env.sLR.symm.subR (by omega)
      rw [load_frame3 f9 (sLi.sub (c := 0x40) (l := 16) (by decide) |> fun h => by rwa [← cnF16] at h)
        ((cnin' (c := 0x48) (l := 8) (by decide) env.sLR.symm).subR (by omega)) (env.sLH.symm.subR (by omega)),
        ← hM8, copyWords_load 12 i hi12 (by omega), w7 i hi12]
      rcases hfl with rfl | rfl
      · rw [ite_eq_right (by decide), ite_eq_right (by decide)]; exact load_frame frR6 sLi
      · rw [ite_eq_left rfl, ite_eq_left rfl]
        have e : cnF sp0 + 4 + BitVec.ofNat 32 (4 * i) = cnF sp0 + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * i) := rfl
        have ea : cnF sp0 + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * i) = cnF sp0 + BitVec.ofNat 32 (4 + 4 * i) :=
          add_ofNat_assoc _ _ _
        have sFa : ∀ c l, c + l ≤ 4 + 4 * i ∨ 4 + 4 * i + 4 ≤ c → c + l ≤ 0x90 →
            Sep (cnF sp0 + BitVec.ofNat 32 c) l (cnF sp0 + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * i)) 4 :=
          fun c l h1 h2 => by rw [ea]; exact sep_offsets _ h1 (by omega) (by omega)
        have sRa : Sep (cnR sp0 + BitVec.ofNat 32 0x40) 16 (cnF sp0 + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * i)) 4 := by
          rw [ea, ← cnR_F, add_ofNat_assoc]; exact sep_offsets _ (.inl (by omega)) (by decide) (by omega)
        have s3C : Sep (cnF sp0 + 0x3C) 4 (cnF sp0 + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * i)) 4 :=
          sFa 0x3C 4 (.inr (by omega)) (by decide)
        have s38 : Sep (cnF sp0 + 0x38) 4 (cnF sp0 + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * i)) 4 :=
          sFa 0x38 4 (.inr (by omega)) (by decide)
        have s38' : Sep (cnF sp0 + 0x38) 8 (cnF sp0 + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * i)) 4 :=
          sFa 0x38 8 (.inr (by omega)) (by decide)
        have s34 : Sep (cnF sp0 + 0x34) 1 (cnF sp0 + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * i)) 4 :=
          sFa 0x34 1 (.inr (by omega)) (by decide)
        rw [e, load_frame f6 (sFa 0x40 8 (.inr (by omega)) (by decide)),
          load_frame2 f5 (by rw [cnF16]; exact sRa) (sFa 0x48 8 (.inr (by omega)) (by decide)), ← hM4,
          memLoad32_congr fun q hq => cnNotMem_out (s38'.subR (c := q) (l := 1) (by omega))]
        simp only [cnMidMem]
        rw [memLoad32_store32_sep s3C, memLoad32_store32_sep s38, memLoad32_store8_sep s34]
        exact copyWords_load 12 i hi12 (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    -- the high part
    have hw : ∀ i, i < 2 → memLoad32 n9.mem (hi + BitVec.ofNat 32 (4 * i)) =
        if fl = 1 then memLoad32 M6 (cnF sp0 + 0x40 + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem (hi + BitVec.ofNat 32 (4 * i)) := fun i hi2 => by
      rw [w9 i hi2]
      have ea : cnF sp0 + 0x40 + BitVec.ofNat 32 (4 * i) = cnF sp0 + BitVec.ofNat 32 (0x40 + 4 * i) :=
        add_ofNat_assoc _ 0x40 _
      have sLa : Sep lo 48 (cnF sp0 + 0x40 + BitVec.ofNat 32 (4 * i)) 4 := by
        rw [ea]; exact (cnin' (c := 0x40 + 4 * i) (l := 4) (by omega) env.sLR.symm).symm
      have s50a : Sep (cnF sp0 + 0xFFFFFFB0) 0x50 (cnF sp0 + 0x40 + BitVec.ofNat 32 (4 * i)) 4 := by
        rw [ea, cnFR, ← cnR_F, add_ofNat_assoc]
        have := sep_offsets (cnR sp0) (c := 0) (n := 0x50) (d := 0x50 + (0x40 + 4 * i)) (k := 4) (.inl (by omega))
          (by decide) (by omega)
        rwa [add_ofNat_zero] at this
      have s48a : Sep (cnF sp0 + 0x48) 48 (cnF sp0 + 0x40 + BitVec.ofNat 32 (4 * i)) 4 := by
        rw [ea]; exact sep_offsets _ (c := 0x48) (.inr (by omega)) (by decide) (by omega)
      have sHi : Sep (cnR sp0) 0xE0 (hi + BitVec.ofNat 32 (4 * i)) 4 := env.sHR.symm.subR (by omega)
      rw [← hM8, copyWords_load_sep sLa, load_frame2 f7 s50a s48a,
        copyWords_load_sep (env.sLH.subR (c := 4 * i) (l := 4) (by omega)), load_frame frR7 sHi]
    -- the carry, `!hi`, and its sum
    have n38 : ∀ j, j < 2 → memLoad32 n5.mem (cnF sp0 + 0x38 + BitVec.ofNat 32 (4 * j)) =
        aluEval .xor (memLoad32 m.mem (hi + BitVec.ofNat 32 (4 * j))) 0xFFFFFFFF := fun j hj => by
      have ea : cnF sp0 + 0x38 + BitVec.ofNat 32 (4 * j) = cnF sp0 + BitVec.ofNat 32 (0x38 + 4 * j) :=
        add_ofNat_assoc _ 0x38 _
      have s16 : Sep (cnF sp0 + 0xFFFFFFF0) 16 (cnF sp0 + 0x38 + BitVec.ofNat 32 (4 * j)) 4 := by
        rw [ea, cnF16, ← cnR_F, add_ofNat_assoc]
        exact sep_offsets _ (c := 0x40) (n := 16) (d := 0x50 + (0x38 + 4 * j)) (k := 4) (.inl (by omega)) (by decide)
          (by omega)
      have s48 : Sep (cnF sp0 + 0x48) 8 (cnF sp0 + 0x38 + BitVec.ofNat 32 (4 * j)) 4 := by
        rw [ea]; exact sep_offsets _ (c := 0x48) (.inr (by omega)) (by decide) (by omega)
      have sHj : Sep (cnR sp0) 0xE0 (hi + BitVec.ofNat 32 (4 * j)) 4 := env.sHR.symm.subR (by omega)
      have s44 : Sep (cnF sp0 + 0x38 + 4) 4 (cnF sp0 + 0x38) 4 := by
        have := sep_offsets (cnF sp0 + 0x38) (c := 4) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide)
          (by decide)
        rwa [add_ofNat_zero] at this
      rw [load_frame2 f5 s16 s48, ← hM4]
      simp only [cnNotMem]
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simp only [u2_slot0] at sHj ⊢
        rw [memLoad32_store32_sep s44, memLoad32_store32_same, load_frame frR3 sHj]
      · simp only [u2_slot1'] at sHj ⊢
        rw [memLoad32_store32_same, load_frame frR3 sHj]
    have eLo : accV M1 lo 12 = accV m.mem lo 12 :=
      accV_congr 12 fun i hi => load_frame fr1 (env.sLR.symm.subR (by omega))
    have hA := accV_lt M2 (cnF sp0 + BitVec.ofNat 32 0x48) 12
    have hL := accV_lt m.mem lo 12
    have e2 : ∀ M, accV M hi 2 = (memLoad32 M hi).toNat + (memLoad32 M (hi + 4)).toNat * 2 ^ 32 := fun M => by
      rw [accV_succ1, accV_succ1]
      simp only [u2_slot0, u2_slot1']
      rw [show accV M hi 0 = 0 from rfl]
      omega
    rw [limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt]
    rcases hfl with rfl | rfl
    · rw [ite_eq_right (by decide)]
      rw [accV_congr (M := m.mem) (M' := n9.mem) (b := lo) 12 fun i h => by rw [lw i h, ite_eq_right (by decide)],
        accV_congr (M := m.mem) (M' := n9.mem) (b := hi) 2 fun i h => by rw [hw i h, ite_eq_right (by decide)]]
    · rw [ite_eq_left rfl]
      have lA : accV n9.mem lo 12 = accV M2 (cnF sp0 + BitVec.ofNat 32 0x48) 12 :=
        accV_congr2 12 fun i h => by rw [lw i h, ite_eq_left rfl]
      rw [lA, e2 n9.mem, e2 m.mem]
      have d0 := hw 0 (by decide)
      have d1 := hw 1 (by decide)
      rw [ite_eq_left rfl] at d0 d1
      simp only [u2_slot0, u2_slot1'] at d0 d1
      rw [d0, d1]
      have x0 := n38 0 (by decide)
      have x1 := n38 1 (by decide)
      simp only [u2_slot0, u2_slot1'] at x0 x1
      rw [x0, x1, w5c, w50] at hv6
      rw [eLo] at hv2
      have o0 := xor_ones_toNat (memLoad32 m.mem hi)
      have o1 := xor_ones_toNat (memLoad32 m.mem (hi + 4))
      have z0 : (0 : Word).toNat = 0 := rfl
      rw [z0] at hv6
      have b0 := (memLoad32 M6 (cnF sp0 + 0x40)).isLt
      have b1 := (memLoad32 M6 (cnF sp0 + 0x40 + 4)).isLt
      have b2 := (memLoad32 m.mem hi).isLt
      have b3 := (memLoad32 m.mem (hi + 4)).isLt
      generalize (memLoad32 M6 (cnF sp0 + 0x40)).toNat = D0 at hv6 b0 ⊢
      generalize (memLoad32 M6 (cnF sp0 + 0x40 + 4)).toNat = D1 at hv6 b1 ⊢
      generalize (memLoad32 m.mem hi).toNat = h0 at o0 b2 ⊢
      generalize (memLoad32 m.mem (hi + 4)).toNat = h1 at o1 b3 ⊢
      generalize (aluEval .xor (memLoad32 m.mem hi) 0xFFFFFFFF).toNat = N0 at o0 hv6
      generalize (aluEval .xor (memLoad32 m.mem (hi + 4)) 0xFFFFFFFF).toNat = N1 at o1 hv6
      generalize (reg n6 a1).toNat = k at hv6
      generalize accV M2 (cnF sp0 + BitVec.ofNat 32 0x48) 12 = A at hA hv2 ⊢
      generalize accV m.mem lo 12 = Lo at hL hv2 ⊢
      generalize c.toNat = cc at hv2 hc2 hv6
      omega
  · intro x hx hl hh
    rw [f9 x (inRm hx) (inR (c := 0x48) (by decide) hx) hh, frR8 x hx hl]

end C3.RV32
