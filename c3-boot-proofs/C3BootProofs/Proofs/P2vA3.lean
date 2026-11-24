import C3BootProofs.Proofs.P2vMs0

/-!
# `p256VerifyPrehash`: the P-256 check's inputs

From 0x186 to the inversion's head at 0x3E0: the key's point at offsets 0x120, 0x140, and 0x160 in projective form, `r` and `s` at 0x180 and 0x1A0, the prehash as a scalar at 0x1C0, and the order and the inversion's state set up.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vA3186 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x200, .aluImm .add a2 x0 0x20]
theorem p2vA3186_end : blockEnd p256VerifyPrehashCode 0x186 p2vA3186 = some 0x194 := by
  simp only [p2vA3186]
  rw [blockEnd, p2v_at_186]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_18a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_18e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_190]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA319c : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x4A1, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x7E5, .aluImm .add a2 x0 0x20]
theorem p2vA319c_end : blockEnd p256VerifyPrehashCode 0x19C p2vA319c = some 0x1B0 := by
  simp only [p2vA319c]
  rw [blockEnd, p2v_at_19c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1a0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1a4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1a8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1ac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA31b8 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x40]
theorem p2vA31b8_end : blockEnd p256VerifyPrehashCode 0x1B8 p2vA31b8 = some 0x1CC := by
  simp only [p2vA31b8]
  rw [blockEnd, p2v_at_1b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1bc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1c4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1c8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA31d4 : List BInstr :=
  [.aluImm .add a0 sp 0xE0, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .aluImm .add a2 x0 0x40]
theorem p2vA31d4_end : blockEnd p256VerifyPrehashCode 0x1D4 p2vA31d4 = some 0x1E2 := by
  simp only [p2vA31d4]
  rw [blockEnd, p2v_at_1d4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1d6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1da]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1de]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA31ea : List BInstr :=
  [.aluImm .add (20 : Fin 32) sp 0x7FF, .aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4A1, .aluImm .add a1 sp 0x78, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (20 : Fin 32)]
theorem p2vA31ea_end : blockEnd p256VerifyPrehashCode 0x1EA p2vA31ea = some 0x1FA := by
  simp only [p2vA31ea]
  rw [blockEnd, p2v_at_1ea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1ee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1f8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3202 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x58, .aluImm .add a2 x0 0x20]
theorem p2vA3202_end : blockEnd p256VerifyPrehashCode 0x202 p2vA3202 = some 0x210 := by
  simp only [p2vA3202]
  rw [blockEnd, p2v_at_202]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_206]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_20a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_20c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3218 : List BInstr :=
  [.aluImm .add (21 : Fin 32) sp 0x7FF, .aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4C1, .lui a1 0x3FCC4000, .aluImm .add a1 a1 0x218, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (21 : Fin 32)]
theorem p2vA3218_end : blockEnd p256VerifyPrehashCode 0x218 p2vA3218 = some 0x22E := by
  simp only [p2vA3218]
  rw [blockEnd, p2v_at_218]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_21c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_220]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_224]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_228]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_22c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3236 : List BInstr :=
  [.alu .add a0 x0 (18 : Fin 32)]
theorem p2vA3236_end : blockEnd p256VerifyPrehashCode 0x236 p2vA3236 = some 0x238 := by
  simp only [p2vA3236]
  rw [blockEnd, p2v_at_236]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3240 : List BInstr :=
  [.aluImm .and (8 : Fin 32) a0 0xFF, .lui (9 : Fin 32) 0x3FCC4000, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x3D0, .aluImm .add a0 sp 0x120, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .alu .add a2 x0 (9 : Fin 32), .alu .add a3 x0 (8 : Fin 32)]
theorem p2vA3240_end : blockEnd p256VerifyPrehashCode 0x240 p2vA3240 = some 0x25A := by
  simp only [p2vA3240]
  rw [blockEnd, p2v_at_240]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_244]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_248]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_24c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_24e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_252]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_256]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_258]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3262 : List BInstr :=
  [.aluImm .add a0 sp 0x140, .aluImm .add a2 (9 : Fin 32) 0x20, .alu .add a1 x0 (20 : Fin 32), .alu .add a3 x0 (8 : Fin 32)]
theorem p2vA3262_end : blockEnd p256VerifyPrehashCode 0x262 p2vA3262 = some 0x26C := by
  simp only [p2vA3262]
  rw [blockEnd, p2v_at_262]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_264]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_268]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_26a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3274 : List BInstr :=
  [.aluImm .add a0 sp 0x160, .aluImm .add a2 (9 : Fin 32) 0x40, .alu .add a1 x0 (21 : Fin 32), .alu .add a3 x0 (8 : Fin 32)]
theorem p2vA3274_end : blockEnd p256VerifyPrehashCode 0x274 p2vA3274 = some 0x27E := by
  simp only [p2vA3274]
  rw [blockEnd, p2v_at_274]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_276]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_27a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_27c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3286 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0xE0, .aluImm .add a2 x0 0x20]
theorem p2vA3286_end : blockEnd p256VerifyPrehashCode 0x286 p2vA3286 = some 0x294 := by
  simp only [p2vA3286]
  rw [blockEnd, p2v_at_286]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_28a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_28e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_290]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA329c : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481]
theorem p2vA329c_end : blockEnd p256VerifyPrehashCode 0x29C p2vA329c = some 0x2AC := by
  simp only [p2vA329c]
  rw [blockEnd, p2v_at_29c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2a0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2a4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2a8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA32b4 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181]
theorem p2vA32b4_end : blockEnd p256VerifyPrehashCode 0x2B4 p2vA32b4 = some 0x2C4 := by
  simp only [p2vA32b4]
  rw [blockEnd, p2v_at_2b4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2bc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA32cc : List BInstr :=
  [.aluImm .add (8 : Fin 32) sp 0x7FF, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4A1, .aluImm .add a1 sp 0x100, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5, .aluImm .add a2 x0 0x20]
theorem p2vA32cc_end : blockEnd p256VerifyPrehashCode 0x2CC p2vA32cc = some 0x2E2 := by
  simp only [p2vA32cc]
  rw [blockEnd, p2v_at_2cc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2d0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2d4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2d6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2da]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2de]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA32ea : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x7E5]
theorem p2vA32ea_end : blockEnd p256VerifyPrehashCode 0x2EA p2vA32ea = some 0x2FA := by
  simp only [p2vA32ea]
  rw [blockEnd, p2v_at_2ea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2ee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_2f6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3302 : List BInstr :=
  [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .alu .add a0 x0 (8 : Fin 32)]
theorem p2vA3302_end : blockEnd p256VerifyPrehashCode 0x302 p2vA3302 = some 0x30C := by
  simp only [p2vA3302]
  rw [blockEnd, p2v_at_302]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_306]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_30a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3314 : List BInstr :=
  [.aluImm .add a0 sp 0x180, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x20]
theorem p2vA3314_end : blockEnd p256VerifyPrehashCode 0x314 p2vA3314 = some 0x322 := by
  simp only [p2vA3314]
  rw [blockEnd, p2v_at_314]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_316]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_31a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_31e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA332a : List BInstr :=
  [.aluImm .add a0 sp 0x1A0, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (8 : Fin 32)]
theorem p2vA332a_end : blockEnd p256VerifyPrehashCode 0x32A p2vA332a = some 0x332 := by
  simp only [p2vA332a]
  rw [blockEnd, p2v_at_32a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_32c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_330]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA333a : List BInstr :=
  [.aluImm .add a0 sp 0x1C0, .alu .add a1 x0 (19 : Fin 32)]
theorem p2vA333a_end : blockEnd p256VerifyPrehashCode 0x33A p2vA333a = some 0x33E := by
  simp only [p2vA333a]
  rw [blockEnd, p2v_at_33a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_33c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3346 : List BInstr :=
  [.aluImm .add a0 sp 0x1A0]
theorem p2vA3346_end : blockEnd p256VerifyPrehashCode 0x346 p2vA3346 = some 0x348 := by
  simp only [p2vA3346]
  rw [blockEnd, p2v_at_346]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3350 : List BInstr :=
  [.aluImm .and (22 : Fin 32) a0 0xFF, .lui a1 0x3FCC4000, .aluImm .add a1 a1 0xD8, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x101, .aluImm .add a2 x0 0x20]
theorem p2vA3350_end : blockEnd p256VerifyPrehashCode 0x350 p2vA3350 = some 0x368 := by
  simp only [p2vA3350]
  rw [blockEnd, p2v_at_350]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_354]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_358]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_35c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_360]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_364]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3374 : List BInstr :=
  [.aluImm .add a0 sp 0x200, .aluImm .add a1 sp 0x1A0, .aluImm .add a2 x0 0x20]
theorem p2vA3374_end : blockEnd p256VerifyPrehashCode 0x374 p2vA3374 = some 0x37C := by
  simp only [p2vA3374]
  rw [blockEnd, p2v_at_374]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_376]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_378]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA3388 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5, .aluImm .add a2 x0 0x24, .aluImm .add a1 x0 0x0]
theorem p2vA3388_end : blockEnd p256VerifyPrehashCode 0x388 p2vA3388 = some 0x396 := by
  simp only [p2vA3388]
  rw [blockEnd, p2v_at_388]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_38c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_390]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_394]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA339e : List BInstr :=
  [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x158, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a2 x0 0x20]
theorem p2vA339e_end : blockEnd p256VerifyPrehashCode 0x39E p2vA339e = some 0x3B2 := by
  simp only [p2vA339e]
  rw [blockEnd, p2v_at_39e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3ae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA33ba : List BInstr :=
  [.aluImm .add (21 : Fin 32) x0 0x0]
theorem p2vA33ba_end : blockEnd p256VerifyPrehashCode 0x3BA p2vA33ba = some 0x3BC := by
  simp only [p2vA33ba]
  rw [blockEnd, p2v_at_3ba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vA33c0 : List BInstr :=
  [.aluImm .add (23 : Fin 32) sp 0x7FF, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4A5, .aluImm .add (19 : Fin 32) x0 0x1, .aluImm .add (24 : Fin 32) x0 0x24F, .aluImm .add (27 : Fin 32) x0 0x7, .lui a0 0x11FF4000, .lui a1 0x332E3000, .aluImm .add (8 : Fin 32) a0 0x3B1, .aluImm .add (9 : Fin 32) a1 0x755]
theorem p2vA33c0_end : blockEnd p256VerifyPrehashCode 0x3C0 p2vA33c0 = some 0x3E0 := by
  simp only [p2vA33c0]
  rw [blockEnd, p2v_at_3c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3c4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3c8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3ca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3ce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3d0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3d4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3d8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_3dc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_a3 {B pk dg rp sq : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x186 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32)
    (g0_19 : reg n0 (19 : Fin 32) = dg)
    (g0_26 : reg n0 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920)
    (a0_58 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256)
    (a0_78 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256)
    (a0_200 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32))
    (a0_fe4 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32))
    (EC0 : P2vEcCode M0)
    (RS : P2vRoSep B)
    (BY0 : BYEnv M0)
    (hrz : beNat (memBytes M0 rp 32) ≠ 0)
    (hsz : beNat (memBytes M0 sq 32) ≠ 0)
    (dg_in : P2vIn B dg 32) :
    (¬ (True) ∧ P2vRet B v n0 0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x3E0 (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 ∧
        reg n' (19 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' (21 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (22 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 ∧
        reg n' (24 : Fin 32) = BitVec.ofNat 32 0x24F ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        reg n' (27 : Fin 32) = BitVec.ofNat 32 0x7 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = 0 ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256OneAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 ∧
        P2vKeepL B n0.mem n'.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20), (0x220, 0x1), (0xFE4, 0x24), (0x980, 0x20), (0x9A0, 0x1)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x186
  obtain ⟨n1, c1, u1⟩ := s0.block p2vA3186 E0.self p2vA3186_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem P2V n1 0x194 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock p2vA3186 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
  have fr1 : ∀ x, P2vR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, P2vR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : P2vCode n1.mem := E0.fr F fr1
  have V1 : P2vSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by
    rw [rb1, runBlock_reg _ _ _ sp s0.zero (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (3 : Fin 32) s0.zero (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (4 : Fin 32) s0.zero (by decide), g0_4]
  have g1_18 : reg n1 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = dg := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_26 : reg n1 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vA3186, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_26, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vA3186, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_26, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vA3186, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_26, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have a1_58 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m1]; exact a0_58
  have a1_78 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m1]; exact a0_78
  have a1_200 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m1]; exact a0_200
  have a1_fe4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m1]; exact a0_fe4
  -- 0x194: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := p2v_mc (c := 0xC80) (d := 0x200) (N := 0x20) F E1 s1 p2v_at_194 p2v_at_198
    (by decide) (by decide) g1_2 g1_10 g1_11 g1_12
    (by decide) (by decide) (by decide)
  have s2 := P2.st
  have fr2 := P2.fr
  have t2 : Steps n0 n2 := t1.trans P2.steps
  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : P2vCode n2.mem := E1.fr F fr2
  have V2 : P2vSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [P2.regs sp (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P2.regs (3 : Fin 32) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P2.regs (4 : Fin 32) (by decide), g1_4]
  have g2_18 : reg n2 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P2.regs (18 : Fin 32) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = dg := by rw [P2.regs (19 : Fin 32) (by decide), g1_19]
  have g2_26 : reg n2 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P2.regs (26 : Fin 32) (by decide), g1_26]
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0xC80, 0x20)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have a2_58 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K2.acc (by decide) (by decide)).trans a1_58
  have a2_78 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K2.acc (by decide) (by decide)).trans a1_78
  have a2_200 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K2.acc (by decide) (by decide)).trans a1_200
  have a2_fe4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K2.acc (by decide) (by decide)).trans a1_fe4
  have a2_c80 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (accV_S 8 fun q hq => by
    rw [show 0xC80 + q = 0xC80 + (0x0 + q) by omega, X2 (0x0 + q) (by omega),
      show 0x200 + (0x0 + q) = 0x200 + q by omega]).trans a1_200
  clear a1_fe4 a1_200 a1_78 a1_58 g1_12 g1_11 g1_10 g1_26 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x19C
  obtain ⟨n3, c3, u3⟩ := s2.block p2vA319c E2.self p2vA319c_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem P2V n3 0x1B0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock p2vA319c (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have fr3 : ∀ x, P2vR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by
    rw [rb3, runBlock_reg _ _ _ sp s2.zero (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (3 : Fin 32) s2.zero (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (4 : Fin 32) s2.zero (by decide), g2_4]
  have g3_18 : reg n3 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = dg := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_26 : reg n3 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vA319c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_26, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_11 : reg n3 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vA319c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_26, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_12 : reg n3 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vA319c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_26, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0xC80, 0x20)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have a3_58 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m3]; exact a2_58
  have a3_78 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m3]; exact a2_78
  have a3_200 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m3]; exact a2_200
  have a3_c80 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m3]; exact a2_c80
  have a3_fe4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m3]; exact a2_fe4
  clear a2_c80 a2_fe4 a2_200 a2_78 a2_58 g2_26 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0x1B0: memcpy
  obtain ⟨n4, P4, K4, X4⟩ := p2v_mc (c := 0xCA0) (d := 0xFE4) (N := 0x20) F E3 s3 p2v_at_1b0 p2v_at_1b4
    (by decide) (by decide) g3_2 g3_10 g3_11 g3_12
    (by decide) (by decide) (by decide)
  have s4 := P4.st
  have fr4 := P4.fr
  have t4 : Steps n0 n4 := t3.trans P4.steps
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [P4.regs sp (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P4.regs (3 : Fin 32) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P4.regs (4 : Fin 32) (by decide), g3_4]
  have g4_18 : reg n4 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P4.regs (18 : Fin 32) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = dg := by rw [P4.regs (19 : Fin 32) (by decide), g3_19]
  have g4_26 : reg n4 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P4.regs (26 : Fin 32) (by decide), g3_26]
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0xC80, 0x20), (0xCA0, 0x20)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have a4_58 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K4.acc (by decide) (by decide)).trans a3_58
  have a4_78 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K4.acc (by decide) (by decide)).trans a3_78
  have a4_200 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K4.acc (by decide) (by decide)).trans a3_200
  have a4_c80 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K4.acc (by decide) (by decide)).trans a3_c80
  have a4_fe4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K4.acc (by decide) (by decide)).trans a3_fe4
  have a4_ca0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (accV_S 8 fun q hq => by
    rw [show 0xCA0 + q = 0xCA0 + (0x0 + q) by omega, X4 (0x0 + q) (by omega),
      show 0xFE4 + (0x0 + q) = 0xFE4 + q by omega]).trans a3_fe4
  clear a3_fe4 a3_c80 a3_200 a3_78 a3_58 g3_12 g3_11 g3_10 g3_26 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0x1B8
  obtain ⟨n5, c5, u5⟩ := s4.block p2vA31b8 E4.self p2vA31b8_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem P2V n5 0x1CC (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock p2vA31b8 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have fr5 : ∀ x, P2vR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, P2vR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : P2vCode n5.mem := E4.fr F fr5
  have V5 : P2vSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by
    rw [rb5, runBlock_reg _ _ _ sp s4.zero (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (3 : Fin 32) s4.zero (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (4 : Fin 32) s4.zero (by decide), g4_4]
  have g5_18 : reg n5 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = dg := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vA31b8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_18, g4_19, g4_26, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_11 : reg n5 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vA31b8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_18, g4_19, g4_26, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_12 : reg n5 a2 = BitVec.ofNat 32 0x40 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vA31b8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_18, g4_19, g4_26, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0xC80, 0x20), (0xCA0, 0x20)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have a5_58 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m5]; exact a4_58
  have a5_78 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m5]; exact a4_78
  have a5_200 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m5]; exact a4_200
  have a5_c80 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m5]; exact a4_c80
  have a5_ca0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m5]; exact a4_ca0
  have a5_fe4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m5]; exact a4_fe4
  clear a4_ca0 a4_fe4 a4_c80 a4_200 a4_78 a4_58 g4_26 g4_19 g4_18 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 s4 X4 K4 P4
  -- 0x1CC: memcpy
  obtain ⟨n6, P6, K6, X6⟩ := p2v_mc (c := 0x980) (d := 0xC80) (N := 0x40) F E5 s5 p2v_at_1cc p2v_at_1d0
    (by decide) (by decide) g5_2 g5_10 g5_11 g5_12
    (by decide) (by decide) (by decide)
  have s6 := P6.st
  have fr6 := P6.fr
  have t6 : Steps n0 n6 := t5.trans P6.steps
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [P6.regs sp (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P6.regs (3 : Fin 32) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P6.regs (4 : Fin 32) (by decide), g5_4]
  have g6_18 : reg n6 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P6.regs (18 : Fin 32) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = dg := by rw [P6.regs (19 : Fin 32) (by decide), g5_19]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P6.regs (26 : Fin 32) (by decide), g5_26]
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have a6_58 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K6.acc (by decide) (by decide)).trans a5_58
  have a6_78 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K6.acc (by decide) (by decide)).trans a5_78
  have a6_200 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K6.acc (by decide) (by decide)).trans a5_200
  have a6_c80 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K6.acc (by decide) (by decide)).trans a5_c80
  have a6_ca0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K6.acc (by decide) (by decide)).trans a5_ca0
  have a6_fe4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K6.acc (by decide) (by decide)).trans a5_fe4
  have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (accV_S 8 fun q hq => by
    rw [show 0x980 + q = 0x980 + (0x0 + q) by omega, X6 (0x0 + q) (by omega),
      show 0xC80 + (0x0 + q) = 0xC80 + q by omega]).trans a5_c80
  have a6_9a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (accV_S 8 fun q hq => by
    rw [show 0x9A0 + q = 0x980 + (0x20 + q) by omega, X6 (0x20 + q) (by omega),
      show 0xC80 + (0x20 + q) = 0xCA0 + q by omega]).trans a5_ca0
  clear a5_fe4 a5_ca0 a5_c80 a5_200 a5_78 a5_58 g5_12 g5_11 g5_10 g5_26 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x1D4
  obtain ⟨n7, c7, u7⟩ := s6.block p2vA31d4 E6.self p2vA31d4_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem P2V n7 0x1E2 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock p2vA31d4 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have fr7 : ∀ x, P2vR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by
    rw [rb7, runBlock_reg _ _ _ sp s6.zero (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (3 : Fin 32) s6.zero (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (4 : Fin 32) s6.zero (by decide), g6_4]
  have g7_18 : reg n7 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = dg := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0xE0 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vA31d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_18, g6_19, g6_26, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_11 : reg n7 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vA31d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_18, g6_19, g6_26, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_12 : reg n7 a2 = BitVec.ofNat 32 0x40 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vA31d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_18, g6_19, g6_26, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have a7_58 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m7]; exact a6_58
  have a7_78 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m7]; exact a6_78
  have a7_200 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m7]; exact a6_200
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m7]; exact a6_980
  have a7_9a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m7]; exact a6_9a0
  have a7_c80 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m7]; exact a6_c80
  have a7_ca0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m7]; exact a6_ca0
  have a7_fe4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m7]; exact a6_fe4
  clear a6_9a0 a6_980 a6_fe4 a6_ca0 a6_c80 a6_200 a6_78 a6_58 g6_26 g6_19 g6_18 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 s6 X6 K6 P6
  -- 0x1E2: memcpy
  obtain ⟨n8, P8, K8, X8⟩ := p2v_mc (c := 0xE0) (d := 0x980) (N := 0x40) F E7 s7 p2v_at_1e2 p2v_at_1e6
    (by decide) (by decide) g7_2 g7_10 g7_11 g7_12
    (by decide) (by decide) (by decide)
  have s8 := P8.st
  have fr8 := P8.fr
  have t8 : Steps n0 n8 := t7.trans P8.steps
  have fR8 : ∀ x, P2vR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : P2vCode n8.mem := E7.fr F fr8
  have V8 : P2vSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [P8.regs sp (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P8.regs (3 : Fin 32) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P8.regs (4 : Fin 32) (by decide), g7_4]
  have g8_18 : reg n8 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P8.regs (18 : Fin 32) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = dg := by rw [P8.regs (19 : Fin 32) (by decide), g7_19]
  have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P8.regs (26 : Fin 32) (by decide), g7_26]
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have a8_58 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K8.acc (by decide) (by decide)).trans a7_58
  have a8_78 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K8.acc (by decide) (by decide)).trans a7_78
  have a8_200 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K8.acc (by decide) (by decide)).trans a7_200
  have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K8.acc (by decide) (by decide)).trans a7_980
  have a8_9a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (K8.acc (by decide) (by decide)).trans a7_9a0
  have a8_c80 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K8.acc (by decide) (by decide)).trans a7_c80
  have a8_ca0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K8.acc (by decide) (by decide)).trans a7_ca0
  have a8_fe4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K8.acc (by decide) (by decide)).trans a7_fe4
  have a8_e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (accV_S 8 fun q hq => by
    rw [show 0xE0 + q = 0xE0 + (0x0 + q) by omega, X8 (0x0 + q) (by omega),
      show 0x980 + (0x0 + q) = 0x980 + q by omega]).trans a7_980
  have a8_100 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (accV_S 8 fun q hq => by
    rw [show 0x100 + q = 0xE0 + (0x20 + q) by omega, X8 (0x20 + q) (by omega),
      show 0x980 + (0x20 + q) = 0x9A0 + q by omega]).trans a7_9a0
  clear a7_fe4 a7_ca0 a7_c80 a7_9a0 a7_980 a7_200 a7_78 a7_58 g7_12 g7_11 g7_10 g7_26 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x1EA
  obtain ⟨n9, c9, u9⟩ := s8.block p2vA31ea E8.self p2vA31ea_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem P2V n9 0x1FA (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock p2vA31ea (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  have fr9 : ∀ x, P2vR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by
    rw [rb9, runBlock_reg _ _ _ sp s8.zero (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (3 : Fin 32) s8.zero (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (4 : Fin 32) s8.zero (by decide), g8_4]
  have g9_18 : reg n9 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = dg := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vA31ea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_18, g8_19, g8_26, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_11 : reg n9 a1 = B + 0x21A0 + BitVec.ofNat 32 0x78 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vA31ea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_18, g8_19, g8_26, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_12 : reg n9 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vA31ea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_18, g8_19, g8_26, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_20 : reg n9 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vA31ea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_18, g8_19, g8_26, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have a9_58 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m9]; exact a8_58
  have a9_78 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m9]; exact a8_78
  have a9_e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m9]; exact a8_e0
  have a9_100 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m9]; exact a8_100
  have a9_200 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m9]; exact a8_200
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m9]; exact a8_980
  have a9_9a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m9]; exact a8_9a0
  have a9_c80 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m9]; exact a8_c80
  have a9_ca0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m9]; exact a8_ca0
  have a9_fe4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m9]; exact a8_fe4
  clear a8_100 a8_e0 a8_fe4 a8_ca0 a8_c80 a8_9a0 a8_980 a8_200 a8_78 a8_58 g8_26 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 s8 X8 K8 P8
  -- 0x1FA: memcpy
  obtain ⟨n10, P10, K10, X10⟩ := p2v_mc (c := 0xCA0) (d := 0x78) (N := 0x20) F E9 s9 p2v_at_1fa p2v_at_1fe
    (by decide) (by decide) g9_2 g9_10 g9_11 g9_12
    (by decide) (by decide) (by decide)
  have s10 := P10.st
  have fr10 := P10.fr
  have t10 : Steps n0 n10 := t9.trans P10.steps
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [P10.regs sp (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P10.regs (3 : Fin 32) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P10.regs (4 : Fin 32) (by decide), g9_4]
  have g10_18 : reg n10 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P10.regs (18 : Fin 32) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = dg := by rw [P10.regs (19 : Fin 32) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P10.regs (20 : Fin 32) (by decide), g9_20]
  have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P10.regs (26 : Fin 32) (by decide), g9_26]
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have a10_58 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K10.acc (by decide) (by decide)).trans a9_58
  have a10_78 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K10.acc (by decide) (by decide)).trans a9_78
  have a10_e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K10.acc (by decide) (by decide)).trans a9_e0
  have a10_100 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K10.acc (by decide) (by decide)).trans a9_100
  have a10_200 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K10.acc (by decide) (by decide)).trans a9_200
  have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K10.acc (by decide) (by decide)).trans a9_980
  have a10_9a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (K10.acc (by decide) (by decide)).trans a9_9a0
  have a10_c80 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K10.acc (by decide) (by decide)).trans a9_c80
  have a10_fe4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K10.acc (by decide) (by decide)).trans a9_fe4
  have a10_ca0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (accV_S 8 fun q hq => by
    rw [show 0xCA0 + q = 0xCA0 + (0x0 + q) by omega, X10 (0x0 + q) (by omega),
      show 0x78 + (0x0 + q) = 0x78 + q by omega]).trans a9_78
  clear a9_fe4 a9_ca0 a9_c80 a9_9a0 a9_980 a9_200 a9_100 a9_e0 a9_78 a9_58 g9_20 g9_12 g9_11 g9_10 g9_26 g9_19 g9_18 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x202
  obtain ⟨n11, c11, u11⟩ := s10.block p2vA3202 E10.self p2vA3202_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem P2V n11 0x210 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock p2vA3202 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  have fr11 : ∀ x, P2vR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by
    rw [rb11, runBlock_reg _ _ _ sp s10.zero (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (3 : Fin 32) s10.zero (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (4 : Fin 32) s10.zero (by decide), g10_4]
  have g11_18 : reg n11 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = dg := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_10 : reg n11 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vA3202, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_18, g10_19, g10_20, g10_26, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g11_11 : reg n11 a1 = B + 0x21A0 + BitVec.ofNat 32 0x58 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vA3202, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_18, g10_19, g10_20, g10_26, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g11_12 : reg n11 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vA3202, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_18, g10_19, g10_20, g10_26, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have a11_58 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m11]; exact a10_58
  have a11_78 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m11]; exact a10_78
  have a11_e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m11]; exact a10_e0
  have a11_100 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m11]; exact a10_100
  have a11_200 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m11]; exact a10_200
  have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m11]; exact a10_980
  have a11_9a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m11]; exact a10_9a0
  have a11_c80 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m11]; exact a10_c80
  have a11_ca0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m11]; exact a10_ca0
  have a11_fe4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m11]; exact a10_fe4
  clear a10_ca0 a10_fe4 a10_c80 a10_9a0 a10_980 a10_200 a10_100 a10_e0 a10_78 a10_58 g10_26 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 s10 X10 K10 P10
  -- 0x210: memcpy
  obtain ⟨n12, P12, K12, X12⟩ := p2v_mc (c := 0xC80) (d := 0x58) (N := 0x20) F E11 s11 p2v_at_210 p2v_at_214
    (by decide) (by decide) g11_2 g11_10 g11_11 g11_12
    (by decide) (by decide) (by decide)
  have s12 := P12.st
  have fr12 := P12.fr
  have t12 : Steps n0 n12 := t11.trans P12.steps
  have fR12 : ∀ x, P2vR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : P2vCode n12.mem := E11.fr F fr12
  have V12 : P2vSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [P12.regs sp (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P12.regs (3 : Fin 32) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P12.regs (4 : Fin 32) (by decide), g11_4]
  have g12_18 : reg n12 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P12.regs (18 : Fin 32) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = dg := by rw [P12.regs (19 : Fin 32) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P12.regs (20 : Fin 32) (by decide), g11_20]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P12.regs (26 : Fin 32) (by decide), g11_26]
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have a12_58 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K12.acc (by decide) (by decide)).trans a11_58
  have a12_78 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K12.acc (by decide) (by decide)).trans a11_78
  have a12_e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K12.acc (by decide) (by decide)).trans a11_e0
  have a12_100 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K12.acc (by decide) (by decide)).trans a11_100
  have a12_200 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K12.acc (by decide) (by decide)).trans a11_200
  have a12_980 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K12.acc (by decide) (by decide)).trans a11_980
  have a12_9a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (K12.acc (by decide) (by decide)).trans a11_9a0
  have a12_ca0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K12.acc (by decide) (by decide)).trans a11_ca0
  have a12_fe4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K12.acc (by decide) (by decide)).trans a11_fe4
  have a12_c80 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (accV_S 8 fun q hq => by
    rw [show 0xC80 + q = 0xC80 + (0x0 + q) by omega, X12 (0x0 + q) (by omega),
      show 0x58 + (0x0 + q) = 0x58 + q by omega]).trans a11_58
  clear a11_fe4 a11_ca0 a11_c80 a11_9a0 a11_980 a11_200 a11_100 a11_e0 a11_78 a11_58 g11_12 g11_11 g11_10 g11_26 g11_20 g11_19 g11_18 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x218
  obtain ⟨n13, c13, u13⟩ := s12.block p2vA3218 E12.self p2vA3218_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem P2V n13 0x22E (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock p2vA3218 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have fr13 : ∀ x, P2vR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, P2vR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : P2vCode n13.mem := E12.fr F fr13
  have V13 : P2vSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by
    rw [rb13, runBlock_reg _ _ _ sp s12.zero (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (3 : Fin 32) s12.zero (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (4 : Fin 32) s12.zero (by decide), g12_4]
  have g13_18 : reg n13 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = dg := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_26 : reg n13 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vA3218, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_18, g12_19, g12_20, g12_26, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 (img% p256MontOneAddress) := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vA3218, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_18, g12_19, g12_20, g12_26, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vA3218, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_18, g12_19, g12_20, g12_26, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g13_21 : reg n13 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vA3218, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_18, g12_19, g12_20, g12_26, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have a13_58 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m13]; exact a12_58
  have a13_78 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m13]; exact a12_78
  have a13_e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m13]; exact a12_e0
  have a13_100 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m13]; exact a12_100
  have a13_200 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m13]; exact a12_200
  have a13_980 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m13]; exact a12_980
  have a13_9a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m13]; exact a12_9a0
  have a13_c80 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m13]; exact a12_c80
  have a13_ca0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m13]; exact a12_ca0
  have a13_fe4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m13]; exact a12_fe4
  clear a12_c80 a12_fe4 a12_ca0 a12_9a0 a12_980 a12_200 a12_100 a12_e0 a12_78 a12_58 g12_26 g12_20 g12_19 g12_18 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 s12 X12 K12 P12
  -- 0x22E: memcpy from outside the stack
  obtain ⟨n14, P14, K14, X14⟩ := p2v_mcRo2 (c := 0xCC0) (N := 0x20) F RS E13 s13 p2v_at_22e p2v_at_232
    (by decide) (by decide) g13_2 g13_10 g13_11 g13_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s14 := P14.st
  have fr14 := P14.fr
  have t14 : Steps n0 n14 := t13.trans P14.steps
  have fR14 : ∀ x, P2vR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : P2vCode n14.mem := E13.fr F fr14
  have V14 : P2vSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [P14.regs sp (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P14.regs (3 : Fin 32) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P14.regs (4 : Fin 32) (by decide), g13_4]
  have g14_18 : reg n14 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P14.regs (18 : Fin 32) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = dg := by rw [P14.regs (19 : Fin 32) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P14.regs (20 : Fin 32) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P14.regs (21 : Fin 32) (by decide), g13_21]
  have g14_26 : reg n14 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P14.regs (26 : Fin 32) (by decide), g13_26]
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have a14_58 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K14.acc (by decide) (by decide)).trans a13_58
  have a14_78 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K14.acc (by decide) (by decide)).trans a13_78
  have a14_e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K14.acc (by decide) (by decide)).trans a13_e0
  have a14_100 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K14.acc (by decide) (by decide)).trans a13_100
  have a14_200 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K14.acc (by decide) (by decide)).trans a13_200
  have a14_980 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K14.acc (by decide) (by decide)).trans a13_980
  have a14_9a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (K14.acc (by decide) (by decide)).trans a13_9a0
  have a14_c80 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K14.acc (by decide) (by decide)).trans a13_c80
  have a14_ca0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K14.acc (by decide) (by decide)).trans a13_ca0
  have a14_fe4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K14.acc (by decide) (by decide)).trans a13_fe4
  have q14_cc0 : ∀ j, j < 32 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X14 j hj).trans (fR13 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a14_cc0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := acc_of_frame q14_cc0
  clear a13_fe4 a13_ca0 a13_c80 a13_9a0 a13_980 a13_200 a13_100 a13_e0 a13_78 a13_58 g13_21 g13_12 g13_11 g13_10 g13_26 g13_20 g13_19 g13_18 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x236
  obtain ⟨n15, c15, u15⟩ := s14.block p2vA3236 E14.self p2vA3236_end
    ⟨trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem P2V n15 0x238 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock p2vA3236 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  have fr15 : ∀ x, P2vR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, P2vR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : P2vCode n15.mem := E14.fr F fr15
  have V15 : P2vSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by
    rw [rb15, runBlock_reg _ _ _ sp s14.zero (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (3 : Fin 32) s14.zero (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (4 : Fin 32) s14.zero (by decide), g14_4]
  have g15_18 : reg n15 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = dg := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb15, runBlock_reg _ _ _ (20 : Fin 32) s14.zero (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_26 : reg n15 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_10 : reg n15 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vA3236, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_18, g14_19, g14_20, g14_21, g14_26, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have q15_cc0 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_cc0 j hj
  have a15_58 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m15]; exact a14_58
  have a15_78 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m15]; exact a14_78
  have a15_e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m15]; exact a14_e0
  have a15_100 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m15]; exact a14_100
  have a15_200 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m15]; exact a14_200
  have a15_980 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m15]; exact a14_980
  have a15_9a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m15]; exact a14_9a0
  have a15_c80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m15]; exact a14_c80
  have a15_ca0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m15]; exact a14_ca0
  have a15_cc0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m15]; exact a14_cc0
  have a15_fe4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m15]; exact a14_fe4
  clear a14_cc0 q14_cc0 a14_fe4 a14_ca0 a14_c80 a14_9a0 a14_980 a14_200 a14_100 a14_e0 a14_78 a14_58 g14_26 g14_21 g14_20 g14_19 g14_18 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 s14 X14 K14 P14
  -- 0x238: p2v_bbF
  obtain ⟨n16, c16, s16, sp16, rk16, a0_16, K16, fr16⟩ := p2v_bbF 
    F E15 s15 p2v_at_238 p2v_at_23c (by decide) (by decide) g15_2
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.keepL K16 (by decide)
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk16 (3 : Fin 32) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk16 (4 : Fin 32) (by decide), g15_4]
  have g16_18 : reg n16 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk16 (18 : Fin 32) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = dg := by rw [rk16 (19 : Fin 32) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk16 (20 : Fin 32) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rk16 (21 : Fin 32) (by decide), g15_21]
  have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk16 (26 : Fin 32) (by decide), g15_26]
  have g16_2 : reg n16 sp = B + 0x21A0 := sp16
  have g16_10 : reg n16 a0 = ((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [a0_16, g15_10]
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20)] := keep_kk15.trans K16
  clear keep_kk15
  have q16_cc0 : ∀ j, j < 32 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_cc0 j hj)
  have a16_58 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K16.acc (by decide) (by decide)).trans a15_58
  have a16_78 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K16.acc (by decide) (by decide)).trans a15_78
  have a16_e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K16.acc (by decide) (by decide)).trans a15_e0
  have a16_100 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K16.acc (by decide) (by decide)).trans a15_100
  have a16_200 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K16.acc (by decide) (by decide)).trans a15_200
  have a16_980 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K16.acc (by decide) (by decide)).trans a15_980
  have a16_9a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (K16.acc (by decide) (by decide)).trans a15_9a0
  have a16_c80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K16.acc (by decide) (by decide)).trans a15_c80
  have a16_ca0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K16.acc (by decide) (by decide)).trans a15_ca0
  have a16_cc0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K16.acc (by decide) (by decide)).trans a15_cc0
  have a16_fe4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K16.acc (by decide) (by decide)).trans a15_fe4
  clear a15_fe4 a15_cc0 a15_ca0 a15_c80 a15_9a0 a15_980 a15_200 a15_100 a15_e0 a15_78 a15_58 q15_cc0 g15_10 g15_26 g15_21 g15_20 g15_19 g15_18 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0x240
  obtain ⟨n17, c17, u17⟩ := s16.block p2vA3240 E16.self p2vA3240_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem P2V n17 0x25A (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock p2vA3240 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
  have fr17 : ∀ x, P2vR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, P2vR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : P2vCode n17.mem := E16.fr F fr17
  have V17 : P2vSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by
    rw [rb17, runBlock_reg _ _ _ sp s16.zero (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (3 : Fin 32) s16.zero (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (4 : Fin 32) s16.zero (by decide), g16_4]
  have g17_18 : reg n17 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = dg := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_8 : reg n17 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vA3240, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_18, g16_19, g16_20, g16_21, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_9 : reg n17 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vA3240, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_18, g16_19, g16_20, g16_21, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x120 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vA3240, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_18, g16_19, g16_20, g16_21, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vA3240, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_18, g16_19, g16_20, g16_21, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vA3240, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_18, g16_19, g16_20, g16_21, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_13 : reg n17 a3 = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vA3240, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_18, g16_19, g16_20, g16_21, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have q17_cc0 : ∀ j, j < 32 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_cc0 j hj
  have a17_58 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m17]; exact a16_58
  have a17_78 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m17]; exact a16_78
  have a17_e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m17]; exact a16_e0
  have a17_100 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m17]; exact a16_100
  have a17_200 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m17]; exact a16_200
  have a17_980 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m17]; exact a16_980
  have a17_9a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m17]; exact a16_9a0
  have a17_c80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m17]; exact a16_c80
  have a17_ca0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m17]; exact a16_ca0
  have a17_cc0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m17]; exact a16_cc0
  have a17_fe4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m17]; exact a16_fe4
  clear a16_fe4 a16_cc0 a16_ca0 a16_c80 a16_9a0 a16_980 a16_200 a16_100 a16_e0 a16_78 a16_58 q16_cc0 g16_10 g16_2 g16_26 g16_21 g16_20 g16_19 g16_18 g16_4 g16_3 V16 E16 fR16 t16 fr16 K16 a0_16 rk16 sp16 s16 c16
  -- 0x25A: p2v_cs2F
  obtain ⟨n18, c18, s18, sp18, rk18, W18, K18, fr18⟩ := p2v_cs2F (co := 0x120) (ca := 0xC80)
    F E17 (EC0.p2v F fR17) s17 p2v_at_25a p2v_at_25e (by decide) (by decide) g17_2
    g17_10 g17_11 g17_12 g17_13 (.inl (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, P2vR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : P2vCode n18.mem := E17.fr F fr18
  have V18 : P2vSaves B n18.mem v := V17.keepL K18 (by decide)
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk18 (3 : Fin 32) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk18 (4 : Fin 32) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [rk18 (8 : Fin 32) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rk18 (9 : Fin 32) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk18 (18 : Fin 32) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = dg := by rw [rk18 (19 : Fin 32) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk18 (20 : Fin 32) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rk18 (21 : Fin 32) (by decide), g17_21]
  have g18_26 : reg n18 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk18 (26 : Fin 32) (by decide), g17_26]
  have g18_2 : reg n18 sp = B + 0x21A0 := sp18
  have keep_kk18 : P2vKeepL B n0.mem n18.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20)] := keep_kk17.trans K18
  clear keep_kk17
  have q18_cc0 : ∀ j, j < 32 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_cc0 j hj)
  have a18_58 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K18.acc (by decide) (by decide)).trans a17_58
  have a18_78 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K18.acc (by decide) (by decide)).trans a17_78
  have a18_e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K18.acc (by decide) (by decide)).trans a17_e0
  have a18_100 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K18.acc (by decide) (by decide)).trans a17_100
  have a18_200 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K18.acc (by decide) (by decide)).trans a17_200
  have a18_980 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K18.acc (by decide) (by decide)).trans a17_980
  have a18_9a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (K18.acc (by decide) (by decide)).trans a17_9a0
  have a18_c80 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K18.acc (by decide) (by decide)).trans a17_c80
  have a18_ca0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K18.acc (by decide) (by decide)).trans a17_ca0
  have a18_cc0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K18.acc (by decide) (by decide)).trans a17_cc0
  have a18_fe4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K18.acc (by decide) (by decide)).trans a17_fe4
  have a18_120 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (acc_of_sel0 (by decide) W18).trans a17_c80
  clear a17_fe4 a17_cc0 a17_ca0 a17_c80 a17_9a0 a17_980 a17_200 a17_100 a17_e0 a17_78 a17_58 q17_cc0 g17_13 g17_12 g17_11 g17_10 g17_9 g17_8 g17_26 g17_21 g17_20 g17_19 g17_18 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x262
  obtain ⟨n19, c19, u19⟩ := s18.block p2vA3262 E18.self p2vA3262_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem P2V n19 0x26C (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock p2vA3262 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
  have fr19 : ∀ x, P2vR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, P2vR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : P2vCode n19.mem := E18.fr F fr19
  have V19 : P2vSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by
    rw [rb19, runBlock_reg _ _ _ sp s18.zero (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (3 : Fin 32) s18.zero (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (4 : Fin 32) s18.zero (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = dg := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_26 : reg n19 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x140 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vA3262, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vA3262, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_12 : reg n19 a2 = BitVec.ofNat 32 (img% p256IdentityAddress + 0x20) := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vA3262, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_13 : reg n19 a3 = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vA3262, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_26, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk19 : P2vKeepL B n0.mem n19.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have q19_cc0 : ∀ j, j < 32 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_cc0 j hj
  have a19_58 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m19]; exact a18_58
  have a19_78 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m19]; exact a18_78
  have a19_e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m19]; exact a18_e0
  have a19_100 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m19]; exact a18_100
  have a19_120 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m19]; exact a18_120
  have a19_200 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m19]; exact a18_200
  have a19_980 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m19]; exact a18_980
  have a19_9a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m19]; exact a18_9a0
  have a19_c80 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m19]; exact a18_c80
  have a19_ca0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m19]; exact a18_ca0
  have a19_cc0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m19]; exact a18_cc0
  have a19_fe4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m19]; exact a18_fe4
  clear a18_120 a18_fe4 a18_cc0 a18_ca0 a18_c80 a18_9a0 a18_980 a18_200 a18_100 a18_e0 a18_78 a18_58 q18_cc0 g18_2 g18_26 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 V18 E18 fR18 t18 fr18 K18 W18 rk18 sp18 s18 c18
  -- 0x26C: p2v_cs2F
  obtain ⟨n20, c20, s20, sp20, rk20, W20, K20, fr20⟩ := p2v_cs2F (co := 0x140) (ca := 0xCA0)
    F E19 (EC0.p2v F fR19) s19 p2v_at_26c p2v_at_270 (by decide) (by decide) g19_2
    g19_10 g19_11 g19_12 g19_13 (.inl (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, P2vR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : P2vCode n20.mem := E19.fr F fr20
  have V20 : P2vSaves B n20.mem v := V19.keepL K20 (by decide)
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk20 (3 : Fin 32) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk20 (4 : Fin 32) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [rk20 (8 : Fin 32) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rk20 (9 : Fin 32) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk20 (18 : Fin 32) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = dg := by rw [rk20 (19 : Fin 32) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk20 (20 : Fin 32) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rk20 (21 : Fin 32) (by decide), g19_21]
  have g20_26 : reg n20 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk20 (26 : Fin 32) (by decide), g19_26]
  have g20_2 : reg n20 sp = B + 0x21A0 := sp20
  have keep_kk20 : P2vKeepL B n0.mem n20.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20)] := keep_kk19.trans K20
  clear keep_kk19
  have q20_cc0 : ∀ j, j < 32 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_cc0 j hj)
  have a20_58 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K20.acc (by decide) (by decide)).trans a19_58
  have a20_78 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K20.acc (by decide) (by decide)).trans a19_78
  have a20_e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K20.acc (by decide) (by decide)).trans a19_e0
  have a20_100 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K20.acc (by decide) (by decide)).trans a19_100
  have a20_120 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K20.acc (by decide) (by decide)).trans a19_120
  have a20_200 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K20.acc (by decide) (by decide)).trans a19_200
  have a20_980 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K20.acc (by decide) (by decide)).trans a19_980
  have a20_9a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (K20.acc (by decide) (by decide)).trans a19_9a0
  have a20_c80 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K20.acc (by decide) (by decide)).trans a19_c80
  have a20_ca0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K20.acc (by decide) (by decide)).trans a19_ca0
  have a20_cc0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K20.acc (by decide) (by decide)).trans a19_cc0
  have a20_fe4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K20.acc (by decide) (by decide)).trans a19_fe4
  have a20_140 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (acc_of_sel0 (by decide) W20).trans a19_ca0
  clear a19_fe4 a19_cc0 a19_ca0 a19_c80 a19_9a0 a19_980 a19_200 a19_120 a19_100 a19_e0 a19_78 a19_58 q19_cc0 g19_13 g19_12 g19_11 g19_10 g19_26 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x274
  obtain ⟨n21, c21, u21⟩ := s20.block p2vA3274 E20.self p2vA3274_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem P2V n21 0x27E (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock p2vA3274 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
  have fr21 : ∀ x, P2vR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, P2vR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : P2vCode n21.mem := E20.fr F fr21
  have V21 : P2vSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by
    rw [rb21, runBlock_reg _ _ _ sp s20.zero (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (3 : Fin 32) s20.zero (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (4 : Fin 32) s20.zero (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = dg := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_26 : reg n21 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0x160 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vA3274, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_26, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g21_11 : reg n21 a1 = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vA3274, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_26, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g21_12 : reg n21 a2 = BitVec.ofNat 32 (img% p256IdentityAddress + 0x40) := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vA3274, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_26, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g21_13 : reg n21 a3 = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vA3274, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_26, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk21 : P2vKeepL B n0.mem n21.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have q21_cc0 : ∀ j, j < 32 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_cc0 j hj
  have a21_58 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m21]; exact a20_58
  have a21_78 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m21]; exact a20_78
  have a21_e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m21]; exact a20_e0
  have a21_100 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m21]; exact a20_100
  have a21_120 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m21]; exact a20_120
  have a21_140 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m21]; exact a20_140
  have a21_200 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m21]; exact a20_200
  have a21_980 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m21]; exact a20_980
  have a21_9a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m21]; exact a20_9a0
  have a21_c80 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m21]; exact a20_c80
  have a21_ca0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m21]; exact a20_ca0
  have a21_cc0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m21]; exact a20_cc0
  have a21_fe4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m21]; exact a20_fe4
  clear a20_140 a20_fe4 a20_cc0 a20_ca0 a20_c80 a20_9a0 a20_980 a20_200 a20_120 a20_100 a20_e0 a20_78 a20_58 q20_cc0 g20_2 g20_26 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 V20 E20 fR20 t20 fr20 K20 W20 rk20 sp20 s20 c20
  -- 0x27E: p2v_cs2F
  obtain ⟨n22, c22, s22, sp22, rk22, W22, K22, fr22⟩ := p2v_cs2F (co := 0x160) (ca := 0xCC0)
    F E21 (EC0.p2v F fR21) s21 p2v_at_27e p2v_at_282 (by decide) (by decide) g21_2
    g21_10 g21_11 g21_12 g21_13 (.inl (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, P2vR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : P2vCode n22.mem := E21.fr F fr22
  have V22 : P2vSaves B n22.mem v := V21.keepL K22 (by decide)
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk22 (3 : Fin 32) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk22 (4 : Fin 32) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [rk22 (8 : Fin 32) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rk22 (9 : Fin 32) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk22 (18 : Fin 32) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = dg := by rw [rk22 (19 : Fin 32) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk22 (20 : Fin 32) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rk22 (21 : Fin 32) (by decide), g21_21]
  have g22_26 : reg n22 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk22 (26 : Fin 32) (by decide), g21_26]
  have g22_2 : reg n22 sp = B + 0x21A0 := sp22
  have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20)] := keep_kk21.trans K22
  clear keep_kk21
  have q22_cc0 : ∀ j, j < 32 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_cc0 j hj)
  have a22_58 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K22.acc (by decide) (by decide)).trans a21_58
  have a22_78 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K22.acc (by decide) (by decide)).trans a21_78
  have a22_e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K22.acc (by decide) (by decide)).trans a21_e0
  have a22_100 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K22.acc (by decide) (by decide)).trans a21_100
  have a22_120 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K22.acc (by decide) (by decide)).trans a21_120
  have a22_140 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K22.acc (by decide) (by decide)).trans a21_140
  have a22_200 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K22.acc (by decide) (by decide)).trans a21_200
  have a22_980 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K22.acc (by decide) (by decide)).trans a21_980
  have a22_9a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (K22.acc (by decide) (by decide)).trans a21_9a0
  have a22_c80 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K22.acc (by decide) (by decide)).trans a21_c80
  have a22_ca0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K22.acc (by decide) (by decide)).trans a21_ca0
  have a22_cc0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K22.acc (by decide) (by decide)).trans a21_cc0
  have a22_fe4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K22.acc (by decide) (by decide)).trans a21_fe4
  have a22_160 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (acc_of_sel0 (by decide) W22).trans a21_cc0
  clear a21_fe4 a21_cc0 a21_ca0 a21_c80 a21_9a0 a21_980 a21_200 a21_140 a21_120 a21_100 a21_e0 a21_78 a21_58 q21_cc0 g21_13 g21_12 g21_11 g21_10 g21_26 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x286
  obtain ⟨n23, c23, u23⟩ := s22.block p2vA3286 E22.self p2vA3286_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem P2V n23 0x294 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock p2vA3286 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
  have fr23 : ∀ x, P2vR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans c23
  have fR23 : ∀ x, P2vR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : P2vCode n23.mem := E22.fr F fr23
  have V23 : P2vSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by
    rw [rb23, runBlock_reg _ _ _ sp s22.zero (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (3 : Fin 32) s22.zero (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (4 : Fin 32) s22.zero (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = dg := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_26 : reg n23 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vA3286, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_26, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0xE0 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vA3286, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_26, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vA3286, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_26, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have q23_cc0 : ∀ j, j < 32 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_cc0 j hj
  have a23_58 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m23]; exact a22_58
  have a23_78 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m23]; exact a22_78
  have a23_e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m23]; exact a22_e0
  have a23_100 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m23]; exact a22_100
  have a23_120 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m23]; exact a22_120
  have a23_140 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m23]; exact a22_140
  have a23_160 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m23]; exact a22_160
  have a23_200 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m23]; exact a22_200
  have a23_980 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m23]; exact a22_980
  have a23_9a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m23]; exact a22_9a0
  have a23_c80 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m23]; exact a22_c80
  have a23_ca0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m23]; exact a22_ca0
  have a23_cc0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m23]; exact a22_cc0
  have a23_fe4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m23]; exact a22_fe4
  clear a22_160 a22_fe4 a22_cc0 a22_ca0 a22_c80 a22_9a0 a22_980 a22_200 a22_140 a22_120 a22_100 a22_e0 a22_78 a22_58 q22_cc0 g22_2 g22_26 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 V22 E22 fR22 t22 fr22 K22 W22 rk22 sp22 s22 c22
  -- 0x294: memcpy
  obtain ⟨n24, P24, K24, X24⟩ := p2v_mc (c := 0xC80) (d := 0xE0) (N := 0x20) F E23 s23 p2v_at_294 p2v_at_298
    (by decide) (by decide) g23_2 g23_10 g23_11 g23_12
    (by decide) (by decide) (by decide)
  have s24 := P24.st
  have fr24 := P24.fr
  have t24 : Steps n0 n24 := t23.trans P24.steps
  have fR24 : ∀ x, P2vR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : P2vCode n24.mem := E23.fr F fr24
  have V24 : P2vSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [P24.regs sp (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P24.regs (3 : Fin 32) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P24.regs (4 : Fin 32) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [P24.regs (8 : Fin 32) (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [P24.regs (9 : Fin 32) (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P24.regs (18 : Fin 32) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = dg := by rw [P24.regs (19 : Fin 32) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P24.regs (20 : Fin 32) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P24.regs (21 : Fin 32) (by decide), g23_21]
  have g24_26 : reg n24 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P24.regs (26 : Fin 32) (by decide), g23_26]
  have keep_kk24 : P2vKeepL B n0.mem n24.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20)] := keep_kk23.trans K24.toL
  clear keep_kk23
  have q24_cc0 : ∀ j, j < 32 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K24.range (by decide) (by decide) j hj).trans (q23_cc0 j hj)
  have a24_58 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K24.acc (by decide) (by decide)).trans a23_58
  have a24_78 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K24.acc (by decide) (by decide)).trans a23_78
  have a24_e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K24.acc (by decide) (by decide)).trans a23_e0
  have a24_100 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K24.acc (by decide) (by decide)).trans a23_100
  have a24_120 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K24.acc (by decide) (by decide)).trans a23_120
  have a24_140 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K24.acc (by decide) (by decide)).trans a23_140
  have a24_160 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K24.acc (by decide) (by decide)).trans a23_160
  have a24_200 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K24.acc (by decide) (by decide)).trans a23_200
  have a24_980 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K24.acc (by decide) (by decide)).trans a23_980
  have a24_9a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := (K24.acc (by decide) (by decide)).trans a23_9a0
  have a24_ca0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K24.acc (by decide) (by decide)).trans a23_ca0
  have a24_cc0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K24.acc (by decide) (by decide)).trans a23_cc0
  have a24_fe4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K24.acc (by decide) (by decide)).trans a23_fe4
  have a24_c80 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (accV_S 8 fun q hq => by
    rw [show 0xC80 + q = 0xC80 + (0x0 + q) by omega, X24 (0x0 + q) (by omega),
      show 0xE0 + (0x0 + q) = 0xE0 + q by omega]).trans a23_e0
  clear a23_fe4 a23_cc0 a23_ca0 a23_c80 a23_9a0 a23_980 a23_200 a23_160 a23_140 a23_120 a23_100 a23_e0 a23_78 a23_58 q23_cc0 g23_12 g23_11 g23_10 g23_26 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x29C
  obtain ⟨n25, c25, u25⟩ := s24.block p2vA329c E24.self p2vA329c_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem P2V n25 0x2AC (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock p2vA329c (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
  have fr25 : ∀ x, P2vR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, P2vR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : P2vCode n25.mem := E24.fr F fr25
  have V25 : P2vSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by
    rw [rb25, runBlock_reg _ _ _ sp s24.zero (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (3 : Fin 32) s24.zero (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (4 : Fin 32) s24.zero (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = dg := by
    rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb25, runBlock_reg _ _ _ (20 : Fin 32) s24.zero (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
  have g25_26 : reg n25 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vA329c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_26, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vA329c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_26, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk25 : P2vKeepL B n0.mem n25.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have q25_cc0 : ∀ j, j < 32 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_cc0 j hj
  have a25_58 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m25]; exact a24_58
  have a25_78 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m25]; exact a24_78
  have a25_e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m25]; exact a24_e0
  have a25_100 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m25]; exact a24_100
  have a25_120 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m25]; exact a24_120
  have a25_140 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m25]; exact a24_140
  have a25_160 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m25]; exact a24_160
  have a25_200 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m25]; exact a24_200
  have a25_980 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m25]; exact a24_980
  have a25_9a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = beNat (memBytes M0 sq 32) := by rw [m25]; exact a24_9a0
  have a25_c80 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m25]; exact a24_c80
  have a25_ca0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m25]; exact a24_ca0
  have a25_cc0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m25]; exact a24_cc0
  have a25_fe4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m25]; exact a24_fe4
  clear a24_c80 a24_fe4 a24_cc0 a24_ca0 a24_9a0 a24_980 a24_200 a24_160 a24_140 a24_120 a24_100 a24_e0 a24_78 a24_58 q24_cc0 g24_26 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 s24 X24 K24 P24
  -- 0x2AC: p2v_nz2F
  obtain ⟨n26, c26, s26, sp26, rk26, W26, Z26, K26, fr26⟩ := p2v_nz2F (co := 0x980) (cx := 0xC80)
    F E25 (EC0.p2v F fR25) s25 p2v_at_2ac p2v_at_2b0 (by decide) (by decide) g25_2
    g25_10 g25_11 (by decide) (by decide) (by decide) (by decide)
  simp only [limbs0_iff a25_c80, ite_eq_right hrz] at Z26
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, P2vR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : P2vCode n26.mem := E25.fr F fr26
  have V26 : P2vSaves B n26.mem v := V25.keepL K26 (by decide)
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk26 (3 : Fin 32) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk26 (4 : Fin 32) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [rk26 (8 : Fin 32) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rk26 (9 : Fin 32) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk26 (18 : Fin 32) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = dg := by rw [rk26 (19 : Fin 32) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk26 (20 : Fin 32) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rk26 (21 : Fin 32) (by decide), g25_21]
  have g26_26 : reg n26 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk26 (26 : Fin 32) (by decide), g25_26]
  have g26_2 : reg n26 sp = B + 0x21A0 := sp26
  have keep_kk26 : P2vKeepL B n0.mem n26.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21)] := keep_kk25.trans K26
  clear keep_kk25
  have q26_cc0 : ∀ j, j < 32 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_cc0 j hj)
  have a26_58 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K26.acc (by decide) (by decide)).trans a25_58
  have a26_78 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K26.acc (by decide) (by decide)).trans a25_78
  have a26_e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K26.acc (by decide) (by decide)).trans a25_e0
  have a26_100 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K26.acc (by decide) (by decide)).trans a25_100
  have a26_120 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K26.acc (by decide) (by decide)).trans a25_120
  have a26_140 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K26.acc (by decide) (by decide)).trans a25_140
  have a26_160 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K26.acc (by decide) (by decide)).trans a25_160
  have a26_200 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K26.acc (by decide) (by decide)).trans a25_200
  have a26_c80 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K26.acc (by decide) (by decide)).trans a25_c80
  have a26_ca0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K26.acc (by decide) (by decide)).trans a25_ca0
  have a26_cc0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K26.acc (by decide) (by decide)).trans a25_cc0
  have a26_fe4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K26.acc (by decide) (by decide)).trans a25_fe4
  have a26_980 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (acc_of_bytes W26).trans a25_c80
  have b26_9a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [show B + 0x21A0 + BitVec.ofNat 32 0x9A0 = B + 0x21A0 + BitVec.ofNat 32 0x980 + 0x20 by p2v_addr]; exact Z26
  clear a25_fe4 a25_cc0 a25_ca0 a25_c80 a25_9a0 a25_980 a25_200 a25_160 a25_140 a25_120 a25_100 a25_e0 a25_78 a25_58 q25_cc0 g25_11 g25_10 g25_26 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x2B4
  obtain ⟨n27, c27, u27⟩ := s26.block p2vA32b4 E26.self p2vA32b4_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem P2V n27 0x2C4 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock p2vA32b4 (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
  have fr27 : ∀ x, P2vR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, P2vR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : P2vCode n27.mem := E26.fr F fr27
  have V27 : P2vSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by
    rw [rb27, runBlock_reg _ _ _ sp s26.zero (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (3 : Fin 32) s26.zero (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (4 : Fin 32) s26.zero (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = dg := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb27, runBlock_reg _ _ _ (20 : Fin 32) s26.zero (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_26 : reg n27 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_10 : reg n27 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, p2vA32b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_26, s26.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, p2vA32b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_26, s26.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk27 : P2vKeepL B n0.mem n27.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have b27_9a0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m27]; exact b26_9a0
  have q27_cc0 : ∀ j, j < 32 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_cc0 j hj
  have a27_58 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m27]; exact a26_58
  have a27_78 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m27]; exact a26_78
  have a27_e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m27]; exact a26_e0
  have a27_100 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m27]; exact a26_100
  have a27_120 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m27]; exact a26_120
  have a27_140 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m27]; exact a26_140
  have a27_160 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m27]; exact a26_160
  have a27_200 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m27]; exact a26_200
  have a27_980 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m27]; exact a26_980
  have a27_c80 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m27]; exact a26_c80
  have a27_ca0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m27]; exact a26_ca0
  have a27_cc0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m27]; exact a26_cc0
  have a27_fe4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m27]; exact a26_fe4
  clear b26_9a0 a26_980 a26_fe4 a26_cc0 a26_ca0 a26_c80 a26_200 a26_160 a26_140 a26_120 a26_100 a26_e0 a26_78 a26_58 q26_cc0 g26_2 g26_26 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 V26 E26 fR26 t26 fr26 K26 Z26 W26 rk26 sp26 s26 c26
  -- 0x2C4: CtOption::unwrap
  obtain ⟨n28, P28, K28, X28⟩ := p2v_cu2 (co := 0xC80) (cs := 0x980) F E27 (EC0.p2v F fR27) s27
    p2v_at_2c4 p2v_at_2c8 (by decide) (by decide) g27_2 g27_10 g27_11
    (by decide) (by decide) (by decide) b27_9a0
  have s28 := P28.st
  have fr28 := P28.fr
  have t28 : Steps n0 n28 := t27.trans P28.steps
  have fR28 : ∀ x, P2vR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : P2vCode n28.mem := E27.fr F fr28
  have V28 : P2vSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [P28.regs sp (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P28.regs (3 : Fin 32) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P28.regs (4 : Fin 32) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = (((((0 : BitVec 8)).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by rw [P28.regs (8 : Fin 32) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [P28.regs (9 : Fin 32) (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P28.regs (18 : Fin 32) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = dg := by rw [P28.regs (19 : Fin 32) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P28.regs (20 : Fin 32) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P28.regs (21 : Fin 32) (by decide), g27_21]
  have g28_26 : reg n28 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P28.regs (26 : Fin 32) (by decide), g27_26]
  have keep_kk28 : P2vKeepL B n0.mem n28.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have b28_9a0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K28.b8 (by decide) (by decide)).trans b27_9a0
  have q28_cc0 : ∀ j, j < 32 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_cc0 j hj)
  have a28_58 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K28.acc (by decide) (by decide)).trans a27_58
  have a28_78 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K28.acc (by decide) (by decide)).trans a27_78
  have a28_e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K28.acc (by decide) (by decide)).trans a27_e0
  have a28_100 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K28.acc (by decide) (by decide)).trans a27_100
  have a28_120 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K28.acc (by decide) (by decide)).trans a27_120
  have a28_140 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K28.acc (by decide) (by decide)).trans a27_140
  have a28_160 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K28.acc (by decide) (by decide)).trans a27_160
  have a28_200 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K28.acc (by decide) (by decide)).trans a27_200
  have a28_980 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K28.acc (by decide) (by decide)).trans a27_980
  have a28_ca0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K28.acc (by decide) (by decide)).trans a27_ca0
  have a28_cc0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K28.acc (by decide) (by decide)).trans a27_cc0
  have a28_fe4 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K28.acc (by decide) (by decide)).trans a27_fe4
  have a28_c80 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (accV_S 8 fun q hq => by
    rw [show 0xC80 + q = 0xC80 + (0x0 + q) by omega, X28 (0x0 + q) (by omega),
      show 0x980 + (0x0 + q) = 0x980 + q by omega]).trans a27_980
  clear a27_fe4 a27_cc0 a27_ca0 a27_c80 a27_980 a27_200 a27_160 a27_140 a27_120 a27_100 a27_e0 a27_78 a27_58 q27_cc0 b27_9a0 g27_11 g27_10 g27_26 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x2CC
  obtain ⟨n29, c29, u29⟩ := s28.block p2vA32cc E28.self p2vA32cc_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem P2V n29 0x2E2 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock p2vA32cc (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
  have fr29 : ∀ x, P2vR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans c29
  have fR29 : ∀ x, P2vR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : P2vCode n29.mem := E28.fr F fr29
  have V29 : P2vSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by
    rw [rb29, runBlock_reg _ _ _ sp s28.zero (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb29, runBlock_reg _ _ _ (3 : Fin 32) s28.zero (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb29, runBlock_reg _ _ _ (4 : Fin 32) s28.zero (by decide), g28_4]
  have g29_9 : reg n29 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = dg := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_26 : reg n29 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_8 : reg n29 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, p2vA32cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_26, s28.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, p2vA32cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_26, s28.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0x100 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, p2vA32cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_26, s28.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g29_12 : reg n29 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, p2vA32cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_26, s28.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk29 : P2vKeepL B n0.mem n29.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have b29_9a0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m29]; exact b28_9a0
  have q29_cc0 : ∀ j, j < 32 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_cc0 j hj
  have a29_58 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m29]; exact a28_58
  have a29_78 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m29]; exact a28_78
  have a29_e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m29]; exact a28_e0
  have a29_100 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m29]; exact a28_100
  have a29_120 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m29]; exact a28_120
  have a29_140 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m29]; exact a28_140
  have a29_160 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m29]; exact a28_160
  have a29_200 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m29]; exact a28_200
  have a29_980 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m29]; exact a28_980
  have a29_c80 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m29]; exact a28_c80
  have a29_ca0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m29]; exact a28_ca0
  have a29_cc0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m29]; exact a28_cc0
  have a29_fe4 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m29]; exact a28_fe4
  clear a28_c80 a28_fe4 a28_cc0 a28_ca0 a28_980 a28_200 a28_160 a28_140 a28_120 a28_100 a28_e0 a28_78 a28_58 q28_cc0 b28_9a0 g28_26 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 s28 X28 K28 P28
  -- 0x2E2: memcpy
  obtain ⟨n30, P30, K30, X30⟩ := p2v_mc (c := 0xFE4) (d := 0x100) (N := 0x20) F E29 s29 p2v_at_2e2 p2v_at_2e6
    (by decide) (by decide) g29_2 g29_10 g29_11 g29_12
    (by decide) (by decide) (by decide)
  have s30 := P30.st
  have fr30 := P30.fr
  have t30 : Steps n0 n30 := t29.trans P30.steps
  have fR30 : ∀ x, P2vR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : P2vCode n30.mem := E29.fr F fr30
  have V30 : P2vSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [P30.regs sp (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P30.regs (3 : Fin 32) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P30.regs (4 : Fin 32) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P30.regs (8 : Fin 32) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [P30.regs (9 : Fin 32) (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P30.regs (18 : Fin 32) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = dg := by rw [P30.regs (19 : Fin 32) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P30.regs (20 : Fin 32) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P30.regs (21 : Fin 32) (by decide), g29_21]
  have g30_26 : reg n30 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P30.regs (26 : Fin 32) (by decide), g29_26]
  have keep_kk30 : P2vKeepL B n0.mem n30.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have b30_9a0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K30.b8 (by decide) (by decide)).trans b29_9a0
  have q30_cc0 : ∀ j, j < 32 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_cc0 j hj)
  have a30_58 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K30.acc (by decide) (by decide)).trans a29_58
  have a30_78 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K30.acc (by decide) (by decide)).trans a29_78
  have a30_e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K30.acc (by decide) (by decide)).trans a29_e0
  have a30_100 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K30.acc (by decide) (by decide)).trans a29_100
  have a30_120 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K30.acc (by decide) (by decide)).trans a29_120
  have a30_140 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K30.acc (by decide) (by decide)).trans a29_140
  have a30_160 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K30.acc (by decide) (by decide)).trans a29_160
  have a30_200 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K30.acc (by decide) (by decide)).trans a29_200
  have a30_980 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := (K30.acc (by decide) (by decide)).trans a29_980
  have a30_c80 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K30.acc (by decide) (by decide)).trans a29_c80
  have a30_ca0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K30.acc (by decide) (by decide)).trans a29_ca0
  have a30_cc0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K30.acc (by decide) (by decide)).trans a29_cc0
  have a30_fe4 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (accV_S 8 fun q hq => by
    rw [show 0xFE4 + q = 0xFE4 + (0x0 + q) by omega, X30 (0x0 + q) (by omega),
      show 0x100 + (0x0 + q) = 0x100 + q by omega]).trans a29_100
  clear a29_fe4 a29_cc0 a29_ca0 a29_c80 a29_980 a29_200 a29_160 a29_140 a29_120 a29_100 a29_e0 a29_78 a29_58 q29_cc0 b29_9a0 g29_12 g29_11 g29_10 g29_8 g29_26 g29_21 g29_20 g29_19 g29_18 g29_9 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  -- 0x2EA
  obtain ⟨n31, c31, u31⟩ := s30.block p2vA32ea E30.self p2vA32ea_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem P2V n31 0x2FA (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock p2vA32ea (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
  have fr31 : ∀ x, P2vR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans c31
  have fR31 : ∀ x, P2vR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : P2vCode n31.mem := E30.fr F fr31
  have V31 : P2vSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by
    rw [rb31, runBlock_reg _ _ _ sp s30.zero (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (3 : Fin 32) s30.zero (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (4 : Fin 32) s30.zero (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb31, runBlock_reg _ _ _ (8 : Fin 32) s30.zero (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
  have g31_18 : reg n31 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = dg := by
    rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
  have g31_26 : reg n31 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
  have g31_10 : reg n31 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, p2vA32ea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_18, g30_19, g30_20, g30_21, g30_26, s30.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g31_11 : reg n31 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, p2vA32ea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_18, g30_19, g30_20, g30_21, g30_26, s30.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk31 : P2vKeepL B n0.mem n31.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have b31_9a0 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m31]; exact b30_9a0
  have q31_cc0 : ∀ j, j < 32 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_cc0 j hj
  have a31_58 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m31]; exact a30_58
  have a31_78 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m31]; exact a30_78
  have a31_e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m31]; exact a30_e0
  have a31_100 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m31]; exact a30_100
  have a31_120 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m31]; exact a30_120
  have a31_140 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m31]; exact a30_140
  have a31_160 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m31]; exact a30_160
  have a31_200 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m31]; exact a30_200
  have a31_980 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 rp 32) := by rw [m31]; exact a30_980
  have a31_c80 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m31]; exact a30_c80
  have a31_ca0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m31]; exact a30_ca0
  have a31_cc0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m31]; exact a30_cc0
  have a31_fe4 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m31]; exact a30_fe4
  clear a30_fe4 a30_cc0 a30_ca0 a30_c80 a30_980 a30_200 a30_160 a30_140 a30_120 a30_100 a30_e0 a30_78 a30_58 q30_cc0 b30_9a0 g30_26 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 s30 X30 K30 P30
  -- 0x2FA: p2v_nz2F
  obtain ⟨n32, c32, s32, sp32, rk32, W32, Z32, K32, fr32⟩ := p2v_nz2F (co := 0x980) (cx := 0xFE4)
    F E31 (EC0.p2v F fR31) s31 p2v_at_2fa p2v_at_2fe (by decide) (by decide) g31_2
    g31_10 g31_11 (by decide) (by decide) (by decide) (by decide)
  simp only [limbs0_iff a31_fe4, ite_eq_right hsz] at Z32
  have t32 : Steps n0 n32 := t31.trans c32
  have fR32 : ∀ x, P2vR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : P2vCode n32.mem := E31.fr F fr32
  have V32 : P2vSaves B n32.mem v := V31.keepL K32 (by decide)
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk32 (3 : Fin 32) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk32 (4 : Fin 32) (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk32 (8 : Fin 32) (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rk32 (9 : Fin 32) (by decide), g31_9]
  have g32_18 : reg n32 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk32 (18 : Fin 32) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = dg := by rw [rk32 (19 : Fin 32) (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk32 (20 : Fin 32) (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rk32 (21 : Fin 32) (by decide), g31_21]
  have g32_26 : reg n32 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk32 (26 : Fin 32) (by decide), g31_26]
  have g32_2 : reg n32 sp = B + 0x21A0 := sp32
  have keep_kk32 : P2vKeepL B n0.mem n32.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21)] := keep_kk31.trans K32
  clear keep_kk31
  have q32_cc0 : ∀ j, j < 32 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_cc0 j hj)
  have a32_58 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K32.acc (by decide) (by decide)).trans a31_58
  have a32_78 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K32.acc (by decide) (by decide)).trans a31_78
  have a32_e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K32.acc (by decide) (by decide)).trans a31_e0
  have a32_100 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K32.acc (by decide) (by decide)).trans a31_100
  have a32_120 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K32.acc (by decide) (by decide)).trans a31_120
  have a32_140 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K32.acc (by decide) (by decide)).trans a31_140
  have a32_160 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K32.acc (by decide) (by decide)).trans a31_160
  have a32_200 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K32.acc (by decide) (by decide)).trans a31_200
  have a32_c80 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K32.acc (by decide) (by decide)).trans a31_c80
  have a32_ca0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K32.acc (by decide) (by decide)).trans a31_ca0
  have a32_cc0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K32.acc (by decide) (by decide)).trans a31_cc0
  have a32_fe4 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K32.acc (by decide) (by decide)).trans a31_fe4
  have a32_980 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (acc_of_bytes W32).trans a31_fe4
  have b32_9a0 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [show B + 0x21A0 + BitVec.ofNat 32 0x9A0 = B + 0x21A0 + BitVec.ofNat 32 0x980 + 0x20 by p2v_addr]; exact Z32
  clear a31_fe4 a31_cc0 a31_ca0 a31_c80 a31_980 a31_200 a31_160 a31_140 a31_120 a31_100 a31_e0 a31_78 a31_58 q31_cc0 b31_9a0 g31_11 g31_10 g31_26 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
  -- 0x302
  obtain ⟨n33, c33, u33⟩ := s32.block p2vA3302 E32.self p2vA3302_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem P2V n33 0x30C (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock p2vA3302 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
  have fr33 : ∀ x, P2vR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans c33
  have fR33 : ∀ x, P2vR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : P2vCode n33.mem := E32.fr F fr33
  have V33 : P2vSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by
    rw [rb33, runBlock_reg _ _ _ sp s32.zero (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (3 : Fin 32) s32.zero (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (4 : Fin 32) s32.zero (by decide), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb33, runBlock_reg _ _ _ (8 : Fin 32) s32.zero (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = dg := by
    rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb33, runBlock_reg _ _ _ (20 : Fin 32) s32.zero (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
  have g33_26 : reg n33 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
  have g33_10 : reg n33 a0 = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, p2vA3302, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_18, g32_19, g32_20, g32_21, g32_26, s32.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g33_11 : reg n33 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, p2vA3302, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_18, g32_19, g32_20, g32_21, g32_26, s32.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk33 : P2vKeepL B n0.mem n33.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have b33_9a0 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m33]; exact b32_9a0
  have q33_cc0 : ∀ j, j < 32 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_cc0 j hj
  have a33_58 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m33]; exact a32_58
  have a33_78 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m33]; exact a32_78
  have a33_e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m33]; exact a32_e0
  have a33_100 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m33]; exact a32_100
  have a33_120 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m33]; exact a32_120
  have a33_140 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m33]; exact a32_140
  have a33_160 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m33]; exact a32_160
  have a33_200 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m33]; exact a32_200
  have a33_980 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := by rw [m33]; exact a32_980
  have a33_c80 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m33]; exact a32_c80
  have a33_ca0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m33]; exact a32_ca0
  have a33_cc0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m33]; exact a32_cc0
  have a33_fe4 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m33]; exact a32_fe4
  clear b32_9a0 a32_980 a32_fe4 a32_cc0 a32_ca0 a32_c80 a32_200 a32_160 a32_140 a32_120 a32_100 a32_e0 a32_78 a32_58 q32_cc0 g32_2 g32_26 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 V32 E32 fR32 t32 fr32 K32 Z32 W32 rk32 sp32 s32 c32
  -- 0x30C: CtOption::unwrap
  obtain ⟨n34, P34, K34, X34⟩ := p2v_cu2 (co := 0xCA0) (cs := 0x980) F E33 (EC0.p2v F fR33) s33
    p2v_at_30c p2v_at_310 (by decide) (by decide) g33_2 g33_10 g33_11
    (by decide) (by decide) (by decide) b33_9a0
  have s34 := P34.st
  have fr34 := P34.fr
  have t34 : Steps n0 n34 := t33.trans P34.steps
  have fR34 : ∀ x, P2vR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : P2vCode n34.mem := E33.fr F fr34
  have V34 : P2vSaves B n34.mem v := V33.keep K34 (by decide)
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [P34.regs sp (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P34.regs (3 : Fin 32) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P34.regs (4 : Fin 32) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P34.regs (8 : Fin 32) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [P34.regs (9 : Fin 32) (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P34.regs (18 : Fin 32) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = dg := by rw [P34.regs (19 : Fin 32) (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P34.regs (20 : Fin 32) (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P34.regs (21 : Fin 32) (by decide), g33_21]
  have g34_26 : reg n34 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P34.regs (26 : Fin 32) (by decide), g33_26]
  have keep_kk34 : P2vKeepL B n0.mem n34.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20)] := keep_kk33.trans K34.toL
  clear keep_kk33
  have b34_9a0 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K34.b8 (by decide) (by decide)).trans b33_9a0
  have q34_cc0 : ∀ j, j < 32 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_cc0 j hj)
  have a34_58 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K34.acc (by decide) (by decide)).trans a33_58
  have a34_78 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K34.acc (by decide) (by decide)).trans a33_78
  have a34_e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K34.acc (by decide) (by decide)).trans a33_e0
  have a34_100 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K34.acc (by decide) (by decide)).trans a33_100
  have a34_120 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K34.acc (by decide) (by decide)).trans a33_120
  have a34_140 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K34.acc (by decide) (by decide)).trans a33_140
  have a34_160 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K34.acc (by decide) (by decide)).trans a33_160
  have a34_200 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K34.acc (by decide) (by decide)).trans a33_200
  have a34_980 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K34.acc (by decide) (by decide)).trans a33_980
  have a34_c80 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K34.acc (by decide) (by decide)).trans a33_c80
  have a34_cc0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K34.acc (by decide) (by decide)).trans a33_cc0
  have a34_fe4 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K34.acc (by decide) (by decide)).trans a33_fe4
  have a34_ca0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (accV_S 8 fun q hq => by
    rw [show 0xCA0 + q = 0xCA0 + (0x0 + q) by omega, X34 (0x0 + q) (by omega),
      show 0x980 + (0x0 + q) = 0x980 + q by omega]).trans a33_980
  clear a33_fe4 a33_cc0 a33_ca0 a33_c80 a33_980 a33_200 a33_160 a33_140 a33_120 a33_100 a33_e0 a33_78 a33_58 q33_cc0 b33_9a0 g33_11 g33_10 g33_26 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x314
  obtain ⟨n35, c35, u35⟩ := s34.block p2vA3314 E34.self p2vA3314_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have s35 : St n35.mem P2V n35 0x322 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have rb35 : ∀ q, reg n35 q = (runBlock p2vA3314 (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
  have fr35 : ∀ x, P2vR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans c35
  have fR35 : ∀ x, P2vR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : P2vCode n35.mem := E34.fr F fr35
  have V35 : P2vSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by
    rw [rb35, runBlock_reg _ _ _ sp s34.zero (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (3 : Fin 32) s34.zero (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (4 : Fin 32) s34.zero (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb35, runBlock_reg _ _ _ (8 : Fin 32) s34.zero (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb35, runBlock_reg _ _ _ (9 : Fin 32) s34.zero (by decide), g34_9]
  have g35_18 : reg n35 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb35, runBlock_reg _ _ _ (18 : Fin 32) s34.zero (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = dg := by
    rw [rb35, runBlock_reg _ _ _ (19 : Fin 32) s34.zero (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb35, runBlock_reg _ _ _ (20 : Fin 32) s34.zero (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb35, runBlock_reg _ _ _ (21 : Fin 32) s34.zero (by decide), g34_21]
  have g35_26 : reg n35 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb35, runBlock_reg _ _ _ (26 : Fin 32) s34.zero (by decide), g34_26]
  have g35_10 : reg n35 a0 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, p2vA3314, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_18, g34_19, g34_20, g34_21, g34_26, s34.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g35_11 : reg n35 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, p2vA3314, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_18, g34_19, g34_20, g34_21, g34_26, s34.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g35_12 : reg n35 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, p2vA3314, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_18, g34_19, g34_20, g34_21, g34_26, s34.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk35 : P2vKeepL B n0.mem n35.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have b35_9a0 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m35]; exact b34_9a0
  have q35_cc0 : ∀ j, j < 32 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m35]; exact q34_cc0 j hj
  have a35_58 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m35]; exact a34_58
  have a35_78 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m35]; exact a34_78
  have a35_e0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m35]; exact a34_e0
  have a35_100 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m35]; exact a34_100
  have a35_120 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m35]; exact a34_120
  have a35_140 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m35]; exact a34_140
  have a35_160 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m35]; exact a34_160
  have a35_200 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m35]; exact a34_200
  have a35_980 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := by rw [m35]; exact a34_980
  have a35_c80 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m35]; exact a34_c80
  have a35_ca0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m35]; exact a34_ca0
  have a35_cc0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m35]; exact a34_cc0
  have a35_fe4 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m35]; exact a34_fe4
  clear a34_ca0 a34_fe4 a34_cc0 a34_c80 a34_980 a34_200 a34_160 a34_140 a34_120 a34_100 a34_e0 a34_78 a34_58 q34_cc0 b34_9a0 g34_26 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 s34 X34 K34 P34
  -- 0x322: memcpy
  obtain ⟨n36, P36, K36, X36⟩ := p2v_mc (c := 0x180) (d := 0xC80) (N := 0x20) F E35 s35 p2v_at_322 p2v_at_326
    (by decide) (by decide) g35_2 g35_10 g35_11 g35_12
    (by decide) (by decide) (by decide)
  have s36 := P36.st
  have fr36 := P36.fr
  have t36 : Steps n0 n36 := t35.trans P36.steps
  have fR36 : ∀ x, P2vR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : P2vCode n36.mem := E35.fr F fr36
  have V36 : P2vSaves B n36.mem v := V35.keep K36 (by decide)
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [P36.regs sp (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P36.regs (3 : Fin 32) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P36.regs (4 : Fin 32) (by decide), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P36.regs (8 : Fin 32) (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [P36.regs (9 : Fin 32) (by decide), g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P36.regs (18 : Fin 32) (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = dg := by rw [P36.regs (19 : Fin 32) (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P36.regs (20 : Fin 32) (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P36.regs (21 : Fin 32) (by decide), g35_21]
  have g36_26 : reg n36 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P36.regs (26 : Fin 32) (by decide), g35_26]
  have keep_kk36 : P2vKeepL B n0.mem n36.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20)] := keep_kk35.trans K36.toL
  clear keep_kk35
  have b36_9a0 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K36.b8 (by decide) (by decide)).trans b35_9a0
  have q36_cc0 : ∀ j, j < 32 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K36.range (by decide) (by decide) j hj).trans (q35_cc0 j hj)
  have a36_58 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K36.acc (by decide) (by decide)).trans a35_58
  have a36_78 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K36.acc (by decide) (by decide)).trans a35_78
  have a36_e0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K36.acc (by decide) (by decide)).trans a35_e0
  have a36_100 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K36.acc (by decide) (by decide)).trans a35_100
  have a36_120 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K36.acc (by decide) (by decide)).trans a35_120
  have a36_140 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K36.acc (by decide) (by decide)).trans a35_140
  have a36_160 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K36.acc (by decide) (by decide)).trans a35_160
  have a36_200 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K36.acc (by decide) (by decide)).trans a35_200
  have a36_980 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K36.acc (by decide) (by decide)).trans a35_980
  have a36_c80 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K36.acc (by decide) (by decide)).trans a35_c80
  have a36_ca0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K36.acc (by decide) (by decide)).trans a35_ca0
  have a36_cc0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K36.acc (by decide) (by decide)).trans a35_cc0
  have a36_fe4 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K36.acc (by decide) (by decide)).trans a35_fe4
  have a36_180 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (accV_S 8 fun q hq => by
    rw [show 0x180 + q = 0x180 + (0x0 + q) by omega, X36 (0x0 + q) (by omega),
      show 0xC80 + (0x0 + q) = 0xC80 + q by omega]).trans a35_c80
  clear a35_fe4 a35_cc0 a35_ca0 a35_c80 a35_980 a35_200 a35_160 a35_140 a35_120 a35_100 a35_e0 a35_78 a35_58 q35_cc0 b35_9a0 g35_12 g35_11 g35_10 g35_26 g35_21 g35_20 g35_19 g35_18 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 rb35 s35 m35 u35 c35
  -- 0x32A
  obtain ⟨n37, c37, u37⟩ := s36.block p2vA332a E36.self p2vA332a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have s37 : St n37.mem P2V n37 0x332 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have rb37 : ∀ q, reg n37 q = (runBlock p2vA332a (n36.mem, reg n36)).2 q := fun q => by rw [u37.regs]
  have fr37 : ∀ x, P2vR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans c37
  have fR37 : ∀ x, P2vR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : P2vCode n37.mem := E36.fr F fr37
  have V37 : P2vSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by
    rw [rb37, runBlock_reg _ _ _ sp s36.zero (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (3 : Fin 32) s36.zero (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (4 : Fin 32) s36.zero (by decide), g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb37, runBlock_reg _ _ _ (8 : Fin 32) s36.zero (by decide), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb37, runBlock_reg _ _ _ (9 : Fin 32) s36.zero (by decide), g36_9]
  have g37_18 : reg n37 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb37, runBlock_reg _ _ _ (18 : Fin 32) s36.zero (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = dg := by
    rw [rb37, runBlock_reg _ _ _ (19 : Fin 32) s36.zero (by decide), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb37, runBlock_reg _ _ _ (20 : Fin 32) s36.zero (by decide), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb37, runBlock_reg _ _ _ (21 : Fin 32) s36.zero (by decide), g36_21]
  have g37_26 : reg n37 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb37, runBlock_reg _ _ _ (26 : Fin 32) s36.zero (by decide), g36_26]
  have g37_10 : reg n37 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1A0 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, p2vA332a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_26, s36.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g37_11 : reg n37 a1 = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, p2vA332a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_26, s36.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g37_12 : reg n37 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, p2vA332a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_26, s36.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk37 : P2vKeepL B n0.mem n37.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have b37_9a0 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m37]; exact b36_9a0
  have q37_cc0 : ∀ j, j < 32 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_cc0 j hj
  have a37_58 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m37]; exact a36_58
  have a37_78 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m37]; exact a36_78
  have a37_e0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m37]; exact a36_e0
  have a37_100 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m37]; exact a36_100
  have a37_120 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m37]; exact a36_120
  have a37_140 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m37]; exact a36_140
  have a37_160 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m37]; exact a36_160
  have a37_180 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := by rw [m37]; exact a36_180
  have a37_200 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m37]; exact a36_200
  have a37_980 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := by rw [m37]; exact a36_980
  have a37_c80 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m37]; exact a36_c80
  have a37_ca0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m37]; exact a36_ca0
  have a37_cc0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m37]; exact a36_cc0
  have a37_fe4 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m37]; exact a36_fe4
  clear a36_180 a36_fe4 a36_cc0 a36_ca0 a36_c80 a36_980 a36_200 a36_160 a36_140 a36_120 a36_100 a36_e0 a36_78 a36_58 q36_cc0 b36_9a0 g36_26 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 s36 X36 K36 P36
  -- 0x332: memcpy
  obtain ⟨n38, P38, K38, X38⟩ := p2v_mc (c := 0x1A0) (d := 0xCA0) (N := 0x20) F E37 s37 p2v_at_332 p2v_at_336
    (by decide) (by decide) g37_2 g37_10 g37_11 g37_12
    (by decide) (by decide) (by decide)
  have s38 := P38.st
  have fr38 := P38.fr
  have t38 : Steps n0 n38 := t37.trans P38.steps
  have fR38 : ∀ x, P2vR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : P2vCode n38.mem := E37.fr F fr38
  have V38 : P2vSaves B n38.mem v := V37.keep K38 (by decide)
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [P38.regs sp (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P38.regs (3 : Fin 32) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P38.regs (4 : Fin 32) (by decide), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P38.regs (8 : Fin 32) (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [P38.regs (9 : Fin 32) (by decide), g37_9]
  have g38_18 : reg n38 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P38.regs (18 : Fin 32) (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = dg := by rw [P38.regs (19 : Fin 32) (by decide), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P38.regs (20 : Fin 32) (by decide), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P38.regs (21 : Fin 32) (by decide), g37_21]
  have g38_26 : reg n38 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P38.regs (26 : Fin 32) (by decide), g37_26]
  have keep_kk38 : P2vKeepL B n0.mem n38.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20)] := keep_kk37.trans K38.toL
  clear keep_kk37
  have b38_9a0 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K38.b8 (by decide) (by decide)).trans b37_9a0
  have q38_cc0 : ∀ j, j < 32 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K38.range (by decide) (by decide) j hj).trans (q37_cc0 j hj)
  have a38_58 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K38.acc (by decide) (by decide)).trans a37_58
  have a38_78 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K38.acc (by decide) (by decide)).trans a37_78
  have a38_e0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K38.acc (by decide) (by decide)).trans a37_e0
  have a38_100 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K38.acc (by decide) (by decide)).trans a37_100
  have a38_120 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K38.acc (by decide) (by decide)).trans a37_120
  have a38_140 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K38.acc (by decide) (by decide)).trans a37_140
  have a38_160 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K38.acc (by decide) (by decide)).trans a37_160
  have a38_180 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K38.acc (by decide) (by decide)).trans a37_180
  have a38_200 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K38.acc (by decide) (by decide)).trans a37_200
  have a38_980 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K38.acc (by decide) (by decide)).trans a37_980
  have a38_c80 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K38.acc (by decide) (by decide)).trans a37_c80
  have a38_ca0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K38.acc (by decide) (by decide)).trans a37_ca0
  have a38_cc0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K38.acc (by decide) (by decide)).trans a37_cc0
  have a38_fe4 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K38.acc (by decide) (by decide)).trans a37_fe4
  have a38_1a0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (accV_S 8 fun q hq => by
    rw [show 0x1A0 + q = 0x1A0 + (0x0 + q) by omega, X38 (0x0 + q) (by omega),
      show 0xCA0 + (0x0 + q) = 0xCA0 + q by omega]).trans a37_ca0
  clear a37_fe4 a37_cc0 a37_ca0 a37_c80 a37_980 a37_200 a37_180 a37_160 a37_140 a37_120 a37_100 a37_e0 a37_78 a37_58 q37_cc0 b37_9a0 g37_12 g37_11 g37_10 g37_26 g37_21 g37_20 g37_19 g37_18 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 rb37 s37 m37 u37 c37
  -- 0x33A
  obtain ⟨n39, c39, u39⟩ := s38.block p2vA333a E38.self p2vA333a_end
    ⟨trivial, trivial, trivial⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have s39 : St n39.mem P2V n39 0x33E (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have rb39 : ∀ q, reg n39 q = (runBlock p2vA333a (n38.mem, reg n38)).2 q := fun q => by rw [u39.regs]
  have fr39 : ∀ x, P2vR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
  have t39 : Steps n0 n39 := t38.trans c39
  have fR39 : ∀ x, P2vR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : P2vCode n39.mem := E38.fr F fr39
  have V39 : P2vSaves B n39.mem v := V38.same m39
  have g39_2 : reg n39 sp = B + 0x21A0 := by
    rw [rb39, runBlock_reg _ _ _ sp s38.zero (by decide), g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb39, runBlock_reg _ _ _ (3 : Fin 32) s38.zero (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb39, runBlock_reg _ _ _ (4 : Fin 32) s38.zero (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb39, runBlock_reg _ _ _ (8 : Fin 32) s38.zero (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb39, runBlock_reg _ _ _ (9 : Fin 32) s38.zero (by decide), g38_9]
  have g39_18 : reg n39 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb39, runBlock_reg _ _ _ (18 : Fin 32) s38.zero (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = dg := by
    rw [rb39, runBlock_reg _ _ _ (19 : Fin 32) s38.zero (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb39, runBlock_reg _ _ _ (20 : Fin 32) s38.zero (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb39, runBlock_reg _ _ _ (21 : Fin 32) s38.zero (by decide), g38_21]
  have g39_26 : reg n39 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb39, runBlock_reg _ _ _ (26 : Fin 32) s38.zero (by decide), g38_26]
  have g39_10 : reg n39 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1C0 := by
    rw [rb39]; simp +decide only [runBlock, BInstr.run, p2vA333a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g38_2, g38_3, g38_4, g38_8, g38_9, g38_18, g38_19, g38_20, g38_21, g38_26, s38.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g39_11 : reg n39 a1 = dg := by
    rw [rb39]; simp +decide only [runBlock, BInstr.run, p2vA333a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g38_2, g38_3, g38_4, g38_8, g38_9, g38_18, g38_19, g38_20, g38_21, g38_26, s38.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk39 : P2vKeepL B n0.mem n39.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20)] := by rw [m39]; exact keep_kk38
  clear keep_kk38
  have b39_9a0 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m39]; exact b38_9a0
  have q39_cc0 : ∀ j, j < 32 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m39]; exact q38_cc0 j hj
  have a39_58 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m39]; exact a38_58
  have a39_78 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m39]; exact a38_78
  have a39_e0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m39]; exact a38_e0
  have a39_100 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m39]; exact a38_100
  have a39_120 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m39]; exact a38_120
  have a39_140 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m39]; exact a38_140
  have a39_160 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m39]; exact a38_160
  have a39_180 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := by rw [m39]; exact a38_180
  have a39_1a0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := by rw [m39]; exact a38_1a0
  have a39_200 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m39]; exact a38_200
  have a39_980 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := by rw [m39]; exact a38_980
  have a39_c80 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m39]; exact a38_c80
  have a39_ca0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m39]; exact a38_ca0
  have a39_cc0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m39]; exact a38_cc0
  have a39_fe4 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m39]; exact a38_fe4
  clear a38_1a0 a38_fe4 a38_cc0 a38_ca0 a38_c80 a38_980 a38_200 a38_180 a38_160 a38_140 a38_120 a38_100 a38_e0 a38_78 a38_58 q38_cc0 b38_9a0 g38_26 g38_21 g38_20 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 s38 X38 K38 P38
  -- 0x33E: p2v_by2F
  obtain ⟨n40, c40, s40, sp40, rk40, A40, K40, fr40⟩ := p2v_by2F (co := 0x1C0)
    F E39 (BY0.p2v F fR39) s39 p2v_at_33e p2v_at_342 (by decide) (by decide) g39_2
    g39_10 g39_11 (by decide) (by decide) dg_in
  rw [p2v_mb fR39 dg_in] at A40
  have t40 : Steps n0 n40 := t39.trans c40
  have fR40 : ∀ x, P2vR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : P2vCode n40.mem := E39.fr F fr40
  have V40 : P2vSaves B n40.mem v := V39.keepL K40 (by decide)
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk40 (3 : Fin 32) (by decide), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk40 (4 : Fin 32) (by decide), g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk40 (8 : Fin 32) (by decide), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rk40 (9 : Fin 32) (by decide), g39_9]
  have g40_18 : reg n40 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk40 (18 : Fin 32) (by decide), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = dg := by rw [rk40 (19 : Fin 32) (by decide), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk40 (20 : Fin 32) (by decide), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rk40 (21 : Fin 32) (by decide), g39_21]
  have g40_26 : reg n40 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk40 (26 : Fin 32) (by decide), g39_26]
  have g40_2 : reg n40 sp = B + 0x21A0 := sp40
  have keep_kk40 : P2vKeepL B n0.mem n40.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20)] := keep_kk39.trans K40
  clear keep_kk39
  have b40_9a0 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K40.b8 (by decide) (by decide)).trans b39_9a0
  have q40_cc0 : ∀ j, j < 32 → n40.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K40.range (by decide) (by decide) j hj).trans (q39_cc0 j hj)
  have a40_58 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K40.acc (by decide) (by decide)).trans a39_58
  have a40_78 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K40.acc (by decide) (by decide)).trans a39_78
  have a40_e0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K40.acc (by decide) (by decide)).trans a39_e0
  have a40_100 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K40.acc (by decide) (by decide)).trans a39_100
  have a40_120 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K40.acc (by decide) (by decide)).trans a39_120
  have a40_140 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K40.acc (by decide) (by decide)).trans a39_140
  have a40_160 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K40.acc (by decide) (by decide)).trans a39_160
  have a40_180 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K40.acc (by decide) (by decide)).trans a39_180
  have a40_1a0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (K40.acc (by decide) (by decide)).trans a39_1a0
  have a40_200 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K40.acc (by decide) (by decide)).trans a39_200
  have a40_980 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K40.acc (by decide) (by decide)).trans a39_980
  have a40_c80 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K40.acc (by decide) (by decide)).trans a39_c80
  have a40_ca0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K40.acc (by decide) (by decide)).trans a39_ca0
  have a40_cc0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K40.acc (by decide) (by decide)).trans a39_cc0
  have a40_fe4 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K40.acc (by decide) (by decide)).trans a39_fe4
  have a40_1c0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := A40
  clear a39_fe4 a39_cc0 a39_ca0 a39_c80 a39_980 a39_200 a39_1a0 a39_180 a39_160 a39_140 a39_120 a39_100 a39_e0 a39_78 a39_58 q39_cc0 b39_9a0 g39_11 g39_10 g39_26 g39_21 g39_20 g39_19 g39_18 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 rb39 s39 m39 u39 c39
  -- 0x346
  obtain ⟨n41, c41, u41⟩ := s40.block p2vA3346 E40.self p2vA3346_end
    ⟨trivial, trivial⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have s41 : St n41.mem P2V n41 0x348 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have rb41 : ∀ q, reg n41 q = (runBlock p2vA3346 (n40.mem, reg n40)).2 q := fun q => by rw [u41.regs]
  have fr41 : ∀ x, P2vR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
  have t41 : Steps n0 n41 := t40.trans c41
  have fR41 : ∀ x, P2vR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : P2vCode n41.mem := E40.fr F fr41
  have V41 : P2vSaves B n41.mem v := V40.same m41
  have g41_2 : reg n41 sp = B + 0x21A0 := by
    rw [rb41, runBlock_reg _ _ _ sp s40.zero (by decide), g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb41, runBlock_reg _ _ _ (3 : Fin 32) s40.zero (by decide), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb41, runBlock_reg _ _ _ (4 : Fin 32) s40.zero (by decide), g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb41, runBlock_reg _ _ _ (8 : Fin 32) s40.zero (by decide), g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb41, runBlock_reg _ _ _ (9 : Fin 32) s40.zero (by decide), g40_9]
  have g41_18 : reg n41 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb41, runBlock_reg _ _ _ (18 : Fin 32) s40.zero (by decide), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = dg := by
    rw [rb41, runBlock_reg _ _ _ (19 : Fin 32) s40.zero (by decide), g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb41, runBlock_reg _ _ _ (20 : Fin 32) s40.zero (by decide), g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb41, runBlock_reg _ _ _ (21 : Fin 32) s40.zero (by decide), g40_21]
  have g41_26 : reg n41 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb41, runBlock_reg _ _ _ (26 : Fin 32) s40.zero (by decide), g40_26]
  have g41_10 : reg n41 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1A0 := by
    rw [rb41]; simp +decide only [runBlock, BInstr.run, p2vA3346, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g40_2, g40_3, g40_4, g40_8, g40_9, g40_18, g40_19, g40_20, g40_21, g40_26, s40.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk41 : P2vKeepL B n0.mem n41.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have b41_9a0 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m41]; exact b40_9a0
  have q41_cc0 : ∀ j, j < 32 → n41.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m41]; exact q40_cc0 j hj
  have a41_58 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m41]; exact a40_58
  have a41_78 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m41]; exact a40_78
  have a41_e0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m41]; exact a40_e0
  have a41_100 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m41]; exact a40_100
  have a41_120 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m41]; exact a40_120
  have a41_140 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m41]; exact a40_140
  have a41_160 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m41]; exact a40_160
  have a41_180 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := by rw [m41]; exact a40_180
  have a41_1a0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := by rw [m41]; exact a40_1a0
  have a41_1c0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := by rw [m41]; exact a40_1c0
  have a41_200 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m41]; exact a40_200
  have a41_980 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := by rw [m41]; exact a40_980
  have a41_c80 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m41]; exact a40_c80
  have a41_ca0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m41]; exact a40_ca0
  have a41_cc0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m41]; exact a40_cc0
  have a41_fe4 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m41]; exact a40_fe4
  clear a40_1c0 a40_fe4 a40_cc0 a40_ca0 a40_c80 a40_980 a40_200 a40_1a0 a40_180 a40_160 a40_140 a40_120 a40_100 a40_e0 a40_78 a40_58 q40_cc0 b40_9a0 g40_2 g40_26 g40_21 g40_20 g40_19 g40_18 g40_9 g40_8 g40_4 g40_3 V40 E40 fR40 t40 fr40 K40 A40 rk40 sp40 s40 c40
  -- 0x348: p2v_unz8F
  obtain ⟨n42, c42, s42, sp42, rk42, a0_42, K42, fr42⟩ := p2v_unz8F (cx := 0x1A0)
    F E41 (EC0.p2v F fR41) s41 p2v_at_348 p2v_at_34c (by decide) (by decide) g41_2
    g41_10 (by decide) (by decide)
  simp only [limbs0_iff a41_1a0] at a0_42
  have t42 : Steps n0 n42 := t41.trans c42
  have fR42 : ∀ x, P2vR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : P2vCode n42.mem := E41.fr F fr42
  have V42 : P2vSaves B n42.mem v := V41.keepL K42 (by decide)
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk42 (3 : Fin 32) (by decide), g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk42 (4 : Fin 32) (by decide), g41_4]
  have g42_8 : reg n42 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk42 (8 : Fin 32) (by decide), g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rk42 (9 : Fin 32) (by decide), g41_9]
  have g42_18 : reg n42 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk42 (18 : Fin 32) (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = dg := by rw [rk42 (19 : Fin 32) (by decide), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk42 (20 : Fin 32) (by decide), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rk42 (21 : Fin 32) (by decide), g41_21]
  have g42_26 : reg n42 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk42 (26 : Fin 32) (by decide), g41_26]
  have g42_2 : reg n42 sp = B + 0x21A0 := sp42
  have keep_kk42 : P2vKeepL B n0.mem n42.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20)] := keep_kk41.trans K42
  clear keep_kk41
  have b42_9a0 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K42.b8 (by decide) (by decide)).trans b41_9a0
  have q42_cc0 : ∀ j, j < 32 → n42.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K42.range (by decide) (by decide) j hj).trans (q41_cc0 j hj)
  have a42_58 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K42.acc (by decide) (by decide)).trans a41_58
  have a42_78 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K42.acc (by decide) (by decide)).trans a41_78
  have a42_e0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K42.acc (by decide) (by decide)).trans a41_e0
  have a42_100 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K42.acc (by decide) (by decide)).trans a41_100
  have a42_120 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K42.acc (by decide) (by decide)).trans a41_120
  have a42_140 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K42.acc (by decide) (by decide)).trans a41_140
  have a42_160 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K42.acc (by decide) (by decide)).trans a41_160
  have a42_180 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K42.acc (by decide) (by decide)).trans a41_180
  have a42_1a0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (K42.acc (by decide) (by decide)).trans a41_1a0
  have a42_1c0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := (K42.acc (by decide) (by decide)).trans a41_1c0
  have a42_200 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K42.acc (by decide) (by decide)).trans a41_200
  have a42_980 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K42.acc (by decide) (by decide)).trans a41_980
  have a42_c80 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K42.acc (by decide) (by decide)).trans a41_c80
  have a42_ca0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K42.acc (by decide) (by decide)).trans a41_ca0
  have a42_cc0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K42.acc (by decide) (by decide)).trans a41_cc0
  have a42_fe4 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K42.acc (by decide) (by decide)).trans a41_fe4
  clear a41_fe4 a41_cc0 a41_ca0 a41_c80 a41_980 a41_200 a41_1c0 a41_1a0 a41_180 a41_160 a41_140 a41_120 a41_100 a41_e0 a41_78 a41_58 q41_cc0 b41_9a0 g41_10 g41_26 g41_21 g41_20 g41_19 g41_18 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 rb41 s41 m41 u41 c41
  have g42_10 : reg n42 a0 = BitVec.ofNat 32 1 := by rw [a0_42, ite_eq_right hsz]; rfl
  -- 0x350
  obtain ⟨n43, c43, u43⟩ := s42.block p2vA3350 E42.self p2vA3350_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m43 : n43.mem = n42.mem := u43.mem
  have s43 : St n43.mem P2V n43 0x368 (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
  have rb43 : ∀ q, reg n43 q = (runBlock p2vA3350 (n42.mem, reg n42)).2 q := fun q => by rw [u43.regs]
  have fr43 : ∀ x, P2vR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
  have t43 : Steps n0 n43 := t42.trans c43
  have fR43 : ∀ x, P2vR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : P2vCode n43.mem := E42.fr F fr43
  have V43 : P2vSaves B n43.mem v := V42.same m43
  have g43_2 : reg n43 sp = B + 0x21A0 := by
    rw [rb43, runBlock_reg _ _ _ sp s42.zero (by decide), g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb43, runBlock_reg _ _ _ (3 : Fin 32) s42.zero (by decide), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb43, runBlock_reg _ _ _ (4 : Fin 32) s42.zero (by decide), g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb43, runBlock_reg _ _ _ (8 : Fin 32) s42.zero (by decide), g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb43, runBlock_reg _ _ _ (9 : Fin 32) s42.zero (by decide), g42_9]
  have g43_18 : reg n43 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb43, runBlock_reg _ _ _ (18 : Fin 32) s42.zero (by decide), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = dg := by
    rw [rb43, runBlock_reg _ _ _ (19 : Fin 32) s42.zero (by decide), g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb43, runBlock_reg _ _ _ (20 : Fin 32) s42.zero (by decide), g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb43, runBlock_reg _ _ _ (21 : Fin 32) s42.zero (by decide), g42_21]
  have g43_26 : reg n43 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb43, runBlock_reg _ _ _ (26 : Fin 32) s42.zero (by decide), g42_26]
  have g43_10 : reg n43 a0 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb43]; simp +decide only [runBlock, BInstr.run, p2vA3350, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g42_2, g42_3, g42_4, g42_8, g42_9, g42_10, g42_18, g42_19, g42_20, g42_21, g42_26, s42.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g43_11 : reg n43 a1 = BitVec.ofNat 32 (img% b2sOrder256Address) := by
    rw [rb43]; simp +decide only [runBlock, BInstr.run, p2vA3350, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g42_2, g42_3, g42_4, g42_8, g42_9, g42_10, g42_18, g42_19, g42_20, g42_21, g42_26, s42.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g43_12 : reg n43 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb43]; simp +decide only [runBlock, BInstr.run, p2vA3350, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g42_2, g42_3, g42_4, g42_8, g42_9, g42_10, g42_18, g42_19, g42_20, g42_21, g42_26, s42.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g43_22 : reg n43 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb43]; simp +decide only [runBlock, BInstr.run, p2vA3350, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g42_2, g42_3, g42_4, g42_8, g42_9, g42_10, g42_18, g42_19, g42_20, g42_21, g42_26, s42.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk43 : P2vKeepL B n0.mem n43.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20)] := by rw [m43]; exact keep_kk42
  clear keep_kk42
  have b43_9a0 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m43]; exact b42_9a0
  have q43_cc0 : ∀ j, j < 32 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m43]; exact q42_cc0 j hj
  have a43_58 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m43]; exact a42_58
  have a43_78 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m43]; exact a42_78
  have a43_e0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m43]; exact a42_e0
  have a43_100 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m43]; exact a42_100
  have a43_120 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m43]; exact a42_120
  have a43_140 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m43]; exact a42_140
  have a43_160 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m43]; exact a42_160
  have a43_180 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := by rw [m43]; exact a42_180
  have a43_1a0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := by rw [m43]; exact a42_1a0
  have a43_1c0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := by rw [m43]; exact a42_1c0
  have a43_200 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m43]; exact a42_200
  have a43_980 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := by rw [m43]; exact a42_980
  have a43_c80 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m43]; exact a42_c80
  have a43_ca0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m43]; exact a42_ca0
  have a43_cc0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m43]; exact a42_cc0
  have a43_fe4 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m43]; exact a42_fe4
  clear a42_fe4 a42_cc0 a42_ca0 a42_c80 a42_980 a42_200 a42_1c0 a42_1a0 a42_180 a42_160 a42_140 a42_120 a42_100 a42_e0 a42_78 a42_58 q42_cc0 b42_9a0 g42_2 g42_26 g42_21 g42_20 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 V42 E42 fR42 t42 fr42 K42 a0_42 rk42 sp42 s42 c42
  -- 0x368: memcpy from outside the stack
  obtain ⟨n44, P44, K44, X44⟩ := p2v_mcRo2 (c := 0x900) (N := 0x20) F RS E43 s43 p2v_at_368 p2v_at_36c
    (by decide) (by decide) g43_2 g43_10 g43_11 g43_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s44 := P44.st
  have fr44 := P44.fr
  have t44 : Steps n0 n44 := t43.trans P44.steps
  have fR44 : ∀ x, P2vR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : P2vCode n44.mem := E43.fr F fr44
  have V44 : P2vSaves B n44.mem v := V43.keep K44 (by decide)
  have g44_2 : reg n44 sp = B + 0x21A0 := by rw [P44.regs sp (by decide), g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P44.regs (3 : Fin 32) (by decide), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P44.regs (4 : Fin 32) (by decide), g43_4]
  have g44_8 : reg n44 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P44.regs (8 : Fin 32) (by decide), g43_8]
  have g44_9 : reg n44 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [P44.regs (9 : Fin 32) (by decide), g43_9]
  have g44_18 : reg n44 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P44.regs (18 : Fin 32) (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = dg := by rw [P44.regs (19 : Fin 32) (by decide), g43_19]
  have g44_20 : reg n44 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P44.regs (20 : Fin 32) (by decide), g43_20]
  have g44_21 : reg n44 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P44.regs (21 : Fin 32) (by decide), g43_21]
  have g44_22 : reg n44 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P44.regs (22 : Fin 32) (by decide), g43_22]
  have g44_26 : reg n44 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P44.regs (26 : Fin 32) (by decide), g43_26]
  have keep_kk44 : P2vKeepL B n0.mem n44.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20)] := keep_kk43.trans K44.toL
  clear keep_kk43
  have b44_9a0 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K44.b8 (by decide) (by decide)).trans b43_9a0
  have q44_cc0 : ∀ j, j < 32 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K44.range (by decide) (by decide) j hj).trans (q43_cc0 j hj)
  have a44_58 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K44.acc (by decide) (by decide)).trans a43_58
  have a44_78 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K44.acc (by decide) (by decide)).trans a43_78
  have a44_e0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K44.acc (by decide) (by decide)).trans a43_e0
  have a44_100 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K44.acc (by decide) (by decide)).trans a43_100
  have a44_120 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K44.acc (by decide) (by decide)).trans a43_120
  have a44_140 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K44.acc (by decide) (by decide)).trans a43_140
  have a44_160 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K44.acc (by decide) (by decide)).trans a43_160
  have a44_180 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K44.acc (by decide) (by decide)).trans a43_180
  have a44_1a0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (K44.acc (by decide) (by decide)).trans a43_1a0
  have a44_1c0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := (K44.acc (by decide) (by decide)).trans a43_1c0
  have a44_200 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K44.acc (by decide) (by decide)).trans a43_200
  have a44_980 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K44.acc (by decide) (by decide)).trans a43_980
  have a44_c80 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K44.acc (by decide) (by decide)).trans a43_c80
  have a44_ca0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K44.acc (by decide) (by decide)).trans a43_ca0
  have a44_cc0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K44.acc (by decide) (by decide)).trans a43_cc0
  have a44_fe4 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K44.acc (by decide) (by decide)).trans a43_fe4
  have q44_900 : ∀ j, j < 32 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) :=
    fun j hj => (X44 j hj).trans (fR43 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a44_900 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := acc_of_frame q44_900
  clear a43_fe4 a43_cc0 a43_ca0 a43_c80 a43_980 a43_200 a43_1c0 a43_1a0 a43_180 a43_160 a43_140 a43_120 a43_100 a43_e0 a43_78 a43_58 q43_cc0 b43_9a0 g43_22 g43_12 g43_11 g43_10 g43_26 g43_21 g43_20 g43_19 g43_18 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 rb43 s43 m43 u43 c43 g42_10
  -- 0x370: sb
  obtain ⟨n45, d45, s45, fr45, K45, W45, rg45⟩ := p2v_sb F E44 s44 p2v_at_370 (off' := 0x374) (c := 0x920)
    (by decide) (by rw [g44_26]; p2v_addr) (by decide)
  have t45 : Steps n0 n45 := t44.trans d45
  have fR45 : ∀ x, P2vR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : P2vCode n45.mem := E44.fr F fr45
  have V45 : P2vSaves B n45.mem v := V44.keep K45 (by decide)
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [rg45 sp, g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg45 (3 : Fin 32), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg45 (4 : Fin 32), g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rg45 (8 : Fin 32), g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rg45 (9 : Fin 32), g44_9]
  have g45_18 : reg n45 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rg45 (18 : Fin 32), g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = dg := by rw [rg45 (19 : Fin 32), g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rg45 (20 : Fin 32), g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rg45 (21 : Fin 32), g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg45 (22 : Fin 32), g44_22]
  have g45_26 : reg n45 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg45 (26 : Fin 32), g44_26]
  have keep_kk45 : P2vKeepL B n0.mem n45.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1)] := keep_kk44.trans K45.toL
  clear keep_kk44
  have b45_9a0 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K45.b8 (by decide) (by decide)).trans b44_9a0
  have b45_920 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W45, s44.zero]; rfl
  have q45_900 : ∀ j, j < 32 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => (K45.range (by decide) (by decide) j hj).trans (q44_900 j hj)
  have q45_cc0 : ∀ j, j < 32 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K45.range (by decide) (by decide) j hj).trans (q44_cc0 j hj)
  have a45_58 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K45.acc (by decide) (by decide)).trans a44_58
  have a45_78 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K45.acc (by decide) (by decide)).trans a44_78
  have a45_e0 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K45.acc (by decide) (by decide)).trans a44_e0
  have a45_100 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K45.acc (by decide) (by decide)).trans a44_100
  have a45_120 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K45.acc (by decide) (by decide)).trans a44_120
  have a45_140 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K45.acc (by decide) (by decide)).trans a44_140
  have a45_160 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K45.acc (by decide) (by decide)).trans a44_160
  have a45_180 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K45.acc (by decide) (by decide)).trans a44_180
  have a45_1a0 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (K45.acc (by decide) (by decide)).trans a44_1a0
  have a45_1c0 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := (K45.acc (by decide) (by decide)).trans a44_1c0
  have a45_200 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := (K45.acc (by decide) (by decide)).trans a44_200
  have a45_900 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := (K45.acc (by decide) (by decide)).trans a44_900
  have a45_980 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K45.acc (by decide) (by decide)).trans a44_980
  have a45_c80 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K45.acc (by decide) (by decide)).trans a44_c80
  have a45_ca0 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K45.acc (by decide) (by decide)).trans a44_ca0
  have a45_cc0 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K45.acc (by decide) (by decide)).trans a44_cc0
  have a45_fe4 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K45.acc (by decide) (by decide)).trans a44_fe4
  clear a44_900 q44_900 a44_fe4 a44_cc0 a44_ca0 a44_c80 a44_980 a44_200 a44_1c0 a44_1a0 a44_180 a44_160 a44_140 a44_120 a44_100 a44_e0 a44_78 a44_58 q44_cc0 b44_9a0 g44_26 g44_22 g44_21 g44_20 g44_19 g44_18 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 s44 X44 K44 P44
  -- 0x374
  obtain ⟨n46, c46, u46⟩ := s45.block p2vA3374 E45.self p2vA3374_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have s46 : St n46.mem P2V n46 0x37C (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have rb46 : ∀ q, reg n46 q = (runBlock p2vA3374 (n45.mem, reg n45)).2 q := fun q => by rw [u46.regs]
  have fr46 : ∀ x, P2vR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans c46
  have fR46 : ∀ x, P2vR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : P2vCode n46.mem := E45.fr F fr46
  have V46 : P2vSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by
    rw [rb46, runBlock_reg _ _ _ sp s45.zero (by decide), g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb46, runBlock_reg _ _ _ (3 : Fin 32) s45.zero (by decide), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb46, runBlock_reg _ _ _ (4 : Fin 32) s45.zero (by decide), g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb46, runBlock_reg _ _ _ (8 : Fin 32) s45.zero (by decide), g45_8]
  have g46_9 : reg n46 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb46, runBlock_reg _ _ _ (9 : Fin 32) s45.zero (by decide), g45_9]
  have g46_18 : reg n46 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb46, runBlock_reg _ _ _ (18 : Fin 32) s45.zero (by decide), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = dg := by
    rw [rb46, runBlock_reg _ _ _ (19 : Fin 32) s45.zero (by decide), g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb46, runBlock_reg _ _ _ (20 : Fin 32) s45.zero (by decide), g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb46, runBlock_reg _ _ _ (21 : Fin 32) s45.zero (by decide), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb46, runBlock_reg _ _ _ (22 : Fin 32) s45.zero (by decide), g45_22]
  have g46_26 : reg n46 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb46, runBlock_reg _ _ _ (26 : Fin 32) s45.zero (by decide), g45_26]
  have g46_10 : reg n46 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb46]; simp +decide only [runBlock, BInstr.run, p2vA3374, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_18, g45_19, g45_20, g45_21, g45_22, g45_26, s45.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g46_11 : reg n46 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1A0 := by
    rw [rb46]; simp +decide only [runBlock, BInstr.run, p2vA3374, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_18, g45_19, g45_20, g45_21, g45_22, g45_26, s45.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g46_12 : reg n46 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb46]; simp +decide only [runBlock, BInstr.run, p2vA3374, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_18, g45_19, g45_20, g45_21, g45_22, g45_26, s45.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk46 : P2vKeepL B n0.mem n46.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1)] := by rw [m46]; exact keep_kk45
  clear keep_kk45
  have b46_920 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m46]; exact b45_920
  have b46_9a0 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m46]; exact b45_9a0
  have q46_900 : ∀ j, j < 32 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m46]; exact q45_900 j hj
  have q46_cc0 : ∀ j, j < 32 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m46]; exact q45_cc0 j hj
  have a46_58 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m46]; exact a45_58
  have a46_78 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m46]; exact a45_78
  have a46_e0 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m46]; exact a45_e0
  have a46_100 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m46]; exact a45_100
  have a46_120 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m46]; exact a45_120
  have a46_140 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m46]; exact a45_140
  have a46_160 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m46]; exact a45_160
  have a46_180 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := by rw [m46]; exact a45_180
  have a46_1a0 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := by rw [m46]; exact a45_1a0
  have a46_1c0 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := by rw [m46]; exact a45_1c0
  have a46_200 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 rp 32) := by rw [m46]; exact a45_200
  have a46_900 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := by rw [m46]; exact a45_900
  have a46_980 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := by rw [m46]; exact a45_980
  have a46_c80 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m46]; exact a45_c80
  have a46_ca0 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m46]; exact a45_ca0
  have a46_cc0 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m46]; exact a45_cc0
  have a46_fe4 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m46]; exact a45_fe4
  clear a45_fe4 a45_cc0 a45_ca0 a45_c80 a45_980 a45_900 a45_200 a45_1c0 a45_1a0 a45_180 a45_160 a45_140 a45_120 a45_100 a45_e0 a45_78 a45_58 q45_cc0 q45_900 b45_920 b45_9a0 g45_26 g45_22 g45_21 g45_20 g45_19 g45_18 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 rg45 W45 K45 fr45 s45 d45
  -- 0x37C: memcpy
  obtain ⟨n47, P47, K47, X47⟩ := p2v_mc (c := 0x200) (d := 0x1A0) (N := 0x20) F E46 s46 p2v_at_37c p2v_at_380
    (by decide) (by decide) g46_2 g46_10 g46_11 g46_12
    (by decide) (by decide) (by decide)
  have s47 := P47.st
  have fr47 := P47.fr
  have t47 : Steps n0 n47 := t46.trans P47.steps
  have fR47 : ∀ x, P2vR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : P2vCode n47.mem := E46.fr F fr47
  have V47 : P2vSaves B n47.mem v := V46.keep K47 (by decide)
  have g47_2 : reg n47 sp = B + 0x21A0 := by rw [P47.regs sp (by decide), g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P47.regs (3 : Fin 32) (by decide), g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P47.regs (4 : Fin 32) (by decide), g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P47.regs (8 : Fin 32) (by decide), g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [P47.regs (9 : Fin 32) (by decide), g46_9]
  have g47_18 : reg n47 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P47.regs (18 : Fin 32) (by decide), g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = dg := by rw [P47.regs (19 : Fin 32) (by decide), g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P47.regs (20 : Fin 32) (by decide), g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P47.regs (21 : Fin 32) (by decide), g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P47.regs (22 : Fin 32) (by decide), g46_22]
  have g47_26 : reg n47 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P47.regs (26 : Fin 32) (by decide), g46_26]
  have keep_kk47 : P2vKeepL B n0.mem n47.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20)] := keep_kk46.trans K47.toL
  clear keep_kk46
  have b47_920 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K47.b8 (by decide) (by decide)).trans b46_920
  have b47_9a0 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K47.b8 (by decide) (by decide)).trans b46_9a0
  have q47_900 : ∀ j, j < 32 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => (K47.range (by decide) (by decide) j hj).trans (q46_900 j hj)
  have q47_cc0 : ∀ j, j < 32 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K47.range (by decide) (by decide) j hj).trans (q46_cc0 j hj)
  have a47_58 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K47.acc (by decide) (by decide)).trans a46_58
  have a47_78 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K47.acc (by decide) (by decide)).trans a46_78
  have a47_e0 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K47.acc (by decide) (by decide)).trans a46_e0
  have a47_100 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K47.acc (by decide) (by decide)).trans a46_100
  have a47_120 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K47.acc (by decide) (by decide)).trans a46_120
  have a47_140 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K47.acc (by decide) (by decide)).trans a46_140
  have a47_160 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K47.acc (by decide) (by decide)).trans a46_160
  have a47_180 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K47.acc (by decide) (by decide)).trans a46_180
  have a47_1a0 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (K47.acc (by decide) (by decide)).trans a46_1a0
  have a47_1c0 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := (K47.acc (by decide) (by decide)).trans a46_1c0
  have a47_900 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := (K47.acc (by decide) (by decide)).trans a46_900
  have a47_980 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K47.acc (by decide) (by decide)).trans a46_980
  have a47_c80 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K47.acc (by decide) (by decide)).trans a46_c80
  have a47_ca0 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K47.acc (by decide) (by decide)).trans a46_ca0
  have a47_cc0 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K47.acc (by decide) (by decide)).trans a46_cc0
  have a47_fe4 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K47.acc (by decide) (by decide)).trans a46_fe4
  have a47_200 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) := (accV_S 8 fun q hq => by
    rw [show 0x200 + q = 0x200 + (0x0 + q) by omega, X47 (0x0 + q) (by omega),
      show 0x1A0 + (0x0 + q) = 0x1A0 + q by omega]).trans a46_1a0
  clear a46_fe4 a46_cc0 a46_ca0 a46_c80 a46_980 a46_900 a46_200 a46_1c0 a46_1a0 a46_180 a46_160 a46_140 a46_120 a46_100 a46_e0 a46_78 a46_58 q46_cc0 q46_900 b46_9a0 b46_920 g46_12 g46_11 g46_10 g46_26 g46_22 g46_21 g46_20 g46_19 g46_18 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 rb46 s46 m46 u46 c46
  -- 0x384: sb
  obtain ⟨n48, d48, s48, fr48, K48, W48, rg48⟩ := p2v_sb F E47 s47 p2v_at_384 (off' := 0x388) (c := 0x220)
    (by decide) (by rw [g47_2]; p2v_addr) (by decide)
  have t48 : Steps n0 n48 := t47.trans d48
  have fR48 : ∀ x, P2vR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : P2vCode n48.mem := E47.fr F fr48
  have V48 : P2vSaves B n48.mem v := V47.keep K48 (by decide)
  have g48_2 : reg n48 sp = B + 0x21A0 := by rw [rg48 sp, g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg48 (3 : Fin 32), g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg48 (4 : Fin 32), g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rg48 (8 : Fin 32), g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rg48 (9 : Fin 32), g47_9]
  have g48_18 : reg n48 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rg48 (18 : Fin 32), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = dg := by rw [rg48 (19 : Fin 32), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rg48 (20 : Fin 32), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rg48 (21 : Fin 32), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg48 (22 : Fin 32), g47_22]
  have g48_26 : reg n48 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg48 (26 : Fin 32), g47_26]
  have keep_kk48 : P2vKeepL B n0.mem n48.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20), (0x220, 0x1)] := keep_kk47.trans K48.toL
  clear keep_kk47
  have b48_920 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K48.b8 (by decide) (by decide)).trans b47_920
  have b48_9a0 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K48.b8 (by decide) (by decide)).trans b47_9a0
  have b48_220 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W48, s47.zero]; rfl
  have q48_900 : ∀ j, j < 32 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => (K48.range (by decide) (by decide) j hj).trans (q47_900 j hj)
  have q48_cc0 : ∀ j, j < 32 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K48.range (by decide) (by decide) j hj).trans (q47_cc0 j hj)
  have a48_58 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K48.acc (by decide) (by decide)).trans a47_58
  have a48_78 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K48.acc (by decide) (by decide)).trans a47_78
  have a48_e0 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K48.acc (by decide) (by decide)).trans a47_e0
  have a48_100 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K48.acc (by decide) (by decide)).trans a47_100
  have a48_120 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K48.acc (by decide) (by decide)).trans a47_120
  have a48_140 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K48.acc (by decide) (by decide)).trans a47_140
  have a48_160 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K48.acc (by decide) (by decide)).trans a47_160
  have a48_180 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K48.acc (by decide) (by decide)).trans a47_180
  have a48_1a0 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (K48.acc (by decide) (by decide)).trans a47_1a0
  have a48_1c0 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := (K48.acc (by decide) (by decide)).trans a47_1c0
  have a48_200 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) := (K48.acc (by decide) (by decide)).trans a47_200
  have a48_900 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := (K48.acc (by decide) (by decide)).trans a47_900
  have a48_980 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K48.acc (by decide) (by decide)).trans a47_980
  have a48_c80 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K48.acc (by decide) (by decide)).trans a47_c80
  have a48_ca0 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K48.acc (by decide) (by decide)).trans a47_ca0
  have a48_cc0 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K48.acc (by decide) (by decide)).trans a47_cc0
  have a48_fe4 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := (K48.acc (by decide) (by decide)).trans a47_fe4
  clear a47_200 a47_fe4 a47_cc0 a47_ca0 a47_c80 a47_980 a47_900 a47_1c0 a47_1a0 a47_180 a47_160 a47_140 a47_120 a47_100 a47_e0 a47_78 a47_58 q47_cc0 q47_900 b47_9a0 b47_920 g47_26 g47_22 g47_21 g47_20 g47_19 g47_18 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 s47 X47 K47 P47
  -- 0x388
  obtain ⟨n49, c49, u49⟩ := s48.block p2vA3388 E48.self p2vA3388_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m49 : n49.mem = n48.mem := u49.mem
  have s49 : St n49.mem P2V n49 0x396 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
  have rb49 : ∀ q, reg n49 q = (runBlock p2vA3388 (n48.mem, reg n48)).2 q := fun q => by rw [u49.regs]
  have fr49 : ∀ x, P2vR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
  have t49 : Steps n0 n49 := t48.trans c49
  have fR49 : ∀ x, P2vR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : P2vCode n49.mem := E48.fr F fr49
  have V49 : P2vSaves B n49.mem v := V48.same m49
  have g49_2 : reg n49 sp = B + 0x21A0 := by
    rw [rb49, runBlock_reg _ _ _ sp s48.zero (by decide), g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb49, runBlock_reg _ _ _ (3 : Fin 32) s48.zero (by decide), g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb49, runBlock_reg _ _ _ (4 : Fin 32) s48.zero (by decide), g48_4]
  have g49_8 : reg n49 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb49, runBlock_reg _ _ _ (8 : Fin 32) s48.zero (by decide), g48_8]
  have g49_9 : reg n49 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb49, runBlock_reg _ _ _ (9 : Fin 32) s48.zero (by decide), g48_9]
  have g49_18 : reg n49 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb49, runBlock_reg _ _ _ (18 : Fin 32) s48.zero (by decide), g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = dg := by
    rw [rb49, runBlock_reg _ _ _ (19 : Fin 32) s48.zero (by decide), g48_19]
  have g49_20 : reg n49 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb49, runBlock_reg _ _ _ (20 : Fin 32) s48.zero (by decide), g48_20]
  have g49_21 : reg n49 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb49, runBlock_reg _ _ _ (21 : Fin 32) s48.zero (by decide), g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb49, runBlock_reg _ _ _ (22 : Fin 32) s48.zero (by decide), g48_22]
  have g49_26 : reg n49 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb49, runBlock_reg _ _ _ (26 : Fin 32) s48.zero (by decide), g48_26]
  have g49_10 : reg n49 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb49]; simp +decide only [runBlock, BInstr.run, p2vA3388, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g48_2, g48_3, g48_4, g48_8, g48_9, g48_18, g48_19, g48_20, g48_21, g48_22, g48_26, s48.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g49_11 : reg n49 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb49]; simp +decide only [runBlock, BInstr.run, p2vA3388, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g48_2, g48_3, g48_4, g48_8, g48_9, g48_18, g48_19, g48_20, g48_21, g48_22, g48_26, s48.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g49_12 : reg n49 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb49]; simp +decide only [runBlock, BInstr.run, p2vA3388, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g48_2, g48_3, g48_4, g48_8, g48_9, g48_18, g48_19, g48_20, g48_21, g48_22, g48_26, s48.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk49 : P2vKeepL B n0.mem n49.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20), (0x220, 0x1)] := by rw [m49]; exact keep_kk48
  clear keep_kk48
  have b49_220 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m49]; exact b48_220
  have b49_920 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m49]; exact b48_920
  have b49_9a0 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m49]; exact b48_9a0
  have q49_900 : ∀ j, j < 32 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m49]; exact q48_900 j hj
  have q49_cc0 : ∀ j, j < 32 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m49]; exact q48_cc0 j hj
  have a49_58 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m49]; exact a48_58
  have a49_78 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m49]; exact a48_78
  have a49_e0 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m49]; exact a48_e0
  have a49_100 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m49]; exact a48_100
  have a49_120 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m49]; exact a48_120
  have a49_140 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m49]; exact a48_140
  have a49_160 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m49]; exact a48_160
  have a49_180 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := by rw [m49]; exact a48_180
  have a49_1a0 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := by rw [m49]; exact a48_1a0
  have a49_1c0 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := by rw [m49]; exact a48_1c0
  have a49_200 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) := by rw [m49]; exact a48_200
  have a49_900 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := by rw [m49]; exact a48_900
  have a49_980 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := by rw [m49]; exact a48_980
  have a49_c80 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m49]; exact a48_c80
  have a49_ca0 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m49]; exact a48_ca0
  have a49_cc0 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m49]; exact a48_cc0
  have a49_fe4 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = beNat (memBytes M0 sq 32) := by rw [m49]; exact a48_fe4
  clear a48_fe4 a48_cc0 a48_ca0 a48_c80 a48_980 a48_900 a48_200 a48_1c0 a48_1a0 a48_180 a48_160 a48_140 a48_120 a48_100 a48_e0 a48_78 a48_58 q48_cc0 q48_900 b48_220 b48_9a0 b48_920 g48_26 g48_22 g48_21 g48_20 g48_19 g48_18 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 rg48 W48 K48 fr48 s48 d48
  -- 0x396: p2v_ms3F
  obtain ⟨n50, c50, s50, rk50, K50, fr50, Z50⟩ := p2v_ms3F (c := 0xFE4) (N := 0x24)
    F E49 s49 p2v_at_396 p2v_at_39a (by decide) (by decide)
    g49_10 g49_11 g49_12 (by decide)
  have t50 : Steps n0 n50 := t49.trans c50
  have fR50 : ∀ x, P2vR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : P2vCode n50.mem := E49.fr F fr50
  have V50 : P2vSaves B n50.mem v := V49.keepL K50 (by decide)
  have g50_2 : reg n50 sp = B + 0x21A0 := by rw [rk50 sp (by decide), g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk50 (3 : Fin 32) (by decide), g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk50 (4 : Fin 32) (by decide), g49_4]
  have g50_8 : reg n50 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk50 (8 : Fin 32) (by decide), g49_8]
  have g50_9 : reg n50 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rk50 (9 : Fin 32) (by decide), g49_9]
  have g50_18 : reg n50 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rk50 (18 : Fin 32) (by decide), g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = dg := by rw [rk50 (19 : Fin 32) (by decide), g49_19]
  have g50_20 : reg n50 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rk50 (20 : Fin 32) (by decide), g49_20]
  have g50_21 : reg n50 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [rk50 (21 : Fin 32) (by decide), g49_21]
  have g50_22 : reg n50 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk50 (22 : Fin 32) (by decide), g49_22]
  have g50_26 : reg n50 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk50 (26 : Fin 32) (by decide), g49_26]
  have keep_kk50 : P2vKeepL B n0.mem n50.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20), (0x220, 0x1), (0xFE4, 0x24)] := keep_kk49.trans K50
  clear keep_kk49
  have b50_220 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K50.b8 (by decide) (by decide)).trans b49_220
  have b50_920 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K50.b8 (by decide) (by decide)).trans b49_920
  have b50_9a0 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K50.b8 (by decide) (by decide)).trans b49_9a0
  have q50_900 : ∀ j, j < 32 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => (K50.range (by decide) (by decide) j hj).trans (q49_900 j hj)
  have q50_cc0 : ∀ j, j < 32 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K50.range (by decide) (by decide) j hj).trans (q49_cc0 j hj)
  have a50_58 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K50.acc (by decide) (by decide)).trans a49_58
  have a50_78 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K50.acc (by decide) (by decide)).trans a49_78
  have a50_e0 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K50.acc (by decide) (by decide)).trans a49_e0
  have a50_100 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K50.acc (by decide) (by decide)).trans a49_100
  have a50_120 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K50.acc (by decide) (by decide)).trans a49_120
  have a50_140 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K50.acc (by decide) (by decide)).trans a49_140
  have a50_160 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K50.acc (by decide) (by decide)).trans a49_160
  have a50_180 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K50.acc (by decide) (by decide)).trans a49_180
  have a50_1a0 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (K50.acc (by decide) (by decide)).trans a49_1a0
  have a50_1c0 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := (K50.acc (by decide) (by decide)).trans a49_1c0
  have a50_200 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) := (K50.acc (by decide) (by decide)).trans a49_200
  have a50_900 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := (K50.acc (by decide) (by decide)).trans a49_900
  have a50_980 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := (K50.acc (by decide) (by decide)).trans a49_980
  have a50_c80 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K50.acc (by decide) (by decide)).trans a49_c80
  have a50_ca0 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K50.acc (by decide) (by decide)).trans a49_ca0
  have a50_cc0 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K50.acc (by decide) (by decide)).trans a49_cc0
  have a50_fe4 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := acc0_of_fill fun j hj => by rw [show 0xFE4 + j = 0xFE4 + (0x0 + j) by omega]; exact Z50 _ (by omega)
  have b50_1004 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = 0 := by rw [show 0x1004 = 0xFE4 + 0x20 from rfl]; exact Z50 _ (by decide)
  clear a49_fe4 a49_cc0 a49_ca0 a49_c80 a49_980 a49_900 a49_200 a49_1c0 a49_1a0 a49_180 a49_160 a49_140 a49_120 a49_100 a49_e0 a49_78 a49_58 q49_cc0 q49_900 b49_9a0 b49_920 b49_220 g49_12 g49_11 g49_10 g49_26 g49_22 g49_21 g49_20 g49_19 g49_18 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 rb49 s49 m49 u49 c49
  -- 0x39E
  obtain ⟨n51, c51, u51⟩ := s50.block p2vA339e E50.self p2vA339e_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m51 : n51.mem = n50.mem := u51.mem
  have s51 : St n51.mem P2V n51 0x3B2 (reg n51) := ⟨u51.pc, rfl, fun _ => rfl⟩
  have rb51 : ∀ q, reg n51 q = (runBlock p2vA339e (n50.mem, reg n50)).2 q := fun q => by rw [u51.regs]
  have fr51 : ∀ x, P2vR B x → n51.mem x = n50.mem x := fun x _ => by rw [m51]
  have t51 : Steps n0 n51 := t50.trans c51
  have fR51 : ∀ x, P2vR B x → n51.mem x = M0 x := fun x hx => (fr51 x hx).trans (fR50 x hx)
  have E51 : P2vCode n51.mem := E50.fr F fr51
  have V51 : P2vSaves B n51.mem v := V50.same m51
  have g51_2 : reg n51 sp = B + 0x21A0 := by
    rw [rb51, runBlock_reg _ _ _ sp s50.zero (by decide), g50_2]
  have g51_3 : reg n51 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb51, runBlock_reg _ _ _ (3 : Fin 32) s50.zero (by decide), g50_3]
  have g51_4 : reg n51 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb51, runBlock_reg _ _ _ (4 : Fin 32) s50.zero (by decide), g50_4]
  have g51_8 : reg n51 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb51, runBlock_reg _ _ _ (8 : Fin 32) s50.zero (by decide), g50_8]
  have g51_9 : reg n51 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb51, runBlock_reg _ _ _ (9 : Fin 32) s50.zero (by decide), g50_9]
  have g51_18 : reg n51 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb51, runBlock_reg _ _ _ (18 : Fin 32) s50.zero (by decide), g50_18]
  have g51_19 : reg n51 (19 : Fin 32) = dg := by
    rw [rb51, runBlock_reg _ _ _ (19 : Fin 32) s50.zero (by decide), g50_19]
  have g51_20 : reg n51 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb51, runBlock_reg _ _ _ (20 : Fin 32) s50.zero (by decide), g50_20]
  have g51_21 : reg n51 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by
    rw [rb51, runBlock_reg _ _ _ (21 : Fin 32) s50.zero (by decide), g50_21]
  have g51_22 : reg n51 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb51, runBlock_reg _ _ _ (22 : Fin 32) s50.zero (by decide), g50_22]
  have g51_26 : reg n51 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb51, runBlock_reg _ _ _ (26 : Fin 32) s50.zero (by decide), g50_26]
  have g51_10 : reg n51 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb51]; simp +decide only [runBlock, BInstr.run, p2vA339e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g50_2, g50_3, g50_4, g50_8, g50_9, g50_18, g50_19, g50_20, g50_21, g50_22, g50_26, s50.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g51_11 : reg n51 a1 = BitVec.ofNat 32 (img% p256OneAddress) := by
    rw [rb51]; simp +decide only [runBlock, BInstr.run, p2vA339e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g50_2, g50_3, g50_4, g50_8, g50_9, g50_18, g50_19, g50_20, g50_21, g50_22, g50_26, s50.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g51_12 : reg n51 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb51]; simp +decide only [runBlock, BInstr.run, p2vA339e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g50_2, g50_3, g50_4, g50_8, g50_9, g50_18, g50_19, g50_20, g50_21, g50_22, g50_26, s50.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk51 : P2vKeepL B n0.mem n51.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20), (0x220, 0x1), (0xFE4, 0x24)] := by rw [m51]; exact keep_kk50
  clear keep_kk50
  have b51_220 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m51]; exact b50_220
  have b51_920 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m51]; exact b50_920
  have b51_9a0 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m51]; exact b50_9a0
  have b51_1004 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = 0 := by rw [m51]; exact b50_1004
  have q51_900 : ∀ j, j < 32 → n51.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m51]; exact q50_900 j hj
  have q51_cc0 : ∀ j, j < 32 → n51.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m51]; exact q50_cc0 j hj
  have a51_58 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m51]; exact a50_58
  have a51_78 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m51]; exact a50_78
  have a51_e0 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m51]; exact a50_e0
  have a51_100 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m51]; exact a50_100
  have a51_120 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m51]; exact a50_120
  have a51_140 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m51]; exact a50_140
  have a51_160 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m51]; exact a50_160
  have a51_180 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := by rw [m51]; exact a50_180
  have a51_1a0 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := by rw [m51]; exact a50_1a0
  have a51_1c0 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := by rw [m51]; exact a50_1c0
  have a51_200 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) := by rw [m51]; exact a50_200
  have a51_900 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := by rw [m51]; exact a50_900
  have a51_980 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = beNat (memBytes M0 sq 32) := by rw [m51]; exact a50_980
  have a51_c80 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m51]; exact a50_c80
  have a51_ca0 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m51]; exact a50_ca0
  have a51_cc0 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m51]; exact a50_cc0
  have a51_fe4 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := by rw [m51]; exact a50_fe4
  clear b50_1004 a50_fe4 a50_cc0 a50_ca0 a50_c80 a50_980 a50_900 a50_200 a50_1c0 a50_1a0 a50_180 a50_160 a50_140 a50_120 a50_100 a50_e0 a50_78 a50_58 q50_cc0 q50_900 b50_9a0 b50_920 b50_220 g50_26 g50_22 g50_21 g50_20 g50_19 g50_18 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 Z50 fr50 K50 rk50 s50 c50
  -- 0x3B2: memcpy from outside the stack
  obtain ⟨n52, P52, K52, X52⟩ := p2v_mcRo2 (c := 0x980) (N := 0x20) F RS E51 s51 p2v_at_3b2 p2v_at_3b6
    (by decide) (by decide) g51_2 g51_10 g51_11 g51_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s52 := P52.st
  have fr52 := P52.fr
  have t52 : Steps n0 n52 := t51.trans P52.steps
  have fR52 : ∀ x, P2vR B x → n52.mem x = M0 x := fun x hx => (fr52 x hx).trans (fR51 x hx)
  have E52 : P2vCode n52.mem := E51.fr F fr52
  have V52 : P2vSaves B n52.mem v := V51.keep K52 (by decide)
  have g52_2 : reg n52 sp = B + 0x21A0 := by rw [P52.regs sp (by decide), g51_2]
  have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P52.regs (3 : Fin 32) (by decide), g51_3]
  have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P52.regs (4 : Fin 32) (by decide), g51_4]
  have g52_8 : reg n52 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P52.regs (8 : Fin 32) (by decide), g51_8]
  have g52_9 : reg n52 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [P52.regs (9 : Fin 32) (by decide), g51_9]
  have g52_18 : reg n52 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [P52.regs (18 : Fin 32) (by decide), g51_18]
  have g52_19 : reg n52 (19 : Fin 32) = dg := by rw [P52.regs (19 : Fin 32) (by decide), g51_19]
  have g52_20 : reg n52 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [P52.regs (20 : Fin 32) (by decide), g51_20]
  have g52_21 : reg n52 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCC0 := by rw [P52.regs (21 : Fin 32) (by decide), g51_21]
  have g52_22 : reg n52 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P52.regs (22 : Fin 32) (by decide), g51_22]
  have g52_26 : reg n52 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P52.regs (26 : Fin 32) (by decide), g51_26]
  have keep_kk52 : P2vKeepL B n0.mem n52.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20), (0x220, 0x1), (0xFE4, 0x24), (0x980, 0x20)] := keep_kk51.trans K52.toL
  clear keep_kk51
  have b52_220 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K52.b8 (by decide) (by decide)).trans b51_220
  have b52_920 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K52.b8 (by decide) (by decide)).trans b51_920
  have b52_9a0 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := (K52.b8 (by decide) (by decide)).trans b51_9a0
  have b52_1004 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = 0 := (K52.b8 (by decide) (by decide)).trans b51_1004
  have q52_900 : ∀ j, j < 32 → n52.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => (K52.range (by decide) (by decide) j hj).trans (q51_900 j hj)
  have q52_cc0 : ∀ j, j < 32 → n52.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K52.range (by decide) (by decide) j hj).trans (q51_cc0 j hj)
  have a52_58 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K52.acc (by decide) (by decide)).trans a51_58
  have a52_78 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K52.acc (by decide) (by decide)).trans a51_78
  have a52_e0 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K52.acc (by decide) (by decide)).trans a51_e0
  have a52_100 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K52.acc (by decide) (by decide)).trans a51_100
  have a52_120 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K52.acc (by decide) (by decide)).trans a51_120
  have a52_140 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K52.acc (by decide) (by decide)).trans a51_140
  have a52_160 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K52.acc (by decide) (by decide)).trans a51_160
  have a52_180 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K52.acc (by decide) (by decide)).trans a51_180
  have a52_1a0 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (K52.acc (by decide) (by decide)).trans a51_1a0
  have a52_1c0 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := (K52.acc (by decide) (by decide)).trans a51_1c0
  have a52_200 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) := (K52.acc (by decide) (by decide)).trans a51_200
  have a52_900 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := (K52.acc (by decide) (by decide)).trans a51_900
  have a52_c80 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K52.acc (by decide) (by decide)).trans a51_c80
  have a52_ca0 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K52.acc (by decide) (by decide)).trans a51_ca0
  have a52_cc0 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K52.acc (by decide) (by decide)).trans a51_cc0
  have a52_fe4 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := (K52.acc (by decide) (by decide)).trans a51_fe4
  have q52_980 : ∀ j, j < 32 → n52.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256OneAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X52 j hj).trans (fR51 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a52_980 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 := acc_of_frame q52_980
  clear a51_fe4 a51_cc0 a51_ca0 a51_c80 a51_980 a51_900 a51_200 a51_1c0 a51_1a0 a51_180 a51_160 a51_140 a51_120 a51_100 a51_e0 a51_78 a51_58 q51_cc0 q51_900 b51_1004 b51_9a0 b51_920 b51_220 g51_12 g51_11 g51_10 g51_26 g51_22 g51_21 g51_20 g51_19 g51_18 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 rb51 s51 m51 u51 c51
  -- 0x3BA
  obtain ⟨n53, c53, u53⟩ := s52.block p2vA33ba E52.self p2vA33ba_end
    ⟨trivial, trivial⟩
  have m53 : n53.mem = n52.mem := u53.mem
  have s53 : St n53.mem P2V n53 0x3BC (reg n53) := ⟨u53.pc, rfl, fun _ => rfl⟩
  have rb53 : ∀ q, reg n53 q = (runBlock p2vA33ba (n52.mem, reg n52)).2 q := fun q => by rw [u53.regs]
  have fr53 : ∀ x, P2vR B x → n53.mem x = n52.mem x := fun x _ => by rw [m53]
  have t53 : Steps n0 n53 := t52.trans c53
  have fR53 : ∀ x, P2vR B x → n53.mem x = M0 x := fun x hx => (fr53 x hx).trans (fR52 x hx)
  have E53 : P2vCode n53.mem := E52.fr F fr53
  have V53 : P2vSaves B n53.mem v := V52.same m53
  have g53_2 : reg n53 sp = B + 0x21A0 := by
    rw [rb53, runBlock_reg _ _ _ sp s52.zero (by decide), g52_2]
  have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb53, runBlock_reg _ _ _ (3 : Fin 32) s52.zero (by decide), g52_3]
  have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb53, runBlock_reg _ _ _ (4 : Fin 32) s52.zero (by decide), g52_4]
  have g53_8 : reg n53 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb53, runBlock_reg _ _ _ (8 : Fin 32) s52.zero (by decide), g52_8]
  have g53_9 : reg n53 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [rb53, runBlock_reg _ _ _ (9 : Fin 32) s52.zero (by decide), g52_9]
  have g53_18 : reg n53 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb53, runBlock_reg _ _ _ (18 : Fin 32) s52.zero (by decide), g52_18]
  have g53_19 : reg n53 (19 : Fin 32) = dg := by
    rw [rb53, runBlock_reg _ _ _ (19 : Fin 32) s52.zero (by decide), g52_19]
  have g53_20 : reg n53 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb53, runBlock_reg _ _ _ (20 : Fin 32) s52.zero (by decide), g52_20]
  have g53_22 : reg n53 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb53, runBlock_reg _ _ _ (22 : Fin 32) s52.zero (by decide), g52_22]
  have g53_26 : reg n53 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb53, runBlock_reg _ _ _ (26 : Fin 32) s52.zero (by decide), g52_26]
  have g53_21 : reg n53 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb53]; simp +decide only [runBlock, BInstr.run, p2vA33ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g52_2, g52_3, g52_4, g52_8, g52_9, g52_18, g52_19, g52_20, g52_21, g52_22, g52_26, s52.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk53 : P2vKeepL B n0.mem n53.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20), (0x220, 0x1), (0xFE4, 0x24), (0x980, 0x20)] := by rw [m53]; exact keep_kk52
  clear keep_kk52
  have b53_220 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m53]; exact b52_220
  have b53_920 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m53]; exact b52_920
  have b53_9a0 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (1 : BitVec 8) := by rw [m53]; exact b52_9a0
  have b53_1004 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = 0 := by rw [m53]; exact b52_1004
  have q53_900 : ∀ j, j < 32 → n53.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m53]; exact q52_900 j hj
  have q53_980 : ∀ j, j < 32 → n53.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256OneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m53]; exact q52_980 j hj
  have q53_cc0 : ∀ j, j < 32 → n53.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m53]; exact q52_cc0 j hj
  have a53_58 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m53]; exact a52_58
  have a53_78 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m53]; exact a52_78
  have a53_e0 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m53]; exact a52_e0
  have a53_100 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m53]; exact a52_100
  have a53_120 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m53]; exact a52_120
  have a53_140 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m53]; exact a52_140
  have a53_160 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m53]; exact a52_160
  have a53_180 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := by rw [m53]; exact a52_180
  have a53_1a0 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := by rw [m53]; exact a52_1a0
  have a53_1c0 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := by rw [m53]; exact a52_1c0
  have a53_200 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) := by rw [m53]; exact a52_200
  have a53_900 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := by rw [m53]; exact a52_900
  have a53_980 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 := by rw [m53]; exact a52_980
  have a53_c80 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m53]; exact a52_c80
  have a53_ca0 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m53]; exact a52_ca0
  have a53_cc0 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m53]; exact a52_cc0
  have a53_fe4 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := by rw [m53]; exact a52_fe4
  clear a52_980 q52_980 a52_fe4 a52_cc0 a52_ca0 a52_c80 a52_900 a52_200 a52_1c0 a52_1a0 a52_180 a52_160 a52_140 a52_120 a52_100 a52_e0 a52_78 a52_58 q52_cc0 q52_900 b52_1004 b52_9a0 b52_920 b52_220 g52_26 g52_22 g52_21 g52_20 g52_19 g52_18 g52_9 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 fr52 s52 X52 K52 P52
  -- 0x3BC: sb
  obtain ⟨n54, d54, s54, fr54, K54, W54, rg54⟩ := p2v_sb F E53 s53 p2v_at_3bc (off' := 0x3C0) (c := 0x9A0)
    (by decide) (by rw [g53_26]; p2v_addr) (by decide)
  have t54 : Steps n0 n54 := t53.trans d54
  have fR54 : ∀ x, P2vR B x → n54.mem x = M0 x := fun x hx => (fr54 x hx).trans (fR53 x hx)
  have E54 : P2vCode n54.mem := E53.fr F fr54
  have V54 : P2vSaves B n54.mem v := V53.keep K54 (by decide)
  have g54_2 : reg n54 sp = B + 0x21A0 := by rw [rg54 sp, g53_2]
  have g54_3 : reg n54 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg54 (3 : Fin 32), g53_3]
  have g54_4 : reg n54 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg54 (4 : Fin 32), g53_4]
  have g54_8 : reg n54 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rg54 (8 : Fin 32), g53_8]
  have g54_9 : reg n54 (9 : Fin 32) = BitVec.ofNat 32 (img% p256IdentityAddress) := by rw [rg54 (9 : Fin 32), g53_9]
  have g54_18 : reg n54 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by rw [rg54 (18 : Fin 32), g53_18]
  have g54_19 : reg n54 (19 : Fin 32) = dg := by rw [rg54 (19 : Fin 32), g53_19]
  have g54_20 : reg n54 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by rw [rg54 (20 : Fin 32), g53_20]
  have g54_21 : reg n54 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg54 (21 : Fin 32), g53_21]
  have g54_22 : reg n54 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg54 (22 : Fin 32), g53_22]
  have g54_26 : reg n54 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg54 (26 : Fin 32), g53_26]
  have keep_kk54 : P2vKeepL B n0.mem n54.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20), (0x220, 0x1), (0xFE4, 0x24), (0x980, 0x20), (0x9A0, 0x1)] := keep_kk53.trans K54.toL
  clear keep_kk53
  have b54_220 : n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K54.b8 (by decide) (by decide)).trans b53_220
  have b54_920 : n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K54.b8 (by decide) (by decide)).trans b53_920
  have b54_1004 : n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = 0 := (K54.b8 (by decide) (by decide)).trans b53_1004
  have b54_9a0 : n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W54, s53.zero]; rfl
  have q54_900 : ∀ j, j < 32 → n54.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => (K54.range (by decide) (by decide) j hj).trans (q53_900 j hj)
  have q54_980 : ∀ j, j < 32 → n54.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256OneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K54.range (by decide) (by decide) j hj).trans (q53_980 j hj)
  have q54_cc0 : ∀ j, j < 32 → n54.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => (K54.range (by decide) (by decide) j hj).trans (q53_cc0 j hj)
  have a54_58 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K54.acc (by decide) (by decide)).trans a53_58
  have a54_78 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K54.acc (by decide) (by decide)).trans a53_78
  have a54_e0 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := (K54.acc (by decide) (by decide)).trans a53_e0
  have a54_100 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := (K54.acc (by decide) (by decide)).trans a53_100
  have a54_120 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := (K54.acc (by decide) (by decide)).trans a53_120
  have a54_140 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := (K54.acc (by decide) (by decide)).trans a53_140
  have a54_160 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K54.acc (by decide) (by decide)).trans a53_160
  have a54_180 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := (K54.acc (by decide) (by decide)).trans a53_180
  have a54_1a0 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := (K54.acc (by decide) (by decide)).trans a53_1a0
  have a54_1c0 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := (K54.acc (by decide) (by decide)).trans a53_1c0
  have a54_200 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) := (K54.acc (by decide) (by decide)).trans a53_200
  have a54_900 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := (K54.acc (by decide) (by decide)).trans a53_900
  have a54_980 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 := (K54.acc (by decide) (by decide)).trans a53_980
  have a54_c80 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := (K54.acc (by decide) (by decide)).trans a53_c80
  have a54_ca0 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := (K54.acc (by decide) (by decide)).trans a53_ca0
  have a54_cc0 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := (K54.acc (by decide) (by decide)).trans a53_cc0
  have a54_fe4 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := (K54.acc (by decide) (by decide)).trans a53_fe4
  clear a53_fe4 a53_cc0 a53_ca0 a53_c80 a53_980 a53_900 a53_200 a53_1c0 a53_1a0 a53_180 a53_160 a53_140 a53_120 a53_100 a53_e0 a53_78 a53_58 q53_cc0 q53_980 q53_900 b53_1004 b53_9a0 b53_920 b53_220 g53_21 g53_26 g53_22 g53_20 g53_19 g53_18 g53_9 g53_8 g53_4 g53_3 g53_2 V53 E53 fR53 t53 fr53 rb53 s53 m53 u53 c53
  -- 0x3C0
  obtain ⟨n55, c55, u55⟩ := s54.block p2vA33c0 E54.self p2vA33c0_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m55 : n55.mem = n54.mem := u55.mem
  have s55 : St n55.mem P2V n55 0x3E0 (reg n55) := ⟨u55.pc, rfl, fun _ => rfl⟩
  have rb55 : ∀ q, reg n55 q = (runBlock p2vA33c0 (n54.mem, reg n54)).2 q := fun q => by rw [u55.regs]
  have fr55 : ∀ x, P2vR B x → n55.mem x = n54.mem x := fun x _ => by rw [m55]
  have t55 : Steps n0 n55 := t54.trans c55
  have fR55 : ∀ x, P2vR B x → n55.mem x = M0 x := fun x hx => (fr55 x hx).trans (fR54 x hx)
  have E55 : P2vCode n55.mem := E54.fr F fr55
  have V55 : P2vSaves B n55.mem v := V54.same m55
  have g55_2 : reg n55 sp = B + 0x21A0 := by
    rw [rb55, runBlock_reg _ _ _ sp s54.zero (by decide), g54_2]
  have g55_3 : reg n55 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb55, runBlock_reg _ _ _ (3 : Fin 32) s54.zero (by decide), g54_3]
  have g55_4 : reg n55 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb55, runBlock_reg _ _ _ (4 : Fin 32) s54.zero (by decide), g54_4]
  have g55_18 : reg n55 (18 : Fin 32) = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb55, runBlock_reg _ _ _ (18 : Fin 32) s54.zero (by decide), g54_18]
  have g55_20 : reg n55 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb55, runBlock_reg _ _ _ (20 : Fin 32) s54.zero (by decide), g54_20]
  have g55_21 : reg n55 (21 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb55, runBlock_reg _ _ _ (21 : Fin 32) s54.zero (by decide), g54_21]
  have g55_22 : reg n55 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb55, runBlock_reg _ _ _ (22 : Fin 32) s54.zero (by decide), g54_22]
  have g55_26 : reg n55 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb55, runBlock_reg _ _ _ (26 : Fin 32) s54.zero (by decide), g54_26]
  have g55_8 : reg n55 (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1 := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, p2vA33c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_18, g54_19, g54_20, g54_21, g54_22, g54_26, s54.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g55_9 : reg n55 (9 : Fin 32) = BitVec.ofNat 32 0x332E3755 := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, p2vA33c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_18, g54_19, g54_20, g54_21, g54_22, g54_26, s54.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g55_10 : reg n55 a0 = BitVec.ofNat 32 0x11FF4000 := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, p2vA33c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_18, g54_19, g54_20, g54_21, g54_22, g54_26, s54.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g55_11 : reg n55 a1 = BitVec.ofNat 32 0x332E3000 := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, p2vA33c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_18, g54_19, g54_20, g54_21, g54_22, g54_26, s54.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g55_19 : reg n55 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, p2vA33c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_18, g54_19, g54_20, g54_21, g54_22, g54_26, s54.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g55_23 : reg n55 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, p2vA33c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_18, g54_19, g54_20, g54_21, g54_22, g54_26, s54.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g55_24 : reg n55 (24 : Fin 32) = BitVec.ofNat 32 0x24F := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, p2vA33c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_18, g54_19, g54_20, g54_21, g54_22, g54_26, s54.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g55_27 : reg n55 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, p2vA33c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_18, g54_19, g54_20, g54_21, g54_22, g54_26, s54.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk55 : P2vKeepL B n0.mem n55.mem [(0xC80, 0x20), (0xCA0, 0x20), (0x980, 0x40), (0xE0, 0x40), (0xCA0, 0x20), (0xC80, 0x20), (0xCC0, 0x20), (0x120, 0x20), (0x140, 0x20), (0x160, 0x20), (0xC80, 0x20), (0x980, 0x21), (0xC80, 0x20), (0xFE4, 0x20), (0x980, 0x21), (0xCA0, 0x20), (0x180, 0x20), (0x1A0, 0x20), (0x1C0, 0x20), (0x900, 0x20), (0x920, 0x1), (0x200, 0x20), (0x220, 0x1), (0xFE4, 0x24), (0x980, 0x20), (0x9A0, 0x1)] := by rw [m55]; exact keep_kk54
  clear keep_kk54
  have b55_220 : n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m55]; exact b54_220
  have b55_920 : n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m55]; exact b54_920
  have b55_9a0 : n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m55]; exact b54_9a0
  have b55_1004 : n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = 0 := by rw [m55]; exact b54_1004
  have q55_900 : ∀ j, j < 32 → n55.mem (B + 0x21A0 + BitVec.ofNat 32 (0x900 + j)) = M0 ((BitVec.ofNat 32 (img% b2sOrder256Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m55]; exact q54_900 j hj
  have q55_980 : ∀ j, j < 32 → n55.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256OneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m55]; exact q54_980 j hj
  have q55_cc0 : ∀ j, j < 32 → n55.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256MontOneAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m55]; exact q54_cc0 j hj
  have a55_58 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m55]; exact a54_58
  have a55_78 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m55]; exact a54_78
  have a55_e0 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) 8 = beNat (memBytes M0 rp 32) := by rw [m55]; exact a54_e0
  have a55_100 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) 8 = beNat (memBytes M0 sq 32) := by rw [m55]; exact a54_100
  have a55_120 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = gsVal M0 pk 1 * 2 ^ 256 % p256 := by rw [m55]; exact a54_120
  have a55_140 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = gsVal M0 pk 0x21 * 2 ^ 256 % p256 := by rw [m55]; exact a54_140
  have a55_160 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m55]; exact a54_160
  have a55_180 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = beNat (memBytes M0 rp 32) := by rw [m55]; exact a54_180
  have a55_1a0 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = beNat (memBytes M0 sq 32) := by rw [m55]; exact a54_1a0
  have a55_1c0 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = beNat (memBytes M0 (dg) 32) % C3.p256.n := by rw [m55]; exact a54_1c0
  have a55_200 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = beNat (memBytes M0 sq 32) := by rw [m55]; exact a54_200
  have a55_900 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := by rw [m55]; exact a54_900
  have a55_980 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 := by rw [m55]; exact a54_980
  have a55_c80 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = beNat (memBytes M0 rp 32) := by rw [m55]; exact a54_c80
  have a55_ca0 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = beNat (memBytes M0 sq 32) := by rw [m55]; exact a54_ca0
  have a55_cc0 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 := by rw [m55]; exact a54_cc0
  have a55_fe4 : accV n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := by rw [m55]; exact a54_fe4
  clear a54_fe4 a54_cc0 a54_ca0 a54_c80 a54_980 a54_900 a54_200 a54_1c0 a54_1a0 a54_180 a54_160 a54_140 a54_120 a54_100 a54_e0 a54_78 a54_58 q54_cc0 q54_980 q54_900 b54_9a0 b54_1004 b54_920 b54_220 g54_26 g54_22 g54_21 g54_20 g54_19 g54_18 g54_9 g54_8 g54_4 g54_3 g54_2 V54 E54 fR54 t54 rg54 W54 K54 fr54 s54 d54
  exact .inr ⟨n55, t55, s55, E55, V55, fR55, g55_2, g55_3, g55_4, g55_8, g55_9, g55_19, g55_21, g55_22, g55_23, g55_24, g55_26, g55_27, b55_220, b55_920, b55_9a0, b55_1004, q55_900, q55_980, q55_cc0, a55_58, a55_78, a55_e0, a55_100, a55_120, a55_140, a55_160, a55_180, a55_1a0, a55_1c0, a55_200, a55_900, a55_980, a55_c80, a55_ca0, a55_cc0, a55_fe4, keep_kk55.mono (by decide)⟩

end C3.RV32.P2v
