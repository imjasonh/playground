import C3BootProofs.Proofs.P2vZLib2

/-!
# `p256VerifyPrehash`: the end of the check

From the inversion's exit at 0xF00 to 0x10C4: `d`, normalized by `f`'s sign, is `Z⁻¹` when `f` is 1 and `Z` is nonzero; the affine `x` of the sum, or the identity's, becomes a scalar, and the check returns 0 unless it equals `r`.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vZEf04 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x2F4, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x200, .aluImm .add a3 sp 0x7FF, .aluImm .add a3 a3 0x181, .alu .add (9 : Fin 32) x0 a4]
theorem p2vZEf04_end : blockEnd p256VerifyPrehashCode 0xF04 p2vZEf04 = some 0xF18 := by
  simp only [p2vZEf04]
  rw [blockEnd, p2v_at_f04]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f06]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f0a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f0c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f0e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f12]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f16]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEf20 : List BInstr :=
  [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x158, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x781]
theorem p2vZEf20_end : blockEnd p256VerifyPrehashCode 0xF20 p2vZEf20 = some 0xF30 := by
  simp only [p2vZEf20]
  rw [blockEnd, p2v_at_f20]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f24]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f28]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f2c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEf38 : List BInstr :=
  [.aluImm .and a0 a0 0xFF]
theorem p2vZEf38_end : blockEnd p256VerifyPrehashCode 0xF38 p2vZEf38 = some 0xF3C := by
  simp only [p2vZEf38]
  rw [blockEnd, p2v_at_f38]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEf3e : List BInstr :=
  [.alu .and a0 a0 a1]
theorem p2vZEf3e_end : blockEnd p256VerifyPrehashCode 0xF3E p2vZEf3e = some 0xF40 := by
  simp only [p2vZEf3e]
  rw [blockEnd, p2v_at_f3e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEf48 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .lui a1 0x1000, .aluImm .add a1 a1 0x2F4, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x20]
theorem p2vZEf48_end : blockEnd p256VerifyPrehashCode 0xF48 p2vZEf48 = some 0xF5E := by
  simp only [p2vZEf48]
  rw [blockEnd, p2v_at_f48]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f4a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f4e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f52]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f54]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f58]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f5a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEf6a : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]
theorem p2vZEf6a_end : blockEnd p256VerifyPrehashCode 0xF6A p2vZEf6a = some 0xF78 := by
  simp only [p2vZEf6a]
  rw [blockEnd, p2v_at_f6a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f6e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f72]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f76]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEf80 : List BInstr :=
  [.aluImm .and a3 (8 : Fin 32) 0xFF, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x7E5, .aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x481]
theorem p2vZEf80_end : blockEnd p256VerifyPrehashCode 0xF80 p2vZEf80 = some 0xF9C := by
  simp only [p2vZEf80]
  rw [blockEnd, p2v_at_f80]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f84]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f88]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f8c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f90]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f94]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_f98]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEfa8 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181]
theorem p2vZEfa8_end : blockEnd p256VerifyPrehashCode 0xFA8 p2vZEfa8 = some 0xFB8 := by
  simp only [p2vZEfa8]
  rw [blockEnd, p2v_at_fa8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fb0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fb4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEfc0 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]
theorem p2vZEfc0_end : blockEnd p256VerifyPrehashCode 0xFC0 p2vZEfc0 = some 0xFCE := by
  simp only [p2vZEfc0]
  rw [blockEnd, p2v_at_fc0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fc4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fc8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fcc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEfda : List BInstr :=
  [.aluImm .add a0 sp 0x200, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x7E5, .alu .add a3 x0 (8 : Fin 32)]
theorem p2vZEfda_end : blockEnd p256VerifyPrehashCode 0xFDA p2vZEfda = some 0xFEE := by
  simp only [p2vZEfda]
  rw [blockEnd, p2v_at_fda]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fdc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fe0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fe4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fe8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_fec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZEff6 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .lui a1 0x1000, .aluImm .add a1 a1 0x338, .alu .add a1 a1 sp, .aluImm .add a2 sp 0x200]
theorem p2vZEff6_end : blockEnd p256VerifyPrehashCode 0xFF6 p2vZEff6 = some 0x1008 := by
  simp only [p2vZEff6]
  rw [blockEnd, p2v_at_ff6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ffa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ffe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1000]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1004]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1006]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZE1010 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x4A1, .aluImm .add a2 sp 0x200, .lui a1 0x1000, .aluImm .add a1 a1 0x358, .alu .add a1 a1 sp]
theorem p2vZE1010_end : blockEnd p256VerifyPrehashCode 0x1010 p2vZE1010 = some 0x1022 := by
  simp only [p2vZE1010]
  rw [blockEnd, p2v_at_1010]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1014]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1018]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_101a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_101c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1020]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZE1032 : List BInstr :=
  [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0x29C, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481]
theorem p2vZE1032_end : blockEnd p256VerifyPrehashCode 0x1032 p2vZE1032 = some 0x104A := by
  simp only [p2vZE1032]
  rw [blockEnd, p2v_at_1032]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1036]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_103a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_103e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1042]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1046]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZE1052 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x398, .alu .add a0 a0 sp]
theorem p2vZE1052_end : blockEnd p256VerifyPrehashCode 0x1052 p2vZE1052 = some 0x105A := by
  simp only [p2vZE1052]
  rw [blockEnd, p2v_at_1052]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1054]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1058]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZE1062 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181]
theorem p2vZE1062_end : blockEnd p256VerifyPrehashCode 0x1062 p2vZE1062 = some 0x1072 := by
  simp only [p2vZE1062]
  rw [blockEnd, p2v_at_1062]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1066]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_106a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_106e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZE107a : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x398, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481]
theorem p2vZE107a_end : blockEnd p256VerifyPrehashCode 0x107A p2vZE107a = some 0x108A := by
  simp only [p2vZE107a]
  rw [blockEnd, p2v_at_107a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_107c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1080]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1082]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1086]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZE1092 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .lui a1 0x1000, .aluImm .add a1 a1 0x398, .alu .add a1 a1 sp]
theorem p2vZE1092_end : blockEnd p256VerifyPrehashCode 0x1092 p2vZE1092 = some 0x10A2 := by
  simp only [p2vZE1092]
  rw [blockEnd, p2v_at_1092]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_1096]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_109a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_109c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_10a0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZE10aa : List BInstr :=
  [.aluImm .add a0 sp 0x180, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481]
theorem p2vZE10aa_end : blockEnd p256VerifyPrehashCode 0x10AA p2vZE10aa = some 0x10B4 := by
  simp only [p2vZE10aa]
  rw [blockEnd, p2v_at_10aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_10ac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_10b0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZE10bc : List BInstr :=
  [.aluImm .and a0 a0 0xFF, .alu .sltu a0 x0 a0]
theorem p2vZE10bc_end : blockEnd p256VerifyPrehashCode 0x10BC p2vZE10bc = some 0x10C4 := by
  simp only [p2vZE10bc]
  rw [blockEnd, p2v_at_10bc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_10c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_ze {B dlo dhi rem nzw : Word} {fs gs ds es : BitVec 8} {rv X Y fv gv dv ev : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0xF00 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_14 : reg n0 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920)
    (g0_24 : reg n0 (24 : Fin 32) = dhi)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo)
    (a0_180 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv)
    (a0_200 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv)
    (a0_900 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv)
    (a0_980 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8)
    (a0_f80 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv)
    (a0_fe4 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev)
    (a0_1338 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X)
    (a0_1358 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y)
    (b0_220 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds)
    (b0_920 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs)
    (b0_fa0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs)
    (b0_1004 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es)
    (UC0 : P2vUpCode M0)
    (EC0 : P2vEcCode M0)
    (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode)
    (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code)
    (P2C0 : P2Code M0)
    (GDC0 : C3.RV32.Gd.GdCode M0)
    (P2D0 : P2Data M0)
    (SC0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode)
    (BY0 : BYEnv M0)
    (WN0 : P2vWnCode M0)
    (hfs : fs.toNat ≤ 1)
    (hds : ds.toNat ≤ 1)
    (hnz : nzw = 0 ∨ nzw = 1)
    (hX : X < p256)
    (hY : Y < p256)
    (hid : accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8 < p256)
    (hzi : normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) < p256) :
    (¬ ((rv = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n) ∧ True) ∧ P2vRet B v n0 0) ∨
    ((rv = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x10C4 (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' a0 = 1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y ∧
        leN (memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 0x20).reverse = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 ∧
        P2vKeepL B n0.mem n'.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20), (0x1398, 0x20), (0xC80, 0x20)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xF00: lbu
  obtain ⟨n1, d1, u1⟩ := s0.lbu E0.self p2v_at_f00 (off' := 0xF04) (by decide)
  have s1 : St n1.mem P2V n1 0xF04 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, P2vR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, P2vR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : P2vCode n1.mem := E0.fr F fr1
  have V1 : P2vSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_14 : reg n1 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_14]
  have g1_24 : reg n1 (24 : Fin 32) = dhi := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_12 : reg n1 a2 = (fs).zeroExtend 32 := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_14, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x680 = B + 0x21A0 + BitVec.ofNat 32 0xFA0 by p2v_addr, b0_fa0]
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have w1_10 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m1]; exact w0_10
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m1]; exact w0_40
  have b1_220 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m1]; exact b0_220
  have b1_920 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m1]; exact b0_920
  have b1_fa0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m1]; exact b0_fa0
  have b1_1004 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m1]; exact b0_1004
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m1]; exact a0_180
  have a1_200 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m1]; exact a0_200
  have a1_900 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m1]; exact a0_900
  have a1_980 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m1]; exact a0_980
  have a1_f80 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m1]; exact a0_f80
  have a1_fe4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m1]; exact a0_fe4
  have a1_1338 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m1]; exact a0_1338
  have a1_1358 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m1]; exact a0_1358
  -- 0xF04
  obtain ⟨n2, c2, u2⟩ := s1.block p2vZEf04 E1.self p2vZEf04_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem P2V n2 0xF18 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock p2vZEf04 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
  have fr2 : ∀ x, P2vR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : P2vCode n2.mem := E1.fr F fr2
  have V2 : P2vSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by
    rw [rb2, runBlock_reg _ _ _ sp s1.zero (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (3 : Fin 32) s1.zero (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (4 : Fin 32) s1.zero (by decide), g1_4]
  have g2_12 : reg n2 a2 = (fs).zeroExtend 32 := by
    rw [rb2, runBlock_reg _ _ _ a2 s1.zero (by decide), g1_12]
  have g2_14 : reg n2 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb2, runBlock_reg _ _ _ a4 s1.zero (by decide), g1_14]
  have g2_24 : reg n2 (24 : Fin 32) = dhi := by
    rw [rb2, runBlock_reg _ _ _ (24 : Fin 32) s1.zero (by decide), g1_24]
  have g2_9 : reg n2 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vZEf04, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_12, g1_14, g1_24, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x12F4 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vZEf04, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_12, g1_14, g1_24, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g2_11 : reg n2 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vZEf04, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_12, g1_14, g1_24, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g2_13 : reg n2 a3 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vZEf04, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_12, g1_14, g1_24, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_10 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m2]; exact w1_10
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m2]; exact w1_40
  have b2_220 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m2]; exact b1_220
  have b2_920 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m2]; exact b1_920
  have b2_fa0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m2]; exact b1_fa0
  have b2_1004 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m2]; exact b1_1004
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m2]; exact a1_180
  have a2_200 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m2]; exact a1_200
  have a2_900 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m2]; exact a1_900
  have a2_980 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m2]; exact a1_980
  have a2_f80 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m2]; exact a1_f80
  have a2_fe4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m2]; exact a1_fe4
  have a2_1338 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m2]; exact a1_1338
  have a2_1358 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m2]; exact a1_1358
  clear a1_1358 a1_1338 a1_fe4 a1_f80 a1_980 a1_900 a1_200 a1_180 b1_1004 b1_fa0 b1_920 b1_220 w1_40 w1_10 g1_12 g1_24 g1_14 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0xF18: p2v_nrm8Fs
  obtain ⟨n3, c3, s3, sp3, rk3, A3, K3, fr3⟩ := p2v_nrm8Fs (co := 0x12F4) (cx := 0x200)
    F E2 (UC0.p2v F fR2) (EC0.p2v F fR2) (codeIn_p2v F fR2 N80 (by decide) (by decide)) s2 p2v_at_f18 p2v_at_f1c (by decide) (by decide) g2_2
    g2_10 g2_11 g2_12 (zext_01 hfs) g2_13 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show 0x200 + 0x20 = 0x220 from rfl, b2_220]; exact hds)
  rw [show 0x200 + 0x20 = 0x220 from rfl, b2_220, a2_200,
    a2_980] at A3
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.keepL K3 (by decide)
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk3 (3 : Fin 32) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk3 (4 : Fin 32) (by decide), g2_4]
  have g3_9 : reg n3 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk3 (9 : Fin 32) (by decide), g2_9]
  have g3_24 : reg n3 (24 : Fin 32) = dhi := by rw [rk3 (24 : Fin 32) (by decide), g2_24]
  have g3_2 : reg n3 sp = B + 0x21A0 := sp3
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0x12F4, 0x20)] := keep_kk2.trans K3
  clear keep_kk2
  have w3_10 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K3.w32 (by decide) (by decide)).trans w2_10
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K3.w32 (by decide) (by decide)).trans w2_40
  have b3_220 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K3.b8 (by decide) (by decide)).trans b2_220
  have b3_920 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K3.b8 (by decide) (by decide)).trans b2_920
  have b3_fa0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K3.b8 (by decide) (by decide)).trans b2_fa0
  have b3_1004 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K3.b8 (by decide) (by decide)).trans b2_1004
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K3.acc (by decide) (by decide)).trans a2_180
  have a3_200 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K3.acc (by decide) (by decide)).trans a2_200
  have a3_900 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K3.acc (by decide) (by decide)).trans a2_900
  have a3_980 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K3.acc (by decide) (by decide)).trans a2_980
  have a3_f80 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K3.acc (by decide) (by decide)).trans a2_f80
  have a3_fe4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K3.acc (by decide) (by decide)).trans a2_fe4
  have a3_1338 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K3.acc (by decide) (by decide)).trans a2_1338
  have a3_1358 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K3.acc (by decide) (by decide)).trans a2_1358
  have a3_12f4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := A3
  clear a2_1358 a2_1338 a2_fe4 a2_f80 a2_980 a2_900 a2_200 a2_180 b2_1004 b2_fa0 b2_920 b2_220 w2_40 w2_10 g2_13 g2_11 g2_10 g2_9 g2_24 g2_14 g2_12 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0xF20
  obtain ⟨n4, c4, u4⟩ := s3.block p2vZEf20 E3.self p2vZEf20_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem P2V n4 0xF30 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock p2vZEf20 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  have fr4 : ∀ x, P2vR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by
    rw [rb4, runBlock_reg _ _ _ sp s3.zero (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb4, runBlock_reg _ _ _ (3 : Fin 32) s3.zero (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb4, runBlock_reg _ _ _ (4 : Fin 32) s3.zero (by decide), g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_24 : reg n4 (24 : Fin 32) = dhi := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vZEf20, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_9, g3_24, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g4_11 : reg n4 a1 = BitVec.ofNat 32 (img% p256OneAddress) := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vZEf20, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_9, g3_24, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0x12F4, 0x20)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_10 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m4]; exact w3_10
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m4]; exact w3_40
  have b4_220 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m4]; exact b3_220
  have b4_920 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m4]; exact b3_920
  have b4_fa0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m4]; exact b3_fa0
  have b4_1004 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m4]; exact b3_1004
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m4]; exact a3_180
  have a4_200 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m4]; exact a3_200
  have a4_900 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m4]; exact a3_900
  have a4_980 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m4]; exact a3_980
  have a4_f80 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m4]; exact a3_f80
  have a4_fe4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m4]; exact a3_fe4
  have a4_12f4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m4]; exact a3_12f4
  have a4_1338 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m4]; exact a3_1338
  have a4_1358 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m4]; exact a3_1358
  clear a3_12f4 a3_1358 a3_1338 a3_fe4 a3_f80 a3_980 a3_900 a3_200 a3_180 b3_1004 b3_fa0 b3_920 b3_220 w3_40 w3_10 g3_2 g3_24 g3_9 g3_4 g3_3 V3 E3 fR3 t3 fr3 K3 A3 rk3 sp3 s3 c3
  -- 0xF30: p2v_ueq8F
  obtain ⟨n5, c5, s5, sp5, rk5, a0_5, K5, fr5⟩ := p2v_ueq8F (cp := 0xF80)
    F E4 (codeIn_p2v F fR4 UE0 (by decide) (by decide)) s4 p2v_at_f30 p2v_at_f34 (by decide) (by decide) g4_2
    g4_10 g4_11 (by decide) (by decide) (by decide)
  rw [a4_f80, accV_dataR F fR4 (by decide) (by decide)] at a0_5
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, P2vR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : P2vCode n5.mem := E4.fr F fr5
  have V5 : P2vSaves B n5.mem v := V4.keepL K5 (by decide)
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk5 (3 : Fin 32) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk5 (4 : Fin 32) (by decide), g4_4]
  have g5_9 : reg n5 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk5 (9 : Fin 32) (by decide), g4_9]
  have g5_24 : reg n5 (24 : Fin 32) = dhi := by rw [rk5 (24 : Fin 32) (by decide), g4_24]
  have g5_2 : reg n5 sp = B + 0x21A0 := sp5
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0x12F4, 0x20)] := keep_kk4.trans K5
  clear keep_kk4
  have w5_10 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K5.w32 (by decide) (by decide)).trans w4_10
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K5.w32 (by decide) (by decide)).trans w4_40
  have b5_220 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K5.b8 (by decide) (by decide)).trans b4_220
  have b5_920 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K5.b8 (by decide) (by decide)).trans b4_920
  have b5_fa0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K5.b8 (by decide) (by decide)).trans b4_fa0
  have b5_1004 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K5.b8 (by decide) (by decide)).trans b4_1004
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K5.acc (by decide) (by decide)).trans a4_180
  have a5_200 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K5.acc (by decide) (by decide)).trans a4_200
  have a5_900 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K5.acc (by decide) (by decide)).trans a4_900
  have a5_980 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K5.acc (by decide) (by decide)).trans a4_980
  have a5_f80 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K5.acc (by decide) (by decide)).trans a4_f80
  have a5_fe4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K5.acc (by decide) (by decide)).trans a4_fe4
  have a5_12f4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K5.acc (by decide) (by decide)).trans a4_12f4
  have a5_1338 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K5.acc (by decide) (by decide)).trans a4_1338
  have a5_1358 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K5.acc (by decide) (by decide)).trans a4_1358
  clear a4_1358 a4_1338 a4_12f4 a4_fe4 a4_f80 a4_980 a4_900 a4_200 a4_180 b4_1004 b4_fa0 b4_920 b4_220 w4_40 w4_10 g4_11 g4_10 g4_24 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  have g5_10 : reg n5 a0 = (if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word) := a0_5
  -- 0xF38
  obtain ⟨n6, c6, u6⟩ := s5.block p2vZEf38 E5.self p2vZEf38_end
    ⟨trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem P2V n6 0xF3C (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock p2vZEf38 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have fr6 : ∀ x, P2vR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by
    rw [rb6, runBlock_reg _ _ _ sp s5.zero (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (3 : Fin 32) s5.zero (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (4 : Fin 32) s5.zero (by decide), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
  have g6_24 : reg n6 (24 : Fin 32) = dhi := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_10 : reg n6 a0 = ((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vZEf38, upd, ↓reduceIte]; rw [g5_10] <;> rfl
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0x12F4, 0x20)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_10 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m6]; exact w5_10
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m6]; exact w5_40
  have b6_220 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m6]; exact b5_220
  have b6_920 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m6]; exact b5_920
  have b6_fa0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m6]; exact b5_fa0
  have b6_1004 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m6]; exact b5_1004
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m6]; exact a5_180
  have a6_200 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m6]; exact a5_200
  have a6_900 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m6]; exact a5_900
  have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m6]; exact a5_980
  have a6_f80 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m6]; exact a5_f80
  have a6_fe4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m6]; exact a5_fe4
  have a6_12f4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m6]; exact a5_12f4
  have a6_1338 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m6]; exact a5_1338
  have a6_1358 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m6]; exact a5_1358
  clear a5_1358 a5_1338 a5_12f4 a5_fe4 a5_f80 a5_980 a5_900 a5_200 a5_180 b5_1004 b5_fa0 b5_920 b5_220 w5_40 w5_10 g5_2 g5_24 g5_9 g5_4 g5_3 V5 E5 fR5 t5 fr5 K5 a0_5 rk5 sp5 s5 c5
  -- 0xF3C: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self p2v_at_f3c (off' := 0xF3E) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x10 = B + 0x21A0 + BitVec.ofNat 32 0x10 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s7 : St n7.mem P2V n7 0xF3E (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, P2vR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_9 : reg n7 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
  have g7_10 : reg n7 a0 = ((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [u7.regs, upd_ne (by decide) (by decide), g6_10]
  have g7_24 : reg n7 (24 : Fin 32) = dhi := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
  have g7_11 : reg n7 a1 = nzw := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x10 = B + 0x21A0 + BitVec.ofNat 32 0x10 by p2v_addr, w6_10]
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0x12F4, 0x20)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_10 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m7]; exact w6_10
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m7]; exact w6_40
  have b7_220 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m7]; exact b6_220
  have b7_920 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m7]; exact b6_920
  have b7_fa0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m7]; exact b6_fa0
  have b7_1004 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m7]; exact b6_1004
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m7]; exact a6_180
  have a7_200 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m7]; exact a6_200
  have a7_900 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m7]; exact a6_900
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m7]; exact a6_980
  have a7_f80 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m7]; exact a6_f80
  have a7_fe4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m7]; exact a6_fe4
  have a7_12f4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m7]; exact a6_12f4
  have a7_1338 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m7]; exact a6_1338
  have a7_1358 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m7]; exact a6_1358
  clear a6_1358 a6_1338 a6_12f4 a6_fe4 a6_f80 a6_980 a6_900 a6_200 a6_180 b6_1004 b6_fa0 b6_920 b6_220 w6_40 w6_10 g6_10 g6_24 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6 g5_10
  -- 0xF3E
  obtain ⟨n8, c8, u8⟩ := s7.block p2vZEf3e E7.self p2vZEf3e_end
    ⟨trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem P2V n8 0xF40 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock p2vZEf3e (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have fr8 : ∀ x, P2vR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, P2vR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : P2vCode n8.mem := E7.fr F fr8
  have V8 : P2vSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by
    rw [rb8, runBlock_reg _ _ _ sp s7.zero (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (3 : Fin 32) s7.zero (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (4 : Fin 32) s7.zero (by decide), g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
  have g8_11 : reg n8 a1 = nzw := by
    rw [rb8, runBlock_reg _ _ _ a1 s7.zero (by decide), g7_11]
  have g8_24 : reg n8 (24 : Fin 32) = dhi := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_10 : reg n8 a0 = (((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw) := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vZEf3e, upd, ↓reduceIte]; rw [g7_10, g7_11] <;> rfl
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0x12F4, 0x20)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_10 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m8]; exact w7_10
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m8]; exact w7_40
  have b8_220 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m8]; exact b7_220
  have b8_920 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m8]; exact b7_920
  have b8_fa0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m8]; exact b7_fa0
  have b8_1004 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m8]; exact b7_1004
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m8]; exact a7_180
  have a8_200 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m8]; exact a7_200
  have a8_900 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m8]; exact a7_900
  have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m8]; exact a7_980
  have a8_f80 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m8]; exact a7_f80
  have a8_fe4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m8]; exact a7_fe4
  have a8_12f4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m8]; exact a7_12f4
  have a8_1338 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m8]; exact a7_1338
  have a8_1358 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m8]; exact a7_1358
  clear a7_1358 a7_1338 a7_12f4 a7_fe4 a7_f80 a7_980 a7_900 a7_200 a7_180 b7_1004 b7_fa0 b7_920 b7_220 w7_40 w7_10 g7_11 g7_24 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0xF40: p2v_bbF
  obtain ⟨n9, c9, s9, sp9, rk9, a0_9, K9, fr9⟩ := p2v_bbF 
    F E8 s8 p2v_at_f40 p2v_at_f44 (by decide) (by decide) g8_2
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.keepL K9 (by decide)
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide), g8_4]
  have g9_9 : reg n9 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk9 (9 : Fin 32) (by decide), g8_9]
  have g9_24 : reg n9 (24 : Fin 32) = dhi := by rw [rk9 (24 : Fin 32) (by decide), g8_24]
  have g9_2 : reg n9 sp = B + 0x21A0 := sp9
  have g9_10 : reg n9 a0 = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by rw [a0_9, g8_10]
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0x12F4, 0x20)] := keep_kk8.trans K9
  clear keep_kk8
  have w9_10 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K9.w32 (by decide) (by decide)).trans w8_10
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K9.w32 (by decide) (by decide)).trans w8_40
  have b9_220 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K9.b8 (by decide) (by decide)).trans b8_220
  have b9_920 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K9.b8 (by decide) (by decide)).trans b8_920
  have b9_fa0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K9.b8 (by decide) (by decide)).trans b8_fa0
  have b9_1004 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K9.b8 (by decide) (by decide)).trans b8_1004
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K9.acc (by decide) (by decide)).trans a8_180
  have a9_200 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K9.acc (by decide) (by decide)).trans a8_200
  have a9_900 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K9.acc (by decide) (by decide)).trans a8_900
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K9.acc (by decide) (by decide)).trans a8_980
  have a9_f80 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K9.acc (by decide) (by decide)).trans a8_f80
  have a9_fe4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K9.acc (by decide) (by decide)).trans a8_fe4
  have a9_12f4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K9.acc (by decide) (by decide)).trans a8_12f4
  have a9_1338 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K9.acc (by decide) (by decide)).trans a8_1338
  have a9_1358 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K9.acc (by decide) (by decide)).trans a8_1358
  clear a8_1358 a8_1338 a8_12f4 a8_fe4 a8_f80 a8_980 a8_900 a8_200 a8_180 b8_1004 b8_fa0 b8_920 b8_220 w8_40 w8_10 g8_10 g8_24 g8_11 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0xF48
  obtain ⟨n10, c10, u10⟩ := s9.block p2vZEf48 E9.self p2vZEf48_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem P2V n10 0xF5E (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock p2vZEf48 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  have fr10 : ∀ x, P2vR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by
    rw [rb10, runBlock_reg _ _ _ sp s9.zero (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (3 : Fin 32) s9.zero (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (4 : Fin 32) s9.zero (by decide), g9_4]
  have g10_9 : reg n10 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_24 : reg n10 (24 : Fin 32) = dhi := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_8 : reg n10 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vZEf48, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_24, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vZEf48, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_24, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g10_11 : reg n10 a1 = B + 0x21A0 + BitVec.ofNat 32 0x12F4 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vZEf48, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_24, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g10_12 : reg n10 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vZEf48, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_24, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0x12F4, 0x20)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_10 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m10]; exact w9_10
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m10]; exact w9_40
  have b10_220 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m10]; exact b9_220
  have b10_920 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m10]; exact b9_920
  have b10_fa0 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m10]; exact b9_fa0
  have b10_1004 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m10]; exact b9_1004
  have a10_180 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m10]; exact a9_180
  have a10_200 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m10]; exact a9_200
  have a10_900 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m10]; exact a9_900
  have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m10]; exact a9_980
  have a10_f80 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m10]; exact a9_f80
  have a10_fe4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m10]; exact a9_fe4
  have a10_12f4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m10]; exact a9_12f4
  have a10_1338 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m10]; exact a9_1338
  have a10_1358 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m10]; exact a9_1358
  clear a9_1358 a9_1338 a9_12f4 a9_fe4 a9_f80 a9_980 a9_900 a9_200 a9_180 b9_1004 b9_fa0 b9_920 b9_220 w9_40 w9_10 g9_10 g9_2 g9_24 g9_9 g9_4 g9_3 V9 E9 fR9 t9 fr9 K9 a0_9 rk9 sp9 s9 c9
  -- 0xF5E: memcpy
  obtain ⟨n11, P11, K11, X11⟩ := p2v_mc (c := 0xC80) (d := 0x12F4) (N := 0x20) F E10 s10 p2v_at_f5e p2v_at_f62
    (by decide) (by decide) g10_2 g10_10 g10_11 g10_12
    (by decide) (by decide) (by decide)
  have s11 := P11.st
  have fr11 := P11.fr
  have t11 : Steps n0 n11 := t10.trans P11.steps
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [P11.regs sp (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P11.regs (3 : Fin 32) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P11.regs (4 : Fin 32) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by rw [P11.regs (8 : Fin 32) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P11.regs (9 : Fin 32) (by decide), g10_9]
  have g11_24 : reg n11 (24 : Fin 32) = dhi := by rw [P11.regs (24 : Fin 32) (by decide), g10_24]
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0x12F4, 0x20), (0xC80, 0x20)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_10 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K11.w32 (by decide) (by decide)).trans w10_10
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K11.w32 (by decide) (by decide)).trans w10_40
  have b11_220 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K11.b8 (by decide) (by decide)).trans b10_220
  have b11_920 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K11.b8 (by decide) (by decide)).trans b10_920
  have b11_fa0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K11.b8 (by decide) (by decide)).trans b10_fa0
  have b11_1004 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K11.b8 (by decide) (by decide)).trans b10_1004
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K11.acc (by decide) (by decide)).trans a10_180
  have a11_200 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K11.acc (by decide) (by decide)).trans a10_200
  have a11_900 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K11.acc (by decide) (by decide)).trans a10_900
  have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K11.acc (by decide) (by decide)).trans a10_980
  have a11_f80 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K11.acc (by decide) (by decide)).trans a10_f80
  have a11_fe4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K11.acc (by decide) (by decide)).trans a10_fe4
  have a11_12f4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K11.acc (by decide) (by decide)).trans a10_12f4
  have a11_1338 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K11.acc (by decide) (by decide)).trans a10_1338
  have a11_1358 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K11.acc (by decide) (by decide)).trans a10_1358
  have a11_c80 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (accV_S 8 fun q hq => by
    rw [show 0xC80 + q = 0xC80 + (0x0 + q) by omega, X11 (0x0 + q) (by omega),
      show 0x12F4 + (0x0 + q) = 0x12F4 + q by omega]).trans a10_12f4
  clear a10_1358 a10_1338 a10_12f4 a10_fe4 a10_f80 a10_980 a10_900 a10_200 a10_180 b10_1004 b10_fa0 b10_920 b10_220 w10_40 w10_10 g10_12 g10_11 g10_10 g10_8 g10_24 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0xF66: sb
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := p2v_sb F E11 s11 p2v_at_f66 (off' := 0xF6A) (c := 0xCA0)
    (by decide) (by rw [g11_9]; p2v_addr) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, P2vR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : P2vCode n12.mem := E11.fr F fr12
  have V12 : P2vSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by rw [rg12 (8 : Fin 32), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg12 (9 : Fin 32), g11_9]
  have g12_24 : reg n12 (24 : Fin 32) = dhi := by rw [rg12 (24 : Fin 32), g11_24]
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_10 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K12.w32 (by decide) (by decide)).trans w11_10
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K12.w32 (by decide) (by decide)).trans w11_40
  have b12_220 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K12.b8 (by decide) (by decide)).trans b11_220
  have b12_920 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K12.b8 (by decide) (by decide)).trans b11_920
  have b12_fa0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K12.b8 (by decide) (by decide)).trans b11_fa0
  have b12_1004 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K12.b8 (by decide) (by decide)).trans b11_1004
  have b12_ca0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [W12, g11_8]
  have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K12.acc (by decide) (by decide)).trans a11_180
  have a12_200 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K12.acc (by decide) (by decide)).trans a11_200
  have a12_900 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K12.acc (by decide) (by decide)).trans a11_900
  have a12_980 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K12.acc (by decide) (by decide)).trans a11_980
  have a12_c80 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K12.acc (by decide) (by decide)).trans a11_c80
  have a12_f80 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K12.acc (by decide) (by decide)).trans a11_f80
  have a12_fe4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := (K12.acc (by decide) (by decide)).trans a11_fe4
  have a12_12f4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K12.acc (by decide) (by decide)).trans a11_12f4
  have a12_1338 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K12.acc (by decide) (by decide)).trans a11_1338
  have a12_1358 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K12.acc (by decide) (by decide)).trans a11_1358
  clear a11_c80 a11_1358 a11_1338 a11_12f4 a11_fe4 a11_f80 a11_980 a11_900 a11_200 a11_180 b11_1004 b11_fa0 b11_920 b11_220 w11_40 w11_10 g11_24 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 s11 X11 K11 P11
  -- 0xF6A
  obtain ⟨n13, c13, u13⟩ := s12.block p2vZEf6a E12.self p2vZEf6a_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem P2V n13 0xF78 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock p2vZEf6a (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_8 : reg n13 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_24 : reg n13 (24 : Fin 32) = dhi := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vZEf6a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_24, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vZEf6a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_24, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vZEf6a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_24, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_10 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m13]; exact w12_10
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m13]; exact w12_40
  have b13_220 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m13]; exact b12_220
  have b13_920 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m13]; exact b12_920
  have b13_ca0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m13]; exact b12_ca0
  have b13_fa0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m13]; exact b12_fa0
  have b13_1004 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m13]; exact b12_1004
  have a13_180 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m13]; exact a12_180
  have a13_200 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m13]; exact a12_200
  have a13_900 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m13]; exact a12_900
  have a13_980 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m13]; exact a12_980
  have a13_c80 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m13]; exact a12_c80
  have a13_f80 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m13]; exact a12_f80
  have a13_fe4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = ev := by rw [m13]; exact a12_fe4
  have a13_12f4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m13]; exact a12_12f4
  have a13_1338 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m13]; exact a12_1338
  have a13_1358 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m13]; exact a12_1358
  clear a12_1358 a12_1338 a12_12f4 a12_fe4 a12_f80 a12_c80 a12_980 a12_900 a12_200 a12_180 b12_ca0 b12_1004 b12_fa0 b12_920 b12_220 w12_40 w12_10 g12_24 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0xF78: p2v_ms3F
  obtain ⟨n14, c14, s14, rk14, K14, fr14, Z14⟩ := p2v_ms3F (c := 0xFE4) (N := 0x20)
    F E13 s13 p2v_at_f78 p2v_at_f7c (by decide) (by decide)
    g13_10 g13_11 g13_12 (by decide)
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, P2vR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : P2vCode n14.mem := E13.fr F fr14
  have V14 : P2vSaves B n14.mem v := V13.keepL K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rk14 sp (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk14 (3 : Fin 32) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk14 (4 : Fin 32) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by rw [rk14 (8 : Fin 32) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk14 (9 : Fin 32) (by decide), g13_9]
  have g14_24 : reg n14 (24 : Fin 32) = dhi := by rw [rk14 (24 : Fin 32) (by decide), g13_24]
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20)] := keep_kk13.trans K14
  clear keep_kk13
  have w14_10 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K14.w32 (by decide) (by decide)).trans w13_10
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K14.w32 (by decide) (by decide)).trans w13_40
  have b14_220 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K14.b8 (by decide) (by decide)).trans b13_220
  have b14_920 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K14.b8 (by decide) (by decide)).trans b13_920
  have b14_ca0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_ca0
  have b14_fa0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K14.b8 (by decide) (by decide)).trans b13_fa0
  have b14_1004 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K14.b8 (by decide) (by decide)).trans b13_1004
  have a14_180 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K14.acc (by decide) (by decide)).trans a13_180
  have a14_200 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K14.acc (by decide) (by decide)).trans a13_200
  have a14_900 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K14.acc (by decide) (by decide)).trans a13_900
  have a14_980 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K14.acc (by decide) (by decide)).trans a13_980
  have a14_c80 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K14.acc (by decide) (by decide)).trans a13_c80
  have a14_f80 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K14.acc (by decide) (by decide)).trans a13_f80
  have a14_12f4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K14.acc (by decide) (by decide)).trans a13_12f4
  have a14_1338 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K14.acc (by decide) (by decide)).trans a13_1338
  have a14_1358 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K14.acc (by decide) (by decide)).trans a13_1358
  have a14_fe4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := acc0_of_fill fun j hj => by rw [show 0xFE4 + j = 0xFE4 + (0x0 + j) by omega]; exact Z14 _ (by omega)
  clear a13_1358 a13_1338 a13_12f4 a13_fe4 a13_f80 a13_c80 a13_980 a13_900 a13_200 a13_180 b13_1004 b13_fa0 b13_ca0 b13_920 b13_220 w13_40 w13_10 g13_12 g13_11 g13_10 g13_24 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0xF80
  obtain ⟨n15, c15, u15⟩ := s14.block p2vZEf80 E14.self p2vZEf80_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem P2V n15 0xF9C (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock p2vZEf80 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
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
  have g15_8 : reg n15 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb15, runBlock_reg _ _ _ (8 : Fin 32) s14.zero (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
  have g15_24 : reg n15 (24 : Fin 32) = dhi := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vZEf80, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_24, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vZEf80, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_24, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g15_12 : reg n15 a2 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vZEf80, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_24, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g15_13 : reg n15 a3 = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vZEf80, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_24, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_10 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m15]; exact w14_10
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m15]; exact w14_40
  have b15_220 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m15]; exact b14_220
  have b15_920 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m15]; exact b14_920
  have b15_ca0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m15]; exact b14_ca0
  have b15_fa0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m15]; exact b14_fa0
  have b15_1004 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m15]; exact b14_1004
  have a15_180 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m15]; exact a14_180
  have a15_200 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m15]; exact a14_200
  have a15_900 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m15]; exact a14_900
  have a15_980 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m15]; exact a14_980
  have a15_c80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m15]; exact a14_c80
  have a15_f80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m15]; exact a14_f80
  have a15_fe4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := by rw [m15]; exact a14_fe4
  have a15_12f4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m15]; exact a14_12f4
  have a15_1338 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m15]; exact a14_1338
  have a15_1358 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m15]; exact a14_1358
  clear a14_fe4 a14_1358 a14_1338 a14_12f4 a14_f80 a14_c80 a14_980 a14_900 a14_200 a14_180 b14_1004 b14_fa0 b14_ca0 b14_920 b14_220 w14_40 w14_10 g14_24 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 Z14 fr14 K14 rk14 s14 c14
  -- 0xF9C: p2v_cselF
  obtain ⟨n16, c16, s16, sp16, rk16, A16, K16, fr16⟩ := p2v_cselF (co := 0x980) (ca := 0xFE4) (cb := 0xC80)
    F E15 (P2C0.p2v F fR15) s15 p2v_at_f9c p2v_at_fa0 (by decide) (by decide) g15_2
    g15_10 g15_11 g15_12 g15_13 (ch01 hnz) (by decide) (by decide) (by decide) (by decide)
  rw [a15_fe4, a15_c80] at A16
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.keepL K16 (by decide)
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk16 (3 : Fin 32) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk16 (4 : Fin 32) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by rw [rk16 (8 : Fin 32) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk16 (9 : Fin 32) (by decide), g15_9]
  have g16_24 : reg n16 (24 : Fin 32) = dhi := by rw [rk16 (24 : Fin 32) (by decide), g15_24]
  have g16_2 : reg n16 sp = B + 0x21A0 := sp16
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20)] := keep_kk15.trans K16
  clear keep_kk15
  have w16_10 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K16.w32 (by decide) (by decide)).trans w15_10
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K16.w32 (by decide) (by decide)).trans w15_40
  have b16_220 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K16.b8 (by decide) (by decide)).trans b15_220
  have b16_920 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K16.b8 (by decide) (by decide)).trans b15_920
  have b16_ca0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_ca0
  have b16_fa0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K16.b8 (by decide) (by decide)).trans b15_fa0
  have b16_1004 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K16.b8 (by decide) (by decide)).trans b15_1004
  have a16_180 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K16.acc (by decide) (by decide)).trans a15_180
  have a16_200 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K16.acc (by decide) (by decide)).trans a15_200
  have a16_900 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K16.acc (by decide) (by decide)).trans a15_900
  have a16_c80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K16.acc (by decide) (by decide)).trans a15_c80
  have a16_f80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K16.acc (by decide) (by decide)).trans a15_f80
  have a16_fe4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := (K16.acc (by decide) (by decide)).trans a15_fe4
  have a16_12f4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K16.acc (by decide) (by decide)).trans a15_12f4
  have a16_1338 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K16.acc (by decide) (by decide)).trans a15_1338
  have a16_1358 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K16.acc (by decide) (by decide)).trans a15_1358
  have a16_980 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) := A16
  clear a15_1358 a15_1338 a15_12f4 a15_fe4 a15_f80 a15_c80 a15_980 a15_900 a15_200 a15_180 b15_1004 b15_fa0 b15_ca0 b15_920 b15_220 w15_40 w15_10 g15_13 g15_12 g15_11 g15_10 g15_24 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0xFA4: sb
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := p2v_sb F E16 s16 p2v_at_fa4 (off' := 0xFA8) (c := 0x9A0)
    (by decide) (by rw [g16_9]; p2v_addr) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, P2vR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : P2vCode n17.mem := E16.fr F fr17
  have V17 : P2vSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by rw [rg17 (8 : Fin 32), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg17 (9 : Fin 32), g16_9]
  have g17_24 : reg n17 (24 : Fin 32) = dhi := by rw [rg17 (24 : Fin 32), g16_24]
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_10 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K17.w32 (by decide) (by decide)).trans w16_10
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K17.w32 (by decide) (by decide)).trans w16_40
  have b17_220 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K17.b8 (by decide) (by decide)).trans b16_220
  have b17_920 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K17.b8 (by decide) (by decide)).trans b16_920
  have b17_ca0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K17.b8 (by decide) (by decide)).trans b16_ca0
  have b17_fa0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K17.b8 (by decide) (by decide)).trans b16_fa0
  have b17_1004 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := (K17.b8 (by decide) (by decide)).trans b16_1004
  have b17_9a0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [W17, g16_8]
  have a17_180 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K17.acc (by decide) (by decide)).trans a16_180
  have a17_200 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K17.acc (by decide) (by decide)).trans a16_200
  have a17_900 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K17.acc (by decide) (by decide)).trans a16_900
  have a17_980 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) := (K17.acc (by decide) (by decide)).trans a16_980
  have a17_c80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K17.acc (by decide) (by decide)).trans a16_c80
  have a17_f80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K17.acc (by decide) (by decide)).trans a16_f80
  have a17_fe4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := (K17.acc (by decide) (by decide)).trans a16_fe4
  have a17_12f4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K17.acc (by decide) (by decide)).trans a16_12f4
  have a17_1338 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K17.acc (by decide) (by decide)).trans a16_1338
  have a17_1358 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K17.acc (by decide) (by decide)).trans a16_1358
  clear a16_980 a16_1358 a16_1338 a16_12f4 a16_fe4 a16_f80 a16_c80 a16_900 a16_200 a16_180 b16_1004 b16_fa0 b16_ca0 b16_920 b16_220 w16_40 w16_10 g16_2 g16_24 g16_9 g16_8 g16_4 g16_3 V16 E16 fR16 t16 fr16 K16 A16 rk16 sp16 s16 c16
  -- 0xFA8
  obtain ⟨n18, c18, u18⟩ := s17.block p2vZEfa8 E17.self p2vZEfa8_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem P2V n18 0xFB8 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock p2vZEfa8 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
  have fr18 : ∀ x, P2vR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, P2vR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : P2vCode n18.mem := E17.fr F fr18
  have V18 : P2vSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by
    rw [rb18, runBlock_reg _ _ _ sp s17.zero (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (3 : Fin 32) s17.zero (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (4 : Fin 32) s17.zero (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb18, runBlock_reg _ _ _ (9 : Fin 32) s17.zero (by decide), g17_9]
  have g18_24 : reg n18 (24 : Fin 32) = dhi := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, p2vZEfa8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_24, s17.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g18_11 : reg n18 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, p2vZEfa8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_24, s17.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk18 : P2vKeepL B n0.mem n18.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_10 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m18]; exact w17_10
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m18]; exact w17_40
  have b18_220 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m18]; exact b17_220
  have b18_920 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m18]; exact b17_920
  have b18_9a0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m18]; exact b17_9a0
  have b18_ca0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m18]; exact b17_ca0
  have b18_fa0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m18]; exact b17_fa0
  have b18_1004 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = es := by rw [m18]; exact b17_1004
  have a18_180 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m18]; exact a17_180
  have a18_200 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m18]; exact a17_200
  have a18_900 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m18]; exact a17_900
  have a18_980 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) := by rw [m18]; exact a17_980
  have a18_c80 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m18]; exact a17_c80
  have a18_f80 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m18]; exact a17_f80
  have a18_fe4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = 0 := by rw [m18]; exact a17_fe4
  have a18_12f4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m18]; exact a17_12f4
  have a18_1338 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m18]; exact a17_1338
  have a18_1358 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m18]; exact a17_1358
  clear a17_1358 a17_1338 a17_12f4 a17_fe4 a17_f80 a17_c80 a17_980 a17_900 a17_200 a17_180 b17_9a0 b17_1004 b17_fa0 b17_ca0 b17_920 b17_220 w17_40 w17_10 g17_24 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0xFB8: p2v_cmapF
  obtain ⟨n19, c19, s19, sp19, rk19, A19, T19, K19, fr19⟩ := p2v_cmapF (co := 0xFE4) (cx := 0x980)
    F E18 (P2C0.p2v F fR18) (GDC0.p2v F fR18) s18 p2v_at_fb8 p2v_at_fbc (by decide) (by decide) g18_2
    g18_10 g18_11 (by decide) (by decide) (by decide) (by rw [show 0x980 + 0x20 = 0x9A0 from rfl, b18_9a0]; exact (ch01b hnz))
  rw [show 0x980 + 0x20 = 0x9A0 from rfl, b18_9a0, a18_980] at A19
  rw [show 0x980 + 0x20 = 0x9A0 from rfl, b18_9a0,
    show 0xFE4 + 0x20 = 0x1004 from rfl] at T19
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, P2vR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : P2vCode n19.mem := E18.fr F fr19
  have V19 : P2vSaves B n19.mem v := V18.keepL K19 (by decide)
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk19 (3 : Fin 32) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk19 (4 : Fin 32) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by rw [rk19 (8 : Fin 32) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk19 (9 : Fin 32) (by decide), g18_9]
  have g19_24 : reg n19 (24 : Fin 32) = dhi := by rw [rk19 (24 : Fin 32) (by decide), g18_24]
  have g19_2 : reg n19 sp = B + 0x21A0 := sp19
  have keep_kk19 : P2vKeepL B n0.mem n19.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21)] := keep_kk18.trans K19
  clear keep_kk18
  have w19_10 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K19.w32 (by decide) (by decide)).trans w18_10
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K19.w32 (by decide) (by decide)).trans w18_40
  have b19_220 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K19.b8 (by decide) (by decide)).trans b18_220
  have b19_920 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K19.b8 (by decide) (by decide)).trans b18_920
  have b19_9a0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_9a0
  have b19_ca0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_ca0
  have b19_fa0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K19.b8 (by decide) (by decide)).trans b18_fa0
  have a19_180 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K19.acc (by decide) (by decide)).trans a18_180
  have a19_200 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K19.acc (by decide) (by decide)).trans a18_200
  have a19_900 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K19.acc (by decide) (by decide)).trans a18_900
  have a19_980 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) := (K19.acc (by decide) (by decide)).trans a18_980
  have a19_c80 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K19.acc (by decide) (by decide)).trans a18_c80
  have a19_f80 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K19.acc (by decide) (by decide)).trans a18_f80
  have a19_12f4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K19.acc (by decide) (by decide)).trans a18_12f4
  have a19_1338 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K19.acc (by decide) (by decide)).trans a18_1338
  have a19_1358 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K19.acc (by decide) (by decide)).trans a18_1358
  have a19_fe4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := A19
  have b19_1004 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := T19
  clear a18_1358 a18_1338 a18_12f4 a18_fe4 a18_f80 a18_c80 a18_980 a18_900 a18_200 a18_180 b18_1004 b18_fa0 b18_ca0 b18_9a0 b18_920 b18_220 w18_40 w18_10 g18_11 g18_10 g18_24 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0xFC0
  obtain ⟨n20, c20, u20⟩ := s19.block p2vZEfc0 E19.self p2vZEfc0_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem P2V n20 0xFCE (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock p2vZEfc0 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
  have fr20 : ∀ x, P2vR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, P2vR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : P2vCode n20.mem := E19.fr F fr20
  have V20 : P2vSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by
    rw [rb20, runBlock_reg _ _ _ sp s19.zero (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (3 : Fin 32) s19.zero (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (4 : Fin 32) s19.zero (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_24 : reg n20 (24 : Fin 32) = dhi := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vZEfc0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_24, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vZEfc0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_24, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g20_12 : reg n20 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vZEfc0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_24, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk20 : P2vKeepL B n0.mem n20.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_10 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m20]; exact w19_10
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m20]; exact w19_40
  have b20_220 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m20]; exact b19_220
  have b20_920 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m20]; exact b19_920
  have b20_9a0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m20]; exact b19_9a0
  have b20_ca0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m20]; exact b19_ca0
  have b20_fa0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m20]; exact b19_fa0
  have b20_1004 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m20]; exact b19_1004
  have a20_180 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m20]; exact a19_180
  have a20_200 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m20]; exact a19_200
  have a20_900 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m20]; exact a19_900
  have a20_980 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) := by rw [m20]; exact a19_980
  have a20_c80 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m20]; exact a19_c80
  have a20_f80 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m20]; exact a19_f80
  have a20_fe4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m20]; exact a19_fe4
  have a20_12f4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m20]; exact a19_12f4
  have a20_1338 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m20]; exact a19_1338
  have a20_1358 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m20]; exact a19_1358
  clear b19_1004 a19_fe4 a19_1358 a19_1338 a19_12f4 a19_f80 a19_c80 a19_980 a19_900 a19_200 a19_180 b19_fa0 b19_ca0 b19_9a0 b19_920 b19_220 w19_40 w19_10 g19_2 g19_24 g19_9 g19_8 g19_4 g19_3 V19 E19 fR19 t19 fr19 K19 T19 A19 rk19 sp19 s19 c19
  -- 0xFCE: p2v_ms3F
  obtain ⟨n21, c21, s21, rk21, K21, fr21, Z21⟩ := p2v_ms3F (c := 0x980) (N := 0x20)
    F E20 s20 p2v_at_fce p2v_at_fd2 (by decide) (by decide)
    g20_10 g20_11 g20_12 (by decide)
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, P2vR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : P2vCode n21.mem := E20.fr F fr21
  have V21 : P2vSaves B n21.mem v := V20.keepL K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rk21 sp (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk21 (3 : Fin 32) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk21 (4 : Fin 32) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = (((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32 := by rw [rk21 (8 : Fin 32) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk21 (9 : Fin 32) (by decide), g20_9]
  have g21_24 : reg n21 (24 : Fin 32) = dhi := by rw [rk21 (24 : Fin 32) (by decide), g20_24]
  have keep_kk21 : P2vKeepL B n0.mem n21.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20)] := keep_kk20.trans K21
  clear keep_kk20
  have w21_10 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K21.w32 (by decide) (by decide)).trans w20_10
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K21.w32 (by decide) (by decide)).trans w20_40
  have b21_220 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K21.b8 (by decide) (by decide)).trans b20_220
  have b21_920 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K21.b8 (by decide) (by decide)).trans b20_920
  have b21_9a0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_9a0
  have b21_ca0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_ca0
  have b21_fa0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K21.b8 (by decide) (by decide)).trans b20_fa0
  have b21_1004 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_1004
  have a21_180 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K21.acc (by decide) (by decide)).trans a20_180
  have a21_200 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := (K21.acc (by decide) (by decide)).trans a20_200
  have a21_900 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K21.acc (by decide) (by decide)).trans a20_900
  have a21_c80 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K21.acc (by decide) (by decide)).trans a20_c80
  have a21_f80 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K21.acc (by decide) (by decide)).trans a20_f80
  have a21_fe4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K21.acc (by decide) (by decide)).trans a20_fe4
  have a21_12f4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K21.acc (by decide) (by decide)).trans a20_12f4
  have a21_1338 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K21.acc (by decide) (by decide)).trans a20_1338
  have a21_1358 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K21.acc (by decide) (by decide)).trans a20_1358
  have a21_980 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := acc0_of_fill fun j hj => by rw [show 0x980 + j = 0x980 + (0x0 + j) by omega]; exact Z21 _ (by omega)
  clear a20_1358 a20_1338 a20_12f4 a20_fe4 a20_f80 a20_c80 a20_980 a20_900 a20_200 a20_180 b20_1004 b20_fa0 b20_ca0 b20_9a0 b20_920 b20_220 w20_40 w20_10 g20_12 g20_11 g20_10 g20_24 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0xFD6: lbu
  obtain ⟨n22, d22, u22⟩ := s21.lbu E21.self p2v_at_fd6 (off' := 0xFDA) (by decide)
  have s22 : St n22.mem P2V n22 0xFDA (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, P2vR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, P2vR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : P2vCode n22.mem := E21.fr F fr22
  have V22 : P2vSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_9 : reg n22 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
  have g22_24 : reg n22 (24 : Fin 32) = dhi := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
  have g22_8 : reg n22 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_9, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x6E4 = B + 0x21A0 + BitVec.ofNat 32 0x1004 by p2v_addr, b21_1004]
  have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_10 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m22]; exact w21_10
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m22]; exact w21_40
  have b22_220 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m22]; exact b21_220
  have b22_920 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m22]; exact b21_920
  have b22_9a0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m22]; exact b21_9a0
  have b22_ca0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m22]; exact b21_ca0
  have b22_fa0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m22]; exact b21_fa0
  have b22_1004 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m22]; exact b21_1004
  have a22_180 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m22]; exact a21_180
  have a22_200 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m22]; exact a21_200
  have a22_900 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m22]; exact a21_900
  have a22_980 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := by rw [m22]; exact a21_980
  have a22_c80 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m22]; exact a21_c80
  have a22_f80 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m22]; exact a21_f80
  have a22_fe4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m22]; exact a21_fe4
  have a22_12f4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m22]; exact a21_12f4
  have a22_1338 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m22]; exact a21_1338
  have a22_1358 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m22]; exact a21_1358
  clear a21_980 a21_1358 a21_1338 a21_12f4 a21_fe4 a21_f80 a21_c80 a21_900 a21_200 a21_180 b21_1004 b21_fa0 b21_ca0 b21_9a0 b21_920 b21_220 w21_40 w21_10 g21_24 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 Z21 fr21 K21 rk21 s21 c21
  -- 0xFDA
  obtain ⟨n23, c23, u23⟩ := s22.block p2vZEfda E22.self p2vZEfda_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem P2V n23 0xFEE (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock p2vZEfda (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_8 : reg n23 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_24 : reg n23 (24 : Fin 32) = dhi := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vZEfda, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_24, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vZEfda, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_24, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g23_12 : reg n23 a2 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vZEfda, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_24, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g23_13 : reg n23 a3 = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vZEfda, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_24, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_10 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m23]; exact w22_10
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m23]; exact w22_40
  have b23_220 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m23]; exact b22_220
  have b23_920 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m23]; exact b22_920
  have b23_9a0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m23]; exact b22_9a0
  have b23_ca0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m23]; exact b22_ca0
  have b23_fa0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m23]; exact b22_fa0
  have b23_1004 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m23]; exact b22_1004
  have a23_180 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m23]; exact a22_180
  have a23_200 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = dv := by rw [m23]; exact a22_200
  have a23_900 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m23]; exact a22_900
  have a23_980 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := by rw [m23]; exact a22_980
  have a23_c80 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m23]; exact a22_c80
  have a23_f80 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m23]; exact a22_f80
  have a23_fe4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m23]; exact a22_fe4
  have a23_12f4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m23]; exact a22_12f4
  have a23_1338 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m23]; exact a22_1338
  have a23_1358 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m23]; exact a22_1358
  clear a22_1358 a22_1338 a22_12f4 a22_fe4 a22_f80 a22_c80 a22_980 a22_900 a22_200 a22_180 b22_1004 b22_fa0 b22_ca0 b22_9a0 b22_920 b22_220 w22_40 w22_10 g22_8 g22_24 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0xFEE: p2v_cselF
  obtain ⟨n24, c24, s24, sp24, rk24, A24, K24, fr24⟩ := p2v_cselF (co := 0x200) (ca := 0x980) (cb := 0xFE4)
    F E23 (P2C0.p2v F fR23) s23 p2v_at_fee p2v_at_ff2 (by decide) (by decide) g23_2
    g23_10 g23_11 g23_12 g23_13 (zext_01b (ch01b hnz)) (by decide) (by decide) (by decide) (by decide)
  rw [a23_980, a23_fe4] at A24
  have t24 : Steps n0 n24 := t23.trans c24
  have fR24 : ∀ x, P2vR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : P2vCode n24.mem := E23.fr F fr24
  have V24 : P2vSaves B n24.mem v := V23.keepL K24 (by decide)
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk24 (3 : Fin 32) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk24 (4 : Fin 32) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rk24 (8 : Fin 32) (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk24 (9 : Fin 32) (by decide), g23_9]
  have g24_24 : reg n24 (24 : Fin 32) = dhi := by rw [rk24 (24 : Fin 32) (by decide), g23_24]
  have g24_2 : reg n24 sp = B + 0x21A0 := sp24
  have keep_kk24 : P2vKeepL B n0.mem n24.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20)] := keep_kk23.trans K24
  clear keep_kk23
  have w24_10 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K24.w32 (by decide) (by decide)).trans w23_10
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K24.w32 (by decide) (by decide)).trans w23_40
  have b24_220 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K24.b8 (by decide) (by decide)).trans b23_220
  have b24_920 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K24.b8 (by decide) (by decide)).trans b23_920
  have b24_9a0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_9a0
  have b24_ca0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_ca0
  have b24_fa0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K24.b8 (by decide) (by decide)).trans b23_fa0
  have b24_1004 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_1004
  have a24_180 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K24.acc (by decide) (by decide)).trans a23_180
  have a24_900 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K24.acc (by decide) (by decide)).trans a23_900
  have a24_980 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := (K24.acc (by decide) (by decide)).trans a23_980
  have a24_c80 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K24.acc (by decide) (by decide)).trans a23_c80
  have a24_f80 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K24.acc (by decide) (by decide)).trans a23_f80
  have a24_fe4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K24.acc (by decide) (by decide)).trans a23_fe4
  have a24_12f4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K24.acc (by decide) (by decide)).trans a23_12f4
  have a24_1338 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K24.acc (by decide) (by decide)).trans a23_1338
  have a24_1358 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K24.acc (by decide) (by decide)).trans a23_1358
  have a24_200 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := A24
  clear a23_1358 a23_1338 a23_12f4 a23_fe4 a23_f80 a23_c80 a23_980 a23_900 a23_200 a23_180 b23_1004 b23_fa0 b23_ca0 b23_9a0 b23_920 b23_220 w23_40 w23_10 g23_13 g23_12 g23_11 g23_10 g23_24 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0xFF6
  obtain ⟨n25, c25, u25⟩ := s24.block p2vZEff6 E24.self p2vZEff6_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem P2V n25 0x1008 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock p2vZEff6 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_8 : reg n25 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_24 : reg n25 (24 : Fin 32) = dhi := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vZEff6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_24, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1338 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vZEff6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_24, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g25_12 : reg n25 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vZEff6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_24, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk25 : P2vKeepL B n0.mem n25.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_10 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m25]; exact w24_10
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m25]; exact w24_40
  have b25_220 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m25]; exact b24_220
  have b25_920 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m25]; exact b24_920
  have b25_9a0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m25]; exact b24_9a0
  have b25_ca0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m25]; exact b24_ca0
  have b25_fa0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m25]; exact b24_fa0
  have b25_1004 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m25]; exact b24_1004
  have a25_180 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m25]; exact a24_180
  have a25_200 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m25]; exact a24_200
  have a25_900 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m25]; exact a24_900
  have a25_980 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := by rw [m25]; exact a24_980
  have a25_c80 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m25]; exact a24_c80
  have a25_f80 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m25]; exact a24_f80
  have a25_fe4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m25]; exact a24_fe4
  have a25_12f4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m25]; exact a24_12f4
  have a25_1338 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m25]; exact a24_1338
  have a25_1358 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m25]; exact a24_1358
  clear a24_200 a24_1358 a24_1338 a24_12f4 a24_fe4 a24_f80 a24_c80 a24_980 a24_900 a24_180 b24_1004 b24_fa0 b24_ca0 b24_9a0 b24_920 b24_220 w24_40 w24_10 g24_2 g24_24 g24_9 g24_8 g24_4 g24_3 V24 E24 fR24 t24 fr24 K24 A24 rk24 sp24 s24 c24
  -- 0x1008: p2v_fmulF
  obtain ⟨n26, c26, s26, sp26, rk26, A26, K26, fr26⟩ := p2v_fmulF (co := 0xC80) (cx := 0x1338) (cy := 0x200)
    F E25 (P2C0.p2v F fR25) s25 p2v_at_1008 p2v_at_100c (by decide) (by decide) g25_2
    g25_10 g25_11 g25_12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [a25_1338]; exact hX) (by rw [a25_200]; exact (by repeat' (first | exact hzi | exact p256_pos | apply ite_lt)))
  rw [a25_1338, a25_200] at A26
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, P2vR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : P2vCode n26.mem := E25.fr F fr26
  have V26 : P2vSaves B n26.mem v := V25.keepL K26 (by decide)
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk26 (3 : Fin 32) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk26 (4 : Fin 32) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rk26 (8 : Fin 32) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk26 (9 : Fin 32) (by decide), g25_9]
  have g26_24 : reg n26 (24 : Fin 32) = dhi := by rw [rk26 (24 : Fin 32) (by decide), g25_24]
  have g26_2 : reg n26 sp = B + 0x21A0 := sp26
  have keep_kk26 : P2vKeepL B n0.mem n26.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20)] := keep_kk25.trans K26
  clear keep_kk25
  have w26_10 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K26.w32 (by decide) (by decide)).trans w25_10
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K26.w32 (by decide) (by decide)).trans w25_40
  have b26_220 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K26.b8 (by decide) (by decide)).trans b25_220
  have b26_920 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K26.b8 (by decide) (by decide)).trans b25_920
  have b26_9a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_9a0
  have b26_ca0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_ca0
  have b26_fa0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K26.b8 (by decide) (by decide)).trans b25_fa0
  have b26_1004 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_1004
  have a26_180 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K26.acc (by decide) (by decide)).trans a25_180
  have a26_200 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K26.acc (by decide) (by decide)).trans a25_200
  have a26_900 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K26.acc (by decide) (by decide)).trans a25_900
  have a26_980 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := (K26.acc (by decide) (by decide)).trans a25_980
  have a26_f80 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K26.acc (by decide) (by decide)).trans a25_f80
  have a26_fe4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K26.acc (by decide) (by decide)).trans a25_fe4
  have a26_12f4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K26.acc (by decide) (by decide)).trans a25_12f4
  have a26_1338 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K26.acc (by decide) (by decide)).trans a25_1338
  have a26_1358 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K26.acc (by decide) (by decide)).trans a25_1358
  have a26_c80 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := A26
  clear a25_1358 a25_1338 a25_12f4 a25_fe4 a25_f80 a25_c80 a25_980 a25_900 a25_200 a25_180 b25_1004 b25_fa0 b25_ca0 b25_9a0 b25_920 b25_220 w25_40 w25_10 g25_12 g25_11 g25_10 g25_24 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x1010
  obtain ⟨n27, c27, u27⟩ := s26.block p2vZE1010 E26.self p2vZE1010_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem P2V n27 0x1022 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock p2vZE1010 (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
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
  have g27_8 : reg n27 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_24 : reg n27 (24 : Fin 32) = dhi := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_10 : reg n27 a0 = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, p2vZE1010, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_24, s26.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1358 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, p2vZE1010, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_24, s26.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g27_12 : reg n27 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, p2vZE1010, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_24, s26.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk27 : P2vKeepL B n0.mem n27.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_10 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m27]; exact w26_10
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m27]; exact w26_40
  have b27_220 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m27]; exact b26_220
  have b27_920 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m27]; exact b26_920
  have b27_9a0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m27]; exact b26_9a0
  have b27_ca0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m27]; exact b26_ca0
  have b27_fa0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m27]; exact b26_fa0
  have b27_1004 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m27]; exact b26_1004
  have a27_180 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m27]; exact a26_180
  have a27_200 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m27]; exact a26_200
  have a27_900 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m27]; exact a26_900
  have a27_980 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := by rw [m27]; exact a26_980
  have a27_c80 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m27]; exact a26_c80
  have a27_f80 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m27]; exact a26_f80
  have a27_fe4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m27]; exact a26_fe4
  have a27_12f4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m27]; exact a26_12f4
  have a27_1338 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m27]; exact a26_1338
  have a27_1358 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m27]; exact a26_1358
  clear a26_c80 a26_1358 a26_1338 a26_12f4 a26_fe4 a26_f80 a26_980 a26_900 a26_200 a26_180 b26_1004 b26_fa0 b26_ca0 b26_9a0 b26_920 b26_220 w26_40 w26_10 g26_2 g26_24 g26_9 g26_8 g26_4 g26_3 V26 E26 fR26 t26 fr26 K26 A26 rk26 sp26 s26 c26
  -- 0x1022: p2v_fmulF
  obtain ⟨n28, c28, s28, sp28, rk28, A28, K28, fr28⟩ := p2v_fmulF (co := 0xCA0) (cx := 0x1358) (cy := 0x200)
    F E27 (P2C0.p2v F fR27) s27 p2v_at_1022 p2v_at_1026 (by decide) (by decide) g27_2
    g27_10 g27_11 g27_12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [a27_1358]; exact hY) (by rw [a27_200]; exact (by repeat' (first | exact hzi | exact p256_pos | apply ite_lt)))
  rw [a27_1358, a27_200] at A28
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, P2vR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : P2vCode n28.mem := E27.fr F fr28
  have V28 : P2vSaves B n28.mem v := V27.keepL K28 (by decide)
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk28 (3 : Fin 32) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk28 (4 : Fin 32) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rk28 (8 : Fin 32) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk28 (9 : Fin 32) (by decide), g27_9]
  have g28_24 : reg n28 (24 : Fin 32) = dhi := by rw [rk28 (24 : Fin 32) (by decide), g27_24]
  have g28_2 : reg n28 sp = B + 0x21A0 := sp28
  have keep_kk28 : P2vKeepL B n0.mem n28.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20)] := keep_kk27.trans K28
  clear keep_kk27
  have w28_10 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K28.w32 (by decide) (by decide)).trans w27_10
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K28.w32 (by decide) (by decide)).trans w27_40
  have b28_220 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K28.b8 (by decide) (by decide)).trans b27_220
  have b28_920 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K28.b8 (by decide) (by decide)).trans b27_920
  have b28_9a0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_9a0
  have b28_fa0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K28.b8 (by decide) (by decide)).trans b27_fa0
  have b28_1004 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_1004
  have a28_180 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K28.acc (by decide) (by decide)).trans a27_180
  have a28_200 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K28.acc (by decide) (by decide)).trans a27_200
  have a28_900 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K28.acc (by decide) (by decide)).trans a27_900
  have a28_980 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := (K28.acc (by decide) (by decide)).trans a27_980
  have a28_c80 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K28.acc (by decide) (by decide)).trans a27_c80
  have a28_f80 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K28.acc (by decide) (by decide)).trans a27_f80
  have a28_fe4 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K28.acc (by decide) (by decide)).trans a27_fe4
  have a28_12f4 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K28.acc (by decide) (by decide)).trans a27_12f4
  have a28_1338 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K28.acc (by decide) (by decide)).trans a27_1338
  have a28_1358 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K28.acc (by decide) (by decide)).trans a27_1358
  have a28_ca0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := A28
  clear a27_1358 a27_1338 a27_12f4 a27_fe4 a27_f80 a27_c80 a27_980 a27_900 a27_200 a27_180 b27_1004 b27_fa0 b27_ca0 b27_9a0 b27_920 b27_220 w27_40 w27_10 g27_12 g27_11 g27_10 g27_24 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x102A: sb
  obtain ⟨n29, d29, s29, fr29, K29, W29, rg29⟩ := p2v_sb F E28 s28 p2v_at_102a (off' := 0x102E) (c := 0xCC0)
    (by decide) (by rw [g28_9]; p2v_addr) (by decide)
  have t29 : Steps n0 n29 := t28.trans d29
  have fR29 : ∀ x, P2vR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : P2vCode n29.mem := E28.fr F fr29
  have V29 : P2vSaves B n29.mem v := V28.keep K29 (by decide)
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [rg29 sp, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg29 (3 : Fin 32), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg29 (4 : Fin 32), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rg29 (8 : Fin 32), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg29 (9 : Fin 32), g28_9]
  have g29_24 : reg n29 (24 : Fin 32) = dhi := by rw [rg29 (24 : Fin 32), g28_24]
  have keep_kk29 : P2vKeepL B n0.mem n29.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1)] := keep_kk28.trans K29.toL
  clear keep_kk28
  have w29_10 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K29.w32 (by decide) (by decide)).trans w28_10
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K29.w32 (by decide) (by decide)).trans w28_40
  have b29_220 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K29.b8 (by decide) (by decide)).trans b28_220
  have b29_920 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K29.b8 (by decide) (by decide)).trans b28_920
  have b29_9a0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K29.b8 (by decide) (by decide)).trans b28_9a0
  have b29_fa0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K29.b8 (by decide) (by decide)).trans b28_fa0
  have b29_1004 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K29.b8 (by decide) (by decide)).trans b28_1004
  have b29_cc0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W29, s28.zero]; rfl
  have a29_180 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K29.acc (by decide) (by decide)).trans a28_180
  have a29_200 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K29.acc (by decide) (by decide)).trans a28_200
  have a29_900 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K29.acc (by decide) (by decide)).trans a28_900
  have a29_980 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := (K29.acc (by decide) (by decide)).trans a28_980
  have a29_c80 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K29.acc (by decide) (by decide)).trans a28_c80
  have a29_ca0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K29.acc (by decide) (by decide)).trans a28_ca0
  have a29_f80 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K29.acc (by decide) (by decide)).trans a28_f80
  have a29_fe4 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K29.acc (by decide) (by decide)).trans a28_fe4
  have a29_12f4 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K29.acc (by decide) (by decide)).trans a28_12f4
  have a29_1338 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K29.acc (by decide) (by decide)).trans a28_1338
  have a29_1358 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K29.acc (by decide) (by decide)).trans a28_1358
  clear a28_ca0 a28_1358 a28_1338 a28_12f4 a28_fe4 a28_f80 a28_c80 a28_980 a28_900 a28_200 a28_180 b28_1004 b28_fa0 b28_9a0 b28_920 b28_220 w28_40 w28_10 g28_2 g28_24 g28_9 g28_8 g28_4 g28_3 V28 E28 fR28 t28 fr28 K28 A28 rk28 sp28 s28 c28
  -- 0x102E: sb
  obtain ⟨n30, d30, s30, fr30, K30, W30, rg30⟩ := p2v_sb F E29 s29 p2v_at_102e (off' := 0x1032) (c := 0xCC4)
    (by decide) (by rw [g29_9]; p2v_addr) (by decide)
  have t30 : Steps n0 n30 := t29.trans d30
  have fR30 : ∀ x, P2vR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : P2vCode n30.mem := E29.fr F fr30
  have V30 : P2vSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rg30 sp, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg30 (3 : Fin 32), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg30 (4 : Fin 32), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rg30 (8 : Fin 32), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg30 (9 : Fin 32), g29_9]
  have g30_24 : reg n30 (24 : Fin 32) = dhi := by rw [rg30 (24 : Fin 32), g29_24]
  have keep_kk30 : P2vKeepL B n0.mem n30.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have w30_10 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K30.w32 (by decide) (by decide)).trans w29_10
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K30.w32 (by decide) (by decide)).trans w29_40
  have b30_220 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K30.b8 (by decide) (by decide)).trans b29_220
  have b30_920 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K30.b8 (by decide) (by decide)).trans b29_920
  have b30_9a0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_9a0
  have b30_cc0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_cc0
  have b30_fa0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K30.b8 (by decide) (by decide)).trans b29_fa0
  have b30_1004 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_1004
  have b30_cc4 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [W30, g29_8, lbu_low]
  have a30_180 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K30.acc (by decide) (by decide)).trans a29_180
  have a30_200 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K30.acc (by decide) (by decide)).trans a29_200
  have a30_900 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K30.acc (by decide) (by decide)).trans a29_900
  have a30_980 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := (K30.acc (by decide) (by decide)).trans a29_980
  have a30_c80 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K30.acc (by decide) (by decide)).trans a29_c80
  have a30_ca0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K30.acc (by decide) (by decide)).trans a29_ca0
  have a30_f80 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K30.acc (by decide) (by decide)).trans a29_f80
  have a30_fe4 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K30.acc (by decide) (by decide)).trans a29_fe4
  have a30_12f4 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K30.acc (by decide) (by decide)).trans a29_12f4
  have a30_1338 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K30.acc (by decide) (by decide)).trans a29_1338
  have a30_1358 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K30.acc (by decide) (by decide)).trans a29_1358
  clear a29_1358 a29_1338 a29_12f4 a29_fe4 a29_f80 a29_ca0 a29_c80 a29_980 a29_900 a29_200 a29_180 b29_cc0 b29_1004 b29_fa0 b29_9a0 b29_920 b29_220 w29_40 w29_10 g29_24 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 rg29 W29 K29 fr29 s29 d29
  -- 0x1032
  obtain ⟨n31, c31, u31⟩ := s30.block p2vZE1032 E30.self p2vZE1032_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem P2V n31 0x104A (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock p2vZE1032 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
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
  have g31_8 : reg n31 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb31, runBlock_reg _ _ _ (8 : Fin 32) s30.zero (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
  have g31_24 : reg n31 (24 : Fin 32) = dhi := by
    rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
  have g31_10 : reg n31 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, p2vZE1032, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_24, s30.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g31_11 : reg n31 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, p2vZE1032, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_24, s30.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g31_12 : reg n31 a2 = BitVec.ofNat 32 (img% p256AffineIdXAddress) := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, p2vZE1032, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_24, s30.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk31 : P2vKeepL B n0.mem n31.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_10 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m31]; exact w30_10
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m31]; exact w30_40
  have b31_220 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m31]; exact b30_220
  have b31_920 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m31]; exact b30_920
  have b31_9a0 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m31]; exact b30_9a0
  have b31_cc0 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m31]; exact b30_cc0
  have b31_cc4 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m31]; exact b30_cc4
  have b31_fa0 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m31]; exact b30_fa0
  have b31_1004 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m31]; exact b30_1004
  have a31_180 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m31]; exact a30_180
  have a31_200 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m31]; exact a30_200
  have a31_900 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m31]; exact a30_900
  have a31_980 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = 0 := by rw [m31]; exact a30_980
  have a31_c80 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m31]; exact a30_c80
  have a31_ca0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m31]; exact a30_ca0
  have a31_f80 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m31]; exact a30_f80
  have a31_fe4 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m31]; exact a30_fe4
  have a31_12f4 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m31]; exact a30_12f4
  have a31_1338 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m31]; exact a30_1338
  have a31_1358 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m31]; exact a30_1358
  clear a30_1358 a30_1338 a30_12f4 a30_fe4 a30_f80 a30_ca0 a30_c80 a30_980 a30_900 a30_200 a30_180 b30_cc4 b30_1004 b30_fa0 b30_cc0 b30_9a0 b30_920 b30_220 w30_40 w30_10 g30_24 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 rg30 W30 K30 fr30 s30 d30
  -- 0x104A: p2v_uorF
  obtain ⟨n32, c32, s32, sp32, rk32, A32, K32, fr32⟩ := p2v_uorF (co := 0x980) (cs := 0xC80)
    F E31 (P2C0.p2v F fR31) s31 p2v_at_104a p2v_at_104e (by decide) (by decide) g31_2
    g31_10 g31_11 g31_12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [show 0xC80 + 0x44 = 0xCC4 from rfl, b31_cc4]; exact (ch01b hnz))
  rw [show 0xC80 + 0x44 = 0xCC4 from rfl, b31_cc4, a31_c80,
    accV_dataR F fR31 (by decide) (by decide)] at A32
  have t32 : Steps n0 n32 := t31.trans c32
  have fR32 : ∀ x, P2vR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : P2vCode n32.mem := E31.fr F fr32
  have V32 : P2vSaves B n32.mem v := V31.keepL K32 (by decide)
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk32 (3 : Fin 32) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk32 (4 : Fin 32) (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rk32 (8 : Fin 32) (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk32 (9 : Fin 32) (by decide), g31_9]
  have g32_24 : reg n32 (24 : Fin 32) = dhi := by rw [rk32 (24 : Fin 32) (by decide), g31_24]
  have g32_2 : reg n32 sp = B + 0x21A0 := sp32
  have keep_kk32 : P2vKeepL B n0.mem n32.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41)] := keep_kk31.trans K32
  clear keep_kk31
  have w32_10 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K32.w32 (by decide) (by decide)).trans w31_10
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K32.w32 (by decide) (by decide)).trans w31_40
  have b32_220 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K32.b8 (by decide) (by decide)).trans b31_220
  have b32_920 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K32.b8 (by decide) (by decide)).trans b31_920
  have b32_cc0 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K32.b8 (by decide) (by decide)).trans b31_cc0
  have b32_cc4 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K32.b8 (by decide) (by decide)).trans b31_cc4
  have b32_fa0 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K32.b8 (by decide) (by decide)).trans b31_fa0
  have b32_1004 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K32.b8 (by decide) (by decide)).trans b31_1004
  have a32_180 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K32.acc (by decide) (by decide)).trans a31_180
  have a32_200 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K32.acc (by decide) (by decide)).trans a31_200
  have a32_900 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K32.acc (by decide) (by decide)).trans a31_900
  have a32_c80 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K32.acc (by decide) (by decide)).trans a31_c80
  have a32_ca0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K32.acc (by decide) (by decide)).trans a31_ca0
  have a32_f80 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K32.acc (by decide) (by decide)).trans a31_f80
  have a32_fe4 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K32.acc (by decide) (by decide)).trans a31_fe4
  have a32_12f4 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K32.acc (by decide) (by decide)).trans a31_12f4
  have a32_1338 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K32.acc (by decide) (by decide)).trans a31_1338
  have a32_1358 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K32.acc (by decide) (by decide)).trans a31_1358
  have a32_980 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := A32
  clear a31_1358 a31_1338 a31_12f4 a31_fe4 a31_f80 a31_ca0 a31_c80 a31_980 a31_900 a31_200 a31_180 b31_1004 b31_fa0 b31_cc4 b31_cc0 b31_9a0 b31_920 b31_220 w31_40 w31_10 g31_12 g31_11 g31_10 g31_24 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
  -- 0x1052
  obtain ⟨n33, c33, u33⟩ := s32.block p2vZE1052 E32.self p2vZE1052_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem P2V n33 0x105A (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock p2vZE1052 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
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
  have g33_8 : reg n33 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb33, runBlock_reg _ _ _ (8 : Fin 32) s32.zero (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_24 : reg n33 (24 : Fin 32) = dhi := by
    rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
  have g33_10 : reg n33 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1398 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, p2vZE1052, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_24, s32.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk33 : P2vKeepL B n0.mem n33.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_10 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m33]; exact w32_10
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m33]; exact w32_40
  have b33_220 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m33]; exact b32_220
  have b33_920 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m33]; exact b32_920
  have b33_cc0 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m33]; exact b32_cc0
  have b33_cc4 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m33]; exact b32_cc4
  have b33_fa0 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m33]; exact b32_fa0
  have b33_1004 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m33]; exact b32_1004
  have a33_180 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m33]; exact a32_180
  have a33_200 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m33]; exact a32_200
  have a33_900 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m33]; exact a32_900
  have a33_980 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := by rw [m33]; exact a32_980
  have a33_c80 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m33]; exact a32_c80
  have a33_ca0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m33]; exact a32_ca0
  have a33_f80 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m33]; exact a32_f80
  have a33_fe4 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m33]; exact a32_fe4
  have a33_12f4 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m33]; exact a32_12f4
  have a33_1338 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m33]; exact a32_1338
  have a33_1358 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m33]; exact a32_1358
  clear a32_980 a32_1358 a32_1338 a32_12f4 a32_fe4 a32_f80 a32_ca0 a32_c80 a32_900 a32_200 a32_180 b32_1004 b32_fa0 b32_cc4 b32_cc0 b32_920 b32_220 w32_40 w32_10 g32_2 g32_24 g32_9 g32_8 g32_4 g32_3 V32 E32 fR32 t32 fr32 K32 A32 rk32 sp32 s32 c32
  -- 0x105A: p2v_z32F
  obtain ⟨n34, c34, s34, sp34, rk34, Z34, K34, fr34⟩ := p2v_z32F (co := 0x1398)
    F E33 (P2C0.p2v F fR33) s33 p2v_at_105a p2v_at_105e (by decide) (by decide) g33_2
    g33_10 (by decide)
  have t34 : Steps n0 n34 := t33.trans c34
  have fR34 : ∀ x, P2vR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : P2vCode n34.mem := E33.fr F fr34
  have V34 : P2vSaves B n34.mem v := V33.keepL K34 (by decide)
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk34 (3 : Fin 32) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk34 (4 : Fin 32) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rk34 (8 : Fin 32) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk34 (9 : Fin 32) (by decide), g33_9]
  have g34_24 : reg n34 (24 : Fin 32) = dhi := by rw [rk34 (24 : Fin 32) (by decide), g33_24]
  have g34_2 : reg n34 sp = B + 0x21A0 := sp34
  have keep_kk34 : P2vKeepL B n0.mem n34.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20)] := keep_kk33.trans K34
  clear keep_kk33
  have w34_10 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K34.w32 (by decide) (by decide)).trans w33_10
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K34.w32 (by decide) (by decide)).trans w33_40
  have b34_220 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K34.b8 (by decide) (by decide)).trans b33_220
  have b34_920 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K34.b8 (by decide) (by decide)).trans b33_920
  have b34_cc0 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K34.b8 (by decide) (by decide)).trans b33_cc0
  have b34_cc4 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K34.b8 (by decide) (by decide)).trans b33_cc4
  have b34_fa0 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K34.b8 (by decide) (by decide)).trans b33_fa0
  have b34_1004 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K34.b8 (by decide) (by decide)).trans b33_1004
  have a34_180 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K34.acc (by decide) (by decide)).trans a33_180
  have a34_200 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K34.acc (by decide) (by decide)).trans a33_200
  have a34_900 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K34.acc (by decide) (by decide)).trans a33_900
  have a34_980 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := (K34.acc (by decide) (by decide)).trans a33_980
  have a34_c80 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K34.acc (by decide) (by decide)).trans a33_c80
  have a34_ca0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K34.acc (by decide) (by decide)).trans a33_ca0
  have a34_f80 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K34.acc (by decide) (by decide)).trans a33_f80
  have a34_fe4 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K34.acc (by decide) (by decide)).trans a33_fe4
  have a34_12f4 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K34.acc (by decide) (by decide)).trans a33_12f4
  have a34_1338 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K34.acc (by decide) (by decide)).trans a33_1338
  have a34_1358 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K34.acc (by decide) (by decide)).trans a33_1358
  have a34_1398 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 8 = 0 := acc0_of_fill Z34
  clear a33_1358 a33_1338 a33_12f4 a33_fe4 a33_f80 a33_ca0 a33_c80 a33_980 a33_900 a33_200 a33_180 b33_1004 b33_fa0 b33_cc4 b33_cc0 b33_920 b33_220 w33_40 w33_10 g33_10 g33_24 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x1062
  obtain ⟨n35, c35, u35⟩ := s34.block p2vZE1062 E34.self p2vZE1062_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have s35 : St n35.mem P2V n35 0x1072 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have rb35 : ∀ q, reg n35 q = (runBlock p2vZE1062 (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
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
  have g35_8 : reg n35 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb35, runBlock_reg _ _ _ (8 : Fin 32) s34.zero (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb35, runBlock_reg _ _ _ (9 : Fin 32) s34.zero (by decide), g34_9]
  have g35_24 : reg n35 (24 : Fin 32) = dhi := by
    rw [rb35, runBlock_reg _ _ _ (24 : Fin 32) s34.zero (by decide), g34_24]
  have g35_10 : reg n35 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, p2vZE1062, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_24, s34.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g35_11 : reg n35 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, p2vZE1062, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_24, s34.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk35 : P2vKeepL B n0.mem n35.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_10 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m35]; exact w34_10
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m35]; exact w34_40
  have b35_220 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m35]; exact b34_220
  have b35_920 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m35]; exact b34_920
  have b35_cc0 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m35]; exact b34_cc0
  have b35_cc4 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m35]; exact b34_cc4
  have b35_fa0 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m35]; exact b34_fa0
  have b35_1004 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m35]; exact b34_1004
  have a35_180 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m35]; exact a34_180
  have a35_200 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m35]; exact a34_200
  have a35_900 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m35]; exact a34_900
  have a35_980 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := by rw [m35]; exact a34_980
  have a35_c80 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m35]; exact a34_c80
  have a35_ca0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m35]; exact a34_ca0
  have a35_f80 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m35]; exact a34_f80
  have a35_fe4 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m35]; exact a34_fe4
  have a35_12f4 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m35]; exact a34_12f4
  have a35_1338 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m35]; exact a34_1338
  have a35_1358 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m35]; exact a34_1358
  have a35_1398 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 8 = 0 := by rw [m35]; exact a34_1398
  clear a34_1398 a34_1358 a34_1338 a34_12f4 a34_fe4 a34_f80 a34_ca0 a34_c80 a34_980 a34_900 a34_200 a34_180 b34_1004 b34_fa0 b34_cc4 b34_cc0 b34_920 b34_220 w34_40 w34_10 g34_2 g34_24 g34_9 g34_8 g34_4 g34_3 V34 E34 fR34 t34 fr34 K34 Z34 rk34 sp34 s34 c34
  -- 0x1072: p2v_fretF
  obtain ⟨n36, c36, s36, sp36, rk36, A36, K36, fr36⟩ := p2v_fretF (co := 0xC80) (cx := 0x980)
    F E35 (P2C0.p2v F fR35) (GDC0.p2v F fR35) (P2D0.p2v F fR35) s35 p2v_at_1072 p2v_at_1076 (by decide) (by decide) g35_2
    g35_10 g35_11 (by decide) (by decide) (by decide) (by decide) (by rw [a35_980]; exact (ite_lt (p2fm_lt _ _) hid))
  rw [a35_980] at A36
  have t36 : Steps n0 n36 := t35.trans c36
  have fR36 : ∀ x, P2vR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : P2vCode n36.mem := E35.fr F fr36
  have V36 : P2vSaves B n36.mem v := V35.keepL K36 (by decide)
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk36 (3 : Fin 32) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk36 (4 : Fin 32) (by decide), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rk36 (8 : Fin 32) (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk36 (9 : Fin 32) (by decide), g35_9]
  have g36_24 : reg n36 (24 : Fin 32) = dhi := by rw [rk36 (24 : Fin 32) (by decide), g35_24]
  have g36_2 : reg n36 sp = B + 0x21A0 := sp36
  have keep_kk36 : P2vKeepL B n0.mem n36.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20)] := keep_kk35.trans K36
  clear keep_kk35
  have w36_10 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K36.w32 (by decide) (by decide)).trans w35_10
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K36.w32 (by decide) (by decide)).trans w35_40
  have b36_220 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K36.b8 (by decide) (by decide)).trans b35_220
  have b36_920 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K36.b8 (by decide) (by decide)).trans b35_920
  have b36_cc0 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K36.b8 (by decide) (by decide)).trans b35_cc0
  have b36_cc4 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K36.b8 (by decide) (by decide)).trans b35_cc4
  have b36_fa0 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K36.b8 (by decide) (by decide)).trans b35_fa0
  have b36_1004 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K36.b8 (by decide) (by decide)).trans b35_1004
  have a36_180 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K36.acc (by decide) (by decide)).trans a35_180
  have a36_200 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K36.acc (by decide) (by decide)).trans a35_200
  have a36_900 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K36.acc (by decide) (by decide)).trans a35_900
  have a36_980 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := (K36.acc (by decide) (by decide)).trans a35_980
  have a36_ca0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K36.acc (by decide) (by decide)).trans a35_ca0
  have a36_f80 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K36.acc (by decide) (by decide)).trans a35_f80
  have a36_fe4 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K36.acc (by decide) (by decide)).trans a35_fe4
  have a36_12f4 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K36.acc (by decide) (by decide)).trans a35_12f4
  have a36_1338 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K36.acc (by decide) (by decide)).trans a35_1338
  have a36_1358 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K36.acc (by decide) (by decide)).trans a35_1358
  have a36_1398 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 8 = 0 := (K36.acc (by decide) (by decide)).trans a35_1398
  have a36_c80 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := A36
  clear a35_1398 a35_1358 a35_1338 a35_12f4 a35_fe4 a35_f80 a35_ca0 a35_c80 a35_980 a35_900 a35_200 a35_180 b35_1004 b35_fa0 b35_cc4 b35_cc0 b35_920 b35_220 w35_40 w35_10 g35_11 g35_10 g35_24 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 rb35 s35 m35 u35 c35
  -- 0x107A
  obtain ⟨n37, c37, u37⟩ := s36.block p2vZE107a E36.self p2vZE107a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have s37 : St n37.mem P2V n37 0x108A (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have rb37 : ∀ q, reg n37 q = (runBlock p2vZE107a (n36.mem, reg n36)).2 q := fun q => by rw [u37.regs]
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
  have g37_8 : reg n37 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb37, runBlock_reg _ _ _ (8 : Fin 32) s36.zero (by decide), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb37, runBlock_reg _ _ _ (9 : Fin 32) s36.zero (by decide), g36_9]
  have g37_24 : reg n37 (24 : Fin 32) = dhi := by
    rw [rb37, runBlock_reg _ _ _ (24 : Fin 32) s36.zero (by decide), g36_24]
  have g37_10 : reg n37 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1398 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, p2vZE107a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_24, s36.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g37_11 : reg n37 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, p2vZE107a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_24, s36.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk37 : P2vKeepL B n0.mem n37.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_10 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m37]; exact w36_10
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m37]; exact w36_40
  have b37_220 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m37]; exact b36_220
  have b37_920 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m37]; exact b36_920
  have b37_cc0 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m37]; exact b36_cc0
  have b37_cc4 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m37]; exact b36_cc4
  have b37_fa0 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m37]; exact b36_fa0
  have b37_1004 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m37]; exact b36_1004
  have a37_180 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m37]; exact a36_180
  have a37_200 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m37]; exact a36_200
  have a37_900 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m37]; exact a36_900
  have a37_980 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := by rw [m37]; exact a36_980
  have a37_c80 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := by rw [m37]; exact a36_c80
  have a37_ca0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m37]; exact a36_ca0
  have a37_f80 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m37]; exact a36_f80
  have a37_fe4 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m37]; exact a36_fe4
  have a37_12f4 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m37]; exact a36_12f4
  have a37_1338 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m37]; exact a36_1338
  have a37_1358 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m37]; exact a36_1358
  have a37_1398 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 8 = 0 := by rw [m37]; exact a36_1398
  clear a36_c80 a36_1398 a36_1358 a36_1338 a36_12f4 a36_fe4 a36_f80 a36_ca0 a36_980 a36_900 a36_200 a36_180 b36_1004 b36_fa0 b36_cc4 b36_cc0 b36_920 b36_220 w36_40 w36_10 g36_2 g36_24 g36_9 g36_8 g36_4 g36_3 V36 E36 fR36 t36 fr36 K36 A36 rk36 sp36 s36 c36
  -- 0x108A: to_be_byte_array
  obtain ⟨n38, P38, K38, L38⟩ := p2v_tbb8 (co := 0x1398) (cx := 0xC80) F E37 (WN0.p2v F fR37) s37
    p2v_at_108a p2v_at_108e (by decide) (by decide) g37_2 g37_10 g37_11
    (by decide) (by decide) (by decide)
  rw [a37_c80] at L38
  have s38 := P38.st
  have fr38 := P38.fr
  have t38 : Steps n0 n38 := t37.trans P38.steps
  have fR38 : ∀ x, P2vR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : P2vCode n38.mem := E37.fr F fr38
  have V38 : P2vSaves B n38.mem v := V37.keep K38 (by decide)
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [P38.regs sp (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P38.regs (3 : Fin 32) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P38.regs (4 : Fin 32) (by decide), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [P38.regs (8 : Fin 32) (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P38.regs (9 : Fin 32) (by decide), g37_9]
  have g38_24 : reg n38 (24 : Fin 32) = dhi := by rw [P38.regs (24 : Fin 32) (by decide), g37_24]
  have keep_kk38 : P2vKeepL B n0.mem n38.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20), (0x1398, 0x20)] := keep_kk37.trans K38.toL
  clear keep_kk37
  have w38_10 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K38.w32 (by decide) (by decide)).trans w37_10
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K38.w32 (by decide) (by decide)).trans w37_40
  have b38_220 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K38.b8 (by decide) (by decide)).trans b37_220
  have b38_920 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K38.b8 (by decide) (by decide)).trans b37_920
  have b38_cc0 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K38.b8 (by decide) (by decide)).trans b37_cc0
  have b38_cc4 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K38.b8 (by decide) (by decide)).trans b37_cc4
  have b38_fa0 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K38.b8 (by decide) (by decide)).trans b37_fa0
  have b38_1004 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K38.b8 (by decide) (by decide)).trans b37_1004
  have a38_180 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K38.acc (by decide) (by decide)).trans a37_180
  have a38_200 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K38.acc (by decide) (by decide)).trans a37_200
  have a38_900 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K38.acc (by decide) (by decide)).trans a37_900
  have a38_980 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := (K38.acc (by decide) (by decide)).trans a37_980
  have a38_c80 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := (K38.acc (by decide) (by decide)).trans a37_c80
  have a38_ca0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K38.acc (by decide) (by decide)).trans a37_ca0
  have a38_f80 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K38.acc (by decide) (by decide)).trans a37_f80
  have a38_fe4 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K38.acc (by decide) (by decide)).trans a37_fe4
  have a38_12f4 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K38.acc (by decide) (by decide)).trans a37_12f4
  have a38_1338 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K38.acc (by decide) (by decide)).trans a37_1338
  have a38_1358 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K38.acc (by decide) (by decide)).trans a37_1358
  have mb38_1398 : leN (memBytes n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 0x20).reverse = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := L38
  clear a37_1398 a37_1358 a37_1338 a37_12f4 a37_fe4 a37_f80 a37_ca0 a37_c80 a37_980 a37_900 a37_200 a37_180 b37_1004 b37_fa0 b37_cc4 b37_cc0 b37_920 b37_220 w37_40 w37_10 g37_11 g37_10 g37_24 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 rb37 s37 m37 u37 c37
  -- 0x1092
  obtain ⟨n39, c39, u39⟩ := s38.block p2vZE1092 E38.self p2vZE1092_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have s39 : St n39.mem P2V n39 0x10A2 (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have rb39 : ∀ q, reg n39 q = (runBlock p2vZE1092 (n38.mem, reg n38)).2 q := fun q => by rw [u39.regs]
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
  have g39_8 : reg n39 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb39, runBlock_reg _ _ _ (8 : Fin 32) s38.zero (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb39, runBlock_reg _ _ _ (9 : Fin 32) s38.zero (by decide), g38_9]
  have g39_24 : reg n39 (24 : Fin 32) = dhi := by
    rw [rb39, runBlock_reg _ _ _ (24 : Fin 32) s38.zero (by decide), g38_24]
  have g39_10 : reg n39 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb39]; simp +decide only [runBlock, BInstr.run, p2vZE1092, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g38_2, g38_3, g38_4, g38_8, g38_9, g38_24, s38.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g39_11 : reg n39 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1398 := by
    rw [rb39]; simp +decide only [runBlock, BInstr.run, p2vZE1092, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g38_2, g38_3, g38_4, g38_8, g38_9, g38_24, s38.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk39 : P2vKeepL B n0.mem n39.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20), (0x1398, 0x20)] := by rw [m39]; exact keep_kk38
  clear keep_kk38
  have w39_10 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m39]; exact w38_10
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m39]; exact w38_40
  have b39_220 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m39]; exact b38_220
  have b39_920 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m39]; exact b38_920
  have b39_cc0 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m39]; exact b38_cc0
  have b39_cc4 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m39]; exact b38_cc4
  have b39_fa0 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m39]; exact b38_fa0
  have b39_1004 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m39]; exact b38_1004
  have a39_180 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m39]; exact a38_180
  have a39_200 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m39]; exact a38_200
  have a39_900 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m39]; exact a38_900
  have a39_980 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := by rw [m39]; exact a38_980
  have a39_c80 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := by rw [m39]; exact a38_c80
  have a39_ca0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m39]; exact a38_ca0
  have a39_f80 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m39]; exact a38_f80
  have a39_fe4 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m39]; exact a38_fe4
  have a39_12f4 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m39]; exact a38_12f4
  have a39_1338 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m39]; exact a38_1338
  have a39_1358 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m39]; exact a38_1358
  have mb39_1398 : leN (memBytes n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 0x20).reverse = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := by rw [m39]; exact mb38_1398
  clear mb38_1398 a38_1358 a38_1338 a38_12f4 a38_fe4 a38_f80 a38_ca0 a38_c80 a38_980 a38_900 a38_200 a38_180 b38_1004 b38_fa0 b38_cc4 b38_cc0 b38_920 b38_220 w38_40 w38_10 g38_24 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 s38 L38 K38 P38
  -- 0x10A2: p2v_by2Fs
  obtain ⟨n40, c40, s40, sp40, rk40, A40, K40, fr40⟩ := p2v_by2Fs (co := 0xC80) (cb := 0x1398)
    F E39 (BY0.p2v F fR39) s39 p2v_at_10a2 p2v_at_10a6 (by decide) (by decide) g39_2
    g39_10 g39_11 (by decide) (by decide) (by decide)
  rw [beNat_of_leNr mb39_1398] at A40
  have t40 : Steps n0 n40 := t39.trans c40
  have fR40 : ∀ x, P2vR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : P2vCode n40.mem := E39.fr F fr40
  have V40 : P2vSaves B n40.mem v := V39.keepL K40 (by decide)
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk40 (3 : Fin 32) (by decide), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk40 (4 : Fin 32) (by decide), g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rk40 (8 : Fin 32) (by decide), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk40 (9 : Fin 32) (by decide), g39_9]
  have g40_24 : reg n40 (24 : Fin 32) = dhi := by rw [rk40 (24 : Fin 32) (by decide), g39_24]
  have g40_2 : reg n40 sp = B + 0x21A0 := sp40
  have keep_kk40 : P2vKeepL B n0.mem n40.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20), (0x1398, 0x20), (0xC80, 0x20)] := keep_kk39.trans K40
  clear keep_kk39
  have w40_10 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K40.w32 (by decide) (by decide)).trans w39_10
  have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K40.w32 (by decide) (by decide)).trans w39_40
  have b40_220 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K40.b8 (by decide) (by decide)).trans b39_220
  have b40_920 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K40.b8 (by decide) (by decide)).trans b39_920
  have b40_cc0 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K40.b8 (by decide) (by decide)).trans b39_cc0
  have b40_cc4 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K40.b8 (by decide) (by decide)).trans b39_cc4
  have b40_fa0 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K40.b8 (by decide) (by decide)).trans b39_fa0
  have b40_1004 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K40.b8 (by decide) (by decide)).trans b39_1004
  have a40_180 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K40.acc (by decide) (by decide)).trans a39_180
  have a40_200 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K40.acc (by decide) (by decide)).trans a39_200
  have a40_900 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K40.acc (by decide) (by decide)).trans a39_900
  have a40_980 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := (K40.acc (by decide) (by decide)).trans a39_980
  have a40_ca0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K40.acc (by decide) (by decide)).trans a39_ca0
  have a40_f80 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K40.acc (by decide) (by decide)).trans a39_f80
  have a40_fe4 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K40.acc (by decide) (by decide)).trans a39_fe4
  have a40_12f4 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K40.acc (by decide) (by decide)).trans a39_12f4
  have a40_1338 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K40.acc (by decide) (by decide)).trans a39_1338
  have a40_1358 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K40.acc (by decide) (by decide)).trans a39_1358
  have mb40_1398 : leN (memBytes n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 0x20).reverse = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := by rw [K40.mb (by decide) (by decide)]; exact mb39_1398
  have a40_c80 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n := A40
  clear mb39_1398 a39_1358 a39_1338 a39_12f4 a39_fe4 a39_f80 a39_ca0 a39_c80 a39_980 a39_900 a39_200 a39_180 b39_1004 b39_fa0 b39_cc4 b39_cc0 b39_920 b39_220 w39_40 w39_10 g39_11 g39_10 g39_24 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 rb39 s39 m39 u39 c39
  -- 0x10AA
  obtain ⟨n41, c41, u41⟩ := s40.block p2vZE10aa E40.self p2vZE10aa_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have s41 : St n41.mem P2V n41 0x10B4 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have rb41 : ∀ q, reg n41 q = (runBlock p2vZE10aa (n40.mem, reg n40)).2 q := fun q => by rw [u41.regs]
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
  have g41_8 : reg n41 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb41, runBlock_reg _ _ _ (8 : Fin 32) s40.zero (by decide), g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb41, runBlock_reg _ _ _ (9 : Fin 32) s40.zero (by decide), g40_9]
  have g41_24 : reg n41 (24 : Fin 32) = dhi := by
    rw [rb41, runBlock_reg _ _ _ (24 : Fin 32) s40.zero (by decide), g40_24]
  have g41_10 : reg n41 a0 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by
    rw [rb41]; simp +decide only [runBlock, BInstr.run, p2vZE10aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g40_2, g40_3, g40_4, g40_8, g40_9, g40_24, s40.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g41_11 : reg n41 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb41]; simp +decide only [runBlock, BInstr.run, p2vZE10aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g40_2, g40_3, g40_4, g40_8, g40_9, g40_24, s40.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk41 : P2vKeepL B n0.mem n41.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20), (0x1398, 0x20), (0xC80, 0x20)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have w41_10 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m41]; exact w40_10
  have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m41]; exact w40_40
  have b41_220 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m41]; exact b40_220
  have b41_920 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m41]; exact b40_920
  have b41_cc0 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m41]; exact b40_cc0
  have b41_cc4 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m41]; exact b40_cc4
  have b41_fa0 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m41]; exact b40_fa0
  have b41_1004 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m41]; exact b40_1004
  have a41_180 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m41]; exact a40_180
  have a41_200 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m41]; exact a40_200
  have a41_900 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m41]; exact a40_900
  have a41_980 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := by rw [m41]; exact a40_980
  have a41_c80 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n := by rw [m41]; exact a40_c80
  have a41_ca0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m41]; exact a40_ca0
  have a41_f80 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m41]; exact a40_f80
  have a41_fe4 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m41]; exact a40_fe4
  have a41_12f4 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m41]; exact a40_12f4
  have a41_1338 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m41]; exact a40_1338
  have a41_1358 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m41]; exact a40_1358
  have mb41_1398 : leN (memBytes n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 0x20).reverse = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := by rw [m41]; exact mb40_1398
  clear a40_c80 mb40_1398 a40_1358 a40_1338 a40_12f4 a40_fe4 a40_f80 a40_ca0 a40_980 a40_900 a40_200 a40_180 b40_1004 b40_fa0 b40_cc4 b40_cc0 b40_920 b40_220 w40_40 w40_10 g40_2 g40_24 g40_9 g40_8 g40_4 g40_3 V40 E40 fR40 t40 fr40 K40 A40 rk40 sp40 s40 c40
  -- 0x10B4: p2v_sctF
  obtain ⟨n42, c42, s42, sp42, rk42, a0_42, K42, fr42⟩ := p2v_sctF (ca := 0x180) (cb := 0xC80)
    F E41 (P2C0.p2v F fR41) (codeIn_p2v F fR41 SC0 (by decide) (by decide)) s41 p2v_at_10b4 p2v_at_10b8 (by decide) (by decide) g41_2
    g41_10 g41_11 (by decide) (by decide) (by decide) (by decide)
  simp only [limbs_eq_iff a41_180 a41_c80] at a0_42
  have t42 : Steps n0 n42 := t41.trans c42
  have fR42 : ∀ x, P2vR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : P2vCode n42.mem := E41.fr F fr42
  have V42 : P2vSaves B n42.mem v := V41.keepL K42 (by decide)
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk42 (3 : Fin 32) (by decide), g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk42 (4 : Fin 32) (by decide), g41_4]
  have g42_8 : reg n42 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [rk42 (8 : Fin 32) (by decide), g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk42 (9 : Fin 32) (by decide), g41_9]
  have g42_24 : reg n42 (24 : Fin 32) = dhi := by rw [rk42 (24 : Fin 32) (by decide), g41_24]
  have g42_2 : reg n42 sp = B + 0x21A0 := sp42
  have g42_10 : reg n42 a0 = (if rv = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n then 1 else 0 : Word) := a0_42
  have keep_kk42 : P2vKeepL B n0.mem n42.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20), (0x1398, 0x20), (0xC80, 0x20)] := keep_kk41.trans K42
  clear keep_kk41
  have w42_10 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := (K42.w32 (by decide) (by decide)).trans w41_10
  have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := (K42.w32 (by decide) (by decide)).trans w41_40
  have b42_220 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := (K42.b8 (by decide) (by decide)).trans b41_220
  have b42_920 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := (K42.b8 (by decide) (by decide)).trans b41_920
  have b42_cc0 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K42.b8 (by decide) (by decide)).trans b41_cc0
  have b42_cc4 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K42.b8 (by decide) (by decide)).trans b41_cc4
  have b42_fa0 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := (K42.b8 (by decide) (by decide)).trans b41_fa0
  have b42_1004 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := (K42.b8 (by decide) (by decide)).trans b41_1004
  have a42_180 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K42.acc (by decide) (by decide)).trans a41_180
  have a42_200 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := (K42.acc (by decide) (by decide)).trans a41_200
  have a42_900 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := (K42.acc (by decide) (by decide)).trans a41_900
  have a42_980 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := (K42.acc (by decide) (by decide)).trans a41_980
  have a42_c80 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n := (K42.acc (by decide) (by decide)).trans a41_c80
  have a42_ca0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := (K42.acc (by decide) (by decide)).trans a41_ca0
  have a42_f80 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := (K42.acc (by decide) (by decide)).trans a41_f80
  have a42_fe4 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := (K42.acc (by decide) (by decide)).trans a41_fe4
  have a42_12f4 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := (K42.acc (by decide) (by decide)).trans a41_12f4
  have a42_1338 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K42.acc (by decide) (by decide)).trans a41_1338
  have a42_1358 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K42.acc (by decide) (by decide)).trans a41_1358
  have mb42_1398 : leN (memBytes n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 0x20).reverse = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := by rw [K42.mb (by decide) (by decide)]; exact mb41_1398
  clear mb41_1398 a41_1358 a41_1338 a41_12f4 a41_fe4 a41_f80 a41_ca0 a41_c80 a41_980 a41_900 a41_200 a41_180 b41_1004 b41_fa0 b41_cc4 b41_cc0 b41_920 b41_220 w41_40 w41_10 g41_11 g41_10 g41_24 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 rb41 s41 m41 u41 c41
  by_cases hxr : rv = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n
  rotate_left
  · have g42_10 : reg n42 a0 = BitVec.ofNat 32 0 := by rw [a0_42, ite_eq_right hxr]; rfl
    -- 0x10BC
    obtain ⟨n43, c43, u43⟩ := s42.block p2vZE10bc E42.self p2vZE10bc_end
      ⟨trivial, trivial, trivial⟩
    have m43 : n43.mem = n42.mem := u43.mem
    have s43 : St n43.mem P2V n43 0x10C4 (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
    have rb43 : ∀ q, reg n43 q = (runBlock p2vZE10bc (n42.mem, reg n42)).2 q := fun q => by rw [u43.regs]
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
    have g43_8 : reg n43 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
      rw [rb43, runBlock_reg _ _ _ (8 : Fin 32) s42.zero (by decide), g42_8]
    have g43_9 : reg n43 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
      rw [rb43, runBlock_reg _ _ _ (9 : Fin 32) s42.zero (by decide), g42_9]
    have g43_24 : reg n43 (24 : Fin 32) = dhi := by
      rw [rb43, runBlock_reg _ _ _ (24 : Fin 32) s42.zero (by decide), g42_24]
    have g43_10 : reg n43 a0 = 0 := by
      rw [rb43]; simp +decide only [runBlock, BInstr.run, p2vZE10bc, upd, ↓reduceIte]; rw [g42_10]; decide
    have keep_kk43 : P2vKeepL B n0.mem n43.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20), (0x1398, 0x20), (0xC80, 0x20)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_10 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m43]; exact w42_10
    have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m43]; exact w42_40
    have b43_220 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m43]; exact b42_220
    have b43_920 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m43]; exact b42_920
    have b43_cc0 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m43]; exact b42_cc0
    have b43_cc4 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m43]; exact b42_cc4
    have b43_fa0 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m43]; exact b42_fa0
    have b43_1004 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m43]; exact b42_1004
    have a43_180 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m43]; exact a42_180
    have a43_200 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m43]; exact a42_200
    have a43_900 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m43]; exact a42_900
    have a43_980 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := by rw [m43]; exact a42_980
    have a43_c80 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n := by rw [m43]; exact a42_c80
    have a43_ca0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m43]; exact a42_ca0
    have a43_f80 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m43]; exact a42_f80
    have a43_fe4 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m43]; exact a42_fe4
    have a43_12f4 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m43]; exact a42_12f4
    have a43_1338 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m43]; exact a42_1338
    have a43_1358 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m43]; exact a42_1358
    have mb43_1398 : leN (memBytes n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 0x20).reverse = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := by rw [m43]; exact mb42_1398
    clear mb42_1398 a42_1358 a42_1338 a42_12f4 a42_fe4 a42_f80 a42_ca0 a42_c80 a42_980 a42_900 a42_200 a42_180 b42_1004 b42_fa0 b42_cc4 b42_cc0 b42_920 b42_220 w42_40 w42_10 g42_10 g42_2 g42_24 g42_9 g42_8 g42_4 g42_3 V42 E42 fR42 t42 fr42 K42 a0_42 rk42 sp42 s42 c42
    -- 0x10C4: j
    obtain ⟨n44, d44, u44⟩ := s43.jump E43.self p2v_at_10c4 (off' := 0x144) (by decide)
      (by rw [s43.pc]; decide)
    have s44 : St n44.mem P2V n44 0x144 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have fr44 : ∀ x, P2vR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
    have t44 : Steps n0 n44 := t43.trans (.single d44)
    have fR44 : ∀ x, P2vR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
    have E44 : P2vCode n44.mem := E43.fr F fr44
    have V44 : P2vSaves B n44.mem v := V43.same m44
    have g44_2 : reg n44 sp = B + 0x21A0 := by rw [u44.regs, g43_2]
    have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u44.regs, g43_3]
    have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u44.regs, g43_4]
    have g44_8 : reg n44 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by rw [u44.regs, g43_8]
    have g44_9 : reg n44 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u44.regs, g43_9]
    have g44_10 : reg n44 a0 = 0 := by rw [u44.regs, g43_10]
    have g44_24 : reg n44 (24 : Fin 32) = dhi := by rw [u44.regs, g43_24]
    have keep_kk44 : P2vKeepL B n0.mem n44.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20), (0x1398, 0x20), (0xC80, 0x20)] := by rw [m44]; exact keep_kk43
    clear keep_kk43
    have w44_10 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m44]; exact w43_10
    have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m44]; exact w43_40
    have b44_220 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m44]; exact b43_220
    have b44_920 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m44]; exact b43_920
    have b44_cc0 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m44]; exact b43_cc0
    have b44_cc4 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m44]; exact b43_cc4
    have b44_fa0 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m44]; exact b43_fa0
    have b44_1004 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m44]; exact b43_1004
    have a44_180 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m44]; exact a43_180
    have a44_200 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m44]; exact a43_200
    have a44_900 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m44]; exact a43_900
    have a44_980 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := by rw [m44]; exact a43_980
    have a44_c80 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n := by rw [m44]; exact a43_c80
    have a44_ca0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m44]; exact a43_ca0
    have a44_f80 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m44]; exact a43_f80
    have a44_fe4 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m44]; exact a43_fe4
    have a44_12f4 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m44]; exact a43_12f4
    have a44_1338 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m44]; exact a43_1338
    have a44_1358 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m44]; exact a43_1358
    have mb44_1398 : leN (memBytes n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 0x20).reverse = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := by rw [m44]; exact mb43_1398
    clear mb43_1398 a43_1358 a43_1338 a43_12f4 a43_fe4 a43_f80 a43_ca0 a43_c80 a43_980 a43_900 a43_200 a43_180 b43_1004 b43_fa0 b43_cc4 b43_cc0 b43_920 b43_220 w43_40 w43_10 g43_10 g43_24 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 rb43 s43 m43 u43 c43 g42_10
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hxr h0'), p2v_fail0 F E44 s44 t44 (fun x hx => (fR44 x hx).trans (fM x hx).symm) V44 hret g44_2 g44_3 g44_4 g44_10⟩
  have g42_10 : reg n42 a0 = BitVec.ofNat 32 1 := by rw [a0_42, ite_eq_left hxr]; rfl
  -- 0x10BC
  obtain ⟨n43, c43, u43⟩ := s42.block p2vZE10bc E42.self p2vZE10bc_end
    ⟨trivial, trivial, trivial⟩
  have m43 : n43.mem = n42.mem := u43.mem
  have s43 : St n43.mem P2V n43 0x10C4 (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
  have rb43 : ∀ q, reg n43 q = (runBlock p2vZE10bc (n42.mem, reg n42)).2 q := fun q => by rw [u43.regs]
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
  have g43_8 : reg n43 (8 : Fin 32) = (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb43, runBlock_reg _ _ _ (8 : Fin 32) s42.zero (by decide), g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb43, runBlock_reg _ _ _ (9 : Fin 32) s42.zero (by decide), g42_9]
  have g43_24 : reg n43 (24 : Fin 32) = dhi := by
    rw [rb43, runBlock_reg _ _ _ (24 : Fin 32) s42.zero (by decide), g42_24]
  have g43_10 : reg n43 a0 = 1 := by
    rw [rb43]; simp +decide only [runBlock, BInstr.run, p2vZE10bc, upd, ↓reduceIte]; rw [g42_10]; decide
  have keep_kk43 : P2vKeepL B n0.mem n43.mem [(0x12F4, 0x20), (0xC80, 0x20), (0xCA0, 0x1), (0xFE4, 0x20), (0x980, 0x20), (0x9A0, 0x1), (0xFE4, 0x21), (0x980, 0x20), (0x200, 0x20), (0xC80, 0x20), (0xCA0, 0x20), (0xCC0, 0x1), (0xCC4, 0x1), (0x980, 0x41), (0x1398, 0x20), (0xC80, 0x20), (0x1398, 0x20), (0xC80, 0x20)] := by rw [m43]; exact keep_kk42
  clear keep_kk42
  have w43_10 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw := by rw [m43]; exact w42_10
  have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = dlo := by rw [m43]; exact w42_40
  have b43_220 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = ds := by rw [m43]; exact b42_220
  have b43_920 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = gs := by rw [m43]; exact b42_920
  have b43_cc0 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m43]; exact b42_cc0
  have b43_cc4 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC4) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m43]; exact b42_cc4
  have b43_fa0 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = fs := by rw [m43]; exact b42_fa0
  have b43_1004 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 := by rw [m43]; exact b42_1004
  have a43_180 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m43]; exact a42_180
  have a43_200 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = (if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0) := by rw [m43]; exact a42_200
  have a43_900 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = gv := by rw [m43]; exact a42_900
  have a43_980 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) := by rw [m43]; exact a42_980
  have a43_c80 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = (p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n := by rw [m43]; exact a42_c80
  have a43_ca0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = p2fm (Y) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) := by rw [m43]; exact a42_ca0
  have a43_f80 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = fv := by rw [m43]; exact a42_f80
  have a43_fe4 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) := by rw [m43]; exact a42_fe4
  have a43_12f4 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x12F4) 8 = normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) := by rw [m43]; exact a42_12f4
  have a43_1338 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m43]; exact a42_1338
  have a43_1358 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m43]; exact a42_1358
  have mb43_1398 : leN (memBytes n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1398) 0x20).reverse = p2fm ((if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((if fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (nzw)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 (ds).toNat ((fs).zeroExtend 32).toNat (dv) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 := by rw [m43]; exact mb42_1398
  clear mb42_1398 a42_1358 a42_1338 a42_12f4 a42_fe4 a42_f80 a42_ca0 a42_c80 a42_980 a42_900 a42_200 a42_180 b42_1004 b42_fa0 b42_cc4 b42_cc0 b42_920 b42_220 w42_40 w42_10 g42_10 g42_2 g42_24 g42_9 g42_8 g42_4 g42_3 V42 E42 fR42 t42 fr42 K42 a0_42 rk42 sp42 s42 c42
  exact .inr ⟨hxr, n43, t43, s43, E43, V43, fR43, g43_2, g43_3, g43_4, g43_10, a43_180, a43_200, a43_900, a43_980, a43_c80, a43_ca0, a43_f80, a43_fe4, a43_12f4, a43_1338, a43_1358, mb43_1398, keep_kk43.mono (by decide)⟩

end C3.RV32.P2v
