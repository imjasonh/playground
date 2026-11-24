import C3BootProofs.Proofs.P2vMs0

/-!
# `p256VerifyPrehash`: the start of the inversion of `Z`

From 0xB00 to the inversion's head at 0xBEE: the sum moves to 0x1338, the word at 0x10 records whether its `Z` is nonzero, and the inversion of `Z` starts from `f = p`, `g = Z`, `d = 0`, `e = R²`, and `δ = 1`, with 591 steps left.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vZSb00 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x338, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .aluImm .add a2 x0 0x60]
theorem p2vZSb00_end : blockEnd p256VerifyPrehashCode 0xB00 p2vZSb00 = some 0xB14 := by
  simp only [p2vZSb00]
  rw [blockEnd, p2v_at_b00]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b02]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b06]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b08]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b0c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b10]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSb1c : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x378, .alu .add (18 : Fin 32) sp a0, .lui (9 : Fin 32) 0x3FCC5000, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFBA0, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (9 : Fin 32)]
theorem p2vZSb1c_end : blockEnd p256VerifyPrehashCode 0xB1C p2vZSb1c = some 0xB3C := by
  simp only [p2vZSb1c]
  rw [blockEnd, p2v_at_b1c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b1e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b22]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b26]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b2a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b2e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b32]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b36]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b3a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSb44 : List BInstr :=
  [.aluImm .add a0 x0 0xFFFFFFFF, .aluImm .add (24 : Fin 32) sp 0x7FF, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x121]
theorem p2vZSb44_end : blockEnd p256VerifyPrehashCode 0xB44 p2vZSb44 = some 0xB4E := by
  simp only [p2vZSb44]
  rw [blockEnd, p2v_at_b44]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b46]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b4a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSb56 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x1A1, .aluImm .add (8 : Fin 32) (9 : Fin 32) 0x40, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (8 : Fin 32)]
theorem p2vZSb56_end : blockEnd p256VerifyPrehashCode 0xB56 p2vZSb56 = some 0xB68 := by
  simp only [p2vZSb56]
  rw [blockEnd, p2v_at_b56]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b5a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b5e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b62]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b66]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSb70 : List BInstr :=
  [.alu .add a0 x0 (18 : Fin 32)]
theorem p2vZSb70_end : blockEnd p256VerifyPrehashCode 0xB70 p2vZSb70 = some 0xB72 := by
  simp only [p2vZSb70]
  rw [blockEnd, p2v_at_b70]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSb7a : List BInstr :=
  [.aluImm .and a0 a0 0xFF]
theorem p2vZSb7a_end : blockEnd p256VerifyPrehashCode 0xB7A p2vZSb7a = some 0xB7E := by
  simp only [p2vZSb7a]
  rw [blockEnd, p2v_at_b7a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSb80 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x781, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (9 : Fin 32)]
theorem p2vZSb80_end : blockEnd p256VerifyPrehashCode 0xB80 p2vZSb80 = some 0xB8E := by
  simp only [p2vZSb80]
  rw [blockEnd, p2v_at_b80]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b84]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b88]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b8c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSb9a : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x101, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (18 : Fin 32)]
theorem p2vZSb9a_end : blockEnd p256VerifyPrehashCode 0xB9A p2vZSb9a = some 0xBA8 := by
  simp only [p2vZSb9a]
  rw [blockEnd, p2v_at_b9a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_b9e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ba2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_ba6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSbb4 : List BInstr :=
  [.aluImm .add a0 sp 0x200, .aluImm .add a2 x0 0x24, .aluImm .add a1 x0 0x0]
theorem p2vZSbb4_end : blockEnd p256VerifyPrehashCode 0xBB4 p2vZSbb4 = some 0xBBC := by
  simp only [p2vZSbb4]
  rw [blockEnd, p2v_at_bb4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_bb6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_bba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSbc4 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (8 : Fin 32)]
theorem p2vZSbc4_end : blockEnd p256VerifyPrehashCode 0xBC4 p2vZSbc4 = some 0xBD2 := by
  simp only [p2vZSbc4]
  rw [blockEnd, p2v_at_bc4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_bc8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_bcc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_bd0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSbda : List BInstr :=
  [.alu .add a4 x0 (24 : Fin 32), .aluImm .add (24 : Fin 32) x0 0x0]
theorem p2vZSbda_end : blockEnd p256VerifyPrehashCode 0xBDA p2vZSbda = some 0xBDE := by
  simp only [p2vZSbda]
  rw [blockEnd, p2v_at_bda]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_bdc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSbe2 : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem p2vZSbe2_end : blockEnd p256VerifyPrehashCode 0xBE2 p2vZSbe2 = some 0xBE4 := by
  simp only [p2vZSbe2]
  rw [blockEnd, p2v_at_be2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vZSbe6 : List BInstr :=
  [.aluImm .add a0 x0 0x24F]
theorem p2vZSbe6_end : blockEnd p256VerifyPrehashCode 0xBE6 p2vZSbe6 = some 0xBEA := by
  simp only [p2vZSbe6]
  rw [blockEnd, p2v_at_be6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_zs {B : Word} {rv X Y Z : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0xB00 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (a0_180 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv)
    (a0_980 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = X)
    (a0_9a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = Y)
    (a0_9c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = Z)
    (RS : P2vRoSep B)
    (EC0 : P2vEcCode M0) :
    (¬ (True) ∧ P2vRet B v n0 0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0xBEE (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' a0 = BitVec.ofNat 32 0x24F ∧
        reg n' a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        reg n' (24 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 0x1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z ∧
        P2vKeepL B n0.mem n'.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24), (0xFE4, 0x20), (0x1004, 0x1), (0x40, 0x4)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xB00
  obtain ⟨n1, c1, u1⟩ := s0.block p2vZSb00 E0.self p2vZSb00_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem P2V n1 0xB14 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock p2vZSb00 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1338 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vZSb00, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vZSb00, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vZSb00, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m1]; exact a0_180
  have a1_980 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = X := by rw [m1]; exact a0_980
  have a1_9a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = Y := by rw [m1]; exact a0_9a0
  have a1_9c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = Z := by rw [m1]; exact a0_9c0
  -- 0xB14: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := p2v_mc (c := 0x1338) (d := 0x980) (N := 0x60) F E1 s1 p2v_at_b14 p2v_at_b18
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
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0x1338, 0x60)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_180
  have a2_980 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = X := (K2.acc (by decide) (by decide)).trans a1_980
  have a2_9a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = Y := (K2.acc (by decide) (by decide)).trans a1_9a0
  have a2_9c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = Z := (K2.acc (by decide) (by decide)).trans a1_9c0
  have a2_1338 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (accV_S 8 fun q hq => by
    rw [show 0x1338 + q = 0x1338 + (0x0 + q) by omega, X2 (0x0 + q) (by omega),
      show 0x980 + (0x0 + q) = 0x980 + q by omega]).trans a1_980
  have a2_1358 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (accV_S 8 fun q hq => by
    rw [show 0x1358 + q = 0x1338 + (0x20 + q) by omega, X2 (0x20 + q) (by omega),
      show 0x980 + (0x20 + q) = 0x9A0 + q by omega]).trans a1_9a0
  have a2_1378 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (accV_S 8 fun q hq => by
    rw [show 0x1378 + q = 0x1338 + (0x40 + q) by omega, X2 (0x40 + q) (by omega),
      show 0x980 + (0x40 + q) = 0x9C0 + q by omega]).trans a1_9c0
  clear a1_9c0 a1_9a0 a1_980 a1_180 g1_12 g1_11 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0xB1C
  obtain ⟨n3, c3, u3⟩ := s2.block p2vZSb1c E2.self p2vZSb1c_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem P2V n3 0xB3C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock p2vZSb1c (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_9 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vZSb1c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vZSb1c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_11 : reg n3 a1 = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vZSb1c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_12 : reg n3 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vZSb1c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_18 : reg n3 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vZSb1c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0x1338, 0x60)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m3]; exact a2_180
  have a3_980 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = X := by rw [m3]; exact a2_980
  have a3_9a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = Y := by rw [m3]; exact a2_9a0
  have a3_9c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = Z := by rw [m3]; exact a2_9c0
  have a3_1338 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m3]; exact a2_1338
  have a3_1358 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m3]; exact a2_1358
  have a3_1378 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m3]; exact a2_1378
  clear a2_1378 a2_1358 a2_1338 a2_9c0 a2_9a0 a2_980 a2_180 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0xB3C: memcpy from outside the stack
  obtain ⟨n4, P4, K4, X4⟩ := p2v_mcRo2 (c := 0x980) (N := 0x20) F RS E3 s3 p2v_at_b3c p2v_at_b40
    (by decide) (by decide) g3_2 g3_10 g3_11 g3_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s4 := P4.st
  have fr4 := P4.fr
  have t4 : Steps n0 n4 := t3.trans P4.steps
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [P4.regs sp (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P4.regs (3 : Fin 32) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P4.regs (4 : Fin 32) (by decide), g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [P4.regs (9 : Fin 32) (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [P4.regs (18 : Fin 32) (by decide), g3_18]
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0x1338, 0x60), (0x980, 0x20)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K4.acc (by decide) (by decide)).trans a3_180
  have a4_9a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = Y := (K4.acc (by decide) (by decide)).trans a3_9a0
  have a4_9c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = Z := (K4.acc (by decide) (by decide)).trans a3_9c0
  have a4_1338 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K4.acc (by decide) (by decide)).trans a3_1338
  have a4_1358 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K4.acc (by decide) (by decide)).trans a3_1358
  have a4_1378 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K4.acc (by decide) (by decide)).trans a3_1378
  have q4_980 : ∀ j, j < 32 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X4 j hj).trans (fR3 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a4_980 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := acc_of_frame q4_980
  clear a3_1378 a3_1358 a3_1338 a3_9c0 a3_9a0 a3_980 a3_180 g3_18 g3_12 g3_11 g3_10 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0xB44
  obtain ⟨n5, c5, u5⟩ := s4.block p2vZSb44 E4.self p2vZSb44_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem P2V n5 0xB4E (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock p2vZSb44 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_9 : reg n5 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vZSb44, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_18, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_24 : reg n5 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vZSb44, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_18, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0x1338, 0x60), (0x980, 0x20)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have q5_980 : ∀ j, j < 32 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_980 j hj
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m5]; exact a4_180
  have a5_980 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m5]; exact a4_980
  have a5_9a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = Y := by rw [m5]; exact a4_9a0
  have a5_9c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = Z := by rw [m5]; exact a4_9c0
  have a5_1338 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m5]; exact a4_1338
  have a5_1358 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m5]; exact a4_1358
  have a5_1378 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m5]; exact a4_1378
  clear a4_980 q4_980 a4_1378 a4_1358 a4_1338 a4_9c0 a4_9a0 a4_180 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 s4 X4 K4 P4
  -- 0xB4E: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := p2v_sw F E5 s5 p2v_at_b4e (off' := 0xB52) (c := 0x9C0)
    (by decide) (by rw [g5_24]; p2v_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [rg6 (9 : Fin 32), g5_9]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [rg6 a0, g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [rg6 (18 : Fin 32), g5_18]
  have g6_24 : reg n6 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg6 (24 : Fin 32), g5_24]
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_9c0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [W6, g5_10]
  have q6_980 : ∀ j, j < 32 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K6.range (by decide) (by decide) j hj).trans (q5_980 j hj)
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K6.acc (by decide) (by decide)).trans a5_180
  have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K6.acc (by decide) (by decide)).trans a5_980
  have a6_9a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = Y := (K6.acc (by decide) (by decide)).trans a5_9a0
  have a6_1338 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K6.acc (by decide) (by decide)).trans a5_1338
  have a6_1358 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K6.acc (by decide) (by decide)).trans a5_1358
  have a6_1378 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K6.acc (by decide) (by decide)).trans a5_1378
  clear a5_1378 a5_1358 a5_1338 a5_9c0 a5_9a0 a5_980 a5_180 q5_980 g5_24 g5_10 g5_18 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0xB52: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := p2v_sw F E6 s6 p2v_at_b52 (off' := 0xB56) (c := 0x9C4)
    (by decide) (by rw [g6_24]; p2v_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_9 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [rg7 (9 : Fin 32), g6_9]
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [rg7 a0, g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_24 : reg n7 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg7 (24 : Fin 32), g6_24]
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_9c0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K7.w32 (by decide) (by decide)).trans w6_9c0
  have w7_9c4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [W7, g6_10]
  have q7_980 : ∀ j, j < 32 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_980 j hj)
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K7.acc (by decide) (by decide)).trans a6_180
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K7.acc (by decide) (by decide)).trans a6_980
  have a7_9a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = Y := (K7.acc (by decide) (by decide)).trans a6_9a0
  have a7_1338 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K7.acc (by decide) (by decide)).trans a6_1338
  have a7_1358 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K7.acc (by decide) (by decide)).trans a6_1358
  have a7_1378 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K7.acc (by decide) (by decide)).trans a6_1378
  clear a6_1378 a6_1358 a6_1338 a6_9a0 a6_980 a6_180 q6_980 w6_9c0 g6_24 g6_18 g6_10 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0xB56
  obtain ⟨n8, c8, u8⟩ := s7.block p2vZSb56 E7.self p2vZSb56_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem P2V n8 0xB68 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock p2vZSb56 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_9 : reg n8 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_24 : reg n8 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vZSb56, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_9, g7_10, g7_18, g7_24, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x9A0 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vZSb56, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_9, g7_10, g7_18, g7_24, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g8_11 : reg n8 a1 = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vZSb56, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_9, g7_10, g7_18, g7_24, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g8_12 : reg n8 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vZSb56, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_9, g7_10, g7_18, g7_24, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_9c0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m8]; exact w7_9c0
  have w8_9c4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m8]; exact w7_9c4
  have q8_980 : ∀ j, j < 32 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m8]; exact q7_980 j hj
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m8]; exact a7_180
  have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m8]; exact a7_980
  have a8_9a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = Y := by rw [m8]; exact a7_9a0
  have a8_1338 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m8]; exact a7_1338
  have a8_1358 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m8]; exact a7_1358
  have a8_1378 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m8]; exact a7_1378
  clear a7_1378 a7_1358 a7_1338 a7_9a0 a7_980 a7_180 q7_980 w7_9c4 w7_9c0 g7_24 g7_18 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0xB68: memcpy from outside the stack
  obtain ⟨n9, P9, K9, X9⟩ := p2v_mcRo2 (c := 0x9A0) (N := 0x20) F RS E8 s8 p2v_at_b68 p2v_at_b6c
    (by decide) (by decide) g8_2 g8_10 g8_11 g8_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s9 := P9.st
  have fr9 := P9.fr
  have t9 : Steps n0 n9 := t8.trans P9.steps
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [P9.regs sp (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P9.regs (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P9.regs (4 : Fin 32) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [P9.regs (8 : Fin 32) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [P9.regs (9 : Fin 32) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [P9.regs (18 : Fin 32) (by decide), g8_18]
  have g9_24 : reg n9 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P9.regs (24 : Fin 32) (by decide), g8_24]
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_9c0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K9.w32 (by decide) (by decide)).trans w8_9c0
  have w9_9c4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K9.w32 (by decide) (by decide)).trans w8_9c4
  have q9_980 : ∀ j, j < 32 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_980 j hj)
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K9.acc (by decide) (by decide)).trans a8_180
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K9.acc (by decide) (by decide)).trans a8_980
  have a9_1338 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K9.acc (by decide) (by decide)).trans a8_1338
  have a9_1358 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K9.acc (by decide) (by decide)).trans a8_1358
  have a9_1378 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K9.acc (by decide) (by decide)).trans a8_1378
  have q9_9a0 : ∀ j, j < 32 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) :=
    fun j hj => (X9 j hj).trans (fR8 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a9_9a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := acc_of_frame q9_9a0
  clear a8_1378 a8_1358 a8_1338 a8_9a0 a8_980 a8_180 q8_980 w8_9c4 w8_9c0 g8_12 g8_11 g8_10 g8_8 g8_24 g8_18 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0xB70
  obtain ⟨n10, c10, u10⟩ := s9.block p2vZSb70 E9.self p2vZSb70_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem P2V n10 0xB72 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock p2vZSb70 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_24 : reg n10 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vZSb70, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_24, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_9c0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m10]; exact w9_9c0
  have w10_9c4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m10]; exact w9_9c4
  have q10_980 : ∀ j, j < 32 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m10]; exact q9_980 j hj
  have q10_9a0 : ∀ j, j < 32 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m10]; exact q9_9a0 j hj
  have a10_180 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m10]; exact a9_180
  have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m10]; exact a9_980
  have a10_9a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m10]; exact a9_9a0
  have a10_1338 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m10]; exact a9_1338
  have a10_1358 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m10]; exact a9_1358
  have a10_1378 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m10]; exact a9_1378
  clear a9_9a0 q9_9a0 a9_1378 a9_1358 a9_1338 a9_980 a9_180 q9_980 w9_9c4 w9_9c0 g9_24 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 s9 X9 K9 P9
  -- 0xB72: p2v_unz8F
  obtain ⟨n11, c11, s11, sp11, rk11, a0_11, K11, fr11⟩ := p2v_unz8F (cx := 0x1378)
    F E10 (EC0.p2v F fR10) s10 p2v_at_b72 p2v_at_b76 (by decide) (by decide) g10_2
    g10_10 (by decide) (by decide)
  simp only [limbs0_iff a10_1378] at a0_11
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.keepL K11 (by decide)
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk11 (3 : Fin 32) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk11 (4 : Fin 32) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [rk11 (8 : Fin 32) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [rk11 (9 : Fin 32) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [rk11 (18 : Fin 32) (by decide), g10_18]
  have g11_24 : reg n11 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk11 (24 : Fin 32) (by decide), g10_24]
  have g11_2 : reg n11 sp = B + 0x21A0 := sp11
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20)] := keep_kk10.trans K11
  clear keep_kk10
  have w11_9c0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K11.w32 (by decide) (by decide)).trans w10_9c0
  have w11_9c4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K11.w32 (by decide) (by decide)).trans w10_9c4
  have q11_980 : ∀ j, j < 32 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_980 j hj)
  have q11_9a0 : ∀ j, j < 32 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_9a0 j hj)
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K11.acc (by decide) (by decide)).trans a10_180
  have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K11.acc (by decide) (by decide)).trans a10_980
  have a11_9a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K11.acc (by decide) (by decide)).trans a10_9a0
  have a11_1338 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K11.acc (by decide) (by decide)).trans a10_1338
  have a11_1358 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K11.acc (by decide) (by decide)).trans a10_1358
  have a11_1378 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K11.acc (by decide) (by decide)).trans a10_1378
  clear a10_1378 a10_1358 a10_1338 a10_9a0 a10_980 a10_180 q10_9a0 q10_980 w10_9c4 w10_9c0 g10_10 g10_24 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  have g11_10 : reg n11 a0 = (if Z = 0 then 0 else 1 : Word) := a0_11
  -- 0xB7A
  obtain ⟨n12, c12, u12⟩ := s11.block p2vZSb7a E11.self p2vZSb7a_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem P2V n12 0xB7E (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock p2vZSb7a (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  have fr12 : ∀ x, P2vR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans c12
  have fR12 : ∀ x, P2vR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : P2vCode n12.mem := E11.fr F fr12
  have V12 : P2vSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by
    rw [rb12, runBlock_reg _ _ _ sp s11.zero (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (3 : Fin 32) s11.zero (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (4 : Fin 32) s11.zero (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_24 : reg n12 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_10 : reg n12 a0 = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vZSb7a, upd, ↓reduceIte]; rw [g11_10] <;> rfl
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_9c0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m12]; exact w11_9c0
  have w12_9c4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m12]; exact w11_9c4
  have q12_980 : ∀ j, j < 32 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_980 j hj
  have q12_9a0 : ∀ j, j < 32 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_9a0 j hj
  have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m12]; exact a11_180
  have a12_980 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m12]; exact a11_980
  have a12_9a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m12]; exact a11_9a0
  have a12_1338 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m12]; exact a11_1338
  have a12_1358 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m12]; exact a11_1358
  have a12_1378 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m12]; exact a11_1378
  clear a11_1378 a11_1358 a11_1338 a11_9a0 a11_980 a11_180 q11_9a0 q11_980 w11_9c4 w11_9c0 g11_2 g11_24 g11_18 g11_9 g11_8 g11_4 g11_3 V11 E11 fR11 t11 fr11 K11 a0_11 rk11 sp11 s11 c11
  -- 0xB7E: sw
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := p2v_sw F E12 s12 p2v_at_b7e (off' := 0xB80) (c := 0x10)
    (by decide) (by rw [g12_2]; p2v_addr) (by decide) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, P2vR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : P2vCode n13.mem := E12.fr F fr13
  have V13 : P2vSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [rg13 (8 : Fin 32), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [rg13 (9 : Fin 32), g12_9]
  have g13_10 : reg n13 a0 = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [rg13 a0, g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_24 : reg n13 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg13 (24 : Fin 32), g12_24]
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_9c0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K13.w32 (by decide) (by decide)).trans w12_9c0
  have w13_9c4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K13.w32 (by decide) (by decide)).trans w12_9c4
  have w13_10 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [W13, g12_10]
  have q13_980 : ∀ j, j < 32 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K13.range (by decide) (by decide) j hj).trans (q12_980 j hj)
  have q13_9a0 : ∀ j, j < 32 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K13.range (by decide) (by decide) j hj).trans (q12_9a0 j hj)
  have a13_180 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K13.acc (by decide) (by decide)).trans a12_180
  have a13_980 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K13.acc (by decide) (by decide)).trans a12_980
  have a13_9a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K13.acc (by decide) (by decide)).trans a12_9a0
  have a13_1338 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K13.acc (by decide) (by decide)).trans a12_1338
  have a13_1358 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K13.acc (by decide) (by decide)).trans a12_1358
  have a13_1378 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K13.acc (by decide) (by decide)).trans a12_1378
  clear a12_1378 a12_1358 a12_1338 a12_9a0 a12_980 a12_180 q12_9a0 q12_980 w12_9c4 w12_9c0 g12_10 g12_24 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12 g11_10
  -- 0xB80
  obtain ⟨n14, c14, u14⟩ := s13.block p2vZSb80 E13.self p2vZSb80_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem P2V n14 0xB8E (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock p2vZSb80 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
  have fr14 : ∀ x, P2vR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, P2vR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : P2vCode n14.mem := E13.fr F fr14
  have V14 : P2vSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by
    rw [rb14, runBlock_reg _ _ _ sp s13.zero (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (3 : Fin 32) s13.zero (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (4 : Fin 32) s13.zero (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_24 : reg n14 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vZSb80, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_18, g13_24, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vZSb80, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_18, g13_24, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_12 : reg n14 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vZSb80, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_18, g13_24, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_10 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m14]; exact w13_10
  have w14_9c0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m14]; exact w13_9c0
  have w14_9c4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m14]; exact w13_9c4
  have q14_980 : ∀ j, j < 32 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m14]; exact q13_980 j hj
  have q14_9a0 : ∀ j, j < 32 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m14]; exact q13_9a0 j hj
  have a14_180 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m14]; exact a13_180
  have a14_980 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m14]; exact a13_980
  have a14_9a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m14]; exact a13_9a0
  have a14_1338 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m14]; exact a13_1338
  have a14_1358 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m14]; exact a13_1358
  have a14_1378 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m14]; exact a13_1378
  clear a13_1378 a13_1358 a13_1338 a13_9a0 a13_980 a13_180 q13_9a0 q13_980 w13_10 w13_9c4 w13_9c0 g13_24 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0xB8E: memcpy from outside the stack
  obtain ⟨n15, P15, K15, X15⟩ := p2v_mcRo2 (c := 0xF80) (N := 0x20) F RS E14 s14 p2v_at_b8e p2v_at_b92
    (by decide) (by decide) g14_2 g14_10 g14_11 g14_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s15 := P15.st
  have fr15 := P15.fr
  have t15 : Steps n0 n15 := t14.trans P15.steps
  have fR15 : ∀ x, P2vR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : P2vCode n15.mem := E14.fr F fr15
  have V15 : P2vSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [P15.regs sp (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P15.regs (3 : Fin 32) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P15.regs (4 : Fin 32) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [P15.regs (8 : Fin 32) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [P15.regs (9 : Fin 32) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [P15.regs (18 : Fin 32) (by decide), g14_18]
  have g15_24 : reg n15 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P15.regs (24 : Fin 32) (by decide), g14_24]
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_10 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K15.w32 (by decide) (by decide)).trans w14_10
  have w15_9c0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K15.w32 (by decide) (by decide)).trans w14_9c0
  have w15_9c4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K15.w32 (by decide) (by decide)).trans w14_9c4
  have q15_980 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_980 j hj)
  have q15_9a0 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_9a0 j hj)
  have a15_180 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K15.acc (by decide) (by decide)).trans a14_180
  have a15_980 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K15.acc (by decide) (by decide)).trans a14_980
  have a15_9a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K15.acc (by decide) (by decide)).trans a14_9a0
  have a15_1338 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K15.acc (by decide) (by decide)).trans a14_1338
  have a15_1358 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K15.acc (by decide) (by decide)).trans a14_1358
  have a15_1378 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K15.acc (by decide) (by decide)).trans a14_1378
  have q15_f80 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X15 j hj).trans (fR14 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a15_f80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := acc_of_frame q15_f80
  clear a14_1378 a14_1358 a14_1338 a14_9a0 a14_980 a14_180 q14_9a0 q14_980 w14_9c4 w14_9c0 w14_10 g14_12 g14_11 g14_10 g14_24 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0xB96: sb
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := p2v_sb F E15 s15 p2v_at_b96 (off' := 0xB9A) (c := 0xFA0)
    (by decide) (by rw [g15_24]; p2v_addr) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [rg16 (8 : Fin 32), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_24 : reg n16 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg16 (24 : Fin 32), g15_24]
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_10 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K16.w32 (by decide) (by decide)).trans w15_10
  have w16_9c0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K16.w32 (by decide) (by decide)).trans w15_9c0
  have w16_9c4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K16.w32 (by decide) (by decide)).trans w15_9c4
  have b16_fa0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W16, s15.zero]; rfl
  have q16_980 : ∀ j, j < 32 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_980 j hj)
  have q16_9a0 : ∀ j, j < 32 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_9a0 j hj)
  have q16_f80 : ∀ j, j < 32 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_f80 j hj)
  have a16_180 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K16.acc (by decide) (by decide)).trans a15_180
  have a16_980 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K16.acc (by decide) (by decide)).trans a15_980
  have a16_9a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K16.acc (by decide) (by decide)).trans a15_9a0
  have a16_f80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K16.acc (by decide) (by decide)).trans a15_f80
  have a16_1338 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K16.acc (by decide) (by decide)).trans a15_1338
  have a16_1358 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K16.acc (by decide) (by decide)).trans a15_1358
  have a16_1378 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K16.acc (by decide) (by decide)).trans a15_1378
  clear a15_f80 q15_f80 a15_1378 a15_1358 a15_1338 a15_9a0 a15_980 a15_180 q15_9a0 q15_980 w15_9c4 w15_9c0 w15_10 g15_24 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 s15 X15 K15 P15
  -- 0xB9A
  obtain ⟨n17, c17, u17⟩ := s16.block p2vZSb9a E16.self p2vZSb9a_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem P2V n17 0xBA8 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock p2vZSb9a (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_24 : reg n17 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vZSb9a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_24, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vZSb9a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_24, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vZSb9a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_24, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_10 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m17]; exact w16_10
  have w17_9c0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m17]; exact w16_9c0
  have w17_9c4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m17]; exact w16_9c4
  have b17_fa0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m17]; exact b16_fa0
  have q17_980 : ∀ j, j < 32 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_980 j hj
  have q17_9a0 : ∀ j, j < 32 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_9a0 j hj
  have q17_f80 : ∀ j, j < 32 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_f80 j hj
  have a17_180 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m17]; exact a16_180
  have a17_980 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m17]; exact a16_980
  have a17_9a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m17]; exact a16_9a0
  have a17_f80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m17]; exact a16_f80
  have a17_1338 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m17]; exact a16_1338
  have a17_1358 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m17]; exact a16_1358
  have a17_1378 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m17]; exact a16_1378
  clear a16_1378 a16_1358 a16_1338 a16_f80 a16_9a0 a16_980 a16_180 q16_f80 q16_9a0 q16_980 b16_fa0 w16_9c4 w16_9c0 w16_10 g16_24 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0xBA8: memcpy
  obtain ⟨n18, P18, K18, X18⟩ := p2v_mc (c := 0x900) (d := 0x1378) (N := 0x20) F E17 s17 p2v_at_ba8 p2v_at_bac
    (by decide) (by decide) g17_2 g17_10 g17_11 g17_12
    (by decide) (by decide) (by decide)
  have s18 := P18.st
  have fr18 := P18.fr
  have t18 : Steps n0 n18 := t17.trans P18.steps
  have fR18 : ∀ x, P2vR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : P2vCode n18.mem := E17.fr F fr18
  have V18 : P2vSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [P18.regs sp (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P18.regs (3 : Fin 32) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P18.regs (4 : Fin 32) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [P18.regs (8 : Fin 32) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [P18.regs (9 : Fin 32) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [P18.regs (18 : Fin 32) (by decide), g17_18]
  have g18_24 : reg n18 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P18.regs (24 : Fin 32) (by decide), g17_24]
  have keep_kk18 : P2vKeepL B n0.mem n18.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_10 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K18.w32 (by decide) (by decide)).trans w17_10
  have w18_9c0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K18.w32 (by decide) (by decide)).trans w17_9c0
  have w18_9c4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K18.w32 (by decide) (by decide)).trans w17_9c4
  have b18_fa0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_fa0
  have q18_980 : ∀ j, j < 32 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_980 j hj)
  have q18_9a0 : ∀ j, j < 32 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_9a0 j hj)
  have q18_f80 : ∀ j, j < 32 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_f80 j hj)
  have a18_180 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K18.acc (by decide) (by decide)).trans a17_180
  have a18_980 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K18.acc (by decide) (by decide)).trans a17_980
  have a18_9a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K18.acc (by decide) (by decide)).trans a17_9a0
  have a18_f80 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K18.acc (by decide) (by decide)).trans a17_f80
  have a18_1338 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K18.acc (by decide) (by decide)).trans a17_1338
  have a18_1358 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K18.acc (by decide) (by decide)).trans a17_1358
  have a18_1378 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K18.acc (by decide) (by decide)).trans a17_1378
  have a18_900 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := (accV_S 8 fun q hq => by
    rw [show 0x900 + q = 0x900 + (0x0 + q) by omega, X18 (0x0 + q) (by omega),
      show 0x1378 + (0x0 + q) = 0x1378 + q by omega]).trans a17_1378
  clear a17_1378 a17_1358 a17_1338 a17_f80 a17_9a0 a17_980 a17_180 q17_f80 q17_9a0 q17_980 b17_fa0 w17_9c4 w17_9c0 w17_10 g17_12 g17_11 g17_10 g17_24 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0xBB0: sb
  obtain ⟨n19, d19, s19, fr19, K19, W19, rg19⟩ := p2v_sb F E18 s18 p2v_at_bb0 (off' := 0xBB4) (c := 0x920)
    (by decide) (by rw [g18_24]; p2v_addr) (by decide)
  have t19 : Steps n0 n19 := t18.trans d19
  have fR19 : ∀ x, P2vR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : P2vCode n19.mem := E18.fr F fr19
  have V19 : P2vSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rg19 sp, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg19 (3 : Fin 32), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg19 (4 : Fin 32), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [rg19 (8 : Fin 32), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [rg19 (9 : Fin 32), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [rg19 (18 : Fin 32), g18_18]
  have g19_24 : reg n19 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg19 (24 : Fin 32), g18_24]
  have keep_kk19 : P2vKeepL B n0.mem n19.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1)] := keep_kk18.trans K19.toL
  clear keep_kk18
  have w19_10 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K19.w32 (by decide) (by decide)).trans w18_10
  have w19_9c0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K19.w32 (by decide) (by decide)).trans w18_9c0
  have w19_9c4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K19.w32 (by decide) (by decide)).trans w18_9c4
  have b19_fa0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_fa0
  have b19_920 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W19, s18.zero]; rfl
  have q19_980 : ∀ j, j < 32 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_980 j hj)
  have q19_9a0 : ∀ j, j < 32 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_9a0 j hj)
  have q19_f80 : ∀ j, j < 32 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_f80 j hj)
  have a19_180 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K19.acc (by decide) (by decide)).trans a18_180
  have a19_900 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := (K19.acc (by decide) (by decide)).trans a18_900
  have a19_980 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K19.acc (by decide) (by decide)).trans a18_980
  have a19_9a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K19.acc (by decide) (by decide)).trans a18_9a0
  have a19_f80 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K19.acc (by decide) (by decide)).trans a18_f80
  have a19_1338 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K19.acc (by decide) (by decide)).trans a18_1338
  have a19_1358 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K19.acc (by decide) (by decide)).trans a18_1358
  have a19_1378 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K19.acc (by decide) (by decide)).trans a18_1378
  clear a18_900 a18_1378 a18_1358 a18_1338 a18_f80 a18_9a0 a18_980 a18_180 q18_f80 q18_9a0 q18_980 b18_fa0 w18_9c4 w18_9c0 w18_10 g18_24 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 s18 X18 K18 P18
  -- 0xBB4
  obtain ⟨n20, c20, u20⟩ := s19.block p2vZSbb4 E19.self p2vZSbb4_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem P2V n20 0xBBC (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock p2vZSbb4 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_24 : reg n20 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vZSbb4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_24, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vZSbb4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_24, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g20_12 : reg n20 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vZSbb4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_24, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk20 : P2vKeepL B n0.mem n20.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_10 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m20]; exact w19_10
  have w20_9c0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m20]; exact w19_9c0
  have w20_9c4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m20]; exact w19_9c4
  have b20_920 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m20]; exact b19_920
  have b20_fa0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m20]; exact b19_fa0
  have q20_980 : ∀ j, j < 32 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_980 j hj
  have q20_9a0 : ∀ j, j < 32 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_9a0 j hj
  have q20_f80 : ∀ j, j < 32 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_f80 j hj
  have a20_180 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m20]; exact a19_180
  have a20_900 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := by rw [m20]; exact a19_900
  have a20_980 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m20]; exact a19_980
  have a20_9a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m20]; exact a19_9a0
  have a20_f80 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m20]; exact a19_f80
  have a20_1338 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m20]; exact a19_1338
  have a20_1358 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m20]; exact a19_1358
  have a20_1378 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m20]; exact a19_1378
  clear a19_1378 a19_1358 a19_1338 a19_f80 a19_9a0 a19_980 a19_900 a19_180 q19_f80 q19_9a0 q19_980 b19_920 b19_fa0 w19_9c4 w19_9c0 w19_10 g19_24 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 rg19 W19 K19 fr19 s19 d19
  -- 0xBBC: p2v_ms3F
  obtain ⟨n21, c21, s21, rk21, K21, fr21, Z21⟩ := p2v_ms3F (c := 0x200) (N := 0x24)
    F E20 s20 p2v_at_bbc p2v_at_bc0 (by decide) (by decide)
    g20_10 g20_11 g20_12 (by decide)
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, P2vR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : P2vCode n21.mem := E20.fr F fr21
  have V21 : P2vSaves B n21.mem v := V20.keepL K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rk21 sp (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk21 (3 : Fin 32) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk21 (4 : Fin 32) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [rk21 (8 : Fin 32) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [rk21 (9 : Fin 32) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [rk21 (18 : Fin 32) (by decide), g20_18]
  have g21_24 : reg n21 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk21 (24 : Fin 32) (by decide), g20_24]
  have keep_kk21 : P2vKeepL B n0.mem n21.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24)] := keep_kk20.trans K21
  clear keep_kk20
  have w21_10 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K21.w32 (by decide) (by decide)).trans w20_10
  have w21_9c0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K21.w32 (by decide) (by decide)).trans w20_9c0
  have w21_9c4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K21.w32 (by decide) (by decide)).trans w20_9c4
  have b21_920 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_920
  have b21_fa0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_fa0
  have q21_980 : ∀ j, j < 32 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K21.range (by decide) (by decide) j hj).trans (q20_980 j hj)
  have q21_9a0 : ∀ j, j < 32 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K21.range (by decide) (by decide) j hj).trans (q20_9a0 j hj)
  have q21_f80 : ∀ j, j < 32 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K21.range (by decide) (by decide) j hj).trans (q20_f80 j hj)
  have a21_180 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K21.acc (by decide) (by decide)).trans a20_180
  have a21_900 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := (K21.acc (by decide) (by decide)).trans a20_900
  have a21_980 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K21.acc (by decide) (by decide)).trans a20_980
  have a21_9a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K21.acc (by decide) (by decide)).trans a20_9a0
  have a21_f80 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K21.acc (by decide) (by decide)).trans a20_f80
  have a21_1338 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K21.acc (by decide) (by decide)).trans a20_1338
  have a21_1358 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K21.acc (by decide) (by decide)).trans a20_1358
  have a21_1378 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K21.acc (by decide) (by decide)).trans a20_1378
  have a21_200 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 := acc0_of_fill fun j hj => by rw [show 0x200 + j = 0x200 + (0x0 + j) by omega]; exact Z21 _ (by omega)
  have b21_220 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 := by rw [show 0x220 = 0x200 + 0x20 from rfl]; exact Z21 _ (by decide)
  clear a20_1378 a20_1358 a20_1338 a20_f80 a20_9a0 a20_980 a20_900 a20_180 q20_f80 q20_9a0 q20_980 b20_fa0 b20_920 w20_9c4 w20_9c0 w20_10 g20_12 g20_11 g20_10 g20_24 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0xBC4
  obtain ⟨n22, c22, u22⟩ := s21.block p2vZSbc4 E21.self p2vZSbc4_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem P2V n22 0xBD2 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock p2vZSbc4 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
  have fr22 : ∀ x, P2vR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, P2vR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : P2vCode n22.mem := E21.fr F fr22
  have V22 : P2vSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by
    rw [rb22, runBlock_reg _ _ _ sp s21.zero (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (3 : Fin 32) s21.zero (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (4 : Fin 32) s21.zero (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_24 : reg n22 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_10 : reg n22 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vZSbc4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_18, g21_24, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g22_11 : reg n22 a1 = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vZSbc4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_18, g21_24, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g22_12 : reg n22 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vZSbc4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_18, g21_24, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_10 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m22]; exact w21_10
  have w22_9c0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m22]; exact w21_9c0
  have w22_9c4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m22]; exact w21_9c4
  have b22_220 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 := by rw [m22]; exact b21_220
  have b22_920 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m22]; exact b21_920
  have b22_fa0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m22]; exact b21_fa0
  have q22_980 : ∀ j, j < 32 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m22]; exact q21_980 j hj
  have q22_9a0 : ∀ j, j < 32 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m22]; exact q21_9a0 j hj
  have q22_f80 : ∀ j, j < 32 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m22]; exact q21_f80 j hj
  have a22_180 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m22]; exact a21_180
  have a22_200 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 := by rw [m22]; exact a21_200
  have a22_900 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := by rw [m22]; exact a21_900
  have a22_980 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m22]; exact a21_980
  have a22_9a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m22]; exact a21_9a0
  have a22_f80 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m22]; exact a21_f80
  have a22_1338 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m22]; exact a21_1338
  have a22_1358 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m22]; exact a21_1358
  have a22_1378 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m22]; exact a21_1378
  clear b21_220 a21_200 a21_1378 a21_1358 a21_1338 a21_f80 a21_9a0 a21_980 a21_900 a21_180 q21_f80 q21_9a0 q21_980 b21_fa0 b21_920 w21_9c4 w21_9c0 w21_10 g21_24 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 Z21 fr21 K21 rk21 s21 c21
  -- 0xBD2: memcpy from outside the stack
  obtain ⟨n23, P23, K23, X23⟩ := p2v_mcRo2 (c := 0xFE4) (N := 0x20) F RS E22 s22 p2v_at_bd2 p2v_at_bd6
    (by decide) (by decide) g22_2 g22_10 g22_11 g22_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s23 := P23.st
  have fr23 := P23.fr
  have t23 : Steps n0 n23 := t22.trans P23.steps
  have fR23 : ∀ x, P2vR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : P2vCode n23.mem := E22.fr F fr23
  have V23 : P2vSaves B n23.mem v := V22.keep K23 (by decide)
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [P23.regs sp (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P23.regs (3 : Fin 32) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P23.regs (4 : Fin 32) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [P23.regs (8 : Fin 32) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [P23.regs (9 : Fin 32) (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [P23.regs (18 : Fin 32) (by decide), g22_18]
  have g23_24 : reg n23 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P23.regs (24 : Fin 32) (by decide), g22_24]
  have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24), (0xFE4, 0x20)] := keep_kk22.trans K23.toL
  clear keep_kk22
  have w23_10 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K23.w32 (by decide) (by decide)).trans w22_10
  have w23_9c0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K23.w32 (by decide) (by decide)).trans w22_9c0
  have w23_9c4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K23.w32 (by decide) (by decide)).trans w22_9c4
  have b23_220 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 := (K23.b8 (by decide) (by decide)).trans b22_220
  have b23_920 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K23.b8 (by decide) (by decide)).trans b22_920
  have b23_fa0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K23.b8 (by decide) (by decide)).trans b22_fa0
  have q23_980 : ∀ j, j < 32 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_980 j hj)
  have q23_9a0 : ∀ j, j < 32 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_9a0 j hj)
  have q23_f80 : ∀ j, j < 32 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_f80 j hj)
  have a23_180 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K23.acc (by decide) (by decide)).trans a22_180
  have a23_200 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 := (K23.acc (by decide) (by decide)).trans a22_200
  have a23_900 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := (K23.acc (by decide) (by decide)).trans a22_900
  have a23_980 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K23.acc (by decide) (by decide)).trans a22_980
  have a23_9a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K23.acc (by decide) (by decide)).trans a22_9a0
  have a23_f80 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K23.acc (by decide) (by decide)).trans a22_f80
  have a23_1338 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K23.acc (by decide) (by decide)).trans a22_1338
  have a23_1358 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K23.acc (by decide) (by decide)).trans a22_1358
  have a23_1378 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K23.acc (by decide) (by decide)).trans a22_1378
  have q23_fe4 : ∀ j, j < 32 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) :=
    fun j hj => (X23 j hj).trans (fR22 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a23_fe4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := acc_of_frame q23_fe4
  clear a22_1378 a22_1358 a22_1338 a22_f80 a22_9a0 a22_980 a22_900 a22_200 a22_180 q22_f80 q22_9a0 q22_980 b22_fa0 b22_920 b22_220 w22_9c4 w22_9c0 w22_10 g22_12 g22_11 g22_10 g22_24 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0xBDA
  obtain ⟨n24, c24, u24⟩ := s23.block p2vZSbda E23.self p2vZSbda_end
    ⟨trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem P2V n24 0xBDE (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock p2vZSbda (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
  have fr24 : ∀ x, P2vR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans c24
  have fR24 : ∀ x, P2vR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : P2vCode n24.mem := E23.fr F fr24
  have V24 : P2vSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by
    rw [rb24, runBlock_reg _ _ _ sp s23.zero (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (3 : Fin 32) s23.zero (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (4 : Fin 32) s23.zero (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_14 : reg n24 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, p2vZSbda, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_24, s23.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g24_24 : reg n24 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, p2vZSbda, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_24, s23.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk24 : P2vKeepL B n0.mem n24.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24), (0xFE4, 0x20)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_10 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m24]; exact w23_10
  have w24_9c0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m24]; exact w23_9c0
  have w24_9c4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m24]; exact w23_9c4
  have b24_220 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 := by rw [m24]; exact b23_220
  have b24_920 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m24]; exact b23_920
  have b24_fa0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m24]; exact b23_fa0
  have q24_980 : ∀ j, j < 32 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_980 j hj
  have q24_9a0 : ∀ j, j < 32 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_9a0 j hj
  have q24_f80 : ∀ j, j < 32 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_f80 j hj
  have q24_fe4 : ∀ j, j < 32 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_fe4 j hj
  have a24_180 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m24]; exact a23_180
  have a24_200 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 := by rw [m24]; exact a23_200
  have a24_900 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := by rw [m24]; exact a23_900
  have a24_980 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m24]; exact a23_980
  have a24_9a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m24]; exact a23_9a0
  have a24_f80 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m24]; exact a23_f80
  have a24_fe4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m24]; exact a23_fe4
  have a24_1338 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m24]; exact a23_1338
  have a24_1358 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m24]; exact a23_1358
  have a24_1378 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m24]; exact a23_1378
  clear a23_fe4 q23_fe4 a23_1378 a23_1358 a23_1338 a23_f80 a23_9a0 a23_980 a23_900 a23_200 a23_180 q23_f80 q23_9a0 q23_980 b23_fa0 b23_920 b23_220 w23_9c4 w23_9c0 w23_10 g23_24 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 s23 X23 K23 P23
  -- 0xBDE: sb
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := p2v_sb F E24 s24 p2v_at_bde (off' := 0xBE2) (c := 0x1004)
    (by decide) (by rw [g24_14]; p2v_addr) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, P2vR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : P2vCode n25.mem := E24.fr F fr25
  have V25 : P2vSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [rg25 (8 : Fin 32), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [rg25 (9 : Fin 32), g24_9]
  have g25_14 : reg n25 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg25 a4, g24_14]
  have g25_18 : reg n25 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_24 : reg n25 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg25 (24 : Fin 32), g24_24]
  have keep_kk25 : P2vKeepL B n0.mem n25.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24), (0xFE4, 0x20), (0x1004, 0x1)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_10 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K25.w32 (by decide) (by decide)).trans w24_10
  have w25_9c0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K25.w32 (by decide) (by decide)).trans w24_9c0
  have w25_9c4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K25.w32 (by decide) (by decide)).trans w24_9c4
  have b25_220 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 := (K25.b8 (by decide) (by decide)).trans b24_220
  have b25_920 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_920
  have b25_fa0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_fa0
  have b25_1004 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W25, s24.zero]; rfl
  have q25_980 : ∀ j, j < 32 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_980 j hj)
  have q25_9a0 : ∀ j, j < 32 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_9a0 j hj)
  have q25_f80 : ∀ j, j < 32 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_f80 j hj)
  have q25_fe4 : ∀ j, j < 32 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_fe4 j hj)
  have a25_180 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K25.acc (by decide) (by decide)).trans a24_180
  have a25_200 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 := (K25.acc (by decide) (by decide)).trans a24_200
  have a25_900 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := (K25.acc (by decide) (by decide)).trans a24_900
  have a25_980 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K25.acc (by decide) (by decide)).trans a24_980
  have a25_9a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K25.acc (by decide) (by decide)).trans a24_9a0
  have a25_f80 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K25.acc (by decide) (by decide)).trans a24_f80
  have a25_fe4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K25.acc (by decide) (by decide)).trans a24_fe4
  have a25_1338 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K25.acc (by decide) (by decide)).trans a24_1338
  have a25_1358 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K25.acc (by decide) (by decide)).trans a24_1358
  have a25_1378 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K25.acc (by decide) (by decide)).trans a24_1378
  clear a24_1378 a24_1358 a24_1338 a24_fe4 a24_f80 a24_9a0 a24_980 a24_900 a24_200 a24_180 q24_fe4 q24_f80 q24_9a0 q24_980 b24_fa0 b24_920 b24_220 w24_9c4 w24_9c0 w24_10 g24_24 g24_14 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0xBE2
  obtain ⟨n26, c26, u26⟩ := s25.block p2vZSbe2 E25.self p2vZSbe2_end
    ⟨trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem P2V n26 0xBE4 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock p2vZSbe2 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
  have fr26 : ∀ x, P2vR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, P2vR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : P2vCode n26.mem := E25.fr F fr26
  have V26 : P2vSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by
    rw [rb26, runBlock_reg _ _ _ sp s25.zero (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (3 : Fin 32) s25.zero (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (4 : Fin 32) s25.zero (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
  have g26_14 : reg n26 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb26, runBlock_reg _ _ _ a4 s25.zero (by decide), g25_14]
  have g26_18 : reg n26 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
  have g26_24 : reg n26 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
  have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, p2vZSbe2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_14, g25_18, g25_24, s25.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk26 : P2vKeepL B n0.mem n26.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24), (0xFE4, 0x20), (0x1004, 0x1)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_10 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m26]; exact w25_10
  have w26_9c0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m26]; exact w25_9c0
  have w26_9c4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m26]; exact w25_9c4
  have b26_220 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 := by rw [m26]; exact b25_220
  have b26_920 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m26]; exact b25_920
  have b26_fa0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m26]; exact b25_fa0
  have b26_1004 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m26]; exact b25_1004
  have q26_980 : ∀ j, j < 32 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_980 j hj
  have q26_9a0 : ∀ j, j < 32 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_9a0 j hj
  have q26_f80 : ∀ j, j < 32 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_f80 j hj
  have q26_fe4 : ∀ j, j < 32 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_fe4 j hj
  have a26_180 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m26]; exact a25_180
  have a26_200 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 := by rw [m26]; exact a25_200
  have a26_900 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := by rw [m26]; exact a25_900
  have a26_980 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m26]; exact a25_980
  have a26_9a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m26]; exact a25_9a0
  have a26_f80 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m26]; exact a25_f80
  have a26_fe4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m26]; exact a25_fe4
  have a26_1338 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m26]; exact a25_1338
  have a26_1358 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m26]; exact a25_1358
  have a26_1378 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m26]; exact a25_1378
  clear a25_1378 a25_1358 a25_1338 a25_fe4 a25_f80 a25_9a0 a25_980 a25_900 a25_200 a25_180 q25_fe4 q25_f80 q25_9a0 q25_980 b25_1004 b25_fa0 b25_920 b25_220 w25_9c4 w25_9c0 w25_10 g25_24 g25_18 g25_14 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0xBE4: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := p2v_sw F E26 s26 p2v_at_be4 (off' := 0xBE6) (c := 0x40)
    (by decide) (by rw [g26_2]; p2v_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, P2vR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : P2vCode n27.mem := E26.fr F fr27
  have V27 : P2vSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [rg27 (8 : Fin 32), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [rg27 (9 : Fin 32), g26_9]
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x1 := by rw [rg27 a0, g26_10]
  have g27_14 : reg n27 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg27 a4, g26_14]
  have g27_18 : reg n27 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_24 : reg n27 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg27 (24 : Fin 32), g26_24]
  have keep_kk27 : P2vKeepL B n0.mem n27.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24), (0xFE4, 0x20), (0x1004, 0x1), (0x40, 0x4)] := keep_kk26.trans K27.toL
  clear keep_kk26
  have w27_10 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K27.w32 (by decide) (by decide)).trans w26_10
  have w27_9c0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := (K27.w32 (by decide) (by decide)).trans w26_9c0
  have w27_9c4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := (K27.w32 (by decide) (by decide)).trans w26_9c4
  have b27_220 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 := (K27.b8 (by decide) (by decide)).trans b26_220
  have b27_920 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_920
  have b27_fa0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_fa0
  have b27_1004 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_1004
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 0x1 := by rw [W27, g26_10]
  have q27_980 : ∀ j, j < 32 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_980 j hj)
  have q27_9a0 : ∀ j, j < 32 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_9a0 j hj)
  have q27_f80 : ∀ j, j < 32 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_f80 j hj)
  have q27_fe4 : ∀ j, j < 32 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_fe4 j hj)
  have a27_180 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K27.acc (by decide) (by decide)).trans a26_180
  have a27_200 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 := (K27.acc (by decide) (by decide)).trans a26_200
  have a27_900 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := (K27.acc (by decide) (by decide)).trans a26_900
  have a27_980 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K27.acc (by decide) (by decide)).trans a26_980
  have a27_9a0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K27.acc (by decide) (by decide)).trans a26_9a0
  have a27_f80 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := (K27.acc (by decide) (by decide)).trans a26_f80
  have a27_fe4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := (K27.acc (by decide) (by decide)).trans a26_fe4
  have a27_1338 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := (K27.acc (by decide) (by decide)).trans a26_1338
  have a27_1358 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := (K27.acc (by decide) (by decide)).trans a26_1358
  have a27_1378 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := (K27.acc (by decide) (by decide)).trans a26_1378
  clear a26_1378 a26_1358 a26_1338 a26_fe4 a26_f80 a26_9a0 a26_980 a26_900 a26_200 a26_180 q26_fe4 q26_f80 q26_9a0 q26_980 b26_1004 b26_fa0 b26_920 b26_220 w26_9c4 w26_9c0 w26_10 g26_10 g26_24 g26_18 g26_14 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
  -- 0xBE6
  obtain ⟨n28, c28, u28⟩ := s27.block p2vZSbe6 E27.self p2vZSbe6_end
    ⟨trivial, trivial⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have s28 : St n28.mem P2V n28 0xBEA (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have rb28 : ∀ q, reg n28 q = (runBlock p2vZSbe6 (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
  have fr28 : ∀ x, P2vR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, P2vR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : P2vCode n28.mem := E27.fr F fr28
  have V28 : P2vSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by
    rw [rb28, runBlock_reg _ _ _ sp s27.zero (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (3 : Fin 32) s27.zero (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (4 : Fin 32) s27.zero (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by
    rw [rb28, runBlock_reg _ _ _ (8 : Fin 32) s27.zero (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by
    rw [rb28, runBlock_reg _ _ _ (9 : Fin 32) s27.zero (by decide), g27_9]
  have g28_14 : reg n28 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb28, runBlock_reg _ _ _ a4 s27.zero (by decide), g27_14]
  have g28_18 : reg n28 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by
    rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
  have g28_24 : reg n28 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb28, runBlock_reg _ _ _ (24 : Fin 32) s27.zero (by decide), g27_24]
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x24F := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, p2vZSbe6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_14, g27_18, g27_24, s27.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk28 : P2vKeepL B n0.mem n28.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24), (0xFE4, 0x20), (0x1004, 0x1), (0x40, 0x4)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_10 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m28]; exact w27_10
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 0x1 := by rw [m28]; exact w27_40
  have w28_9c0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m28]; exact w27_9c0
  have w28_9c4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m28]; exact w27_9c4
  have b28_220 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 := by rw [m28]; exact b27_220
  have b28_920 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m28]; exact b27_920
  have b28_fa0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m28]; exact b27_fa0
  have b28_1004 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m28]; exact b27_1004
  have q28_980 : ∀ j, j < 32 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_980 j hj
  have q28_9a0 : ∀ j, j < 32 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_9a0 j hj
  have q28_f80 : ∀ j, j < 32 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_f80 j hj
  have q28_fe4 : ∀ j, j < 32 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_fe4 j hj
  have a28_180 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m28]; exact a27_180
  have a28_200 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 := by rw [m28]; exact a27_200
  have a28_900 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := by rw [m28]; exact a27_900
  have a28_980 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m28]; exact a27_980
  have a28_9a0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m28]; exact a27_9a0
  have a28_f80 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m28]; exact a27_f80
  have a28_fe4 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m28]; exact a27_fe4
  have a28_1338 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m28]; exact a27_1338
  have a28_1358 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m28]; exact a27_1358
  have a28_1378 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m28]; exact a27_1378
  clear a27_1378 a27_1358 a27_1338 a27_fe4 a27_f80 a27_9a0 a27_980 a27_900 a27_200 a27_180 q27_fe4 q27_f80 q27_9a0 q27_980 w27_40 b27_1004 b27_fa0 b27_920 b27_220 w27_9c4 w27_9c0 w27_10 g27_24 g27_18 g27_14 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
  -- 0xBEA: branch, not taken
  obtain ⟨n29, d29, u29⟩ := s28.notTaken E28.self 0xBEE p2v_at_bea
    (by decide) (by rw [g28_10, s28.zero]; decide)
  have s29 : St n29.mem P2V n29 0xBEE (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, P2vR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, P2vR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : P2vCode n29.mem := E28.fr F fr29
  have V29 : P2vSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 (img% p256R2Address) := by rw [u29.regs, g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = BitVec.ofNat 32 (img% p256ModulusAddress) := by rw [u29.regs, g28_9]
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x24F := by rw [u29.regs, g28_10]
  have g29_14 : reg n29 a4 = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u29.regs, g28_14]
  have g29_18 : reg n29 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1378 := by rw [u29.regs, g28_18]
  have g29_24 : reg n29 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_24]
  have keep_kk29 : P2vKeepL B n0.mem n29.mem [(0x1338, 0x60), (0x980, 0x20), (0x9C0, 0x4), (0x9C4, 0x4), (0x9A0, 0x20), (0x10, 0x4), (0xF80, 0x20), (0xFA0, 0x1), (0x900, 0x20), (0x920, 0x1), (0x200, 0x24), (0xFE4, 0x20), (0x1004, 0x1), (0x40, 0x4)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_10 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m29]; exact w28_10
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 0x1 := by rw [m29]; exact w28_40
  have w29_9c0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_9c0
  have w29_9c4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C4) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_9c4
  have b29_220 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = 0 := by rw [m29]; exact b28_220
  have b29_920 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m29]; exact b28_920
  have b29_fa0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m29]; exact b28_fa0
  have b29_1004 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m29]; exact b28_1004
  have q29_980 : ∀ j, j < 32 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_980 j hj
  have q29_9a0 : ∀ j, j < 32 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_9a0 j hj
  have q29_f80 : ∀ j, j < 32 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF80 + j)) = M0 ((BitVec.ofNat 32 (img% p256ModulusAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_f80 j hj
  have q29_fe4 : ∀ j, j < 32 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256R2Address)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_fe4 j hj
  have a29_180 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m29]; exact a28_180
  have a29_200 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = 0 := by rw [m29]; exact a28_200
  have a29_900 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = Z := by rw [m29]; exact a28_900
  have a29_980 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m29]; exact a28_980
  have a29_9a0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m29]; exact a28_9a0
  have a29_f80 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by rw [m29]; exact a28_f80
  have a29_fe4 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 := by rw [m29]; exact a28_fe4
  have a29_1338 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X := by rw [m29]; exact a28_1338
  have a29_1358 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y := by rw [m29]; exact a28_1358
  have a29_1378 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1378) 8 = Z := by rw [m29]; exact a28_1378
  clear a28_1378 a28_1358 a28_1338 a28_fe4 a28_f80 a28_9a0 a28_980 a28_900 a28_200 a28_180 q28_fe4 q28_f80 q28_9a0 q28_980 b28_1004 b28_fa0 b28_920 b28_220 w28_9c4 w28_9c0 w28_40 w28_10 g28_10 g28_24 g28_18 g28_14 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
  exact .inr ⟨n29, t29, s29, E29, V29, fR29, g29_2, g29_3, g29_4, g29_10, g29_14, g29_24, w29_10, w29_40, b29_220, b29_920, b29_fa0, b29_1004, q29_980, q29_9a0, q29_f80, q29_fe4, a29_180, a29_200, a29_900, a29_980, a29_9a0, a29_f80, a29_fe4, a29_1338, a29_1358, a29_1378, keep_kk29.mono (by decide)⟩

end C3.RV32.P2v
