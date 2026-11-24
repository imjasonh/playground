import C3BootProofs.Proofs.P2vEcPt

/-!
# `p256VerifyPrehash`: `u₁` and `u₂`, and the pairs of the linear combination

From 0x690 to the table loop at 0x754: `u₁ = z·s⁻¹` and `u₂ = r·s⁻¹` with the scalar field's `mul`, and the pairs `(G, u₁)` and `(Q, u₂)` copied to offset 0xFE4.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vEcD690 : List BInstr :=
  [.aluImm .add a0 sp 0x1E0, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .aluImm .add a2 x0 0x20]
theorem p2vEcD690_end : blockEnd p256VerifyPrehashCode 0x690 p2vEcD690 = some 0x69E := by
  simp only [p2vEcD690]
  rw [blockEnd, p2v_at_690]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_692]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_696]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_69a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcD6a6 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x1E1, .aluImm .add a1 sp 0x1C0, .aluImm .add a2 sp 0x1E0]
theorem p2vEcD6a6_end : blockEnd p256VerifyPrehashCode 0x6A6 p2vEcD6a6 = some 0x6B2 := by
  simp only [p2vEcD6a6]
  rw [blockEnd, p2v_at_6a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6ae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6b0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcD6ba : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x4E1, .aluImm .add a1 sp 0x180, .aluImm .add a2 sp 0x1E0]
theorem p2vEcD6ba_end : blockEnd p256VerifyPrehashCode 0x6BA p2vEcD6ba = some 0x6C6 := by
  simp only [p2vEcD6ba]
  rw [blockEnd, p2v_at_6ba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6c2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6c4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcD6ce : List BInstr :=
  [.lui (23 : Fin 32) 0x3FCC4000, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x500, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a2 x0 0x60, .alu .add a1 x0 (23 : Fin 32)]
theorem p2vEcD6ce_end : blockEnd p256VerifyPrehashCode 0x6CE p2vEcD6ce = some 0x6E4 := by
  simp only [p2vEcD6ce]
  rw [blockEnd, p2v_at_6ce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6d2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6d6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6da]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6de]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6e2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcD6ec : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x120, .aluImm .add a2 x0 0x60]
theorem p2vEcD6ec_end : blockEnd p256VerifyPrehashCode 0x6EC p2vEcD6ec = some 0x6FA := by
  simp only [p2vEcD6ec]
  rw [blockEnd, p2v_at_6ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6f0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_6f6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcD702 : List BInstr :=
  [.aluImm .add a0 sp 0x200, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .aluImm .add a2 x0 0x80]
theorem p2vEcD702_end : blockEnd p256VerifyPrehashCode 0x702 p2vEcD702 = some 0x710 := by
  simp only [p2vEcD702]
  rw [blockEnd, p2v_at_702]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_704]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_708]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_70c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcD718 : List BInstr :=
  [.aluImm .add a0 sp 0x280, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x80]
theorem p2vEcD718_end : blockEnd p256VerifyPrehashCode 0x718 p2vEcD718 = some 0x726 := by
  simp only [p2vEcD718]
  rw [blockEnd, p2v_at_718]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_71a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_71e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_722]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcD72e : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x7E5, .aluImm .add a1 sp 0x200, .aluImm .add a2 x0 0x100]
theorem p2vEcD72e_end : blockEnd p256VerifyPrehashCode 0x72E p2vEcD72e = some 0x73C := by
  simp only [p2vEcD72e]
  rw [blockEnd, p2v_at_72e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_732]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_736]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_738]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcD744 : List BInstr :=
  [.aluImm .add (19 : Fin 32) x0 0x0, .aluImm .add (20 : Fin 32) x0 0x2, .aluImm .add (21 : Fin 32) x0 0x300, .aluImm .add (22 : Fin 32) sp 0x300, .aluImm .add a0 sp 0x7FF]
theorem p2vEcD744_end : blockEnd p256VerifyPrehashCode 0x744 p2vEcD744 = some 0x754 := by
  simp only [p2vEcD744]
  rw [blockEnd, p2v_at_744]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_746]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_748]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_74c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_750]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_ecd {B dlo dhi rem : Word} {fs gs ds es : BitVec 8} {wv : Nat} {qx qy qz rv sv zv fv gv dv ev : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x690 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4)
    (g0_19 : reg n0 (19 : Fin 32) = dlo)
    (g0_21 : reg n0 (21 : Fin 32) = dhi)
    (g0_22 : reg n0 (22 : Fin 32) = BitVec.ofNat 32 0x1)
    (g0_23 : reg n0 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4)
    (g0_24 : reg n0 (24 : Fin 32) = rem)
    (g0_26 : reg n0 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920)
    (g0_27 : reg n0 (27 : Fin 32) = BitVec.ofNat 32 0x7)
    (a0_120 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx)
    (a0_140 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy)
    (a0_160 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz)
    (a0_180 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv)
    (a0_1a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv)
    (a0_1c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv)
    (a0_200 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv)
    (a0_900 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv)
    (a0_fe4 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv)
    (b0_220 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs)
    (b0_920 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs)
    (b0_9a0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es)
    (b0_1004 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds)
    (a0_980 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = wv)
    (RS : P2vRoSep B)
    (PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode)
    (WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode) :
    (¬ (True) ∧ P2vRet B v n0 0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x754 (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 ∧
        reg n' (19 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x2 ∧
        reg n' (21 : Fin 32) = BitVec.ofNat 32 0x300 ∧
        reg n' (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 ∧
        reg n' (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) ∧
        reg n' (24 : Fin 32) = rem ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        reg n' (27 : Fin 32) = BitVec.ofNat 32 0x7 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x200 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = psmVal ((zv) * (wv)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = psmVal ((rv) * (wv)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = psmVal ((zv) * (wv)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1064) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1084) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10A4) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = psmVal ((rv) * (wv)) ∧
        P2vKeepL B n0.mem n'.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60), (0xC80, 0x60), (0x200, 0x80), (0x280, 0x80), (0xFE4, 0x100)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x690
  obtain ⟨n1, c1, u1⟩ := s0.block p2vEcD690 E0.self p2vEcD690_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem P2V n1 0x69E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock p2vEcD690 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_18 : reg n1 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = dlo := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = dhi := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = rem := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_26 : reg n1 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1E0 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vEcD690, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_21, g0_22, g0_23, g0_24, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vEcD690, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_21, g0_22, g0_23, g0_24, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vEcD690, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_21, g0_22, g0_23, g0_24, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have b1_220 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m1]; exact b0_220
  have b1_920 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m1]; exact b0_920
  have b1_9a0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m1]; exact b0_9a0
  have b1_1004 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m1]; exact b0_1004
  have a1_120 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m1]; exact a0_120
  have a1_140 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m1]; exact a0_140
  have a1_160 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m1]; exact a0_160
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m1]; exact a0_180
  have a1_1a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m1]; exact a0_1a0
  have a1_1c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m1]; exact a0_1c0
  have a1_200 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m1]; exact a0_200
  have a1_900 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m1]; exact a0_900
  have a1_980 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = wv := by rw [m1]; exact a0_980
  have a1_fe4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m1]; exact a0_fe4
  -- 0x69E: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := p2v_mc (c := 0x1E0) (d := 0x980) (N := 0x20) F E1 s1 p2v_at_69e p2v_at_6a2
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
  have g2_18 : reg n2 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P2.regs (18 : Fin 32) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = dlo := by rw [P2.regs (19 : Fin 32) (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = dhi := by rw [P2.regs (21 : Fin 32) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P2.regs (22 : Fin 32) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [P2.regs (23 : Fin 32) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = rem := by rw [P2.regs (24 : Fin 32) (by decide), g1_24]
  have g2_26 : reg n2 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P2.regs (26 : Fin 32) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P2.regs (27 : Fin 32) (by decide), g1_27]
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0x1E0, 0x20)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have b2_220 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K2.b8 (by decide) (by decide)).trans b1_220
  have b2_920 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K2.b8 (by decide) (by decide)).trans b1_920
  have b2_9a0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K2.b8 (by decide) (by decide)).trans b1_9a0
  have b2_1004 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K2.b8 (by decide) (by decide)).trans b1_1004
  have a2_120 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K2.acc (by decide) (by decide)).trans a1_120
  have a2_140 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K2.acc (by decide) (by decide)).trans a1_140
  have a2_160 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K2.acc (by decide) (by decide)).trans a1_160
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_180
  have a2_1a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K2.acc (by decide) (by decide)).trans a1_1a0
  have a2_1c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K2.acc (by decide) (by decide)).trans a1_1c0
  have a2_200 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K2.acc (by decide) (by decide)).trans a1_200
  have a2_900 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K2.acc (by decide) (by decide)).trans a1_900
  have a2_980 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = wv := (K2.acc (by decide) (by decide)).trans a1_980
  have a2_fe4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K2.acc (by decide) (by decide)).trans a1_fe4
  have a2_1e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (accV_S 8 fun q hq => by
    rw [show 0x1E0 + q = 0x1E0 + (0x0 + q) by omega, X2 (0x0 + q) (by omega),
      show 0x980 + (0x0 + q) = 0x980 + q by omega]).trans a1_980
  clear a1_fe4 a1_980 a1_900 a1_200 a1_1c0 a1_1a0 a1_180 a1_160 a1_140 a1_120 b1_1004 b1_9a0 b1_920 b1_220 g1_12 g1_11 g1_10 g1_27 g1_26 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x6A6
  obtain ⟨n3, c3, u3⟩ := s2.block p2vEcD6a6 E2.self p2vEcD6a6_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem P2V n3 0x6B2 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock p2vEcD6a6 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_18 : reg n3 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = dlo := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = dhi := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = rem := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x9E0 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vEcD6a6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_21, g2_22, g2_23, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_11 : reg n3 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1C0 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vEcD6a6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_21, g2_22, g2_23, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_12 : reg n3 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1E0 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vEcD6a6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_21, g2_22, g2_23, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0x1E0, 0x20)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have b3_220 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m3]; exact b2_220
  have b3_920 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m3]; exact b2_920
  have b3_9a0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m3]; exact b2_9a0
  have b3_1004 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m3]; exact b2_1004
  have a3_120 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m3]; exact a2_120
  have a3_140 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m3]; exact a2_140
  have a3_160 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m3]; exact a2_160
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m3]; exact a2_180
  have a3_1a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m3]; exact a2_1a0
  have a3_1c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m3]; exact a2_1c0
  have a3_1e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m3]; exact a2_1e0
  have a3_200 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m3]; exact a2_200
  have a3_900 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m3]; exact a2_900
  have a3_980 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = wv := by rw [m3]; exact a2_980
  have a3_fe4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m3]; exact a2_fe4
  clear a2_1e0 a2_fe4 a2_980 a2_900 a2_200 a2_1c0 a2_1a0 a2_180 a2_160 a2_140 a2_120 b2_1004 b2_9a0 b2_920 b2_220 g2_27 g2_26 g2_24 g2_23 g2_22 g2_21 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0x6B2: p2v_psmF
  obtain ⟨n4, c4, s4, sp4, rk4, A4, K4, fr4⟩ := p2v_psmF (co := 0x9E0) (ca := 0x1C0) (cb := 0x1E0)
    F E3 (codeIn_p2v F fR3 PM0 (by decide) (by decide)) (codeIn_p2v F fR3 WM0 (by decide) (by decide))
    s3 p2v_at_6b2 p2v_at_6b6 (by decide) (by decide) g3_2
    g3_10 g3_11 g3_12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [a3_1c0, a3_1e0] at A4
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.keepL K4 (by decide)
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk4 (3 : Fin 32) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk4 (4 : Fin 32) (by decide), g3_4]
  have g4_18 : reg n4 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [rk4 (18 : Fin 32) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = dlo := by rw [rk4 (19 : Fin 32) (by decide), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = dhi := by rw [rk4 (21 : Fin 32) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk4 (22 : Fin 32) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk4 (23 : Fin 32) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = rem := by rw [rk4 (24 : Fin 32) (by decide), g3_24]
  have g4_26 : reg n4 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk4 (26 : Fin 32) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk4 (27 : Fin 32) (by decide), g3_27]
  have g4_2 : reg n4 sp = B + 0x21A0 := sp4
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0x1E0, 0x20), (0x9E0, 0x20)] := keep_kk3.trans K4
  clear keep_kk3
  have b4_220 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K4.b8 (by decide) (by decide)).trans b3_220
  have b4_920 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K4.b8 (by decide) (by decide)).trans b3_920
  have b4_9a0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K4.b8 (by decide) (by decide)).trans b3_9a0
  have b4_1004 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K4.b8 (by decide) (by decide)).trans b3_1004
  have a4_120 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K4.acc (by decide) (by decide)).trans a3_120
  have a4_140 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K4.acc (by decide) (by decide)).trans a3_140
  have a4_160 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K4.acc (by decide) (by decide)).trans a3_160
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K4.acc (by decide) (by decide)).trans a3_180
  have a4_1a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K4.acc (by decide) (by decide)).trans a3_1a0
  have a4_1c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K4.acc (by decide) (by decide)).trans a3_1c0
  have a4_1e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K4.acc (by decide) (by decide)).trans a3_1e0
  have a4_200 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K4.acc (by decide) (by decide)).trans a3_200
  have a4_900 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K4.acc (by decide) (by decide)).trans a3_900
  have a4_980 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = wv := (K4.acc (by decide) (by decide)).trans a3_980
  have a4_fe4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K4.acc (by decide) (by decide)).trans a3_fe4
  have a4_9e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := A4
  clear a3_fe4 a3_980 a3_900 a3_200 a3_1e0 a3_1c0 a3_1a0 a3_180 a3_160 a3_140 a3_120 b3_1004 b3_9a0 b3_920 b3_220 g3_12 g3_11 g3_10 g3_27 g3_26 g3_24 g3_23 g3_22 g3_21 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0x6BA
  obtain ⟨n5, c5, u5⟩ := s4.block p2vEcD6ba E4.self p2vEcD6ba_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem P2V n5 0x6C6 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock p2vEcD6ba (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_18 : reg n5 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = dlo := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = dhi := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = rem := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0xCE0 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vEcD6ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_18, g4_19, g4_21, g4_22, g4_23, g4_24, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_11 : reg n5 a1 = B + 0x21A0 + BitVec.ofNat 32 0x180 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vEcD6ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_18, g4_19, g4_21, g4_22, g4_23, g4_24, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_12 : reg n5 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1E0 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vEcD6ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_18, g4_19, g4_21, g4_22, g4_23, g4_24, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0x1E0, 0x20), (0x9E0, 0x20)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have b5_220 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m5]; exact b4_220
  have b5_920 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m5]; exact b4_920
  have b5_9a0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m5]; exact b4_9a0
  have b5_1004 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m5]; exact b4_1004
  have a5_120 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m5]; exact a4_120
  have a5_140 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m5]; exact a4_140
  have a5_160 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m5]; exact a4_160
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m5]; exact a4_180
  have a5_1a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m5]; exact a4_1a0
  have a5_1c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m5]; exact a4_1c0
  have a5_1e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m5]; exact a4_1e0
  have a5_200 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m5]; exact a4_200
  have a5_900 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m5]; exact a4_900
  have a5_980 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = wv := by rw [m5]; exact a4_980
  have a5_9e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m5]; exact a4_9e0
  have a5_fe4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m5]; exact a4_fe4
  clear a4_9e0 a4_fe4 a4_980 a4_900 a4_200 a4_1e0 a4_1c0 a4_1a0 a4_180 a4_160 a4_140 a4_120 b4_1004 b4_9a0 b4_920 b4_220 g4_2 g4_27 g4_26 g4_24 g4_23 g4_22 g4_21 g4_19 g4_18 g4_4 g4_3 V4 E4 fR4 t4 fr4 K4 A4 rk4 sp4 s4 c4
  -- 0x6C6: p2v_psmF
  obtain ⟨n6, c6, s6, sp6, rk6, A6, K6, fr6⟩ := p2v_psmF (co := 0xCE0) (ca := 0x180) (cb := 0x1E0)
    F E5 (codeIn_p2v F fR5 PM0 (by decide) (by decide)) (codeIn_p2v F fR5 WM0 (by decide) (by decide))
    s5 p2v_at_6c6 p2v_at_6ca (by decide) (by decide) g5_2
    g5_10 g5_11 g5_12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [a5_180, a5_1e0] at A6
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.keepL K6 (by decide)
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk6 (3 : Fin 32) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk6 (4 : Fin 32) (by decide), g5_4]
  have g6_18 : reg n6 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [rk6 (18 : Fin 32) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = dlo := by rw [rk6 (19 : Fin 32) (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = dhi := by rw [rk6 (21 : Fin 32) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk6 (22 : Fin 32) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4 := by rw [rk6 (23 : Fin 32) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = rem := by rw [rk6 (24 : Fin 32) (by decide), g5_24]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk6 (26 : Fin 32) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk6 (27 : Fin 32) (by decide), g5_27]
  have g6_2 : reg n6 sp = B + 0x21A0 := sp6
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20)] := keep_kk5.trans K6
  clear keep_kk5
  have b6_220 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K6.b8 (by decide) (by decide)).trans b5_220
  have b6_920 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K6.b8 (by decide) (by decide)).trans b5_920
  have b6_9a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := (K6.b8 (by decide) (by decide)).trans b5_9a0
  have b6_1004 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K6.b8 (by decide) (by decide)).trans b5_1004
  have a6_120 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K6.acc (by decide) (by decide)).trans a5_120
  have a6_140 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K6.acc (by decide) (by decide)).trans a5_140
  have a6_160 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K6.acc (by decide) (by decide)).trans a5_160
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K6.acc (by decide) (by decide)).trans a5_180
  have a6_1a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K6.acc (by decide) (by decide)).trans a5_1a0
  have a6_1c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K6.acc (by decide) (by decide)).trans a5_1c0
  have a6_1e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K6.acc (by decide) (by decide)).trans a5_1e0
  have a6_200 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K6.acc (by decide) (by decide)).trans a5_200
  have a6_900 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K6.acc (by decide) (by decide)).trans a5_900
  have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = wv := (K6.acc (by decide) (by decide)).trans a5_980
  have a6_9e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K6.acc (by decide) (by decide)).trans a5_9e0
  have a6_fe4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K6.acc (by decide) (by decide)).trans a5_fe4
  have a6_ce0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := A6
  clear a5_fe4 a5_9e0 a5_980 a5_900 a5_200 a5_1e0 a5_1c0 a5_1a0 a5_180 a5_160 a5_140 a5_120 b5_1004 b5_9a0 b5_920 b5_220 g5_12 g5_11 g5_10 g5_27 g5_26 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x6CE
  obtain ⟨n7, c7, u7⟩ := s6.block p2vEcD6ce E6.self p2vEcD6ce_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem P2V n7 0x6E4 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock p2vEcD6ce (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_18 : reg n7 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = dlo := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = dhi := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_24 : reg n7 (24 : Fin 32) = rem := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcD6ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_11 : reg n7 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcD6ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_12 : reg n7 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcD6ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_23 : reg n7 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcD6ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have b7_220 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m7]; exact b6_220
  have b7_920 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m7]; exact b6_920
  have b7_9a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) = es := by rw [m7]; exact b6_9a0
  have b7_1004 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m7]; exact b6_1004
  have a7_120 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m7]; exact a6_120
  have a7_140 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m7]; exact a6_140
  have a7_160 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m7]; exact a6_160
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m7]; exact a6_180
  have a7_1a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m7]; exact a6_1a0
  have a7_1c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m7]; exact a6_1c0
  have a7_1e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m7]; exact a6_1e0
  have a7_200 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m7]; exact a6_200
  have a7_900 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m7]; exact a6_900
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = wv := by rw [m7]; exact a6_980
  have a7_9e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m7]; exact a6_9e0
  have a7_ce0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m7]; exact a6_ce0
  have a7_fe4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m7]; exact a6_fe4
  clear a6_ce0 a6_fe4 a6_9e0 a6_980 a6_900 a6_200 a6_1e0 a6_1c0 a6_1a0 a6_180 a6_160 a6_140 a6_120 b6_1004 b6_9a0 b6_920 b6_220 g6_2 g6_27 g6_26 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_4 g6_3 V6 E6 fR6 t6 fr6 K6 A6 rk6 sp6 s6 c6
  -- 0x6E4: memcpy from outside the stack
  obtain ⟨n8, P8, K8, X8⟩ := p2v_mcRo2 (c := 0x980) (N := 0x60) F RS E7 s7 p2v_at_6e4 p2v_at_6e8
    (by decide) (by decide) g7_2 g7_10 g7_11 g7_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s8 := P8.st
  have fr8 := P8.fr
  have t8 : Steps n0 n8 := t7.trans P8.steps
  have fR8 : ∀ x, P2vR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : P2vCode n8.mem := E7.fr F fr8
  have V8 : P2vSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [P8.regs sp (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P8.regs (3 : Fin 32) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P8.regs (4 : Fin 32) (by decide), g7_4]
  have g8_18 : reg n8 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P8.regs (18 : Fin 32) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = dlo := by rw [P8.regs (19 : Fin 32) (by decide), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = dhi := by rw [P8.regs (21 : Fin 32) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P8.regs (22 : Fin 32) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P8.regs (23 : Fin 32) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = rem := by rw [P8.regs (24 : Fin 32) (by decide), g7_24]
  have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P8.regs (26 : Fin 32) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P8.regs (27 : Fin 32) (by decide), g7_27]
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have b8_220 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K8.b8 (by decide) (by decide)).trans b7_220
  have b8_920 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K8.b8 (by decide) (by decide)).trans b7_920
  have b8_1004 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K8.b8 (by decide) (by decide)).trans b7_1004
  have a8_120 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K8.acc (by decide) (by decide)).trans a7_120
  have a8_140 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K8.acc (by decide) (by decide)).trans a7_140
  have a8_160 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K8.acc (by decide) (by decide)).trans a7_160
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K8.acc (by decide) (by decide)).trans a7_180
  have a8_1a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K8.acc (by decide) (by decide)).trans a7_1a0
  have a8_1c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K8.acc (by decide) (by decide)).trans a7_1c0
  have a8_1e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K8.acc (by decide) (by decide)).trans a7_1e0
  have a8_200 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K8.acc (by decide) (by decide)).trans a7_200
  have a8_900 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K8.acc (by decide) (by decide)).trans a7_900
  have a8_9e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K8.acc (by decide) (by decide)).trans a7_9e0
  have a8_ce0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := (K8.acc (by decide) (by decide)).trans a7_ce0
  have a8_fe4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K8.acc (by decide) (by decide)).trans a7_fe4
  have q8_980 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X8 j hj).trans (fR7 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := acc_of_frame_at (d := 0x0) q8_980 (by decide)
  have a8_9a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := acc_of_frame_at (d := 0x20) q8_980 (by decide)
  have a8_9c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := acc_of_frame_at (d := 0x40) q8_980 (by decide)
  clear a7_fe4 a7_ce0 a7_9e0 a7_980 a7_900 a7_200 a7_1e0 a7_1c0 a7_1a0 a7_180 a7_160 a7_140 a7_120 b7_1004 b7_9a0 b7_920 b7_220 g7_23 g7_12 g7_11 g7_10 g7_27 g7_26 g7_24 g7_22 g7_21 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x6EC
  obtain ⟨n9, c9, u9⟩ := s8.block p2vEcD6ec E8.self p2vEcD6ec_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem P2V n9 0x6FA (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock p2vEcD6ec (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_18 : reg n9 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = dlo := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = dhi := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = rem := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vEcD6ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_18, g8_19, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_11 : reg n9 a1 = B + 0x21A0 + BitVec.ofNat 32 0x120 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vEcD6ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_18, g8_19, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_12 : reg n9 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vEcD6ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_18, g8_19, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have b9_220 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m9]; exact b8_220
  have b9_920 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m9]; exact b8_920
  have b9_1004 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m9]; exact b8_1004
  have q9_980 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_980 j hj
  have a9_120 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m9]; exact a8_120
  have a9_140 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m9]; exact a8_140
  have a9_160 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m9]; exact a8_160
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m9]; exact a8_180
  have a9_1a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m9]; exact a8_1a0
  have a9_1c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m9]; exact a8_1c0
  have a9_1e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m9]; exact a8_1e0
  have a9_200 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m9]; exact a8_200
  have a9_900 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m9]; exact a8_900
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m9]; exact a8_980
  have a9_9a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m9]; exact a8_9a0
  have a9_9c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m9]; exact a8_9c0
  have a9_9e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m9]; exact a8_9e0
  have a9_ce0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m9]; exact a8_ce0
  have a9_fe4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m9]; exact a8_fe4
  clear a8_9c0 a8_9a0 a8_980 q8_980 a8_fe4 a8_ce0 a8_9e0 a8_900 a8_200 a8_1e0 a8_1c0 a8_1a0 a8_180 a8_160 a8_140 a8_120 b8_1004 b8_920 b8_220 g8_27 g8_26 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 s8 X8 K8 P8
  -- 0x6FA: memcpy
  obtain ⟨n10, P10, K10, X10⟩ := p2v_mc (c := 0xC80) (d := 0x120) (N := 0x60) F E9 s9 p2v_at_6fa p2v_at_6fe
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
  have g10_18 : reg n10 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P10.regs (18 : Fin 32) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = dlo := by rw [P10.regs (19 : Fin 32) (by decide), g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = dhi := by rw [P10.regs (21 : Fin 32) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P10.regs (22 : Fin 32) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P10.regs (23 : Fin 32) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = rem := by rw [P10.regs (24 : Fin 32) (by decide), g9_24]
  have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P10.regs (26 : Fin 32) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P10.regs (27 : Fin 32) (by decide), g9_27]
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60), (0xC80, 0x60)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have b10_220 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := (K10.b8 (by decide) (by decide)).trans b9_220
  have b10_920 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K10.b8 (by decide) (by decide)).trans b9_920
  have b10_1004 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K10.b8 (by decide) (by decide)).trans b9_1004
  have q10_980 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_980 j hj)
  have a10_120 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K10.acc (by decide) (by decide)).trans a9_120
  have a10_140 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K10.acc (by decide) (by decide)).trans a9_140
  have a10_160 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K10.acc (by decide) (by decide)).trans a9_160
  have a10_180 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K10.acc (by decide) (by decide)).trans a9_180
  have a10_1a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K10.acc (by decide) (by decide)).trans a9_1a0
  have a10_1c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K10.acc (by decide) (by decide)).trans a9_1c0
  have a10_1e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K10.acc (by decide) (by decide)).trans a9_1e0
  have a10_200 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := (K10.acc (by decide) (by decide)).trans a9_200
  have a10_900 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K10.acc (by decide) (by decide)).trans a9_900
  have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K10.acc (by decide) (by decide)).trans a9_980
  have a10_9a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K10.acc (by decide) (by decide)).trans a9_9a0
  have a10_9c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K10.acc (by decide) (by decide)).trans a9_9c0
  have a10_9e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K10.acc (by decide) (by decide)).trans a9_9e0
  have a10_ce0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := (K10.acc (by decide) (by decide)).trans a9_ce0
  have a10_fe4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K10.acc (by decide) (by decide)).trans a9_fe4
  have a10_c80 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := (accV_S 8 fun q hq => by
    rw [show 0xC80 + q = 0xC80 + (0x0 + q) by omega, X10 (0x0 + q) (by omega),
      show 0x120 + (0x0 + q) = 0x120 + q by omega]).trans a9_120
  have a10_ca0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := (accV_S 8 fun q hq => by
    rw [show 0xCA0 + q = 0xC80 + (0x20 + q) by omega, X10 (0x20 + q) (by omega),
      show 0x120 + (0x20 + q) = 0x140 + q by omega]).trans a9_140
  have a10_cc0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := (accV_S 8 fun q hq => by
    rw [show 0xCC0 + q = 0xC80 + (0x40 + q) by omega, X10 (0x40 + q) (by omega),
      show 0x120 + (0x40 + q) = 0x160 + q by omega]).trans a9_160
  clear a9_fe4 a9_ce0 a9_9e0 a9_9c0 a9_9a0 a9_980 a9_900 a9_200 a9_1e0 a9_1c0 a9_1a0 a9_180 a9_160 a9_140 a9_120 q9_980 b9_1004 b9_920 b9_220 g9_12 g9_11 g9_10 g9_27 g9_26 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x702
  obtain ⟨n11, c11, u11⟩ := s10.block p2vEcD702 E10.self p2vEcD702_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem P2V n11 0x710 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock p2vEcD702 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
  have g11_18 : reg n11 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = dlo := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = dhi := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = rem := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_10 : reg n11 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vEcD702, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_18, g10_19, g10_21, g10_22, g10_23, g10_24, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g11_11 : reg n11 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vEcD702, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_18, g10_19, g10_21, g10_22, g10_23, g10_24, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g11_12 : reg n11 a2 = BitVec.ofNat 32 0x80 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vEcD702, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_18, g10_19, g10_21, g10_22, g10_23, g10_24, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60), (0xC80, 0x60)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have b11_220 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) = gs := by rw [m11]; exact b10_220
  have b11_920 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m11]; exact b10_920
  have b11_1004 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m11]; exact b10_1004
  have q11_980 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_980 j hj
  have a11_120 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m11]; exact a10_120
  have a11_140 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m11]; exact a10_140
  have a11_160 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m11]; exact a10_160
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m11]; exact a10_180
  have a11_1a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m11]; exact a10_1a0
  have a11_1c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m11]; exact a10_1c0
  have a11_1e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m11]; exact a10_1e0
  have a11_200 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = gv := by rw [m11]; exact a10_200
  have a11_900 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m11]; exact a10_900
  have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m11]; exact a10_980
  have a11_9a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m11]; exact a10_9a0
  have a11_9c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m11]; exact a10_9c0
  have a11_9e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m11]; exact a10_9e0
  have a11_c80 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := by rw [m11]; exact a10_c80
  have a11_ca0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := by rw [m11]; exact a10_ca0
  have a11_cc0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := by rw [m11]; exact a10_cc0
  have a11_ce0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m11]; exact a10_ce0
  have a11_fe4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m11]; exact a10_fe4
  clear a10_cc0 a10_ca0 a10_c80 a10_fe4 a10_ce0 a10_9e0 a10_9c0 a10_9a0 a10_980 a10_900 a10_200 a10_1e0 a10_1c0 a10_1a0 a10_180 a10_160 a10_140 a10_120 q10_980 b10_1004 b10_920 b10_220 g10_27 g10_26 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 s10 X10 K10 P10
  -- 0x710: memcpy
  obtain ⟨n12, P12, K12, X12⟩ := p2v_mc (c := 0x200) (d := 0x980) (N := 0x80) F E11 s11 p2v_at_710 p2v_at_714
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
  have g12_18 : reg n12 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P12.regs (18 : Fin 32) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = dlo := by rw [P12.regs (19 : Fin 32) (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = dhi := by rw [P12.regs (21 : Fin 32) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P12.regs (22 : Fin 32) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P12.regs (23 : Fin 32) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = rem := by rw [P12.regs (24 : Fin 32) (by decide), g11_24]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P12.regs (26 : Fin 32) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P12.regs (27 : Fin 32) (by decide), g11_27]
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60), (0xC80, 0x60), (0x200, 0x80)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have b12_920 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K12.b8 (by decide) (by decide)).trans b11_920
  have b12_1004 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K12.b8 (by decide) (by decide)).trans b11_1004
  have q12_980 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K12.range (by decide) (by decide) j hj).trans (q11_980 j hj)
  have a12_120 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K12.acc (by decide) (by decide)).trans a11_120
  have a12_140 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K12.acc (by decide) (by decide)).trans a11_140
  have a12_160 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K12.acc (by decide) (by decide)).trans a11_160
  have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K12.acc (by decide) (by decide)).trans a11_180
  have a12_1a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K12.acc (by decide) (by decide)).trans a11_1a0
  have a12_1c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K12.acc (by decide) (by decide)).trans a11_1c0
  have a12_1e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K12.acc (by decide) (by decide)).trans a11_1e0
  have a12_900 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K12.acc (by decide) (by decide)).trans a11_900
  have a12_980 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K12.acc (by decide) (by decide)).trans a11_980
  have a12_9a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K12.acc (by decide) (by decide)).trans a11_9a0
  have a12_9c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K12.acc (by decide) (by decide)).trans a11_9c0
  have a12_9e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K12.acc (by decide) (by decide)).trans a11_9e0
  have a12_c80 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := (K12.acc (by decide) (by decide)).trans a11_c80
  have a12_ca0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := (K12.acc (by decide) (by decide)).trans a11_ca0
  have a12_cc0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := (K12.acc (by decide) (by decide)).trans a11_cc0
  have a12_ce0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := (K12.acc (by decide) (by decide)).trans a11_ce0
  have a12_fe4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K12.acc (by decide) (by decide)).trans a11_fe4
  have a12_200 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (accV_S 8 fun q hq => by
    rw [show 0x200 + q = 0x200 + (0x0 + q) by omega, X12 (0x0 + q) (by omega),
      show 0x980 + (0x0 + q) = 0x980 + q by omega]).trans a11_980
  have a12_220 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (accV_S 8 fun q hq => by
    rw [show 0x220 + q = 0x200 + (0x20 + q) by omega, X12 (0x20 + q) (by omega),
      show 0x980 + (0x20 + q) = 0x9A0 + q by omega]).trans a11_9a0
  have a12_240 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (accV_S 8 fun q hq => by
    rw [show 0x240 + q = 0x200 + (0x40 + q) by omega, X12 (0x40 + q) (by omega),
      show 0x980 + (0x40 + q) = 0x9C0 + q by omega]).trans a11_9c0
  have a12_260 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = psmVal ((zv) * (wv)) := (accV_S 8 fun q hq => by
    rw [show 0x260 + q = 0x200 + (0x60 + q) by omega, X12 (0x60 + q) (by omega),
      show 0x980 + (0x60 + q) = 0x9E0 + q by omega]).trans a11_9e0
  have q12_200 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x200 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x200 + j = 0x200 + (0x0 + j) by omega, X12 (0x0 + j) (by omega),
      show 0x980 + (0x0 + j) = 0x980 + j by omega]; exact q11_980 j (by omega)
  clear a11_fe4 a11_ce0 a11_cc0 a11_ca0 a11_c80 a11_9e0 a11_9c0 a11_9a0 a11_980 a11_900 a11_200 a11_1e0 a11_1c0 a11_1a0 a11_180 a11_160 a11_140 a11_120 q11_980 b11_1004 b11_920 b11_220 g11_12 g11_11 g11_10 g11_27 g11_26 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x718
  obtain ⟨n13, c13, u13⟩ := s12.block p2vEcD718 E12.self p2vEcD718_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem P2V n13 0x726 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock p2vEcD718 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_18 : reg n13 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = dlo := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = dhi := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = rem := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_26 : reg n13 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vEcD718, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_18, g12_19, g12_21, g12_22, g12_23, g12_24, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g13_11 : reg n13 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vEcD718, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_18, g12_19, g12_21, g12_22, g12_23, g12_24, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0x80 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vEcD718, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_18, g12_19, g12_21, g12_22, g12_23, g12_24, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60), (0xC80, 0x60), (0x200, 0x80)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have b13_920 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m13]; exact b12_920
  have b13_1004 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m13]; exact b12_1004
  have q13_200 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x200 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_200 j hj
  have q13_980 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_980 j hj
  have a13_120 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m13]; exact a12_120
  have a13_140 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m13]; exact a12_140
  have a13_160 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m13]; exact a12_160
  have a13_180 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m13]; exact a12_180
  have a13_1a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m13]; exact a12_1a0
  have a13_1c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m13]; exact a12_1c0
  have a13_1e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m13]; exact a12_1e0
  have a13_200 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m13]; exact a12_200
  have a13_220 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m13]; exact a12_220
  have a13_240 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m13]; exact a12_240
  have a13_260 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = psmVal ((zv) * (wv)) := by rw [m13]; exact a12_260
  have a13_900 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m13]; exact a12_900
  have a13_980 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m13]; exact a12_980
  have a13_9a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m13]; exact a12_9a0
  have a13_9c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m13]; exact a12_9c0
  have a13_9e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m13]; exact a12_9e0
  have a13_c80 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := by rw [m13]; exact a12_c80
  have a13_ca0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := by rw [m13]; exact a12_ca0
  have a13_cc0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := by rw [m13]; exact a12_cc0
  have a13_ce0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m13]; exact a12_ce0
  have a13_fe4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m13]; exact a12_fe4
  clear q12_200 a12_260 a12_240 a12_220 a12_200 a12_fe4 a12_ce0 a12_cc0 a12_ca0 a12_c80 a12_9e0 a12_9c0 a12_9a0 a12_980 a12_900 a12_1e0 a12_1c0 a12_1a0 a12_180 a12_160 a12_140 a12_120 q12_980 b12_1004 b12_920 g12_27 g12_26 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 s12 X12 K12 P12
  -- 0x726: memcpy
  obtain ⟨n14, P14, K14, X14⟩ := p2v_mc (c := 0x280) (d := 0xC80) (N := 0x80) F E13 s13 p2v_at_726 p2v_at_72a
    (by decide) (by decide) g13_2 g13_10 g13_11 g13_12
    (by decide) (by decide) (by decide)
  have s14 := P14.st
  have fr14 := P14.fr
  have t14 : Steps n0 n14 := t13.trans P14.steps
  have fR14 : ∀ x, P2vR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : P2vCode n14.mem := E13.fr F fr14
  have V14 : P2vSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [P14.regs sp (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P14.regs (3 : Fin 32) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P14.regs (4 : Fin 32) (by decide), g13_4]
  have g14_18 : reg n14 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P14.regs (18 : Fin 32) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = dlo := by rw [P14.regs (19 : Fin 32) (by decide), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = dhi := by rw [P14.regs (21 : Fin 32) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P14.regs (22 : Fin 32) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P14.regs (23 : Fin 32) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = rem := by rw [P14.regs (24 : Fin 32) (by decide), g13_24]
  have g14_26 : reg n14 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P14.regs (26 : Fin 32) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P14.regs (27 : Fin 32) (by decide), g13_27]
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60), (0xC80, 0x60), (0x200, 0x80), (0x280, 0x80)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have b14_920 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K14.b8 (by decide) (by decide)).trans b13_920
  have b14_1004 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := (K14.b8 (by decide) (by decide)).trans b13_1004
  have q14_200 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x200 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_200 j hj)
  have q14_980 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_980 j hj)
  have a14_120 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K14.acc (by decide) (by decide)).trans a13_120
  have a14_140 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K14.acc (by decide) (by decide)).trans a13_140
  have a14_160 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K14.acc (by decide) (by decide)).trans a13_160
  have a14_180 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K14.acc (by decide) (by decide)).trans a13_180
  have a14_1a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K14.acc (by decide) (by decide)).trans a13_1a0
  have a14_1c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K14.acc (by decide) (by decide)).trans a13_1c0
  have a14_1e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K14.acc (by decide) (by decide)).trans a13_1e0
  have a14_200 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K14.acc (by decide) (by decide)).trans a13_200
  have a14_220 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K14.acc (by decide) (by decide)).trans a13_220
  have a14_240 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K14.acc (by decide) (by decide)).trans a13_240
  have a14_260 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = psmVal ((zv) * (wv)) := (K14.acc (by decide) (by decide)).trans a13_260
  have a14_900 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K14.acc (by decide) (by decide)).trans a13_900
  have a14_980 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K14.acc (by decide) (by decide)).trans a13_980
  have a14_9a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K14.acc (by decide) (by decide)).trans a13_9a0
  have a14_9c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K14.acc (by decide) (by decide)).trans a13_9c0
  have a14_9e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K14.acc (by decide) (by decide)).trans a13_9e0
  have a14_c80 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := (K14.acc (by decide) (by decide)).trans a13_c80
  have a14_ca0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := (K14.acc (by decide) (by decide)).trans a13_ca0
  have a14_cc0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := (K14.acc (by decide) (by decide)).trans a13_cc0
  have a14_ce0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := (K14.acc (by decide) (by decide)).trans a13_ce0
  have a14_fe4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := (K14.acc (by decide) (by decide)).trans a13_fe4
  have a14_280 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qx := (accV_S 8 fun q hq => by
    rw [show 0x280 + q = 0x280 + (0x0 + q) by omega, X14 (0x0 + q) (by omega),
      show 0xC80 + (0x0 + q) = 0xC80 + q by omega]).trans a13_c80
  have a14_2a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = qy := (accV_S 8 fun q hq => by
    rw [show 0x2A0 + q = 0x280 + (0x20 + q) by omega, X14 (0x20 + q) (by omega),
      show 0xC80 + (0x20 + q) = 0xCA0 + q by omega]).trans a13_ca0
  have a14_2c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = qz := (accV_S 8 fun q hq => by
    rw [show 0x2C0 + q = 0x280 + (0x40 + q) by omega, X14 (0x40 + q) (by omega),
      show 0xC80 + (0x40 + q) = 0xCC0 + q by omega]).trans a13_cc0
  have a14_2e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = psmVal ((rv) * (wv)) := (accV_S 8 fun q hq => by
    rw [show 0x2E0 + q = 0x280 + (0x60 + q) by omega, X14 (0x60 + q) (by omega),
      show 0xC80 + (0x60 + q) = 0xCE0 + q by omega]).trans a13_ce0
  clear a13_fe4 a13_ce0 a13_cc0 a13_ca0 a13_c80 a13_9e0 a13_9c0 a13_9a0 a13_980 a13_900 a13_260 a13_240 a13_220 a13_200 a13_1e0 a13_1c0 a13_1a0 a13_180 a13_160 a13_140 a13_120 q13_980 q13_200 b13_1004 b13_920 g13_12 g13_11 g13_10 g13_27 g13_26 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x72E
  obtain ⟨n15, c15, u15⟩ := s14.block p2vEcD72e E14.self p2vEcD72e_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem P2V n15 0x73C (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock p2vEcD72e (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
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
  have g15_18 : reg n15 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = dlo := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = dhi := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = rem := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_26 : reg n15 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vEcD72e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_18, g14_19, g14_21, g14_22, g14_23, g14_24, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vEcD72e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_18, g14_19, g14_21, g14_22, g14_23, g14_24, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g15_12 : reg n15 a2 = BitVec.ofNat 32 0x100 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vEcD72e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_18, g14_19, g14_21, g14_22, g14_23, g14_24, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60), (0xC80, 0x60), (0x200, 0x80), (0x280, 0x80)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have b15_920 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m15]; exact b14_920
  have b15_1004 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) = ds := by rw [m15]; exact b14_1004
  have q15_200 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x200 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_200 j hj
  have q15_980 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_980 j hj
  have a15_120 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m15]; exact a14_120
  have a15_140 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m15]; exact a14_140
  have a15_160 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m15]; exact a14_160
  have a15_180 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m15]; exact a14_180
  have a15_1a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m15]; exact a14_1a0
  have a15_1c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m15]; exact a14_1c0
  have a15_1e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m15]; exact a14_1e0
  have a15_200 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m15]; exact a14_200
  have a15_220 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m15]; exact a14_220
  have a15_240 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m15]; exact a14_240
  have a15_260 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = psmVal ((zv) * (wv)) := by rw [m15]; exact a14_260
  have a15_280 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qx := by rw [m15]; exact a14_280
  have a15_2a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = qy := by rw [m15]; exact a14_2a0
  have a15_2c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = qz := by rw [m15]; exact a14_2c0
  have a15_2e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = psmVal ((rv) * (wv)) := by rw [m15]; exact a14_2e0
  have a15_900 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m15]; exact a14_900
  have a15_980 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m15]; exact a14_980
  have a15_9a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m15]; exact a14_9a0
  have a15_9c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m15]; exact a14_9c0
  have a15_9e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m15]; exact a14_9e0
  have a15_c80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := by rw [m15]; exact a14_c80
  have a15_ca0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := by rw [m15]; exact a14_ca0
  have a15_cc0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := by rw [m15]; exact a14_cc0
  have a15_ce0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m15]; exact a14_ce0
  have a15_fe4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = dv := by rw [m15]; exact a14_fe4
  clear a14_2e0 a14_2c0 a14_2a0 a14_280 a14_fe4 a14_ce0 a14_cc0 a14_ca0 a14_c80 a14_9e0 a14_9c0 a14_9a0 a14_980 a14_900 a14_260 a14_240 a14_220 a14_200 a14_1e0 a14_1c0 a14_1a0 a14_180 a14_160 a14_140 a14_120 q14_980 q14_200 b14_1004 b14_920 g14_27 g14_26 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 s14 X14 K14 P14
  -- 0x73C: memcpy
  obtain ⟨n16, P16, K16, X16⟩ := p2v_mc (c := 0xFE4) (d := 0x200) (N := 0x100) F E15 s15 p2v_at_73c p2v_at_740
    (by decide) (by decide) g15_2 g15_10 g15_11 g15_12
    (by decide) (by decide) (by decide)
  have s16 := P16.st
  have fr16 := P16.fr
  have t16 : Steps n0 n16 := t15.trans P16.steps
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [P16.regs sp (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P16.regs (3 : Fin 32) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P16.regs (4 : Fin 32) (by decide), g15_4]
  have g16_18 : reg n16 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P16.regs (18 : Fin 32) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = dlo := by rw [P16.regs (19 : Fin 32) (by decide), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = dhi := by rw [P16.regs (21 : Fin 32) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P16.regs (22 : Fin 32) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P16.regs (23 : Fin 32) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = rem := by rw [P16.regs (24 : Fin 32) (by decide), g15_24]
  have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P16.regs (26 : Fin 32) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P16.regs (27 : Fin 32) (by decide), g15_27]
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60), (0xC80, 0x60), (0x200, 0x80), (0x280, 0x80), (0xFE4, 0x100)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have b16_920 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := (K16.b8 (by decide) (by decide)).trans b15_920
  have q16_200 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x200 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_200 j hj)
  have q16_980 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_980 j hj)
  have a16_120 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K16.acc (by decide) (by decide)).trans a15_120
  have a16_140 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K16.acc (by decide) (by decide)).trans a15_140
  have a16_160 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K16.acc (by decide) (by decide)).trans a15_160
  have a16_180 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K16.acc (by decide) (by decide)).trans a15_180
  have a16_1a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K16.acc (by decide) (by decide)).trans a15_1a0
  have a16_1c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K16.acc (by decide) (by decide)).trans a15_1c0
  have a16_1e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K16.acc (by decide) (by decide)).trans a15_1e0
  have a16_200 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K16.acc (by decide) (by decide)).trans a15_200
  have a16_220 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K16.acc (by decide) (by decide)).trans a15_220
  have a16_240 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K16.acc (by decide) (by decide)).trans a15_240
  have a16_260 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = psmVal ((zv) * (wv)) := (K16.acc (by decide) (by decide)).trans a15_260
  have a16_280 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qx := (K16.acc (by decide) (by decide)).trans a15_280
  have a16_2a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = qy := (K16.acc (by decide) (by decide)).trans a15_2a0
  have a16_2c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = qz := (K16.acc (by decide) (by decide)).trans a15_2c0
  have a16_2e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = psmVal ((rv) * (wv)) := (K16.acc (by decide) (by decide)).trans a15_2e0
  have a16_900 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := (K16.acc (by decide) (by decide)).trans a15_900
  have a16_980 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K16.acc (by decide) (by decide)).trans a15_980
  have a16_9a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K16.acc (by decide) (by decide)).trans a15_9a0
  have a16_9c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K16.acc (by decide) (by decide)).trans a15_9c0
  have a16_9e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K16.acc (by decide) (by decide)).trans a15_9e0
  have a16_c80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := (K16.acc (by decide) (by decide)).trans a15_c80
  have a16_ca0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := (K16.acc (by decide) (by decide)).trans a15_ca0
  have a16_cc0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := (K16.acc (by decide) (by decide)).trans a15_cc0
  have a16_ce0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := (K16.acc (by decide) (by decide)).trans a15_ce0
  have a16_fe4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (accV_S 8 fun q hq => by
    rw [show 0xFE4 + q = 0xFE4 + (0x0 + q) by omega, X16 (0x0 + q) (by omega),
      show 0x200 + (0x0 + q) = 0x200 + q by omega]).trans a15_200
  have a16_1004 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (accV_S 8 fun q hq => by
    rw [show 0x1004 + q = 0xFE4 + (0x20 + q) by omega, X16 (0x20 + q) (by omega),
      show 0x200 + (0x20 + q) = 0x220 + q by omega]).trans a15_220
  have a16_1024 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (accV_S 8 fun q hq => by
    rw [show 0x1024 + q = 0xFE4 + (0x40 + q) by omega, X16 (0x40 + q) (by omega),
      show 0x200 + (0x40 + q) = 0x240 + q by omega]).trans a15_240
  have a16_1044 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = psmVal ((zv) * (wv)) := (accV_S 8 fun q hq => by
    rw [show 0x1044 + q = 0xFE4 + (0x60 + q) by omega, X16 (0x60 + q) (by omega),
      show 0x200 + (0x60 + q) = 0x260 + q by omega]).trans a15_260
  have a16_1064 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1064) 8 = qx := (accV_S 8 fun q hq => by
    rw [show 0x1064 + q = 0xFE4 + (0x80 + q) by omega, X16 (0x80 + q) (by omega),
      show 0x200 + (0x80 + q) = 0x280 + q by omega]).trans a15_280
  have a16_1084 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1084) 8 = qy := (accV_S 8 fun q hq => by
    rw [show 0x1084 + q = 0xFE4 + (0xA0 + q) by omega, X16 (0xA0 + q) (by omega),
      show 0x200 + (0xA0 + q) = 0x2A0 + q by omega]).trans a15_2a0
  have a16_10a4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10A4) 8 = qz := (accV_S 8 fun q hq => by
    rw [show 0x10A4 + q = 0xFE4 + (0xC0 + q) by omega, X16 (0xC0 + q) (by omega),
      show 0x200 + (0xC0 + q) = 0x2C0 + q by omega]).trans a15_2c0
  have a16_10c4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = psmVal ((rv) * (wv)) := (accV_S 8 fun q hq => by
    rw [show 0x10C4 + q = 0xFE4 + (0xE0 + q) by omega, X16 (0xE0 + q) (by omega),
      show 0x200 + (0xE0 + q) = 0x2E0 + q by omega]).trans a15_2e0
  have q16_fe4 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0xFE4 + j = 0xFE4 + (0x0 + j) by omega, X16 (0x0 + j) (by omega),
      show 0x200 + (0x0 + j) = 0x200 + j by omega]; exact q15_200 j (by omega)
  clear a15_fe4 a15_ce0 a15_cc0 a15_ca0 a15_c80 a15_9e0 a15_9c0 a15_9a0 a15_980 a15_900 a15_2e0 a15_2c0 a15_2a0 a15_280 a15_260 a15_240 a15_220 a15_200 a15_1e0 a15_1c0 a15_1a0 a15_180 a15_160 a15_140 a15_120 q15_980 q15_200 b15_1004 b15_920 g15_12 g15_11 g15_10 g15_27 g15_26 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0x744
  obtain ⟨n17, c17, u17⟩ := s16.block p2vEcD744 E16.self p2vEcD744_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem P2V n17 0x754 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock p2vEcD744 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_18 : reg n17 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = rem := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x7FF := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcD744, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_18, g16_19, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_19 : reg n17 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcD744, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_18, g16_19, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_20 : reg n17 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcD744, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_18, g16_19, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_21 : reg n17 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcD744, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_18, g16_19, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_22 : reg n17 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcD744, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_18, g16_19, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0x1E0, 0x20), (0x9E0, 0x20), (0xCE0, 0x20), (0x980, 0x60), (0xC80, 0x60), (0x200, 0x80), (0x280, 0x80), (0xFE4, 0x100)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have b17_920 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m17]; exact b16_920
  have q17_200 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x200 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_200 j hj
  have q17_980 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_980 j hj
  have q17_fe4 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xFE4 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_fe4 j hj
  have a17_120 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m17]; exact a16_120
  have a17_140 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m17]; exact a16_140
  have a17_160 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m17]; exact a16_160
  have a17_180 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m17]; exact a16_180
  have a17_1a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m17]; exact a16_1a0
  have a17_1c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m17]; exact a16_1c0
  have a17_1e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m17]; exact a16_1e0
  have a17_200 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m17]; exact a16_200
  have a17_220 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x220) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m17]; exact a16_220
  have a17_240 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m17]; exact a16_240
  have a17_260 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = psmVal ((zv) * (wv)) := by rw [m17]; exact a16_260
  have a17_280 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qx := by rw [m17]; exact a16_280
  have a17_2a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = qy := by rw [m17]; exact a16_2a0
  have a17_2c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = qz := by rw [m17]; exact a16_2c0
  have a17_2e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = psmVal ((rv) * (wv)) := by rw [m17]; exact a16_2e0
  have a17_900 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m17]; exact a16_900
  have a17_980 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m17]; exact a16_980
  have a17_9a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m17]; exact a16_9a0
  have a17_9c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m17]; exact a16_9c0
  have a17_9e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m17]; exact a16_9e0
  have a17_c80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := by rw [m17]; exact a16_c80
  have a17_ca0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := by rw [m17]; exact a16_ca0
  have a17_cc0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := by rw [m17]; exact a16_cc0
  have a17_ce0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m17]; exact a16_ce0
  have a17_fe4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m17]; exact a16_fe4
  have a17_1004 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m17]; exact a16_1004
  have a17_1024 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m17]; exact a16_1024
  have a17_1044 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = psmVal ((zv) * (wv)) := by rw [m17]; exact a16_1044
  have a17_1064 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1064) 8 = qx := by rw [m17]; exact a16_1064
  have a17_1084 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1084) 8 = qy := by rw [m17]; exact a16_1084
  have a17_10a4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10A4) 8 = qz := by rw [m17]; exact a16_10a4
  have a17_10c4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = psmVal ((rv) * (wv)) := by rw [m17]; exact a16_10c4
  clear q16_fe4 a16_10c4 a16_10a4 a16_1084 a16_1064 a16_1044 a16_1024 a16_1004 a16_fe4 a16_ce0 a16_cc0 a16_ca0 a16_c80 a16_9e0 a16_9c0 a16_9a0 a16_980 a16_900 a16_2e0 a16_2c0 a16_2a0 a16_280 a16_260 a16_240 a16_220 a16_200 a16_1e0 a16_1c0 a16_1a0 a16_180 a16_160 a16_140 a16_120 q16_980 q16_200 b16_920 g16_27 g16_26 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 s16 X16 K16 P16
  exact .inr ⟨n17, t17, s17, E17, V17, fR17, g17_2, g17_3, g17_4, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_26, g17_27, b17_920, q17_200, q17_980, q17_fe4, a17_120, a17_140, a17_160, a17_180, a17_1a0, a17_1c0, a17_1e0, a17_200, a17_220, a17_240, a17_260, a17_280, a17_2a0, a17_2c0, a17_2e0, a17_900, a17_980, a17_9a0, a17_9c0, a17_9e0, a17_c80, a17_ca0, a17_cc0, a17_ce0, a17_fe4, a17_1004, a17_1024, a17_1044, a17_1064, a17_1084, a17_10a4, a17_10c4, keep_kk17.mono (by decide)⟩

end C3.RV32.P2v
