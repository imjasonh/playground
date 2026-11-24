import C3BootProofs.Proofs.P2vEcPt

/-!
# `p256VerifyPrehash`: the tables of the linear combination, part 0a

Part 0a of the table loop from 0x754 to 0x862: the odd multiples `P + j·2P` of `G` and of `Q`, stored at offsets 0x300 and 0x600.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vEcT0a758 : List BInstr :=
  [.aluImm .add a0 a0 0x101, .aluImm .add a2 x0 0x80, .alu .add a1 x0 (18 : Fin 32)]
theorem p2vEcT0a758_end : blockEnd p256VerifyPrehashCode 0x758 p2vEcT0a758 = some 0x762 := by
  simp only [p2vEcT0a758]
  rw [blockEnd, p2v_at_758]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_75c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_760]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT0a76a : List BInstr :=
  [.aluImm .add (8 : Fin 32) sp 0x7FF, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x481, .aluImm .add (9 : Fin 32) x0 0x8]
theorem p2vEcT0a76a_end : blockEnd p256VerifyPrehashCode 0x76A p2vEcT0a76a = some 0x774 := by
  simp only [p2vEcT0a76a]
  rw [blockEnd, p2v_at_76a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_76e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_772]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT0a776 : List BInstr :=
  [.aluImm .add a2 x0 0x60, .alu .add a0 x0 (8 : Fin 32), .alu .add a1 x0 (23 : Fin 32)]
theorem p2vEcT0a776_end : blockEnd p256VerifyPrehashCode 0x776 p2vEcT0a776 = some 0x77E := by
  simp only [p2vEcT0a776]
  rw [blockEnd, p2v_at_776]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_77a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_77c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT0a786 : List BInstr :=
  [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x60, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]
theorem p2vEcT0a786_end : blockEnd p256VerifyPrehashCode 0x786 p2vEcT0a786 = some 0x78C := by
  simp only [p2vEcT0a786]
  rw [blockEnd, p2v_at_786]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_78a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT0a78e : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x300, .aluImm .add (8 : Fin 32) sp 0x7FF, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x181, .aluImm .add (9 : Fin 32) x0 0x300]
theorem p2vEcT0a78e_end : blockEnd p256VerifyPrehashCode 0x78E p2vEcT0a78e = some 0x7AE := by
  simp only [p2vEcT0a78e]
  rw [blockEnd, p2v_at_78e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_792]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_796]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_79a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_79e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_7a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_7a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_7aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_ect0a {B dlo dhi rem : Word} {fs gs ds es : BitVec 8} {wv U1 U2 : Nat} {P0 P1 : Pt2} {qx qy qz rv sv zv fv gv dv ev : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x754 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = B + 0x21A0 + BitVec.ofNat 32 0x7FF)
    (g0_18 : reg n0 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4)
    (g0_19 : reg n0 (19 : Fin 32) = BitVec.ofNat 32 0x0)
    (g0_20 : reg n0 (20 : Fin 32) = BitVec.ofNat 32 0x2)
    (g0_21 : reg n0 (21 : Fin 32) = BitVec.ofNat 32 0x300)
    (g0_22 : reg n0 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300)
    (g0_23 : reg n0 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress))
    (g0_24 : reg n0 (24 : Fin 32) = rem)
    (g0_26 : reg n0 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920)
    (g0_27 : reg n0 (27 : Fin 32) = BitVec.ofNat 32 0x7)
    (b0_920 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs)
    (a0_120 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx)
    (a0_140 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy)
    (a0_160 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz)
    (a0_180 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv)
    (a0_1a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv)
    (a0_1c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv)
    (a0_1e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv)
    (a0_260 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1)
    (a0_2e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2)
    (a0_900 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv)
    (a0_980 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8)
    (a0_9a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8)
    (a0_9c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8)
    (a0_9e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)))
    (a0_c80 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx)
    (a0_ca0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy)
    (a0_cc0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz)
    (a0_ce0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)))
    (a0_1044 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1)
    (a0_10c4 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2)
    (p0_200 : ptF n0.mem B 0x200 = P0)
    (p0_280 : ptF n0.mem B 0x280 = P1)
    (p0_fe4 : ptF n0.mem B 0xFE4 = P0)
    (p0_1064 : ptF n0.mem B 0x1064 = P1)
    (RS : P2vRoSep B)
    (hP0 : Pt2Lt P0)
    (hP1 : Pt2Lt P1)
    (RS : P2vRoSep B)
    (PT0 : P2vPtCode M0) :
    (¬ (True) ∧ P2vRet B v n0 0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x7B6 (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x980 ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 0x300 ∧
        reg n' (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 ∧
        reg n' (19 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x2 ∧
        reg n' (21 : Fin 32) = BitVec.ofNat 32 0x300 ∧
        reg n' (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 ∧
        reg n' (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) ∧
        reg n' (24 : Fin 32) = rem ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        reg n' (27 : Fin 32) = BitVec.ofNat 32 0x7 ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xAA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 ∧
        ptF n'.mem B 0x200 = P0 ∧
        ptF n'.mem B 0x280 = P1 ∧
        ptF n'.mem B 0x900 = P0 ∧
        ptF n'.mem B 0xFE4 = P0 ∧
        ptF n'.mem B 0x1064 = P1 ∧
        P2vKeepL B n0.mem n'.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60), (0xF20, 0x60), (0x980, 0x300)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x754: branch, not taken
  obtain ⟨n1, d1, u1⟩ := s0.notTaken E0.self 0x758 p2v_at_754
    (by decide) (by rw [g0_19, g0_20]; decide)
  have s1 : St n1.mem P2V n1 0x758 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, P2vR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, P2vR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : P2vCode n1.mem := E0.fr F fr1
  have V1 : P2vSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x7FF := by rw [u1.regs, g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u1.regs, g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u1.regs, g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u1.regs, g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u1.regs, g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u1.regs, g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u1.regs, g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = rem := by rw [u1.regs, g0_24]
  have g1_26 : reg n1 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u1.regs, g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u1.regs, g0_27]
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have b1_920 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m1]; exact b0_920
  have a1_120 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m1]; exact a0_120
  have a1_140 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m1]; exact a0_140
  have a1_160 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m1]; exact a0_160
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m1]; exact a0_180
  have a1_1a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m1]; exact a0_1a0
  have a1_1c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m1]; exact a0_1c0
  have a1_1e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m1]; exact a0_1e0
  have a1_260 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m1]; exact a0_260
  have a1_2e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m1]; exact a0_2e0
  have a1_900 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m1]; exact a0_900
  have a1_980 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m1]; exact a0_980
  have a1_9a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m1]; exact a0_9a0
  have a1_9c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m1]; exact a0_9c0
  have a1_9e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m1]; exact a0_9e0
  have a1_c80 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := by rw [m1]; exact a0_c80
  have a1_ca0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := by rw [m1]; exact a0_ca0
  have a1_cc0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := by rw [m1]; exact a0_cc0
  have a1_ce0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m1]; exact a0_ce0
  have a1_1044 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m1]; exact a0_1044
  have a1_10c4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m1]; exact a0_10c4
  have p1_200 : ptF n1.mem B 0x200 = P0 := by rw [m1]; exact p0_200
  have p1_280 : ptF n1.mem B 0x280 = P1 := by rw [m1]; exact p0_280
  have p1_fe4 : ptF n1.mem B 0xFE4 = P0 := by rw [m1]; exact p0_fe4
  have p1_1064 : ptF n1.mem B 0x1064 = P1 := by rw [m1]; exact p0_1064
  -- 0x758
  obtain ⟨n2, c2, u2⟩ := s1.block p2vEcT0a758 E1.self p2vEcT0a758_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem P2V n2 0x762 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock p2vEcT0a758 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
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
  have g2_18 : reg n2 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb2, runBlock_reg _ _ _ (18 : Fin 32) s1.zero (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb2, runBlock_reg _ _ _ (19 : Fin 32) s1.zero (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb2, runBlock_reg _ _ _ (20 : Fin 32) s1.zero (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb2, runBlock_reg _ _ _ (21 : Fin 32) s1.zero (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb2, runBlock_reg _ _ _ (22 : Fin 32) s1.zero (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb2, runBlock_reg _ _ _ (23 : Fin 32) s1.zero (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = rem := by
    rw [rb2, runBlock_reg _ _ _ (24 : Fin 32) s1.zero (by decide), g1_24]
  have g2_26 : reg n2 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb2, runBlock_reg _ _ _ (26 : Fin 32) s1.zero (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb2, runBlock_reg _ _ _ (27 : Fin 32) s1.zero (by decide), g1_27]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vEcT0a758, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_10, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g2_11 : reg n2 a1 = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vEcT0a758, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_10, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g2_12 : reg n2 a2 = BitVec.ofNat 32 0x80 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, p2vEcT0a758, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_10, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have b2_920 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x920) = fs := by rw [m2]; exact b1_920
  have a2_120 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m2]; exact a1_120
  have a2_140 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m2]; exact a1_140
  have a2_160 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m2]; exact a1_160
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m2]; exact a1_180
  have a2_1a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m2]; exact a1_1a0
  have a2_1c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m2]; exact a1_1c0
  have a2_1e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m2]; exact a1_1e0
  have a2_260 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m2]; exact a1_260
  have a2_2e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m2]; exact a1_2e0
  have a2_900 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = fv := by rw [m2]; exact a1_900
  have a2_980 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m2]; exact a1_980
  have a2_9a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m2]; exact a1_9a0
  have a2_9c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m2]; exact a1_9c0
  have a2_9e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m2]; exact a1_9e0
  have a2_c80 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := by rw [m2]; exact a1_c80
  have a2_ca0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := by rw [m2]; exact a1_ca0
  have a2_cc0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := by rw [m2]; exact a1_cc0
  have a2_ce0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m2]; exact a1_ce0
  have a2_1044 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m2]; exact a1_1044
  have a2_10c4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m2]; exact a1_10c4
  have p2_200 : ptF n2.mem B 0x200 = P0 := by rw [m2]; exact p1_200
  have p2_280 : ptF n2.mem B 0x280 = P1 := by rw [m2]; exact p1_280
  have p2_fe4 : ptF n2.mem B 0xFE4 = P0 := by rw [m2]; exact p1_fe4
  have p2_1064 : ptF n2.mem B 0x1064 = P1 := by rw [m2]; exact p1_1064
  clear p1_1064 p1_fe4 p1_280 p1_200 a1_10c4 a1_1044 a1_ce0 a1_cc0 a1_ca0 a1_c80 a1_9e0 a1_9c0 a1_9a0 a1_980 a1_900 a1_2e0 a1_260 a1_1e0 a1_1c0 a1_1a0 a1_180 a1_160 a1_140 a1_120 b1_920 g1_27 g1_26 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x762: memcpy
  obtain ⟨n3, P3, K3, X3⟩ := p2v_mc (c := 0x900) (d := 0xFE4) (N := 0x80) F E2 s2 p2v_at_762 p2v_at_766
    (by decide) (by decide) g2_2 g2_10 g2_11 g2_12
    (by decide) (by decide) (by decide)
  have s3 := P3.st
  have fr3 := P3.fr
  have t3 : Steps n0 n3 := t2.trans P3.steps
  have fR3 : ∀ x, P2vR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : P2vCode n3.mem := E2.fr F fr3
  have V3 : P2vSaves B n3.mem v := V2.keep K3 (by decide)
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [P3.regs sp (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P3.regs (3 : Fin 32) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P3.regs (4 : Fin 32) (by decide), g2_4]
  have g3_18 : reg n3 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P3.regs (18 : Fin 32) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P3.regs (19 : Fin 32) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P3.regs (20 : Fin 32) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P3.regs (21 : Fin 32) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P3.regs (22 : Fin 32) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P3.regs (23 : Fin 32) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = rem := by rw [P3.regs (24 : Fin 32) (by decide), g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P3.regs (26 : Fin 32) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P3.regs (27 : Fin 32) (by decide), g2_27]
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0x900, 0x80)] := keep_kk2.trans K3.toL
  clear keep_kk2
  have a3_120 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K3.acc (by decide) (by decide)).trans a2_120
  have a3_140 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K3.acc (by decide) (by decide)).trans a2_140
  have a3_160 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K3.acc (by decide) (by decide)).trans a2_160
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K3.acc (by decide) (by decide)).trans a2_180
  have a3_1a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K3.acc (by decide) (by decide)).trans a2_1a0
  have a3_1c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K3.acc (by decide) (by decide)).trans a2_1c0
  have a3_1e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K3.acc (by decide) (by decide)).trans a2_1e0
  have a3_260 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K3.acc (by decide) (by decide)).trans a2_260
  have a3_2e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K3.acc (by decide) (by decide)).trans a2_2e0
  have a3_980 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K3.acc (by decide) (by decide)).trans a2_980
  have a3_9a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K3.acc (by decide) (by decide)).trans a2_9a0
  have a3_9c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K3.acc (by decide) (by decide)).trans a2_9c0
  have a3_9e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K3.acc (by decide) (by decide)).trans a2_9e0
  have a3_c80 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := (K3.acc (by decide) (by decide)).trans a2_c80
  have a3_ca0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := (K3.acc (by decide) (by decide)).trans a2_ca0
  have a3_cc0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := (K3.acc (by decide) (by decide)).trans a2_cc0
  have a3_ce0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := (K3.acc (by decide) (by decide)).trans a2_ce0
  have a3_1044 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K3.acc (by decide) (by decide)).trans a2_1044
  have a3_10c4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K3.acc (by decide) (by decide)).trans a2_10c4
  have p3_200 : ptF n3.mem B 0x200 = P0 := (K3.pt (by decide) (by decide)).trans p2_200
  have p3_280 : ptF n3.mem B 0x280 = P1 := (K3.pt (by decide) (by decide)).trans p2_280
  have p3_fe4 : ptF n3.mem B 0xFE4 = P0 := (K3.pt (by decide) (by decide)).trans p2_fe4
  have p3_1064 : ptF n3.mem B 0x1064 = P1 := (K3.pt (by decide) (by decide)).trans p2_1064
  have p3_900 : ptF n3.mem B 0x900 = P0 := (ptF_cp X3 (by decide) (by decide) (by decide)).trans p2_fe4
  have a3_960 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (accV_S 8 fun q hq => by
    rw [show 0x960 + q = 0x900 + (0x60 + q) by omega, X3 (0x60 + q) (by omega),
      show 0xFE4 + (0x60 + q) = 0x1044 + q by omega]).trans a2_1044
  clear p2_1064 p2_fe4 p2_280 p2_200 a2_10c4 a2_1044 a2_ce0 a2_cc0 a2_ca0 a2_c80 a2_9e0 a2_9c0 a2_9a0 a2_980 a2_900 a2_2e0 a2_260 a2_1e0 a2_1c0 a2_1a0 a2_180 a2_160 a2_140 a2_120 b2_920 g2_12 g2_11 g2_10 g2_27 g2_26 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x76A
  obtain ⟨n4, c4, u4⟩ := s3.block p2vEcT0a76a E3.self p2vEcT0a76a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem P2V n4 0x774 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock p2vEcT0a76a (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_18 : reg n4 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb4, runBlock_reg _ _ _ (20 : Fin 32) s3.zero (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb4, runBlock_reg _ _ _ (23 : Fin 32) s3.zero (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = rem := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_26 : reg n4 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_8 : reg n4 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vEcT0a76a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g4_9 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 0x8 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, p2vEcT0a76a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0x900, 0x80)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have a4_120 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m4]; exact a3_120
  have a4_140 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m4]; exact a3_140
  have a4_160 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m4]; exact a3_160
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m4]; exact a3_180
  have a4_1a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m4]; exact a3_1a0
  have a4_1c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m4]; exact a3_1c0
  have a4_1e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m4]; exact a3_1e0
  have a4_260 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m4]; exact a3_260
  have a4_2e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m4]; exact a3_2e0
  have a4_960 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m4]; exact a3_960
  have a4_980 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m4]; exact a3_980
  have a4_9a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m4]; exact a3_9a0
  have a4_9c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m4]; exact a3_9c0
  have a4_9e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m4]; exact a3_9e0
  have a4_c80 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := by rw [m4]; exact a3_c80
  have a4_ca0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := by rw [m4]; exact a3_ca0
  have a4_cc0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := by rw [m4]; exact a3_cc0
  have a4_ce0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m4]; exact a3_ce0
  have a4_1044 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m4]; exact a3_1044
  have a4_10c4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m4]; exact a3_10c4
  have p4_200 : ptF n4.mem B 0x200 = P0 := by rw [m4]; exact p3_200
  have p4_280 : ptF n4.mem B 0x280 = P1 := by rw [m4]; exact p3_280
  have p4_900 : ptF n4.mem B 0x900 = P0 := by rw [m4]; exact p3_900
  have p4_fe4 : ptF n4.mem B 0xFE4 = P0 := by rw [m4]; exact p3_fe4
  have p4_1064 : ptF n4.mem B 0x1064 = P1 := by rw [m4]; exact p3_1064
  clear a3_960 p3_900 p3_1064 p3_fe4 p3_280 p3_200 a3_10c4 a3_1044 a3_ce0 a3_cc0 a3_ca0 a3_c80 a3_9e0 a3_9c0 a3_9a0 a3_980 a3_2e0 a3_260 a3_1e0 a3_1c0 a3_1a0 a3_180 a3_160 a3_140 a3_120 g3_27 g3_26 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 s3 X3 K3 P3
  -- 0x774: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0x776 p2v_at_774
    (by decide) (by rw [g4_9, s4.zero]; decide)
  have s5 : St n5.mem P2V n5 0x776 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, P2vR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, P2vR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : P2vCode n5.mem := E4.fr F fr5
  have V5 : P2vSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [u5.regs, g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = BitVec.ofNat 32 0x8 := by rw [u5.regs, g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u5.regs, g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u5.regs, g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u5.regs, g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u5.regs, g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u5.regs, g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = rem := by rw [u5.regs, g4_24]
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u5.regs, g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u5.regs, g4_27]
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0x900, 0x80)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have a5_120 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m5]; exact a4_120
  have a5_140 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m5]; exact a4_140
  have a5_160 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m5]; exact a4_160
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m5]; exact a4_180
  have a5_1a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m5]; exact a4_1a0
  have a5_1c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m5]; exact a4_1c0
  have a5_1e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m5]; exact a4_1e0
  have a5_260 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m5]; exact a4_260
  have a5_2e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m5]; exact a4_2e0
  have a5_960 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m5]; exact a4_960
  have a5_980 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m5]; exact a4_980
  have a5_9a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m5]; exact a4_9a0
  have a5_9c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m5]; exact a4_9c0
  have a5_9e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m5]; exact a4_9e0
  have a5_c80 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := by rw [m5]; exact a4_c80
  have a5_ca0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := by rw [m5]; exact a4_ca0
  have a5_cc0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := by rw [m5]; exact a4_cc0
  have a5_ce0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m5]; exact a4_ce0
  have a5_1044 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m5]; exact a4_1044
  have a5_10c4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m5]; exact a4_10c4
  have p5_200 : ptF n5.mem B 0x200 = P0 := by rw [m5]; exact p4_200
  have p5_280 : ptF n5.mem B 0x280 = P1 := by rw [m5]; exact p4_280
  have p5_900 : ptF n5.mem B 0x900 = P0 := by rw [m5]; exact p4_900
  have p5_fe4 : ptF n5.mem B 0xFE4 = P0 := by rw [m5]; exact p4_fe4
  have p5_1064 : ptF n5.mem B 0x1064 = P1 := by rw [m5]; exact p4_1064
  clear p4_1064 p4_fe4 p4_900 p4_280 p4_200 a4_10c4 a4_1044 a4_ce0 a4_cc0 a4_ca0 a4_c80 a4_9e0 a4_9c0 a4_9a0 a4_980 a4_960 a4_2e0 a4_260 a4_1e0 a4_1c0 a4_1a0 a4_180 a4_160 a4_140 a4_120 g4_9 g4_8 g4_27 g4_26 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x776
  obtain ⟨n6, c6, u6⟩ := s5.block p2vEcT0a776 E5.self p2vEcT0a776_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem P2V n6 0x77E (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock p2vEcT0a776 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_8 : reg n6 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 0x8 := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb6, runBlock_reg _ _ _ (20 : Fin 32) s5.zero (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = rem := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g6_12 : reg n6 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0x900, 0x80)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have a6_120 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m6]; exact a5_120
  have a6_140 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m6]; exact a5_140
  have a6_160 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m6]; exact a5_160
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m6]; exact a5_180
  have a6_1a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m6]; exact a5_1a0
  have a6_1c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m6]; exact a5_1c0
  have a6_1e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m6]; exact a5_1e0
  have a6_260 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m6]; exact a5_260
  have a6_2e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m6]; exact a5_2e0
  have a6_960 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m6]; exact a5_960
  have a6_980 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m6]; exact a5_980
  have a6_9a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m6]; exact a5_9a0
  have a6_9c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m6]; exact a5_9c0
  have a6_9e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m6]; exact a5_9e0
  have a6_c80 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = qx := by rw [m6]; exact a5_c80
  have a6_ca0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xCA0) 8 = qy := by rw [m6]; exact a5_ca0
  have a6_cc0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC0) 8 = qz := by rw [m6]; exact a5_cc0
  have a6_ce0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m6]; exact a5_ce0
  have a6_1044 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m6]; exact a5_1044
  have a6_10c4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m6]; exact a5_10c4
  have p6_200 : ptF n6.mem B 0x200 = P0 := by rw [m6]; exact p5_200
  have p6_280 : ptF n6.mem B 0x280 = P1 := by rw [m6]; exact p5_280
  have p6_900 : ptF n6.mem B 0x900 = P0 := by rw [m6]; exact p5_900
  have p6_fe4 : ptF n6.mem B 0xFE4 = P0 := by rw [m6]; exact p5_fe4
  have p6_1064 : ptF n6.mem B 0x1064 = P1 := by rw [m6]; exact p5_1064
  clear p5_1064 p5_fe4 p5_900 p5_280 p5_200 a5_10c4 a5_1044 a5_ce0 a5_cc0 a5_ca0 a5_c80 a5_9e0 a5_9c0 a5_9a0 a5_980 a5_960 a5_2e0 a5_260 a5_1e0 a5_1c0 a5_1a0 a5_180 a5_160 a5_140 a5_120 g5_27 g5_26 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x77E: memcpy from outside the stack
  obtain ⟨n7, P7, K7, X7⟩ := p2v_mcRo2 (c := 0xC80) (N := 0x60) F RS E6 s6 p2v_at_77e p2v_at_782
    (by decide) (by decide) g6_2 g6_10 g6_11 g6_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s7 := P7.st
  have fr7 := P7.fr
  have t7 : Steps n0 n7 := t6.trans P7.steps
  have fR7 : ∀ x, P2vR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : P2vCode n7.mem := E6.fr F fr7
  have V7 : P2vSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [P7.regs sp (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P7.regs (3 : Fin 32) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P7.regs (4 : Fin 32) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [P7.regs (8 : Fin 32) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 0x8 := by rw [P7.regs (9 : Fin 32) (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P7.regs (18 : Fin 32) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P7.regs (19 : Fin 32) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P7.regs (20 : Fin 32) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P7.regs (21 : Fin 32) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P7.regs (22 : Fin 32) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P7.regs (23 : Fin 32) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = rem := by rw [P7.regs (24 : Fin 32) (by decide), g6_24]
  have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P7.regs (26 : Fin 32) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P7.regs (27 : Fin 32) (by decide), g6_27]
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0x900, 0x80), (0xC80, 0x60)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have a7_120 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K7.acc (by decide) (by decide)).trans a6_120
  have a7_140 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K7.acc (by decide) (by decide)).trans a6_140
  have a7_160 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K7.acc (by decide) (by decide)).trans a6_160
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K7.acc (by decide) (by decide)).trans a6_180
  have a7_1a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K7.acc (by decide) (by decide)).trans a6_1a0
  have a7_1c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K7.acc (by decide) (by decide)).trans a6_1c0
  have a7_1e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K7.acc (by decide) (by decide)).trans a6_1e0
  have a7_260 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K7.acc (by decide) (by decide)).trans a6_260
  have a7_2e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K7.acc (by decide) (by decide)).trans a6_2e0
  have a7_960 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (K7.acc (by decide) (by decide)).trans a6_960
  have a7_980 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K7.acc (by decide) (by decide)).trans a6_980
  have a7_9a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K7.acc (by decide) (by decide)).trans a6_9a0
  have a7_9c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K7.acc (by decide) (by decide)).trans a6_9c0
  have a7_9e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K7.acc (by decide) (by decide)).trans a6_9e0
  have a7_ce0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := (K7.acc (by decide) (by decide)).trans a6_ce0
  have a7_1044 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K7.acc (by decide) (by decide)).trans a6_1044
  have a7_10c4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K7.acc (by decide) (by decide)).trans a6_10c4
  have p7_200 : ptF n7.mem B 0x200 = P0 := (K7.pt (by decide) (by decide)).trans p6_200
  have p7_280 : ptF n7.mem B 0x280 = P1 := (K7.pt (by decide) (by decide)).trans p6_280
  have p7_900 : ptF n7.mem B 0x900 = P0 := (K7.pt (by decide) (by decide)).trans p6_900
  have p7_fe4 : ptF n7.mem B 0xFE4 = P0 := (K7.pt (by decide) (by decide)).trans p6_fe4
  have p7_1064 : ptF n7.mem B 0x1064 = P1 := (K7.pt (by decide) (by decide)).trans p6_1064
  have q7_c80 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X7 j hj).trans (fR6 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p6_1064 p6_fe4 p6_900 p6_280 p6_200 a6_10c4 a6_1044 a6_ce0 a6_cc0 a6_ca0 a6_c80 a6_9e0 a6_9c0 a6_9a0 a6_980 a6_960 a6_2e0 a6_260 a6_1e0 a6_1c0 a6_1a0 a6_180 a6_160 a6_140 a6_120 g6_12 g6_11 g6_10 g6_27 g6_26 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x786
  obtain ⟨n8, c8, u8⟩ := s7.block p2vEcT0a786 E7.self p2vEcT0a786_end
    ⟨trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem P2V n8 0x78C (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock p2vEcT0a786 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_18 : reg n8 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = rem := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_8 : reg n8 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCE0 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g8_9 : reg n8 (9 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0x900, 0x80), (0xC80, 0x60)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have q8_c80 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m8]; exact q7_c80 j hj
  have a8_120 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m8]; exact a7_120
  have a8_140 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m8]; exact a7_140
  have a8_160 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m8]; exact a7_160
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m8]; exact a7_180
  have a8_1a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m8]; exact a7_1a0
  have a8_1c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m8]; exact a7_1c0
  have a8_1e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m8]; exact a7_1e0
  have a8_260 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m8]; exact a7_260
  have a8_2e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m8]; exact a7_2e0
  have a8_960 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m8]; exact a7_960
  have a8_980 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m8]; exact a7_980
  have a8_9a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m8]; exact a7_9a0
  have a8_9c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m8]; exact a7_9c0
  have a8_9e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m8]; exact a7_9e0
  have a8_ce0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m8]; exact a7_ce0
  have a8_1044 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m8]; exact a7_1044
  have a8_10c4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m8]; exact a7_10c4
  have p8_200 : ptF n8.mem B 0x200 = P0 := by rw [m8]; exact p7_200
  have p8_280 : ptF n8.mem B 0x280 = P1 := by rw [m8]; exact p7_280
  have p8_900 : ptF n8.mem B 0x900 = P0 := by rw [m8]; exact p7_900
  have p8_fe4 : ptF n8.mem B 0xFE4 = P0 := by rw [m8]; exact p7_fe4
  have p8_1064 : ptF n8.mem B 0x1064 = P1 := by rw [m8]; exact p7_1064
  clear q7_c80 p7_1064 p7_fe4 p7_900 p7_280 p7_200 a7_10c4 a7_1044 a7_ce0 a7_9e0 a7_9c0 a7_9a0 a7_980 a7_960 a7_2e0 a7_260 a7_1e0 a7_1c0 a7_1a0 a7_180 a7_160 a7_140 a7_120 g7_27 g7_26 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 s7 X7 K7 P7
  -- 0x78C: branch, taken
  obtain ⟨n9, d9, u9⟩ := s8.taken E8.self 0x776 p2v_at_78c
    (by decide) (by rw [g8_9, s8.zero]; decide)
  have s9 : St n9.mem P2V n9 0x776 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, P2vR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, P2vR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : P2vCode n9.mem := E8.fr F fr9
  have V9 : P2vSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCE0 := by rw [u9.regs, g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u9.regs, g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u9.regs, g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u9.regs, g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u9.regs, g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u9.regs, g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u9.regs, g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u9.regs, g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = rem := by rw [u9.regs, g8_24]
  have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u9.regs, g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u9.regs, g8_27]
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0x900, 0x80), (0xC80, 0x60)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have q9_c80 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_c80 j hj
  have a9_120 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m9]; exact a8_120
  have a9_140 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m9]; exact a8_140
  have a9_160 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m9]; exact a8_160
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m9]; exact a8_180
  have a9_1a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m9]; exact a8_1a0
  have a9_1c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m9]; exact a8_1c0
  have a9_1e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m9]; exact a8_1e0
  have a9_260 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m9]; exact a8_260
  have a9_2e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m9]; exact a8_2e0
  have a9_960 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m9]; exact a8_960
  have a9_980 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m9]; exact a8_980
  have a9_9a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m9]; exact a8_9a0
  have a9_9c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m9]; exact a8_9c0
  have a9_9e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m9]; exact a8_9e0
  have a9_ce0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m9]; exact a8_ce0
  have a9_1044 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m9]; exact a8_1044
  have a9_10c4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m9]; exact a8_10c4
  have p9_200 : ptF n9.mem B 0x200 = P0 := by rw [m9]; exact p8_200
  have p9_280 : ptF n9.mem B 0x280 = P1 := by rw [m9]; exact p8_280
  have p9_900 : ptF n9.mem B 0x900 = P0 := by rw [m9]; exact p8_900
  have p9_fe4 : ptF n9.mem B 0xFE4 = P0 := by rw [m9]; exact p8_fe4
  have p9_1064 : ptF n9.mem B 0x1064 = P1 := by rw [m9]; exact p8_1064
  clear p8_1064 p8_fe4 p8_900 p8_280 p8_200 a8_10c4 a8_1044 a8_ce0 a8_9e0 a8_9c0 a8_9a0 a8_980 a8_960 a8_2e0 a8_260 a8_1e0 a8_1c0 a8_1a0 a8_180 a8_160 a8_140 a8_120 q8_c80 g8_9 g8_8 g8_27 g8_26 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x776
  obtain ⟨n10, c10, u10⟩ := s9.block p2vEcT0a776 E9.self p2vEcT0a776_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem P2V n10 0x77E (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock p2vEcT0a776 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_8 : reg n10 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCE0 := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = rem := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0xCE0 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g10_11 : reg n10 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g10_12 : reg n10 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0x900, 0x80), (0xC80, 0x60)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have q10_c80 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m10]; exact q9_c80 j hj
  have a10_120 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m10]; exact a9_120
  have a10_140 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m10]; exact a9_140
  have a10_160 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m10]; exact a9_160
  have a10_180 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m10]; exact a9_180
  have a10_1a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m10]; exact a9_1a0
  have a10_1c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m10]; exact a9_1c0
  have a10_1e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m10]; exact a9_1e0
  have a10_260 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m10]; exact a9_260
  have a10_2e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m10]; exact a9_2e0
  have a10_960 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m10]; exact a9_960
  have a10_980 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m10]; exact a9_980
  have a10_9a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m10]; exact a9_9a0
  have a10_9c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m10]; exact a9_9c0
  have a10_9e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m10]; exact a9_9e0
  have a10_ce0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCE0) 8 = psmVal ((rv) * (wv)) := by rw [m10]; exact a9_ce0
  have a10_1044 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m10]; exact a9_1044
  have a10_10c4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m10]; exact a9_10c4
  have p10_200 : ptF n10.mem B 0x200 = P0 := by rw [m10]; exact p9_200
  have p10_280 : ptF n10.mem B 0x280 = P1 := by rw [m10]; exact p9_280
  have p10_900 : ptF n10.mem B 0x900 = P0 := by rw [m10]; exact p9_900
  have p10_fe4 : ptF n10.mem B 0xFE4 = P0 := by rw [m10]; exact p9_fe4
  have p10_1064 : ptF n10.mem B 0x1064 = P1 := by rw [m10]; exact p9_1064
  clear p9_1064 p9_fe4 p9_900 p9_280 p9_200 a9_10c4 a9_1044 a9_ce0 a9_9e0 a9_9c0 a9_9a0 a9_980 a9_960 a9_2e0 a9_260 a9_1e0 a9_1c0 a9_1a0 a9_180 a9_160 a9_140 a9_120 q9_c80 g9_27 g9_26 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x77E: memcpy from outside the stack
  obtain ⟨n11, P11, K11, X11⟩ := p2v_mcRo2 (c := 0xCE0) (N := 0x60) F RS E10 s10 p2v_at_77e p2v_at_782
    (by decide) (by decide) g10_2 g10_10 g10_11 g10_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s11 := P11.st
  have fr11 := P11.fr
  have t11 : Steps n0 n11 := t10.trans P11.steps
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [P11.regs sp (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P11.regs (3 : Fin 32) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P11.regs (4 : Fin 32) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCE0 := by rw [P11.regs (8 : Fin 32) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P11.regs (9 : Fin 32) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P11.regs (18 : Fin 32) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P11.regs (19 : Fin 32) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P11.regs (20 : Fin 32) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P11.regs (21 : Fin 32) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P11.regs (22 : Fin 32) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P11.regs (23 : Fin 32) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = rem := by rw [P11.regs (24 : Fin 32) (by decide), g10_24]
  have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P11.regs (26 : Fin 32) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P11.regs (27 : Fin 32) (by decide), g10_27]
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have q11_c80 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_c80 j hj)
  have a11_120 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K11.acc (by decide) (by decide)).trans a10_120
  have a11_140 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K11.acc (by decide) (by decide)).trans a10_140
  have a11_160 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K11.acc (by decide) (by decide)).trans a10_160
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K11.acc (by decide) (by decide)).trans a10_180
  have a11_1a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K11.acc (by decide) (by decide)).trans a10_1a0
  have a11_1c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K11.acc (by decide) (by decide)).trans a10_1c0
  have a11_1e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K11.acc (by decide) (by decide)).trans a10_1e0
  have a11_260 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K11.acc (by decide) (by decide)).trans a10_260
  have a11_2e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K11.acc (by decide) (by decide)).trans a10_2e0
  have a11_960 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (K11.acc (by decide) (by decide)).trans a10_960
  have a11_980 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K11.acc (by decide) (by decide)).trans a10_980
  have a11_9a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K11.acc (by decide) (by decide)).trans a10_9a0
  have a11_9c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K11.acc (by decide) (by decide)).trans a10_9c0
  have a11_9e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K11.acc (by decide) (by decide)).trans a10_9e0
  have a11_1044 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K11.acc (by decide) (by decide)).trans a10_1044
  have a11_10c4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K11.acc (by decide) (by decide)).trans a10_10c4
  have p11_200 : ptF n11.mem B 0x200 = P0 := (K11.pt (by decide) (by decide)).trans p10_200
  have p11_280 : ptF n11.mem B 0x280 = P1 := (K11.pt (by decide) (by decide)).trans p10_280
  have p11_900 : ptF n11.mem B 0x900 = P0 := (K11.pt (by decide) (by decide)).trans p10_900
  have p11_fe4 : ptF n11.mem B 0xFE4 = P0 := (K11.pt (by decide) (by decide)).trans p10_fe4
  have p11_1064 : ptF n11.mem B 0x1064 = P1 := (K11.pt (by decide) (by decide)).trans p10_1064
  have q11_ce0 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X11 j hj).trans (fR10 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p10_1064 p10_fe4 p10_900 p10_280 p10_200 a10_10c4 a10_1044 a10_ce0 a10_9e0 a10_9c0 a10_9a0 a10_980 a10_960 a10_2e0 a10_260 a10_1e0 a10_1c0 a10_1a0 a10_180 a10_160 a10_140 a10_120 q10_c80 g10_12 g10_11 g10_10 g10_27 g10_26 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x786
  obtain ⟨n12, c12, u12⟩ := s11.block p2vEcT0a786 E11.self p2vEcT0a786_end
    ⟨trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem P2V n12 0x78C (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock p2vEcT0a786 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_18 : reg n12 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = rem := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_8 : reg n12 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xD40 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g12_9 : reg n12 (9 : Fin 32) = BitVec.ofNat 32 0x6 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have q12_c80 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_c80 j hj
  have q12_ce0 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_ce0 j hj
  have a12_120 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m12]; exact a11_120
  have a12_140 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m12]; exact a11_140
  have a12_160 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m12]; exact a11_160
  have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m12]; exact a11_180
  have a12_1a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m12]; exact a11_1a0
  have a12_1c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m12]; exact a11_1c0
  have a12_1e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m12]; exact a11_1e0
  have a12_260 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m12]; exact a11_260
  have a12_2e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m12]; exact a11_2e0
  have a12_960 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m12]; exact a11_960
  have a12_980 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m12]; exact a11_980
  have a12_9a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m12]; exact a11_9a0
  have a12_9c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m12]; exact a11_9c0
  have a12_9e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m12]; exact a11_9e0
  have a12_1044 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m12]; exact a11_1044
  have a12_10c4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m12]; exact a11_10c4
  have p12_200 : ptF n12.mem B 0x200 = P0 := by rw [m12]; exact p11_200
  have p12_280 : ptF n12.mem B 0x280 = P1 := by rw [m12]; exact p11_280
  have p12_900 : ptF n12.mem B 0x900 = P0 := by rw [m12]; exact p11_900
  have p12_fe4 : ptF n12.mem B 0xFE4 = P0 := by rw [m12]; exact p11_fe4
  have p12_1064 : ptF n12.mem B 0x1064 = P1 := by rw [m12]; exact p11_1064
  clear q11_ce0 p11_1064 p11_fe4 p11_900 p11_280 p11_200 a11_10c4 a11_1044 a11_9e0 a11_9c0 a11_9a0 a11_980 a11_960 a11_2e0 a11_260 a11_1e0 a11_1c0 a11_1a0 a11_180 a11_160 a11_140 a11_120 q11_c80 g11_27 g11_26 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 s11 X11 K11 P11
  -- 0x78C: branch, taken
  obtain ⟨n13, d13, u13⟩ := s12.taken E12.self 0x776 p2v_at_78c
    (by decide) (by rw [g12_9, s12.zero]; decide)
  have s13 : St n13.mem P2V n13 0x776 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, P2vR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, P2vR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : P2vCode n13.mem := E12.fr F fr13
  have V13 : P2vSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xD40 := by rw [u13.regs, g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = BitVec.ofNat 32 0x6 := by rw [u13.regs, g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u13.regs, g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u13.regs, g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u13.regs, g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u13.regs, g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u13.regs, g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u13.regs, g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = rem := by rw [u13.regs, g12_24]
  have g13_26 : reg n13 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u13.regs, g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u13.regs, g12_27]
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have q13_c80 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_c80 j hj
  have q13_ce0 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_ce0 j hj
  have a13_120 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m13]; exact a12_120
  have a13_140 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m13]; exact a12_140
  have a13_160 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m13]; exact a12_160
  have a13_180 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m13]; exact a12_180
  have a13_1a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m13]; exact a12_1a0
  have a13_1c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m13]; exact a12_1c0
  have a13_1e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m13]; exact a12_1e0
  have a13_260 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m13]; exact a12_260
  have a13_2e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m13]; exact a12_2e0
  have a13_960 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m13]; exact a12_960
  have a13_980 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m13]; exact a12_980
  have a13_9a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m13]; exact a12_9a0
  have a13_9c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m13]; exact a12_9c0
  have a13_9e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m13]; exact a12_9e0
  have a13_1044 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m13]; exact a12_1044
  have a13_10c4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m13]; exact a12_10c4
  have p13_200 : ptF n13.mem B 0x200 = P0 := by rw [m13]; exact p12_200
  have p13_280 : ptF n13.mem B 0x280 = P1 := by rw [m13]; exact p12_280
  have p13_900 : ptF n13.mem B 0x900 = P0 := by rw [m13]; exact p12_900
  have p13_fe4 : ptF n13.mem B 0xFE4 = P0 := by rw [m13]; exact p12_fe4
  have p13_1064 : ptF n13.mem B 0x1064 = P1 := by rw [m13]; exact p12_1064
  clear p12_1064 p12_fe4 p12_900 p12_280 p12_200 a12_10c4 a12_1044 a12_9e0 a12_9c0 a12_9a0 a12_980 a12_960 a12_2e0 a12_260 a12_1e0 a12_1c0 a12_1a0 a12_180 a12_160 a12_140 a12_120 q12_ce0 q12_c80 g12_9 g12_8 g12_27 g12_26 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x776
  obtain ⟨n14, c14, u14⟩ := s13.block p2vEcT0a776 E13.self p2vEcT0a776_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem P2V n14 0x77E (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock p2vEcT0a776 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_8 : reg n14 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xD40 := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = BitVec.ofNat 32 0x6 := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = rem := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_26 : reg n14 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0xD40 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_12 : reg n14 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have q14_c80 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m14]; exact q13_c80 j hj
  have q14_ce0 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m14]; exact q13_ce0 j hj
  have a14_120 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m14]; exact a13_120
  have a14_140 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m14]; exact a13_140
  have a14_160 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m14]; exact a13_160
  have a14_180 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m14]; exact a13_180
  have a14_1a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m14]; exact a13_1a0
  have a14_1c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m14]; exact a13_1c0
  have a14_1e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m14]; exact a13_1e0
  have a14_260 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m14]; exact a13_260
  have a14_2e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m14]; exact a13_2e0
  have a14_960 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m14]; exact a13_960
  have a14_980 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m14]; exact a13_980
  have a14_9a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m14]; exact a13_9a0
  have a14_9c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m14]; exact a13_9c0
  have a14_9e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m14]; exact a13_9e0
  have a14_1044 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m14]; exact a13_1044
  have a14_10c4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m14]; exact a13_10c4
  have p14_200 : ptF n14.mem B 0x200 = P0 := by rw [m14]; exact p13_200
  have p14_280 : ptF n14.mem B 0x280 = P1 := by rw [m14]; exact p13_280
  have p14_900 : ptF n14.mem B 0x900 = P0 := by rw [m14]; exact p13_900
  have p14_fe4 : ptF n14.mem B 0xFE4 = P0 := by rw [m14]; exact p13_fe4
  have p14_1064 : ptF n14.mem B 0x1064 = P1 := by rw [m14]; exact p13_1064
  clear p13_1064 p13_fe4 p13_900 p13_280 p13_200 a13_10c4 a13_1044 a13_9e0 a13_9c0 a13_9a0 a13_980 a13_960 a13_2e0 a13_260 a13_1e0 a13_1c0 a13_1a0 a13_180 a13_160 a13_140 a13_120 q13_ce0 q13_c80 g13_27 g13_26 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0x77E: memcpy from outside the stack
  obtain ⟨n15, P15, K15, X15⟩ := p2v_mcRo2 (c := 0xD40) (N := 0x60) F RS E14 s14 p2v_at_77e p2v_at_782
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
  have g15_8 : reg n15 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xD40 := by rw [P15.regs (8 : Fin 32) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = BitVec.ofNat 32 0x6 := by rw [P15.regs (9 : Fin 32) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P15.regs (18 : Fin 32) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P15.regs (19 : Fin 32) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P15.regs (20 : Fin 32) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P15.regs (21 : Fin 32) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P15.regs (22 : Fin 32) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P15.regs (23 : Fin 32) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = rem := by rw [P15.regs (24 : Fin 32) (by decide), g14_24]
  have g15_26 : reg n15 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P15.regs (26 : Fin 32) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P15.regs (27 : Fin 32) (by decide), g14_27]
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have q15_c80 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_c80 j hj)
  have q15_ce0 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_ce0 j hj)
  have a15_120 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K15.acc (by decide) (by decide)).trans a14_120
  have a15_140 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K15.acc (by decide) (by decide)).trans a14_140
  have a15_160 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K15.acc (by decide) (by decide)).trans a14_160
  have a15_180 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K15.acc (by decide) (by decide)).trans a14_180
  have a15_1a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K15.acc (by decide) (by decide)).trans a14_1a0
  have a15_1c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K15.acc (by decide) (by decide)).trans a14_1c0
  have a15_1e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K15.acc (by decide) (by decide)).trans a14_1e0
  have a15_260 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K15.acc (by decide) (by decide)).trans a14_260
  have a15_2e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K15.acc (by decide) (by decide)).trans a14_2e0
  have a15_960 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (K15.acc (by decide) (by decide)).trans a14_960
  have a15_980 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K15.acc (by decide) (by decide)).trans a14_980
  have a15_9a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K15.acc (by decide) (by decide)).trans a14_9a0
  have a15_9c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K15.acc (by decide) (by decide)).trans a14_9c0
  have a15_9e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K15.acc (by decide) (by decide)).trans a14_9e0
  have a15_1044 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K15.acc (by decide) (by decide)).trans a14_1044
  have a15_10c4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K15.acc (by decide) (by decide)).trans a14_10c4
  have p15_200 : ptF n15.mem B 0x200 = P0 := (K15.pt (by decide) (by decide)).trans p14_200
  have p15_280 : ptF n15.mem B 0x280 = P1 := (K15.pt (by decide) (by decide)).trans p14_280
  have p15_900 : ptF n15.mem B 0x900 = P0 := (K15.pt (by decide) (by decide)).trans p14_900
  have p15_fe4 : ptF n15.mem B 0xFE4 = P0 := (K15.pt (by decide) (by decide)).trans p14_fe4
  have p15_1064 : ptF n15.mem B 0x1064 = P1 := (K15.pt (by decide) (by decide)).trans p14_1064
  have q15_d40 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X15 j hj).trans (fR14 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p14_1064 p14_fe4 p14_900 p14_280 p14_200 a14_10c4 a14_1044 a14_9e0 a14_9c0 a14_9a0 a14_980 a14_960 a14_2e0 a14_260 a14_1e0 a14_1c0 a14_1a0 a14_180 a14_160 a14_140 a14_120 q14_ce0 q14_c80 g14_12 g14_11 g14_10 g14_27 g14_26 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0x786
  obtain ⟨n16, c16, u16⟩ := s15.block p2vEcT0a786 E15.self p2vEcT0a786_end
    ⟨trivial, trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem P2V n16 0x78C (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock p2vEcT0a786 (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
  have fr16 : ∀ x, P2vR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by
    rw [rb16, runBlock_reg _ _ _ sp s15.zero (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (3 : Fin 32) s15.zero (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (4 : Fin 32) s15.zero (by decide), g15_4]
  have g16_18 : reg n16 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = rem := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
  have g16_8 : reg n16 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xDA0 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_9, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g16_9 : reg n16 (9 : Fin 32) = BitVec.ofNat 32 0x5 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_9, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have q16_c80 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m16]; exact q15_c80 j hj
  have q16_ce0 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m16]; exact q15_ce0 j hj
  have q16_d40 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m16]; exact q15_d40 j hj
  have a16_120 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m16]; exact a15_120
  have a16_140 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m16]; exact a15_140
  have a16_160 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m16]; exact a15_160
  have a16_180 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m16]; exact a15_180
  have a16_1a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m16]; exact a15_1a0
  have a16_1c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m16]; exact a15_1c0
  have a16_1e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m16]; exact a15_1e0
  have a16_260 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m16]; exact a15_260
  have a16_2e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m16]; exact a15_2e0
  have a16_960 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m16]; exact a15_960
  have a16_980 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m16]; exact a15_980
  have a16_9a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m16]; exact a15_9a0
  have a16_9c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m16]; exact a15_9c0
  have a16_9e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m16]; exact a15_9e0
  have a16_1044 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m16]; exact a15_1044
  have a16_10c4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m16]; exact a15_10c4
  have p16_200 : ptF n16.mem B 0x200 = P0 := by rw [m16]; exact p15_200
  have p16_280 : ptF n16.mem B 0x280 = P1 := by rw [m16]; exact p15_280
  have p16_900 : ptF n16.mem B 0x900 = P0 := by rw [m16]; exact p15_900
  have p16_fe4 : ptF n16.mem B 0xFE4 = P0 := by rw [m16]; exact p15_fe4
  have p16_1064 : ptF n16.mem B 0x1064 = P1 := by rw [m16]; exact p15_1064
  clear q15_d40 p15_1064 p15_fe4 p15_900 p15_280 p15_200 a15_10c4 a15_1044 a15_9e0 a15_9c0 a15_9a0 a15_980 a15_960 a15_2e0 a15_260 a15_1e0 a15_1c0 a15_1a0 a15_180 a15_160 a15_140 a15_120 q15_ce0 q15_c80 g15_27 g15_26 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 s15 X15 K15 P15
  -- 0x78C: branch, taken
  obtain ⟨n17, d17, u17⟩ := s16.taken E16.self 0x776 p2v_at_78c
    (by decide) (by rw [g16_9, s16.zero]; decide)
  have s17 : St n17.mem P2V n17 0x776 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, P2vR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, P2vR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : P2vCode n17.mem := E16.fr F fr17
  have V17 : P2vSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xDA0 := by rw [u17.regs, g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = BitVec.ofNat 32 0x5 := by rw [u17.regs, g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u17.regs, g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u17.regs, g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u17.regs, g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u17.regs, g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u17.regs, g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u17.regs, g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = rem := by rw [u17.regs, g16_24]
  have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u17.regs, g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u17.regs, g16_27]
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have q17_c80 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_c80 j hj
  have q17_ce0 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_ce0 j hj
  have q17_d40 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_d40 j hj
  have a17_120 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m17]; exact a16_120
  have a17_140 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m17]; exact a16_140
  have a17_160 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m17]; exact a16_160
  have a17_180 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m17]; exact a16_180
  have a17_1a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m17]; exact a16_1a0
  have a17_1c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m17]; exact a16_1c0
  have a17_1e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m17]; exact a16_1e0
  have a17_260 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m17]; exact a16_260
  have a17_2e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m17]; exact a16_2e0
  have a17_960 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m17]; exact a16_960
  have a17_980 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m17]; exact a16_980
  have a17_9a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m17]; exact a16_9a0
  have a17_9c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m17]; exact a16_9c0
  have a17_9e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m17]; exact a16_9e0
  have a17_1044 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m17]; exact a16_1044
  have a17_10c4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m17]; exact a16_10c4
  have p17_200 : ptF n17.mem B 0x200 = P0 := by rw [m17]; exact p16_200
  have p17_280 : ptF n17.mem B 0x280 = P1 := by rw [m17]; exact p16_280
  have p17_900 : ptF n17.mem B 0x900 = P0 := by rw [m17]; exact p16_900
  have p17_fe4 : ptF n17.mem B 0xFE4 = P0 := by rw [m17]; exact p16_fe4
  have p17_1064 : ptF n17.mem B 0x1064 = P1 := by rw [m17]; exact p16_1064
  clear p16_1064 p16_fe4 p16_900 p16_280 p16_200 a16_10c4 a16_1044 a16_9e0 a16_9c0 a16_9a0 a16_980 a16_960 a16_2e0 a16_260 a16_1e0 a16_1c0 a16_1a0 a16_180 a16_160 a16_140 a16_120 q16_d40 q16_ce0 q16_c80 g16_9 g16_8 g16_27 g16_26 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  -- 0x776
  obtain ⟨n18, c18, u18⟩ := s17.block p2vEcT0a776 E17.self p2vEcT0a776_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem P2V n18 0x77E (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock p2vEcT0a776 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
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
  have g18_8 : reg n18 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xDA0 := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = BitVec.ofNat 32 0x5 := by
    rw [rb18, runBlock_reg _ _ _ (9 : Fin 32) s17.zero (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb18, runBlock_reg _ _ _ (20 : Fin 32) s17.zero (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb18, runBlock_reg _ _ _ (22 : Fin 32) s17.zero (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = rem := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_26 : reg n18 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0xDA0 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g18_12 : reg n18 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk18 : P2vKeepL B n0.mem n18.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have q18_c80 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_c80 j hj
  have q18_ce0 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_ce0 j hj
  have q18_d40 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_d40 j hj
  have a18_120 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m18]; exact a17_120
  have a18_140 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m18]; exact a17_140
  have a18_160 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m18]; exact a17_160
  have a18_180 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m18]; exact a17_180
  have a18_1a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m18]; exact a17_1a0
  have a18_1c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m18]; exact a17_1c0
  have a18_1e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m18]; exact a17_1e0
  have a18_260 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m18]; exact a17_260
  have a18_2e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m18]; exact a17_2e0
  have a18_960 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m18]; exact a17_960
  have a18_980 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m18]; exact a17_980
  have a18_9a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m18]; exact a17_9a0
  have a18_9c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m18]; exact a17_9c0
  have a18_9e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m18]; exact a17_9e0
  have a18_1044 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m18]; exact a17_1044
  have a18_10c4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m18]; exact a17_10c4
  have p18_200 : ptF n18.mem B 0x200 = P0 := by rw [m18]; exact p17_200
  have p18_280 : ptF n18.mem B 0x280 = P1 := by rw [m18]; exact p17_280
  have p18_900 : ptF n18.mem B 0x900 = P0 := by rw [m18]; exact p17_900
  have p18_fe4 : ptF n18.mem B 0xFE4 = P0 := by rw [m18]; exact p17_fe4
  have p18_1064 : ptF n18.mem B 0x1064 = P1 := by rw [m18]; exact p17_1064
  clear p17_1064 p17_fe4 p17_900 p17_280 p17_200 a17_10c4 a17_1044 a17_9e0 a17_9c0 a17_9a0 a17_980 a17_960 a17_2e0 a17_260 a17_1e0 a17_1c0 a17_1a0 a17_180 a17_160 a17_140 a17_120 q17_d40 q17_ce0 q17_c80 g17_27 g17_26 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x77E: memcpy from outside the stack
  obtain ⟨n19, P19, K19, X19⟩ := p2v_mcRo2 (c := 0xDA0) (N := 0x60) F RS E18 s18 p2v_at_77e p2v_at_782
    (by decide) (by decide) g18_2 g18_10 g18_11 g18_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s19 := P19.st
  have fr19 := P19.fr
  have t19 : Steps n0 n19 := t18.trans P19.steps
  have fR19 : ∀ x, P2vR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : P2vCode n19.mem := E18.fr F fr19
  have V19 : P2vSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [P19.regs sp (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P19.regs (3 : Fin 32) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P19.regs (4 : Fin 32) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xDA0 := by rw [P19.regs (8 : Fin 32) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = BitVec.ofNat 32 0x5 := by rw [P19.regs (9 : Fin 32) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P19.regs (18 : Fin 32) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P19.regs (19 : Fin 32) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P19.regs (20 : Fin 32) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P19.regs (21 : Fin 32) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P19.regs (22 : Fin 32) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P19.regs (23 : Fin 32) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = rem := by rw [P19.regs (24 : Fin 32) (by decide), g18_24]
  have g19_26 : reg n19 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P19.regs (26 : Fin 32) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P19.regs (27 : Fin 32) (by decide), g18_27]
  have keep_kk19 : P2vKeepL B n0.mem n19.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60)] := keep_kk18.trans K19.toL
  clear keep_kk18
  have q19_c80 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_c80 j hj)
  have q19_ce0 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_ce0 j hj)
  have q19_d40 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K19.range (by decide) (by decide) j hj).trans (q18_d40 j hj)
  have a19_120 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K19.acc (by decide) (by decide)).trans a18_120
  have a19_140 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K19.acc (by decide) (by decide)).trans a18_140
  have a19_160 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K19.acc (by decide) (by decide)).trans a18_160
  have a19_180 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K19.acc (by decide) (by decide)).trans a18_180
  have a19_1a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K19.acc (by decide) (by decide)).trans a18_1a0
  have a19_1c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K19.acc (by decide) (by decide)).trans a18_1c0
  have a19_1e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K19.acc (by decide) (by decide)).trans a18_1e0
  have a19_260 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K19.acc (by decide) (by decide)).trans a18_260
  have a19_2e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K19.acc (by decide) (by decide)).trans a18_2e0
  have a19_960 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (K19.acc (by decide) (by decide)).trans a18_960
  have a19_980 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K19.acc (by decide) (by decide)).trans a18_980
  have a19_9a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K19.acc (by decide) (by decide)).trans a18_9a0
  have a19_9c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K19.acc (by decide) (by decide)).trans a18_9c0
  have a19_9e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K19.acc (by decide) (by decide)).trans a18_9e0
  have a19_1044 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K19.acc (by decide) (by decide)).trans a18_1044
  have a19_10c4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K19.acc (by decide) (by decide)).trans a18_10c4
  have p19_200 : ptF n19.mem B 0x200 = P0 := (K19.pt (by decide) (by decide)).trans p18_200
  have p19_280 : ptF n19.mem B 0x280 = P1 := (K19.pt (by decide) (by decide)).trans p18_280
  have p19_900 : ptF n19.mem B 0x900 = P0 := (K19.pt (by decide) (by decide)).trans p18_900
  have p19_fe4 : ptF n19.mem B 0xFE4 = P0 := (K19.pt (by decide) (by decide)).trans p18_fe4
  have p19_1064 : ptF n19.mem B 0x1064 = P1 := (K19.pt (by decide) (by decide)).trans p18_1064
  have q19_da0 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X19 j hj).trans (fR18 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p18_1064 p18_fe4 p18_900 p18_280 p18_200 a18_10c4 a18_1044 a18_9e0 a18_9c0 a18_9a0 a18_980 a18_960 a18_2e0 a18_260 a18_1e0 a18_1c0 a18_1a0 a18_180 a18_160 a18_140 a18_120 q18_d40 q18_ce0 q18_c80 g18_12 g18_11 g18_10 g18_27 g18_26 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0x786
  obtain ⟨n20, c20, u20⟩ := s19.block p2vEcT0a786 E19.self p2vEcT0a786_end
    ⟨trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem P2V n20 0x78C (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock p2vEcT0a786 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_18 : reg n20 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = rem := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_26 : reg n20 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_8 : reg n20 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xE00 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g20_9 : reg n20 (9 : Fin 32) = BitVec.ofNat 32 0x4 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk20 : P2vKeepL B n0.mem n20.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have q20_c80 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_c80 j hj
  have q20_ce0 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_ce0 j hj
  have q20_d40 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_d40 j hj
  have q20_da0 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_da0 j hj
  have a20_120 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m20]; exact a19_120
  have a20_140 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m20]; exact a19_140
  have a20_160 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m20]; exact a19_160
  have a20_180 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m20]; exact a19_180
  have a20_1a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m20]; exact a19_1a0
  have a20_1c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m20]; exact a19_1c0
  have a20_1e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m20]; exact a19_1e0
  have a20_260 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m20]; exact a19_260
  have a20_2e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m20]; exact a19_2e0
  have a20_960 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m20]; exact a19_960
  have a20_980 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m20]; exact a19_980
  have a20_9a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m20]; exact a19_9a0
  have a20_9c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m20]; exact a19_9c0
  have a20_9e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m20]; exact a19_9e0
  have a20_1044 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m20]; exact a19_1044
  have a20_10c4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m20]; exact a19_10c4
  have p20_200 : ptF n20.mem B 0x200 = P0 := by rw [m20]; exact p19_200
  have p20_280 : ptF n20.mem B 0x280 = P1 := by rw [m20]; exact p19_280
  have p20_900 : ptF n20.mem B 0x900 = P0 := by rw [m20]; exact p19_900
  have p20_fe4 : ptF n20.mem B 0xFE4 = P0 := by rw [m20]; exact p19_fe4
  have p20_1064 : ptF n20.mem B 0x1064 = P1 := by rw [m20]; exact p19_1064
  clear q19_da0 p19_1064 p19_fe4 p19_900 p19_280 p19_200 a19_10c4 a19_1044 a19_9e0 a19_9c0 a19_9a0 a19_980 a19_960 a19_2e0 a19_260 a19_1e0 a19_1c0 a19_1a0 a19_180 a19_160 a19_140 a19_120 q19_d40 q19_ce0 q19_c80 g19_27 g19_26 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 s19 X19 K19 P19
  -- 0x78C: branch, taken
  obtain ⟨n21, d21, u21⟩ := s20.taken E20.self 0x776 p2v_at_78c
    (by decide) (by rw [g20_9, s20.zero]; decide)
  have s21 : St n21.mem P2V n21 0x776 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, P2vR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, P2vR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : P2vCode n21.mem := E20.fr F fr21
  have V21 : P2vSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xE00 := by rw [u21.regs, g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = BitVec.ofNat 32 0x4 := by rw [u21.regs, g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u21.regs, g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u21.regs, g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u21.regs, g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u21.regs, g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u21.regs, g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u21.regs, g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = rem := by rw [u21.regs, g20_24]
  have g21_26 : reg n21 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u21.regs, g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u21.regs, g20_27]
  have keep_kk21 : P2vKeepL B n0.mem n21.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have q21_c80 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_c80 j hj
  have q21_ce0 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_ce0 j hj
  have q21_d40 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_d40 j hj
  have q21_da0 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_da0 j hj
  have a21_120 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m21]; exact a20_120
  have a21_140 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m21]; exact a20_140
  have a21_160 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m21]; exact a20_160
  have a21_180 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m21]; exact a20_180
  have a21_1a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m21]; exact a20_1a0
  have a21_1c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m21]; exact a20_1c0
  have a21_1e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m21]; exact a20_1e0
  have a21_260 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m21]; exact a20_260
  have a21_2e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m21]; exact a20_2e0
  have a21_960 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m21]; exact a20_960
  have a21_980 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m21]; exact a20_980
  have a21_9a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m21]; exact a20_9a0
  have a21_9c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m21]; exact a20_9c0
  have a21_9e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m21]; exact a20_9e0
  have a21_1044 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m21]; exact a20_1044
  have a21_10c4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m21]; exact a20_10c4
  have p21_200 : ptF n21.mem B 0x200 = P0 := by rw [m21]; exact p20_200
  have p21_280 : ptF n21.mem B 0x280 = P1 := by rw [m21]; exact p20_280
  have p21_900 : ptF n21.mem B 0x900 = P0 := by rw [m21]; exact p20_900
  have p21_fe4 : ptF n21.mem B 0xFE4 = P0 := by rw [m21]; exact p20_fe4
  have p21_1064 : ptF n21.mem B 0x1064 = P1 := by rw [m21]; exact p20_1064
  clear p20_1064 p20_fe4 p20_900 p20_280 p20_200 a20_10c4 a20_1044 a20_9e0 a20_9c0 a20_9a0 a20_980 a20_960 a20_2e0 a20_260 a20_1e0 a20_1c0 a20_1a0 a20_180 a20_160 a20_140 a20_120 q20_da0 q20_d40 q20_ce0 q20_c80 g20_9 g20_8 g20_27 g20_26 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x776
  obtain ⟨n22, c22, u22⟩ := s21.block p2vEcT0a776 E21.self p2vEcT0a776_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem P2V n22 0x77E (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock p2vEcT0a776 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
  have g22_8 : reg n22 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xE00 := by
    rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = BitVec.ofNat 32 0x4 := by
    rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = rem := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_26 : reg n22 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_10 : reg n22 a0 = B + 0x21A0 + BitVec.ofNat 32 0xE00 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g22_11 : reg n22 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g22_12 : reg n22 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have q22_c80 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m22]; exact q21_c80 j hj
  have q22_ce0 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m22]; exact q21_ce0 j hj
  have q22_d40 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m22]; exact q21_d40 j hj
  have q22_da0 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m22]; exact q21_da0 j hj
  have a22_120 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m22]; exact a21_120
  have a22_140 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m22]; exact a21_140
  have a22_160 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m22]; exact a21_160
  have a22_180 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m22]; exact a21_180
  have a22_1a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m22]; exact a21_1a0
  have a22_1c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m22]; exact a21_1c0
  have a22_1e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m22]; exact a21_1e0
  have a22_260 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m22]; exact a21_260
  have a22_2e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m22]; exact a21_2e0
  have a22_960 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m22]; exact a21_960
  have a22_980 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m22]; exact a21_980
  have a22_9a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m22]; exact a21_9a0
  have a22_9c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m22]; exact a21_9c0
  have a22_9e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m22]; exact a21_9e0
  have a22_1044 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m22]; exact a21_1044
  have a22_10c4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m22]; exact a21_10c4
  have p22_200 : ptF n22.mem B 0x200 = P0 := by rw [m22]; exact p21_200
  have p22_280 : ptF n22.mem B 0x280 = P1 := by rw [m22]; exact p21_280
  have p22_900 : ptF n22.mem B 0x900 = P0 := by rw [m22]; exact p21_900
  have p22_fe4 : ptF n22.mem B 0xFE4 = P0 := by rw [m22]; exact p21_fe4
  have p22_1064 : ptF n22.mem B 0x1064 = P1 := by rw [m22]; exact p21_1064
  clear p21_1064 p21_fe4 p21_900 p21_280 p21_200 a21_10c4 a21_1044 a21_9e0 a21_9c0 a21_9a0 a21_980 a21_960 a21_2e0 a21_260 a21_1e0 a21_1c0 a21_1a0 a21_180 a21_160 a21_140 a21_120 q21_da0 q21_d40 q21_ce0 q21_c80 g21_27 g21_26 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0x77E: memcpy from outside the stack
  obtain ⟨n23, P23, K23, X23⟩ := p2v_mcRo2 (c := 0xE00) (N := 0x60) F RS E22 s22 p2v_at_77e p2v_at_782
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
  have g23_8 : reg n23 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xE00 := by rw [P23.regs (8 : Fin 32) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = BitVec.ofNat 32 0x4 := by rw [P23.regs (9 : Fin 32) (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P23.regs (18 : Fin 32) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P23.regs (19 : Fin 32) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P23.regs (20 : Fin 32) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P23.regs (21 : Fin 32) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P23.regs (22 : Fin 32) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P23.regs (23 : Fin 32) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = rem := by rw [P23.regs (24 : Fin 32) (by decide), g22_24]
  have g23_26 : reg n23 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P23.regs (26 : Fin 32) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P23.regs (27 : Fin 32) (by decide), g22_27]
  have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60)] := keep_kk22.trans K23.toL
  clear keep_kk22
  have q23_c80 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_c80 j hj)
  have q23_ce0 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_ce0 j hj)
  have q23_d40 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_d40 j hj)
  have q23_da0 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K23.range (by decide) (by decide) j hj).trans (q22_da0 j hj)
  have a23_120 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K23.acc (by decide) (by decide)).trans a22_120
  have a23_140 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K23.acc (by decide) (by decide)).trans a22_140
  have a23_160 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K23.acc (by decide) (by decide)).trans a22_160
  have a23_180 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K23.acc (by decide) (by decide)).trans a22_180
  have a23_1a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K23.acc (by decide) (by decide)).trans a22_1a0
  have a23_1c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K23.acc (by decide) (by decide)).trans a22_1c0
  have a23_1e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K23.acc (by decide) (by decide)).trans a22_1e0
  have a23_260 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K23.acc (by decide) (by decide)).trans a22_260
  have a23_2e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K23.acc (by decide) (by decide)).trans a22_2e0
  have a23_960 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (K23.acc (by decide) (by decide)).trans a22_960
  have a23_980 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K23.acc (by decide) (by decide)).trans a22_980
  have a23_9a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K23.acc (by decide) (by decide)).trans a22_9a0
  have a23_9c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K23.acc (by decide) (by decide)).trans a22_9c0
  have a23_9e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K23.acc (by decide) (by decide)).trans a22_9e0
  have a23_1044 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K23.acc (by decide) (by decide)).trans a22_1044
  have a23_10c4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K23.acc (by decide) (by decide)).trans a22_10c4
  have p23_200 : ptF n23.mem B 0x200 = P0 := (K23.pt (by decide) (by decide)).trans p22_200
  have p23_280 : ptF n23.mem B 0x280 = P1 := (K23.pt (by decide) (by decide)).trans p22_280
  have p23_900 : ptF n23.mem B 0x900 = P0 := (K23.pt (by decide) (by decide)).trans p22_900
  have p23_fe4 : ptF n23.mem B 0xFE4 = P0 := (K23.pt (by decide) (by decide)).trans p22_fe4
  have p23_1064 : ptF n23.mem B 0x1064 = P1 := (K23.pt (by decide) (by decide)).trans p22_1064
  have q23_e00 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X23 j hj).trans (fR22 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p22_1064 p22_fe4 p22_900 p22_280 p22_200 a22_10c4 a22_1044 a22_9e0 a22_9c0 a22_9a0 a22_980 a22_960 a22_2e0 a22_260 a22_1e0 a22_1c0 a22_1a0 a22_180 a22_160 a22_140 a22_120 q22_da0 q22_d40 q22_ce0 q22_c80 g22_12 g22_11 g22_10 g22_27 g22_26 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0x786
  obtain ⟨n24, c24, u24⟩ := s23.block p2vEcT0a786 E23.self p2vEcT0a786_end
    ⟨trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem P2V n24 0x78C (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock p2vEcT0a786 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_18 : reg n24 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb24, runBlock_reg _ _ _ (20 : Fin 32) s23.zero (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = rem := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_26 : reg n24 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_8 : reg n24 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xE60 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g24_9 : reg n24 (9 : Fin 32) = BitVec.ofNat 32 0x3 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk24 : P2vKeepL B n0.mem n24.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have q24_c80 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_c80 j hj
  have q24_ce0 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_ce0 j hj
  have q24_d40 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_d40 j hj
  have q24_da0 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_da0 j hj
  have q24_e00 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_e00 j hj
  have a24_120 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m24]; exact a23_120
  have a24_140 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m24]; exact a23_140
  have a24_160 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m24]; exact a23_160
  have a24_180 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m24]; exact a23_180
  have a24_1a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m24]; exact a23_1a0
  have a24_1c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m24]; exact a23_1c0
  have a24_1e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m24]; exact a23_1e0
  have a24_260 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m24]; exact a23_260
  have a24_2e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m24]; exact a23_2e0
  have a24_960 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m24]; exact a23_960
  have a24_980 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m24]; exact a23_980
  have a24_9a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m24]; exact a23_9a0
  have a24_9c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m24]; exact a23_9c0
  have a24_9e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m24]; exact a23_9e0
  have a24_1044 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m24]; exact a23_1044
  have a24_10c4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m24]; exact a23_10c4
  have p24_200 : ptF n24.mem B 0x200 = P0 := by rw [m24]; exact p23_200
  have p24_280 : ptF n24.mem B 0x280 = P1 := by rw [m24]; exact p23_280
  have p24_900 : ptF n24.mem B 0x900 = P0 := by rw [m24]; exact p23_900
  have p24_fe4 : ptF n24.mem B 0xFE4 = P0 := by rw [m24]; exact p23_fe4
  have p24_1064 : ptF n24.mem B 0x1064 = P1 := by rw [m24]; exact p23_1064
  clear q23_e00 p23_1064 p23_fe4 p23_900 p23_280 p23_200 a23_10c4 a23_1044 a23_9e0 a23_9c0 a23_9a0 a23_980 a23_960 a23_2e0 a23_260 a23_1e0 a23_1c0 a23_1a0 a23_180 a23_160 a23_140 a23_120 q23_da0 q23_d40 q23_ce0 q23_c80 g23_27 g23_26 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 s23 X23 K23 P23
  -- 0x78C: branch, taken
  obtain ⟨n25, d25, u25⟩ := s24.taken E24.self 0x776 p2v_at_78c
    (by decide) (by rw [g24_9, s24.zero]; decide)
  have s25 : St n25.mem P2V n25 0x776 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, P2vR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, P2vR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : P2vCode n25.mem := E24.fr F fr25
  have V25 : P2vSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xE60 := by rw [u25.regs, g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = BitVec.ofNat 32 0x3 := by rw [u25.regs, g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u25.regs, g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u25.regs, g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u25.regs, g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u25.regs, g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u25.regs, g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u25.regs, g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = rem := by rw [u25.regs, g24_24]
  have g25_26 : reg n25 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u25.regs, g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u25.regs, g24_27]
  have keep_kk25 : P2vKeepL B n0.mem n25.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have q25_c80 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_c80 j hj
  have q25_ce0 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_ce0 j hj
  have q25_d40 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_d40 j hj
  have q25_da0 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_da0 j hj
  have q25_e00 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_e00 j hj
  have a25_120 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m25]; exact a24_120
  have a25_140 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m25]; exact a24_140
  have a25_160 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m25]; exact a24_160
  have a25_180 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m25]; exact a24_180
  have a25_1a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m25]; exact a24_1a0
  have a25_1c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m25]; exact a24_1c0
  have a25_1e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m25]; exact a24_1e0
  have a25_260 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m25]; exact a24_260
  have a25_2e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m25]; exact a24_2e0
  have a25_960 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m25]; exact a24_960
  have a25_980 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m25]; exact a24_980
  have a25_9a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m25]; exact a24_9a0
  have a25_9c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m25]; exact a24_9c0
  have a25_9e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m25]; exact a24_9e0
  have a25_1044 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m25]; exact a24_1044
  have a25_10c4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m25]; exact a24_10c4
  have p25_200 : ptF n25.mem B 0x200 = P0 := by rw [m25]; exact p24_200
  have p25_280 : ptF n25.mem B 0x280 = P1 := by rw [m25]; exact p24_280
  have p25_900 : ptF n25.mem B 0x900 = P0 := by rw [m25]; exact p24_900
  have p25_fe4 : ptF n25.mem B 0xFE4 = P0 := by rw [m25]; exact p24_fe4
  have p25_1064 : ptF n25.mem B 0x1064 = P1 := by rw [m25]; exact p24_1064
  clear p24_1064 p24_fe4 p24_900 p24_280 p24_200 a24_10c4 a24_1044 a24_9e0 a24_9c0 a24_9a0 a24_980 a24_960 a24_2e0 a24_260 a24_1e0 a24_1c0 a24_1a0 a24_180 a24_160 a24_140 a24_120 q24_e00 q24_da0 q24_d40 q24_ce0 q24_c80 g24_9 g24_8 g24_27 g24_26 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x776
  obtain ⟨n26, c26, u26⟩ := s25.block p2vEcT0a776 E25.self p2vEcT0a776_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem P2V n26 0x77E (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock p2vEcT0a776 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
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
  have g26_8 : reg n26 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xE60 := by
    rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = BitVec.ofNat 32 0x3 := by
    rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = rem := by
    rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
  have g26_26 : reg n26 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
  have g26_10 : reg n26 a0 = B + 0x21A0 + BitVec.ofNat 32 0xE60 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g26_11 : reg n26 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g26_12 : reg n26 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk26 : P2vKeepL B n0.mem n26.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have q26_c80 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_c80 j hj
  have q26_ce0 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_ce0 j hj
  have q26_d40 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_d40 j hj
  have q26_da0 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_da0 j hj
  have q26_e00 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m26]; exact q25_e00 j hj
  have a26_120 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m26]; exact a25_120
  have a26_140 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m26]; exact a25_140
  have a26_160 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m26]; exact a25_160
  have a26_180 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m26]; exact a25_180
  have a26_1a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m26]; exact a25_1a0
  have a26_1c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m26]; exact a25_1c0
  have a26_1e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m26]; exact a25_1e0
  have a26_260 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m26]; exact a25_260
  have a26_2e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m26]; exact a25_2e0
  have a26_960 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m26]; exact a25_960
  have a26_980 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m26]; exact a25_980
  have a26_9a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m26]; exact a25_9a0
  have a26_9c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m26]; exact a25_9c0
  have a26_9e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m26]; exact a25_9e0
  have a26_1044 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m26]; exact a25_1044
  have a26_10c4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m26]; exact a25_10c4
  have p26_200 : ptF n26.mem B 0x200 = P0 := by rw [m26]; exact p25_200
  have p26_280 : ptF n26.mem B 0x280 = P1 := by rw [m26]; exact p25_280
  have p26_900 : ptF n26.mem B 0x900 = P0 := by rw [m26]; exact p25_900
  have p26_fe4 : ptF n26.mem B 0xFE4 = P0 := by rw [m26]; exact p25_fe4
  have p26_1064 : ptF n26.mem B 0x1064 = P1 := by rw [m26]; exact p25_1064
  clear p25_1064 p25_fe4 p25_900 p25_280 p25_200 a25_10c4 a25_1044 a25_9e0 a25_9c0 a25_9a0 a25_980 a25_960 a25_2e0 a25_260 a25_1e0 a25_1c0 a25_1a0 a25_180 a25_160 a25_140 a25_120 q25_e00 q25_da0 q25_d40 q25_ce0 q25_c80 g25_27 g25_26 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x77E: memcpy from outside the stack
  obtain ⟨n27, P27, K27, X27⟩ := p2v_mcRo2 (c := 0xE60) (N := 0x60) F RS E26 s26 p2v_at_77e p2v_at_782
    (by decide) (by decide) g26_2 g26_10 g26_11 g26_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s27 := P27.st
  have fr27 := P27.fr
  have t27 : Steps n0 n27 := t26.trans P27.steps
  have fR27 : ∀ x, P2vR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : P2vCode n27.mem := E26.fr F fr27
  have V27 : P2vSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [P27.regs sp (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P27.regs (3 : Fin 32) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P27.regs (4 : Fin 32) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xE60 := by rw [P27.regs (8 : Fin 32) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = BitVec.ofNat 32 0x3 := by rw [P27.regs (9 : Fin 32) (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P27.regs (18 : Fin 32) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P27.regs (19 : Fin 32) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P27.regs (20 : Fin 32) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P27.regs (21 : Fin 32) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P27.regs (22 : Fin 32) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P27.regs (23 : Fin 32) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = rem := by rw [P27.regs (24 : Fin 32) (by decide), g26_24]
  have g27_26 : reg n27 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P27.regs (26 : Fin 32) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P27.regs (27 : Fin 32) (by decide), g26_27]
  have keep_kk27 : P2vKeepL B n0.mem n27.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60)] := keep_kk26.trans K27.toL
  clear keep_kk26
  have q27_c80 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_c80 j hj)
  have q27_ce0 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_ce0 j hj)
  have q27_d40 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_d40 j hj)
  have q27_da0 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_da0 j hj)
  have q27_e00 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_e00 j hj)
  have a27_120 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K27.acc (by decide) (by decide)).trans a26_120
  have a27_140 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K27.acc (by decide) (by decide)).trans a26_140
  have a27_160 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K27.acc (by decide) (by decide)).trans a26_160
  have a27_180 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K27.acc (by decide) (by decide)).trans a26_180
  have a27_1a0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K27.acc (by decide) (by decide)).trans a26_1a0
  have a27_1c0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K27.acc (by decide) (by decide)).trans a26_1c0
  have a27_1e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K27.acc (by decide) (by decide)).trans a26_1e0
  have a27_260 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K27.acc (by decide) (by decide)).trans a26_260
  have a27_2e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K27.acc (by decide) (by decide)).trans a26_2e0
  have a27_960 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (K27.acc (by decide) (by decide)).trans a26_960
  have a27_980 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K27.acc (by decide) (by decide)).trans a26_980
  have a27_9a0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K27.acc (by decide) (by decide)).trans a26_9a0
  have a27_9c0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K27.acc (by decide) (by decide)).trans a26_9c0
  have a27_9e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K27.acc (by decide) (by decide)).trans a26_9e0
  have a27_1044 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K27.acc (by decide) (by decide)).trans a26_1044
  have a27_10c4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K27.acc (by decide) (by decide)).trans a26_10c4
  have p27_200 : ptF n27.mem B 0x200 = P0 := (K27.pt (by decide) (by decide)).trans p26_200
  have p27_280 : ptF n27.mem B 0x280 = P1 := (K27.pt (by decide) (by decide)).trans p26_280
  have p27_900 : ptF n27.mem B 0x900 = P0 := (K27.pt (by decide) (by decide)).trans p26_900
  have p27_fe4 : ptF n27.mem B 0xFE4 = P0 := (K27.pt (by decide) (by decide)).trans p26_fe4
  have p27_1064 : ptF n27.mem B 0x1064 = P1 := (K27.pt (by decide) (by decide)).trans p26_1064
  have q27_e60 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X27 j hj).trans (fR26 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p26_1064 p26_fe4 p26_900 p26_280 p26_200 a26_10c4 a26_1044 a26_9e0 a26_9c0 a26_9a0 a26_980 a26_960 a26_2e0 a26_260 a26_1e0 a26_1c0 a26_1a0 a26_180 a26_160 a26_140 a26_120 q26_e00 q26_da0 q26_d40 q26_ce0 q26_c80 g26_12 g26_11 g26_10 g26_27 g26_26 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
  -- 0x786
  obtain ⟨n28, c28, u28⟩ := s27.block p2vEcT0a786 E27.self p2vEcT0a786_end
    ⟨trivial, trivial, trivial⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have s28 : St n28.mem P2V n28 0x78C (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have rb28 : ∀ q, reg n28 q = (runBlock p2vEcT0a786 (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
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
  have g28_18 : reg n28 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb28, runBlock_reg _ _ _ (20 : Fin 32) s27.zero (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb28, runBlock_reg _ _ _ (22 : Fin 32) s27.zero (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = rem := by
    rw [rb28, runBlock_reg _ _ _ (24 : Fin 32) s27.zero (by decide), g27_24]
  have g28_26 : reg n28 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
  have g28_8 : reg n28 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xEC0 := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_26, g27_27, s27.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g28_9 : reg n28 (9 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_26, g27_27, s27.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk28 : P2vKeepL B n0.mem n28.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have q28_c80 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_c80 j hj
  have q28_ce0 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_ce0 j hj
  have q28_d40 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_d40 j hj
  have q28_da0 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_da0 j hj
  have q28_e00 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_e00 j hj
  have q28_e60 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_e60 j hj
  have a28_120 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m28]; exact a27_120
  have a28_140 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m28]; exact a27_140
  have a28_160 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m28]; exact a27_160
  have a28_180 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m28]; exact a27_180
  have a28_1a0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m28]; exact a27_1a0
  have a28_1c0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m28]; exact a27_1c0
  have a28_1e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m28]; exact a27_1e0
  have a28_260 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m28]; exact a27_260
  have a28_2e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m28]; exact a27_2e0
  have a28_960 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m28]; exact a27_960
  have a28_980 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m28]; exact a27_980
  have a28_9a0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m28]; exact a27_9a0
  have a28_9c0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m28]; exact a27_9c0
  have a28_9e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m28]; exact a27_9e0
  have a28_1044 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m28]; exact a27_1044
  have a28_10c4 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m28]; exact a27_10c4
  have p28_200 : ptF n28.mem B 0x200 = P0 := by rw [m28]; exact p27_200
  have p28_280 : ptF n28.mem B 0x280 = P1 := by rw [m28]; exact p27_280
  have p28_900 : ptF n28.mem B 0x900 = P0 := by rw [m28]; exact p27_900
  have p28_fe4 : ptF n28.mem B 0xFE4 = P0 := by rw [m28]; exact p27_fe4
  have p28_1064 : ptF n28.mem B 0x1064 = P1 := by rw [m28]; exact p27_1064
  clear q27_e60 p27_1064 p27_fe4 p27_900 p27_280 p27_200 a27_10c4 a27_1044 a27_9e0 a27_9c0 a27_9a0 a27_980 a27_960 a27_2e0 a27_260 a27_1e0 a27_1c0 a27_1a0 a27_180 a27_160 a27_140 a27_120 q27_e00 q27_da0 q27_d40 q27_ce0 q27_c80 g27_27 g27_26 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 s27 X27 K27 P27
  -- 0x78C: branch, taken
  obtain ⟨n29, d29, u29⟩ := s28.taken E28.self 0x776 p2v_at_78c
    (by decide) (by rw [g28_9, s28.zero]; decide)
  have s29 : St n29.mem P2V n29 0x776 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, P2vR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, P2vR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : P2vCode n29.mem := E28.fr F fr29
  have V29 : P2vSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xEC0 := by rw [u29.regs, g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u29.regs, g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u29.regs, g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u29.regs, g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u29.regs, g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u29.regs, g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u29.regs, g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = rem := by rw [u29.regs, g28_24]
  have g29_26 : reg n29 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u29.regs, g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u29.regs, g28_27]
  have keep_kk29 : P2vKeepL B n0.mem n29.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have q29_c80 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_c80 j hj
  have q29_ce0 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_ce0 j hj
  have q29_d40 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_d40 j hj
  have q29_da0 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_da0 j hj
  have q29_e00 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_e00 j hj
  have q29_e60 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_e60 j hj
  have a29_120 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m29]; exact a28_120
  have a29_140 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m29]; exact a28_140
  have a29_160 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m29]; exact a28_160
  have a29_180 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m29]; exact a28_180
  have a29_1a0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m29]; exact a28_1a0
  have a29_1c0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m29]; exact a28_1c0
  have a29_1e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m29]; exact a28_1e0
  have a29_260 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m29]; exact a28_260
  have a29_2e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m29]; exact a28_2e0
  have a29_960 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m29]; exact a28_960
  have a29_980 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m29]; exact a28_980
  have a29_9a0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m29]; exact a28_9a0
  have a29_9c0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m29]; exact a28_9c0
  have a29_9e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m29]; exact a28_9e0
  have a29_1044 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m29]; exact a28_1044
  have a29_10c4 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m29]; exact a28_10c4
  have p29_200 : ptF n29.mem B 0x200 = P0 := by rw [m29]; exact p28_200
  have p29_280 : ptF n29.mem B 0x280 = P1 := by rw [m29]; exact p28_280
  have p29_900 : ptF n29.mem B 0x900 = P0 := by rw [m29]; exact p28_900
  have p29_fe4 : ptF n29.mem B 0xFE4 = P0 := by rw [m29]; exact p28_fe4
  have p29_1064 : ptF n29.mem B 0x1064 = P1 := by rw [m29]; exact p28_1064
  clear p28_1064 p28_fe4 p28_900 p28_280 p28_200 a28_10c4 a28_1044 a28_9e0 a28_9c0 a28_9a0 a28_980 a28_960 a28_2e0 a28_260 a28_1e0 a28_1c0 a28_1a0 a28_180 a28_160 a28_140 a28_120 q28_e60 q28_e00 q28_da0 q28_d40 q28_ce0 q28_c80 g28_9 g28_8 g28_27 g28_26 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
  -- 0x776
  obtain ⟨n30, c30, u30⟩ := s29.block p2vEcT0a776 E29.self p2vEcT0a776_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have s30 : St n30.mem P2V n30 0x77E (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have rb30 : ∀ q, reg n30 q = (runBlock p2vEcT0a776 (n29.mem, reg n29)).2 q := fun q => by rw [u30.regs]
  have fr30 : ∀ x, P2vR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans c30
  have fR30 : ∀ x, P2vR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : P2vCode n30.mem := E29.fr F fr30
  have V30 : P2vSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by
    rw [rb30, runBlock_reg _ _ _ sp s29.zero (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb30, runBlock_reg _ _ _ (3 : Fin 32) s29.zero (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb30, runBlock_reg _ _ _ (4 : Fin 32) s29.zero (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xEC0 := by
    rw [rb30, runBlock_reg _ _ _ (8 : Fin 32) s29.zero (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb30, runBlock_reg _ _ _ (9 : Fin 32) s29.zero (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb30, runBlock_reg _ _ _ (18 : Fin 32) s29.zero (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb30, runBlock_reg _ _ _ (19 : Fin 32) s29.zero (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb30, runBlock_reg _ _ _ (20 : Fin 32) s29.zero (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb30, runBlock_reg _ _ _ (21 : Fin 32) s29.zero (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb30, runBlock_reg _ _ _ (22 : Fin 32) s29.zero (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb30, runBlock_reg _ _ _ (23 : Fin 32) s29.zero (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = rem := by
    rw [rb30, runBlock_reg _ _ _ (24 : Fin 32) s29.zero (by decide), g29_24]
  have g30_26 : reg n30 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb30, runBlock_reg _ _ _ (26 : Fin 32) s29.zero (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb30, runBlock_reg _ _ _ (27 : Fin 32) s29.zero (by decide), g29_27]
  have g30_10 : reg n30 a0 = B + 0x21A0 + BitVec.ofNat 32 0xEC0 := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_26, g29_27, s29.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g30_11 : reg n30 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_26, g29_27, s29.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g30_12 : reg n30 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_26, g29_27, s29.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk30 : P2vKeepL B n0.mem n30.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have q30_c80 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m30]; exact q29_c80 j hj
  have q30_ce0 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m30]; exact q29_ce0 j hj
  have q30_d40 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m30]; exact q29_d40 j hj
  have q30_da0 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m30]; exact q29_da0 j hj
  have q30_e00 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m30]; exact q29_e00 j hj
  have q30_e60 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m30]; exact q29_e60 j hj
  have a30_120 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m30]; exact a29_120
  have a30_140 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m30]; exact a29_140
  have a30_160 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m30]; exact a29_160
  have a30_180 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m30]; exact a29_180
  have a30_1a0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m30]; exact a29_1a0
  have a30_1c0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m30]; exact a29_1c0
  have a30_1e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m30]; exact a29_1e0
  have a30_260 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m30]; exact a29_260
  have a30_2e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m30]; exact a29_2e0
  have a30_960 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m30]; exact a29_960
  have a30_980 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m30]; exact a29_980
  have a30_9a0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m30]; exact a29_9a0
  have a30_9c0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m30]; exact a29_9c0
  have a30_9e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m30]; exact a29_9e0
  have a30_1044 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m30]; exact a29_1044
  have a30_10c4 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m30]; exact a29_10c4
  have p30_200 : ptF n30.mem B 0x200 = P0 := by rw [m30]; exact p29_200
  have p30_280 : ptF n30.mem B 0x280 = P1 := by rw [m30]; exact p29_280
  have p30_900 : ptF n30.mem B 0x900 = P0 := by rw [m30]; exact p29_900
  have p30_fe4 : ptF n30.mem B 0xFE4 = P0 := by rw [m30]; exact p29_fe4
  have p30_1064 : ptF n30.mem B 0x1064 = P1 := by rw [m30]; exact p29_1064
  clear p29_1064 p29_fe4 p29_900 p29_280 p29_200 a29_10c4 a29_1044 a29_9e0 a29_9c0 a29_9a0 a29_980 a29_960 a29_2e0 a29_260 a29_1e0 a29_1c0 a29_1a0 a29_180 a29_160 a29_140 a29_120 q29_e60 q29_e00 q29_da0 q29_d40 q29_ce0 q29_c80 g29_27 g29_26 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0x77E: memcpy from outside the stack
  obtain ⟨n31, P31, K31, X31⟩ := p2v_mcRo2 (c := 0xEC0) (N := 0x60) F RS E30 s30 p2v_at_77e p2v_at_782
    (by decide) (by decide) g30_2 g30_10 g30_11 g30_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s31 := P31.st
  have fr31 := P31.fr
  have t31 : Steps n0 n31 := t30.trans P31.steps
  have fR31 : ∀ x, P2vR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : P2vCode n31.mem := E30.fr F fr31
  have V31 : P2vSaves B n31.mem v := V30.keep K31 (by decide)
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [P31.regs sp (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P31.regs (3 : Fin 32) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P31.regs (4 : Fin 32) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xEC0 := by rw [P31.regs (8 : Fin 32) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P31.regs (9 : Fin 32) (by decide), g30_9]
  have g31_18 : reg n31 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P31.regs (18 : Fin 32) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P31.regs (19 : Fin 32) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P31.regs (20 : Fin 32) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P31.regs (21 : Fin 32) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P31.regs (22 : Fin 32) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P31.regs (23 : Fin 32) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = rem := by rw [P31.regs (24 : Fin 32) (by decide), g30_24]
  have g31_26 : reg n31 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P31.regs (26 : Fin 32) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P31.regs (27 : Fin 32) (by decide), g30_27]
  have keep_kk31 : P2vKeepL B n0.mem n31.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60)] := keep_kk30.trans K31.toL
  clear keep_kk30
  have q31_c80 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K31.range (by decide) (by decide) j hj).trans (q30_c80 j hj)
  have q31_ce0 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K31.range (by decide) (by decide) j hj).trans (q30_ce0 j hj)
  have q31_d40 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K31.range (by decide) (by decide) j hj).trans (q30_d40 j hj)
  have q31_da0 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K31.range (by decide) (by decide) j hj).trans (q30_da0 j hj)
  have q31_e00 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K31.range (by decide) (by decide) j hj).trans (q30_e00 j hj)
  have q31_e60 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K31.range (by decide) (by decide) j hj).trans (q30_e60 j hj)
  have a31_120 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K31.acc (by decide) (by decide)).trans a30_120
  have a31_140 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K31.acc (by decide) (by decide)).trans a30_140
  have a31_160 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K31.acc (by decide) (by decide)).trans a30_160
  have a31_180 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K31.acc (by decide) (by decide)).trans a30_180
  have a31_1a0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K31.acc (by decide) (by decide)).trans a30_1a0
  have a31_1c0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K31.acc (by decide) (by decide)).trans a30_1c0
  have a31_1e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K31.acc (by decide) (by decide)).trans a30_1e0
  have a31_260 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K31.acc (by decide) (by decide)).trans a30_260
  have a31_2e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K31.acc (by decide) (by decide)).trans a30_2e0
  have a31_960 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (K31.acc (by decide) (by decide)).trans a30_960
  have a31_980 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K31.acc (by decide) (by decide)).trans a30_980
  have a31_9a0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K31.acc (by decide) (by decide)).trans a30_9a0
  have a31_9c0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K31.acc (by decide) (by decide)).trans a30_9c0
  have a31_9e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K31.acc (by decide) (by decide)).trans a30_9e0
  have a31_1044 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K31.acc (by decide) (by decide)).trans a30_1044
  have a31_10c4 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K31.acc (by decide) (by decide)).trans a30_10c4
  have p31_200 : ptF n31.mem B 0x200 = P0 := (K31.pt (by decide) (by decide)).trans p30_200
  have p31_280 : ptF n31.mem B 0x280 = P1 := (K31.pt (by decide) (by decide)).trans p30_280
  have p31_900 : ptF n31.mem B 0x900 = P0 := (K31.pt (by decide) (by decide)).trans p30_900
  have p31_fe4 : ptF n31.mem B 0xFE4 = P0 := (K31.pt (by decide) (by decide)).trans p30_fe4
  have p31_1064 : ptF n31.mem B 0x1064 = P1 := (K31.pt (by decide) (by decide)).trans p30_1064
  have q31_ec0 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X31 j hj).trans (fR30 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p30_1064 p30_fe4 p30_900 p30_280 p30_200 a30_10c4 a30_1044 a30_9e0 a30_9c0 a30_9a0 a30_980 a30_960 a30_2e0 a30_260 a30_1e0 a30_1c0 a30_1a0 a30_180 a30_160 a30_140 a30_120 q30_e60 q30_e00 q30_da0 q30_d40 q30_ce0 q30_c80 g30_12 g30_11 g30_10 g30_27 g30_26 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
  -- 0x786
  obtain ⟨n32, c32, u32⟩ := s31.block p2vEcT0a786 E31.self p2vEcT0a786_end
    ⟨trivial, trivial, trivial⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have s32 : St n32.mem P2V n32 0x78C (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have rb32 : ∀ q, reg n32 q = (runBlock p2vEcT0a786 (n31.mem, reg n31)).2 q := fun q => by rw [u32.regs]
  have fr32 : ∀ x, P2vR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans c32
  have fR32 : ∀ x, P2vR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : P2vCode n32.mem := E31.fr F fr32
  have V32 : P2vSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by
    rw [rb32, runBlock_reg _ _ _ sp s31.zero (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb32, runBlock_reg _ _ _ (3 : Fin 32) s31.zero (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb32, runBlock_reg _ _ _ (4 : Fin 32) s31.zero (by decide), g31_4]
  have g32_18 : reg n32 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb32, runBlock_reg _ _ _ (18 : Fin 32) s31.zero (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb32, runBlock_reg _ _ _ (19 : Fin 32) s31.zero (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb32, runBlock_reg _ _ _ (20 : Fin 32) s31.zero (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb32, runBlock_reg _ _ _ (21 : Fin 32) s31.zero (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb32, runBlock_reg _ _ _ (22 : Fin 32) s31.zero (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb32, runBlock_reg _ _ _ (23 : Fin 32) s31.zero (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = rem := by
    rw [rb32, runBlock_reg _ _ _ (24 : Fin 32) s31.zero (by decide), g31_24]
  have g32_26 : reg n32 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb32, runBlock_reg _ _ _ (26 : Fin 32) s31.zero (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb32, runBlock_reg _ _ _ (27 : Fin 32) s31.zero (by decide), g31_27]
  have g32_8 : reg n32 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xF20 := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_9, g31_18, g31_19, g31_20, g31_21, g31_22, g31_23, g31_24, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g32_9 : reg n32 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_9, g31_18, g31_19, g31_20, g31_21, g31_22, g31_23, g31_24, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk32 : P2vKeepL B n0.mem n32.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have q32_c80 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_c80 j hj
  have q32_ce0 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_ce0 j hj
  have q32_d40 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_d40 j hj
  have q32_da0 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_da0 j hj
  have q32_e00 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_e00 j hj
  have q32_e60 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_e60 j hj
  have q32_ec0 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_ec0 j hj
  have a32_120 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m32]; exact a31_120
  have a32_140 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m32]; exact a31_140
  have a32_160 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m32]; exact a31_160
  have a32_180 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m32]; exact a31_180
  have a32_1a0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m32]; exact a31_1a0
  have a32_1c0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m32]; exact a31_1c0
  have a32_1e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m32]; exact a31_1e0
  have a32_260 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m32]; exact a31_260
  have a32_2e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m32]; exact a31_2e0
  have a32_960 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m32]; exact a31_960
  have a32_980 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m32]; exact a31_980
  have a32_9a0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m32]; exact a31_9a0
  have a32_9c0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m32]; exact a31_9c0
  have a32_9e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m32]; exact a31_9e0
  have a32_1044 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m32]; exact a31_1044
  have a32_10c4 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m32]; exact a31_10c4
  have p32_200 : ptF n32.mem B 0x200 = P0 := by rw [m32]; exact p31_200
  have p32_280 : ptF n32.mem B 0x280 = P1 := by rw [m32]; exact p31_280
  have p32_900 : ptF n32.mem B 0x900 = P0 := by rw [m32]; exact p31_900
  have p32_fe4 : ptF n32.mem B 0xFE4 = P0 := by rw [m32]; exact p31_fe4
  have p32_1064 : ptF n32.mem B 0x1064 = P1 := by rw [m32]; exact p31_1064
  clear q31_ec0 p31_1064 p31_fe4 p31_900 p31_280 p31_200 a31_10c4 a31_1044 a31_9e0 a31_9c0 a31_9a0 a31_980 a31_960 a31_2e0 a31_260 a31_1e0 a31_1c0 a31_1a0 a31_180 a31_160 a31_140 a31_120 q31_e60 q31_e00 q31_da0 q31_d40 q31_ce0 q31_c80 g31_27 g31_26 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 s31 X31 K31 P31
  -- 0x78C: branch, taken
  obtain ⟨n33, d33, u33⟩ := s32.taken E32.self 0x776 p2v_at_78c
    (by decide) (by rw [g32_9, s32.zero]; decide)
  have s33 : St n33.mem P2V n33 0x776 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, P2vR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, P2vR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : P2vCode n33.mem := E32.fr F fr33
  have V33 : P2vSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xF20 := by rw [u33.regs, g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u33.regs, g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u33.regs, g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u33.regs, g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u33.regs, g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u33.regs, g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u33.regs, g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u33.regs, g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = rem := by rw [u33.regs, g32_24]
  have g33_26 : reg n33 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u33.regs, g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u33.regs, g32_27]
  have keep_kk33 : P2vKeepL B n0.mem n33.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have q33_c80 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_c80 j hj
  have q33_ce0 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_ce0 j hj
  have q33_d40 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_d40 j hj
  have q33_da0 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_da0 j hj
  have q33_e00 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_e00 j hj
  have q33_e60 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_e60 j hj
  have q33_ec0 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_ec0 j hj
  have a33_120 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m33]; exact a32_120
  have a33_140 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m33]; exact a32_140
  have a33_160 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m33]; exact a32_160
  have a33_180 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m33]; exact a32_180
  have a33_1a0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m33]; exact a32_1a0
  have a33_1c0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m33]; exact a32_1c0
  have a33_1e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m33]; exact a32_1e0
  have a33_260 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m33]; exact a32_260
  have a33_2e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m33]; exact a32_2e0
  have a33_960 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m33]; exact a32_960
  have a33_980 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m33]; exact a32_980
  have a33_9a0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m33]; exact a32_9a0
  have a33_9c0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m33]; exact a32_9c0
  have a33_9e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m33]; exact a32_9e0
  have a33_1044 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m33]; exact a32_1044
  have a33_10c4 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m33]; exact a32_10c4
  have p33_200 : ptF n33.mem B 0x200 = P0 := by rw [m33]; exact p32_200
  have p33_280 : ptF n33.mem B 0x280 = P1 := by rw [m33]; exact p32_280
  have p33_900 : ptF n33.mem B 0x900 = P0 := by rw [m33]; exact p32_900
  have p33_fe4 : ptF n33.mem B 0xFE4 = P0 := by rw [m33]; exact p32_fe4
  have p33_1064 : ptF n33.mem B 0x1064 = P1 := by rw [m33]; exact p32_1064
  clear p32_1064 p32_fe4 p32_900 p32_280 p32_200 a32_10c4 a32_1044 a32_9e0 a32_9c0 a32_9a0 a32_980 a32_960 a32_2e0 a32_260 a32_1e0 a32_1c0 a32_1a0 a32_180 a32_160 a32_140 a32_120 q32_ec0 q32_e60 q32_e00 q32_da0 q32_d40 q32_ce0 q32_c80 g32_9 g32_8 g32_27 g32_26 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 rb32 s32 m32 u32 c32
  -- 0x776
  obtain ⟨n34, c34, u34⟩ := s33.block p2vEcT0a776 E33.self p2vEcT0a776_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have s34 : St n34.mem P2V n34 0x77E (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have rb34 : ∀ q, reg n34 q = (runBlock p2vEcT0a776 (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
  have fr34 : ∀ x, P2vR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans c34
  have fR34 : ∀ x, P2vR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : P2vCode n34.mem := E33.fr F fr34
  have V34 : P2vSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by
    rw [rb34, runBlock_reg _ _ _ sp s33.zero (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb34, runBlock_reg _ _ _ (3 : Fin 32) s33.zero (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb34, runBlock_reg _ _ _ (4 : Fin 32) s33.zero (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xF20 := by
    rw [rb34, runBlock_reg _ _ _ (8 : Fin 32) s33.zero (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb34, runBlock_reg _ _ _ (9 : Fin 32) s33.zero (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb34, runBlock_reg _ _ _ (18 : Fin 32) s33.zero (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb34, runBlock_reg _ _ _ (19 : Fin 32) s33.zero (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb34, runBlock_reg _ _ _ (20 : Fin 32) s33.zero (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb34, runBlock_reg _ _ _ (21 : Fin 32) s33.zero (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb34, runBlock_reg _ _ _ (22 : Fin 32) s33.zero (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb34, runBlock_reg _ _ _ (23 : Fin 32) s33.zero (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = rem := by
    rw [rb34, runBlock_reg _ _ _ (24 : Fin 32) s33.zero (by decide), g33_24]
  have g34_26 : reg n34 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
  have g34_10 : reg n34 a0 = B + 0x21A0 + BitVec.ofNat 32 0xF20 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g34_11 : reg n34 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g34_12 : reg n34 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, p2vEcT0a776, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk34 : P2vKeepL B n0.mem n34.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have q34_c80 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m34]; exact q33_c80 j hj
  have q34_ce0 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m34]; exact q33_ce0 j hj
  have q34_d40 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m34]; exact q33_d40 j hj
  have q34_da0 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m34]; exact q33_da0 j hj
  have q34_e00 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m34]; exact q33_e00 j hj
  have q34_e60 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m34]; exact q33_e60 j hj
  have q34_ec0 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m34]; exact q33_ec0 j hj
  have a34_120 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m34]; exact a33_120
  have a34_140 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m34]; exact a33_140
  have a34_160 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m34]; exact a33_160
  have a34_180 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m34]; exact a33_180
  have a34_1a0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m34]; exact a33_1a0
  have a34_1c0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m34]; exact a33_1c0
  have a34_1e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m34]; exact a33_1e0
  have a34_260 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m34]; exact a33_260
  have a34_2e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m34]; exact a33_2e0
  have a34_960 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m34]; exact a33_960
  have a34_980 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m34]; exact a33_980
  have a34_9a0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m34]; exact a33_9a0
  have a34_9c0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m34]; exact a33_9c0
  have a34_9e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m34]; exact a33_9e0
  have a34_1044 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m34]; exact a33_1044
  have a34_10c4 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m34]; exact a33_10c4
  have p34_200 : ptF n34.mem B 0x200 = P0 := by rw [m34]; exact p33_200
  have p34_280 : ptF n34.mem B 0x280 = P1 := by rw [m34]; exact p33_280
  have p34_900 : ptF n34.mem B 0x900 = P0 := by rw [m34]; exact p33_900
  have p34_fe4 : ptF n34.mem B 0xFE4 = P0 := by rw [m34]; exact p33_fe4
  have p34_1064 : ptF n34.mem B 0x1064 = P1 := by rw [m34]; exact p33_1064
  clear p33_1064 p33_fe4 p33_900 p33_280 p33_200 a33_10c4 a33_1044 a33_9e0 a33_9c0 a33_9a0 a33_980 a33_960 a33_2e0 a33_260 a33_1e0 a33_1c0 a33_1a0 a33_180 a33_160 a33_140 a33_120 q33_ec0 q33_e60 q33_e00 q33_da0 q33_d40 q33_ce0 q33_c80 g33_27 g33_26 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  -- 0x77E: memcpy from outside the stack
  obtain ⟨n35, P35, K35, X35⟩ := p2v_mcRo2 (c := 0xF20) (N := 0x60) F RS E34 s34 p2v_at_77e p2v_at_782
    (by decide) (by decide) g34_2 g34_10 g34_11 g34_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s35 := P35.st
  have fr35 := P35.fr
  have t35 : Steps n0 n35 := t34.trans P35.steps
  have fR35 : ∀ x, P2vR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : P2vCode n35.mem := E34.fr F fr35
  have V35 : P2vSaves B n35.mem v := V34.keep K35 (by decide)
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [P35.regs sp (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P35.regs (3 : Fin 32) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P35.regs (4 : Fin 32) (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xF20 := by rw [P35.regs (8 : Fin 32) (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P35.regs (9 : Fin 32) (by decide), g34_9]
  have g35_18 : reg n35 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P35.regs (18 : Fin 32) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P35.regs (19 : Fin 32) (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P35.regs (20 : Fin 32) (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P35.regs (21 : Fin 32) (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P35.regs (22 : Fin 32) (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P35.regs (23 : Fin 32) (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = rem := by rw [P35.regs (24 : Fin 32) (by decide), g34_24]
  have g35_26 : reg n35 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P35.regs (26 : Fin 32) (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P35.regs (27 : Fin 32) (by decide), g34_27]
  have keep_kk35 : P2vKeepL B n0.mem n35.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60), (0xF20, 0x60)] := keep_kk34.trans K35.toL
  clear keep_kk34
  have q35_c80 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_c80 j hj)
  have q35_ce0 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_ce0 j hj)
  have q35_d40 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_d40 j hj)
  have q35_da0 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_da0 j hj)
  have q35_e00 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_e00 j hj)
  have q35_e60 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_e60 j hj)
  have q35_ec0 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_ec0 j hj)
  have a35_120 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K35.acc (by decide) (by decide)).trans a34_120
  have a35_140 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K35.acc (by decide) (by decide)).trans a34_140
  have a35_160 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K35.acc (by decide) (by decide)).trans a34_160
  have a35_180 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K35.acc (by decide) (by decide)).trans a34_180
  have a35_1a0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K35.acc (by decide) (by decide)).trans a34_1a0
  have a35_1c0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K35.acc (by decide) (by decide)).trans a34_1c0
  have a35_1e0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K35.acc (by decide) (by decide)).trans a34_1e0
  have a35_260 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K35.acc (by decide) (by decide)).trans a34_260
  have a35_2e0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K35.acc (by decide) (by decide)).trans a34_2e0
  have a35_960 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (K35.acc (by decide) (by decide)).trans a34_960
  have a35_980 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := (K35.acc (by decide) (by decide)).trans a34_980
  have a35_9a0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := (K35.acc (by decide) (by decide)).trans a34_9a0
  have a35_9c0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := (K35.acc (by decide) (by decide)).trans a34_9c0
  have a35_9e0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := (K35.acc (by decide) (by decide)).trans a34_9e0
  have a35_1044 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K35.acc (by decide) (by decide)).trans a34_1044
  have a35_10c4 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K35.acc (by decide) (by decide)).trans a34_10c4
  have p35_200 : ptF n35.mem B 0x200 = P0 := (K35.pt (by decide) (by decide)).trans p34_200
  have p35_280 : ptF n35.mem B 0x280 = P1 := (K35.pt (by decide) (by decide)).trans p34_280
  have p35_900 : ptF n35.mem B 0x900 = P0 := (K35.pt (by decide) (by decide)).trans p34_900
  have p35_fe4 : ptF n35.mem B 0xFE4 = P0 := (K35.pt (by decide) (by decide)).trans p34_fe4
  have p35_1064 : ptF n35.mem B 0x1064 = P1 := (K35.pt (by decide) (by decide)).trans p34_1064
  have q35_f20 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X35 j hj).trans (fR34 _ (P2vRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p34_1064 p34_fe4 p34_900 p34_280 p34_200 a34_10c4 a34_1044 a34_9e0 a34_9c0 a34_9a0 a34_980 a34_960 a34_2e0 a34_260 a34_1e0 a34_1c0 a34_1a0 a34_180 a34_160 a34_140 a34_120 q34_ec0 q34_e60 q34_e00 q34_da0 q34_d40 q34_ce0 q34_c80 g34_12 g34_11 g34_10 g34_27 g34_26 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
  -- 0x786
  obtain ⟨n36, c36, u36⟩ := s35.block p2vEcT0a786 E35.self p2vEcT0a786_end
    ⟨trivial, trivial, trivial⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have s36 : St n36.mem P2V n36 0x78C (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have rb36 : ∀ q, reg n36 q = (runBlock p2vEcT0a786 (n35.mem, reg n35)).2 q := fun q => by rw [u36.regs]
  have fr36 : ∀ x, P2vR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans c36
  have fR36 : ∀ x, P2vR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : P2vCode n36.mem := E35.fr F fr36
  have V36 : P2vSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by
    rw [rb36, runBlock_reg _ _ _ sp s35.zero (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb36, runBlock_reg _ _ _ (3 : Fin 32) s35.zero (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb36, runBlock_reg _ _ _ (4 : Fin 32) s35.zero (by decide), g35_4]
  have g36_18 : reg n36 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb36, runBlock_reg _ _ _ (18 : Fin 32) s35.zero (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb36, runBlock_reg _ _ _ (19 : Fin 32) s35.zero (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb36, runBlock_reg _ _ _ (20 : Fin 32) s35.zero (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb36, runBlock_reg _ _ _ (21 : Fin 32) s35.zero (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb36, runBlock_reg _ _ _ (22 : Fin 32) s35.zero (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb36, runBlock_reg _ _ _ (23 : Fin 32) s35.zero (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = rem := by
    rw [rb36, runBlock_reg _ _ _ (24 : Fin 32) s35.zero (by decide), g35_24]
  have g36_26 : reg n36 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb36, runBlock_reg _ _ _ (26 : Fin 32) s35.zero (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb36, runBlock_reg _ _ _ (27 : Fin 32) s35.zero (by decide), g35_27]
  have g36_8 : reg n36 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g36_9 : reg n36 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, p2vEcT0a786, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk36 : P2vKeepL B n0.mem n36.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60), (0xF20, 0x60)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have q36_c80 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_c80 j hj
  have q36_ce0 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_ce0 j hj
  have q36_d40 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_d40 j hj
  have q36_da0 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_da0 j hj
  have q36_e00 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_e00 j hj
  have q36_e60 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_e60 j hj
  have q36_ec0 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_ec0 j hj
  have q36_f20 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_f20 j hj
  have a36_120 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m36]; exact a35_120
  have a36_140 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m36]; exact a35_140
  have a36_160 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m36]; exact a35_160
  have a36_180 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m36]; exact a35_180
  have a36_1a0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m36]; exact a35_1a0
  have a36_1c0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m36]; exact a35_1c0
  have a36_1e0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m36]; exact a35_1e0
  have a36_260 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m36]; exact a35_260
  have a36_2e0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m36]; exact a35_2e0
  have a36_960 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m36]; exact a35_960
  have a36_980 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m36]; exact a35_980
  have a36_9a0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m36]; exact a35_9a0
  have a36_9c0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m36]; exact a35_9c0
  have a36_9e0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m36]; exact a35_9e0
  have a36_1044 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m36]; exact a35_1044
  have a36_10c4 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m36]; exact a35_10c4
  have p36_200 : ptF n36.mem B 0x200 = P0 := by rw [m36]; exact p35_200
  have p36_280 : ptF n36.mem B 0x280 = P1 := by rw [m36]; exact p35_280
  have p36_900 : ptF n36.mem B 0x900 = P0 := by rw [m36]; exact p35_900
  have p36_fe4 : ptF n36.mem B 0xFE4 = P0 := by rw [m36]; exact p35_fe4
  have p36_1064 : ptF n36.mem B 0x1064 = P1 := by rw [m36]; exact p35_1064
  clear q35_f20 p35_1064 p35_fe4 p35_900 p35_280 p35_200 a35_10c4 a35_1044 a35_9e0 a35_9c0 a35_9a0 a35_980 a35_960 a35_2e0 a35_260 a35_1e0 a35_1c0 a35_1a0 a35_180 a35_160 a35_140 a35_120 q35_ec0 q35_e60 q35_e00 q35_da0 q35_d40 q35_ce0 q35_c80 g35_27 g35_26 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 s35 X35 K35 P35
  -- 0x78C: branch, not taken
  obtain ⟨n37, d37, u37⟩ := s36.notTaken E36.self 0x78E p2v_at_78c
    (by decide) (by rw [g36_9, s36.zero]; decide)
  have s37 : St n37.mem P2V n37 0x78E (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, P2vR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, P2vR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : P2vCode n37.mem := E36.fr F fr37
  have V37 : P2vSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by rw [u37.regs, g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_9]
  have g37_18 : reg n37 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [u37.regs, g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u37.regs, g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u37.regs, g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u37.regs, g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u37.regs, g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = rem := by rw [u37.regs, g36_24]
  have g37_26 : reg n37 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u37.regs, g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u37.regs, g36_27]
  have keep_kk37 : P2vKeepL B n0.mem n37.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60), (0xF20, 0x60)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have q37_c80 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_c80 j hj
  have q37_ce0 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_ce0 j hj
  have q37_d40 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_d40 j hj
  have q37_da0 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_da0 j hj
  have q37_e00 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_e00 j hj
  have q37_e60 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_e60 j hj
  have q37_ec0 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_ec0 j hj
  have q37_f20 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_f20 j hj
  have a37_120 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m37]; exact a36_120
  have a37_140 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m37]; exact a36_140
  have a37_160 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m37]; exact a36_160
  have a37_180 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m37]; exact a36_180
  have a37_1a0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m37]; exact a36_1a0
  have a37_1c0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m37]; exact a36_1c0
  have a37_1e0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m37]; exact a36_1e0
  have a37_260 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m37]; exact a36_260
  have a37_2e0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m37]; exact a36_2e0
  have a37_960 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m37]; exact a36_960
  have a37_980 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m37]; exact a36_980
  have a37_9a0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m37]; exact a36_9a0
  have a37_9c0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m37]; exact a36_9c0
  have a37_9e0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m37]; exact a36_9e0
  have a37_1044 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m37]; exact a36_1044
  have a37_10c4 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m37]; exact a36_10c4
  have p37_200 : ptF n37.mem B 0x200 = P0 := by rw [m37]; exact p36_200
  have p37_280 : ptF n37.mem B 0x280 = P1 := by rw [m37]; exact p36_280
  have p37_900 : ptF n37.mem B 0x900 = P0 := by rw [m37]; exact p36_900
  have p37_fe4 : ptF n37.mem B 0xFE4 = P0 := by rw [m37]; exact p36_fe4
  have p37_1064 : ptF n37.mem B 0x1064 = P1 := by rw [m37]; exact p36_1064
  clear p36_1064 p36_fe4 p36_900 p36_280 p36_200 a36_10c4 a36_1044 a36_9e0 a36_9c0 a36_9a0 a36_980 a36_960 a36_2e0 a36_260 a36_1e0 a36_1c0 a36_1a0 a36_180 a36_160 a36_140 a36_120 q36_f20 q36_ec0 q36_e60 q36_e00 q36_da0 q36_d40 q36_ce0 q36_c80 g36_9 g36_8 g36_27 g36_26 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 rb36 s36 m36 u36 c36
  -- 0x78E
  obtain ⟨n38, c38, u38⟩ := s37.block p2vEcT0a78e E37.self p2vEcT0a78e_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have s38 : St n38.mem P2V n38 0x7AE (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have rb38 : ∀ q, reg n38 q = (runBlock p2vEcT0a78e (n37.mem, reg n37)).2 q := fun q => by rw [u38.regs]
  have fr38 : ∀ x, P2vR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans c38
  have fR38 : ∀ x, P2vR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : P2vCode n38.mem := E37.fr F fr38
  have V38 : P2vSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by
    rw [rb38, runBlock_reg _ _ _ sp s37.zero (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb38, runBlock_reg _ _ _ (3 : Fin 32) s37.zero (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb38, runBlock_reg _ _ _ (4 : Fin 32) s37.zero (by decide), g37_4]
  have g38_18 : reg n38 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by
    rw [rb38, runBlock_reg _ _ _ (18 : Fin 32) s37.zero (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb38, runBlock_reg _ _ _ (19 : Fin 32) s37.zero (by decide), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb38, runBlock_reg _ _ _ (20 : Fin 32) s37.zero (by decide), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb38, runBlock_reg _ _ _ (21 : Fin 32) s37.zero (by decide), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb38, runBlock_reg _ _ _ (22 : Fin 32) s37.zero (by decide), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb38, runBlock_reg _ _ _ (23 : Fin 32) s37.zero (by decide), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = rem := by
    rw [rb38, runBlock_reg _ _ _ (24 : Fin 32) s37.zero (by decide), g37_24]
  have g38_26 : reg n38 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb38, runBlock_reg _ _ _ (26 : Fin 32) s37.zero (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb38, runBlock_reg _ _ _ (27 : Fin 32) s37.zero (by decide), g37_27]
  have g38_8 : reg n38 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb38]; simp +decide only [runBlock, BInstr.run, p2vEcT0a78e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g37_2, g37_3, g37_4, g37_8, g37_9, g37_18, g37_19, g37_20, g37_21, g37_22, g37_23, g37_24, g37_26, g37_27, s37.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g38_9 : reg n38 (9 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb38]; simp +decide only [runBlock, BInstr.run, p2vEcT0a78e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g37_2, g37_3, g37_4, g37_8, g37_9, g37_18, g37_19, g37_20, g37_21, g37_22, g37_23, g37_24, g37_26, g37_27, s37.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g38_10 : reg n38 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb38]; simp +decide only [runBlock, BInstr.run, p2vEcT0a78e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g37_2, g37_3, g37_4, g37_8, g37_9, g37_18, g37_19, g37_20, g37_21, g37_22, g37_23, g37_24, g37_26, g37_27, s37.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g38_11 : reg n38 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb38]; simp +decide only [runBlock, BInstr.run, p2vEcT0a78e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g37_2, g37_3, g37_4, g37_8, g37_9, g37_18, g37_19, g37_20, g37_21, g37_22, g37_23, g37_24, g37_26, g37_27, s37.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g38_12 : reg n38 a2 = BitVec.ofNat 32 0x300 := by
    rw [rb38]; simp +decide only [runBlock, BInstr.run, p2vEcT0a78e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g37_2, g37_3, g37_4, g37_8, g37_9, g37_18, g37_19, g37_20, g37_21, g37_22, g37_23, g37_24, g37_26, g37_27, s37.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk38 : P2vKeepL B n0.mem n38.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60), (0xF20, 0x60)] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have q38_c80 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m38]; exact q37_c80 j hj
  have q38_ce0 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m38]; exact q37_ce0 j hj
  have q38_d40 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m38]; exact q37_d40 j hj
  have q38_da0 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m38]; exact q37_da0 j hj
  have q38_e00 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m38]; exact q37_e00 j hj
  have q38_e60 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m38]; exact q37_e60 j hj
  have q38_ec0 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m38]; exact q37_ec0 j hj
  have q38_f20 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m38]; exact q37_f20 j hj
  have a38_120 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m38]; exact a37_120
  have a38_140 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m38]; exact a37_140
  have a38_160 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m38]; exact a37_160
  have a38_180 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m38]; exact a37_180
  have a38_1a0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m38]; exact a37_1a0
  have a38_1c0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m38]; exact a37_1c0
  have a38_1e0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m38]; exact a37_1e0
  have a38_260 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m38]; exact a37_260
  have a38_2e0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m38]; exact a37_2e0
  have a38_960 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := by rw [m38]; exact a37_960
  have a38_980 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8 := by rw [m38]; exact a37_980
  have a38_9a0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8 := by rw [m38]; exact a37_9a0
  have a38_9c0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C0) 8 = accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8 := by rw [m38]; exact a37_9c0
  have a38_9e0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9E0) 8 = psmVal ((zv) * (wv)) := by rw [m38]; exact a37_9e0
  have a38_1044 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m38]; exact a37_1044
  have a38_10c4 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m38]; exact a37_10c4
  have p38_200 : ptF n38.mem B 0x200 = P0 := by rw [m38]; exact p37_200
  have p38_280 : ptF n38.mem B 0x280 = P1 := by rw [m38]; exact p37_280
  have p38_900 : ptF n38.mem B 0x900 = P0 := by rw [m38]; exact p37_900
  have p38_fe4 : ptF n38.mem B 0xFE4 = P0 := by rw [m38]; exact p37_fe4
  have p38_1064 : ptF n38.mem B 0x1064 = P1 := by rw [m38]; exact p37_1064
  clear p37_1064 p37_fe4 p37_900 p37_280 p37_200 a37_10c4 a37_1044 a37_9e0 a37_9c0 a37_9a0 a37_980 a37_960 a37_2e0 a37_260 a37_1e0 a37_1c0 a37_1a0 a37_180 a37_160 a37_140 a37_120 q37_f20 q37_ec0 q37_e60 q37_e00 q37_da0 q37_d40 q37_ce0 q37_c80 g37_27 g37_26 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  -- 0x7AE: memcpy
  obtain ⟨n39, P39, K39, X39⟩ := p2v_mc (c := 0x980) (d := 0xC80) (N := 0x300) F E38 s38 p2v_at_7ae p2v_at_7b2
    (by decide) (by decide) g38_2 g38_10 g38_11 g38_12
    (by decide) (by decide) (by decide)
  have s39 := P39.st
  have fr39 := P39.fr
  have t39 : Steps n0 n39 := t38.trans P39.steps
  have fR39 : ∀ x, P2vR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : P2vCode n39.mem := E38.fr F fr39
  have V39 : P2vSaves B n39.mem v := V38.keep K39 (by decide)
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [P39.regs sp (by decide), g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P39.regs (3 : Fin 32) (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P39.regs (4 : Fin 32) (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x980 := by rw [P39.regs (8 : Fin 32) (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P39.regs (9 : Fin 32) (by decide), g38_9]
  have g39_18 : reg n39 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xFE4 := by rw [P39.regs (18 : Fin 32) (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P39.regs (19 : Fin 32) (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P39.regs (20 : Fin 32) (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P39.regs (21 : Fin 32) (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P39.regs (22 : Fin 32) (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P39.regs (23 : Fin 32) (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = rem := by rw [P39.regs (24 : Fin 32) (by decide), g38_24]
  have g39_26 : reg n39 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P39.regs (26 : Fin 32) (by decide), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P39.regs (27 : Fin 32) (by decide), g38_27]
  have keep_kk39 : P2vKeepL B n0.mem n39.mem [(0x900, 0x80), (0xC80, 0x60), (0xCE0, 0x60), (0xD40, 0x60), (0xDA0, 0x60), (0xE00, 0x60), (0xE60, 0x60), (0xEC0, 0x60), (0xF20, 0x60), (0x980, 0x300)] := keep_kk38.trans K39.toL
  clear keep_kk38
  have q39_c80 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_c80 j hj)
  have q39_ce0 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_ce0 j hj)
  have q39_d40 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_d40 j hj)
  have q39_da0 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_da0 j hj)
  have q39_e00 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_e00 j hj)
  have q39_e60 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_e60 j hj)
  have q39_ec0 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_ec0 j hj)
  have q39_f20 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_f20 j hj)
  have a39_120 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K39.acc (by decide) (by decide)).trans a38_120
  have a39_140 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K39.acc (by decide) (by decide)).trans a38_140
  have a39_160 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K39.acc (by decide) (by decide)).trans a38_160
  have a39_180 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K39.acc (by decide) (by decide)).trans a38_180
  have a39_1a0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K39.acc (by decide) (by decide)).trans a38_1a0
  have a39_1c0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K39.acc (by decide) (by decide)).trans a38_1c0
  have a39_1e0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K39.acc (by decide) (by decide)).trans a38_1e0
  have a39_260 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K39.acc (by decide) (by decide)).trans a38_260
  have a39_2e0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K39.acc (by decide) (by decide)).trans a38_2e0
  have a39_960 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U1 := (K39.acc (by decide) (by decide)).trans a38_960
  have a39_1044 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K39.acc (by decide) (by decide)).trans a38_1044
  have a39_10c4 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K39.acc (by decide) (by decide)).trans a38_10c4
  have p39_200 : ptF n39.mem B 0x200 = P0 := (K39.pt (by decide) (by decide)).trans p38_200
  have p39_280 : ptF n39.mem B 0x280 = P1 := (K39.pt (by decide) (by decide)).trans p38_280
  have p39_900 : ptF n39.mem B 0x900 = P0 := (K39.pt (by decide) (by decide)).trans p38_900
  have p39_fe4 : ptF n39.mem B 0xFE4 = P0 := (K39.pt (by decide) (by decide)).trans p38_fe4
  have p39_1064 : ptF n39.mem B 0x1064 = P1 := (K39.pt (by decide) (by decide)).trans p38_1064
  have q39_980 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0x980 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x980 + j = 0x980 + (0x0 + j) by omega, X39 (0x0 + j) (by omega),
      show 0xC80 + (0x0 + j) = 0xC80 + j by omega]; exact q38_c80 j (by omega)
  have q39_9e0 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0x9E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x9E0 + j = 0x980 + (0x60 + j) by omega, X39 (0x60 + j) (by omega),
      show 0xC80 + (0x60 + j) = 0xCE0 + j by omega]; exact q38_ce0 j (by omega)
  have q39_a40 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0xA40 + j = 0x980 + (0xC0 + j) by omega, X39 (0xC0 + j) (by omega),
      show 0xC80 + (0xC0 + j) = 0xD40 + j by omega]; exact q38_d40 j (by omega)
  have q39_aa0 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xAA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0xAA0 + j = 0x980 + (0x120 + j) by omega, X39 (0x120 + j) (by omega),
      show 0xC80 + (0x120 + j) = 0xDA0 + j by omega]; exact q38_da0 j (by omega)
  have q39_b00 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0xB00 + j = 0x980 + (0x180 + j) by omega, X39 (0x180 + j) (by omega),
      show 0xC80 + (0x180 + j) = 0xE00 + j by omega]; exact q38_e00 j (by omega)
  have q39_b60 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0xB60 + j = 0x980 + (0x1E0 + j) by omega, X39 (0x1E0 + j) (by omega),
      show 0xC80 + (0x1E0 + j) = 0xE60 + j by omega]; exact q38_e60 j (by omega)
  have q39_bc0 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0xBC0 + j = 0x980 + (0x240 + j) by omega, X39 (0x240 + j) (by omega),
      show 0xC80 + (0x240 + j) = 0xEC0 + j by omega]; exact q38_ec0 j (by omega)
  have q39_c20 : ∀ j, j < 96 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0xC20 + j = 0x980 + (0x2A0 + j) by omega, X39 (0x2A0 + j) (by omega),
      show 0xC80 + (0x2A0 + j) = 0xF20 + j by omega]; exact q38_f20 j (by omega)
  clear p38_1064 p38_fe4 p38_900 p38_280 p38_200 a38_10c4 a38_1044 a38_9e0 a38_9c0 a38_9a0 a38_980 a38_960 a38_2e0 a38_260 a38_1e0 a38_1c0 a38_1a0 a38_180 a38_160 a38_140 a38_120 q38_f20 q38_ec0 q38_e60 q38_e00 q38_da0 q38_d40 q38_ce0 q38_c80 g38_12 g38_11 g38_10 g38_9 g38_8 g38_27 g38_26 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 rb38 s38 m38 u38 c38
  exact .inr ⟨n39, t39, s39, E39, V39, fR39, g39_2, g39_3, g39_4, g39_8, g39_9, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_26, g39_27, q39_980, q39_9e0, q39_a40, q39_aa0, q39_b00, q39_b60, q39_bc0, q39_c20, q39_c80, q39_ce0, q39_d40, q39_da0, q39_e00, q39_e60, q39_ec0, q39_f20, a39_120, a39_140, a39_160, a39_180, a39_1a0, a39_1c0, a39_1e0, a39_260, a39_2e0, a39_960, a39_1044, a39_10c4, p39_200, p39_280, p39_900, p39_fe4, p39_1064, keep_kk39.mono (by decide)⟩

end C3.RV32.P2v
