import C3BootProofs.Proofs.P2vEcT1c

/-!
# `p256VerifyPrehash`: the tables of the linear combination, part 1b

Part 1b of the table loop from 0x754 to 0x862: the odd multiples `P + j·2P` of `G` and of `Q`, stored at offsets 0x300 and 0x600.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vEcT1b7ec : List BInstr :=
  [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x60, .alu .add a0 x0 (8 : Fin 32)]
theorem p2vEcT1b7ec_end : blockEnd p256VerifyPrehashCode 0x7EC p2vEcT1b7ec = some 0x7FA := by
  simp only [p2vEcT1b7ec]
  rw [blockEnd, p2v_at_7ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_7f0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_7f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_7f8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT1b802 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x781]
theorem p2vEcT1b802_end : blockEnd p256VerifyPrehashCode 0x802 p2vEcT1b802 = some 0x812 := by
  simp only [p2vEcT1b802]
  rw [blockEnd, p2v_at_802]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_806]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_80a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_80e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT1b81a : List BInstr :=
  [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x60, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFA0]
theorem p2vEcT1b81a_end : blockEnd p256VerifyPrehashCode 0x81A p2vEcT1b81a = some 0x822 := by
  simp only [p2vEcT1b81a]
  rw [blockEnd, p2v_at_81a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_81e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT1b824 : List BInstr :=
  [.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x80, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .aluImm .add a2 x0 0x300]
theorem p2vEcT1b824_end : blockEnd p256VerifyPrehashCode 0x824 p2vEcT1b824 = some 0x83C := by
  simp only [p2vEcT1b824]
  rw [blockEnd, p2v_at_824]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_828]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_82c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_830]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_834]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_838]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT1b844 : List BInstr :=
  [.alu .mul a0 (19 : Fin 32) (21 : Fin 32), .alu .add a0 a0 (22 : Fin 32), .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x300]
theorem p2vEcT1b844_end : blockEnd p256VerifyPrehashCode 0x844 p2vEcT1b844 = some 0x856 := by
  simp only [p2vEcT1b844]
  rw [blockEnd, p2v_at_844]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_848]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_84a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_84e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_852]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT1b85e : List BInstr :=
  [.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x1]
theorem p2vEcT1b85e_end : blockEnd p256VerifyPrehashCode 0x85E p2vEcT1b85e = some 0x860 := by
  simp only [p2vEcT1b85e]
  rw [blockEnd, p2v_at_85e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcT1b750 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF]
theorem p2vEcT1b750_end : blockEnd p256VerifyPrehashCode 0x750 p2vEcT1b750 = some 0x754 := by
  simp only [p2vEcT1b750]
  rw [blockEnd, p2v_at_750]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_ect1b {B dlo dhi rem : Word} {fs gs ds es : BitVec 8} {wv U1 U2 : Nat} {P0 P1 : Pt2} {qx qy qz rv sv zv fv gv dv ev : Nat} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x7EC (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB00)
    (g0_9 : reg n0 (9 : Fin 32) = BitVec.ofNat 32 0x180)
    (g0_18 : reg n0 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064)
    (g0_19 : reg n0 (19 : Fin 32) = BitVec.ofNat 32 0x1)
    (g0_20 : reg n0 (20 : Fin 32) = BitVec.ofNat 32 0x2)
    (g0_21 : reg n0 (21 : Fin 32) = BitVec.ofNat 32 0x300)
    (g0_22 : reg n0 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300)
    (g0_23 : reg n0 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress))
    (g0_24 : reg n0 (24 : Fin 32) = rem)
    (g0_26 : reg n0 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920)
    (g0_27 : reg n0 (27 : Fin 32) = BitVec.ofNat 32 0x7)
    (q0_b00 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_b60 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_bc0 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_c20 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_ce0 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_d40 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_da0 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_e00 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_e60 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_ec0 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (q0_f20 : ∀ j, j < 96 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j))
    (a0_120 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx)
    (a0_140 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy)
    (a0_160 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz)
    (a0_180 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv)
    (a0_1a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv)
    (a0_1c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv)
    (a0_1e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv)
    (a0_260 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1)
    (a0_2e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2)
    (a0_960 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2)
    (a0_1044 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1)
    (a0_10c4 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2)
    (p0_200 : ptF n0.mem B 0x200 = P0)
    (p0_280 : ptF n0.mem B 0x280 = P1)
    (p0_300 : ptF n0.mem B 0x300 = tbl2 P0 0)
    (p0_360 : ptF n0.mem B 0x360 = tbl2 P0 1)
    (p0_3c0 : ptF n0.mem B 0x3C0 = tbl2 P0 2)
    (p0_420 : ptF n0.mem B 0x420 = tbl2 P0 3)
    (p0_480 : ptF n0.mem B 0x480 = tbl2 P0 4)
    (p0_4e0 : ptF n0.mem B 0x4E0 = tbl2 P0 5)
    (p0_540 : ptF n0.mem B 0x540 = tbl2 P0 6)
    (p0_5a0 : ptF n0.mem B 0x5A0 = tbl2 P0 7)
    (p0_900 : ptF n0.mem B 0x900 = P1)
    (p0_980 : ptF n0.mem B 0x980 = tbl2 P1 0)
    (p0_9e0 : ptF n0.mem B 0x9E0 = tbl2 P1 1)
    (p0_a40 : ptF n0.mem B 0xA40 = tbl2 P1 2)
    (p0_aa0 : ptF n0.mem B 0xAA0 = tbl2 P1 3)
    (p0_c80 : ptF n0.mem B 0xC80 = tbl2 P1 4)
    (p0_f80 : ptF n0.mem B 0xF80 = ptDbl2 P1)
    (p0_fe4 : ptF n0.mem B 0xFE4 = P0)
    (p0_1064 : ptF n0.mem B 0x1064 = P1)
    (RS : P2vRoSep B)
    (hP0 : Pt2Lt P0)
    (hP1 : Pt2Lt P1)
    (RS : P2vRoSep B)
    (PT0 : P2vPtCode M0) :
    (¬ (True) ∧ P2vRet B v n0 0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x862 (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' a0 = B + 0x21A0 + BitVec.ofNat 32 0x7FF ∧
        reg n' (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 ∧
        reg n' (19 : Fin 32) = BitVec.ofNat 32 0x2 ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x2 ∧
        reg n' (21 : Fin 32) = BitVec.ofNat 32 0x300 ∧
        reg n' (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 ∧
        reg n' (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) ∧
        reg n' (24 : Fin 32) = rem ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        reg n' (27 : Fin 32) = BitVec.ofNat 32 0x7 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 ∧
        ptF n'.mem B 0x200 = P0 ∧
        ptF n'.mem B 0x280 = P1 ∧
        ptF n'.mem B 0x300 = tbl2 P0 0 ∧
        ptF n'.mem B 0x360 = tbl2 P0 1 ∧
        ptF n'.mem B 0x3C0 = tbl2 P0 2 ∧
        ptF n'.mem B 0x420 = tbl2 P0 3 ∧
        ptF n'.mem B 0x480 = tbl2 P0 4 ∧
        ptF n'.mem B 0x4E0 = tbl2 P0 5 ∧
        ptF n'.mem B 0x540 = tbl2 P0 6 ∧
        ptF n'.mem B 0x5A0 = tbl2 P0 7 ∧
        ptF n'.mem B 0x600 = tbl2 P1 0 ∧
        ptF n'.mem B 0x660 = tbl2 P1 1 ∧
        ptF n'.mem B 0x6C0 = tbl2 P1 2 ∧
        ptF n'.mem B 0x720 = tbl2 P1 3 ∧
        ptF n'.mem B 0x780 = tbl2 P1 4 ∧
        ptF n'.mem B 0x7E0 = tbl2 P1 5 ∧
        ptF n'.mem B 0x840 = tbl2 P1 6 ∧
        ptF n'.mem B 0x8A0 = tbl2 P1 7 ∧
        ptF n'.mem B 0x900 = P1 ∧
        ptF n'.mem B 0x980 = tbl2 P1 0 ∧
        ptF n'.mem B 0x9E0 = tbl2 P1 1 ∧
        ptF n'.mem B 0xA40 = tbl2 P1 2 ∧
        ptF n'.mem B 0xAA0 = tbl2 P1 3 ∧
        ptF n'.mem B 0xB00 = tbl2 P1 4 ∧
        ptF n'.mem B 0xB60 = tbl2 P1 5 ∧
        ptF n'.mem B 0xBC0 = tbl2 P1 6 ∧
        ptF n'.mem B 0xC20 = tbl2 P1 7 ∧
        ptF n'.mem B 0xC80 = tbl2 P1 0 ∧
        ptF n'.mem B 0xCE0 = tbl2 P1 1 ∧
        ptF n'.mem B 0xD40 = tbl2 P1 2 ∧
        ptF n'.mem B 0xDA0 = tbl2 P1 3 ∧
        ptF n'.mem B 0xE00 = tbl2 P1 4 ∧
        ptF n'.mem B 0xE60 = tbl2 P1 5 ∧
        ptF n'.mem B 0xEC0 = tbl2 P1 6 ∧
        ptF n'.mem B 0xF20 = tbl2 P1 7 ∧
        ptF n'.mem B 0xF80 = ptDbl2 P1 ∧
        ptF n'.mem B 0xFE4 = P0 ∧
        ptF n'.mem B 0x1064 = P1 ∧
        P2vKeepL B n0.mem n'.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60), (0xC80, 0x300), (0x600, 0x300)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x7EC
  obtain ⟨n1, c1, u1⟩ := s0.block p2vEcT1b7ec E0.self p2vEcT1b7ec_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem P2V n1 0x7FA (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock p2vEcT1b7ec (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_8 : reg n1 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB00 := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = BitVec.ofNat 32 0x180 := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = rem := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_26 : reg n1 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0xB00 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have q1_b00 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_b00 j hj
  have q1_b60 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_b60 j hj
  have q1_bc0 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_bc0 j hj
  have q1_c20 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_c20 j hj
  have q1_ce0 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_ce0 j hj
  have q1_d40 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_d40 j hj
  have q1_da0 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_da0 j hj
  have q1_e00 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_e00 j hj
  have q1_e60 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_e60 j hj
  have q1_ec0 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_ec0 j hj
  have q1_f20 : ∀ j, j < 96 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m1]; exact q0_f20 j hj
  have a1_120 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m1]; exact a0_120
  have a1_140 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m1]; exact a0_140
  have a1_160 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m1]; exact a0_160
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m1]; exact a0_180
  have a1_1a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m1]; exact a0_1a0
  have a1_1c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m1]; exact a0_1c0
  have a1_1e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m1]; exact a0_1e0
  have a1_260 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m1]; exact a0_260
  have a1_2e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m1]; exact a0_2e0
  have a1_960 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m1]; exact a0_960
  have a1_1044 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m1]; exact a0_1044
  have a1_10c4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m1]; exact a0_10c4
  have p1_200 : ptF n1.mem B 0x200 = P0 := by rw [m1]; exact p0_200
  have p1_280 : ptF n1.mem B 0x280 = P1 := by rw [m1]; exact p0_280
  have p1_300 : ptF n1.mem B 0x300 = tbl2 P0 0 := by rw [m1]; exact p0_300
  have p1_360 : ptF n1.mem B 0x360 = tbl2 P0 1 := by rw [m1]; exact p0_360
  have p1_3c0 : ptF n1.mem B 0x3C0 = tbl2 P0 2 := by rw [m1]; exact p0_3c0
  have p1_420 : ptF n1.mem B 0x420 = tbl2 P0 3 := by rw [m1]; exact p0_420
  have p1_480 : ptF n1.mem B 0x480 = tbl2 P0 4 := by rw [m1]; exact p0_480
  have p1_4e0 : ptF n1.mem B 0x4E0 = tbl2 P0 5 := by rw [m1]; exact p0_4e0
  have p1_540 : ptF n1.mem B 0x540 = tbl2 P0 6 := by rw [m1]; exact p0_540
  have p1_5a0 : ptF n1.mem B 0x5A0 = tbl2 P0 7 := by rw [m1]; exact p0_5a0
  have p1_900 : ptF n1.mem B 0x900 = P1 := by rw [m1]; exact p0_900
  have p1_980 : ptF n1.mem B 0x980 = tbl2 P1 0 := by rw [m1]; exact p0_980
  have p1_9e0 : ptF n1.mem B 0x9E0 = tbl2 P1 1 := by rw [m1]; exact p0_9e0
  have p1_a40 : ptF n1.mem B 0xA40 = tbl2 P1 2 := by rw [m1]; exact p0_a40
  have p1_aa0 : ptF n1.mem B 0xAA0 = tbl2 P1 3 := by rw [m1]; exact p0_aa0
  have p1_c80 : ptF n1.mem B 0xC80 = tbl2 P1 4 := by rw [m1]; exact p0_c80
  have p1_f80 : ptF n1.mem B 0xF80 = ptDbl2 P1 := by rw [m1]; exact p0_f80
  have p1_fe4 : ptF n1.mem B 0xFE4 = P0 := by rw [m1]; exact p0_fe4
  have p1_1064 : ptF n1.mem B 0x1064 = P1 := by rw [m1]; exact p0_1064
  -- 0x7FA: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := p2v_mc (c := 0xB00) (d := 0xC80) (N := 0x60) F E1 s1 p2v_at_7fa p2v_at_7fe
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
  have g2_8 : reg n2 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB00 := by rw [P2.regs (8 : Fin 32) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = BitVec.ofNat 32 0x180 := by rw [P2.regs (9 : Fin 32) (by decide), g1_9]
  have g2_18 : reg n2 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [P2.regs (18 : Fin 32) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P2.regs (19 : Fin 32) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P2.regs (20 : Fin 32) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P2.regs (21 : Fin 32) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P2.regs (22 : Fin 32) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P2.regs (23 : Fin 32) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = rem := by rw [P2.regs (24 : Fin 32) (by decide), g1_24]
  have g2_26 : reg n2 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P2.regs (26 : Fin 32) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P2.regs (27 : Fin 32) (by decide), g1_27]
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0xB00, 0x60)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have q2_b60 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_b60 j hj)
  have q2_bc0 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_bc0 j hj)
  have q2_c20 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_c20 j hj)
  have q2_ce0 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_ce0 j hj)
  have q2_d40 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_d40 j hj)
  have q2_da0 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_da0 j hj)
  have q2_e00 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_e00 j hj)
  have q2_e60 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_e60 j hj)
  have q2_ec0 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_ec0 j hj)
  have q2_f20 : ∀ j, j < 96 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_f20 j hj)
  have a2_120 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K2.acc (by decide) (by decide)).trans a1_120
  have a2_140 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K2.acc (by decide) (by decide)).trans a1_140
  have a2_160 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K2.acc (by decide) (by decide)).trans a1_160
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_180
  have a2_1a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K2.acc (by decide) (by decide)).trans a1_1a0
  have a2_1c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K2.acc (by decide) (by decide)).trans a1_1c0
  have a2_1e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K2.acc (by decide) (by decide)).trans a1_1e0
  have a2_260 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K2.acc (by decide) (by decide)).trans a1_260
  have a2_2e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K2.acc (by decide) (by decide)).trans a1_2e0
  have a2_960 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K2.acc (by decide) (by decide)).trans a1_960
  have a2_1044 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K2.acc (by decide) (by decide)).trans a1_1044
  have a2_10c4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K2.acc (by decide) (by decide)).trans a1_10c4
  have p2_200 : ptF n2.mem B 0x200 = P0 := (K2.pt (by decide) (by decide)).trans p1_200
  have p2_280 : ptF n2.mem B 0x280 = P1 := (K2.pt (by decide) (by decide)).trans p1_280
  have p2_300 : ptF n2.mem B 0x300 = tbl2 P0 0 := (K2.pt (by decide) (by decide)).trans p1_300
  have p2_360 : ptF n2.mem B 0x360 = tbl2 P0 1 := (K2.pt (by decide) (by decide)).trans p1_360
  have p2_3c0 : ptF n2.mem B 0x3C0 = tbl2 P0 2 := (K2.pt (by decide) (by decide)).trans p1_3c0
  have p2_420 : ptF n2.mem B 0x420 = tbl2 P0 3 := (K2.pt (by decide) (by decide)).trans p1_420
  have p2_480 : ptF n2.mem B 0x480 = tbl2 P0 4 := (K2.pt (by decide) (by decide)).trans p1_480
  have p2_4e0 : ptF n2.mem B 0x4E0 = tbl2 P0 5 := (K2.pt (by decide) (by decide)).trans p1_4e0
  have p2_540 : ptF n2.mem B 0x540 = tbl2 P0 6 := (K2.pt (by decide) (by decide)).trans p1_540
  have p2_5a0 : ptF n2.mem B 0x5A0 = tbl2 P0 7 := (K2.pt (by decide) (by decide)).trans p1_5a0
  have p2_900 : ptF n2.mem B 0x900 = P1 := (K2.pt (by decide) (by decide)).trans p1_900
  have p2_980 : ptF n2.mem B 0x980 = tbl2 P1 0 := (K2.pt (by decide) (by decide)).trans p1_980
  have p2_9e0 : ptF n2.mem B 0x9E0 = tbl2 P1 1 := (K2.pt (by decide) (by decide)).trans p1_9e0
  have p2_a40 : ptF n2.mem B 0xA40 = tbl2 P1 2 := (K2.pt (by decide) (by decide)).trans p1_a40
  have p2_aa0 : ptF n2.mem B 0xAA0 = tbl2 P1 3 := (K2.pt (by decide) (by decide)).trans p1_aa0
  have p2_c80 : ptF n2.mem B 0xC80 = tbl2 P1 4 := (K2.pt (by decide) (by decide)).trans p1_c80
  have p2_f80 : ptF n2.mem B 0xF80 = ptDbl2 P1 := (K2.pt (by decide) (by decide)).trans p1_f80
  have p2_fe4 : ptF n2.mem B 0xFE4 = P0 := (K2.pt (by decide) (by decide)).trans p1_fe4
  have p2_1064 : ptF n2.mem B 0x1064 = P1 := (K2.pt (by decide) (by decide)).trans p1_1064
  have p2_b00 : ptF n2.mem B 0xB00 = tbl2 P1 4 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_c80
  clear p1_1064 p1_fe4 p1_f80 p1_c80 p1_aa0 p1_a40 p1_9e0 p1_980 p1_900 p1_5a0 p1_540 p1_4e0 p1_480 p1_420 p1_3c0 p1_360 p1_300 p1_280 p1_200 a1_10c4 a1_1044 a1_960 a1_2e0 a1_260 a1_1e0 a1_1c0 a1_1a0 a1_180 a1_160 a1_140 a1_120 q1_f20 q1_ec0 q1_e60 q1_e00 q1_da0 q1_d40 q1_ce0 q1_c20 q1_bc0 q1_b60 q1_b00 g1_12 g1_11 g1_10 g1_27 g1_26 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x802
  obtain ⟨n3, c3, u3⟩ := s2.block p2vEcT1b802 E2.self p2vEcT1b802_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem P2V n3 0x812 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock p2vEcT1b802 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_8 : reg n3 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB00 := by
    rw [rb3, runBlock_reg _ _ _ (8 : Fin 32) s2.zero (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 0x180 := by
    rw [rb3, runBlock_reg _ _ _ (9 : Fin 32) s2.zero (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = rem := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vEcT1b802, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_11 : reg n3 a1 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vEcT1b802, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0xB00, 0x60)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have q3_b60 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_b60 j hj
  have q3_bc0 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_bc0 j hj
  have q3_c20 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_c20 j hj
  have q3_ce0 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_ce0 j hj
  have q3_d40 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_d40 j hj
  have q3_da0 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_da0 j hj
  have q3_e00 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_e00 j hj
  have q3_e60 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_e60 j hj
  have q3_ec0 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_ec0 j hj
  have q3_f20 : ∀ j, j < 96 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m3]; exact q2_f20 j hj
  have a3_120 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m3]; exact a2_120
  have a3_140 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m3]; exact a2_140
  have a3_160 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m3]; exact a2_160
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m3]; exact a2_180
  have a3_1a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m3]; exact a2_1a0
  have a3_1c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m3]; exact a2_1c0
  have a3_1e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m3]; exact a2_1e0
  have a3_260 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m3]; exact a2_260
  have a3_2e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m3]; exact a2_2e0
  have a3_960 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m3]; exact a2_960
  have a3_1044 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m3]; exact a2_1044
  have a3_10c4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m3]; exact a2_10c4
  have p3_200 : ptF n3.mem B 0x200 = P0 := by rw [m3]; exact p2_200
  have p3_280 : ptF n3.mem B 0x280 = P1 := by rw [m3]; exact p2_280
  have p3_300 : ptF n3.mem B 0x300 = tbl2 P0 0 := by rw [m3]; exact p2_300
  have p3_360 : ptF n3.mem B 0x360 = tbl2 P0 1 := by rw [m3]; exact p2_360
  have p3_3c0 : ptF n3.mem B 0x3C0 = tbl2 P0 2 := by rw [m3]; exact p2_3c0
  have p3_420 : ptF n3.mem B 0x420 = tbl2 P0 3 := by rw [m3]; exact p2_420
  have p3_480 : ptF n3.mem B 0x480 = tbl2 P0 4 := by rw [m3]; exact p2_480
  have p3_4e0 : ptF n3.mem B 0x4E0 = tbl2 P0 5 := by rw [m3]; exact p2_4e0
  have p3_540 : ptF n3.mem B 0x540 = tbl2 P0 6 := by rw [m3]; exact p2_540
  have p3_5a0 : ptF n3.mem B 0x5A0 = tbl2 P0 7 := by rw [m3]; exact p2_5a0
  have p3_900 : ptF n3.mem B 0x900 = P1 := by rw [m3]; exact p2_900
  have p3_980 : ptF n3.mem B 0x980 = tbl2 P1 0 := by rw [m3]; exact p2_980
  have p3_9e0 : ptF n3.mem B 0x9E0 = tbl2 P1 1 := by rw [m3]; exact p2_9e0
  have p3_a40 : ptF n3.mem B 0xA40 = tbl2 P1 2 := by rw [m3]; exact p2_a40
  have p3_aa0 : ptF n3.mem B 0xAA0 = tbl2 P1 3 := by rw [m3]; exact p2_aa0
  have p3_b00 : ptF n3.mem B 0xB00 = tbl2 P1 4 := by rw [m3]; exact p2_b00
  have p3_c80 : ptF n3.mem B 0xC80 = tbl2 P1 4 := by rw [m3]; exact p2_c80
  have p3_f80 : ptF n3.mem B 0xF80 = ptDbl2 P1 := by rw [m3]; exact p2_f80
  have p3_fe4 : ptF n3.mem B 0xFE4 = P0 := by rw [m3]; exact p2_fe4
  have p3_1064 : ptF n3.mem B 0x1064 = P1 := by rw [m3]; exact p2_1064
  clear p2_b00 p2_1064 p2_fe4 p2_f80 p2_c80 p2_aa0 p2_a40 p2_9e0 p2_980 p2_900 p2_5a0 p2_540 p2_4e0 p2_480 p2_420 p2_3c0 p2_360 p2_300 p2_280 p2_200 a2_10c4 a2_1044 a2_960 a2_2e0 a2_260 a2_1e0 a2_1c0 a2_1a0 a2_180 a2_160 a2_140 a2_120 q2_f20 q2_ec0 q2_e60 q2_e00 q2_da0 q2_d40 q2_ce0 q2_c20 q2_bc0 q2_b60 g2_27 g2_26 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0x812: p2v_pa2F
  obtain ⟨n4, c4, s4, sp4, rk4, P4, K4, fr4⟩ := p2v_pa2F (cl := 0xC80) (cr := 0xF80)
    F E3 (PT0.p2v F fR3) s3 p2v_at_812 p2v_at_816 (by decide) (by decide) g3_2
    g3_10 g3_11 (by decide) (by decide) (by decide) (by decide)
    p3_c80 p3_f80 (tbl2_lt hP1 4) (ptDbl2_lt _)
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.keepL K4 (by decide)
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk4 (3 : Fin 32) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk4 (4 : Fin 32) (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB00 := by rw [rk4 (8 : Fin 32) (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 0x180 := by rw [rk4 (9 : Fin 32) (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [rk4 (18 : Fin 32) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk4 (19 : Fin 32) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rk4 (20 : Fin 32) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [rk4 (21 : Fin 32) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rk4 (22 : Fin 32) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [rk4 (23 : Fin 32) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = rem := by rw [rk4 (24 : Fin 32) (by decide), g3_24]
  have g4_26 : reg n4 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk4 (26 : Fin 32) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk4 (27 : Fin 32) (by decide), g3_27]
  have g4_2 : reg n4 sp = B + 0x21A0 := sp4
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0xB00, 0x60), (0xC80, 0x60)] := keep_kk3.trans K4
  clear keep_kk3
  have q4_b60 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_b60 j hj)
  have q4_bc0 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_bc0 j hj)
  have q4_c20 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_c20 j hj)
  have q4_ce0 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_ce0 j hj)
  have q4_d40 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_d40 j hj)
  have q4_da0 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_da0 j hj)
  have q4_e00 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_e00 j hj)
  have q4_e60 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_e60 j hj)
  have q4_ec0 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_ec0 j hj)
  have q4_f20 : ∀ j, j < 96 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_f20 j hj)
  have a4_120 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K4.acc (by decide) (by decide)).trans a3_120
  have a4_140 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K4.acc (by decide) (by decide)).trans a3_140
  have a4_160 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K4.acc (by decide) (by decide)).trans a3_160
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K4.acc (by decide) (by decide)).trans a3_180
  have a4_1a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K4.acc (by decide) (by decide)).trans a3_1a0
  have a4_1c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K4.acc (by decide) (by decide)).trans a3_1c0
  have a4_1e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K4.acc (by decide) (by decide)).trans a3_1e0
  have a4_260 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K4.acc (by decide) (by decide)).trans a3_260
  have a4_2e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K4.acc (by decide) (by decide)).trans a3_2e0
  have a4_960 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K4.acc (by decide) (by decide)).trans a3_960
  have a4_1044 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K4.acc (by decide) (by decide)).trans a3_1044
  have a4_10c4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K4.acc (by decide) (by decide)).trans a3_10c4
  have p4_200 : ptF n4.mem B 0x200 = P0 := (K4.pt (by decide) (by decide)).trans p3_200
  have p4_280 : ptF n4.mem B 0x280 = P1 := (K4.pt (by decide) (by decide)).trans p3_280
  have p4_300 : ptF n4.mem B 0x300 = tbl2 P0 0 := (K4.pt (by decide) (by decide)).trans p3_300
  have p4_360 : ptF n4.mem B 0x360 = tbl2 P0 1 := (K4.pt (by decide) (by decide)).trans p3_360
  have p4_3c0 : ptF n4.mem B 0x3C0 = tbl2 P0 2 := (K4.pt (by decide) (by decide)).trans p3_3c0
  have p4_420 : ptF n4.mem B 0x420 = tbl2 P0 3 := (K4.pt (by decide) (by decide)).trans p3_420
  have p4_480 : ptF n4.mem B 0x480 = tbl2 P0 4 := (K4.pt (by decide) (by decide)).trans p3_480
  have p4_4e0 : ptF n4.mem B 0x4E0 = tbl2 P0 5 := (K4.pt (by decide) (by decide)).trans p3_4e0
  have p4_540 : ptF n4.mem B 0x540 = tbl2 P0 6 := (K4.pt (by decide) (by decide)).trans p3_540
  have p4_5a0 : ptF n4.mem B 0x5A0 = tbl2 P0 7 := (K4.pt (by decide) (by decide)).trans p3_5a0
  have p4_900 : ptF n4.mem B 0x900 = P1 := (K4.pt (by decide) (by decide)).trans p3_900
  have p4_980 : ptF n4.mem B 0x980 = tbl2 P1 0 := (K4.pt (by decide) (by decide)).trans p3_980
  have p4_9e0 : ptF n4.mem B 0x9E0 = tbl2 P1 1 := (K4.pt (by decide) (by decide)).trans p3_9e0
  have p4_a40 : ptF n4.mem B 0xA40 = tbl2 P1 2 := (K4.pt (by decide) (by decide)).trans p3_a40
  have p4_aa0 : ptF n4.mem B 0xAA0 = tbl2 P1 3 := (K4.pt (by decide) (by decide)).trans p3_aa0
  have p4_b00 : ptF n4.mem B 0xB00 = tbl2 P1 4 := (K4.pt (by decide) (by decide)).trans p3_b00
  have p4_f80 : ptF n4.mem B 0xF80 = ptDbl2 P1 := (K4.pt (by decide) (by decide)).trans p3_f80
  have p4_fe4 : ptF n4.mem B 0xFE4 = P0 := (K4.pt (by decide) (by decide)).trans p3_fe4
  have p4_1064 : ptF n4.mem B 0x1064 = P1 := (K4.pt (by decide) (by decide)).trans p3_1064
  clear p3_1064 p3_fe4 p3_f80 p3_c80 p3_b00 p3_aa0 p3_a40 p3_9e0 p3_980 p3_900 p3_5a0 p3_540 p3_4e0 p3_480 p3_420 p3_3c0 p3_360 p3_300 p3_280 p3_200 a3_10c4 a3_1044 a3_960 a3_2e0 a3_260 a3_1e0 a3_1c0 a3_1a0 a3_180 a3_160 a3_140 a3_120 q3_f20 q3_ec0 q3_e60 q3_e00 q3_da0 q3_d40 q3_ce0 q3_c20 q3_bc0 q3_b60 g3_11 g3_10 g3_27 g3_26 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  have p4_c80 : ptF n4.mem B 0xC80 = tbl2 P1 5 := P4
  -- 0x81A
  obtain ⟨n5, c5, u5⟩ := s4.block p2vEcT1b81a E4.self p2vEcT1b81a_end
    ⟨trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem P2V n5 0x822 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock p2vEcT1b81a (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_18 : reg n5 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = rem := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_8 : reg n5 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB60 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vEcT1b81a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_9 : reg n5 (9 : Fin 32) = BitVec.ofNat 32 0x120 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vEcT1b81a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0xB00, 0x60), (0xC80, 0x60)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have q5_b60 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_b60 j hj
  have q5_bc0 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_bc0 j hj
  have q5_c20 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_c20 j hj
  have q5_ce0 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_ce0 j hj
  have q5_d40 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_d40 j hj
  have q5_da0 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_da0 j hj
  have q5_e00 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_e00 j hj
  have q5_e60 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_e60 j hj
  have q5_ec0 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_ec0 j hj
  have q5_f20 : ∀ j, j < 96 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_f20 j hj
  have a5_120 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m5]; exact a4_120
  have a5_140 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m5]; exact a4_140
  have a5_160 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m5]; exact a4_160
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m5]; exact a4_180
  have a5_1a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m5]; exact a4_1a0
  have a5_1c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m5]; exact a4_1c0
  have a5_1e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m5]; exact a4_1e0
  have a5_260 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m5]; exact a4_260
  have a5_2e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m5]; exact a4_2e0
  have a5_960 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m5]; exact a4_960
  have a5_1044 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m5]; exact a4_1044
  have a5_10c4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m5]; exact a4_10c4
  have p5_200 : ptF n5.mem B 0x200 = P0 := by rw [m5]; exact p4_200
  have p5_280 : ptF n5.mem B 0x280 = P1 := by rw [m5]; exact p4_280
  have p5_300 : ptF n5.mem B 0x300 = tbl2 P0 0 := by rw [m5]; exact p4_300
  have p5_360 : ptF n5.mem B 0x360 = tbl2 P0 1 := by rw [m5]; exact p4_360
  have p5_3c0 : ptF n5.mem B 0x3C0 = tbl2 P0 2 := by rw [m5]; exact p4_3c0
  have p5_420 : ptF n5.mem B 0x420 = tbl2 P0 3 := by rw [m5]; exact p4_420
  have p5_480 : ptF n5.mem B 0x480 = tbl2 P0 4 := by rw [m5]; exact p4_480
  have p5_4e0 : ptF n5.mem B 0x4E0 = tbl2 P0 5 := by rw [m5]; exact p4_4e0
  have p5_540 : ptF n5.mem B 0x540 = tbl2 P0 6 := by rw [m5]; exact p4_540
  have p5_5a0 : ptF n5.mem B 0x5A0 = tbl2 P0 7 := by rw [m5]; exact p4_5a0
  have p5_900 : ptF n5.mem B 0x900 = P1 := by rw [m5]; exact p4_900
  have p5_980 : ptF n5.mem B 0x980 = tbl2 P1 0 := by rw [m5]; exact p4_980
  have p5_9e0 : ptF n5.mem B 0x9E0 = tbl2 P1 1 := by rw [m5]; exact p4_9e0
  have p5_a40 : ptF n5.mem B 0xA40 = tbl2 P1 2 := by rw [m5]; exact p4_a40
  have p5_aa0 : ptF n5.mem B 0xAA0 = tbl2 P1 3 := by rw [m5]; exact p4_aa0
  have p5_b00 : ptF n5.mem B 0xB00 = tbl2 P1 4 := by rw [m5]; exact p4_b00
  have p5_c80 : ptF n5.mem B 0xC80 = tbl2 P1 5 := by rw [m5]; exact p4_c80
  have p5_f80 : ptF n5.mem B 0xF80 = ptDbl2 P1 := by rw [m5]; exact p4_f80
  have p5_fe4 : ptF n5.mem B 0xFE4 = P0 := by rw [m5]; exact p4_fe4
  have p5_1064 : ptF n5.mem B 0x1064 = P1 := by rw [m5]; exact p4_1064
  clear p4_1064 p4_fe4 p4_f80 p4_b00 p4_aa0 p4_a40 p4_9e0 p4_980 p4_900 p4_5a0 p4_540 p4_4e0 p4_480 p4_420 p4_3c0 p4_360 p4_300 p4_280 p4_200 a4_10c4 a4_1044 a4_960 a4_2e0 a4_260 a4_1e0 a4_1c0 a4_1a0 a4_180 a4_160 a4_140 a4_120 q4_f20 q4_ec0 q4_e60 q4_e00 q4_da0 q4_d40 q4_ce0 q4_c20 q4_bc0 q4_b60 g4_2 g4_27 g4_26 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 V4 E4 fR4 t4 fr4 K4 P4 rk4 sp4 s4 c4
  -- 0x822: branch, taken
  obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0x7EC p2v_at_822
    (by decide) (by rw [g5_9, s5.zero]; decide)
  have s6 : St n6.mem P2V n6 0x7EC (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, P2vR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB60 := by rw [u6.regs, g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 0x120 := by rw [u6.regs, g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [u6.regs, g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u6.regs, g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u6.regs, g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u6.regs, g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u6.regs, g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u6.regs, g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = rem := by rw [u6.regs, g5_24]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u6.regs, g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u6.regs, g5_27]
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0xB00, 0x60), (0xC80, 0x60)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have q6_b60 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_b60 j hj
  have q6_bc0 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_bc0 j hj
  have q6_c20 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_c20 j hj
  have q6_ce0 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_ce0 j hj
  have q6_d40 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_d40 j hj
  have q6_da0 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_da0 j hj
  have q6_e00 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_e00 j hj
  have q6_e60 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_e60 j hj
  have q6_ec0 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_ec0 j hj
  have q6_f20 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_f20 j hj
  have a6_120 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m6]; exact a5_120
  have a6_140 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m6]; exact a5_140
  have a6_160 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m6]; exact a5_160
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m6]; exact a5_180
  have a6_1a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m6]; exact a5_1a0
  have a6_1c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m6]; exact a5_1c0
  have a6_1e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m6]; exact a5_1e0
  have a6_260 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m6]; exact a5_260
  have a6_2e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m6]; exact a5_2e0
  have a6_960 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m6]; exact a5_960
  have a6_1044 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m6]; exact a5_1044
  have a6_10c4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m6]; exact a5_10c4
  have p6_200 : ptF n6.mem B 0x200 = P0 := by rw [m6]; exact p5_200
  have p6_280 : ptF n6.mem B 0x280 = P1 := by rw [m6]; exact p5_280
  have p6_300 : ptF n6.mem B 0x300 = tbl2 P0 0 := by rw [m6]; exact p5_300
  have p6_360 : ptF n6.mem B 0x360 = tbl2 P0 1 := by rw [m6]; exact p5_360
  have p6_3c0 : ptF n6.mem B 0x3C0 = tbl2 P0 2 := by rw [m6]; exact p5_3c0
  have p6_420 : ptF n6.mem B 0x420 = tbl2 P0 3 := by rw [m6]; exact p5_420
  have p6_480 : ptF n6.mem B 0x480 = tbl2 P0 4 := by rw [m6]; exact p5_480
  have p6_4e0 : ptF n6.mem B 0x4E0 = tbl2 P0 5 := by rw [m6]; exact p5_4e0
  have p6_540 : ptF n6.mem B 0x540 = tbl2 P0 6 := by rw [m6]; exact p5_540
  have p6_5a0 : ptF n6.mem B 0x5A0 = tbl2 P0 7 := by rw [m6]; exact p5_5a0
  have p6_900 : ptF n6.mem B 0x900 = P1 := by rw [m6]; exact p5_900
  have p6_980 : ptF n6.mem B 0x980 = tbl2 P1 0 := by rw [m6]; exact p5_980
  have p6_9e0 : ptF n6.mem B 0x9E0 = tbl2 P1 1 := by rw [m6]; exact p5_9e0
  have p6_a40 : ptF n6.mem B 0xA40 = tbl2 P1 2 := by rw [m6]; exact p5_a40
  have p6_aa0 : ptF n6.mem B 0xAA0 = tbl2 P1 3 := by rw [m6]; exact p5_aa0
  have p6_b00 : ptF n6.mem B 0xB00 = tbl2 P1 4 := by rw [m6]; exact p5_b00
  have p6_c80 : ptF n6.mem B 0xC80 = tbl2 P1 5 := by rw [m6]; exact p5_c80
  have p6_f80 : ptF n6.mem B 0xF80 = ptDbl2 P1 := by rw [m6]; exact p5_f80
  have p6_fe4 : ptF n6.mem B 0xFE4 = P0 := by rw [m6]; exact p5_fe4
  have p6_1064 : ptF n6.mem B 0x1064 = P1 := by rw [m6]; exact p5_1064
  clear p5_1064 p5_fe4 p5_f80 p5_c80 p5_b00 p5_aa0 p5_a40 p5_9e0 p5_980 p5_900 p5_5a0 p5_540 p5_4e0 p5_480 p5_420 p5_3c0 p5_360 p5_300 p5_280 p5_200 a5_10c4 a5_1044 a5_960 a5_2e0 a5_260 a5_1e0 a5_1c0 a5_1a0 a5_180 a5_160 a5_140 a5_120 q5_f20 q5_ec0 q5_e60 q5_e00 q5_da0 q5_d40 q5_ce0 q5_c20 q5_bc0 q5_b60 g5_9 g5_8 g5_27 g5_26 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5 p4_c80
  -- 0x7EC
  obtain ⟨n7, c7, u7⟩ := s6.block p2vEcT1b7ec E6.self p2vEcT1b7ec_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem P2V n7 0x7FA (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock p2vEcT1b7ec (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_8 : reg n7 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB60 := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 0x120 := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb7, runBlock_reg _ _ _ (20 : Fin 32) s6.zero (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = rem := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0xB60 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_11 : reg n7 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_12 : reg n7 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0xB00, 0x60), (0xC80, 0x60)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have q7_b60 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_b60 j hj
  have q7_bc0 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_bc0 j hj
  have q7_c20 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_c20 j hj
  have q7_ce0 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_ce0 j hj
  have q7_d40 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_d40 j hj
  have q7_da0 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_da0 j hj
  have q7_e00 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_e00 j hj
  have q7_e60 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_e60 j hj
  have q7_ec0 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_ec0 j hj
  have q7_f20 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_f20 j hj
  have a7_120 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m7]; exact a6_120
  have a7_140 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m7]; exact a6_140
  have a7_160 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m7]; exact a6_160
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m7]; exact a6_180
  have a7_1a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m7]; exact a6_1a0
  have a7_1c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m7]; exact a6_1c0
  have a7_1e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m7]; exact a6_1e0
  have a7_260 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m7]; exact a6_260
  have a7_2e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m7]; exact a6_2e0
  have a7_960 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m7]; exact a6_960
  have a7_1044 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m7]; exact a6_1044
  have a7_10c4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m7]; exact a6_10c4
  have p7_200 : ptF n7.mem B 0x200 = P0 := by rw [m7]; exact p6_200
  have p7_280 : ptF n7.mem B 0x280 = P1 := by rw [m7]; exact p6_280
  have p7_300 : ptF n7.mem B 0x300 = tbl2 P0 0 := by rw [m7]; exact p6_300
  have p7_360 : ptF n7.mem B 0x360 = tbl2 P0 1 := by rw [m7]; exact p6_360
  have p7_3c0 : ptF n7.mem B 0x3C0 = tbl2 P0 2 := by rw [m7]; exact p6_3c0
  have p7_420 : ptF n7.mem B 0x420 = tbl2 P0 3 := by rw [m7]; exact p6_420
  have p7_480 : ptF n7.mem B 0x480 = tbl2 P0 4 := by rw [m7]; exact p6_480
  have p7_4e0 : ptF n7.mem B 0x4E0 = tbl2 P0 5 := by rw [m7]; exact p6_4e0
  have p7_540 : ptF n7.mem B 0x540 = tbl2 P0 6 := by rw [m7]; exact p6_540
  have p7_5a0 : ptF n7.mem B 0x5A0 = tbl2 P0 7 := by rw [m7]; exact p6_5a0
  have p7_900 : ptF n7.mem B 0x900 = P1 := by rw [m7]; exact p6_900
  have p7_980 : ptF n7.mem B 0x980 = tbl2 P1 0 := by rw [m7]; exact p6_980
  have p7_9e0 : ptF n7.mem B 0x9E0 = tbl2 P1 1 := by rw [m7]; exact p6_9e0
  have p7_a40 : ptF n7.mem B 0xA40 = tbl2 P1 2 := by rw [m7]; exact p6_a40
  have p7_aa0 : ptF n7.mem B 0xAA0 = tbl2 P1 3 := by rw [m7]; exact p6_aa0
  have p7_b00 : ptF n7.mem B 0xB00 = tbl2 P1 4 := by rw [m7]; exact p6_b00
  have p7_c80 : ptF n7.mem B 0xC80 = tbl2 P1 5 := by rw [m7]; exact p6_c80
  have p7_f80 : ptF n7.mem B 0xF80 = ptDbl2 P1 := by rw [m7]; exact p6_f80
  have p7_fe4 : ptF n7.mem B 0xFE4 = P0 := by rw [m7]; exact p6_fe4
  have p7_1064 : ptF n7.mem B 0x1064 = P1 := by rw [m7]; exact p6_1064
  clear p6_1064 p6_fe4 p6_f80 p6_c80 p6_b00 p6_aa0 p6_a40 p6_9e0 p6_980 p6_900 p6_5a0 p6_540 p6_4e0 p6_480 p6_420 p6_3c0 p6_360 p6_300 p6_280 p6_200 a6_10c4 a6_1044 a6_960 a6_2e0 a6_260 a6_1e0 a6_1c0 a6_1a0 a6_180 a6_160 a6_140 a6_120 q6_f20 q6_ec0 q6_e60 q6_e00 q6_da0 q6_d40 q6_ce0 q6_c20 q6_bc0 q6_b60 g6_27 g6_26 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x7FA: memcpy
  obtain ⟨n8, P8, K8, X8⟩ := p2v_mc (c := 0xB60) (d := 0xC80) (N := 0x60) F E7 s7 p2v_at_7fa p2v_at_7fe
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
  have g8_8 : reg n8 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB60 := by rw [P8.regs (8 : Fin 32) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = BitVec.ofNat 32 0x120 := by rw [P8.regs (9 : Fin 32) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [P8.regs (18 : Fin 32) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P8.regs (19 : Fin 32) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P8.regs (20 : Fin 32) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P8.regs (21 : Fin 32) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P8.regs (22 : Fin 32) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P8.regs (23 : Fin 32) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = rem := by rw [P8.regs (24 : Fin 32) (by decide), g7_24]
  have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P8.regs (26 : Fin 32) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P8.regs (27 : Fin 32) (by decide), g7_27]
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have q8_bc0 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_bc0 j hj)
  have q8_c20 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_c20 j hj)
  have q8_ce0 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_ce0 j hj)
  have q8_d40 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_d40 j hj)
  have q8_da0 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_da0 j hj)
  have q8_e00 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_e00 j hj)
  have q8_e60 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_e60 j hj)
  have q8_ec0 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_ec0 j hj)
  have q8_f20 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_f20 j hj)
  have a8_120 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K8.acc (by decide) (by decide)).trans a7_120
  have a8_140 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K8.acc (by decide) (by decide)).trans a7_140
  have a8_160 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K8.acc (by decide) (by decide)).trans a7_160
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K8.acc (by decide) (by decide)).trans a7_180
  have a8_1a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K8.acc (by decide) (by decide)).trans a7_1a0
  have a8_1c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K8.acc (by decide) (by decide)).trans a7_1c0
  have a8_1e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K8.acc (by decide) (by decide)).trans a7_1e0
  have a8_260 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K8.acc (by decide) (by decide)).trans a7_260
  have a8_2e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K8.acc (by decide) (by decide)).trans a7_2e0
  have a8_960 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K8.acc (by decide) (by decide)).trans a7_960
  have a8_1044 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K8.acc (by decide) (by decide)).trans a7_1044
  have a8_10c4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K8.acc (by decide) (by decide)).trans a7_10c4
  have p8_200 : ptF n8.mem B 0x200 = P0 := (K8.pt (by decide) (by decide)).trans p7_200
  have p8_280 : ptF n8.mem B 0x280 = P1 := (K8.pt (by decide) (by decide)).trans p7_280
  have p8_300 : ptF n8.mem B 0x300 = tbl2 P0 0 := (K8.pt (by decide) (by decide)).trans p7_300
  have p8_360 : ptF n8.mem B 0x360 = tbl2 P0 1 := (K8.pt (by decide) (by decide)).trans p7_360
  have p8_3c0 : ptF n8.mem B 0x3C0 = tbl2 P0 2 := (K8.pt (by decide) (by decide)).trans p7_3c0
  have p8_420 : ptF n8.mem B 0x420 = tbl2 P0 3 := (K8.pt (by decide) (by decide)).trans p7_420
  have p8_480 : ptF n8.mem B 0x480 = tbl2 P0 4 := (K8.pt (by decide) (by decide)).trans p7_480
  have p8_4e0 : ptF n8.mem B 0x4E0 = tbl2 P0 5 := (K8.pt (by decide) (by decide)).trans p7_4e0
  have p8_540 : ptF n8.mem B 0x540 = tbl2 P0 6 := (K8.pt (by decide) (by decide)).trans p7_540
  have p8_5a0 : ptF n8.mem B 0x5A0 = tbl2 P0 7 := (K8.pt (by decide) (by decide)).trans p7_5a0
  have p8_900 : ptF n8.mem B 0x900 = P1 := (K8.pt (by decide) (by decide)).trans p7_900
  have p8_980 : ptF n8.mem B 0x980 = tbl2 P1 0 := (K8.pt (by decide) (by decide)).trans p7_980
  have p8_9e0 : ptF n8.mem B 0x9E0 = tbl2 P1 1 := (K8.pt (by decide) (by decide)).trans p7_9e0
  have p8_a40 : ptF n8.mem B 0xA40 = tbl2 P1 2 := (K8.pt (by decide) (by decide)).trans p7_a40
  have p8_aa0 : ptF n8.mem B 0xAA0 = tbl2 P1 3 := (K8.pt (by decide) (by decide)).trans p7_aa0
  have p8_b00 : ptF n8.mem B 0xB00 = tbl2 P1 4 := (K8.pt (by decide) (by decide)).trans p7_b00
  have p8_c80 : ptF n8.mem B 0xC80 = tbl2 P1 5 := (K8.pt (by decide) (by decide)).trans p7_c80
  have p8_f80 : ptF n8.mem B 0xF80 = ptDbl2 P1 := (K8.pt (by decide) (by decide)).trans p7_f80
  have p8_fe4 : ptF n8.mem B 0xFE4 = P0 := (K8.pt (by decide) (by decide)).trans p7_fe4
  have p8_1064 : ptF n8.mem B 0x1064 = P1 := (K8.pt (by decide) (by decide)).trans p7_1064
  have p8_b60 : ptF n8.mem B 0xB60 = tbl2 P1 5 := (ptF_cp X8 (by decide) (by decide) (by decide)).trans p7_c80
  clear p7_1064 p7_fe4 p7_f80 p7_c80 p7_b00 p7_aa0 p7_a40 p7_9e0 p7_980 p7_900 p7_5a0 p7_540 p7_4e0 p7_480 p7_420 p7_3c0 p7_360 p7_300 p7_280 p7_200 a7_10c4 a7_1044 a7_960 a7_2e0 a7_260 a7_1e0 a7_1c0 a7_1a0 a7_180 a7_160 a7_140 a7_120 q7_f20 q7_ec0 q7_e60 q7_e00 q7_da0 q7_d40 q7_ce0 q7_c20 q7_bc0 q7_b60 g7_12 g7_11 g7_10 g7_27 g7_26 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x802
  obtain ⟨n9, c9, u9⟩ := s8.block p2vEcT1b802 E8.self p2vEcT1b802_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem P2V n9 0x812 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock p2vEcT1b802 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_8 : reg n9 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB60 := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = BitVec.ofNat 32 0x120 := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
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
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vEcT1b802, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_11 : reg n9 a1 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vEcT1b802, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have q9_bc0 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_bc0 j hj
  have q9_c20 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_c20 j hj
  have q9_ce0 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_ce0 j hj
  have q9_d40 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_d40 j hj
  have q9_da0 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_da0 j hj
  have q9_e00 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_e00 j hj
  have q9_e60 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_e60 j hj
  have q9_ec0 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_ec0 j hj
  have q9_f20 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_f20 j hj
  have a9_120 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m9]; exact a8_120
  have a9_140 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m9]; exact a8_140
  have a9_160 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m9]; exact a8_160
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m9]; exact a8_180
  have a9_1a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m9]; exact a8_1a0
  have a9_1c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m9]; exact a8_1c0
  have a9_1e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m9]; exact a8_1e0
  have a9_260 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m9]; exact a8_260
  have a9_2e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m9]; exact a8_2e0
  have a9_960 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m9]; exact a8_960
  have a9_1044 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m9]; exact a8_1044
  have a9_10c4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m9]; exact a8_10c4
  have p9_200 : ptF n9.mem B 0x200 = P0 := by rw [m9]; exact p8_200
  have p9_280 : ptF n9.mem B 0x280 = P1 := by rw [m9]; exact p8_280
  have p9_300 : ptF n9.mem B 0x300 = tbl2 P0 0 := by rw [m9]; exact p8_300
  have p9_360 : ptF n9.mem B 0x360 = tbl2 P0 1 := by rw [m9]; exact p8_360
  have p9_3c0 : ptF n9.mem B 0x3C0 = tbl2 P0 2 := by rw [m9]; exact p8_3c0
  have p9_420 : ptF n9.mem B 0x420 = tbl2 P0 3 := by rw [m9]; exact p8_420
  have p9_480 : ptF n9.mem B 0x480 = tbl2 P0 4 := by rw [m9]; exact p8_480
  have p9_4e0 : ptF n9.mem B 0x4E0 = tbl2 P0 5 := by rw [m9]; exact p8_4e0
  have p9_540 : ptF n9.mem B 0x540 = tbl2 P0 6 := by rw [m9]; exact p8_540
  have p9_5a0 : ptF n9.mem B 0x5A0 = tbl2 P0 7 := by rw [m9]; exact p8_5a0
  have p9_900 : ptF n9.mem B 0x900 = P1 := by rw [m9]; exact p8_900
  have p9_980 : ptF n9.mem B 0x980 = tbl2 P1 0 := by rw [m9]; exact p8_980
  have p9_9e0 : ptF n9.mem B 0x9E0 = tbl2 P1 1 := by rw [m9]; exact p8_9e0
  have p9_a40 : ptF n9.mem B 0xA40 = tbl2 P1 2 := by rw [m9]; exact p8_a40
  have p9_aa0 : ptF n9.mem B 0xAA0 = tbl2 P1 3 := by rw [m9]; exact p8_aa0
  have p9_b00 : ptF n9.mem B 0xB00 = tbl2 P1 4 := by rw [m9]; exact p8_b00
  have p9_b60 : ptF n9.mem B 0xB60 = tbl2 P1 5 := by rw [m9]; exact p8_b60
  have p9_c80 : ptF n9.mem B 0xC80 = tbl2 P1 5 := by rw [m9]; exact p8_c80
  have p9_f80 : ptF n9.mem B 0xF80 = ptDbl2 P1 := by rw [m9]; exact p8_f80
  have p9_fe4 : ptF n9.mem B 0xFE4 = P0 := by rw [m9]; exact p8_fe4
  have p9_1064 : ptF n9.mem B 0x1064 = P1 := by rw [m9]; exact p8_1064
  clear p8_b60 p8_1064 p8_fe4 p8_f80 p8_c80 p8_b00 p8_aa0 p8_a40 p8_9e0 p8_980 p8_900 p8_5a0 p8_540 p8_4e0 p8_480 p8_420 p8_3c0 p8_360 p8_300 p8_280 p8_200 a8_10c4 a8_1044 a8_960 a8_2e0 a8_260 a8_1e0 a8_1c0 a8_1a0 a8_180 a8_160 a8_140 a8_120 q8_f20 q8_ec0 q8_e60 q8_e00 q8_da0 q8_d40 q8_ce0 q8_c20 q8_bc0 g8_27 g8_26 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 s8 X8 K8 P8
  -- 0x812: p2v_pa2F
  obtain ⟨n10, c10, s10, sp10, rk10, P10, K10, fr10⟩ := p2v_pa2F (cl := 0xC80) (cr := 0xF80)
    F E9 (PT0.p2v F fR9) s9 p2v_at_812 p2v_at_816 (by decide) (by decide) g9_2
    g9_10 g9_11 (by decide) (by decide) (by decide) (by decide)
    p9_c80 p9_f80 (tbl2_lt hP1 5) (ptDbl2_lt _)
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.keepL K10 (by decide)
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk10 (3 : Fin 32) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk10 (4 : Fin 32) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xB60 := by rw [rk10 (8 : Fin 32) (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = BitVec.ofNat 32 0x120 := by rw [rk10 (9 : Fin 32) (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [rk10 (18 : Fin 32) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk10 (19 : Fin 32) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rk10 (20 : Fin 32) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [rk10 (21 : Fin 32) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rk10 (22 : Fin 32) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [rk10 (23 : Fin 32) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = rem := by rw [rk10 (24 : Fin 32) (by decide), g9_24]
  have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk10 (26 : Fin 32) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk10 (27 : Fin 32) (by decide), g9_27]
  have g10_2 : reg n10 sp = B + 0x21A0 := sp10
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60)] := keep_kk9.trans K10
  clear keep_kk9
  have q10_bc0 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_bc0 j hj)
  have q10_c20 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_c20 j hj)
  have q10_ce0 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_ce0 j hj)
  have q10_d40 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_d40 j hj)
  have q10_da0 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_da0 j hj)
  have q10_e00 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_e00 j hj)
  have q10_e60 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_e60 j hj)
  have q10_ec0 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_ec0 j hj)
  have q10_f20 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_f20 j hj)
  have a10_120 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K10.acc (by decide) (by decide)).trans a9_120
  have a10_140 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K10.acc (by decide) (by decide)).trans a9_140
  have a10_160 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K10.acc (by decide) (by decide)).trans a9_160
  have a10_180 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K10.acc (by decide) (by decide)).trans a9_180
  have a10_1a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K10.acc (by decide) (by decide)).trans a9_1a0
  have a10_1c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K10.acc (by decide) (by decide)).trans a9_1c0
  have a10_1e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K10.acc (by decide) (by decide)).trans a9_1e0
  have a10_260 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K10.acc (by decide) (by decide)).trans a9_260
  have a10_2e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K10.acc (by decide) (by decide)).trans a9_2e0
  have a10_960 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K10.acc (by decide) (by decide)).trans a9_960
  have a10_1044 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K10.acc (by decide) (by decide)).trans a9_1044
  have a10_10c4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K10.acc (by decide) (by decide)).trans a9_10c4
  have p10_200 : ptF n10.mem B 0x200 = P0 := (K10.pt (by decide) (by decide)).trans p9_200
  have p10_280 : ptF n10.mem B 0x280 = P1 := (K10.pt (by decide) (by decide)).trans p9_280
  have p10_300 : ptF n10.mem B 0x300 = tbl2 P0 0 := (K10.pt (by decide) (by decide)).trans p9_300
  have p10_360 : ptF n10.mem B 0x360 = tbl2 P0 1 := (K10.pt (by decide) (by decide)).trans p9_360
  have p10_3c0 : ptF n10.mem B 0x3C0 = tbl2 P0 2 := (K10.pt (by decide) (by decide)).trans p9_3c0
  have p10_420 : ptF n10.mem B 0x420 = tbl2 P0 3 := (K10.pt (by decide) (by decide)).trans p9_420
  have p10_480 : ptF n10.mem B 0x480 = tbl2 P0 4 := (K10.pt (by decide) (by decide)).trans p9_480
  have p10_4e0 : ptF n10.mem B 0x4E0 = tbl2 P0 5 := (K10.pt (by decide) (by decide)).trans p9_4e0
  have p10_540 : ptF n10.mem B 0x540 = tbl2 P0 6 := (K10.pt (by decide) (by decide)).trans p9_540
  have p10_5a0 : ptF n10.mem B 0x5A0 = tbl2 P0 7 := (K10.pt (by decide) (by decide)).trans p9_5a0
  have p10_900 : ptF n10.mem B 0x900 = P1 := (K10.pt (by decide) (by decide)).trans p9_900
  have p10_980 : ptF n10.mem B 0x980 = tbl2 P1 0 := (K10.pt (by decide) (by decide)).trans p9_980
  have p10_9e0 : ptF n10.mem B 0x9E0 = tbl2 P1 1 := (K10.pt (by decide) (by decide)).trans p9_9e0
  have p10_a40 : ptF n10.mem B 0xA40 = tbl2 P1 2 := (K10.pt (by decide) (by decide)).trans p9_a40
  have p10_aa0 : ptF n10.mem B 0xAA0 = tbl2 P1 3 := (K10.pt (by decide) (by decide)).trans p9_aa0
  have p10_b00 : ptF n10.mem B 0xB00 = tbl2 P1 4 := (K10.pt (by decide) (by decide)).trans p9_b00
  have p10_b60 : ptF n10.mem B 0xB60 = tbl2 P1 5 := (K10.pt (by decide) (by decide)).trans p9_b60
  have p10_f80 : ptF n10.mem B 0xF80 = ptDbl2 P1 := (K10.pt (by decide) (by decide)).trans p9_f80
  have p10_fe4 : ptF n10.mem B 0xFE4 = P0 := (K10.pt (by decide) (by decide)).trans p9_fe4
  have p10_1064 : ptF n10.mem B 0x1064 = P1 := (K10.pt (by decide) (by decide)).trans p9_1064
  clear p9_1064 p9_fe4 p9_f80 p9_c80 p9_b60 p9_b00 p9_aa0 p9_a40 p9_9e0 p9_980 p9_900 p9_5a0 p9_540 p9_4e0 p9_480 p9_420 p9_3c0 p9_360 p9_300 p9_280 p9_200 a9_10c4 a9_1044 a9_960 a9_2e0 a9_260 a9_1e0 a9_1c0 a9_1a0 a9_180 a9_160 a9_140 a9_120 q9_f20 q9_ec0 q9_e60 q9_e00 q9_da0 q9_d40 q9_ce0 q9_c20 q9_bc0 g9_11 g9_10 g9_27 g9_26 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  have p10_c80 : ptF n10.mem B 0xC80 = tbl2 P1 6 := P10
  -- 0x81A
  obtain ⟨n11, c11, u11⟩ := s10.block p2vEcT1b81a E10.self p2vEcT1b81a_end
    ⟨trivial, trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem P2V n11 0x822 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock p2vEcT1b81a (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
  have g11_18 : reg n11 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = rem := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_8 : reg n11 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xBC0 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vEcT1b81a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g11_9 : reg n11 (9 : Fin 32) = BitVec.ofNat 32 0xC0 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, p2vEcT1b81a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have q11_bc0 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_bc0 j hj
  have q11_c20 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_c20 j hj
  have q11_ce0 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_ce0 j hj
  have q11_d40 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_d40 j hj
  have q11_da0 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_da0 j hj
  have q11_e00 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_e00 j hj
  have q11_e60 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_e60 j hj
  have q11_ec0 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_ec0 j hj
  have q11_f20 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_f20 j hj
  have a11_120 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m11]; exact a10_120
  have a11_140 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m11]; exact a10_140
  have a11_160 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m11]; exact a10_160
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m11]; exact a10_180
  have a11_1a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m11]; exact a10_1a0
  have a11_1c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m11]; exact a10_1c0
  have a11_1e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m11]; exact a10_1e0
  have a11_260 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m11]; exact a10_260
  have a11_2e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m11]; exact a10_2e0
  have a11_960 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m11]; exact a10_960
  have a11_1044 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m11]; exact a10_1044
  have a11_10c4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m11]; exact a10_10c4
  have p11_200 : ptF n11.mem B 0x200 = P0 := by rw [m11]; exact p10_200
  have p11_280 : ptF n11.mem B 0x280 = P1 := by rw [m11]; exact p10_280
  have p11_300 : ptF n11.mem B 0x300 = tbl2 P0 0 := by rw [m11]; exact p10_300
  have p11_360 : ptF n11.mem B 0x360 = tbl2 P0 1 := by rw [m11]; exact p10_360
  have p11_3c0 : ptF n11.mem B 0x3C0 = tbl2 P0 2 := by rw [m11]; exact p10_3c0
  have p11_420 : ptF n11.mem B 0x420 = tbl2 P0 3 := by rw [m11]; exact p10_420
  have p11_480 : ptF n11.mem B 0x480 = tbl2 P0 4 := by rw [m11]; exact p10_480
  have p11_4e0 : ptF n11.mem B 0x4E0 = tbl2 P0 5 := by rw [m11]; exact p10_4e0
  have p11_540 : ptF n11.mem B 0x540 = tbl2 P0 6 := by rw [m11]; exact p10_540
  have p11_5a0 : ptF n11.mem B 0x5A0 = tbl2 P0 7 := by rw [m11]; exact p10_5a0
  have p11_900 : ptF n11.mem B 0x900 = P1 := by rw [m11]; exact p10_900
  have p11_980 : ptF n11.mem B 0x980 = tbl2 P1 0 := by rw [m11]; exact p10_980
  have p11_9e0 : ptF n11.mem B 0x9E0 = tbl2 P1 1 := by rw [m11]; exact p10_9e0
  have p11_a40 : ptF n11.mem B 0xA40 = tbl2 P1 2 := by rw [m11]; exact p10_a40
  have p11_aa0 : ptF n11.mem B 0xAA0 = tbl2 P1 3 := by rw [m11]; exact p10_aa0
  have p11_b00 : ptF n11.mem B 0xB00 = tbl2 P1 4 := by rw [m11]; exact p10_b00
  have p11_b60 : ptF n11.mem B 0xB60 = tbl2 P1 5 := by rw [m11]; exact p10_b60
  have p11_c80 : ptF n11.mem B 0xC80 = tbl2 P1 6 := by rw [m11]; exact p10_c80
  have p11_f80 : ptF n11.mem B 0xF80 = ptDbl2 P1 := by rw [m11]; exact p10_f80
  have p11_fe4 : ptF n11.mem B 0xFE4 = P0 := by rw [m11]; exact p10_fe4
  have p11_1064 : ptF n11.mem B 0x1064 = P1 := by rw [m11]; exact p10_1064
  clear p10_1064 p10_fe4 p10_f80 p10_b60 p10_b00 p10_aa0 p10_a40 p10_9e0 p10_980 p10_900 p10_5a0 p10_540 p10_4e0 p10_480 p10_420 p10_3c0 p10_360 p10_300 p10_280 p10_200 a10_10c4 a10_1044 a10_960 a10_2e0 a10_260 a10_1e0 a10_1c0 a10_1a0 a10_180 a10_160 a10_140 a10_120 q10_f20 q10_ec0 q10_e60 q10_e00 q10_da0 q10_d40 q10_ce0 q10_c20 q10_bc0 g10_2 g10_27 g10_26 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 V10 E10 fR10 t10 fr10 K10 P10 rk10 sp10 s10 c10
  -- 0x822: branch, taken
  obtain ⟨n12, d12, u12⟩ := s11.taken E11.self 0x7EC p2v_at_822
    (by decide) (by rw [g11_9, s11.zero]; decide)
  have s12 : St n12.mem P2V n12 0x7EC (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, P2vR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, P2vR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : P2vCode n12.mem := E11.fr F fr12
  have V12 : P2vSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xBC0 := by rw [u12.regs, g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = BitVec.ofNat 32 0xC0 := by rw [u12.regs, g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [u12.regs, g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u12.regs, g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u12.regs, g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u12.regs, g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u12.regs, g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u12.regs, g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = rem := by rw [u12.regs, g11_24]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u12.regs, g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u12.regs, g11_27]
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have q12_bc0 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_bc0 j hj
  have q12_c20 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_c20 j hj
  have q12_ce0 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_ce0 j hj
  have q12_d40 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_d40 j hj
  have q12_da0 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_da0 j hj
  have q12_e00 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_e00 j hj
  have q12_e60 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_e60 j hj
  have q12_ec0 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_ec0 j hj
  have q12_f20 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_f20 j hj
  have a12_120 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m12]; exact a11_120
  have a12_140 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m12]; exact a11_140
  have a12_160 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m12]; exact a11_160
  have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m12]; exact a11_180
  have a12_1a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m12]; exact a11_1a0
  have a12_1c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m12]; exact a11_1c0
  have a12_1e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m12]; exact a11_1e0
  have a12_260 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m12]; exact a11_260
  have a12_2e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m12]; exact a11_2e0
  have a12_960 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m12]; exact a11_960
  have a12_1044 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m12]; exact a11_1044
  have a12_10c4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m12]; exact a11_10c4
  have p12_200 : ptF n12.mem B 0x200 = P0 := by rw [m12]; exact p11_200
  have p12_280 : ptF n12.mem B 0x280 = P1 := by rw [m12]; exact p11_280
  have p12_300 : ptF n12.mem B 0x300 = tbl2 P0 0 := by rw [m12]; exact p11_300
  have p12_360 : ptF n12.mem B 0x360 = tbl2 P0 1 := by rw [m12]; exact p11_360
  have p12_3c0 : ptF n12.mem B 0x3C0 = tbl2 P0 2 := by rw [m12]; exact p11_3c0
  have p12_420 : ptF n12.mem B 0x420 = tbl2 P0 3 := by rw [m12]; exact p11_420
  have p12_480 : ptF n12.mem B 0x480 = tbl2 P0 4 := by rw [m12]; exact p11_480
  have p12_4e0 : ptF n12.mem B 0x4E0 = tbl2 P0 5 := by rw [m12]; exact p11_4e0
  have p12_540 : ptF n12.mem B 0x540 = tbl2 P0 6 := by rw [m12]; exact p11_540
  have p12_5a0 : ptF n12.mem B 0x5A0 = tbl2 P0 7 := by rw [m12]; exact p11_5a0
  have p12_900 : ptF n12.mem B 0x900 = P1 := by rw [m12]; exact p11_900
  have p12_980 : ptF n12.mem B 0x980 = tbl2 P1 0 := by rw [m12]; exact p11_980
  have p12_9e0 : ptF n12.mem B 0x9E0 = tbl2 P1 1 := by rw [m12]; exact p11_9e0
  have p12_a40 : ptF n12.mem B 0xA40 = tbl2 P1 2 := by rw [m12]; exact p11_a40
  have p12_aa0 : ptF n12.mem B 0xAA0 = tbl2 P1 3 := by rw [m12]; exact p11_aa0
  have p12_b00 : ptF n12.mem B 0xB00 = tbl2 P1 4 := by rw [m12]; exact p11_b00
  have p12_b60 : ptF n12.mem B 0xB60 = tbl2 P1 5 := by rw [m12]; exact p11_b60
  have p12_c80 : ptF n12.mem B 0xC80 = tbl2 P1 6 := by rw [m12]; exact p11_c80
  have p12_f80 : ptF n12.mem B 0xF80 = ptDbl2 P1 := by rw [m12]; exact p11_f80
  have p12_fe4 : ptF n12.mem B 0xFE4 = P0 := by rw [m12]; exact p11_fe4
  have p12_1064 : ptF n12.mem B 0x1064 = P1 := by rw [m12]; exact p11_1064
  clear p11_1064 p11_fe4 p11_f80 p11_c80 p11_b60 p11_b00 p11_aa0 p11_a40 p11_9e0 p11_980 p11_900 p11_5a0 p11_540 p11_4e0 p11_480 p11_420 p11_3c0 p11_360 p11_300 p11_280 p11_200 a11_10c4 a11_1044 a11_960 a11_2e0 a11_260 a11_1e0 a11_1c0 a11_1a0 a11_180 a11_160 a11_140 a11_120 q11_f20 q11_ec0 q11_e60 q11_e00 q11_da0 q11_d40 q11_ce0 q11_c20 q11_bc0 g11_9 g11_8 g11_27 g11_26 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11 p10_c80
  -- 0x7EC
  obtain ⟨n13, c13, u13⟩ := s12.block p2vEcT1b7ec E12.self p2vEcT1b7ec_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem P2V n13 0x7FA (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock p2vEcT1b7ec (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_8 : reg n13 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xBC0 := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = BitVec.ofNat 32 0xC0 := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = rem := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_26 : reg n13 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0xBC0 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g13_11 : reg n13 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have q13_bc0 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xBC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_bc0 j hj
  have q13_c20 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_c20 j hj
  have q13_ce0 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_ce0 j hj
  have q13_d40 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_d40 j hj
  have q13_da0 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_da0 j hj
  have q13_e00 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_e00 j hj
  have q13_e60 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_e60 j hj
  have q13_ec0 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_ec0 j hj
  have q13_f20 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_f20 j hj
  have a13_120 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m13]; exact a12_120
  have a13_140 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m13]; exact a12_140
  have a13_160 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m13]; exact a12_160
  have a13_180 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m13]; exact a12_180
  have a13_1a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m13]; exact a12_1a0
  have a13_1c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m13]; exact a12_1c0
  have a13_1e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m13]; exact a12_1e0
  have a13_260 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m13]; exact a12_260
  have a13_2e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m13]; exact a12_2e0
  have a13_960 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m13]; exact a12_960
  have a13_1044 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m13]; exact a12_1044
  have a13_10c4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m13]; exact a12_10c4
  have p13_200 : ptF n13.mem B 0x200 = P0 := by rw [m13]; exact p12_200
  have p13_280 : ptF n13.mem B 0x280 = P1 := by rw [m13]; exact p12_280
  have p13_300 : ptF n13.mem B 0x300 = tbl2 P0 0 := by rw [m13]; exact p12_300
  have p13_360 : ptF n13.mem B 0x360 = tbl2 P0 1 := by rw [m13]; exact p12_360
  have p13_3c0 : ptF n13.mem B 0x3C0 = tbl2 P0 2 := by rw [m13]; exact p12_3c0
  have p13_420 : ptF n13.mem B 0x420 = tbl2 P0 3 := by rw [m13]; exact p12_420
  have p13_480 : ptF n13.mem B 0x480 = tbl2 P0 4 := by rw [m13]; exact p12_480
  have p13_4e0 : ptF n13.mem B 0x4E0 = tbl2 P0 5 := by rw [m13]; exact p12_4e0
  have p13_540 : ptF n13.mem B 0x540 = tbl2 P0 6 := by rw [m13]; exact p12_540
  have p13_5a0 : ptF n13.mem B 0x5A0 = tbl2 P0 7 := by rw [m13]; exact p12_5a0
  have p13_900 : ptF n13.mem B 0x900 = P1 := by rw [m13]; exact p12_900
  have p13_980 : ptF n13.mem B 0x980 = tbl2 P1 0 := by rw [m13]; exact p12_980
  have p13_9e0 : ptF n13.mem B 0x9E0 = tbl2 P1 1 := by rw [m13]; exact p12_9e0
  have p13_a40 : ptF n13.mem B 0xA40 = tbl2 P1 2 := by rw [m13]; exact p12_a40
  have p13_aa0 : ptF n13.mem B 0xAA0 = tbl2 P1 3 := by rw [m13]; exact p12_aa0
  have p13_b00 : ptF n13.mem B 0xB00 = tbl2 P1 4 := by rw [m13]; exact p12_b00
  have p13_b60 : ptF n13.mem B 0xB60 = tbl2 P1 5 := by rw [m13]; exact p12_b60
  have p13_c80 : ptF n13.mem B 0xC80 = tbl2 P1 6 := by rw [m13]; exact p12_c80
  have p13_f80 : ptF n13.mem B 0xF80 = ptDbl2 P1 := by rw [m13]; exact p12_f80
  have p13_fe4 : ptF n13.mem B 0xFE4 = P0 := by rw [m13]; exact p12_fe4
  have p13_1064 : ptF n13.mem B 0x1064 = P1 := by rw [m13]; exact p12_1064
  clear p12_1064 p12_fe4 p12_f80 p12_c80 p12_b60 p12_b00 p12_aa0 p12_a40 p12_9e0 p12_980 p12_900 p12_5a0 p12_540 p12_4e0 p12_480 p12_420 p12_3c0 p12_360 p12_300 p12_280 p12_200 a12_10c4 a12_1044 a12_960 a12_2e0 a12_260 a12_1e0 a12_1c0 a12_1a0 a12_180 a12_160 a12_140 a12_120 q12_f20 q12_ec0 q12_e60 q12_e00 q12_da0 q12_d40 q12_ce0 q12_c20 q12_bc0 g12_27 g12_26 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x7FA: memcpy
  obtain ⟨n14, P14, K14, X14⟩ := p2v_mc (c := 0xBC0) (d := 0xC80) (N := 0x60) F E13 s13 p2v_at_7fa p2v_at_7fe
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
  have g14_8 : reg n14 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xBC0 := by rw [P14.regs (8 : Fin 32) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = BitVec.ofNat 32 0xC0 := by rw [P14.regs (9 : Fin 32) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [P14.regs (18 : Fin 32) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P14.regs (19 : Fin 32) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P14.regs (20 : Fin 32) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P14.regs (21 : Fin 32) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P14.regs (22 : Fin 32) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P14.regs (23 : Fin 32) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = rem := by rw [P14.regs (24 : Fin 32) (by decide), g13_24]
  have g14_26 : reg n14 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P14.regs (26 : Fin 32) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P14.regs (27 : Fin 32) (by decide), g13_27]
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have q14_c20 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_c20 j hj)
  have q14_ce0 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_ce0 j hj)
  have q14_d40 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_d40 j hj)
  have q14_da0 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_da0 j hj)
  have q14_e00 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_e00 j hj)
  have q14_e60 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_e60 j hj)
  have q14_ec0 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_ec0 j hj)
  have q14_f20 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_f20 j hj)
  have a14_120 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K14.acc (by decide) (by decide)).trans a13_120
  have a14_140 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K14.acc (by decide) (by decide)).trans a13_140
  have a14_160 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K14.acc (by decide) (by decide)).trans a13_160
  have a14_180 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K14.acc (by decide) (by decide)).trans a13_180
  have a14_1a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K14.acc (by decide) (by decide)).trans a13_1a0
  have a14_1c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K14.acc (by decide) (by decide)).trans a13_1c0
  have a14_1e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K14.acc (by decide) (by decide)).trans a13_1e0
  have a14_260 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K14.acc (by decide) (by decide)).trans a13_260
  have a14_2e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K14.acc (by decide) (by decide)).trans a13_2e0
  have a14_960 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K14.acc (by decide) (by decide)).trans a13_960
  have a14_1044 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K14.acc (by decide) (by decide)).trans a13_1044
  have a14_10c4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K14.acc (by decide) (by decide)).trans a13_10c4
  have p14_200 : ptF n14.mem B 0x200 = P0 := (K14.pt (by decide) (by decide)).trans p13_200
  have p14_280 : ptF n14.mem B 0x280 = P1 := (K14.pt (by decide) (by decide)).trans p13_280
  have p14_300 : ptF n14.mem B 0x300 = tbl2 P0 0 := (K14.pt (by decide) (by decide)).trans p13_300
  have p14_360 : ptF n14.mem B 0x360 = tbl2 P0 1 := (K14.pt (by decide) (by decide)).trans p13_360
  have p14_3c0 : ptF n14.mem B 0x3C0 = tbl2 P0 2 := (K14.pt (by decide) (by decide)).trans p13_3c0
  have p14_420 : ptF n14.mem B 0x420 = tbl2 P0 3 := (K14.pt (by decide) (by decide)).trans p13_420
  have p14_480 : ptF n14.mem B 0x480 = tbl2 P0 4 := (K14.pt (by decide) (by decide)).trans p13_480
  have p14_4e0 : ptF n14.mem B 0x4E0 = tbl2 P0 5 := (K14.pt (by decide) (by decide)).trans p13_4e0
  have p14_540 : ptF n14.mem B 0x540 = tbl2 P0 6 := (K14.pt (by decide) (by decide)).trans p13_540
  have p14_5a0 : ptF n14.mem B 0x5A0 = tbl2 P0 7 := (K14.pt (by decide) (by decide)).trans p13_5a0
  have p14_900 : ptF n14.mem B 0x900 = P1 := (K14.pt (by decide) (by decide)).trans p13_900
  have p14_980 : ptF n14.mem B 0x980 = tbl2 P1 0 := (K14.pt (by decide) (by decide)).trans p13_980
  have p14_9e0 : ptF n14.mem B 0x9E0 = tbl2 P1 1 := (K14.pt (by decide) (by decide)).trans p13_9e0
  have p14_a40 : ptF n14.mem B 0xA40 = tbl2 P1 2 := (K14.pt (by decide) (by decide)).trans p13_a40
  have p14_aa0 : ptF n14.mem B 0xAA0 = tbl2 P1 3 := (K14.pt (by decide) (by decide)).trans p13_aa0
  have p14_b00 : ptF n14.mem B 0xB00 = tbl2 P1 4 := (K14.pt (by decide) (by decide)).trans p13_b00
  have p14_b60 : ptF n14.mem B 0xB60 = tbl2 P1 5 := (K14.pt (by decide) (by decide)).trans p13_b60
  have p14_c80 : ptF n14.mem B 0xC80 = tbl2 P1 6 := (K14.pt (by decide) (by decide)).trans p13_c80
  have p14_f80 : ptF n14.mem B 0xF80 = ptDbl2 P1 := (K14.pt (by decide) (by decide)).trans p13_f80
  have p14_fe4 : ptF n14.mem B 0xFE4 = P0 := (K14.pt (by decide) (by decide)).trans p13_fe4
  have p14_1064 : ptF n14.mem B 0x1064 = P1 := (K14.pt (by decide) (by decide)).trans p13_1064
  have p14_bc0 : ptF n14.mem B 0xBC0 = tbl2 P1 6 := (ptF_cp X14 (by decide) (by decide) (by decide)).trans p13_c80
  clear p13_1064 p13_fe4 p13_f80 p13_c80 p13_b60 p13_b00 p13_aa0 p13_a40 p13_9e0 p13_980 p13_900 p13_5a0 p13_540 p13_4e0 p13_480 p13_420 p13_3c0 p13_360 p13_300 p13_280 p13_200 a13_10c4 a13_1044 a13_960 a13_2e0 a13_260 a13_1e0 a13_1c0 a13_1a0 a13_180 a13_160 a13_140 a13_120 q13_f20 q13_ec0 q13_e60 q13_e00 q13_da0 q13_d40 q13_ce0 q13_c20 q13_bc0 g13_12 g13_11 g13_10 g13_27 g13_26 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x802
  obtain ⟨n15, c15, u15⟩ := s14.block p2vEcT1b802 E14.self p2vEcT1b802_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem P2V n15 0x812 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock p2vEcT1b802 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
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
  have g15_8 : reg n15 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xBC0 := by
    rw [rb15, runBlock_reg _ _ _ (8 : Fin 32) s14.zero (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = BitVec.ofNat 32 0xC0 := by
    rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb15, runBlock_reg _ _ _ (20 : Fin 32) s14.zero (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = rem := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_26 : reg n15 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vEcT1b802, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, p2vEcT1b802, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have q15_c20 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_c20 j hj
  have q15_ce0 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_ce0 j hj
  have q15_d40 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_d40 j hj
  have q15_da0 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_da0 j hj
  have q15_e00 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_e00 j hj
  have q15_e60 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_e60 j hj
  have q15_ec0 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_ec0 j hj
  have q15_f20 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_f20 j hj
  have a15_120 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m15]; exact a14_120
  have a15_140 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m15]; exact a14_140
  have a15_160 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m15]; exact a14_160
  have a15_180 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m15]; exact a14_180
  have a15_1a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m15]; exact a14_1a0
  have a15_1c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m15]; exact a14_1c0
  have a15_1e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m15]; exact a14_1e0
  have a15_260 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m15]; exact a14_260
  have a15_2e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m15]; exact a14_2e0
  have a15_960 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m15]; exact a14_960
  have a15_1044 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m15]; exact a14_1044
  have a15_10c4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m15]; exact a14_10c4
  have p15_200 : ptF n15.mem B 0x200 = P0 := by rw [m15]; exact p14_200
  have p15_280 : ptF n15.mem B 0x280 = P1 := by rw [m15]; exact p14_280
  have p15_300 : ptF n15.mem B 0x300 = tbl2 P0 0 := by rw [m15]; exact p14_300
  have p15_360 : ptF n15.mem B 0x360 = tbl2 P0 1 := by rw [m15]; exact p14_360
  have p15_3c0 : ptF n15.mem B 0x3C0 = tbl2 P0 2 := by rw [m15]; exact p14_3c0
  have p15_420 : ptF n15.mem B 0x420 = tbl2 P0 3 := by rw [m15]; exact p14_420
  have p15_480 : ptF n15.mem B 0x480 = tbl2 P0 4 := by rw [m15]; exact p14_480
  have p15_4e0 : ptF n15.mem B 0x4E0 = tbl2 P0 5 := by rw [m15]; exact p14_4e0
  have p15_540 : ptF n15.mem B 0x540 = tbl2 P0 6 := by rw [m15]; exact p14_540
  have p15_5a0 : ptF n15.mem B 0x5A0 = tbl2 P0 7 := by rw [m15]; exact p14_5a0
  have p15_900 : ptF n15.mem B 0x900 = P1 := by rw [m15]; exact p14_900
  have p15_980 : ptF n15.mem B 0x980 = tbl2 P1 0 := by rw [m15]; exact p14_980
  have p15_9e0 : ptF n15.mem B 0x9E0 = tbl2 P1 1 := by rw [m15]; exact p14_9e0
  have p15_a40 : ptF n15.mem B 0xA40 = tbl2 P1 2 := by rw [m15]; exact p14_a40
  have p15_aa0 : ptF n15.mem B 0xAA0 = tbl2 P1 3 := by rw [m15]; exact p14_aa0
  have p15_b00 : ptF n15.mem B 0xB00 = tbl2 P1 4 := by rw [m15]; exact p14_b00
  have p15_b60 : ptF n15.mem B 0xB60 = tbl2 P1 5 := by rw [m15]; exact p14_b60
  have p15_bc0 : ptF n15.mem B 0xBC0 = tbl2 P1 6 := by rw [m15]; exact p14_bc0
  have p15_c80 : ptF n15.mem B 0xC80 = tbl2 P1 6 := by rw [m15]; exact p14_c80
  have p15_f80 : ptF n15.mem B 0xF80 = ptDbl2 P1 := by rw [m15]; exact p14_f80
  have p15_fe4 : ptF n15.mem B 0xFE4 = P0 := by rw [m15]; exact p14_fe4
  have p15_1064 : ptF n15.mem B 0x1064 = P1 := by rw [m15]; exact p14_1064
  clear p14_bc0 p14_1064 p14_fe4 p14_f80 p14_c80 p14_b60 p14_b00 p14_aa0 p14_a40 p14_9e0 p14_980 p14_900 p14_5a0 p14_540 p14_4e0 p14_480 p14_420 p14_3c0 p14_360 p14_300 p14_280 p14_200 a14_10c4 a14_1044 a14_960 a14_2e0 a14_260 a14_1e0 a14_1c0 a14_1a0 a14_180 a14_160 a14_140 a14_120 q14_f20 q14_ec0 q14_e60 q14_e00 q14_da0 q14_d40 q14_ce0 q14_c20 g14_27 g14_26 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 s14 X14 K14 P14
  -- 0x812: p2v_pa2F
  obtain ⟨n16, c16, s16, sp16, rk16, P16, K16, fr16⟩ := p2v_pa2F (cl := 0xC80) (cr := 0xF80)
    F E15 (PT0.p2v F fR15) s15 p2v_at_812 p2v_at_816 (by decide) (by decide) g15_2
    g15_10 g15_11 (by decide) (by decide) (by decide) (by decide)
    p15_c80 p15_f80 (tbl2_lt hP1 6) (ptDbl2_lt _)
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.keepL K16 (by decide)
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk16 (3 : Fin 32) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk16 (4 : Fin 32) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xBC0 := by rw [rk16 (8 : Fin 32) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = BitVec.ofNat 32 0xC0 := by rw [rk16 (9 : Fin 32) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [rk16 (18 : Fin 32) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk16 (19 : Fin 32) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rk16 (20 : Fin 32) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [rk16 (21 : Fin 32) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rk16 (22 : Fin 32) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [rk16 (23 : Fin 32) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = rem := by rw [rk16 (24 : Fin 32) (by decide), g15_24]
  have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk16 (26 : Fin 32) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk16 (27 : Fin 32) (by decide), g15_27]
  have g16_2 : reg n16 sp = B + 0x21A0 := sp16
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60)] := keep_kk15.trans K16
  clear keep_kk15
  have q16_c20 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_c20 j hj)
  have q16_ce0 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_ce0 j hj)
  have q16_d40 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_d40 j hj)
  have q16_da0 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_da0 j hj)
  have q16_e00 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_e00 j hj)
  have q16_e60 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_e60 j hj)
  have q16_ec0 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_ec0 j hj)
  have q16_f20 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_f20 j hj)
  have a16_120 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K16.acc (by decide) (by decide)).trans a15_120
  have a16_140 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K16.acc (by decide) (by decide)).trans a15_140
  have a16_160 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K16.acc (by decide) (by decide)).trans a15_160
  have a16_180 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K16.acc (by decide) (by decide)).trans a15_180
  have a16_1a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K16.acc (by decide) (by decide)).trans a15_1a0
  have a16_1c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K16.acc (by decide) (by decide)).trans a15_1c0
  have a16_1e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K16.acc (by decide) (by decide)).trans a15_1e0
  have a16_260 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K16.acc (by decide) (by decide)).trans a15_260
  have a16_2e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K16.acc (by decide) (by decide)).trans a15_2e0
  have a16_960 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K16.acc (by decide) (by decide)).trans a15_960
  have a16_1044 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K16.acc (by decide) (by decide)).trans a15_1044
  have a16_10c4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K16.acc (by decide) (by decide)).trans a15_10c4
  have p16_200 : ptF n16.mem B 0x200 = P0 := (K16.pt (by decide) (by decide)).trans p15_200
  have p16_280 : ptF n16.mem B 0x280 = P1 := (K16.pt (by decide) (by decide)).trans p15_280
  have p16_300 : ptF n16.mem B 0x300 = tbl2 P0 0 := (K16.pt (by decide) (by decide)).trans p15_300
  have p16_360 : ptF n16.mem B 0x360 = tbl2 P0 1 := (K16.pt (by decide) (by decide)).trans p15_360
  have p16_3c0 : ptF n16.mem B 0x3C0 = tbl2 P0 2 := (K16.pt (by decide) (by decide)).trans p15_3c0
  have p16_420 : ptF n16.mem B 0x420 = tbl2 P0 3 := (K16.pt (by decide) (by decide)).trans p15_420
  have p16_480 : ptF n16.mem B 0x480 = tbl2 P0 4 := (K16.pt (by decide) (by decide)).trans p15_480
  have p16_4e0 : ptF n16.mem B 0x4E0 = tbl2 P0 5 := (K16.pt (by decide) (by decide)).trans p15_4e0
  have p16_540 : ptF n16.mem B 0x540 = tbl2 P0 6 := (K16.pt (by decide) (by decide)).trans p15_540
  have p16_5a0 : ptF n16.mem B 0x5A0 = tbl2 P0 7 := (K16.pt (by decide) (by decide)).trans p15_5a0
  have p16_900 : ptF n16.mem B 0x900 = P1 := (K16.pt (by decide) (by decide)).trans p15_900
  have p16_980 : ptF n16.mem B 0x980 = tbl2 P1 0 := (K16.pt (by decide) (by decide)).trans p15_980
  have p16_9e0 : ptF n16.mem B 0x9E0 = tbl2 P1 1 := (K16.pt (by decide) (by decide)).trans p15_9e0
  have p16_a40 : ptF n16.mem B 0xA40 = tbl2 P1 2 := (K16.pt (by decide) (by decide)).trans p15_a40
  have p16_aa0 : ptF n16.mem B 0xAA0 = tbl2 P1 3 := (K16.pt (by decide) (by decide)).trans p15_aa0
  have p16_b00 : ptF n16.mem B 0xB00 = tbl2 P1 4 := (K16.pt (by decide) (by decide)).trans p15_b00
  have p16_b60 : ptF n16.mem B 0xB60 = tbl2 P1 5 := (K16.pt (by decide) (by decide)).trans p15_b60
  have p16_bc0 : ptF n16.mem B 0xBC0 = tbl2 P1 6 := (K16.pt (by decide) (by decide)).trans p15_bc0
  have p16_f80 : ptF n16.mem B 0xF80 = ptDbl2 P1 := (K16.pt (by decide) (by decide)).trans p15_f80
  have p16_fe4 : ptF n16.mem B 0xFE4 = P0 := (K16.pt (by decide) (by decide)).trans p15_fe4
  have p16_1064 : ptF n16.mem B 0x1064 = P1 := (K16.pt (by decide) (by decide)).trans p15_1064
  clear p15_1064 p15_fe4 p15_f80 p15_c80 p15_bc0 p15_b60 p15_b00 p15_aa0 p15_a40 p15_9e0 p15_980 p15_900 p15_5a0 p15_540 p15_4e0 p15_480 p15_420 p15_3c0 p15_360 p15_300 p15_280 p15_200 a15_10c4 a15_1044 a15_960 a15_2e0 a15_260 a15_1e0 a15_1c0 a15_1a0 a15_180 a15_160 a15_140 a15_120 q15_f20 q15_ec0 q15_e60 q15_e00 q15_da0 q15_d40 q15_ce0 q15_c20 g15_11 g15_10 g15_27 g15_26 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  have p16_c80 : ptF n16.mem B 0xC80 = tbl2 P1 7 := P16
  -- 0x81A
  obtain ⟨n17, c17, u17⟩ := s16.block p2vEcT1b81a E16.self p2vEcT1b81a_end
    ⟨trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem P2V n17 0x822 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock p2vEcT1b81a (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_18 : reg n17 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = rem := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_8 : reg n17 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC20 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcT1b81a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_9 : reg n17 (9 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcT1b81a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have q17_c20 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_c20 j hj
  have q17_ce0 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_ce0 j hj
  have q17_d40 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_d40 j hj
  have q17_da0 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_da0 j hj
  have q17_e00 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_e00 j hj
  have q17_e60 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_e60 j hj
  have q17_ec0 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_ec0 j hj
  have q17_f20 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_f20 j hj
  have a17_120 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m17]; exact a16_120
  have a17_140 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m17]; exact a16_140
  have a17_160 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m17]; exact a16_160
  have a17_180 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m17]; exact a16_180
  have a17_1a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m17]; exact a16_1a0
  have a17_1c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m17]; exact a16_1c0
  have a17_1e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m17]; exact a16_1e0
  have a17_260 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m17]; exact a16_260
  have a17_2e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m17]; exact a16_2e0
  have a17_960 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m17]; exact a16_960
  have a17_1044 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m17]; exact a16_1044
  have a17_10c4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m17]; exact a16_10c4
  have p17_200 : ptF n17.mem B 0x200 = P0 := by rw [m17]; exact p16_200
  have p17_280 : ptF n17.mem B 0x280 = P1 := by rw [m17]; exact p16_280
  have p17_300 : ptF n17.mem B 0x300 = tbl2 P0 0 := by rw [m17]; exact p16_300
  have p17_360 : ptF n17.mem B 0x360 = tbl2 P0 1 := by rw [m17]; exact p16_360
  have p17_3c0 : ptF n17.mem B 0x3C0 = tbl2 P0 2 := by rw [m17]; exact p16_3c0
  have p17_420 : ptF n17.mem B 0x420 = tbl2 P0 3 := by rw [m17]; exact p16_420
  have p17_480 : ptF n17.mem B 0x480 = tbl2 P0 4 := by rw [m17]; exact p16_480
  have p17_4e0 : ptF n17.mem B 0x4E0 = tbl2 P0 5 := by rw [m17]; exact p16_4e0
  have p17_540 : ptF n17.mem B 0x540 = tbl2 P0 6 := by rw [m17]; exact p16_540
  have p17_5a0 : ptF n17.mem B 0x5A0 = tbl2 P0 7 := by rw [m17]; exact p16_5a0
  have p17_900 : ptF n17.mem B 0x900 = P1 := by rw [m17]; exact p16_900
  have p17_980 : ptF n17.mem B 0x980 = tbl2 P1 0 := by rw [m17]; exact p16_980
  have p17_9e0 : ptF n17.mem B 0x9E0 = tbl2 P1 1 := by rw [m17]; exact p16_9e0
  have p17_a40 : ptF n17.mem B 0xA40 = tbl2 P1 2 := by rw [m17]; exact p16_a40
  have p17_aa0 : ptF n17.mem B 0xAA0 = tbl2 P1 3 := by rw [m17]; exact p16_aa0
  have p17_b00 : ptF n17.mem B 0xB00 = tbl2 P1 4 := by rw [m17]; exact p16_b00
  have p17_b60 : ptF n17.mem B 0xB60 = tbl2 P1 5 := by rw [m17]; exact p16_b60
  have p17_bc0 : ptF n17.mem B 0xBC0 = tbl2 P1 6 := by rw [m17]; exact p16_bc0
  have p17_c80 : ptF n17.mem B 0xC80 = tbl2 P1 7 := by rw [m17]; exact p16_c80
  have p17_f80 : ptF n17.mem B 0xF80 = ptDbl2 P1 := by rw [m17]; exact p16_f80
  have p17_fe4 : ptF n17.mem B 0xFE4 = P0 := by rw [m17]; exact p16_fe4
  have p17_1064 : ptF n17.mem B 0x1064 = P1 := by rw [m17]; exact p16_1064
  clear p16_1064 p16_fe4 p16_f80 p16_bc0 p16_b60 p16_b00 p16_aa0 p16_a40 p16_9e0 p16_980 p16_900 p16_5a0 p16_540 p16_4e0 p16_480 p16_420 p16_3c0 p16_360 p16_300 p16_280 p16_200 a16_10c4 a16_1044 a16_960 a16_2e0 a16_260 a16_1e0 a16_1c0 a16_1a0 a16_180 a16_160 a16_140 a16_120 q16_f20 q16_ec0 q16_e60 q16_e00 q16_da0 q16_d40 q16_ce0 q16_c20 g16_2 g16_27 g16_26 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 V16 E16 fR16 t16 fr16 K16 P16 rk16 sp16 s16 c16
  -- 0x822: branch, taken
  obtain ⟨n18, d18, u18⟩ := s17.taken E17.self 0x7EC p2v_at_822
    (by decide) (by rw [g17_9, s17.zero]; decide)
  have s18 : St n18.mem P2V n18 0x7EC (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, P2vR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, P2vR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : P2vCode n18.mem := E17.fr F fr18
  have V18 : P2vSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC20 := by rw [u18.regs, g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [u18.regs, g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [u18.regs, g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u18.regs, g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u18.regs, g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u18.regs, g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u18.regs, g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u18.regs, g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = rem := by rw [u18.regs, g17_24]
  have g18_26 : reg n18 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u18.regs, g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u18.regs, g17_27]
  have keep_kk18 : P2vKeepL B n0.mem n18.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have q18_c20 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_c20 j hj
  have q18_ce0 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_ce0 j hj
  have q18_d40 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_d40 j hj
  have q18_da0 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_da0 j hj
  have q18_e00 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_e00 j hj
  have q18_e60 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_e60 j hj
  have q18_ec0 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_ec0 j hj
  have q18_f20 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m18]; exact q17_f20 j hj
  have a18_120 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m18]; exact a17_120
  have a18_140 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m18]; exact a17_140
  have a18_160 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m18]; exact a17_160
  have a18_180 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m18]; exact a17_180
  have a18_1a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m18]; exact a17_1a0
  have a18_1c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m18]; exact a17_1c0
  have a18_1e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m18]; exact a17_1e0
  have a18_260 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m18]; exact a17_260
  have a18_2e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m18]; exact a17_2e0
  have a18_960 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m18]; exact a17_960
  have a18_1044 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m18]; exact a17_1044
  have a18_10c4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m18]; exact a17_10c4
  have p18_200 : ptF n18.mem B 0x200 = P0 := by rw [m18]; exact p17_200
  have p18_280 : ptF n18.mem B 0x280 = P1 := by rw [m18]; exact p17_280
  have p18_300 : ptF n18.mem B 0x300 = tbl2 P0 0 := by rw [m18]; exact p17_300
  have p18_360 : ptF n18.mem B 0x360 = tbl2 P0 1 := by rw [m18]; exact p17_360
  have p18_3c0 : ptF n18.mem B 0x3C0 = tbl2 P0 2 := by rw [m18]; exact p17_3c0
  have p18_420 : ptF n18.mem B 0x420 = tbl2 P0 3 := by rw [m18]; exact p17_420
  have p18_480 : ptF n18.mem B 0x480 = tbl2 P0 4 := by rw [m18]; exact p17_480
  have p18_4e0 : ptF n18.mem B 0x4E0 = tbl2 P0 5 := by rw [m18]; exact p17_4e0
  have p18_540 : ptF n18.mem B 0x540 = tbl2 P0 6 := by rw [m18]; exact p17_540
  have p18_5a0 : ptF n18.mem B 0x5A0 = tbl2 P0 7 := by rw [m18]; exact p17_5a0
  have p18_900 : ptF n18.mem B 0x900 = P1 := by rw [m18]; exact p17_900
  have p18_980 : ptF n18.mem B 0x980 = tbl2 P1 0 := by rw [m18]; exact p17_980
  have p18_9e0 : ptF n18.mem B 0x9E0 = tbl2 P1 1 := by rw [m18]; exact p17_9e0
  have p18_a40 : ptF n18.mem B 0xA40 = tbl2 P1 2 := by rw [m18]; exact p17_a40
  have p18_aa0 : ptF n18.mem B 0xAA0 = tbl2 P1 3 := by rw [m18]; exact p17_aa0
  have p18_b00 : ptF n18.mem B 0xB00 = tbl2 P1 4 := by rw [m18]; exact p17_b00
  have p18_b60 : ptF n18.mem B 0xB60 = tbl2 P1 5 := by rw [m18]; exact p17_b60
  have p18_bc0 : ptF n18.mem B 0xBC0 = tbl2 P1 6 := by rw [m18]; exact p17_bc0
  have p18_c80 : ptF n18.mem B 0xC80 = tbl2 P1 7 := by rw [m18]; exact p17_c80
  have p18_f80 : ptF n18.mem B 0xF80 = ptDbl2 P1 := by rw [m18]; exact p17_f80
  have p18_fe4 : ptF n18.mem B 0xFE4 = P0 := by rw [m18]; exact p17_fe4
  have p18_1064 : ptF n18.mem B 0x1064 = P1 := by rw [m18]; exact p17_1064
  clear p17_1064 p17_fe4 p17_f80 p17_c80 p17_bc0 p17_b60 p17_b00 p17_aa0 p17_a40 p17_9e0 p17_980 p17_900 p17_5a0 p17_540 p17_4e0 p17_480 p17_420 p17_3c0 p17_360 p17_300 p17_280 p17_200 a17_10c4 a17_1044 a17_960 a17_2e0 a17_260 a17_1e0 a17_1c0 a17_1a0 a17_180 a17_160 a17_140 a17_120 q17_f20 q17_ec0 q17_e60 q17_e00 q17_da0 q17_d40 q17_ce0 q17_c20 g17_9 g17_8 g17_27 g17_26 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17 p16_c80
  -- 0x7EC
  obtain ⟨n19, c19, u19⟩ := s18.block p2vEcT1b7ec E18.self p2vEcT1b7ec_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem P2V n19 0x7FA (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock p2vEcT1b7ec (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_8 : reg n19 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC20 := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = rem := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_26 : reg n19 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC20 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_12 : reg n19 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vEcT1b7ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk19 : P2vKeepL B n0.mem n19.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have q19_c20 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_c20 j hj
  have q19_ce0 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_ce0 j hj
  have q19_d40 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_d40 j hj
  have q19_da0 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_da0 j hj
  have q19_e00 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_e00 j hj
  have q19_e60 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_e60 j hj
  have q19_ec0 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_ec0 j hj
  have q19_f20 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_f20 j hj
  have a19_120 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m19]; exact a18_120
  have a19_140 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m19]; exact a18_140
  have a19_160 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m19]; exact a18_160
  have a19_180 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m19]; exact a18_180
  have a19_1a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m19]; exact a18_1a0
  have a19_1c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m19]; exact a18_1c0
  have a19_1e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m19]; exact a18_1e0
  have a19_260 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m19]; exact a18_260
  have a19_2e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m19]; exact a18_2e0
  have a19_960 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m19]; exact a18_960
  have a19_1044 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m19]; exact a18_1044
  have a19_10c4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m19]; exact a18_10c4
  have p19_200 : ptF n19.mem B 0x200 = P0 := by rw [m19]; exact p18_200
  have p19_280 : ptF n19.mem B 0x280 = P1 := by rw [m19]; exact p18_280
  have p19_300 : ptF n19.mem B 0x300 = tbl2 P0 0 := by rw [m19]; exact p18_300
  have p19_360 : ptF n19.mem B 0x360 = tbl2 P0 1 := by rw [m19]; exact p18_360
  have p19_3c0 : ptF n19.mem B 0x3C0 = tbl2 P0 2 := by rw [m19]; exact p18_3c0
  have p19_420 : ptF n19.mem B 0x420 = tbl2 P0 3 := by rw [m19]; exact p18_420
  have p19_480 : ptF n19.mem B 0x480 = tbl2 P0 4 := by rw [m19]; exact p18_480
  have p19_4e0 : ptF n19.mem B 0x4E0 = tbl2 P0 5 := by rw [m19]; exact p18_4e0
  have p19_540 : ptF n19.mem B 0x540 = tbl2 P0 6 := by rw [m19]; exact p18_540
  have p19_5a0 : ptF n19.mem B 0x5A0 = tbl2 P0 7 := by rw [m19]; exact p18_5a0
  have p19_900 : ptF n19.mem B 0x900 = P1 := by rw [m19]; exact p18_900
  have p19_980 : ptF n19.mem B 0x980 = tbl2 P1 0 := by rw [m19]; exact p18_980
  have p19_9e0 : ptF n19.mem B 0x9E0 = tbl2 P1 1 := by rw [m19]; exact p18_9e0
  have p19_a40 : ptF n19.mem B 0xA40 = tbl2 P1 2 := by rw [m19]; exact p18_a40
  have p19_aa0 : ptF n19.mem B 0xAA0 = tbl2 P1 3 := by rw [m19]; exact p18_aa0
  have p19_b00 : ptF n19.mem B 0xB00 = tbl2 P1 4 := by rw [m19]; exact p18_b00
  have p19_b60 : ptF n19.mem B 0xB60 = tbl2 P1 5 := by rw [m19]; exact p18_b60
  have p19_bc0 : ptF n19.mem B 0xBC0 = tbl2 P1 6 := by rw [m19]; exact p18_bc0
  have p19_c80 : ptF n19.mem B 0xC80 = tbl2 P1 7 := by rw [m19]; exact p18_c80
  have p19_f80 : ptF n19.mem B 0xF80 = ptDbl2 P1 := by rw [m19]; exact p18_f80
  have p19_fe4 : ptF n19.mem B 0xFE4 = P0 := by rw [m19]; exact p18_fe4
  have p19_1064 : ptF n19.mem B 0x1064 = P1 := by rw [m19]; exact p18_1064
  clear p18_1064 p18_fe4 p18_f80 p18_c80 p18_bc0 p18_b60 p18_b00 p18_aa0 p18_a40 p18_9e0 p18_980 p18_900 p18_5a0 p18_540 p18_4e0 p18_480 p18_420 p18_3c0 p18_360 p18_300 p18_280 p18_200 a18_10c4 a18_1044 a18_960 a18_2e0 a18_260 a18_1e0 a18_1c0 a18_1a0 a18_180 a18_160 a18_140 a18_120 q18_f20 q18_ec0 q18_e60 q18_e00 q18_da0 q18_d40 q18_ce0 q18_c20 g18_27 g18_26 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x7FA: memcpy
  obtain ⟨n20, P20, K20, X20⟩ := p2v_mc (c := 0xC20) (d := 0xC80) (N := 0x60) F E19 s19 p2v_at_7fa p2v_at_7fe
    (by decide) (by decide) g19_2 g19_10 g19_11 g19_12
    (by decide) (by decide) (by decide)
  have s20 := P20.st
  have fr20 := P20.fr
  have t20 : Steps n0 n20 := t19.trans P20.steps
  have fR20 : ∀ x, P2vR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : P2vCode n20.mem := E19.fr F fr20
  have V20 : P2vSaves B n20.mem v := V19.keep K20 (by decide)
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [P20.regs sp (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P20.regs (3 : Fin 32) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P20.regs (4 : Fin 32) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC20 := by rw [P20.regs (8 : Fin 32) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [P20.regs (9 : Fin 32) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [P20.regs (18 : Fin 32) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P20.regs (19 : Fin 32) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P20.regs (20 : Fin 32) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P20.regs (21 : Fin 32) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P20.regs (22 : Fin 32) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P20.regs (23 : Fin 32) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = rem := by rw [P20.regs (24 : Fin 32) (by decide), g19_24]
  have g20_26 : reg n20 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P20.regs (26 : Fin 32) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P20.regs (27 : Fin 32) (by decide), g19_27]
  have keep_kk20 : P2vKeepL B n0.mem n20.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60)] := keep_kk19.trans K20.toL
  clear keep_kk19
  have q20_ce0 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_ce0 j hj)
  have q20_d40 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_d40 j hj)
  have q20_da0 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_da0 j hj)
  have q20_e00 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_e00 j hj)
  have q20_e60 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_e60 j hj)
  have q20_ec0 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_ec0 j hj)
  have q20_f20 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_f20 j hj)
  have a20_120 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K20.acc (by decide) (by decide)).trans a19_120
  have a20_140 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K20.acc (by decide) (by decide)).trans a19_140
  have a20_160 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K20.acc (by decide) (by decide)).trans a19_160
  have a20_180 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K20.acc (by decide) (by decide)).trans a19_180
  have a20_1a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K20.acc (by decide) (by decide)).trans a19_1a0
  have a20_1c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K20.acc (by decide) (by decide)).trans a19_1c0
  have a20_1e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K20.acc (by decide) (by decide)).trans a19_1e0
  have a20_260 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K20.acc (by decide) (by decide)).trans a19_260
  have a20_2e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K20.acc (by decide) (by decide)).trans a19_2e0
  have a20_960 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K20.acc (by decide) (by decide)).trans a19_960
  have a20_1044 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K20.acc (by decide) (by decide)).trans a19_1044
  have a20_10c4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K20.acc (by decide) (by decide)).trans a19_10c4
  have p20_200 : ptF n20.mem B 0x200 = P0 := (K20.pt (by decide) (by decide)).trans p19_200
  have p20_280 : ptF n20.mem B 0x280 = P1 := (K20.pt (by decide) (by decide)).trans p19_280
  have p20_300 : ptF n20.mem B 0x300 = tbl2 P0 0 := (K20.pt (by decide) (by decide)).trans p19_300
  have p20_360 : ptF n20.mem B 0x360 = tbl2 P0 1 := (K20.pt (by decide) (by decide)).trans p19_360
  have p20_3c0 : ptF n20.mem B 0x3C0 = tbl2 P0 2 := (K20.pt (by decide) (by decide)).trans p19_3c0
  have p20_420 : ptF n20.mem B 0x420 = tbl2 P0 3 := (K20.pt (by decide) (by decide)).trans p19_420
  have p20_480 : ptF n20.mem B 0x480 = tbl2 P0 4 := (K20.pt (by decide) (by decide)).trans p19_480
  have p20_4e0 : ptF n20.mem B 0x4E0 = tbl2 P0 5 := (K20.pt (by decide) (by decide)).trans p19_4e0
  have p20_540 : ptF n20.mem B 0x540 = tbl2 P0 6 := (K20.pt (by decide) (by decide)).trans p19_540
  have p20_5a0 : ptF n20.mem B 0x5A0 = tbl2 P0 7 := (K20.pt (by decide) (by decide)).trans p19_5a0
  have p20_900 : ptF n20.mem B 0x900 = P1 := (K20.pt (by decide) (by decide)).trans p19_900
  have p20_980 : ptF n20.mem B 0x980 = tbl2 P1 0 := (K20.pt (by decide) (by decide)).trans p19_980
  have p20_9e0 : ptF n20.mem B 0x9E0 = tbl2 P1 1 := (K20.pt (by decide) (by decide)).trans p19_9e0
  have p20_a40 : ptF n20.mem B 0xA40 = tbl2 P1 2 := (K20.pt (by decide) (by decide)).trans p19_a40
  have p20_aa0 : ptF n20.mem B 0xAA0 = tbl2 P1 3 := (K20.pt (by decide) (by decide)).trans p19_aa0
  have p20_b00 : ptF n20.mem B 0xB00 = tbl2 P1 4 := (K20.pt (by decide) (by decide)).trans p19_b00
  have p20_b60 : ptF n20.mem B 0xB60 = tbl2 P1 5 := (K20.pt (by decide) (by decide)).trans p19_b60
  have p20_bc0 : ptF n20.mem B 0xBC0 = tbl2 P1 6 := (K20.pt (by decide) (by decide)).trans p19_bc0
  have p20_c80 : ptF n20.mem B 0xC80 = tbl2 P1 7 := (K20.pt (by decide) (by decide)).trans p19_c80
  have p20_f80 : ptF n20.mem B 0xF80 = ptDbl2 P1 := (K20.pt (by decide) (by decide)).trans p19_f80
  have p20_fe4 : ptF n20.mem B 0xFE4 = P0 := (K20.pt (by decide) (by decide)).trans p19_fe4
  have p20_1064 : ptF n20.mem B 0x1064 = P1 := (K20.pt (by decide) (by decide)).trans p19_1064
  have p20_c20 : ptF n20.mem B 0xC20 = tbl2 P1 7 := (ptF_cp X20 (by decide) (by decide) (by decide)).trans p19_c80
  clear p19_1064 p19_fe4 p19_f80 p19_c80 p19_bc0 p19_b60 p19_b00 p19_aa0 p19_a40 p19_9e0 p19_980 p19_900 p19_5a0 p19_540 p19_4e0 p19_480 p19_420 p19_3c0 p19_360 p19_300 p19_280 p19_200 a19_10c4 a19_1044 a19_960 a19_2e0 a19_260 a19_1e0 a19_1c0 a19_1a0 a19_180 a19_160 a19_140 a19_120 q19_f20 q19_ec0 q19_e60 q19_e00 q19_da0 q19_d40 q19_ce0 q19_c20 g19_12 g19_11 g19_10 g19_27 g19_26 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x802
  obtain ⟨n21, c21, u21⟩ := s20.block p2vEcT1b802 E20.self p2vEcT1b802_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem P2V n21 0x812 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock p2vEcT1b802 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_8 : reg n21 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC20 := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = rem := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_26 : reg n21 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vEcT1b802, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g21_11 : reg n21 a1 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vEcT1b802, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk21 : P2vKeepL B n0.mem n21.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have q21_ce0 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_ce0 j hj
  have q21_d40 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_d40 j hj
  have q21_da0 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_da0 j hj
  have q21_e00 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_e00 j hj
  have q21_e60 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_e60 j hj
  have q21_ec0 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_ec0 j hj
  have q21_f20 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_f20 j hj
  have a21_120 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m21]; exact a20_120
  have a21_140 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m21]; exact a20_140
  have a21_160 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m21]; exact a20_160
  have a21_180 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m21]; exact a20_180
  have a21_1a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m21]; exact a20_1a0
  have a21_1c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m21]; exact a20_1c0
  have a21_1e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m21]; exact a20_1e0
  have a21_260 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m21]; exact a20_260
  have a21_2e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m21]; exact a20_2e0
  have a21_960 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m21]; exact a20_960
  have a21_1044 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m21]; exact a20_1044
  have a21_10c4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m21]; exact a20_10c4
  have p21_200 : ptF n21.mem B 0x200 = P0 := by rw [m21]; exact p20_200
  have p21_280 : ptF n21.mem B 0x280 = P1 := by rw [m21]; exact p20_280
  have p21_300 : ptF n21.mem B 0x300 = tbl2 P0 0 := by rw [m21]; exact p20_300
  have p21_360 : ptF n21.mem B 0x360 = tbl2 P0 1 := by rw [m21]; exact p20_360
  have p21_3c0 : ptF n21.mem B 0x3C0 = tbl2 P0 2 := by rw [m21]; exact p20_3c0
  have p21_420 : ptF n21.mem B 0x420 = tbl2 P0 3 := by rw [m21]; exact p20_420
  have p21_480 : ptF n21.mem B 0x480 = tbl2 P0 4 := by rw [m21]; exact p20_480
  have p21_4e0 : ptF n21.mem B 0x4E0 = tbl2 P0 5 := by rw [m21]; exact p20_4e0
  have p21_540 : ptF n21.mem B 0x540 = tbl2 P0 6 := by rw [m21]; exact p20_540
  have p21_5a0 : ptF n21.mem B 0x5A0 = tbl2 P0 7 := by rw [m21]; exact p20_5a0
  have p21_900 : ptF n21.mem B 0x900 = P1 := by rw [m21]; exact p20_900
  have p21_980 : ptF n21.mem B 0x980 = tbl2 P1 0 := by rw [m21]; exact p20_980
  have p21_9e0 : ptF n21.mem B 0x9E0 = tbl2 P1 1 := by rw [m21]; exact p20_9e0
  have p21_a40 : ptF n21.mem B 0xA40 = tbl2 P1 2 := by rw [m21]; exact p20_a40
  have p21_aa0 : ptF n21.mem B 0xAA0 = tbl2 P1 3 := by rw [m21]; exact p20_aa0
  have p21_b00 : ptF n21.mem B 0xB00 = tbl2 P1 4 := by rw [m21]; exact p20_b00
  have p21_b60 : ptF n21.mem B 0xB60 = tbl2 P1 5 := by rw [m21]; exact p20_b60
  have p21_bc0 : ptF n21.mem B 0xBC0 = tbl2 P1 6 := by rw [m21]; exact p20_bc0
  have p21_c20 : ptF n21.mem B 0xC20 = tbl2 P1 7 := by rw [m21]; exact p20_c20
  have p21_c80 : ptF n21.mem B 0xC80 = tbl2 P1 7 := by rw [m21]; exact p20_c80
  have p21_f80 : ptF n21.mem B 0xF80 = ptDbl2 P1 := by rw [m21]; exact p20_f80
  have p21_fe4 : ptF n21.mem B 0xFE4 = P0 := by rw [m21]; exact p20_fe4
  have p21_1064 : ptF n21.mem B 0x1064 = P1 := by rw [m21]; exact p20_1064
  clear p20_c20 p20_1064 p20_fe4 p20_f80 p20_c80 p20_bc0 p20_b60 p20_b00 p20_aa0 p20_a40 p20_9e0 p20_980 p20_900 p20_5a0 p20_540 p20_4e0 p20_480 p20_420 p20_3c0 p20_360 p20_300 p20_280 p20_200 a20_10c4 a20_1044 a20_960 a20_2e0 a20_260 a20_1e0 a20_1c0 a20_1a0 a20_180 a20_160 a20_140 a20_120 q20_f20 q20_ec0 q20_e60 q20_e00 q20_da0 q20_d40 q20_ce0 g20_27 g20_26 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 s20 X20 K20 P20
  -- 0x812: p2v_pa2F
  obtain ⟨n22, c22, s22, sp22, rk22, P22, K22, fr22⟩ := p2v_pa2F (cl := 0xC80) (cr := 0xF80)
    F E21 (PT0.p2v F fR21) s21 p2v_at_812 p2v_at_816 (by decide) (by decide) g21_2
    g21_10 g21_11 (by decide) (by decide) (by decide) (by decide)
    p21_c80 p21_f80 (tbl2_lt hP1 7) (ptDbl2_lt _)
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, P2vR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : P2vCode n22.mem := E21.fr F fr22
  have V22 : P2vSaves B n22.mem v := V21.keepL K22 (by decide)
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk22 (3 : Fin 32) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk22 (4 : Fin 32) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC20 := by rw [rk22 (8 : Fin 32) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rk22 (9 : Fin 32) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [rk22 (18 : Fin 32) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk22 (19 : Fin 32) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rk22 (20 : Fin 32) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [rk22 (21 : Fin 32) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rk22 (22 : Fin 32) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [rk22 (23 : Fin 32) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = rem := by rw [rk22 (24 : Fin 32) (by decide), g21_24]
  have g22_26 : reg n22 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk22 (26 : Fin 32) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [rk22 (27 : Fin 32) (by decide), g21_27]
  have g22_2 : reg n22 sp = B + 0x21A0 := sp22
  have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60)] := keep_kk21.trans K22
  clear keep_kk21
  have q22_ce0 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_ce0 j hj)
  have q22_d40 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_d40 j hj)
  have q22_da0 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_da0 j hj)
  have q22_e00 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_e00 j hj)
  have q22_e60 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_e60 j hj)
  have q22_ec0 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_ec0 j hj)
  have q22_f20 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_f20 j hj)
  have a22_120 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K22.acc (by decide) (by decide)).trans a21_120
  have a22_140 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K22.acc (by decide) (by decide)).trans a21_140
  have a22_160 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K22.acc (by decide) (by decide)).trans a21_160
  have a22_180 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K22.acc (by decide) (by decide)).trans a21_180
  have a22_1a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K22.acc (by decide) (by decide)).trans a21_1a0
  have a22_1c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K22.acc (by decide) (by decide)).trans a21_1c0
  have a22_1e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K22.acc (by decide) (by decide)).trans a21_1e0
  have a22_260 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K22.acc (by decide) (by decide)).trans a21_260
  have a22_2e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K22.acc (by decide) (by decide)).trans a21_2e0
  have a22_960 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K22.acc (by decide) (by decide)).trans a21_960
  have a22_1044 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K22.acc (by decide) (by decide)).trans a21_1044
  have a22_10c4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K22.acc (by decide) (by decide)).trans a21_10c4
  have p22_200 : ptF n22.mem B 0x200 = P0 := (K22.pt (by decide) (by decide)).trans p21_200
  have p22_280 : ptF n22.mem B 0x280 = P1 := (K22.pt (by decide) (by decide)).trans p21_280
  have p22_300 : ptF n22.mem B 0x300 = tbl2 P0 0 := (K22.pt (by decide) (by decide)).trans p21_300
  have p22_360 : ptF n22.mem B 0x360 = tbl2 P0 1 := (K22.pt (by decide) (by decide)).trans p21_360
  have p22_3c0 : ptF n22.mem B 0x3C0 = tbl2 P0 2 := (K22.pt (by decide) (by decide)).trans p21_3c0
  have p22_420 : ptF n22.mem B 0x420 = tbl2 P0 3 := (K22.pt (by decide) (by decide)).trans p21_420
  have p22_480 : ptF n22.mem B 0x480 = tbl2 P0 4 := (K22.pt (by decide) (by decide)).trans p21_480
  have p22_4e0 : ptF n22.mem B 0x4E0 = tbl2 P0 5 := (K22.pt (by decide) (by decide)).trans p21_4e0
  have p22_540 : ptF n22.mem B 0x540 = tbl2 P0 6 := (K22.pt (by decide) (by decide)).trans p21_540
  have p22_5a0 : ptF n22.mem B 0x5A0 = tbl2 P0 7 := (K22.pt (by decide) (by decide)).trans p21_5a0
  have p22_900 : ptF n22.mem B 0x900 = P1 := (K22.pt (by decide) (by decide)).trans p21_900
  have p22_980 : ptF n22.mem B 0x980 = tbl2 P1 0 := (K22.pt (by decide) (by decide)).trans p21_980
  have p22_9e0 : ptF n22.mem B 0x9E0 = tbl2 P1 1 := (K22.pt (by decide) (by decide)).trans p21_9e0
  have p22_a40 : ptF n22.mem B 0xA40 = tbl2 P1 2 := (K22.pt (by decide) (by decide)).trans p21_a40
  have p22_aa0 : ptF n22.mem B 0xAA0 = tbl2 P1 3 := (K22.pt (by decide) (by decide)).trans p21_aa0
  have p22_b00 : ptF n22.mem B 0xB00 = tbl2 P1 4 := (K22.pt (by decide) (by decide)).trans p21_b00
  have p22_b60 : ptF n22.mem B 0xB60 = tbl2 P1 5 := (K22.pt (by decide) (by decide)).trans p21_b60
  have p22_bc0 : ptF n22.mem B 0xBC0 = tbl2 P1 6 := (K22.pt (by decide) (by decide)).trans p21_bc0
  have p22_c20 : ptF n22.mem B 0xC20 = tbl2 P1 7 := (K22.pt (by decide) (by decide)).trans p21_c20
  have p22_f80 : ptF n22.mem B 0xF80 = ptDbl2 P1 := (K22.pt (by decide) (by decide)).trans p21_f80
  have p22_fe4 : ptF n22.mem B 0xFE4 = P0 := (K22.pt (by decide) (by decide)).trans p21_fe4
  have p22_1064 : ptF n22.mem B 0x1064 = P1 := (K22.pt (by decide) (by decide)).trans p21_1064
  clear p21_1064 p21_fe4 p21_f80 p21_c80 p21_c20 p21_bc0 p21_b60 p21_b00 p21_aa0 p21_a40 p21_9e0 p21_980 p21_900 p21_5a0 p21_540 p21_4e0 p21_480 p21_420 p21_3c0 p21_360 p21_300 p21_280 p21_200 a21_10c4 a21_1044 a21_960 a21_2e0 a21_260 a21_1e0 a21_1c0 a21_1a0 a21_180 a21_160 a21_140 a21_120 q21_f20 q21_ec0 q21_e60 q21_e00 q21_da0 q21_d40 q21_ce0 g21_11 g21_10 g21_27 g21_26 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  have p22_c80 : ptF n22.mem B 0xC80 = tbl2 P1 8 := P22
  -- 0x81A
  obtain ⟨n23, c23, u23⟩ := s22.block p2vEcT1b81a E22.self p2vEcT1b81a_end
    ⟨trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem P2V n23 0x822 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock p2vEcT1b81a (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_18 : reg n23 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb23, runBlock_reg _ _ _ (22 : Fin 32) s22.zero (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = rem := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_26 : reg n23 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_8 : reg n23 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vEcT1b81a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g23_9 : reg n23 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, p2vEcT1b81a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have q23_ce0 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_ce0 j hj
  have q23_d40 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_d40 j hj
  have q23_da0 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_da0 j hj
  have q23_e00 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_e00 j hj
  have q23_e60 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_e60 j hj
  have q23_ec0 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_ec0 j hj
  have q23_f20 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_f20 j hj
  have a23_120 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m23]; exact a22_120
  have a23_140 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m23]; exact a22_140
  have a23_160 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m23]; exact a22_160
  have a23_180 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m23]; exact a22_180
  have a23_1a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m23]; exact a22_1a0
  have a23_1c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m23]; exact a22_1c0
  have a23_1e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m23]; exact a22_1e0
  have a23_260 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m23]; exact a22_260
  have a23_2e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m23]; exact a22_2e0
  have a23_960 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m23]; exact a22_960
  have a23_1044 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m23]; exact a22_1044
  have a23_10c4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m23]; exact a22_10c4
  have p23_200 : ptF n23.mem B 0x200 = P0 := by rw [m23]; exact p22_200
  have p23_280 : ptF n23.mem B 0x280 = P1 := by rw [m23]; exact p22_280
  have p23_300 : ptF n23.mem B 0x300 = tbl2 P0 0 := by rw [m23]; exact p22_300
  have p23_360 : ptF n23.mem B 0x360 = tbl2 P0 1 := by rw [m23]; exact p22_360
  have p23_3c0 : ptF n23.mem B 0x3C0 = tbl2 P0 2 := by rw [m23]; exact p22_3c0
  have p23_420 : ptF n23.mem B 0x420 = tbl2 P0 3 := by rw [m23]; exact p22_420
  have p23_480 : ptF n23.mem B 0x480 = tbl2 P0 4 := by rw [m23]; exact p22_480
  have p23_4e0 : ptF n23.mem B 0x4E0 = tbl2 P0 5 := by rw [m23]; exact p22_4e0
  have p23_540 : ptF n23.mem B 0x540 = tbl2 P0 6 := by rw [m23]; exact p22_540
  have p23_5a0 : ptF n23.mem B 0x5A0 = tbl2 P0 7 := by rw [m23]; exact p22_5a0
  have p23_900 : ptF n23.mem B 0x900 = P1 := by rw [m23]; exact p22_900
  have p23_980 : ptF n23.mem B 0x980 = tbl2 P1 0 := by rw [m23]; exact p22_980
  have p23_9e0 : ptF n23.mem B 0x9E0 = tbl2 P1 1 := by rw [m23]; exact p22_9e0
  have p23_a40 : ptF n23.mem B 0xA40 = tbl2 P1 2 := by rw [m23]; exact p22_a40
  have p23_aa0 : ptF n23.mem B 0xAA0 = tbl2 P1 3 := by rw [m23]; exact p22_aa0
  have p23_b00 : ptF n23.mem B 0xB00 = tbl2 P1 4 := by rw [m23]; exact p22_b00
  have p23_b60 : ptF n23.mem B 0xB60 = tbl2 P1 5 := by rw [m23]; exact p22_b60
  have p23_bc0 : ptF n23.mem B 0xBC0 = tbl2 P1 6 := by rw [m23]; exact p22_bc0
  have p23_c20 : ptF n23.mem B 0xC20 = tbl2 P1 7 := by rw [m23]; exact p22_c20
  have p23_c80 : ptF n23.mem B 0xC80 = tbl2 P1 8 := by rw [m23]; exact p22_c80
  have p23_f80 : ptF n23.mem B 0xF80 = ptDbl2 P1 := by rw [m23]; exact p22_f80
  have p23_fe4 : ptF n23.mem B 0xFE4 = P0 := by rw [m23]; exact p22_fe4
  have p23_1064 : ptF n23.mem B 0x1064 = P1 := by rw [m23]; exact p22_1064
  clear p22_1064 p22_fe4 p22_f80 p22_c20 p22_bc0 p22_b60 p22_b00 p22_aa0 p22_a40 p22_9e0 p22_980 p22_900 p22_5a0 p22_540 p22_4e0 p22_480 p22_420 p22_3c0 p22_360 p22_300 p22_280 p22_200 a22_10c4 a22_1044 a22_960 a22_2e0 a22_260 a22_1e0 a22_1c0 a22_1a0 a22_180 a22_160 a22_140 a22_120 q22_f20 q22_ec0 q22_e60 q22_e00 q22_da0 q22_d40 q22_ce0 g22_2 g22_27 g22_26 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 V22 E22 fR22 t22 fr22 K22 P22 rk22 sp22 s22 c22
  -- 0x822: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0x824 p2v_at_822
    (by decide) (by rw [g23_9, s23.zero]; decide)
  have s24 : St n24.mem P2V n24 0x824 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, P2vR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, P2vR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : P2vCode n24.mem := E23.fr F fr24
  have V24 : P2vSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u24.regs, g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u24.regs, g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u24.regs, g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = rem := by rw [u24.regs, g23_24]
  have g24_26 : reg n24 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u24.regs, g23_27]
  have keep_kk24 : P2vKeepL B n0.mem n24.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have q24_ce0 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_ce0 j hj
  have q24_d40 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_d40 j hj
  have q24_da0 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_da0 j hj
  have q24_e00 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_e00 j hj
  have q24_e60 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_e60 j hj
  have q24_ec0 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_ec0 j hj
  have q24_f20 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_f20 j hj
  have a24_120 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m24]; exact a23_120
  have a24_140 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m24]; exact a23_140
  have a24_160 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m24]; exact a23_160
  have a24_180 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m24]; exact a23_180
  have a24_1a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m24]; exact a23_1a0
  have a24_1c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m24]; exact a23_1c0
  have a24_1e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m24]; exact a23_1e0
  have a24_260 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m24]; exact a23_260
  have a24_2e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m24]; exact a23_2e0
  have a24_960 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m24]; exact a23_960
  have a24_1044 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m24]; exact a23_1044
  have a24_10c4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m24]; exact a23_10c4
  have p24_200 : ptF n24.mem B 0x200 = P0 := by rw [m24]; exact p23_200
  have p24_280 : ptF n24.mem B 0x280 = P1 := by rw [m24]; exact p23_280
  have p24_300 : ptF n24.mem B 0x300 = tbl2 P0 0 := by rw [m24]; exact p23_300
  have p24_360 : ptF n24.mem B 0x360 = tbl2 P0 1 := by rw [m24]; exact p23_360
  have p24_3c0 : ptF n24.mem B 0x3C0 = tbl2 P0 2 := by rw [m24]; exact p23_3c0
  have p24_420 : ptF n24.mem B 0x420 = tbl2 P0 3 := by rw [m24]; exact p23_420
  have p24_480 : ptF n24.mem B 0x480 = tbl2 P0 4 := by rw [m24]; exact p23_480
  have p24_4e0 : ptF n24.mem B 0x4E0 = tbl2 P0 5 := by rw [m24]; exact p23_4e0
  have p24_540 : ptF n24.mem B 0x540 = tbl2 P0 6 := by rw [m24]; exact p23_540
  have p24_5a0 : ptF n24.mem B 0x5A0 = tbl2 P0 7 := by rw [m24]; exact p23_5a0
  have p24_900 : ptF n24.mem B 0x900 = P1 := by rw [m24]; exact p23_900
  have p24_980 : ptF n24.mem B 0x980 = tbl2 P1 0 := by rw [m24]; exact p23_980
  have p24_9e0 : ptF n24.mem B 0x9E0 = tbl2 P1 1 := by rw [m24]; exact p23_9e0
  have p24_a40 : ptF n24.mem B 0xA40 = tbl2 P1 2 := by rw [m24]; exact p23_a40
  have p24_aa0 : ptF n24.mem B 0xAA0 = tbl2 P1 3 := by rw [m24]; exact p23_aa0
  have p24_b00 : ptF n24.mem B 0xB00 = tbl2 P1 4 := by rw [m24]; exact p23_b00
  have p24_b60 : ptF n24.mem B 0xB60 = tbl2 P1 5 := by rw [m24]; exact p23_b60
  have p24_bc0 : ptF n24.mem B 0xBC0 = tbl2 P1 6 := by rw [m24]; exact p23_bc0
  have p24_c20 : ptF n24.mem B 0xC20 = tbl2 P1 7 := by rw [m24]; exact p23_c20
  have p24_c80 : ptF n24.mem B 0xC80 = tbl2 P1 8 := by rw [m24]; exact p23_c80
  have p24_f80 : ptF n24.mem B 0xF80 = ptDbl2 P1 := by rw [m24]; exact p23_f80
  have p24_fe4 : ptF n24.mem B 0xFE4 = P0 := by rw [m24]; exact p23_fe4
  have p24_1064 : ptF n24.mem B 0x1064 = P1 := by rw [m24]; exact p23_1064
  clear p23_1064 p23_fe4 p23_f80 p23_c80 p23_c20 p23_bc0 p23_b60 p23_b00 p23_aa0 p23_a40 p23_9e0 p23_980 p23_900 p23_5a0 p23_540 p23_4e0 p23_480 p23_420 p23_3c0 p23_360 p23_300 p23_280 p23_200 a23_10c4 a23_1044 a23_960 a23_2e0 a23_260 a23_1e0 a23_1c0 a23_1a0 a23_180 a23_160 a23_140 a23_120 q23_f20 q23_ec0 q23_e60 q23_e00 q23_da0 q23_d40 q23_ce0 g23_9 g23_8 g23_27 g23_26 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23 p22_c80
  -- 0x824
  obtain ⟨n25, c25, u25⟩ := s24.block p2vEcT1b824 E24.self p2vEcT1b824_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem P2V n25 0x83C (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock p2vEcT1b824 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_8 : reg n25 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_19 : reg n25 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb25, runBlock_reg _ _ _ (20 : Fin 32) s24.zero (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb25, runBlock_reg _ _ _ (22 : Fin 32) s24.zero (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = rem := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_26 : reg n25 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vEcT1b824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vEcT1b824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g25_12 : reg n25 a2 = BitVec.ofNat 32 0x300 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vEcT1b824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g25_18 : reg n25 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, p2vEcT1b824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk25 : P2vKeepL B n0.mem n25.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have q25_ce0 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xCE0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_ce0 j hj
  have q25_d40 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD40 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_d40 j hj
  have q25_da0 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xDA0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_da0 j hj
  have q25_e00 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE00 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_e00 j hj
  have q25_e60 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xE60 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_e60 j hj
  have q25_ec0 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xEC0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_ec0 j hj
  have q25_f20 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF20 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_f20 j hj
  have a25_120 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m25]; exact a24_120
  have a25_140 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m25]; exact a24_140
  have a25_160 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m25]; exact a24_160
  have a25_180 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m25]; exact a24_180
  have a25_1a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m25]; exact a24_1a0
  have a25_1c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m25]; exact a24_1c0
  have a25_1e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m25]; exact a24_1e0
  have a25_260 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m25]; exact a24_260
  have a25_2e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m25]; exact a24_2e0
  have a25_960 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m25]; exact a24_960
  have a25_1044 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m25]; exact a24_1044
  have a25_10c4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m25]; exact a24_10c4
  have p25_200 : ptF n25.mem B 0x200 = P0 := by rw [m25]; exact p24_200
  have p25_280 : ptF n25.mem B 0x280 = P1 := by rw [m25]; exact p24_280
  have p25_300 : ptF n25.mem B 0x300 = tbl2 P0 0 := by rw [m25]; exact p24_300
  have p25_360 : ptF n25.mem B 0x360 = tbl2 P0 1 := by rw [m25]; exact p24_360
  have p25_3c0 : ptF n25.mem B 0x3C0 = tbl2 P0 2 := by rw [m25]; exact p24_3c0
  have p25_420 : ptF n25.mem B 0x420 = tbl2 P0 3 := by rw [m25]; exact p24_420
  have p25_480 : ptF n25.mem B 0x480 = tbl2 P0 4 := by rw [m25]; exact p24_480
  have p25_4e0 : ptF n25.mem B 0x4E0 = tbl2 P0 5 := by rw [m25]; exact p24_4e0
  have p25_540 : ptF n25.mem B 0x540 = tbl2 P0 6 := by rw [m25]; exact p24_540
  have p25_5a0 : ptF n25.mem B 0x5A0 = tbl2 P0 7 := by rw [m25]; exact p24_5a0
  have p25_900 : ptF n25.mem B 0x900 = P1 := by rw [m25]; exact p24_900
  have p25_980 : ptF n25.mem B 0x980 = tbl2 P1 0 := by rw [m25]; exact p24_980
  have p25_9e0 : ptF n25.mem B 0x9E0 = tbl2 P1 1 := by rw [m25]; exact p24_9e0
  have p25_a40 : ptF n25.mem B 0xA40 = tbl2 P1 2 := by rw [m25]; exact p24_a40
  have p25_aa0 : ptF n25.mem B 0xAA0 = tbl2 P1 3 := by rw [m25]; exact p24_aa0
  have p25_b00 : ptF n25.mem B 0xB00 = tbl2 P1 4 := by rw [m25]; exact p24_b00
  have p25_b60 : ptF n25.mem B 0xB60 = tbl2 P1 5 := by rw [m25]; exact p24_b60
  have p25_bc0 : ptF n25.mem B 0xBC0 = tbl2 P1 6 := by rw [m25]; exact p24_bc0
  have p25_c20 : ptF n25.mem B 0xC20 = tbl2 P1 7 := by rw [m25]; exact p24_c20
  have p25_c80 : ptF n25.mem B 0xC80 = tbl2 P1 8 := by rw [m25]; exact p24_c80
  have p25_f80 : ptF n25.mem B 0xF80 = ptDbl2 P1 := by rw [m25]; exact p24_f80
  have p25_fe4 : ptF n25.mem B 0xFE4 = P0 := by rw [m25]; exact p24_fe4
  have p25_1064 : ptF n25.mem B 0x1064 = P1 := by rw [m25]; exact p24_1064
  clear p24_1064 p24_fe4 p24_f80 p24_c80 p24_c20 p24_bc0 p24_b60 p24_b00 p24_aa0 p24_a40 p24_9e0 p24_980 p24_900 p24_5a0 p24_540 p24_4e0 p24_480 p24_420 p24_3c0 p24_360 p24_300 p24_280 p24_200 a24_10c4 a24_1044 a24_960 a24_2e0 a24_260 a24_1e0 a24_1c0 a24_1a0 a24_180 a24_160 a24_140 a24_120 q24_f20 q24_ec0 q24_e60 q24_e00 q24_da0 q24_d40 q24_ce0 g24_27 g24_26 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x83C: memcpy
  obtain ⟨n26, P26, K26, X26⟩ := p2v_mc (c := 0xC80) (d := 0x980) (N := 0x300) F E25 s25 p2v_at_83c p2v_at_840
    (by decide) (by decide) g25_2 g25_10 g25_11 g25_12
    (by decide) (by decide) (by decide)
  have s26 := P26.st
  have fr26 := P26.fr
  have t26 : Steps n0 n26 := t25.trans P26.steps
  have fR26 : ∀ x, P2vR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : P2vCode n26.mem := E25.fr F fr26
  have V26 : P2vSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [P26.regs sp (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P26.regs (3 : Fin 32) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P26.regs (4 : Fin 32) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [P26.regs (8 : Fin 32) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P26.regs (9 : Fin 32) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P26.regs (18 : Fin 32) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P26.regs (19 : Fin 32) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P26.regs (20 : Fin 32) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P26.regs (21 : Fin 32) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P26.regs (22 : Fin 32) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P26.regs (23 : Fin 32) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = rem := by rw [P26.regs (24 : Fin 32) (by decide), g25_24]
  have g26_26 : reg n26 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P26.regs (26 : Fin 32) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P26.regs (27 : Fin 32) (by decide), g25_27]
  have keep_kk26 : P2vKeepL B n0.mem n26.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60), (0xC80, 0x300)] := keep_kk25.trans K26.toL
  clear keep_kk25
  have a26_120 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K26.acc (by decide) (by decide)).trans a25_120
  have a26_140 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K26.acc (by decide) (by decide)).trans a25_140
  have a26_160 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K26.acc (by decide) (by decide)).trans a25_160
  have a26_180 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K26.acc (by decide) (by decide)).trans a25_180
  have a26_1a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K26.acc (by decide) (by decide)).trans a25_1a0
  have a26_1c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K26.acc (by decide) (by decide)).trans a25_1c0
  have a26_1e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K26.acc (by decide) (by decide)).trans a25_1e0
  have a26_260 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K26.acc (by decide) (by decide)).trans a25_260
  have a26_2e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K26.acc (by decide) (by decide)).trans a25_2e0
  have a26_960 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K26.acc (by decide) (by decide)).trans a25_960
  have a26_1044 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K26.acc (by decide) (by decide)).trans a25_1044
  have a26_10c4 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K26.acc (by decide) (by decide)).trans a25_10c4
  have p26_200 : ptF n26.mem B 0x200 = P0 := (K26.pt (by decide) (by decide)).trans p25_200
  have p26_280 : ptF n26.mem B 0x280 = P1 := (K26.pt (by decide) (by decide)).trans p25_280
  have p26_300 : ptF n26.mem B 0x300 = tbl2 P0 0 := (K26.pt (by decide) (by decide)).trans p25_300
  have p26_360 : ptF n26.mem B 0x360 = tbl2 P0 1 := (K26.pt (by decide) (by decide)).trans p25_360
  have p26_3c0 : ptF n26.mem B 0x3C0 = tbl2 P0 2 := (K26.pt (by decide) (by decide)).trans p25_3c0
  have p26_420 : ptF n26.mem B 0x420 = tbl2 P0 3 := (K26.pt (by decide) (by decide)).trans p25_420
  have p26_480 : ptF n26.mem B 0x480 = tbl2 P0 4 := (K26.pt (by decide) (by decide)).trans p25_480
  have p26_4e0 : ptF n26.mem B 0x4E0 = tbl2 P0 5 := (K26.pt (by decide) (by decide)).trans p25_4e0
  have p26_540 : ptF n26.mem B 0x540 = tbl2 P0 6 := (K26.pt (by decide) (by decide)).trans p25_540
  have p26_5a0 : ptF n26.mem B 0x5A0 = tbl2 P0 7 := (K26.pt (by decide) (by decide)).trans p25_5a0
  have p26_900 : ptF n26.mem B 0x900 = P1 := (K26.pt (by decide) (by decide)).trans p25_900
  have p26_980 : ptF n26.mem B 0x980 = tbl2 P1 0 := (K26.pt (by decide) (by decide)).trans p25_980
  have p26_9e0 : ptF n26.mem B 0x9E0 = tbl2 P1 1 := (K26.pt (by decide) (by decide)).trans p25_9e0
  have p26_a40 : ptF n26.mem B 0xA40 = tbl2 P1 2 := (K26.pt (by decide) (by decide)).trans p25_a40
  have p26_aa0 : ptF n26.mem B 0xAA0 = tbl2 P1 3 := (K26.pt (by decide) (by decide)).trans p25_aa0
  have p26_b00 : ptF n26.mem B 0xB00 = tbl2 P1 4 := (K26.pt (by decide) (by decide)).trans p25_b00
  have p26_b60 : ptF n26.mem B 0xB60 = tbl2 P1 5 := (K26.pt (by decide) (by decide)).trans p25_b60
  have p26_bc0 : ptF n26.mem B 0xBC0 = tbl2 P1 6 := (K26.pt (by decide) (by decide)).trans p25_bc0
  have p26_c20 : ptF n26.mem B 0xC20 = tbl2 P1 7 := (K26.pt (by decide) (by decide)).trans p25_c20
  have p26_f80 : ptF n26.mem B 0xF80 = ptDbl2 P1 := (K26.pt (by decide) (by decide)).trans p25_f80
  have p26_fe4 : ptF n26.mem B 0xFE4 = P0 := (K26.pt (by decide) (by decide)).trans p25_fe4
  have p26_1064 : ptF n26.mem B 0x1064 = P1 := (K26.pt (by decide) (by decide)).trans p25_1064
  have p26_c80 : ptF n26.mem B 0xC80 = tbl2 P1 0 := (ptF_cp X26 (by decide) (by decide) (by decide)).trans p25_980
  have p26_ce0 : ptF n26.mem B 0xCE0 = tbl2 P1 1 := (ptF_cp X26 (by decide) (by decide) (by decide)).trans p25_9e0
  have p26_d40 : ptF n26.mem B 0xD40 = tbl2 P1 2 := (ptF_cp X26 (by decide) (by decide) (by decide)).trans p25_a40
  have p26_da0 : ptF n26.mem B 0xDA0 = tbl2 P1 3 := (ptF_cp X26 (by decide) (by decide) (by decide)).trans p25_aa0
  have p26_e00 : ptF n26.mem B 0xE00 = tbl2 P1 4 := (ptF_cp X26 (by decide) (by decide) (by decide)).trans p25_b00
  have p26_e60 : ptF n26.mem B 0xE60 = tbl2 P1 5 := (ptF_cp X26 (by decide) (by decide) (by decide)).trans p25_b60
  have p26_ec0 : ptF n26.mem B 0xEC0 = tbl2 P1 6 := (ptF_cp X26 (by decide) (by decide) (by decide)).trans p25_bc0
  have p26_f20 : ptF n26.mem B 0xF20 = tbl2 P1 7 := (ptF_cp X26 (by decide) (by decide) (by decide)).trans p25_c20
  clear p25_1064 p25_fe4 p25_f80 p25_c80 p25_c20 p25_bc0 p25_b60 p25_b00 p25_aa0 p25_a40 p25_9e0 p25_980 p25_900 p25_5a0 p25_540 p25_4e0 p25_480 p25_420 p25_3c0 p25_360 p25_300 p25_280 p25_200 a25_10c4 a25_1044 a25_960 a25_2e0 a25_260 a25_1e0 a25_1c0 a25_1a0 a25_180 a25_160 a25_140 a25_120 q25_f20 q25_ec0 q25_e60 q25_e00 q25_da0 q25_d40 q25_ce0 g25_18 g25_12 g25_11 g25_10 g25_27 g25_26 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x844
  obtain ⟨n27, c27, u27⟩ := s26.block p2vEcT1b844 E26.self p2vEcT1b844_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem P2V n27 0x856 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock p2vEcT1b844 (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
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
  have g27_8 : reg n27 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb27, runBlock_reg _ _ _ (20 : Fin 32) s26.zero (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = rem := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_26 : reg n27 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_10 : reg n27 a0 = B + 0x21A0 + BitVec.ofNat 32 0x600 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, p2vEcT1b844, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_26, g26_27, s26.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, p2vEcT1b844, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_26, g26_27, s26.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g27_12 : reg n27 a2 = BitVec.ofNat 32 0x300 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, p2vEcT1b844, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_26, g26_27, s26.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk27 : P2vKeepL B n0.mem n27.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60), (0xC80, 0x300)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have a27_120 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m27]; exact a26_120
  have a27_140 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m27]; exact a26_140
  have a27_160 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m27]; exact a26_160
  have a27_180 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m27]; exact a26_180
  have a27_1a0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m27]; exact a26_1a0
  have a27_1c0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m27]; exact a26_1c0
  have a27_1e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m27]; exact a26_1e0
  have a27_260 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m27]; exact a26_260
  have a27_2e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m27]; exact a26_2e0
  have a27_960 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m27]; exact a26_960
  have a27_1044 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m27]; exact a26_1044
  have a27_10c4 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m27]; exact a26_10c4
  have p27_200 : ptF n27.mem B 0x200 = P0 := by rw [m27]; exact p26_200
  have p27_280 : ptF n27.mem B 0x280 = P1 := by rw [m27]; exact p26_280
  have p27_300 : ptF n27.mem B 0x300 = tbl2 P0 0 := by rw [m27]; exact p26_300
  have p27_360 : ptF n27.mem B 0x360 = tbl2 P0 1 := by rw [m27]; exact p26_360
  have p27_3c0 : ptF n27.mem B 0x3C0 = tbl2 P0 2 := by rw [m27]; exact p26_3c0
  have p27_420 : ptF n27.mem B 0x420 = tbl2 P0 3 := by rw [m27]; exact p26_420
  have p27_480 : ptF n27.mem B 0x480 = tbl2 P0 4 := by rw [m27]; exact p26_480
  have p27_4e0 : ptF n27.mem B 0x4E0 = tbl2 P0 5 := by rw [m27]; exact p26_4e0
  have p27_540 : ptF n27.mem B 0x540 = tbl2 P0 6 := by rw [m27]; exact p26_540
  have p27_5a0 : ptF n27.mem B 0x5A0 = tbl2 P0 7 := by rw [m27]; exact p26_5a0
  have p27_900 : ptF n27.mem B 0x900 = P1 := by rw [m27]; exact p26_900
  have p27_980 : ptF n27.mem B 0x980 = tbl2 P1 0 := by rw [m27]; exact p26_980
  have p27_9e0 : ptF n27.mem B 0x9E0 = tbl2 P1 1 := by rw [m27]; exact p26_9e0
  have p27_a40 : ptF n27.mem B 0xA40 = tbl2 P1 2 := by rw [m27]; exact p26_a40
  have p27_aa0 : ptF n27.mem B 0xAA0 = tbl2 P1 3 := by rw [m27]; exact p26_aa0
  have p27_b00 : ptF n27.mem B 0xB00 = tbl2 P1 4 := by rw [m27]; exact p26_b00
  have p27_b60 : ptF n27.mem B 0xB60 = tbl2 P1 5 := by rw [m27]; exact p26_b60
  have p27_bc0 : ptF n27.mem B 0xBC0 = tbl2 P1 6 := by rw [m27]; exact p26_bc0
  have p27_c20 : ptF n27.mem B 0xC20 = tbl2 P1 7 := by rw [m27]; exact p26_c20
  have p27_c80 : ptF n27.mem B 0xC80 = tbl2 P1 0 := by rw [m27]; exact p26_c80
  have p27_ce0 : ptF n27.mem B 0xCE0 = tbl2 P1 1 := by rw [m27]; exact p26_ce0
  have p27_d40 : ptF n27.mem B 0xD40 = tbl2 P1 2 := by rw [m27]; exact p26_d40
  have p27_da0 : ptF n27.mem B 0xDA0 = tbl2 P1 3 := by rw [m27]; exact p26_da0
  have p27_e00 : ptF n27.mem B 0xE00 = tbl2 P1 4 := by rw [m27]; exact p26_e00
  have p27_e60 : ptF n27.mem B 0xE60 = tbl2 P1 5 := by rw [m27]; exact p26_e60
  have p27_ec0 : ptF n27.mem B 0xEC0 = tbl2 P1 6 := by rw [m27]; exact p26_ec0
  have p27_f20 : ptF n27.mem B 0xF20 = tbl2 P1 7 := by rw [m27]; exact p26_f20
  have p27_f80 : ptF n27.mem B 0xF80 = ptDbl2 P1 := by rw [m27]; exact p26_f80
  have p27_fe4 : ptF n27.mem B 0xFE4 = P0 := by rw [m27]; exact p26_fe4
  have p27_1064 : ptF n27.mem B 0x1064 = P1 := by rw [m27]; exact p26_1064
  clear p26_f20 p26_ec0 p26_e60 p26_e00 p26_da0 p26_d40 p26_ce0 p26_c80 p26_1064 p26_fe4 p26_f80 p26_c20 p26_bc0 p26_b60 p26_b00 p26_aa0 p26_a40 p26_9e0 p26_980 p26_900 p26_5a0 p26_540 p26_4e0 p26_480 p26_420 p26_3c0 p26_360 p26_300 p26_280 p26_200 a26_10c4 a26_1044 a26_960 a26_2e0 a26_260 a26_1e0 a26_1c0 a26_1a0 a26_180 a26_160 a26_140 a26_120 g26_27 g26_26 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 s26 X26 K26 P26
  -- 0x856: memcpy
  obtain ⟨n28, P28, K28, X28⟩ := p2v_mc (c := 0x600) (d := 0xC80) (N := 0x300) F E27 s27 p2v_at_856 p2v_at_85a
    (by decide) (by decide) g27_2 g27_10 g27_11 g27_12
    (by decide) (by decide) (by decide)
  have s28 := P28.st
  have fr28 := P28.fr
  have t28 : Steps n0 n28 := t27.trans P28.steps
  have fR28 : ∀ x, P2vR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : P2vCode n28.mem := E27.fr F fr28
  have V28 : P2vSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [P28.regs sp (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P28.regs (3 : Fin 32) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P28.regs (4 : Fin 32) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [P28.regs (8 : Fin 32) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P28.regs (9 : Fin 32) (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P28.regs (18 : Fin 32) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P28.regs (19 : Fin 32) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P28.regs (20 : Fin 32) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P28.regs (21 : Fin 32) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [P28.regs (22 : Fin 32) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P28.regs (23 : Fin 32) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = rem := by rw [P28.regs (24 : Fin 32) (by decide), g27_24]
  have g28_26 : reg n28 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P28.regs (26 : Fin 32) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P28.regs (27 : Fin 32) (by decide), g27_27]
  have keep_kk28 : P2vKeepL B n0.mem n28.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60), (0xC80, 0x300), (0x600, 0x300)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have a28_120 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := (K28.acc (by decide) (by decide)).trans a27_120
  have a28_140 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := (K28.acc (by decide) (by decide)).trans a27_140
  have a28_160 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := (K28.acc (by decide) (by decide)).trans a27_160
  have a28_180 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K28.acc (by decide) (by decide)).trans a27_180
  have a28_1a0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K28.acc (by decide) (by decide)).trans a27_1a0
  have a28_1c0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K28.acc (by decide) (by decide)).trans a27_1c0
  have a28_1e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := (K28.acc (by decide) (by decide)).trans a27_1e0
  have a28_260 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K28.acc (by decide) (by decide)).trans a27_260
  have a28_2e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K28.acc (by decide) (by decide)).trans a27_2e0
  have a28_960 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := (K28.acc (by decide) (by decide)).trans a27_960
  have a28_1044 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K28.acc (by decide) (by decide)).trans a27_1044
  have a28_10c4 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K28.acc (by decide) (by decide)).trans a27_10c4
  have p28_200 : ptF n28.mem B 0x200 = P0 := (K28.pt (by decide) (by decide)).trans p27_200
  have p28_280 : ptF n28.mem B 0x280 = P1 := (K28.pt (by decide) (by decide)).trans p27_280
  have p28_300 : ptF n28.mem B 0x300 = tbl2 P0 0 := (K28.pt (by decide) (by decide)).trans p27_300
  have p28_360 : ptF n28.mem B 0x360 = tbl2 P0 1 := (K28.pt (by decide) (by decide)).trans p27_360
  have p28_3c0 : ptF n28.mem B 0x3C0 = tbl2 P0 2 := (K28.pt (by decide) (by decide)).trans p27_3c0
  have p28_420 : ptF n28.mem B 0x420 = tbl2 P0 3 := (K28.pt (by decide) (by decide)).trans p27_420
  have p28_480 : ptF n28.mem B 0x480 = tbl2 P0 4 := (K28.pt (by decide) (by decide)).trans p27_480
  have p28_4e0 : ptF n28.mem B 0x4E0 = tbl2 P0 5 := (K28.pt (by decide) (by decide)).trans p27_4e0
  have p28_540 : ptF n28.mem B 0x540 = tbl2 P0 6 := (K28.pt (by decide) (by decide)).trans p27_540
  have p28_5a0 : ptF n28.mem B 0x5A0 = tbl2 P0 7 := (K28.pt (by decide) (by decide)).trans p27_5a0
  have p28_900 : ptF n28.mem B 0x900 = P1 := (K28.pt (by decide) (by decide)).trans p27_900
  have p28_980 : ptF n28.mem B 0x980 = tbl2 P1 0 := (K28.pt (by decide) (by decide)).trans p27_980
  have p28_9e0 : ptF n28.mem B 0x9E0 = tbl2 P1 1 := (K28.pt (by decide) (by decide)).trans p27_9e0
  have p28_a40 : ptF n28.mem B 0xA40 = tbl2 P1 2 := (K28.pt (by decide) (by decide)).trans p27_a40
  have p28_aa0 : ptF n28.mem B 0xAA0 = tbl2 P1 3 := (K28.pt (by decide) (by decide)).trans p27_aa0
  have p28_b00 : ptF n28.mem B 0xB00 = tbl2 P1 4 := (K28.pt (by decide) (by decide)).trans p27_b00
  have p28_b60 : ptF n28.mem B 0xB60 = tbl2 P1 5 := (K28.pt (by decide) (by decide)).trans p27_b60
  have p28_bc0 : ptF n28.mem B 0xBC0 = tbl2 P1 6 := (K28.pt (by decide) (by decide)).trans p27_bc0
  have p28_c20 : ptF n28.mem B 0xC20 = tbl2 P1 7 := (K28.pt (by decide) (by decide)).trans p27_c20
  have p28_c80 : ptF n28.mem B 0xC80 = tbl2 P1 0 := (K28.pt (by decide) (by decide)).trans p27_c80
  have p28_ce0 : ptF n28.mem B 0xCE0 = tbl2 P1 1 := (K28.pt (by decide) (by decide)).trans p27_ce0
  have p28_d40 : ptF n28.mem B 0xD40 = tbl2 P1 2 := (K28.pt (by decide) (by decide)).trans p27_d40
  have p28_da0 : ptF n28.mem B 0xDA0 = tbl2 P1 3 := (K28.pt (by decide) (by decide)).trans p27_da0
  have p28_e00 : ptF n28.mem B 0xE00 = tbl2 P1 4 := (K28.pt (by decide) (by decide)).trans p27_e00
  have p28_e60 : ptF n28.mem B 0xE60 = tbl2 P1 5 := (K28.pt (by decide) (by decide)).trans p27_e60
  have p28_ec0 : ptF n28.mem B 0xEC0 = tbl2 P1 6 := (K28.pt (by decide) (by decide)).trans p27_ec0
  have p28_f20 : ptF n28.mem B 0xF20 = tbl2 P1 7 := (K28.pt (by decide) (by decide)).trans p27_f20
  have p28_f80 : ptF n28.mem B 0xF80 = ptDbl2 P1 := (K28.pt (by decide) (by decide)).trans p27_f80
  have p28_fe4 : ptF n28.mem B 0xFE4 = P0 := (K28.pt (by decide) (by decide)).trans p27_fe4
  have p28_1064 : ptF n28.mem B 0x1064 = P1 := (K28.pt (by decide) (by decide)).trans p27_1064
  have p28_600 : ptF n28.mem B 0x600 = tbl2 P1 0 := (ptF_cp X28 (by decide) (by decide) (by decide)).trans p27_c80
  have p28_660 : ptF n28.mem B 0x660 = tbl2 P1 1 := (ptF_cp X28 (by decide) (by decide) (by decide)).trans p27_ce0
  have p28_6c0 : ptF n28.mem B 0x6C0 = tbl2 P1 2 := (ptF_cp X28 (by decide) (by decide) (by decide)).trans p27_d40
  have p28_720 : ptF n28.mem B 0x720 = tbl2 P1 3 := (ptF_cp X28 (by decide) (by decide) (by decide)).trans p27_da0
  have p28_780 : ptF n28.mem B 0x780 = tbl2 P1 4 := (ptF_cp X28 (by decide) (by decide) (by decide)).trans p27_e00
  have p28_7e0 : ptF n28.mem B 0x7E0 = tbl2 P1 5 := (ptF_cp X28 (by decide) (by decide) (by decide)).trans p27_e60
  have p28_840 : ptF n28.mem B 0x840 = tbl2 P1 6 := (ptF_cp X28 (by decide) (by decide) (by decide)).trans p27_ec0
  have p28_8a0 : ptF n28.mem B 0x8A0 = tbl2 P1 7 := (ptF_cp X28 (by decide) (by decide) (by decide)).trans p27_f20
  clear p27_1064 p27_fe4 p27_f80 p27_f20 p27_ec0 p27_e60 p27_e00 p27_da0 p27_d40 p27_ce0 p27_c80 p27_c20 p27_bc0 p27_b60 p27_b00 p27_aa0 p27_a40 p27_9e0 p27_980 p27_900 p27_5a0 p27_540 p27_4e0 p27_480 p27_420 p27_3c0 p27_360 p27_300 p27_280 p27_200 a27_10c4 a27_1044 a27_960 a27_2e0 a27_260 a27_1e0 a27_1c0 a27_1a0 a27_180 a27_160 a27_140 a27_120 g27_12 g27_11 g27_10 g27_27 g27_26 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x85E
  obtain ⟨n29, c29, u29⟩ := s28.block p2vEcT1b85e E28.self p2vEcT1b85e_end
    ⟨trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem P2V n29 0x860 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock p2vEcT1b85e (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
  have g29_8 : reg n29 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_20 : reg n29 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = rem := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_26 : reg n29 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_19 : reg n29 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, p2vEcT1b85e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk29 : P2vKeepL B n0.mem n29.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60), (0xC80, 0x300), (0x600, 0x300)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have a29_120 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m29]; exact a28_120
  have a29_140 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m29]; exact a28_140
  have a29_160 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m29]; exact a28_160
  have a29_180 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m29]; exact a28_180
  have a29_1a0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m29]; exact a28_1a0
  have a29_1c0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m29]; exact a28_1c0
  have a29_1e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m29]; exact a28_1e0
  have a29_260 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m29]; exact a28_260
  have a29_2e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m29]; exact a28_2e0
  have a29_960 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m29]; exact a28_960
  have a29_1044 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m29]; exact a28_1044
  have a29_10c4 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m29]; exact a28_10c4
  have p29_200 : ptF n29.mem B 0x200 = P0 := by rw [m29]; exact p28_200
  have p29_280 : ptF n29.mem B 0x280 = P1 := by rw [m29]; exact p28_280
  have p29_300 : ptF n29.mem B 0x300 = tbl2 P0 0 := by rw [m29]; exact p28_300
  have p29_360 : ptF n29.mem B 0x360 = tbl2 P0 1 := by rw [m29]; exact p28_360
  have p29_3c0 : ptF n29.mem B 0x3C0 = tbl2 P0 2 := by rw [m29]; exact p28_3c0
  have p29_420 : ptF n29.mem B 0x420 = tbl2 P0 3 := by rw [m29]; exact p28_420
  have p29_480 : ptF n29.mem B 0x480 = tbl2 P0 4 := by rw [m29]; exact p28_480
  have p29_4e0 : ptF n29.mem B 0x4E0 = tbl2 P0 5 := by rw [m29]; exact p28_4e0
  have p29_540 : ptF n29.mem B 0x540 = tbl2 P0 6 := by rw [m29]; exact p28_540
  have p29_5a0 : ptF n29.mem B 0x5A0 = tbl2 P0 7 := by rw [m29]; exact p28_5a0
  have p29_600 : ptF n29.mem B 0x600 = tbl2 P1 0 := by rw [m29]; exact p28_600
  have p29_660 : ptF n29.mem B 0x660 = tbl2 P1 1 := by rw [m29]; exact p28_660
  have p29_6c0 : ptF n29.mem B 0x6C0 = tbl2 P1 2 := by rw [m29]; exact p28_6c0
  have p29_720 : ptF n29.mem B 0x720 = tbl2 P1 3 := by rw [m29]; exact p28_720
  have p29_780 : ptF n29.mem B 0x780 = tbl2 P1 4 := by rw [m29]; exact p28_780
  have p29_7e0 : ptF n29.mem B 0x7E0 = tbl2 P1 5 := by rw [m29]; exact p28_7e0
  have p29_840 : ptF n29.mem B 0x840 = tbl2 P1 6 := by rw [m29]; exact p28_840
  have p29_8a0 : ptF n29.mem B 0x8A0 = tbl2 P1 7 := by rw [m29]; exact p28_8a0
  have p29_900 : ptF n29.mem B 0x900 = P1 := by rw [m29]; exact p28_900
  have p29_980 : ptF n29.mem B 0x980 = tbl2 P1 0 := by rw [m29]; exact p28_980
  have p29_9e0 : ptF n29.mem B 0x9E0 = tbl2 P1 1 := by rw [m29]; exact p28_9e0
  have p29_a40 : ptF n29.mem B 0xA40 = tbl2 P1 2 := by rw [m29]; exact p28_a40
  have p29_aa0 : ptF n29.mem B 0xAA0 = tbl2 P1 3 := by rw [m29]; exact p28_aa0
  have p29_b00 : ptF n29.mem B 0xB00 = tbl2 P1 4 := by rw [m29]; exact p28_b00
  have p29_b60 : ptF n29.mem B 0xB60 = tbl2 P1 5 := by rw [m29]; exact p28_b60
  have p29_bc0 : ptF n29.mem B 0xBC0 = tbl2 P1 6 := by rw [m29]; exact p28_bc0
  have p29_c20 : ptF n29.mem B 0xC20 = tbl2 P1 7 := by rw [m29]; exact p28_c20
  have p29_c80 : ptF n29.mem B 0xC80 = tbl2 P1 0 := by rw [m29]; exact p28_c80
  have p29_ce0 : ptF n29.mem B 0xCE0 = tbl2 P1 1 := by rw [m29]; exact p28_ce0
  have p29_d40 : ptF n29.mem B 0xD40 = tbl2 P1 2 := by rw [m29]; exact p28_d40
  have p29_da0 : ptF n29.mem B 0xDA0 = tbl2 P1 3 := by rw [m29]; exact p28_da0
  have p29_e00 : ptF n29.mem B 0xE00 = tbl2 P1 4 := by rw [m29]; exact p28_e00
  have p29_e60 : ptF n29.mem B 0xE60 = tbl2 P1 5 := by rw [m29]; exact p28_e60
  have p29_ec0 : ptF n29.mem B 0xEC0 = tbl2 P1 6 := by rw [m29]; exact p28_ec0
  have p29_f20 : ptF n29.mem B 0xF20 = tbl2 P1 7 := by rw [m29]; exact p28_f20
  have p29_f80 : ptF n29.mem B 0xF80 = ptDbl2 P1 := by rw [m29]; exact p28_f80
  have p29_fe4 : ptF n29.mem B 0xFE4 = P0 := by rw [m29]; exact p28_fe4
  have p29_1064 : ptF n29.mem B 0x1064 = P1 := by rw [m29]; exact p28_1064
  clear p28_8a0 p28_840 p28_7e0 p28_780 p28_720 p28_6c0 p28_660 p28_600 p28_1064 p28_fe4 p28_f80 p28_f20 p28_ec0 p28_e60 p28_e00 p28_da0 p28_d40 p28_ce0 p28_c80 p28_c20 p28_bc0 p28_b60 p28_b00 p28_aa0 p28_a40 p28_9e0 p28_980 p28_900 p28_5a0 p28_540 p28_4e0 p28_480 p28_420 p28_3c0 p28_360 p28_300 p28_280 p28_200 a28_10c4 a28_1044 a28_960 a28_2e0 a28_260 a28_1e0 a28_1c0 a28_1a0 a28_180 a28_160 a28_140 a28_120 g28_27 g28_26 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 s28 X28 K28 P28
  -- 0x860: j
  obtain ⟨n30, d30, u30⟩ := s29.jump E29.self p2v_at_860 (off' := 0x750) (by decide)
    (by rw [s29.pc]; decide)
  have s30 : St n30.mem P2V n30 0x750 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, P2vR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, P2vR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : P2vCode n30.mem := E29.fr F fr30
  have V30 : P2vSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [u30.regs, g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u30.regs, g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [u30.regs, g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u30.regs, g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u30.regs, g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u30.regs, g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u30.regs, g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u30.regs, g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = rem := by rw [u30.regs, g29_24]
  have g30_26 : reg n30 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u30.regs, g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u30.regs, g29_27]
  have keep_kk30 : P2vKeepL B n0.mem n30.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60), (0xC80, 0x300), (0x600, 0x300)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have a30_120 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m30]; exact a29_120
  have a30_140 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m30]; exact a29_140
  have a30_160 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m30]; exact a29_160
  have a30_180 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m30]; exact a29_180
  have a30_1a0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m30]; exact a29_1a0
  have a30_1c0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m30]; exact a29_1c0
  have a30_1e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m30]; exact a29_1e0
  have a30_260 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m30]; exact a29_260
  have a30_2e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m30]; exact a29_2e0
  have a30_960 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m30]; exact a29_960
  have a30_1044 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m30]; exact a29_1044
  have a30_10c4 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m30]; exact a29_10c4
  have p30_200 : ptF n30.mem B 0x200 = P0 := by rw [m30]; exact p29_200
  have p30_280 : ptF n30.mem B 0x280 = P1 := by rw [m30]; exact p29_280
  have p30_300 : ptF n30.mem B 0x300 = tbl2 P0 0 := by rw [m30]; exact p29_300
  have p30_360 : ptF n30.mem B 0x360 = tbl2 P0 1 := by rw [m30]; exact p29_360
  have p30_3c0 : ptF n30.mem B 0x3C0 = tbl2 P0 2 := by rw [m30]; exact p29_3c0
  have p30_420 : ptF n30.mem B 0x420 = tbl2 P0 3 := by rw [m30]; exact p29_420
  have p30_480 : ptF n30.mem B 0x480 = tbl2 P0 4 := by rw [m30]; exact p29_480
  have p30_4e0 : ptF n30.mem B 0x4E0 = tbl2 P0 5 := by rw [m30]; exact p29_4e0
  have p30_540 : ptF n30.mem B 0x540 = tbl2 P0 6 := by rw [m30]; exact p29_540
  have p30_5a0 : ptF n30.mem B 0x5A0 = tbl2 P0 7 := by rw [m30]; exact p29_5a0
  have p30_600 : ptF n30.mem B 0x600 = tbl2 P1 0 := by rw [m30]; exact p29_600
  have p30_660 : ptF n30.mem B 0x660 = tbl2 P1 1 := by rw [m30]; exact p29_660
  have p30_6c0 : ptF n30.mem B 0x6C0 = tbl2 P1 2 := by rw [m30]; exact p29_6c0
  have p30_720 : ptF n30.mem B 0x720 = tbl2 P1 3 := by rw [m30]; exact p29_720
  have p30_780 : ptF n30.mem B 0x780 = tbl2 P1 4 := by rw [m30]; exact p29_780
  have p30_7e0 : ptF n30.mem B 0x7E0 = tbl2 P1 5 := by rw [m30]; exact p29_7e0
  have p30_840 : ptF n30.mem B 0x840 = tbl2 P1 6 := by rw [m30]; exact p29_840
  have p30_8a0 : ptF n30.mem B 0x8A0 = tbl2 P1 7 := by rw [m30]; exact p29_8a0
  have p30_900 : ptF n30.mem B 0x900 = P1 := by rw [m30]; exact p29_900
  have p30_980 : ptF n30.mem B 0x980 = tbl2 P1 0 := by rw [m30]; exact p29_980
  have p30_9e0 : ptF n30.mem B 0x9E0 = tbl2 P1 1 := by rw [m30]; exact p29_9e0
  have p30_a40 : ptF n30.mem B 0xA40 = tbl2 P1 2 := by rw [m30]; exact p29_a40
  have p30_aa0 : ptF n30.mem B 0xAA0 = tbl2 P1 3 := by rw [m30]; exact p29_aa0
  have p30_b00 : ptF n30.mem B 0xB00 = tbl2 P1 4 := by rw [m30]; exact p29_b00
  have p30_b60 : ptF n30.mem B 0xB60 = tbl2 P1 5 := by rw [m30]; exact p29_b60
  have p30_bc0 : ptF n30.mem B 0xBC0 = tbl2 P1 6 := by rw [m30]; exact p29_bc0
  have p30_c20 : ptF n30.mem B 0xC20 = tbl2 P1 7 := by rw [m30]; exact p29_c20
  have p30_c80 : ptF n30.mem B 0xC80 = tbl2 P1 0 := by rw [m30]; exact p29_c80
  have p30_ce0 : ptF n30.mem B 0xCE0 = tbl2 P1 1 := by rw [m30]; exact p29_ce0
  have p30_d40 : ptF n30.mem B 0xD40 = tbl2 P1 2 := by rw [m30]; exact p29_d40
  have p30_da0 : ptF n30.mem B 0xDA0 = tbl2 P1 3 := by rw [m30]; exact p29_da0
  have p30_e00 : ptF n30.mem B 0xE00 = tbl2 P1 4 := by rw [m30]; exact p29_e00
  have p30_e60 : ptF n30.mem B 0xE60 = tbl2 P1 5 := by rw [m30]; exact p29_e60
  have p30_ec0 : ptF n30.mem B 0xEC0 = tbl2 P1 6 := by rw [m30]; exact p29_ec0
  have p30_f20 : ptF n30.mem B 0xF20 = tbl2 P1 7 := by rw [m30]; exact p29_f20
  have p30_f80 : ptF n30.mem B 0xF80 = ptDbl2 P1 := by rw [m30]; exact p29_f80
  have p30_fe4 : ptF n30.mem B 0xFE4 = P0 := by rw [m30]; exact p29_fe4
  have p30_1064 : ptF n30.mem B 0x1064 = P1 := by rw [m30]; exact p29_1064
  clear p29_1064 p29_fe4 p29_f80 p29_f20 p29_ec0 p29_e60 p29_e00 p29_da0 p29_d40 p29_ce0 p29_c80 p29_c20 p29_bc0 p29_b60 p29_b00 p29_aa0 p29_a40 p29_9e0 p29_980 p29_900 p29_8a0 p29_840 p29_7e0 p29_780 p29_720 p29_6c0 p29_660 p29_600 p29_5a0 p29_540 p29_4e0 p29_480 p29_420 p29_3c0 p29_360 p29_300 p29_280 p29_200 a29_10c4 a29_1044 a29_960 a29_2e0 a29_260 a29_1e0 a29_1c0 a29_1a0 a29_180 a29_160 a29_140 a29_120 g29_19 g29_27 g29_26 g29_24 g29_23 g29_22 g29_21 g29_20 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  -- 0x750
  obtain ⟨n31, c31, u31⟩ := s30.block p2vEcT1b750 E30.self p2vEcT1b750_end
    ⟨trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem P2V n31 0x754 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock p2vEcT1b750 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
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
  have g31_8 : reg n31 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb31, runBlock_reg _ _ _ (8 : Fin 32) s30.zero (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
  have g31_18 : reg n31 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = rem := by
    rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
  have g31_26 : reg n31 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
  have g31_10 : reg n31 a0 = B + 0x21A0 + BitVec.ofNat 32 0x7FF := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, p2vEcT1b750, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk31 : P2vKeepL B n0.mem n31.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60), (0xC80, 0x300), (0x600, 0x300)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have a31_120 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m31]; exact a30_120
  have a31_140 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m31]; exact a30_140
  have a31_160 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m31]; exact a30_160
  have a31_180 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m31]; exact a30_180
  have a31_1a0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m31]; exact a30_1a0
  have a31_1c0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m31]; exact a30_1c0
  have a31_1e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m31]; exact a30_1e0
  have a31_260 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m31]; exact a30_260
  have a31_2e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m31]; exact a30_2e0
  have a31_960 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m31]; exact a30_960
  have a31_1044 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m31]; exact a30_1044
  have a31_10c4 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m31]; exact a30_10c4
  have p31_200 : ptF n31.mem B 0x200 = P0 := by rw [m31]; exact p30_200
  have p31_280 : ptF n31.mem B 0x280 = P1 := by rw [m31]; exact p30_280
  have p31_300 : ptF n31.mem B 0x300 = tbl2 P0 0 := by rw [m31]; exact p30_300
  have p31_360 : ptF n31.mem B 0x360 = tbl2 P0 1 := by rw [m31]; exact p30_360
  have p31_3c0 : ptF n31.mem B 0x3C0 = tbl2 P0 2 := by rw [m31]; exact p30_3c0
  have p31_420 : ptF n31.mem B 0x420 = tbl2 P0 3 := by rw [m31]; exact p30_420
  have p31_480 : ptF n31.mem B 0x480 = tbl2 P0 4 := by rw [m31]; exact p30_480
  have p31_4e0 : ptF n31.mem B 0x4E0 = tbl2 P0 5 := by rw [m31]; exact p30_4e0
  have p31_540 : ptF n31.mem B 0x540 = tbl2 P0 6 := by rw [m31]; exact p30_540
  have p31_5a0 : ptF n31.mem B 0x5A0 = tbl2 P0 7 := by rw [m31]; exact p30_5a0
  have p31_600 : ptF n31.mem B 0x600 = tbl2 P1 0 := by rw [m31]; exact p30_600
  have p31_660 : ptF n31.mem B 0x660 = tbl2 P1 1 := by rw [m31]; exact p30_660
  have p31_6c0 : ptF n31.mem B 0x6C0 = tbl2 P1 2 := by rw [m31]; exact p30_6c0
  have p31_720 : ptF n31.mem B 0x720 = tbl2 P1 3 := by rw [m31]; exact p30_720
  have p31_780 : ptF n31.mem B 0x780 = tbl2 P1 4 := by rw [m31]; exact p30_780
  have p31_7e0 : ptF n31.mem B 0x7E0 = tbl2 P1 5 := by rw [m31]; exact p30_7e0
  have p31_840 : ptF n31.mem B 0x840 = tbl2 P1 6 := by rw [m31]; exact p30_840
  have p31_8a0 : ptF n31.mem B 0x8A0 = tbl2 P1 7 := by rw [m31]; exact p30_8a0
  have p31_900 : ptF n31.mem B 0x900 = P1 := by rw [m31]; exact p30_900
  have p31_980 : ptF n31.mem B 0x980 = tbl2 P1 0 := by rw [m31]; exact p30_980
  have p31_9e0 : ptF n31.mem B 0x9E0 = tbl2 P1 1 := by rw [m31]; exact p30_9e0
  have p31_a40 : ptF n31.mem B 0xA40 = tbl2 P1 2 := by rw [m31]; exact p30_a40
  have p31_aa0 : ptF n31.mem B 0xAA0 = tbl2 P1 3 := by rw [m31]; exact p30_aa0
  have p31_b00 : ptF n31.mem B 0xB00 = tbl2 P1 4 := by rw [m31]; exact p30_b00
  have p31_b60 : ptF n31.mem B 0xB60 = tbl2 P1 5 := by rw [m31]; exact p30_b60
  have p31_bc0 : ptF n31.mem B 0xBC0 = tbl2 P1 6 := by rw [m31]; exact p30_bc0
  have p31_c20 : ptF n31.mem B 0xC20 = tbl2 P1 7 := by rw [m31]; exact p30_c20
  have p31_c80 : ptF n31.mem B 0xC80 = tbl2 P1 0 := by rw [m31]; exact p30_c80
  have p31_ce0 : ptF n31.mem B 0xCE0 = tbl2 P1 1 := by rw [m31]; exact p30_ce0
  have p31_d40 : ptF n31.mem B 0xD40 = tbl2 P1 2 := by rw [m31]; exact p30_d40
  have p31_da0 : ptF n31.mem B 0xDA0 = tbl2 P1 3 := by rw [m31]; exact p30_da0
  have p31_e00 : ptF n31.mem B 0xE00 = tbl2 P1 4 := by rw [m31]; exact p30_e00
  have p31_e60 : ptF n31.mem B 0xE60 = tbl2 P1 5 := by rw [m31]; exact p30_e60
  have p31_ec0 : ptF n31.mem B 0xEC0 = tbl2 P1 6 := by rw [m31]; exact p30_ec0
  have p31_f20 : ptF n31.mem B 0xF20 = tbl2 P1 7 := by rw [m31]; exact p30_f20
  have p31_f80 : ptF n31.mem B 0xF80 = ptDbl2 P1 := by rw [m31]; exact p30_f80
  have p31_fe4 : ptF n31.mem B 0xFE4 = P0 := by rw [m31]; exact p30_fe4
  have p31_1064 : ptF n31.mem B 0x1064 = P1 := by rw [m31]; exact p30_1064
  clear p30_1064 p30_fe4 p30_f80 p30_f20 p30_ec0 p30_e60 p30_e00 p30_da0 p30_d40 p30_ce0 p30_c80 p30_c20 p30_bc0 p30_b60 p30_b00 p30_aa0 p30_a40 p30_9e0 p30_980 p30_900 p30_8a0 p30_840 p30_7e0 p30_780 p30_720 p30_6c0 p30_660 p30_600 p30_5a0 p30_540 p30_4e0 p30_480 p30_420 p30_3c0 p30_360 p30_300 p30_280 p30_200 a30_10c4 a30_1044 a30_960 a30_2e0 a30_260 a30_1e0 a30_1c0 a30_1a0 a30_180 a30_160 a30_140 a30_120 g30_27 g30_26 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  -- 0x754: branch, taken
  obtain ⟨n32, d32, u32⟩ := s31.taken E31.self 0x862 p2v_at_754
    (by decide) (by rw [g31_19, g31_20]; decide)
  have s32 : St n32.mem P2V n32 0x862 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, P2vR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, P2vR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : P2vCode n32.mem := E31.fr F fr32
  have V32 : P2vSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by rw [u32.regs, g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u32.regs, g31_9]
  have g32_10 : reg n32 a0 = B + 0x21A0 + BitVec.ofNat 32 0x7FF := by rw [u32.regs, g31_10]
  have g32_18 : reg n32 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [u32.regs, g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u32.regs, g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u32.regs, g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u32.regs, g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u32.regs, g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u32.regs, g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = rem := by rw [u32.regs, g31_24]
  have g32_26 : reg n32 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u32.regs, g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u32.regs, g31_27]
  have keep_kk32 : P2vKeepL B n0.mem n32.mem [(0xB00, 0x60), (0xC80, 0x60), (0xB60, 0x60), (0xC80, 0x60), (0xBC0, 0x60), (0xC80, 0x60), (0xC20, 0x60), (0xC80, 0x60), (0xC80, 0x300), (0x600, 0x300)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have a32_120 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx := by rw [m32]; exact a31_120
  have a32_140 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy := by rw [m32]; exact a31_140
  have a32_160 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz := by rw [m32]; exact a31_160
  have a32_180 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m32]; exact a31_180
  have a32_1a0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m32]; exact a31_1a0
  have a32_1c0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m32]; exact a31_1c0
  have a32_1e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1E0) 8 = wv := by rw [m32]; exact a31_1e0
  have a32_260 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m32]; exact a31_260
  have a32_2e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m32]; exact a31_2e0
  have a32_960 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x960) 8 = U2 := by rw [m32]; exact a31_960
  have a32_1044 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m32]; exact a31_1044
  have a32_10c4 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m32]; exact a31_10c4
  have p32_200 : ptF n32.mem B 0x200 = P0 := by rw [m32]; exact p31_200
  have p32_280 : ptF n32.mem B 0x280 = P1 := by rw [m32]; exact p31_280
  have p32_300 : ptF n32.mem B 0x300 = tbl2 P0 0 := by rw [m32]; exact p31_300
  have p32_360 : ptF n32.mem B 0x360 = tbl2 P0 1 := by rw [m32]; exact p31_360
  have p32_3c0 : ptF n32.mem B 0x3C0 = tbl2 P0 2 := by rw [m32]; exact p31_3c0
  have p32_420 : ptF n32.mem B 0x420 = tbl2 P0 3 := by rw [m32]; exact p31_420
  have p32_480 : ptF n32.mem B 0x480 = tbl2 P0 4 := by rw [m32]; exact p31_480
  have p32_4e0 : ptF n32.mem B 0x4E0 = tbl2 P0 5 := by rw [m32]; exact p31_4e0
  have p32_540 : ptF n32.mem B 0x540 = tbl2 P0 6 := by rw [m32]; exact p31_540
  have p32_5a0 : ptF n32.mem B 0x5A0 = tbl2 P0 7 := by rw [m32]; exact p31_5a0
  have p32_600 : ptF n32.mem B 0x600 = tbl2 P1 0 := by rw [m32]; exact p31_600
  have p32_660 : ptF n32.mem B 0x660 = tbl2 P1 1 := by rw [m32]; exact p31_660
  have p32_6c0 : ptF n32.mem B 0x6C0 = tbl2 P1 2 := by rw [m32]; exact p31_6c0
  have p32_720 : ptF n32.mem B 0x720 = tbl2 P1 3 := by rw [m32]; exact p31_720
  have p32_780 : ptF n32.mem B 0x780 = tbl2 P1 4 := by rw [m32]; exact p31_780
  have p32_7e0 : ptF n32.mem B 0x7E0 = tbl2 P1 5 := by rw [m32]; exact p31_7e0
  have p32_840 : ptF n32.mem B 0x840 = tbl2 P1 6 := by rw [m32]; exact p31_840
  have p32_8a0 : ptF n32.mem B 0x8A0 = tbl2 P1 7 := by rw [m32]; exact p31_8a0
  have p32_900 : ptF n32.mem B 0x900 = P1 := by rw [m32]; exact p31_900
  have p32_980 : ptF n32.mem B 0x980 = tbl2 P1 0 := by rw [m32]; exact p31_980
  have p32_9e0 : ptF n32.mem B 0x9E0 = tbl2 P1 1 := by rw [m32]; exact p31_9e0
  have p32_a40 : ptF n32.mem B 0xA40 = tbl2 P1 2 := by rw [m32]; exact p31_a40
  have p32_aa0 : ptF n32.mem B 0xAA0 = tbl2 P1 3 := by rw [m32]; exact p31_aa0
  have p32_b00 : ptF n32.mem B 0xB00 = tbl2 P1 4 := by rw [m32]; exact p31_b00
  have p32_b60 : ptF n32.mem B 0xB60 = tbl2 P1 5 := by rw [m32]; exact p31_b60
  have p32_bc0 : ptF n32.mem B 0xBC0 = tbl2 P1 6 := by rw [m32]; exact p31_bc0
  have p32_c20 : ptF n32.mem B 0xC20 = tbl2 P1 7 := by rw [m32]; exact p31_c20
  have p32_c80 : ptF n32.mem B 0xC80 = tbl2 P1 0 := by rw [m32]; exact p31_c80
  have p32_ce0 : ptF n32.mem B 0xCE0 = tbl2 P1 1 := by rw [m32]; exact p31_ce0
  have p32_d40 : ptF n32.mem B 0xD40 = tbl2 P1 2 := by rw [m32]; exact p31_d40
  have p32_da0 : ptF n32.mem B 0xDA0 = tbl2 P1 3 := by rw [m32]; exact p31_da0
  have p32_e00 : ptF n32.mem B 0xE00 = tbl2 P1 4 := by rw [m32]; exact p31_e00
  have p32_e60 : ptF n32.mem B 0xE60 = tbl2 P1 5 := by rw [m32]; exact p31_e60
  have p32_ec0 : ptF n32.mem B 0xEC0 = tbl2 P1 6 := by rw [m32]; exact p31_ec0
  have p32_f20 : ptF n32.mem B 0xF20 = tbl2 P1 7 := by rw [m32]; exact p31_f20
  have p32_f80 : ptF n32.mem B 0xF80 = ptDbl2 P1 := by rw [m32]; exact p31_f80
  have p32_fe4 : ptF n32.mem B 0xFE4 = P0 := by rw [m32]; exact p31_fe4
  have p32_1064 : ptF n32.mem B 0x1064 = P1 := by rw [m32]; exact p31_1064
  clear p31_1064 p31_fe4 p31_f80 p31_f20 p31_ec0 p31_e60 p31_e00 p31_da0 p31_d40 p31_ce0 p31_c80 p31_c20 p31_bc0 p31_b60 p31_b00 p31_aa0 p31_a40 p31_9e0 p31_980 p31_900 p31_8a0 p31_840 p31_7e0 p31_780 p31_720 p31_6c0 p31_660 p31_600 p31_5a0 p31_540 p31_4e0 p31_480 p31_420 p31_3c0 p31_360 p31_300 p31_280 p31_200 a31_10c4 a31_1044 a31_960 a31_2e0 a31_260 a31_1e0 a31_1c0 a31_1a0 a31_180 a31_160 a31_140 a31_120 g31_10 g31_27 g31_26 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
  exact .inr ⟨n32, t32, s32, E32, V32, fR32, g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_26, g32_27, a32_120, a32_140, a32_160, a32_180, a32_1a0, a32_1c0, a32_1e0, a32_260, a32_2e0, a32_960, a32_1044, a32_10c4, p32_200, p32_280, p32_300, p32_360, p32_3c0, p32_420, p32_480, p32_4e0, p32_540, p32_5a0, p32_600, p32_660, p32_6c0, p32_720, p32_780, p32_7e0, p32_840, p32_8a0, p32_900, p32_980, p32_9e0, p32_a40, p32_aa0, p32_b00, p32_b60, p32_bc0, p32_c20, p32_c80, p32_ce0, p32_d40, p32_da0, p32_e00, p32_e60, p32_ec0, p32_f20, p32_f80, p32_fe4, p32_1064, keep_kk32.mono (by decide)⟩

end C3.RV32.P2v
