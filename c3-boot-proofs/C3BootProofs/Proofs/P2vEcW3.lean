import C3BootProofs.Proofs.P2vEcW2

/-!
# `p256VerifyPrehash`: the wNAF digits of `u₂`

From the loop's second pass at 0x89A to 0x998: `wnaf_form` writes the width-5 NAF digits of `u₂` into the record at 0x11EC, and both lengths are loaded.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def p2vEcW389a : List BInstr :=
  [.aluImm .add a1 (9 : Fin 32) 0x60, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x781, .aluImm .add a2 x0 0x20]
theorem p2vEcW389a_end : blockEnd p256VerifyPrehashCode 0x89A p2vEcW389a = some 0x8AA := by
  simp only [p2vEcW389a]
  rw [blockEnd, p2v_at_89a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_89e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW38b2 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x781]
theorem p2vEcW38b2_end : blockEnd p256VerifyPrehashCode 0x8B2 p2vEcW38b2 = some 0x8C2 := by
  simp only [p2vEcW38b2]
  rw [blockEnd, p2v_at_8b2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8b6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8ba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW38ca : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 x0 0x20]
theorem p2vEcW38ca_end : blockEnd p256VerifyPrehashCode 0x8CA p2vEcW38ca = some 0x8D6 := by
  simp only [p2vEcW38ca]
  rw [blockEnd, p2v_at_8ca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8ce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8d2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW38de : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x101, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .aluImm .add a2 x0 0x20]
theorem p2vEcW38de_end : blockEnd p256VerifyPrehashCode 0x8DE p2vEcW38de = some 0x8F2 := by
  simp only [p2vEcW38de]
  rw [blockEnd, p2v_at_8de]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8e2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8e6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8ea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8ee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW38fa : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 x0 0x101]
theorem p2vEcW38fa_end : blockEnd p256VerifyPrehashCode 0x8FA p2vEcW38fa = some 0x906 := by
  simp only [p2vEcW38fa]
  rw [blockEnd, p2v_at_8fa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_8fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_902]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW3912 : List BInstr :=
  [.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x80, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .aluImm .add a2 x0 0x101, .alu .add a0 x0 (18 : Fin 32)]
theorem p2vEcW3912_end : blockEnd p256VerifyPrehashCode 0x912 p2vEcW3912 = some 0x924 := by
  simp only [p2vEcW3912]
  rw [blockEnd, p2v_at_912]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_916]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_91a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_91e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_922]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW392c : List BInstr :=
  [.aluImm .add a1 x0 0x101, .aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x101, .aluImm .add a3 x0 0x20, .aluImm .add a4 x0 0x100, .alu .add a0 x0 (18 : Fin 32)]
theorem p2vEcW392c_end : blockEnd p256VerifyPrehashCode 0x92C p2vEcW392c = some 0x942 := by
  simp only [p2vEcW392c]
  rw [blockEnd, p2v_at_92c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_930]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_934]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_938]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_93c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_940]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW394e : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x108]
theorem p2vEcW394e_end : blockEnd p256VerifyPrehashCode 0x94E p2vEcW394e = some 0x962 := by
  simp only [p2vEcW394e]
  rw [blockEnd, p2v_at_94e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_952]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_956]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_95a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_95e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW396a : List BInstr :=
  [.alu .mul a0 (8 : Fin 32) (20 : Fin 32), .alu .add a0 a0 (21 : Fin 32), .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x181, .aluImm .add a2 x0 0x108]
theorem p2vEcW396a_end : blockEnd p256VerifyPrehashCode 0x96A p2vEcW396a = some 0x97C := by
  simp only [p2vEcW396a]
  rw [blockEnd, p2v_at_96a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_96e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_970]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_974]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_978]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW3984 : List BInstr :=
  [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1]
theorem p2vEcW3984_end : blockEnd p256VerifyPrehashCode 0x984 p2vEcW3984 = some 0x986 := by
  simp only [p2vEcW3984]
  rw [blockEnd, p2v_at_984]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def p2vEcW398e : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x1EC, .alu .add a0 a0 sp]
theorem p2vEcW398e_end : blockEnd p256VerifyPrehashCode 0x98E p2vEcW398e = some 0x996 := by
  simp only [p2vEcW398e]
  rw [blockEnd, p2v_at_98e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_990]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, p2v_at_994]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem p2v_ecw3 {B : Word} {U1 U2 rv sv zv : Nat} {P0 P1 : Pt2} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x89A (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x1)
    (g0_9 : reg n0 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064)
    (g0_18 : reg n0 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84)
    (g0_19 : reg n0 (19 : Fin 32) = BitVec.ofNat 32 0x2)
    (g0_20 : reg n0 (20 : Fin 32) = BitVec.ofNat 32 0x108)
    (g0_21 : reg n0 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4)
    (g0_26 : reg n0 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920)
    (w0_980 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length)
    (w0_c80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length)
    (w0_10e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length)
    (a0_180 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv)
    (a0_1a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv)
    (a0_1c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv)
    (a0_260 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1)
    (a0_2e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2)
    (a0_f80 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U1)
    (a0_1044 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1)
    (a0_10c4 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2)
    (p0_300 : ptF n0.mem B 0x300 = tbl2 P0 0)
    (p0_360 : ptF n0.mem B 0x360 = tbl2 P0 1)
    (p0_3c0 : ptF n0.mem B 0x3C0 = tbl2 P0 2)
    (p0_420 : ptF n0.mem B 0x420 = tbl2 P0 3)
    (p0_480 : ptF n0.mem B 0x480 = tbl2 P0 4)
    (p0_4e0 : ptF n0.mem B 0x4E0 = tbl2 P0 5)
    (p0_540 : ptF n0.mem B 0x540 = tbl2 P0 6)
    (p0_5a0 : ptF n0.mem B 0x5A0 = tbl2 P0 7)
    (p0_600 : ptF n0.mem B 0x600 = tbl2 P1 0)
    (p0_660 : ptF n0.mem B 0x660 = tbl2 P1 1)
    (p0_6c0 : ptF n0.mem B 0x6C0 = tbl2 P1 2)
    (p0_720 : ptF n0.mem B 0x720 = tbl2 P1 3)
    (p0_780 : ptF n0.mem B 0x780 = tbl2 P1 4)
    (p0_7e0 : ptF n0.mem B 0x7E0 = tbl2 P1 5)
    (p0_840 : ptF n0.mem B 0x840 = tbl2 P1 6)
    (p0_8a0 : ptF n0.mem B 0x8A0 = tbl2 P1 7)
    (mb0_900 : leN (memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U1)
    (mb0_984 : memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101)
    (mb0_c84 : memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101)
    (mb0_10e8 : memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101)
    (WN0 : P2vWnCode M0) :
    (¬ (True) ∧ P2vRet B v n0 0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem P2V n' 0x998 (reg n') ∧
        P2vCode n'.mem ∧
        P2vSaves B n'.mem v ∧
        (∀ x, P2vR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x2 ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length ∧
        reg n' a0 = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length ∧
        reg n' (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 ∧
        reg n' (19 : Fin 32) = BitVec.ofNat 32 0x2 ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x108 ∧
        reg n' (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11EC) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 ∧
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
        leN (memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11F0) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 ∧
        P2vKeepL B n0.mem n'.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4), (0x980, 0x108), (0x11EC, 0x108)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, P2vR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x89A
  obtain ⟨n1, c1, u1⟩ := s0.block p2vEcW389a E0.self p2vEcW389a_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem P2V n1 0x8AA (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock p2vEcW389a (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_8 : reg n1 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_26 : reg n1 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vEcW389a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_26, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x10C4 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vEcW389a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_26, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, p2vEcW389a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_26, s0.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk1 : P2vKeepL B n0.mem n1.mem [] := by rw [m1]; exact (P2vKeepL.refl : P2vKeepL B n0.mem n0.mem [])
  have w1_980 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m1]; exact w0_980
  have w1_c80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m1]; exact w0_c80
  have w1_10e4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m1]; exact w0_10e4
  have a1_180 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m1]; exact a0_180
  have a1_1a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m1]; exact a0_1a0
  have a1_1c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m1]; exact a0_1c0
  have a1_260 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m1]; exact a0_260
  have a1_2e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m1]; exact a0_2e0
  have a1_f80 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U1 := by rw [m1]; exact a0_f80
  have a1_1044 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m1]; exact a0_1044
  have a1_10c4 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m1]; exact a0_10c4
  have p1_300 : ptF n1.mem B 0x300 = tbl2 P0 0 := by rw [m1]; exact p0_300
  have p1_360 : ptF n1.mem B 0x360 = tbl2 P0 1 := by rw [m1]; exact p0_360
  have p1_3c0 : ptF n1.mem B 0x3C0 = tbl2 P0 2 := by rw [m1]; exact p0_3c0
  have p1_420 : ptF n1.mem B 0x420 = tbl2 P0 3 := by rw [m1]; exact p0_420
  have p1_480 : ptF n1.mem B 0x480 = tbl2 P0 4 := by rw [m1]; exact p0_480
  have p1_4e0 : ptF n1.mem B 0x4E0 = tbl2 P0 5 := by rw [m1]; exact p0_4e0
  have p1_540 : ptF n1.mem B 0x540 = tbl2 P0 6 := by rw [m1]; exact p0_540
  have p1_5a0 : ptF n1.mem B 0x5A0 = tbl2 P0 7 := by rw [m1]; exact p0_5a0
  have p1_600 : ptF n1.mem B 0x600 = tbl2 P1 0 := by rw [m1]; exact p0_600
  have p1_660 : ptF n1.mem B 0x660 = tbl2 P1 1 := by rw [m1]; exact p0_660
  have p1_6c0 : ptF n1.mem B 0x6C0 = tbl2 P1 2 := by rw [m1]; exact p0_6c0
  have p1_720 : ptF n1.mem B 0x720 = tbl2 P1 3 := by rw [m1]; exact p0_720
  have p1_780 : ptF n1.mem B 0x780 = tbl2 P1 4 := by rw [m1]; exact p0_780
  have p1_7e0 : ptF n1.mem B 0x7E0 = tbl2 P1 5 := by rw [m1]; exact p0_7e0
  have p1_840 : ptF n1.mem B 0x840 = tbl2 P1 6 := by rw [m1]; exact p0_840
  have p1_8a0 : ptF n1.mem B 0x8A0 = tbl2 P1 7 := by rw [m1]; exact p0_8a0
  have mb1_900 : leN (memBytes n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U1 := by rw [m1]; exact mb0_900
  have mb1_984 : memBytes n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m1]; exact mb0_984
  have mb1_c84 : memBytes n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m1]; exact mb0_c84
  have mb1_10e8 : memBytes n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m1]; exact mb0_10e8
  -- 0x8AA: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := p2v_mc (c := 0xF80) (d := 0x10C4) (N := 0x20) F E1 s1 p2v_at_8aa p2v_at_8ae
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
  have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P2.regs (8 : Fin 32) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [P2.regs (9 : Fin 32) (by decide), g1_9]
  have g2_18 : reg n2 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [P2.regs (18 : Fin 32) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P2.regs (19 : Fin 32) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P2.regs (20 : Fin 32) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P2.regs (21 : Fin 32) (by decide), g1_21]
  have g2_26 : reg n2 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P2.regs (26 : Fin 32) (by decide), g1_26]
  have keep_kk2 : P2vKeepL B n0.mem n2.mem [(0xF80, 0x20)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_980 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K2.w32 (by decide) (by decide)).trans w1_980
  have w2_c80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K2.w32 (by decide) (by decide)).trans w1_c80
  have w2_10e4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K2.w32 (by decide) (by decide)).trans w1_10e4
  have a2_180 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_180
  have a2_1a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K2.acc (by decide) (by decide)).trans a1_1a0
  have a2_1c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K2.acc (by decide) (by decide)).trans a1_1c0
  have a2_260 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K2.acc (by decide) (by decide)).trans a1_260
  have a2_2e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K2.acc (by decide) (by decide)).trans a1_2e0
  have a2_1044 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K2.acc (by decide) (by decide)).trans a1_1044
  have a2_10c4 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K2.acc (by decide) (by decide)).trans a1_10c4
  have p2_300 : ptF n2.mem B 0x300 = tbl2 P0 0 := (K2.pt (by decide) (by decide)).trans p1_300
  have p2_360 : ptF n2.mem B 0x360 = tbl2 P0 1 := (K2.pt (by decide) (by decide)).trans p1_360
  have p2_3c0 : ptF n2.mem B 0x3C0 = tbl2 P0 2 := (K2.pt (by decide) (by decide)).trans p1_3c0
  have p2_420 : ptF n2.mem B 0x420 = tbl2 P0 3 := (K2.pt (by decide) (by decide)).trans p1_420
  have p2_480 : ptF n2.mem B 0x480 = tbl2 P0 4 := (K2.pt (by decide) (by decide)).trans p1_480
  have p2_4e0 : ptF n2.mem B 0x4E0 = tbl2 P0 5 := (K2.pt (by decide) (by decide)).trans p1_4e0
  have p2_540 : ptF n2.mem B 0x540 = tbl2 P0 6 := (K2.pt (by decide) (by decide)).trans p1_540
  have p2_5a0 : ptF n2.mem B 0x5A0 = tbl2 P0 7 := (K2.pt (by decide) (by decide)).trans p1_5a0
  have p2_600 : ptF n2.mem B 0x600 = tbl2 P1 0 := (K2.pt (by decide) (by decide)).trans p1_600
  have p2_660 : ptF n2.mem B 0x660 = tbl2 P1 1 := (K2.pt (by decide) (by decide)).trans p1_660
  have p2_6c0 : ptF n2.mem B 0x6C0 = tbl2 P1 2 := (K2.pt (by decide) (by decide)).trans p1_6c0
  have p2_720 : ptF n2.mem B 0x720 = tbl2 P1 3 := (K2.pt (by decide) (by decide)).trans p1_720
  have p2_780 : ptF n2.mem B 0x780 = tbl2 P1 4 := (K2.pt (by decide) (by decide)).trans p1_780
  have p2_7e0 : ptF n2.mem B 0x7E0 = tbl2 P1 5 := (K2.pt (by decide) (by decide)).trans p1_7e0
  have p2_840 : ptF n2.mem B 0x840 = tbl2 P1 6 := (K2.pt (by decide) (by decide)).trans p1_840
  have p2_8a0 : ptF n2.mem B 0x8A0 = tbl2 P1 7 := (K2.pt (by decide) (by decide)).trans p1_8a0
  have mb2_900 : leN (memBytes n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U1 := by rw [K2.mb (by decide) (by decide)]; exact mb1_900
  have mb2_984 : memBytes n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K2.mb (by decide) (by decide)]; exact mb1_984
  have mb2_c84 : memBytes n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K2.mb (by decide) (by decide)]; exact mb1_c84
  have mb2_10e8 : memBytes n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K2.mb (by decide) (by decide)]; exact mb1_10e8
  have a2_f80 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (accV_S 8 fun q hq => by
    rw [show 0xF80 + q = 0xF80 + (0x0 + q) by omega, X2 (0x0 + q) (by omega),
      show 0x10C4 + (0x0 + q) = 0x10C4 + q by omega]).trans a1_10c4
  clear mb1_10e8 mb1_c84 mb1_984 mb1_900 p1_8a0 p1_840 p1_7e0 p1_780 p1_720 p1_6c0 p1_660 p1_600 p1_5a0 p1_540 p1_4e0 p1_480 p1_420 p1_3c0 p1_360 p1_300 a1_10c4 a1_1044 a1_f80 a1_2e0 a1_260 a1_1c0 a1_1a0 a1_180 w1_10e4 w1_c80 w1_980 g1_12 g1_11 g1_10 g1_26 g1_21 g1_20 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x8B2
  obtain ⟨n3, c3, u3⟩ := s2.block p2vEcW38b2 E2.self p2vEcW38b2_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem P2V n3 0x8C2 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock p2vEcW38b2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb3, runBlock_reg _ _ _ (8 : Fin 32) s2.zero (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb3, runBlock_reg _ _ _ (9 : Fin 32) s2.zero (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_26 : reg n3 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vEcW38b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_18, g2_19, g2_20, g2_21, g2_26, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g3_11 : reg n3 a1 = B + 0x21A0 + BitVec.ofNat 32 0xF80 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, p2vEcW38b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_18, g2_19, g2_20, g2_21, g2_26, s2.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk3 : P2vKeepL B n0.mem n3.mem [(0xF80, 0x20)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_980 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m3]; exact w2_980
  have w3_c80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m3]; exact w2_c80
  have w3_10e4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m3]; exact w2_10e4
  have a3_180 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m3]; exact a2_180
  have a3_1a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m3]; exact a2_1a0
  have a3_1c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m3]; exact a2_1c0
  have a3_260 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m3]; exact a2_260
  have a3_2e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m3]; exact a2_2e0
  have a3_f80 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m3]; exact a2_f80
  have a3_1044 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m3]; exact a2_1044
  have a3_10c4 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m3]; exact a2_10c4
  have p3_300 : ptF n3.mem B 0x300 = tbl2 P0 0 := by rw [m3]; exact p2_300
  have p3_360 : ptF n3.mem B 0x360 = tbl2 P0 1 := by rw [m3]; exact p2_360
  have p3_3c0 : ptF n3.mem B 0x3C0 = tbl2 P0 2 := by rw [m3]; exact p2_3c0
  have p3_420 : ptF n3.mem B 0x420 = tbl2 P0 3 := by rw [m3]; exact p2_420
  have p3_480 : ptF n3.mem B 0x480 = tbl2 P0 4 := by rw [m3]; exact p2_480
  have p3_4e0 : ptF n3.mem B 0x4E0 = tbl2 P0 5 := by rw [m3]; exact p2_4e0
  have p3_540 : ptF n3.mem B 0x540 = tbl2 P0 6 := by rw [m3]; exact p2_540
  have p3_5a0 : ptF n3.mem B 0x5A0 = tbl2 P0 7 := by rw [m3]; exact p2_5a0
  have p3_600 : ptF n3.mem B 0x600 = tbl2 P1 0 := by rw [m3]; exact p2_600
  have p3_660 : ptF n3.mem B 0x660 = tbl2 P1 1 := by rw [m3]; exact p2_660
  have p3_6c0 : ptF n3.mem B 0x6C0 = tbl2 P1 2 := by rw [m3]; exact p2_6c0
  have p3_720 : ptF n3.mem B 0x720 = tbl2 P1 3 := by rw [m3]; exact p2_720
  have p3_780 : ptF n3.mem B 0x780 = tbl2 P1 4 := by rw [m3]; exact p2_780
  have p3_7e0 : ptF n3.mem B 0x7E0 = tbl2 P1 5 := by rw [m3]; exact p2_7e0
  have p3_840 : ptF n3.mem B 0x840 = tbl2 P1 6 := by rw [m3]; exact p2_840
  have p3_8a0 : ptF n3.mem B 0x8A0 = tbl2 P1 7 := by rw [m3]; exact p2_8a0
  have mb3_900 : leN (memBytes n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U1 := by rw [m3]; exact mb2_900
  have mb3_984 : memBytes n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m3]; exact mb2_984
  have mb3_c84 : memBytes n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m3]; exact mb2_c84
  have mb3_10e8 : memBytes n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m3]; exact mb2_10e8
  clear a2_f80 mb2_10e8 mb2_c84 mb2_984 mb2_900 p2_8a0 p2_840 p2_7e0 p2_780 p2_720 p2_6c0 p2_660 p2_600 p2_5a0 p2_540 p2_4e0 p2_480 p2_420 p2_3c0 p2_360 p2_300 a2_10c4 a2_1044 a2_2e0 a2_260 a2_1c0 a2_1a0 a2_180 w2_10e4 w2_c80 w2_980 g2_26 g2_21 g2_20 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0x8C2: to_be_byte_array
  obtain ⟨n4, P4, K4, L4⟩ := p2v_tbb8 (co := 0x980) (cx := 0xF80) F E3 (WN0.p2v F fR3) s3
    p2v_at_8c2 p2v_at_8c6 (by decide) (by decide) g3_2 g3_10 g3_11
    (by decide) (by decide) (by decide)
  rw [a3_f80] at L4
  have s4 := P4.st
  have fr4 := P4.fr
  have t4 : Steps n0 n4 := t3.trans P4.steps
  have fR4 : ∀ x, P2vR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : P2vCode n4.mem := E3.fr F fr4
  have V4 : P2vSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [P4.regs sp (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P4.regs (3 : Fin 32) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P4.regs (4 : Fin 32) (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P4.regs (8 : Fin 32) (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [P4.regs (9 : Fin 32) (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [P4.regs (18 : Fin 32) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P4.regs (19 : Fin 32) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P4.regs (20 : Fin 32) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P4.regs (21 : Fin 32) (by decide), g3_21]
  have g4_26 : reg n4 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P4.regs (26 : Fin 32) (by decide), g3_26]
  have keep_kk4 : P2vKeepL B n0.mem n4.mem [(0xF80, 0x20), (0x980, 0x20)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have w4_c80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K4.w32 (by decide) (by decide)).trans w3_c80
  have w4_10e4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K4.w32 (by decide) (by decide)).trans w3_10e4
  have a4_180 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K4.acc (by decide) (by decide)).trans a3_180
  have a4_1a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K4.acc (by decide) (by decide)).trans a3_1a0
  have a4_1c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K4.acc (by decide) (by decide)).trans a3_1c0
  have a4_260 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K4.acc (by decide) (by decide)).trans a3_260
  have a4_2e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K4.acc (by decide) (by decide)).trans a3_2e0
  have a4_f80 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (K4.acc (by decide) (by decide)).trans a3_f80
  have a4_1044 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K4.acc (by decide) (by decide)).trans a3_1044
  have a4_10c4 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K4.acc (by decide) (by decide)).trans a3_10c4
  have p4_300 : ptF n4.mem B 0x300 = tbl2 P0 0 := (K4.pt (by decide) (by decide)).trans p3_300
  have p4_360 : ptF n4.mem B 0x360 = tbl2 P0 1 := (K4.pt (by decide) (by decide)).trans p3_360
  have p4_3c0 : ptF n4.mem B 0x3C0 = tbl2 P0 2 := (K4.pt (by decide) (by decide)).trans p3_3c0
  have p4_420 : ptF n4.mem B 0x420 = tbl2 P0 3 := (K4.pt (by decide) (by decide)).trans p3_420
  have p4_480 : ptF n4.mem B 0x480 = tbl2 P0 4 := (K4.pt (by decide) (by decide)).trans p3_480
  have p4_4e0 : ptF n4.mem B 0x4E0 = tbl2 P0 5 := (K4.pt (by decide) (by decide)).trans p3_4e0
  have p4_540 : ptF n4.mem B 0x540 = tbl2 P0 6 := (K4.pt (by decide) (by decide)).trans p3_540
  have p4_5a0 : ptF n4.mem B 0x5A0 = tbl2 P0 7 := (K4.pt (by decide) (by decide)).trans p3_5a0
  have p4_600 : ptF n4.mem B 0x600 = tbl2 P1 0 := (K4.pt (by decide) (by decide)).trans p3_600
  have p4_660 : ptF n4.mem B 0x660 = tbl2 P1 1 := (K4.pt (by decide) (by decide)).trans p3_660
  have p4_6c0 : ptF n4.mem B 0x6C0 = tbl2 P1 2 := (K4.pt (by decide) (by decide)).trans p3_6c0
  have p4_720 : ptF n4.mem B 0x720 = tbl2 P1 3 := (K4.pt (by decide) (by decide)).trans p3_720
  have p4_780 : ptF n4.mem B 0x780 = tbl2 P1 4 := (K4.pt (by decide) (by decide)).trans p3_780
  have p4_7e0 : ptF n4.mem B 0x7E0 = tbl2 P1 5 := (K4.pt (by decide) (by decide)).trans p3_7e0
  have p4_840 : ptF n4.mem B 0x840 = tbl2 P1 6 := (K4.pt (by decide) (by decide)).trans p3_840
  have p4_8a0 : ptF n4.mem B 0x8A0 = tbl2 P1 7 := (K4.pt (by decide) (by decide)).trans p3_8a0
  have mb4_900 : leN (memBytes n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U1 := by rw [K4.mb (by decide) (by decide)]; exact mb3_900
  have mb4_c84 : memBytes n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K4.mb (by decide) (by decide)]; exact mb3_c84
  have mb4_10e8 : memBytes n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K4.mb (by decide) (by decide)]; exact mb3_10e8
  have mb4_980 : leN (memBytes n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x20).reverse = U2 := L4
  clear mb3_10e8 mb3_c84 mb3_984 mb3_900 p3_8a0 p3_840 p3_7e0 p3_780 p3_720 p3_6c0 p3_660 p3_600 p3_5a0 p3_540 p3_4e0 p3_480 p3_420 p3_3c0 p3_360 p3_300 a3_10c4 a3_1044 a3_f80 a3_2e0 a3_260 a3_1c0 a3_1a0 a3_180 w3_10e4 w3_c80 w3_980 g3_11 g3_10 g3_26 g3_21 g3_20 g3_19 g3_18 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0x8CA
  obtain ⟨n5, c5, u5⟩ := s4.block p2vEcW38ca E4.self p2vEcW38ca_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem P2V n5 0x8D6 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock p2vEcW38ca (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vEcW38ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_26, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g5_11 : reg n5 a1 = BitVec.ofNat 32 0x20 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, p2vEcW38ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_26, s4.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk5 : P2vKeepL B n0.mem n5.mem [(0xF80, 0x20), (0x980, 0x20)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_c80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m5]; exact w4_c80
  have w5_10e4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m5]; exact w4_10e4
  have a5_180 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m5]; exact a4_180
  have a5_1a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m5]; exact a4_1a0
  have a5_1c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m5]; exact a4_1c0
  have a5_260 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m5]; exact a4_260
  have a5_2e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m5]; exact a4_2e0
  have a5_f80 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m5]; exact a4_f80
  have a5_1044 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m5]; exact a4_1044
  have a5_10c4 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m5]; exact a4_10c4
  have p5_300 : ptF n5.mem B 0x300 = tbl2 P0 0 := by rw [m5]; exact p4_300
  have p5_360 : ptF n5.mem B 0x360 = tbl2 P0 1 := by rw [m5]; exact p4_360
  have p5_3c0 : ptF n5.mem B 0x3C0 = tbl2 P0 2 := by rw [m5]; exact p4_3c0
  have p5_420 : ptF n5.mem B 0x420 = tbl2 P0 3 := by rw [m5]; exact p4_420
  have p5_480 : ptF n5.mem B 0x480 = tbl2 P0 4 := by rw [m5]; exact p4_480
  have p5_4e0 : ptF n5.mem B 0x4E0 = tbl2 P0 5 := by rw [m5]; exact p4_4e0
  have p5_540 : ptF n5.mem B 0x540 = tbl2 P0 6 := by rw [m5]; exact p4_540
  have p5_5a0 : ptF n5.mem B 0x5A0 = tbl2 P0 7 := by rw [m5]; exact p4_5a0
  have p5_600 : ptF n5.mem B 0x600 = tbl2 P1 0 := by rw [m5]; exact p4_600
  have p5_660 : ptF n5.mem B 0x660 = tbl2 P1 1 := by rw [m5]; exact p4_660
  have p5_6c0 : ptF n5.mem B 0x6C0 = tbl2 P1 2 := by rw [m5]; exact p4_6c0
  have p5_720 : ptF n5.mem B 0x720 = tbl2 P1 3 := by rw [m5]; exact p4_720
  have p5_780 : ptF n5.mem B 0x780 = tbl2 P1 4 := by rw [m5]; exact p4_780
  have p5_7e0 : ptF n5.mem B 0x7E0 = tbl2 P1 5 := by rw [m5]; exact p4_7e0
  have p5_840 : ptF n5.mem B 0x840 = tbl2 P1 6 := by rw [m5]; exact p4_840
  have p5_8a0 : ptF n5.mem B 0x8A0 = tbl2 P1 7 := by rw [m5]; exact p4_8a0
  have mb5_900 : leN (memBytes n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U1 := by rw [m5]; exact mb4_900
  have mb5_980 : leN (memBytes n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x20).reverse = U2 := by rw [m5]; exact mb4_980
  have mb5_c84 : memBytes n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m5]; exact mb4_c84
  have mb5_10e8 : memBytes n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m5]; exact mb4_10e8
  clear mb4_980 mb4_10e8 mb4_c84 mb4_900 p4_8a0 p4_840 p4_7e0 p4_780 p4_720 p4_6c0 p4_660 p4_600 p4_5a0 p4_540 p4_4e0 p4_480 p4_420 p4_3c0 p4_360 p4_300 a4_10c4 a4_1044 a4_f80 a4_2e0 a4_260 a4_1c0 a4_1a0 a4_180 w4_10e4 w4_c80 g4_26 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 s4 L4 K4 P4
  -- 0x8D6: reverse
  obtain ⟨n6, P6, K6, R6⟩ := p2v_rev (c := 0x980) (N := 0x20) F E5 (WN0.p2v F fR5) s5
    p2v_at_8d6 p2v_at_8da (by decide) (by decide) g5_10 g5_11 (by decide)
  have mbr6 := mb5_980
  have s6 := P6.st
  have fr6 := P6.fr
  have t6 : Steps n0 n6 := t5.trans P6.steps
  have fR6 : ∀ x, P2vR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : P2vCode n6.mem := E5.fr F fr6
  have V6 : P2vSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [P6.regs sp (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P6.regs (3 : Fin 32) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P6.regs (4 : Fin 32) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P6.regs (8 : Fin 32) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [P6.regs (9 : Fin 32) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [P6.regs (18 : Fin 32) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P6.regs (19 : Fin 32) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P6.regs (20 : Fin 32) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P6.regs (21 : Fin 32) (by decide), g5_21]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P6.regs (26 : Fin 32) (by decide), g5_26]
  have keep_kk6 : P2vKeepL B n0.mem n6.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_c80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K6.w32 (by decide) (by decide)).trans w5_c80
  have w6_10e4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K6.w32 (by decide) (by decide)).trans w5_10e4
  have a6_180 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K6.acc (by decide) (by decide)).trans a5_180
  have a6_1a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K6.acc (by decide) (by decide)).trans a5_1a0
  have a6_1c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K6.acc (by decide) (by decide)).trans a5_1c0
  have a6_260 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K6.acc (by decide) (by decide)).trans a5_260
  have a6_2e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K6.acc (by decide) (by decide)).trans a5_2e0
  have a6_f80 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (K6.acc (by decide) (by decide)).trans a5_f80
  have a6_1044 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K6.acc (by decide) (by decide)).trans a5_1044
  have a6_10c4 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K6.acc (by decide) (by decide)).trans a5_10c4
  have p6_300 : ptF n6.mem B 0x300 = tbl2 P0 0 := (K6.pt (by decide) (by decide)).trans p5_300
  have p6_360 : ptF n6.mem B 0x360 = tbl2 P0 1 := (K6.pt (by decide) (by decide)).trans p5_360
  have p6_3c0 : ptF n6.mem B 0x3C0 = tbl2 P0 2 := (K6.pt (by decide) (by decide)).trans p5_3c0
  have p6_420 : ptF n6.mem B 0x420 = tbl2 P0 3 := (K6.pt (by decide) (by decide)).trans p5_420
  have p6_480 : ptF n6.mem B 0x480 = tbl2 P0 4 := (K6.pt (by decide) (by decide)).trans p5_480
  have p6_4e0 : ptF n6.mem B 0x4E0 = tbl2 P0 5 := (K6.pt (by decide) (by decide)).trans p5_4e0
  have p6_540 : ptF n6.mem B 0x540 = tbl2 P0 6 := (K6.pt (by decide) (by decide)).trans p5_540
  have p6_5a0 : ptF n6.mem B 0x5A0 = tbl2 P0 7 := (K6.pt (by decide) (by decide)).trans p5_5a0
  have p6_600 : ptF n6.mem B 0x600 = tbl2 P1 0 := (K6.pt (by decide) (by decide)).trans p5_600
  have p6_660 : ptF n6.mem B 0x660 = tbl2 P1 1 := (K6.pt (by decide) (by decide)).trans p5_660
  have p6_6c0 : ptF n6.mem B 0x6C0 = tbl2 P1 2 := (K6.pt (by decide) (by decide)).trans p5_6c0
  have p6_720 : ptF n6.mem B 0x720 = tbl2 P1 3 := (K6.pt (by decide) (by decide)).trans p5_720
  have p6_780 : ptF n6.mem B 0x780 = tbl2 P1 4 := (K6.pt (by decide) (by decide)).trans p5_780
  have p6_7e0 : ptF n6.mem B 0x7E0 = tbl2 P1 5 := (K6.pt (by decide) (by decide)).trans p5_7e0
  have p6_840 : ptF n6.mem B 0x840 = tbl2 P1 6 := (K6.pt (by decide) (by decide)).trans p5_840
  have p6_8a0 : ptF n6.mem B 0x8A0 = tbl2 P1 7 := (K6.pt (by decide) (by decide)).trans p5_8a0
  have mb6_900 : leN (memBytes n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U1 := by rw [K6.mb (by decide) (by decide)]; exact mb5_900
  have mb6_c84 : memBytes n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K6.mb (by decide) (by decide)]; exact mb5_c84
  have mb6_10e8 : memBytes n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K6.mb (by decide) (by decide)]; exact mb5_10e8
  have mb6_980 : leN (memBytes n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x20) = U2 := by rw [R6]; exact mbr6
  clear mb5_10e8 mb5_c84 mb5_980 mb5_900 p5_8a0 p5_840 p5_7e0 p5_780 p5_720 p5_6c0 p5_660 p5_600 p5_5a0 p5_540 p5_4e0 p5_480 p5_420 p5_3c0 p5_360 p5_300 a5_10c4 a5_1044 a5_f80 a5_2e0 a5_260 a5_1c0 a5_1a0 a5_180 w5_10e4 w5_c80 g5_11 g5_10 g5_26 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x8DE
  obtain ⟨n7, c7, u7⟩ := s6.block p2vEcW38de E6.self p2vEcW38de_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem P2V n7 0x8F2 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock p2vEcW38de (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb7, runBlock_reg _ _ _ (20 : Fin 32) s6.zero (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcW38de, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_18, g6_19, g6_20, g6_21, g6_26, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_11 : reg n7 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcW38de, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_18, g6_19, g6_20, g6_21, g6_26, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g7_12 : reg n7 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, p2vEcW38de, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_18, g6_19, g6_20, g6_21, g6_26, s6.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk7 : P2vKeepL B n0.mem n7.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_c80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m7]; exact w6_c80
  have w7_10e4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m7]; exact w6_10e4
  have a7_180 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m7]; exact a6_180
  have a7_1a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m7]; exact a6_1a0
  have a7_1c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m7]; exact a6_1c0
  have a7_260 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m7]; exact a6_260
  have a7_2e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m7]; exact a6_2e0
  have a7_f80 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m7]; exact a6_f80
  have a7_1044 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m7]; exact a6_1044
  have a7_10c4 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m7]; exact a6_10c4
  have p7_300 : ptF n7.mem B 0x300 = tbl2 P0 0 := by rw [m7]; exact p6_300
  have p7_360 : ptF n7.mem B 0x360 = tbl2 P0 1 := by rw [m7]; exact p6_360
  have p7_3c0 : ptF n7.mem B 0x3C0 = tbl2 P0 2 := by rw [m7]; exact p6_3c0
  have p7_420 : ptF n7.mem B 0x420 = tbl2 P0 3 := by rw [m7]; exact p6_420
  have p7_480 : ptF n7.mem B 0x480 = tbl2 P0 4 := by rw [m7]; exact p6_480
  have p7_4e0 : ptF n7.mem B 0x4E0 = tbl2 P0 5 := by rw [m7]; exact p6_4e0
  have p7_540 : ptF n7.mem B 0x540 = tbl2 P0 6 := by rw [m7]; exact p6_540
  have p7_5a0 : ptF n7.mem B 0x5A0 = tbl2 P0 7 := by rw [m7]; exact p6_5a0
  have p7_600 : ptF n7.mem B 0x600 = tbl2 P1 0 := by rw [m7]; exact p6_600
  have p7_660 : ptF n7.mem B 0x660 = tbl2 P1 1 := by rw [m7]; exact p6_660
  have p7_6c0 : ptF n7.mem B 0x6C0 = tbl2 P1 2 := by rw [m7]; exact p6_6c0
  have p7_720 : ptF n7.mem B 0x720 = tbl2 P1 3 := by rw [m7]; exact p6_720
  have p7_780 : ptF n7.mem B 0x780 = tbl2 P1 4 := by rw [m7]; exact p6_780
  have p7_7e0 : ptF n7.mem B 0x7E0 = tbl2 P1 5 := by rw [m7]; exact p6_7e0
  have p7_840 : ptF n7.mem B 0x840 = tbl2 P1 6 := by rw [m7]; exact p6_840
  have p7_8a0 : ptF n7.mem B 0x8A0 = tbl2 P1 7 := by rw [m7]; exact p6_8a0
  have mb7_900 : leN (memBytes n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U1 := by rw [m7]; exact mb6_900
  have mb7_980 : leN (memBytes n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x20) = U2 := by rw [m7]; exact mb6_980
  have mb7_c84 : memBytes n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m7]; exact mb6_c84
  have mb7_10e8 : memBytes n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m7]; exact mb6_10e8
  clear mb6_980 mb6_10e8 mb6_c84 mb6_900 p6_8a0 p6_840 p6_7e0 p6_780 p6_720 p6_6c0 p6_660 p6_600 p6_5a0 p6_540 p6_4e0 p6_480 p6_420 p6_3c0 p6_360 p6_300 a6_10c4 a6_1044 a6_f80 a6_2e0 a6_260 a6_1c0 a6_1a0 a6_180 w6_10e4 w6_c80 g6_26 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 s6 mbr6 R6 K6 P6
  -- 0x8F2: memcpy
  obtain ⟨n8, P8, K8, X8⟩ := p2v_mc (c := 0x900) (d := 0x980) (N := 0x20) F E7 s7 p2v_at_8f2 p2v_at_8f6
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
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P8.regs (8 : Fin 32) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [P8.regs (9 : Fin 32) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [P8.regs (18 : Fin 32) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P8.regs (19 : Fin 32) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P8.regs (20 : Fin 32) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P8.regs (21 : Fin 32) (by decide), g7_21]
  have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P8.regs (26 : Fin 32) (by decide), g7_26]
  have keep_kk8 : P2vKeepL B n0.mem n8.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_c80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K8.w32 (by decide) (by decide)).trans w7_c80
  have w8_10e4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K8.w32 (by decide) (by decide)).trans w7_10e4
  have a8_180 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K8.acc (by decide) (by decide)).trans a7_180
  have a8_1a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K8.acc (by decide) (by decide)).trans a7_1a0
  have a8_1c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K8.acc (by decide) (by decide)).trans a7_1c0
  have a8_260 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K8.acc (by decide) (by decide)).trans a7_260
  have a8_2e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K8.acc (by decide) (by decide)).trans a7_2e0
  have a8_f80 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (K8.acc (by decide) (by decide)).trans a7_f80
  have a8_1044 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K8.acc (by decide) (by decide)).trans a7_1044
  have a8_10c4 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K8.acc (by decide) (by decide)).trans a7_10c4
  have p8_300 : ptF n8.mem B 0x300 = tbl2 P0 0 := (K8.pt (by decide) (by decide)).trans p7_300
  have p8_360 : ptF n8.mem B 0x360 = tbl2 P0 1 := (K8.pt (by decide) (by decide)).trans p7_360
  have p8_3c0 : ptF n8.mem B 0x3C0 = tbl2 P0 2 := (K8.pt (by decide) (by decide)).trans p7_3c0
  have p8_420 : ptF n8.mem B 0x420 = tbl2 P0 3 := (K8.pt (by decide) (by decide)).trans p7_420
  have p8_480 : ptF n8.mem B 0x480 = tbl2 P0 4 := (K8.pt (by decide) (by decide)).trans p7_480
  have p8_4e0 : ptF n8.mem B 0x4E0 = tbl2 P0 5 := (K8.pt (by decide) (by decide)).trans p7_4e0
  have p8_540 : ptF n8.mem B 0x540 = tbl2 P0 6 := (K8.pt (by decide) (by decide)).trans p7_540
  have p8_5a0 : ptF n8.mem B 0x5A0 = tbl2 P0 7 := (K8.pt (by decide) (by decide)).trans p7_5a0
  have p8_600 : ptF n8.mem B 0x600 = tbl2 P1 0 := (K8.pt (by decide) (by decide)).trans p7_600
  have p8_660 : ptF n8.mem B 0x660 = tbl2 P1 1 := (K8.pt (by decide) (by decide)).trans p7_660
  have p8_6c0 : ptF n8.mem B 0x6C0 = tbl2 P1 2 := (K8.pt (by decide) (by decide)).trans p7_6c0
  have p8_720 : ptF n8.mem B 0x720 = tbl2 P1 3 := (K8.pt (by decide) (by decide)).trans p7_720
  have p8_780 : ptF n8.mem B 0x780 = tbl2 P1 4 := (K8.pt (by decide) (by decide)).trans p7_780
  have p8_7e0 : ptF n8.mem B 0x7E0 = tbl2 P1 5 := (K8.pt (by decide) (by decide)).trans p7_7e0
  have p8_840 : ptF n8.mem B 0x840 = tbl2 P1 6 := (K8.pt (by decide) (by decide)).trans p7_840
  have p8_8a0 : ptF n8.mem B 0x8A0 = tbl2 P1 7 := (K8.pt (by decide) (by decide)).trans p7_8a0
  have mb8_980 : leN (memBytes n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x20) = U2 := by rw [K8.mb (by decide) (by decide)]; exact mb7_980
  have mb8_c84 : memBytes n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K8.mb (by decide) (by decide)]; exact mb7_c84
  have mb8_10e8 : memBytes n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K8.mb (by decide) (by decide)]; exact mb7_10e8
  have mb8_900 : leN (memBytes n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x900) (d := 0x980) (N := 0x20) fun q hq => by
      rw [show 0x900 + q = 0x900 + (0x0 + q) by omega, X8 (0x0 + q) (by omega),
        show 0x980 + (0x0 + q) = 0x980 + q by omega]]; exact mb7_980
  clear mb7_10e8 mb7_c84 mb7_980 mb7_900 p7_8a0 p7_840 p7_7e0 p7_780 p7_720 p7_6c0 p7_660 p7_600 p7_5a0 p7_540 p7_4e0 p7_480 p7_420 p7_3c0 p7_360 p7_300 a7_10c4 a7_1044 a7_f80 a7_2e0 a7_260 a7_1c0 a7_1a0 a7_180 w7_10e4 w7_c80 g7_12 g7_11 g7_10 g7_26 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x8FA
  obtain ⟨n9, c9, u9⟩ := s8.block p2vEcW38fa E8.self p2vEcW38fa_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem P2V n9 0x906 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock p2vEcW38fa (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vEcW38fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_18, g8_19, g8_20, g8_21, g8_26, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g9_11 : reg n9 a1 = BitVec.ofNat 32 0x101 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, p2vEcW38fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_18, g8_19, g8_20, g8_21, g8_26, s8.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk9 : P2vKeepL B n0.mem n9.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_c80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m9]; exact w8_c80
  have w9_10e4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m9]; exact w8_10e4
  have a9_180 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m9]; exact a8_180
  have a9_1a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m9]; exact a8_1a0
  have a9_1c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m9]; exact a8_1c0
  have a9_260 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m9]; exact a8_260
  have a9_2e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m9]; exact a8_2e0
  have a9_f80 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m9]; exact a8_f80
  have a9_1044 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m9]; exact a8_1044
  have a9_10c4 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m9]; exact a8_10c4
  have p9_300 : ptF n9.mem B 0x300 = tbl2 P0 0 := by rw [m9]; exact p8_300
  have p9_360 : ptF n9.mem B 0x360 = tbl2 P0 1 := by rw [m9]; exact p8_360
  have p9_3c0 : ptF n9.mem B 0x3C0 = tbl2 P0 2 := by rw [m9]; exact p8_3c0
  have p9_420 : ptF n9.mem B 0x420 = tbl2 P0 3 := by rw [m9]; exact p8_420
  have p9_480 : ptF n9.mem B 0x480 = tbl2 P0 4 := by rw [m9]; exact p8_480
  have p9_4e0 : ptF n9.mem B 0x4E0 = tbl2 P0 5 := by rw [m9]; exact p8_4e0
  have p9_540 : ptF n9.mem B 0x540 = tbl2 P0 6 := by rw [m9]; exact p8_540
  have p9_5a0 : ptF n9.mem B 0x5A0 = tbl2 P0 7 := by rw [m9]; exact p8_5a0
  have p9_600 : ptF n9.mem B 0x600 = tbl2 P1 0 := by rw [m9]; exact p8_600
  have p9_660 : ptF n9.mem B 0x660 = tbl2 P1 1 := by rw [m9]; exact p8_660
  have p9_6c0 : ptF n9.mem B 0x6C0 = tbl2 P1 2 := by rw [m9]; exact p8_6c0
  have p9_720 : ptF n9.mem B 0x720 = tbl2 P1 3 := by rw [m9]; exact p8_720
  have p9_780 : ptF n9.mem B 0x780 = tbl2 P1 4 := by rw [m9]; exact p8_780
  have p9_7e0 : ptF n9.mem B 0x7E0 = tbl2 P1 5 := by rw [m9]; exact p8_7e0
  have p9_840 : ptF n9.mem B 0x840 = tbl2 P1 6 := by rw [m9]; exact p8_840
  have p9_8a0 : ptF n9.mem B 0x8A0 = tbl2 P1 7 := by rw [m9]; exact p8_8a0
  have mb9_900 : leN (memBytes n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m9]; exact mb8_900
  have mb9_980 : leN (memBytes n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x20) = U2 := by rw [m9]; exact mb8_980
  have mb9_c84 : memBytes n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m9]; exact mb8_c84
  have mb9_10e8 : memBytes n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m9]; exact mb8_10e8
  clear mb8_900 mb8_10e8 mb8_c84 mb8_980 p8_8a0 p8_840 p8_7e0 p8_780 p8_720 p8_6c0 p8_660 p8_600 p8_5a0 p8_540 p8_4e0 p8_480 p8_420 p8_3c0 p8_360 p8_300 a8_10c4 a8_1044 a8_f80 a8_2e0 a8_260 a8_1c0 a8_1a0 a8_180 w8_10e4 w8_c80 g8_26 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 s8 X8 K8 P8
  -- 0x906: branch, not taken
  obtain ⟨n10, d10, u10⟩ := s9.notTaken E9.self 0x908 p2v_at_906
    (by decide) (by rw [g9_11, s9.zero]; decide)
  have s10 : St n10.mem P2V n10 0x908 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, P2vR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, P2vR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : P2vCode n10.mem := E9.fr F fr10
  have V10 : P2vSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u10.regs, g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [u10.regs, g9_9]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by rw [u10.regs, g9_10]
  have g10_11 : reg n10 a1 = BitVec.ofNat 32 0x101 := by rw [u10.regs, g9_11]
  have g10_18 : reg n10 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [u10.regs, g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u10.regs, g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u10.regs, g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [u10.regs, g9_21]
  have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u10.regs, g9_26]
  have keep_kk10 : P2vKeepL B n0.mem n10.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_c80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m10]; exact w9_c80
  have w10_10e4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m10]; exact w9_10e4
  have a10_180 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m10]; exact a9_180
  have a10_1a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m10]; exact a9_1a0
  have a10_1c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m10]; exact a9_1c0
  have a10_260 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m10]; exact a9_260
  have a10_2e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m10]; exact a9_2e0
  have a10_f80 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m10]; exact a9_f80
  have a10_1044 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m10]; exact a9_1044
  have a10_10c4 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m10]; exact a9_10c4
  have p10_300 : ptF n10.mem B 0x300 = tbl2 P0 0 := by rw [m10]; exact p9_300
  have p10_360 : ptF n10.mem B 0x360 = tbl2 P0 1 := by rw [m10]; exact p9_360
  have p10_3c0 : ptF n10.mem B 0x3C0 = tbl2 P0 2 := by rw [m10]; exact p9_3c0
  have p10_420 : ptF n10.mem B 0x420 = tbl2 P0 3 := by rw [m10]; exact p9_420
  have p10_480 : ptF n10.mem B 0x480 = tbl2 P0 4 := by rw [m10]; exact p9_480
  have p10_4e0 : ptF n10.mem B 0x4E0 = tbl2 P0 5 := by rw [m10]; exact p9_4e0
  have p10_540 : ptF n10.mem B 0x540 = tbl2 P0 6 := by rw [m10]; exact p9_540
  have p10_5a0 : ptF n10.mem B 0x5A0 = tbl2 P0 7 := by rw [m10]; exact p9_5a0
  have p10_600 : ptF n10.mem B 0x600 = tbl2 P1 0 := by rw [m10]; exact p9_600
  have p10_660 : ptF n10.mem B 0x660 = tbl2 P1 1 := by rw [m10]; exact p9_660
  have p10_6c0 : ptF n10.mem B 0x6C0 = tbl2 P1 2 := by rw [m10]; exact p9_6c0
  have p10_720 : ptF n10.mem B 0x720 = tbl2 P1 3 := by rw [m10]; exact p9_720
  have p10_780 : ptF n10.mem B 0x780 = tbl2 P1 4 := by rw [m10]; exact p9_780
  have p10_7e0 : ptF n10.mem B 0x7E0 = tbl2 P1 5 := by rw [m10]; exact p9_7e0
  have p10_840 : ptF n10.mem B 0x840 = tbl2 P1 6 := by rw [m10]; exact p9_840
  have p10_8a0 : ptF n10.mem B 0x8A0 = tbl2 P1 7 := by rw [m10]; exact p9_8a0
  have mb10_900 : leN (memBytes n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m10]; exact mb9_900
  have mb10_980 : leN (memBytes n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x20) = U2 := by rw [m10]; exact mb9_980
  have mb10_c84 : memBytes n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m10]; exact mb9_c84
  have mb10_10e8 : memBytes n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m10]; exact mb9_10e8
  clear mb9_10e8 mb9_c84 mb9_980 mb9_900 p9_8a0 p9_840 p9_7e0 p9_780 p9_720 p9_6c0 p9_660 p9_600 p9_5a0 p9_540 p9_4e0 p9_480 p9_420 p9_3c0 p9_360 p9_300 a9_10c4 a9_1044 a9_f80 a9_2e0 a9_260 a9_1c0 a9_1a0 a9_180 w9_10e4 w9_c80 g9_11 g9_10 g9_26 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x908: clear 0x101 bytes
  obtain ⟨n11, Z11, c11, s11', C11, rk11, z11, fz11⟩ := p2v_zloop F (c := 0x980) (N := 0x101) (by decide)
    0x101 0 (by decide) (by decide) E10.self s10 (by rw [g10_10]; try rfl) g10_11
  have s11 : St n11.mem P2V n11 0x912 (reg n11) := ⟨s11'.pc, rfl, fun _ => rfl⟩
  have fr11 : ∀ x, P2vR B x → n11.mem x = n10.mem x := fun x hx => by
    rw [s11'.mem]; exact fz11 x (p2vR_hi (c := 0x980 + 0) hx (by decide))
  have K11 : P2vKeep B n10.mem n11.mem 0x980 0x101 := fun e he hh => by
    rw [s11'.mem]; exact fz11 _ (sepS (B + 0x21A0) (c := 0x980 + 0) (n := 0x101) (d := e) (k := 1) (by omega) (by omega) (by omega))
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, P2vR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : P2vCode n11.mem := E10.fr F fr11
  have V11 : P2vSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rk11 sp (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk11 (3 : Fin 32) (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk11 (4 : Fin 32) (by decide) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk11 (8 : Fin 32) (by decide) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1064 := by rw [rk11 (9 : Fin 32) (by decide) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [rk11 (18 : Fin 32) (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rk11 (19 : Fin 32) (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [rk11 (20 : Fin 32) (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [rk11 (21 : Fin 32) (by decide) (by decide), g10_21]
  have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rk11 (26 : Fin 32) (by decide) (by decide), g10_26]
  have keep_kk11 : P2vKeepL B n0.mem n11.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_c80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K11.w32 (by decide) (by decide)).trans w10_c80
  have w11_10e4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K11.w32 (by decide) (by decide)).trans w10_10e4
  have a11_180 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K11.acc (by decide) (by decide)).trans a10_180
  have a11_1a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K11.acc (by decide) (by decide)).trans a10_1a0
  have a11_1c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K11.acc (by decide) (by decide)).trans a10_1c0
  have a11_260 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K11.acc (by decide) (by decide)).trans a10_260
  have a11_2e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K11.acc (by decide) (by decide)).trans a10_2e0
  have a11_f80 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (K11.acc (by decide) (by decide)).trans a10_f80
  have a11_1044 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K11.acc (by decide) (by decide)).trans a10_1044
  have a11_10c4 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K11.acc (by decide) (by decide)).trans a10_10c4
  have p11_300 : ptF n11.mem B 0x300 = tbl2 P0 0 := (K11.pt (by decide) (by decide)).trans p10_300
  have p11_360 : ptF n11.mem B 0x360 = tbl2 P0 1 := (K11.pt (by decide) (by decide)).trans p10_360
  have p11_3c0 : ptF n11.mem B 0x3C0 = tbl2 P0 2 := (K11.pt (by decide) (by decide)).trans p10_3c0
  have p11_420 : ptF n11.mem B 0x420 = tbl2 P0 3 := (K11.pt (by decide) (by decide)).trans p10_420
  have p11_480 : ptF n11.mem B 0x480 = tbl2 P0 4 := (K11.pt (by decide) (by decide)).trans p10_480
  have p11_4e0 : ptF n11.mem B 0x4E0 = tbl2 P0 5 := (K11.pt (by decide) (by decide)).trans p10_4e0
  have p11_540 : ptF n11.mem B 0x540 = tbl2 P0 6 := (K11.pt (by decide) (by decide)).trans p10_540
  have p11_5a0 : ptF n11.mem B 0x5A0 = tbl2 P0 7 := (K11.pt (by decide) (by decide)).trans p10_5a0
  have p11_600 : ptF n11.mem B 0x600 = tbl2 P1 0 := (K11.pt (by decide) (by decide)).trans p10_600
  have p11_660 : ptF n11.mem B 0x660 = tbl2 P1 1 := (K11.pt (by decide) (by decide)).trans p10_660
  have p11_6c0 : ptF n11.mem B 0x6C0 = tbl2 P1 2 := (K11.pt (by decide) (by decide)).trans p10_6c0
  have p11_720 : ptF n11.mem B 0x720 = tbl2 P1 3 := (K11.pt (by decide) (by decide)).trans p10_720
  have p11_780 : ptF n11.mem B 0x780 = tbl2 P1 4 := (K11.pt (by decide) (by decide)).trans p10_780
  have p11_7e0 : ptF n11.mem B 0x7E0 = tbl2 P1 5 := (K11.pt (by decide) (by decide)).trans p10_7e0
  have p11_840 : ptF n11.mem B 0x840 = tbl2 P1 6 := (K11.pt (by decide) (by decide)).trans p10_840
  have p11_8a0 : ptF n11.mem B 0x8A0 = tbl2 P1 7 := (K11.pt (by decide) (by decide)).trans p10_8a0
  have mb11_900 : leN (memBytes n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [K11.mb (by decide) (by decide)]; exact mb10_900
  have mb11_c84 : memBytes n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K11.mb (by decide) (by decide)]; exact mb10_c84
  have mb11_10e8 : memBytes n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K11.mb (by decide) (by decide)]; exact mb10_10e8
  have mb11_980 : memBytes n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x101 = List.replicate 0x101 0 :=
    Pv.memBytes_zero fun j hj => by rw [s11'.mem]; have := z11 j hj; rwa [Nat.add_zero] at this
  clear mb10_10e8 mb10_c84 mb10_980 mb10_900 p10_8a0 p10_840 p10_7e0 p10_780 p10_720 p10_6c0 p10_660 p10_600 p10_5a0 p10_540 p10_4e0 p10_480 p10_420 p10_3c0 p10_360 p10_300 a10_10c4 a10_1044 a10_f80 a10_2e0 a10_260 a10_1c0 a10_1a0 a10_180 w10_10e4 w10_c80 g10_26 g10_21 g10_20 g10_19 g10_18 g10_11 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x912
  obtain ⟨n12, c12, u12⟩ := s11.block p2vEcW3912 E11.self p2vEcW3912_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem P2V n12 0x924 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock p2vEcW3912 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_18 : reg n12 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_9 : reg n12 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vEcW3912, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_18, g11_19, g11_20, g11_21, g11_26, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vEcW3912, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_18, g11_19, g11_20, g11_21, g11_26, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vEcW3912, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_18, g11_19, g11_20, g11_21, g11_26, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g12_12 : reg n12 a2 = BitVec.ofNat 32 0x101 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, p2vEcW3912, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_18, g11_19, g11_20, g11_21, g11_26, s11.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk12 : P2vKeepL B n0.mem n12.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_c80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m12]; exact w11_c80
  have w12_10e4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m12]; exact w11_10e4
  have a12_180 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m12]; exact a11_180
  have a12_1a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m12]; exact a11_1a0
  have a12_1c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m12]; exact a11_1c0
  have a12_260 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m12]; exact a11_260
  have a12_2e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m12]; exact a11_2e0
  have a12_f80 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m12]; exact a11_f80
  have a12_1044 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m12]; exact a11_1044
  have a12_10c4 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m12]; exact a11_10c4
  have p12_300 : ptF n12.mem B 0x300 = tbl2 P0 0 := by rw [m12]; exact p11_300
  have p12_360 : ptF n12.mem B 0x360 = tbl2 P0 1 := by rw [m12]; exact p11_360
  have p12_3c0 : ptF n12.mem B 0x3C0 = tbl2 P0 2 := by rw [m12]; exact p11_3c0
  have p12_420 : ptF n12.mem B 0x420 = tbl2 P0 3 := by rw [m12]; exact p11_420
  have p12_480 : ptF n12.mem B 0x480 = tbl2 P0 4 := by rw [m12]; exact p11_480
  have p12_4e0 : ptF n12.mem B 0x4E0 = tbl2 P0 5 := by rw [m12]; exact p11_4e0
  have p12_540 : ptF n12.mem B 0x540 = tbl2 P0 6 := by rw [m12]; exact p11_540
  have p12_5a0 : ptF n12.mem B 0x5A0 = tbl2 P0 7 := by rw [m12]; exact p11_5a0
  have p12_600 : ptF n12.mem B 0x600 = tbl2 P1 0 := by rw [m12]; exact p11_600
  have p12_660 : ptF n12.mem B 0x660 = tbl2 P1 1 := by rw [m12]; exact p11_660
  have p12_6c0 : ptF n12.mem B 0x6C0 = tbl2 P1 2 := by rw [m12]; exact p11_6c0
  have p12_720 : ptF n12.mem B 0x720 = tbl2 P1 3 := by rw [m12]; exact p11_720
  have p12_780 : ptF n12.mem B 0x780 = tbl2 P1 4 := by rw [m12]; exact p11_780
  have p12_7e0 : ptF n12.mem B 0x7E0 = tbl2 P1 5 := by rw [m12]; exact p11_7e0
  have p12_840 : ptF n12.mem B 0x840 = tbl2 P1 6 := by rw [m12]; exact p11_840
  have p12_8a0 : ptF n12.mem B 0x8A0 = tbl2 P1 7 := by rw [m12]; exact p11_8a0
  have mb12_900 : leN (memBytes n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m12]; exact mb11_900
  have mb12_980 : memBytes n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x101 = List.replicate 0x101 0 := by rw [m12]; exact mb11_980
  have mb12_c84 : memBytes n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m12]; exact mb11_c84
  have mb12_10e8 : memBytes n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m12]; exact mb11_10e8
  clear mb11_980 mb11_10e8 mb11_c84 mb11_900 p11_8a0 p11_840 p11_7e0 p11_780 p11_720 p11_6c0 p11_660 p11_600 p11_5a0 p11_540 p11_4e0 p11_480 p11_420 p11_3c0 p11_360 p11_300 a11_10c4 a11_1044 a11_f80 a11_2e0 a11_260 a11_1c0 a11_1a0 a11_180 w11_10e4 w11_c80 g11_26 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 K11 fr11 s11 fz11 z11 rk11 C11 s11' c11 Z11
  -- 0x924: memcpy
  obtain ⟨n13, P13, K13, X13⟩ := p2v_mc (c := 0xC84) (d := 0x980) (N := 0x101) F E12 s12 p2v_at_924 p2v_at_928
    (by decide) (by decide) g12_2 g12_10 g12_11 g12_12
    (by decide) (by decide) (by decide)
  have s13 := P13.st
  have fr13 := P13.fr
  have t13 : Steps n0 n13 := t12.trans P13.steps
  have fR13 : ∀ x, P2vR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : P2vCode n13.mem := E12.fr F fr13
  have V13 : P2vSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [P13.regs sp (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P13.regs (3 : Fin 32) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P13.regs (4 : Fin 32) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P13.regs (8 : Fin 32) (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P13.regs (9 : Fin 32) (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [P13.regs (18 : Fin 32) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P13.regs (19 : Fin 32) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P13.regs (20 : Fin 32) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P13.regs (21 : Fin 32) (by decide), g12_21]
  have g13_26 : reg n13 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P13.regs (26 : Fin 32) (by decide), g12_26]
  have keep_kk13 : P2vKeepL B n0.mem n13.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_c80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K13.w32 (by decide) (by decide)).trans w12_c80
  have w13_10e4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K13.w32 (by decide) (by decide)).trans w12_10e4
  have a13_180 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K13.acc (by decide) (by decide)).trans a12_180
  have a13_1a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K13.acc (by decide) (by decide)).trans a12_1a0
  have a13_1c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K13.acc (by decide) (by decide)).trans a12_1c0
  have a13_260 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K13.acc (by decide) (by decide)).trans a12_260
  have a13_2e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K13.acc (by decide) (by decide)).trans a12_2e0
  have a13_f80 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (K13.acc (by decide) (by decide)).trans a12_f80
  have a13_1044 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K13.acc (by decide) (by decide)).trans a12_1044
  have a13_10c4 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K13.acc (by decide) (by decide)).trans a12_10c4
  have p13_300 : ptF n13.mem B 0x300 = tbl2 P0 0 := (K13.pt (by decide) (by decide)).trans p12_300
  have p13_360 : ptF n13.mem B 0x360 = tbl2 P0 1 := (K13.pt (by decide) (by decide)).trans p12_360
  have p13_3c0 : ptF n13.mem B 0x3C0 = tbl2 P0 2 := (K13.pt (by decide) (by decide)).trans p12_3c0
  have p13_420 : ptF n13.mem B 0x420 = tbl2 P0 3 := (K13.pt (by decide) (by decide)).trans p12_420
  have p13_480 : ptF n13.mem B 0x480 = tbl2 P0 4 := (K13.pt (by decide) (by decide)).trans p12_480
  have p13_4e0 : ptF n13.mem B 0x4E0 = tbl2 P0 5 := (K13.pt (by decide) (by decide)).trans p12_4e0
  have p13_540 : ptF n13.mem B 0x540 = tbl2 P0 6 := (K13.pt (by decide) (by decide)).trans p12_540
  have p13_5a0 : ptF n13.mem B 0x5A0 = tbl2 P0 7 := (K13.pt (by decide) (by decide)).trans p12_5a0
  have p13_600 : ptF n13.mem B 0x600 = tbl2 P1 0 := (K13.pt (by decide) (by decide)).trans p12_600
  have p13_660 : ptF n13.mem B 0x660 = tbl2 P1 1 := (K13.pt (by decide) (by decide)).trans p12_660
  have p13_6c0 : ptF n13.mem B 0x6C0 = tbl2 P1 2 := (K13.pt (by decide) (by decide)).trans p12_6c0
  have p13_720 : ptF n13.mem B 0x720 = tbl2 P1 3 := (K13.pt (by decide) (by decide)).trans p12_720
  have p13_780 : ptF n13.mem B 0x780 = tbl2 P1 4 := (K13.pt (by decide) (by decide)).trans p12_780
  have p13_7e0 : ptF n13.mem B 0x7E0 = tbl2 P1 5 := (K13.pt (by decide) (by decide)).trans p12_7e0
  have p13_840 : ptF n13.mem B 0x840 = tbl2 P1 6 := (K13.pt (by decide) (by decide)).trans p12_840
  have p13_8a0 : ptF n13.mem B 0x8A0 = tbl2 P1 7 := (K13.pt (by decide) (by decide)).trans p12_8a0
  have mb13_900 : leN (memBytes n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [K13.mb (by decide) (by decide)]; exact mb12_900
  have mb13_980 : memBytes n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x101 = List.replicate 0x101 0 := by rw [K13.mb (by decide) (by decide)]; exact mb12_980
  have mb13_10e8 : memBytes n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K13.mb (by decide) (by decide)]; exact mb12_10e8
  have mb13_c84 : memBytes n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = List.replicate 0x101 0 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0xC84) (d := 0x980) (N := 0x101) fun q hq => by
      rw [show 0xC84 + q = 0xC84 + (0x0 + q) by omega, X13 (0x0 + q) (by omega),
        show 0x980 + (0x0 + q) = 0x980 + q by omega]]; exact mb12_980
  clear mb12_10e8 mb12_c84 mb12_980 mb12_900 p12_8a0 p12_840 p12_7e0 p12_780 p12_720 p12_6c0 p12_660 p12_600 p12_5a0 p12_540 p12_4e0 p12_480 p12_420 p12_3c0 p12_360 p12_300 a12_10c4 a12_1044 a12_f80 a12_2e0 a12_260 a12_1c0 a12_1a0 a12_180 w12_10e4 w12_c80 g12_12 g12_11 g12_10 g12_9 g12_26 g12_21 g12_20 g12_19 g12_18 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x92C
  obtain ⟨n14, c14, u14⟩ := s13.block p2vEcW392c E13.self p2vEcW392c_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem P2V n14 0x942 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock p2vEcW392c (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
  have g14_26 : reg n14 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vEcW392c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_26, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 0x101 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vEcW392c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_26, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_12 : reg n14 a2 = B + 0x21A0 + BitVec.ofNat 32 0x900 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vEcW392c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_26, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_13 : reg n14 a3 = BitVec.ofNat 32 0x20 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vEcW392c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_26, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g14_14 : reg n14 a4 = BitVec.ofNat 32 0x100 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, p2vEcW392c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_26, s13.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk14 : P2vKeepL B n0.mem n14.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_c80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m14]; exact w13_c80
  have w14_10e4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m14]; exact w13_10e4
  have a14_180 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m14]; exact a13_180
  have a14_1a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m14]; exact a13_1a0
  have a14_1c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m14]; exact a13_1c0
  have a14_260 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m14]; exact a13_260
  have a14_2e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m14]; exact a13_2e0
  have a14_f80 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m14]; exact a13_f80
  have a14_1044 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m14]; exact a13_1044
  have a14_10c4 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m14]; exact a13_10c4
  have p14_300 : ptF n14.mem B 0x300 = tbl2 P0 0 := by rw [m14]; exact p13_300
  have p14_360 : ptF n14.mem B 0x360 = tbl2 P0 1 := by rw [m14]; exact p13_360
  have p14_3c0 : ptF n14.mem B 0x3C0 = tbl2 P0 2 := by rw [m14]; exact p13_3c0
  have p14_420 : ptF n14.mem B 0x420 = tbl2 P0 3 := by rw [m14]; exact p13_420
  have p14_480 : ptF n14.mem B 0x480 = tbl2 P0 4 := by rw [m14]; exact p13_480
  have p14_4e0 : ptF n14.mem B 0x4E0 = tbl2 P0 5 := by rw [m14]; exact p13_4e0
  have p14_540 : ptF n14.mem B 0x540 = tbl2 P0 6 := by rw [m14]; exact p13_540
  have p14_5a0 : ptF n14.mem B 0x5A0 = tbl2 P0 7 := by rw [m14]; exact p13_5a0
  have p14_600 : ptF n14.mem B 0x600 = tbl2 P1 0 := by rw [m14]; exact p13_600
  have p14_660 : ptF n14.mem B 0x660 = tbl2 P1 1 := by rw [m14]; exact p13_660
  have p14_6c0 : ptF n14.mem B 0x6C0 = tbl2 P1 2 := by rw [m14]; exact p13_6c0
  have p14_720 : ptF n14.mem B 0x720 = tbl2 P1 3 := by rw [m14]; exact p13_720
  have p14_780 : ptF n14.mem B 0x780 = tbl2 P1 4 := by rw [m14]; exact p13_780
  have p14_7e0 : ptF n14.mem B 0x7E0 = tbl2 P1 5 := by rw [m14]; exact p13_7e0
  have p14_840 : ptF n14.mem B 0x840 = tbl2 P1 6 := by rw [m14]; exact p13_840
  have p14_8a0 : ptF n14.mem B 0x8A0 = tbl2 P1 7 := by rw [m14]; exact p13_8a0
  have mb14_900 : leN (memBytes n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m14]; exact mb13_900
  have mb14_980 : memBytes n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x101 = List.replicate 0x101 0 := by rw [m14]; exact mb13_980
  have mb14_c84 : memBytes n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = List.replicate 0x101 0 := by rw [m14]; exact mb13_c84
  have mb14_10e8 : memBytes n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m14]; exact mb13_10e8
  clear mb13_c84 mb13_10e8 mb13_980 mb13_900 p13_8a0 p13_840 p13_7e0 p13_780 p13_720 p13_6c0 p13_660 p13_600 p13_5a0 p13_540 p13_4e0 p13_480 p13_420 p13_3c0 p13_360 p13_300 a13_10c4 a13_1044 a13_f80 a13_2e0 a13_260 a13_1c0 a13_1a0 a13_180 w13_10e4 w13_c80 g13_26 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 s13 X13 K13 P13
  -- 0x942: wnaf_form
  obtain ⟨n15, P15, K15, A15, D15, H15⟩ := p2v_wf (cw := 0xC84) (cc := 0x900) F E14 (WN0.p2v F fR14) s14
    p2v_at_942 p2v_at_946 (by decide) (by decide) g14_2 g14_10 g14_11
    g14_12 g14_13 g14_14 (by decide) (by decide) (by decide) mb14_900 mb14_c84
  have s15 := P15.st
  have fr15 := P15.fr
  have t15 : Steps n0 n15 := t14.trans P15.steps
  have fR15 : ∀ x, P2vR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : P2vCode n15.mem := E14.fr F fr15
  have V15 : P2vSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [P15.regs sp (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P15.regs (3 : Fin 32) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P15.regs (4 : Fin 32) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P15.regs (8 : Fin 32) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P15.regs (9 : Fin 32) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [P15.regs (18 : Fin 32) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P15.regs (19 : Fin 32) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P15.regs (20 : Fin 32) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P15.regs (21 : Fin 32) (by decide), g14_21]
  have g15_26 : reg n15 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P15.regs (26 : Fin 32) (by decide), g14_26]
  have keep_kk15 : P2vKeepL B n0.mem n15.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_c80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K15.w32 (by decide) (by decide)).trans w14_c80
  have w15_10e4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K15.w32 (by decide) (by decide)).trans w14_10e4
  have a15_180 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K15.acc (by decide) (by decide)).trans a14_180
  have a15_1a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K15.acc (by decide) (by decide)).trans a14_1a0
  have a15_1c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K15.acc (by decide) (by decide)).trans a14_1c0
  have a15_260 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K15.acc (by decide) (by decide)).trans a14_260
  have a15_2e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K15.acc (by decide) (by decide)).trans a14_2e0
  have a15_f80 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (K15.acc (by decide) (by decide)).trans a14_f80
  have a15_1044 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K15.acc (by decide) (by decide)).trans a14_1044
  have a15_10c4 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K15.acc (by decide) (by decide)).trans a14_10c4
  have p15_300 : ptF n15.mem B 0x300 = tbl2 P0 0 := (K15.pt (by decide) (by decide)).trans p14_300
  have p15_360 : ptF n15.mem B 0x360 = tbl2 P0 1 := (K15.pt (by decide) (by decide)).trans p14_360
  have p15_3c0 : ptF n15.mem B 0x3C0 = tbl2 P0 2 := (K15.pt (by decide) (by decide)).trans p14_3c0
  have p15_420 : ptF n15.mem B 0x420 = tbl2 P0 3 := (K15.pt (by decide) (by decide)).trans p14_420
  have p15_480 : ptF n15.mem B 0x480 = tbl2 P0 4 := (K15.pt (by decide) (by decide)).trans p14_480
  have p15_4e0 : ptF n15.mem B 0x4E0 = tbl2 P0 5 := (K15.pt (by decide) (by decide)).trans p14_4e0
  have p15_540 : ptF n15.mem B 0x540 = tbl2 P0 6 := (K15.pt (by decide) (by decide)).trans p14_540
  have p15_5a0 : ptF n15.mem B 0x5A0 = tbl2 P0 7 := (K15.pt (by decide) (by decide)).trans p14_5a0
  have p15_600 : ptF n15.mem B 0x600 = tbl2 P1 0 := (K15.pt (by decide) (by decide)).trans p14_600
  have p15_660 : ptF n15.mem B 0x660 = tbl2 P1 1 := (K15.pt (by decide) (by decide)).trans p14_660
  have p15_6c0 : ptF n15.mem B 0x6C0 = tbl2 P1 2 := (K15.pt (by decide) (by decide)).trans p14_6c0
  have p15_720 : ptF n15.mem B 0x720 = tbl2 P1 3 := (K15.pt (by decide) (by decide)).trans p14_720
  have p15_780 : ptF n15.mem B 0x780 = tbl2 P1 4 := (K15.pt (by decide) (by decide)).trans p14_780
  have p15_7e0 : ptF n15.mem B 0x7E0 = tbl2 P1 5 := (K15.pt (by decide) (by decide)).trans p14_7e0
  have p15_840 : ptF n15.mem B 0x840 = tbl2 P1 6 := (K15.pt (by decide) (by decide)).trans p14_840
  have p15_8a0 : ptF n15.mem B 0x8A0 = tbl2 P1 7 := (K15.pt (by decide) (by decide)).trans p14_8a0
  have mb15_900 : leN (memBytes n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [K15.mb (by decide) (by decide)]; exact mb14_900
  have mb15_980 : memBytes n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x101 = List.replicate 0x101 0 := by rw [K15.mb (by decide) (by decide)]; exact mb14_980
  have mb15_10e8 : memBytes n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K15.mb (by decide) (by decide)]; exact mb14_10e8
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := A15
  have mb15_c84 : memBytes n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := D15
  clear mb14_10e8 mb14_c84 mb14_980 mb14_900 p14_8a0 p14_840 p14_7e0 p14_780 p14_720 p14_6c0 p14_660 p14_600 p14_5a0 p14_540 p14_4e0 p14_480 p14_420 p14_3c0 p14_360 p14_300 a14_10c4 a14_1044 a14_f80 a14_2e0 a14_260 a14_1c0 a14_1a0 a14_180 w14_10e4 w14_c80 g14_14 g14_13 g14_12 g14_11 g14_10 g14_26 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0x94A: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := p2v_sw F E15 s15 p2v_at_94a (off' := 0x94E) (c := 0xC80)
    (by decide) (by rw [g15_26]; p2v_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, P2vR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : P2vCode n16.mem := E15.fr F fr16
  have V16 : P2vSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg16 (8 : Fin 32), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [rg16 a0, g15_10]
  have g16_18 : reg n16 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [rg16 (20 : Fin 32), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [rg16 (26 : Fin 32), g15_26]
  have keep_kk16 : P2vKeepL B n0.mem n16.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_10e4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K16.w32 (by decide) (by decide)).trans w15_10e4
  have w16_c80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [W16, g15_10]
  have a16_180 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K16.acc (by decide) (by decide)).trans a15_180
  have a16_1a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K16.acc (by decide) (by decide)).trans a15_1a0
  have a16_1c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K16.acc (by decide) (by decide)).trans a15_1c0
  have a16_260 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K16.acc (by decide) (by decide)).trans a15_260
  have a16_2e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K16.acc (by decide) (by decide)).trans a15_2e0
  have a16_f80 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (K16.acc (by decide) (by decide)).trans a15_f80
  have a16_1044 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K16.acc (by decide) (by decide)).trans a15_1044
  have a16_10c4 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K16.acc (by decide) (by decide)).trans a15_10c4
  have p16_300 : ptF n16.mem B 0x300 = tbl2 P0 0 := (K16.pt (by decide) (by decide)).trans p15_300
  have p16_360 : ptF n16.mem B 0x360 = tbl2 P0 1 := (K16.pt (by decide) (by decide)).trans p15_360
  have p16_3c0 : ptF n16.mem B 0x3C0 = tbl2 P0 2 := (K16.pt (by decide) (by decide)).trans p15_3c0
  have p16_420 : ptF n16.mem B 0x420 = tbl2 P0 3 := (K16.pt (by decide) (by decide)).trans p15_420
  have p16_480 : ptF n16.mem B 0x480 = tbl2 P0 4 := (K16.pt (by decide) (by decide)).trans p15_480
  have p16_4e0 : ptF n16.mem B 0x4E0 = tbl2 P0 5 := (K16.pt (by decide) (by decide)).trans p15_4e0
  have p16_540 : ptF n16.mem B 0x540 = tbl2 P0 6 := (K16.pt (by decide) (by decide)).trans p15_540
  have p16_5a0 : ptF n16.mem B 0x5A0 = tbl2 P0 7 := (K16.pt (by decide) (by decide)).trans p15_5a0
  have p16_600 : ptF n16.mem B 0x600 = tbl2 P1 0 := (K16.pt (by decide) (by decide)).trans p15_600
  have p16_660 : ptF n16.mem B 0x660 = tbl2 P1 1 := (K16.pt (by decide) (by decide)).trans p15_660
  have p16_6c0 : ptF n16.mem B 0x6C0 = tbl2 P1 2 := (K16.pt (by decide) (by decide)).trans p15_6c0
  have p16_720 : ptF n16.mem B 0x720 = tbl2 P1 3 := (K16.pt (by decide) (by decide)).trans p15_720
  have p16_780 : ptF n16.mem B 0x780 = tbl2 P1 4 := (K16.pt (by decide) (by decide)).trans p15_780
  have p16_7e0 : ptF n16.mem B 0x7E0 = tbl2 P1 5 := (K16.pt (by decide) (by decide)).trans p15_7e0
  have p16_840 : ptF n16.mem B 0x840 = tbl2 P1 6 := (K16.pt (by decide) (by decide)).trans p15_840
  have p16_8a0 : ptF n16.mem B 0x8A0 = tbl2 P1 7 := (K16.pt (by decide) (by decide)).trans p15_8a0
  have mb16_900 : leN (memBytes n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [K16.mb (by decide) (by decide)]; exact mb15_900
  have mb16_980 : memBytes n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x101 = List.replicate 0x101 0 := by rw [K16.mb (by decide) (by decide)]; exact mb15_980
  have mb16_c84 : memBytes n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K16.mb (by decide) (by decide)]; exact mb15_c84
  have mb16_10e8 : memBytes n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K16.mb (by decide) (by decide)]; exact mb15_10e8
  clear mb15_c84 g15_10 mb15_10e8 mb15_980 mb15_900 p15_8a0 p15_840 p15_7e0 p15_780 p15_720 p15_6c0 p15_660 p15_600 p15_5a0 p15_540 p15_4e0 p15_480 p15_420 p15_3c0 p15_360 p15_300 a15_10c4 a15_1044 a15_f80 a15_2e0 a15_260 a15_1c0 a15_1a0 a15_180 w15_10e4 w15_c80 g15_26 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 s15 H15 D15 A15 K15 P15
  -- 0x94E
  obtain ⟨n17, c17, u17⟩ := s16.block p2vEcW394e E16.self p2vEcW394e_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem P2V n17 0x962 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock p2vEcW394e (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcW394e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_18, g16_19, g16_20, g16_21, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0xC80 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcW394e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_18, g16_19, g16_20, g16_21, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 0x108 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, p2vEcW394e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_18, g16_19, g16_20, g16_21, g16_26, s16.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk17 : P2vKeepL B n0.mem n17.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_c80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m17]; exact w16_c80
  have w17_10e4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m17]; exact w16_10e4
  have a17_180 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m17]; exact a16_180
  have a17_1a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m17]; exact a16_1a0
  have a17_1c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m17]; exact a16_1c0
  have a17_260 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m17]; exact a16_260
  have a17_2e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m17]; exact a16_2e0
  have a17_f80 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m17]; exact a16_f80
  have a17_1044 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m17]; exact a16_1044
  have a17_10c4 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m17]; exact a16_10c4
  have p17_300 : ptF n17.mem B 0x300 = tbl2 P0 0 := by rw [m17]; exact p16_300
  have p17_360 : ptF n17.mem B 0x360 = tbl2 P0 1 := by rw [m17]; exact p16_360
  have p17_3c0 : ptF n17.mem B 0x3C0 = tbl2 P0 2 := by rw [m17]; exact p16_3c0
  have p17_420 : ptF n17.mem B 0x420 = tbl2 P0 3 := by rw [m17]; exact p16_420
  have p17_480 : ptF n17.mem B 0x480 = tbl2 P0 4 := by rw [m17]; exact p16_480
  have p17_4e0 : ptF n17.mem B 0x4E0 = tbl2 P0 5 := by rw [m17]; exact p16_4e0
  have p17_540 : ptF n17.mem B 0x540 = tbl2 P0 6 := by rw [m17]; exact p16_540
  have p17_5a0 : ptF n17.mem B 0x5A0 = tbl2 P0 7 := by rw [m17]; exact p16_5a0
  have p17_600 : ptF n17.mem B 0x600 = tbl2 P1 0 := by rw [m17]; exact p16_600
  have p17_660 : ptF n17.mem B 0x660 = tbl2 P1 1 := by rw [m17]; exact p16_660
  have p17_6c0 : ptF n17.mem B 0x6C0 = tbl2 P1 2 := by rw [m17]; exact p16_6c0
  have p17_720 : ptF n17.mem B 0x720 = tbl2 P1 3 := by rw [m17]; exact p16_720
  have p17_780 : ptF n17.mem B 0x780 = tbl2 P1 4 := by rw [m17]; exact p16_780
  have p17_7e0 : ptF n17.mem B 0x7E0 = tbl2 P1 5 := by rw [m17]; exact p16_7e0
  have p17_840 : ptF n17.mem B 0x840 = tbl2 P1 6 := by rw [m17]; exact p16_840
  have p17_8a0 : ptF n17.mem B 0x8A0 = tbl2 P1 7 := by rw [m17]; exact p16_8a0
  have mb17_900 : leN (memBytes n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m17]; exact mb16_900
  have mb17_980 : memBytes n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 0x101 = List.replicate 0x101 0 := by rw [m17]; exact mb16_980
  have mb17_c84 : memBytes n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m17]; exact mb16_c84
  have mb17_10e8 : memBytes n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m17]; exact mb16_10e8
  clear mb16_10e8 mb16_c84 mb16_980 mb16_900 p16_8a0 p16_840 p16_7e0 p16_780 p16_720 p16_6c0 p16_660 p16_600 p16_5a0 p16_540 p16_4e0 p16_480 p16_420 p16_3c0 p16_360 p16_300 a16_10c4 a16_1044 a16_f80 a16_2e0 a16_260 a16_1c0 a16_1a0 a16_180 w16_c80 w16_10e4 g16_26 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x962: memcpy
  obtain ⟨n18, P18, K18, X18⟩ := p2v_mc (c := 0x980) (d := 0xC80) (N := 0x108) F E17 s17 p2v_at_962 p2v_at_966
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
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P18.regs (8 : Fin 32) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P18.regs (9 : Fin 32) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [P18.regs (18 : Fin 32) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P18.regs (19 : Fin 32) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P18.regs (20 : Fin 32) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P18.regs (21 : Fin 32) (by decide), g17_21]
  have g18_26 : reg n18 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P18.regs (26 : Fin 32) (by decide), g17_26]
  have keep_kk18 : P2vKeepL B n0.mem n18.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4), (0x980, 0x108)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_c80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := (K18.w32 (by decide) (by decide)).trans w17_c80
  have w18_10e4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K18.w32 (by decide) (by decide)).trans w17_10e4
  have w18_980 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by
    rw [← w17_c80]
    exact ld_cp fun q hq => by
      have := X18 (0x0 + q) (by omega)
      rwa [show 0x980 + (0x0 + q) = 0x980 + q by omega,
        show 0xC80 + (0x0 + q) = 0xC80 + q by omega] at this
  have a18_180 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K18.acc (by decide) (by decide)).trans a17_180
  have a18_1a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K18.acc (by decide) (by decide)).trans a17_1a0
  have a18_1c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K18.acc (by decide) (by decide)).trans a17_1c0
  have a18_260 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K18.acc (by decide) (by decide)).trans a17_260
  have a18_2e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K18.acc (by decide) (by decide)).trans a17_2e0
  have a18_f80 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (K18.acc (by decide) (by decide)).trans a17_f80
  have a18_1044 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K18.acc (by decide) (by decide)).trans a17_1044
  have a18_10c4 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K18.acc (by decide) (by decide)).trans a17_10c4
  have p18_300 : ptF n18.mem B 0x300 = tbl2 P0 0 := (K18.pt (by decide) (by decide)).trans p17_300
  have p18_360 : ptF n18.mem B 0x360 = tbl2 P0 1 := (K18.pt (by decide) (by decide)).trans p17_360
  have p18_3c0 : ptF n18.mem B 0x3C0 = tbl2 P0 2 := (K18.pt (by decide) (by decide)).trans p17_3c0
  have p18_420 : ptF n18.mem B 0x420 = tbl2 P0 3 := (K18.pt (by decide) (by decide)).trans p17_420
  have p18_480 : ptF n18.mem B 0x480 = tbl2 P0 4 := (K18.pt (by decide) (by decide)).trans p17_480
  have p18_4e0 : ptF n18.mem B 0x4E0 = tbl2 P0 5 := (K18.pt (by decide) (by decide)).trans p17_4e0
  have p18_540 : ptF n18.mem B 0x540 = tbl2 P0 6 := (K18.pt (by decide) (by decide)).trans p17_540
  have p18_5a0 : ptF n18.mem B 0x5A0 = tbl2 P0 7 := (K18.pt (by decide) (by decide)).trans p17_5a0
  have p18_600 : ptF n18.mem B 0x600 = tbl2 P1 0 := (K18.pt (by decide) (by decide)).trans p17_600
  have p18_660 : ptF n18.mem B 0x660 = tbl2 P1 1 := (K18.pt (by decide) (by decide)).trans p17_660
  have p18_6c0 : ptF n18.mem B 0x6C0 = tbl2 P1 2 := (K18.pt (by decide) (by decide)).trans p17_6c0
  have p18_720 : ptF n18.mem B 0x720 = tbl2 P1 3 := (K18.pt (by decide) (by decide)).trans p17_720
  have p18_780 : ptF n18.mem B 0x780 = tbl2 P1 4 := (K18.pt (by decide) (by decide)).trans p17_780
  have p18_7e0 : ptF n18.mem B 0x7E0 = tbl2 P1 5 := (K18.pt (by decide) (by decide)).trans p17_7e0
  have p18_840 : ptF n18.mem B 0x840 = tbl2 P1 6 := (K18.pt (by decide) (by decide)).trans p17_840
  have p18_8a0 : ptF n18.mem B 0x8A0 = tbl2 P1 7 := (K18.pt (by decide) (by decide)).trans p17_8a0
  have mb18_900 : leN (memBytes n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [K18.mb (by decide) (by decide)]; exact mb17_900
  have mb18_c84 : memBytes n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K18.mb (by decide) (by decide)]; exact mb17_c84
  have mb18_10e8 : memBytes n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K18.mb (by decide) (by decide)]; exact mb17_10e8
  have mb18_984 : memBytes n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x984) (d := 0xC84) (N := 0x101) fun q hq => by
      rw [show 0x984 + q = 0x980 + (0x4 + q) by omega, X18 (0x4 + q) (by omega),
        show 0xC80 + (0x4 + q) = 0xC84 + q by omega]]; exact mb17_c84
  clear mb17_10e8 mb17_c84 mb17_980 mb17_900 p17_8a0 p17_840 p17_7e0 p17_780 p17_720 p17_6c0 p17_660 p17_600 p17_5a0 p17_540 p17_4e0 p17_480 p17_420 p17_3c0 p17_360 p17_300 a17_10c4 a17_1044 a17_f80 a17_2e0 a17_260 a17_1c0 a17_1a0 a17_180 w17_10e4 w17_c80 g17_12 g17_11 g17_10 g17_26 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x96A
  obtain ⟨n19, c19, u19⟩ := s18.block p2vEcW396a E18.self p2vEcW396a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem P2V n19 0x97C (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock p2vEcW396a (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_26 : reg n19 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vEcW396a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_26, s18.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vEcW396a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_26, s18.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have g19_12 : reg n19 a2 = BitVec.ofNat 32 0x108 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, p2vEcW396a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_26, s18.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk19 : P2vKeepL B n0.mem n19.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4), (0x980, 0x108)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_980 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m19]; exact w18_980
  have w19_c80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m19]; exact w18_c80
  have w19_10e4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m19]; exact w18_10e4
  have a19_180 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m19]; exact a18_180
  have a19_1a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m19]; exact a18_1a0
  have a19_1c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m19]; exact a18_1c0
  have a19_260 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m19]; exact a18_260
  have a19_2e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m19]; exact a18_2e0
  have a19_f80 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m19]; exact a18_f80
  have a19_1044 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m19]; exact a18_1044
  have a19_10c4 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m19]; exact a18_10c4
  have p19_300 : ptF n19.mem B 0x300 = tbl2 P0 0 := by rw [m19]; exact p18_300
  have p19_360 : ptF n19.mem B 0x360 = tbl2 P0 1 := by rw [m19]; exact p18_360
  have p19_3c0 : ptF n19.mem B 0x3C0 = tbl2 P0 2 := by rw [m19]; exact p18_3c0
  have p19_420 : ptF n19.mem B 0x420 = tbl2 P0 3 := by rw [m19]; exact p18_420
  have p19_480 : ptF n19.mem B 0x480 = tbl2 P0 4 := by rw [m19]; exact p18_480
  have p19_4e0 : ptF n19.mem B 0x4E0 = tbl2 P0 5 := by rw [m19]; exact p18_4e0
  have p19_540 : ptF n19.mem B 0x540 = tbl2 P0 6 := by rw [m19]; exact p18_540
  have p19_5a0 : ptF n19.mem B 0x5A0 = tbl2 P0 7 := by rw [m19]; exact p18_5a0
  have p19_600 : ptF n19.mem B 0x600 = tbl2 P1 0 := by rw [m19]; exact p18_600
  have p19_660 : ptF n19.mem B 0x660 = tbl2 P1 1 := by rw [m19]; exact p18_660
  have p19_6c0 : ptF n19.mem B 0x6C0 = tbl2 P1 2 := by rw [m19]; exact p18_6c0
  have p19_720 : ptF n19.mem B 0x720 = tbl2 P1 3 := by rw [m19]; exact p18_720
  have p19_780 : ptF n19.mem B 0x780 = tbl2 P1 4 := by rw [m19]; exact p18_780
  have p19_7e0 : ptF n19.mem B 0x7E0 = tbl2 P1 5 := by rw [m19]; exact p18_7e0
  have p19_840 : ptF n19.mem B 0x840 = tbl2 P1 6 := by rw [m19]; exact p18_840
  have p19_8a0 : ptF n19.mem B 0x8A0 = tbl2 P1 7 := by rw [m19]; exact p18_8a0
  have mb19_900 : leN (memBytes n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m19]; exact mb18_900
  have mb19_984 : memBytes n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m19]; exact mb18_984
  have mb19_c84 : memBytes n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m19]; exact mb18_c84
  have mb19_10e8 : memBytes n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m19]; exact mb18_10e8
  clear mb18_984 mb18_10e8 mb18_c84 mb18_900 p18_8a0 p18_840 p18_7e0 p18_780 p18_720 p18_6c0 p18_660 p18_600 p18_5a0 p18_540 p18_4e0 p18_480 p18_420 p18_3c0 p18_360 p18_300 a18_10c4 a18_1044 a18_f80 a18_2e0 a18_260 a18_1c0 a18_1a0 a18_180 w18_980 w18_10e4 w18_c80 g18_26 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 s18 X18 K18 P18
  -- 0x97C: memcpy
  obtain ⟨n20, P20, K20, X20⟩ := p2v_mc (c := 0x11EC) (d := 0x980) (N := 0x108) F E19 s19 p2v_at_97c p2v_at_980
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
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P20.regs (8 : Fin 32) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P20.regs (9 : Fin 32) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [P20.regs (18 : Fin 32) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P20.regs (19 : Fin 32) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P20.regs (20 : Fin 32) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [P20.regs (21 : Fin 32) (by decide), g19_21]
  have g20_26 : reg n20 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [P20.regs (26 : Fin 32) (by decide), g19_26]
  have keep_kk20 : P2vKeepL B n0.mem n20.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4), (0x980, 0x108), (0x11EC, 0x108)] := keep_kk19.trans K20.toL
  clear keep_kk19
  have w20_980 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := (K20.w32 (by decide) (by decide)).trans w19_980
  have w20_c80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := (K20.w32 (by decide) (by decide)).trans w19_c80
  have w20_10e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K20.w32 (by decide) (by decide)).trans w19_10e4
  have w20_11ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x11EC) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by
    rw [← w19_980]
    exact ld_cp fun q hq => by
      have := X20 (0x0 + q) (by omega)
      rwa [show 0x11EC + (0x0 + q) = 0x11EC + q by omega,
        show 0x980 + (0x0 + q) = 0x980 + q by omega] at this
  have a20_180 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := (K20.acc (by decide) (by decide)).trans a19_180
  have a20_1a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := (K20.acc (by decide) (by decide)).trans a19_1a0
  have a20_1c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := (K20.acc (by decide) (by decide)).trans a19_1c0
  have a20_260 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := (K20.acc (by decide) (by decide)).trans a19_260
  have a20_2e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := (K20.acc (by decide) (by decide)).trans a19_2e0
  have a20_f80 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := (K20.acc (by decide) (by decide)).trans a19_f80
  have a20_1044 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := (K20.acc (by decide) (by decide)).trans a19_1044
  have a20_10c4 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := (K20.acc (by decide) (by decide)).trans a19_10c4
  have p20_300 : ptF n20.mem B 0x300 = tbl2 P0 0 := (K20.pt (by decide) (by decide)).trans p19_300
  have p20_360 : ptF n20.mem B 0x360 = tbl2 P0 1 := (K20.pt (by decide) (by decide)).trans p19_360
  have p20_3c0 : ptF n20.mem B 0x3C0 = tbl2 P0 2 := (K20.pt (by decide) (by decide)).trans p19_3c0
  have p20_420 : ptF n20.mem B 0x420 = tbl2 P0 3 := (K20.pt (by decide) (by decide)).trans p19_420
  have p20_480 : ptF n20.mem B 0x480 = tbl2 P0 4 := (K20.pt (by decide) (by decide)).trans p19_480
  have p20_4e0 : ptF n20.mem B 0x4E0 = tbl2 P0 5 := (K20.pt (by decide) (by decide)).trans p19_4e0
  have p20_540 : ptF n20.mem B 0x540 = tbl2 P0 6 := (K20.pt (by decide) (by decide)).trans p19_540
  have p20_5a0 : ptF n20.mem B 0x5A0 = tbl2 P0 7 := (K20.pt (by decide) (by decide)).trans p19_5a0
  have p20_600 : ptF n20.mem B 0x600 = tbl2 P1 0 := (K20.pt (by decide) (by decide)).trans p19_600
  have p20_660 : ptF n20.mem B 0x660 = tbl2 P1 1 := (K20.pt (by decide) (by decide)).trans p19_660
  have p20_6c0 : ptF n20.mem B 0x6C0 = tbl2 P1 2 := (K20.pt (by decide) (by decide)).trans p19_6c0
  have p20_720 : ptF n20.mem B 0x720 = tbl2 P1 3 := (K20.pt (by decide) (by decide)).trans p19_720
  have p20_780 : ptF n20.mem B 0x780 = tbl2 P1 4 := (K20.pt (by decide) (by decide)).trans p19_780
  have p20_7e0 : ptF n20.mem B 0x7E0 = tbl2 P1 5 := (K20.pt (by decide) (by decide)).trans p19_7e0
  have p20_840 : ptF n20.mem B 0x840 = tbl2 P1 6 := (K20.pt (by decide) (by decide)).trans p19_840
  have p20_8a0 : ptF n20.mem B 0x8A0 = tbl2 P1 7 := (K20.pt (by decide) (by decide)).trans p19_8a0
  have mb20_900 : leN (memBytes n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [K20.mb (by decide) (by decide)]; exact mb19_900
  have mb20_984 : memBytes n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K20.mb (by decide) (by decide)]; exact mb19_984
  have mb20_c84 : memBytes n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K20.mb (by decide) (by decide)]; exact mb19_c84
  have mb20_10e8 : memBytes n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K20.mb (by decide) (by decide)]; exact mb19_10e8
  have mb20_11f0 : memBytes n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x11F0) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x11F0) (d := 0x984) (N := 0x101) fun q hq => by
      rw [show 0x11F0 + q = 0x11EC + (0x4 + q) by omega, X20 (0x4 + q) (by omega),
        show 0x980 + (0x4 + q) = 0x984 + q by omega]]; exact mb19_984
  clear mb19_10e8 mb19_c84 mb19_984 mb19_900 p19_8a0 p19_840 p19_7e0 p19_780 p19_720 p19_6c0 p19_660 p19_600 p19_5a0 p19_540 p19_4e0 p19_480 p19_420 p19_3c0 p19_360 p19_300 a19_10c4 a19_1044 a19_f80 a19_2e0 a19_260 a19_1c0 a19_1a0 a19_180 w19_10e4 w19_c80 w19_980 g19_12 g19_11 g19_10 g19_26 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x984
  obtain ⟨n21, c21, u21⟩ := s20.block p2vEcW3984 E20.self p2vEcW3984_end
    ⟨trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem P2V n21 0x986 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock p2vEcW3984 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_9 : reg n21 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_26 : reg n21 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, p2vEcW3984, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_26, s20.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk21 : P2vKeepL B n0.mem n21.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4), (0x980, 0x108), (0x11EC, 0x108)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_980 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m21]; exact w20_980
  have w21_c80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m21]; exact w20_c80
  have w21_10e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m21]; exact w20_10e4
  have w21_11ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x11EC) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m21]; exact w20_11ec
  have a21_180 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m21]; exact a20_180
  have a21_1a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m21]; exact a20_1a0
  have a21_1c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m21]; exact a20_1c0
  have a21_260 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m21]; exact a20_260
  have a21_2e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m21]; exact a20_2e0
  have a21_f80 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m21]; exact a20_f80
  have a21_1044 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m21]; exact a20_1044
  have a21_10c4 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m21]; exact a20_10c4
  have p21_300 : ptF n21.mem B 0x300 = tbl2 P0 0 := by rw [m21]; exact p20_300
  have p21_360 : ptF n21.mem B 0x360 = tbl2 P0 1 := by rw [m21]; exact p20_360
  have p21_3c0 : ptF n21.mem B 0x3C0 = tbl2 P0 2 := by rw [m21]; exact p20_3c0
  have p21_420 : ptF n21.mem B 0x420 = tbl2 P0 3 := by rw [m21]; exact p20_420
  have p21_480 : ptF n21.mem B 0x480 = tbl2 P0 4 := by rw [m21]; exact p20_480
  have p21_4e0 : ptF n21.mem B 0x4E0 = tbl2 P0 5 := by rw [m21]; exact p20_4e0
  have p21_540 : ptF n21.mem B 0x540 = tbl2 P0 6 := by rw [m21]; exact p20_540
  have p21_5a0 : ptF n21.mem B 0x5A0 = tbl2 P0 7 := by rw [m21]; exact p20_5a0
  have p21_600 : ptF n21.mem B 0x600 = tbl2 P1 0 := by rw [m21]; exact p20_600
  have p21_660 : ptF n21.mem B 0x660 = tbl2 P1 1 := by rw [m21]; exact p20_660
  have p21_6c0 : ptF n21.mem B 0x6C0 = tbl2 P1 2 := by rw [m21]; exact p20_6c0
  have p21_720 : ptF n21.mem B 0x720 = tbl2 P1 3 := by rw [m21]; exact p20_720
  have p21_780 : ptF n21.mem B 0x780 = tbl2 P1 4 := by rw [m21]; exact p20_780
  have p21_7e0 : ptF n21.mem B 0x7E0 = tbl2 P1 5 := by rw [m21]; exact p20_7e0
  have p21_840 : ptF n21.mem B 0x840 = tbl2 P1 6 := by rw [m21]; exact p20_840
  have p21_8a0 : ptF n21.mem B 0x8A0 = tbl2 P1 7 := by rw [m21]; exact p20_8a0
  have mb21_900 : leN (memBytes n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m21]; exact mb20_900
  have mb21_984 : memBytes n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m21]; exact mb20_984
  have mb21_c84 : memBytes n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m21]; exact mb20_c84
  have mb21_10e8 : memBytes n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m21]; exact mb20_10e8
  have mb21_11f0 : memBytes n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x11F0) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m21]; exact mb20_11f0
  clear mb20_11f0 mb20_10e8 mb20_c84 mb20_984 mb20_900 p20_8a0 p20_840 p20_7e0 p20_780 p20_720 p20_6c0 p20_660 p20_600 p20_5a0 p20_540 p20_4e0 p20_480 p20_420 p20_3c0 p20_360 p20_300 a20_10c4 a20_1044 a20_f80 a20_2e0 a20_260 a20_1c0 a20_1a0 a20_180 w20_11ec w20_10e4 w20_c80 w20_980 g20_26 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 s20 X20 K20 P20
  -- 0x986: branch, not taken
  obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0x98A p2v_at_986
    (by decide) (by rw [g21_8, g21_19]; decide)
  have s22 : St n22.mem P2V n22 0x98A (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, P2vR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, P2vR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : P2vCode n22.mem := E21.fr F fr22
  have V22 : P2vSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u22.regs, g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [u22.regs, g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [u22.regs, g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u22.regs, g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u22.regs, g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [u22.regs, g21_21]
  have g22_26 : reg n22 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u22.regs, g21_26]
  have keep_kk22 : P2vKeepL B n0.mem n22.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4), (0x980, 0x108), (0x11EC, 0x108)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_980 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m22]; exact w21_980
  have w22_c80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m22]; exact w21_c80
  have w22_10e4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m22]; exact w21_10e4
  have w22_11ec : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x11EC) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m22]; exact w21_11ec
  have a22_180 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m22]; exact a21_180
  have a22_1a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m22]; exact a21_1a0
  have a22_1c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m22]; exact a21_1c0
  have a22_260 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m22]; exact a21_260
  have a22_2e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m22]; exact a21_2e0
  have a22_f80 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m22]; exact a21_f80
  have a22_1044 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m22]; exact a21_1044
  have a22_10c4 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m22]; exact a21_10c4
  have p22_300 : ptF n22.mem B 0x300 = tbl2 P0 0 := by rw [m22]; exact p21_300
  have p22_360 : ptF n22.mem B 0x360 = tbl2 P0 1 := by rw [m22]; exact p21_360
  have p22_3c0 : ptF n22.mem B 0x3C0 = tbl2 P0 2 := by rw [m22]; exact p21_3c0
  have p22_420 : ptF n22.mem B 0x420 = tbl2 P0 3 := by rw [m22]; exact p21_420
  have p22_480 : ptF n22.mem B 0x480 = tbl2 P0 4 := by rw [m22]; exact p21_480
  have p22_4e0 : ptF n22.mem B 0x4E0 = tbl2 P0 5 := by rw [m22]; exact p21_4e0
  have p22_540 : ptF n22.mem B 0x540 = tbl2 P0 6 := by rw [m22]; exact p21_540
  have p22_5a0 : ptF n22.mem B 0x5A0 = tbl2 P0 7 := by rw [m22]; exact p21_5a0
  have p22_600 : ptF n22.mem B 0x600 = tbl2 P1 0 := by rw [m22]; exact p21_600
  have p22_660 : ptF n22.mem B 0x660 = tbl2 P1 1 := by rw [m22]; exact p21_660
  have p22_6c0 : ptF n22.mem B 0x6C0 = tbl2 P1 2 := by rw [m22]; exact p21_6c0
  have p22_720 : ptF n22.mem B 0x720 = tbl2 P1 3 := by rw [m22]; exact p21_720
  have p22_780 : ptF n22.mem B 0x780 = tbl2 P1 4 := by rw [m22]; exact p21_780
  have p22_7e0 : ptF n22.mem B 0x7E0 = tbl2 P1 5 := by rw [m22]; exact p21_7e0
  have p22_840 : ptF n22.mem B 0x840 = tbl2 P1 6 := by rw [m22]; exact p21_840
  have p22_8a0 : ptF n22.mem B 0x8A0 = tbl2 P1 7 := by rw [m22]; exact p21_8a0
  have mb22_900 : leN (memBytes n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m22]; exact mb21_900
  have mb22_984 : memBytes n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m22]; exact mb21_984
  have mb22_c84 : memBytes n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m22]; exact mb21_c84
  have mb22_10e8 : memBytes n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m22]; exact mb21_10e8
  have mb22_11f0 : memBytes n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x11F0) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m22]; exact mb21_11f0
  clear mb21_11f0 mb21_10e8 mb21_c84 mb21_984 mb21_900 p21_8a0 p21_840 p21_7e0 p21_780 p21_720 p21_6c0 p21_660 p21_600 p21_5a0 p21_540 p21_4e0 p21_480 p21_420 p21_3c0 p21_360 p21_300 a21_10c4 a21_1044 a21_f80 a21_2e0 a21_260 a21_1c0 a21_1a0 a21_180 w21_11ec w21_10e4 w21_c80 w21_980 g21_8 g21_26 g21_21 g21_20 g21_19 g21_18 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x98A: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self p2v_at_98a (off' := 0x98E) (by decide)
    (by rw [g22_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x7C4 = B + 0x21A0 + BitVec.ofNat 32 0x10E4 by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s23 : St n23.mem P2V n23 0x98E (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, P2vR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, P2vR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : P2vCode n23.mem := E22.fr F fr23
  have V23 : P2vSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
  have g23_18 : reg n23 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_26 : reg n23 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_9 : reg n23 (9 : Fin 32) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_26, show B + 0x21A0 + BitVec.ofNat 32 0x920 + 0x7C4 = B + 0x21A0 + BitVec.ofNat 32 0x10E4 by p2v_addr, w22_10e4]
  have keep_kk23 : P2vKeepL B n0.mem n23.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4), (0x980, 0x108), (0x11EC, 0x108)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_980 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m23]; exact w22_980
  have w23_c80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m23]; exact w22_c80
  have w23_10e4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m23]; exact w22_10e4
  have w23_11ec : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x11EC) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m23]; exact w22_11ec
  have a23_180 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m23]; exact a22_180
  have a23_1a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m23]; exact a22_1a0
  have a23_1c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m23]; exact a22_1c0
  have a23_260 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m23]; exact a22_260
  have a23_2e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m23]; exact a22_2e0
  have a23_f80 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m23]; exact a22_f80
  have a23_1044 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m23]; exact a22_1044
  have a23_10c4 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m23]; exact a22_10c4
  have p23_300 : ptF n23.mem B 0x300 = tbl2 P0 0 := by rw [m23]; exact p22_300
  have p23_360 : ptF n23.mem B 0x360 = tbl2 P0 1 := by rw [m23]; exact p22_360
  have p23_3c0 : ptF n23.mem B 0x3C0 = tbl2 P0 2 := by rw [m23]; exact p22_3c0
  have p23_420 : ptF n23.mem B 0x420 = tbl2 P0 3 := by rw [m23]; exact p22_420
  have p23_480 : ptF n23.mem B 0x480 = tbl2 P0 4 := by rw [m23]; exact p22_480
  have p23_4e0 : ptF n23.mem B 0x4E0 = tbl2 P0 5 := by rw [m23]; exact p22_4e0
  have p23_540 : ptF n23.mem B 0x540 = tbl2 P0 6 := by rw [m23]; exact p22_540
  have p23_5a0 : ptF n23.mem B 0x5A0 = tbl2 P0 7 := by rw [m23]; exact p22_5a0
  have p23_600 : ptF n23.mem B 0x600 = tbl2 P1 0 := by rw [m23]; exact p22_600
  have p23_660 : ptF n23.mem B 0x660 = tbl2 P1 1 := by rw [m23]; exact p22_660
  have p23_6c0 : ptF n23.mem B 0x6C0 = tbl2 P1 2 := by rw [m23]; exact p22_6c0
  have p23_720 : ptF n23.mem B 0x720 = tbl2 P1 3 := by rw [m23]; exact p22_720
  have p23_780 : ptF n23.mem B 0x780 = tbl2 P1 4 := by rw [m23]; exact p22_780
  have p23_7e0 : ptF n23.mem B 0x7E0 = tbl2 P1 5 := by rw [m23]; exact p22_7e0
  have p23_840 : ptF n23.mem B 0x840 = tbl2 P1 6 := by rw [m23]; exact p22_840
  have p23_8a0 : ptF n23.mem B 0x8A0 = tbl2 P1 7 := by rw [m23]; exact p22_8a0
  have mb23_900 : leN (memBytes n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m23]; exact mb22_900
  have mb23_984 : memBytes n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m23]; exact mb22_984
  have mb23_c84 : memBytes n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m23]; exact mb22_c84
  have mb23_10e8 : memBytes n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m23]; exact mb22_10e8
  have mb23_11f0 : memBytes n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x11F0) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m23]; exact mb22_11f0
  clear mb22_11f0 mb22_10e8 mb22_c84 mb22_984 mb22_900 p22_8a0 p22_840 p22_7e0 p22_780 p22_720 p22_6c0 p22_660 p22_600 p22_5a0 p22_540 p22_4e0 p22_480 p22_420 p22_3c0 p22_360 p22_300 a22_10c4 a22_1044 a22_f80 a22_2e0 a22_260 a22_1c0 a22_1a0 a22_180 w22_11ec w22_10e4 w22_c80 w22_980 g22_26 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x98E
  obtain ⟨n24, c24, u24⟩ := s23.block p2vEcW398e E23.self p2vEcW398e_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem P2V n24 0x996 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock p2vEcW398e (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb24, runBlock_reg _ _ _ (20 : Fin 32) s23.zero (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_26 : reg n24 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, p2vEcW398e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_20, g23_21, g23_26, s23.zero])
    all_goals first | with_reducible rfl | p2v_addr | decide
  have keep_kk24 : P2vKeepL B n0.mem n24.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4), (0x980, 0x108), (0x11EC, 0x108)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_980 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m24]; exact w23_980
  have w24_c80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m24]; exact w23_c80
  have w24_10e4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m24]; exact w23_10e4
  have w24_11ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x11EC) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m24]; exact w23_11ec
  have a24_180 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m24]; exact a23_180
  have a24_1a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m24]; exact a23_1a0
  have a24_1c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m24]; exact a23_1c0
  have a24_260 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m24]; exact a23_260
  have a24_2e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m24]; exact a23_2e0
  have a24_f80 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m24]; exact a23_f80
  have a24_1044 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m24]; exact a23_1044
  have a24_10c4 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m24]; exact a23_10c4
  have p24_300 : ptF n24.mem B 0x300 = tbl2 P0 0 := by rw [m24]; exact p23_300
  have p24_360 : ptF n24.mem B 0x360 = tbl2 P0 1 := by rw [m24]; exact p23_360
  have p24_3c0 : ptF n24.mem B 0x3C0 = tbl2 P0 2 := by rw [m24]; exact p23_3c0
  have p24_420 : ptF n24.mem B 0x420 = tbl2 P0 3 := by rw [m24]; exact p23_420
  have p24_480 : ptF n24.mem B 0x480 = tbl2 P0 4 := by rw [m24]; exact p23_480
  have p24_4e0 : ptF n24.mem B 0x4E0 = tbl2 P0 5 := by rw [m24]; exact p23_4e0
  have p24_540 : ptF n24.mem B 0x540 = tbl2 P0 6 := by rw [m24]; exact p23_540
  have p24_5a0 : ptF n24.mem B 0x5A0 = tbl2 P0 7 := by rw [m24]; exact p23_5a0
  have p24_600 : ptF n24.mem B 0x600 = tbl2 P1 0 := by rw [m24]; exact p23_600
  have p24_660 : ptF n24.mem B 0x660 = tbl2 P1 1 := by rw [m24]; exact p23_660
  have p24_6c0 : ptF n24.mem B 0x6C0 = tbl2 P1 2 := by rw [m24]; exact p23_6c0
  have p24_720 : ptF n24.mem B 0x720 = tbl2 P1 3 := by rw [m24]; exact p23_720
  have p24_780 : ptF n24.mem B 0x780 = tbl2 P1 4 := by rw [m24]; exact p23_780
  have p24_7e0 : ptF n24.mem B 0x7E0 = tbl2 P1 5 := by rw [m24]; exact p23_7e0
  have p24_840 : ptF n24.mem B 0x840 = tbl2 P1 6 := by rw [m24]; exact p23_840
  have p24_8a0 : ptF n24.mem B 0x8A0 = tbl2 P1 7 := by rw [m24]; exact p23_8a0
  have mb24_900 : leN (memBytes n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m24]; exact mb23_900
  have mb24_984 : memBytes n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m24]; exact mb23_984
  have mb24_c84 : memBytes n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m24]; exact mb23_c84
  have mb24_10e8 : memBytes n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m24]; exact mb23_10e8
  have mb24_11f0 : memBytes n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x11F0) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m24]; exact mb23_11f0
  clear mb23_11f0 mb23_10e8 mb23_c84 mb23_984 mb23_900 p23_8a0 p23_840 p23_7e0 p23_780 p23_720 p23_6c0 p23_660 p23_600 p23_5a0 p23_540 p23_4e0 p23_480 p23_420 p23_3c0 p23_360 p23_300 a23_10c4 a23_1044 a23_f80 a23_2e0 a23_260 a23_1c0 a23_1a0 a23_180 w23_11ec w23_10e4 w23_c80 w23_980 g23_9 g23_26 g23_21 g23_20 g23_19 g23_18 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x996: lw
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self p2v_at_996 (off' := 0x998) (by decide)
    (by rw [g24_10, show B + 0x21A0 + BitVec.ofNat 32 0x11EC + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC by p2v_addr]; exact p2v_al F (by decide) (by decide))
  have s25 : St n25.mem P2V n25 0x998 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, P2vR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, P2vR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : P2vCode n25.mem := E24.fr F fr25
  have V25 : P2vSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_26 : reg n25 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_10 : reg n25 a0 = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_10, show B + 0x21A0 + BitVec.ofNat 32 0x11EC + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0x11EC by p2v_addr, w24_11ec]
  have keep_kk25 : P2vKeepL B n0.mem n25.mem [(0xF80, 0x20), (0x980, 0x20), (0x980, 0x20), (0x900, 0x20), (0x980, 0x101), (0xC84, 0x101), (0xC84, 0x101), (0xC80, 0x4), (0x980, 0x108), (0x11EC, 0x108)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_980 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m25]; exact w24_980
  have w25_c80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m25]; exact w24_c80
  have w25_10e4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m25]; exact w24_10e4
  have w25_11ec : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x11EC) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m25]; exact w24_11ec
  have a25_180 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv := by rw [m25]; exact a24_180
  have a25_1a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv := by rw [m25]; exact a24_1a0
  have a25_1c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv := by rw [m25]; exact a24_1c0
  have a25_260 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = U1 := by rw [m25]; exact a24_260
  have a25_2e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = U2 := by rw [m25]; exact a24_2e0
  have a25_f80 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = U2 := by rw [m25]; exact a24_f80
  have a25_1044 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = U1 := by rw [m25]; exact a24_1044
  have a25_10c4 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = U2 := by rw [m25]; exact a24_10c4
  have p25_300 : ptF n25.mem B 0x300 = tbl2 P0 0 := by rw [m25]; exact p24_300
  have p25_360 : ptF n25.mem B 0x360 = tbl2 P0 1 := by rw [m25]; exact p24_360
  have p25_3c0 : ptF n25.mem B 0x3C0 = tbl2 P0 2 := by rw [m25]; exact p24_3c0
  have p25_420 : ptF n25.mem B 0x420 = tbl2 P0 3 := by rw [m25]; exact p24_420
  have p25_480 : ptF n25.mem B 0x480 = tbl2 P0 4 := by rw [m25]; exact p24_480
  have p25_4e0 : ptF n25.mem B 0x4E0 = tbl2 P0 5 := by rw [m25]; exact p24_4e0
  have p25_540 : ptF n25.mem B 0x540 = tbl2 P0 6 := by rw [m25]; exact p24_540
  have p25_5a0 : ptF n25.mem B 0x5A0 = tbl2 P0 7 := by rw [m25]; exact p24_5a0
  have p25_600 : ptF n25.mem B 0x600 = tbl2 P1 0 := by rw [m25]; exact p24_600
  have p25_660 : ptF n25.mem B 0x660 = tbl2 P1 1 := by rw [m25]; exact p24_660
  have p25_6c0 : ptF n25.mem B 0x6C0 = tbl2 P1 2 := by rw [m25]; exact p24_6c0
  have p25_720 : ptF n25.mem B 0x720 = tbl2 P1 3 := by rw [m25]; exact p24_720
  have p25_780 : ptF n25.mem B 0x780 = tbl2 P1 4 := by rw [m25]; exact p24_780
  have p25_7e0 : ptF n25.mem B 0x7E0 = tbl2 P1 5 := by rw [m25]; exact p24_7e0
  have p25_840 : ptF n25.mem B 0x840 = tbl2 P1 6 := by rw [m25]; exact p24_840
  have p25_8a0 : ptF n25.mem B 0x8A0 = tbl2 P1 7 := by rw [m25]; exact p24_8a0
  have mb25_900 : leN (memBytes n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 0x20) = U2 := by rw [m25]; exact mb24_900
  have mb25_984 : memBytes n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x984) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m25]; exact mb24_984
  have mb25_c84 : memBytes n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC84) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m25]; exact mb24_c84
  have mb25_10e8 : memBytes n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m25]; exact mb24_10e8
  have mb25_11f0 : memBytes n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x11F0) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m25]; exact mb24_11f0
  clear mb24_11f0 mb24_10e8 mb24_c84 mb24_984 mb24_900 p24_8a0 p24_840 p24_7e0 p24_780 p24_720 p24_6c0 p24_660 p24_600 p24_5a0 p24_540 p24_4e0 p24_480 p24_420 p24_3c0 p24_360 p24_300 a24_10c4 a24_1044 a24_f80 a24_2e0 a24_260 a24_1c0 a24_1a0 a24_180 w24_11ec w24_10e4 w24_c80 w24_980 g24_10 g24_26 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  exact .inr ⟨n25, t25, s25, E25, V25, fR25, g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_18, g25_19, g25_20, g25_21, g25_26, w25_980, w25_c80, w25_10e4, w25_11ec, a25_180, a25_1a0, a25_1c0, a25_260, a25_2e0, a25_f80, a25_1044, a25_10c4, p25_300, p25_360, p25_3c0, p25_420, p25_480, p25_4e0, p25_540, p25_5a0, p25_600, p25_660, p25_6c0, p25_720, p25_780, p25_7e0, p25_840, p25_8a0, mb25_900, mb25_984, mb25_c84, mb25_10e8, mb25_11f0, keep_kk25.mono (by decide)⟩

end C3.RV32.P2v
