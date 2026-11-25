import C3BootProofs.Proofs.SvData

/-!
# `sigstore::verify`: an extension with policy OID 1

From the OID tests at 0x4E2 back to the loop head at 0x3B8, for an extension with policy OID 1: its value must be one `UTF8String`, which fills policy slot 1.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svDp14e2 : List BInstr :=
  [.aluImm .add a3 x0 0x3]
theorem svDp14e2_end : blockEnd sigstoreVerifyCode 0x4E2 svDp14e2 = some 0x4E4 := by
  simp only [svDp14e2]
  rw [blockEnd, sv_at_4e2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp14e8 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF8F7]
theorem svDp14e8_end : blockEnd sigstoreVerifyCode 0x4E8 svDp14e8 = some 0x4F0 := by
  simp only [svDp14e8]
  rw [blockEnd, sv_at_4e8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp1572 : List BInstr :=
  [.aluImm .add a3 x0 0x3]
theorem svDp1572_end : blockEnd sigstoreVerifyCode 0x572 svDp1572 = some 0x574 := by
  simp only [svDp1572]
  rw [blockEnd, sv_at_572]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp1578 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF900]
theorem svDp1578_end : blockEnd sigstoreVerifyCode 0x578 svDp1578 = some 0x580 := by
  simp only [svDp1578]
  rw [blockEnd, sv_at_578]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_57c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp1616 : List BInstr :=
  [.aluImm .add a3 x0 0x3]
theorem svDp1616_end : blockEnd sigstoreVerifyCode 0x616 svDp1616 = some 0x618 := by
  simp only [svDp1616]
  rw [blockEnd, sv_at_616]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp161c : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF8FD]
theorem svDp161c_end : blockEnd sigstoreVerifyCode 0x61C svDp161c = some 0x624 := by
  simp only [svDp161c]
  rw [blockEnd, sv_at_61c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_620]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp16f2 : List BInstr :=
  [.aluImm .add a0 x0 0xFFFFFFFF]
theorem svDp16f2_end : blockEnd sigstoreVerifyCode 0x6F2 svDp16f2 = some 0x6F4 := by
  simp only [svDp16f2]
  rw [blockEnd, sv_at_6f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp16f6 : List BInstr :=
  [.lui (26 : Fin 32) 0x3FCC5000, .aluImm .add (26 : Fin 32) (26 : Fin 32) 0xFFFFF958]
theorem svDp16f6_end : blockEnd sigstoreVerifyCode 0x6F6 svDp16f6 = some 0x6FE := by
  simp only [svDp16f6]
  rw [blockEnd, sv_at_6f6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_6fa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp16fe : List BInstr :=
  [.aluImm .add a0 x0 0x4]
theorem svDp16fe_end : blockEnd sigstoreVerifyCode 0x6FE svDp16fe = some 0x700 := by
  simp only [svDp16fe]
  rw [blockEnd, sv_at_6fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp170a : List BInstr :=
  [.aluImm .add a1 x0 0xA]
theorem svDp170a_end : blockEnd sigstoreVerifyCode 0x70A svDp170a = some 0x70C := by
  simp only [svDp170a]
  rw [blockEnd, sv_at_70a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp171a : List BInstr :=
  [.aluImm .add a1 a1 0x1]
theorem svDp171a_end : blockEnd sigstoreVerifyCode 0x71A svDp171a = some 0x71C := by
  simp only [svDp171a]
  rw [blockEnd, sv_at_71a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp171e : List BInstr :=
  [.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x8]
theorem svDp171e_end : blockEnd sigstoreVerifyCode 0x71E svDp171e = some 0x720 := by
  simp only [svDp171e]
  rw [blockEnd, sv_at_71e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp1724 : List BInstr :=
  [.aluImm .add a2 sp 0x380]
theorem svDp1724_end : blockEnd sigstoreVerifyCode 0x724 svDp1724 = some 0x726 := by
  simp only [svDp1724]
  rw [blockEnd, sv_at_724]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp1730 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x380]
theorem svDp1730_end : blockEnd sigstoreVerifyCode 0x730 svDp1730 = some 0x736 := by
  simp only [svDp1730]
  rw [blockEnd, sv_at_730]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_734]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp1748 : List BInstr :=
  [.aluImm .add a2 x0 0xC]
theorem svDp1748_end : blockEnd sigstoreVerifyCode 0x748 svDp1748 = some 0x74A := by
  simp only [svDp1748]
  rw [blockEnd, sv_at_748]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp1958 : List BInstr :=
  [.aluImm .add a0 x0 0x16]
theorem svDp1958_end : blockEnd sigstoreVerifyCode 0x958 svDp1958 = some 0x95A := by
  simp only [svDp1958]
  rw [blockEnd, sv_at_958]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp1940 : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem svDp1940_end : blockEnd sigstoreVerifyCode 0x940 svDp1940 = some 0x942 := by
  simp only [svDp1940]
  rw [blockEnd, sv_at_940]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp175c : List BInstr :=
  [.aluImm .sll (26 : Fin 32) (26 : Fin 32) 0x3, .aluImm .add a2 sp 0x80, .alu .add (26 : Fin 32) (26 : Fin 32) a2, .alu .add a2 x0 (26 : Fin 32)]
theorem svDp175c_end : blockEnd sigstoreVerifyCode 0x75C svDp175c = some 0x764 := by
  simp only [svDp175c]
  rw [blockEnd, sv_at_75c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_75e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_760]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_762]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_dp1 {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c op ol vp vl rest : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x4E2 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x15)
    (g0_9 : reg n0 (9 : Fin 32) = tbp)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_23 : reg n0 (23 : Fin 32) = sgp)
    (g0_24 : reg n0 (24 : Fin 32) = kp)
    (g0_25 : reg n0 (25 : Fin 32) = sgl)
    (g0_27 : reg n0 (27 : Fin 32) = tbl)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5)
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6)
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7)
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8)
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9)
    (w0_150 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0)
    (w0_154 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op)
    (w0_158 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur)
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16)
    (val_in : SvIn B vp vl.toNat)
    (oid_in : SvIn B op ol.toNat)
    (SD0 : SvData M0)
    (hku : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)
    (heku : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)
    (hbc : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)
    (hp0 : ¬ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op ol.toNat)
    (hp1 : memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op ol.toNat) :
    (¬ (∃ tl56, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl56 ∧ (BitVec.ofNat 8 tl56.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl56.header + tl56.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl56, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl56 ∧
    (BitVec.ofNat 8 tl56.tag = BitVec.ofNat 8 0xC) ∧
    ((vl) - BitVec.ofNat 32 (tl56.header + tl56.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x3B8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x15 ∧
        reg n' (9 : Fin 32) = tbp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = sgp ∧
        reg n' (24 : Fin 32) = kp ∧
        reg n' (25 : Fin 32) = sgl ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rest ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (vp) + BitVec.ofNat 32 tl56.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl56.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest ∧
        SvKeepL B n0.mem n'.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x88, 0x4), (0x8C, 0x4), (0x50, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x4E2
  obtain ⟨n1, c1, u1⟩ := s0.block svDp14e2 E0.self svDp14e2_end
    ⟨trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x4E4 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svDp14e2 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by
    rw [rb1, runBlock_reg _ _ _ sp s0.zero (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (3 : Fin 32) s0.zero (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (4 : Fin 32) s0.zero (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = tbp := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = dg := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = rootp := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = ll := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = sgp := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = kp := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = sgl := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_27 : reg n1 (27 : Fin 32) = tbl := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_13 : reg n1 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svDp14e2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m1]; exact w0_2c
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m1]; exact w0_34
  have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m1]; exact w0_38
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m1]; exact w0_44
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m1]; exact w0_48
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m1]; exact w0_4c
  have w1_54 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m1]; exact w0_54
  have w1_58 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m1]; exact w0_58
  have w1_5c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m1]; exact w0_5c
  have w1_60 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m1]; exact w0_60
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m1]; exact w0_64
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m1]; exact w0_68
  have w1_6c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m1]; exact w0_6c
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m1]; exact w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m1]; exact w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m1]; exact w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m1]; exact w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m1]; exact w0_84
  have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m1]; exact w0_88
  have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m1]; exact w0_8c
  have w1_90 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m1]; exact w0_90
  have w1_94 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m1]; exact w0_94
  have w1_98 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m1]; exact w0_98
  have w1_9c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m1]; exact w0_9c
  have w1_a0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m1]; exact w0_a0
  have w1_a4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m1]; exact w0_a4
  have w1_150 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m1]; exact w0_150
  have w1_154 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m1]; exact w0_154
  have w1_158 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m1]; exact w0_158
  have w1_15c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m1]; exact w0_15c
  -- 0x4E4: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_4e4 (off' := 0x4E6) (by decide)
    (by rw [g1_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0x4E6 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = tbp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_9]
  have g2_13 : reg n2 a3 = BitVec.ofNat 32 0x3 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_13]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = sgp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = kp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = sgl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_27 : reg n2 (27 : Fin 32) = tbl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_10 : reg n2 a0 = op := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w1_4c]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m2]; exact w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m2]; exact w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m2]; exact w1_38
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m2]; exact w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m2]; exact w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m2]; exact w1_4c
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m2]; exact w1_54
  have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m2]; exact w1_58
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m2]; exact w1_5c
  have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m2]; exact w1_60
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m2]; exact w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m2]; exact w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m2]; exact w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m2]; exact w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m2]; exact w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m2]; exact w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m2]; exact w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m2]; exact w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m2]; exact w1_8c
  have w2_90 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m2]; exact w1_90
  have w2_94 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m2]; exact w1_94
  have w2_98 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m2]; exact w1_98
  have w2_9c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m2]; exact w1_9c
  have w2_a0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m2]; exact w1_a0
  have w2_a4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m2]; exact w1_a4
  have w2_150 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m2]; exact w1_150
  have w2_154 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m2]; exact w1_154
  have w2_158 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m2]; exact w1_158
  have w2_15c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m2]; exact w1_15c
  clear w1_15c w1_158 w1_154 w1_150 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_4c w1_48 w1_44 w1_38 w1_34 w1_30 w1_2c g1_13 g1_27 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x4E6: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_4e6 (off' := 0x4E8) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x4E8 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = tbp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_10 : reg n3 a0 = op := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
  have g3_13 : reg n3 a3 = BitVec.ofNat 32 0x3 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_13]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = sgp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = kp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = sgl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_27 : reg n3 (27 : Fin 32) = tbl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_11 : reg n3 a1 = ol := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w2_48]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m3]; exact w2_2c
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m3]; exact w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m3]; exact w2_38
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m3]; exact w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m3]; exact w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m3]; exact w2_4c
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m3]; exact w2_54
  have w3_58 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m3]; exact w2_58
  have w3_5c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m3]; exact w2_5c
  have w3_60 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m3]; exact w2_60
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m3]; exact w2_68
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m3]; exact w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m3]; exact w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m3]; exact w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m3]; exact w2_8c
  have w3_90 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m3]; exact w2_90
  have w3_94 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m3]; exact w2_94
  have w3_98 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m3]; exact w2_98
  have w3_9c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m3]; exact w2_9c
  have w3_a0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m3]; exact w2_a0
  have w3_a4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m3]; exact w2_a4
  have w3_150 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m3]; exact w2_150
  have w3_154 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m3]; exact w2_154
  have w3_158 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m3]; exact w2_158
  have w3_15c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m3]; exact w2_15c
  clear w2_15c w2_158 w2_154 w2_150 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_4c w2_48 w2_44 w2_38 w2_34 w2_30 w2_2c g2_10 g2_27 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_13 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x4E8
  obtain ⟨n4, c4, u4⟩ := s3.block svDp14e8 E3.self svDp14e8_end
    ⟨trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x4F0 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svDp14e8 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by
    rw [rb4, runBlock_reg _ _ _ sp s3.zero (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb4, runBlock_reg _ _ _ (3 : Fin 32) s3.zero (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb4, runBlock_reg _ _ _ (4 : Fin 32) s3.zero (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = tbp := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_10 : reg n4 a0 = op := by
    rw [rb4, runBlock_reg _ _ _ a0 s3.zero (by decide), g3_10]
  have g4_11 : reg n4 a1 = ol := by
    rw [rb4, runBlock_reg _ _ _ a1 s3.zero (by decide), g3_11]
  have g4_13 : reg n4 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb4, runBlock_reg _ _ _ a3 s3.zero (by decide), g3_13]
  have g4_18 : reg n4 (18 : Fin 32) = out := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = dg := by
    rw [rb4, runBlock_reg _ _ _ (20 : Fin 32) s3.zero (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = rootp := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = ll := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = sgp := by
    rw [rb4, runBlock_reg _ _ _ (23 : Fin 32) s3.zero (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = kp := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = sgl := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_27 : reg n4 (27 : Fin 32) = tbl := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_12 : reg n4 a2 = BitVec.ofNat 32 (img% svConstExtAddress) := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svDp14e8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_11, g3_13, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m4]; exact w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m4]; exact w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m4]; exact w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m4]; exact w3_38
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m4]; exact w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m4]; exact w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m4]; exact w3_4c
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m4]; exact w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m4]; exact w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m4]; exact w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m4]; exact w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m4]; exact w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m4]; exact w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m4]; exact w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m4]; exact w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m4]; exact w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m4]; exact w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m4]; exact w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m4]; exact w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m4]; exact w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m4]; exact w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m4]; exact w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m4]; exact w3_94
  have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m4]; exact w3_98
  have w4_9c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m4]; exact w3_9c
  have w4_a0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m4]; exact w3_a0
  have w4_a4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m4]; exact w3_a4
  have w4_150 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m4]; exact w3_150
  have w4_154 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m4]; exact w3_154
  have w4_158 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m4]; exact w3_158
  have w4_15c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m4]; exact w3_15c
  clear w3_15c w3_158 w3_154 w3_150 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_4c w3_48 w3_44 w3_38 w3_34 w3_30 w3_2c g3_11 g3_27 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_13 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x4F0: sv_seqEqF
  obtain ⟨n5, c5, s5, rk5, a0_5, K5, fr5⟩ := sv_seqEqF (pl := ol.toNat) (ql := 3)
    F E4 s4 sv_at_4f0 sv_at_4f4 (by decide) (by decide) g4_2
    g4_10 (by rw [g4_11, ofNat_toNat_self]) g4_12 g4_13 (.inl oid_in) (.inr ⟨by decide, by decide⟩)
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keepL K5 (by decide)
  rw [sv_mbRo FW fR4 (.inl oid_in), sv_mbRo FW fR4 (.inr ⟨by decide, by decide⟩)] at a0_5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rk5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk5 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk5 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk5 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = tbp := by rw [rk5 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rk5 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rk5 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = dg := by rw [rk5 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = rootp := by rw [rk5 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = ll := by rw [rk5 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = sgp := by rw [rk5 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = kp := by rw [rk5 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = sgl := by rw [rk5 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_25]
  have g5_27 : reg n5 (27 : Fin 32) = tbl := by rw [rk5 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := keep_kk4.trans K5
  clear keep_kk4
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K5.w32 (by decide) (by decide)).trans w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K5.w32 (by decide) (by decide)).trans w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K5.w32 (by decide) (by decide)).trans w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K5.w32 (by decide) (by decide)).trans w4_38
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K5.w32 (by decide) (by decide)).trans w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K5.w32 (by decide) (by decide)).trans w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K5.w32 (by decide) (by decide)).trans w4_4c
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K5.w32 (by decide) (by decide)).trans w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K5.w32 (by decide) (by decide)).trans w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K5.w32 (by decide) (by decide)).trans w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K5.w32 (by decide) (by decide)).trans w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K5.w32 (by decide) (by decide)).trans w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K5.w32 (by decide) (by decide)).trans w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K5.w32 (by decide) (by decide)).trans w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K5.w32 (by decide) (by decide)).trans w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K5.w32 (by decide) (by decide)).trans w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K5.w32 (by decide) (by decide)).trans w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K5.w32 (by decide) (by decide)).trans w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K5.w32 (by decide) (by decide)).trans w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K5.w32 (by decide) (by decide)).trans w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K5.w32 (by decide) (by decide)).trans w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K5.w32 (by decide) (by decide)).trans w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K5.w32 (by decide) (by decide)).trans w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K5.w32 (by decide) (by decide)).trans w4_94
  have w5_98 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K5.w32 (by decide) (by decide)).trans w4_98
  have w5_9c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K5.w32 (by decide) (by decide)).trans w4_9c
  have w5_a0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K5.w32 (by decide) (by decide)).trans w4_a0
  have w5_a4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K5.w32 (by decide) (by decide)).trans w4_a4
  have w5_150 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K5.w32 (by decide) (by decide)).trans w4_150
  have w5_154 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K5.w32 (by decide) (by decide)).trans w4_154
  have w5_158 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K5.w32 (by decide) (by decide)).trans w4_158
  have w5_15c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K5.w32 (by decide) (by decide)).trans w4_15c
  clear w4_15c w4_158 w4_154 w4_150 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_4c w4_48 w4_44 w4_38 w4_34 w4_30 w4_2c g4_12 g4_27 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_13 g4_11 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 0 := by rw [a0_5, ite_eq_right hku]; rfl
  -- 0x4F8: branch, taken
  obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0x572 sv_at_4f8
    (by decide) (by rw [g5_10, s5.zero]; decide)
  have s6 : St n6.mem SV n6 0x572 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u6.regs, g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = tbp := by rw [u6.regs, g5_9]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 0x0 := by rw [u6.regs, g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [u6.regs, g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = kp := by rw [u6.regs, g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [u6.regs, g5_25]
  have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [u6.regs, g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m6]; exact w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m6]; exact w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m6]; exact w5_38
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m6]; exact w5_4c
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m6]; exact w5_54
  have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m6]; exact w5_58
  have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m6]; exact w5_5c
  have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m6]; exact w5_60
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m6]; exact w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m6]; exact w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m6]; exact w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m6]; exact w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m6]; exact w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m6]; exact w5_8c
  have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m6]; exact w5_90
  have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m6]; exact w5_94
  have w6_98 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m6]; exact w5_98
  have w6_9c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m6]; exact w5_9c
  have w6_a0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m6]; exact w5_a0
  have w6_a4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m6]; exact w5_a4
  have w6_150 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m6]; exact w5_150
  have w6_154 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m6]; exact w5_154
  have w6_158 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m6]; exact w5_158
  have w6_15c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m6]; exact w5_15c
  clear w5_15c w5_158 w5_154 w5_150 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_4c w5_48 w5_44 w5_38 w5_34 w5_30 w5_2c g5_27 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 K5 a0_5 rk5 s5 c5
  -- 0x572
  obtain ⟨n7, c7, u7⟩ := s6.block svDp1572 E6.self svDp1572_end
    ⟨trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x574 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svDp1572 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by
    rw [rb7, runBlock_reg _ _ _ sp s6.zero (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (3 : Fin 32) s6.zero (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (4 : Fin 32) s6.zero (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = tbp := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb7, runBlock_reg _ _ _ a0 s6.zero (by decide), g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = dg := by
    rw [rb7, runBlock_reg _ _ _ (20 : Fin 32) s6.zero (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = rootp := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = ll := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = sgp := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = kp := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = sgl := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_27 : reg n7 (27 : Fin 32) = tbl := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_13 : reg n7 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svDp1572, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m7]; exact w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m7]; exact w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m7]; exact w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m7]; exact w6_38
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m7]; exact w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m7]; exact w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m7]; exact w6_4c
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m7]; exact w6_54
  have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m7]; exact w6_58
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m7]; exact w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m7]; exact w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m7]; exact w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m7]; exact w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m7]; exact w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m7]; exact w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m7]; exact w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m7]; exact w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m7]; exact w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m7]; exact w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m7]; exact w6_8c
  have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m7]; exact w6_90
  have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m7]; exact w6_94
  have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m7]; exact w6_98
  have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m7]; exact w6_9c
  have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m7]; exact w6_a0
  have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m7]; exact w6_a4
  have w7_150 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m7]; exact w6_150
  have w7_154 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m7]; exact w6_154
  have w7_158 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m7]; exact w6_158
  have w7_15c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m7]; exact w6_15c
  clear w6_15c w6_158 w6_154 w6_150 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_4c w6_48 w6_44 w6_38 w6_34 w6_30 w6_2c g6_27 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6 g5_10
  -- 0x574: lw
  obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_574 (off' := 0x576) (by decide)
    (by rw [g7_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s8 : St n8.mem SV n8 0x576 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
  have g8_13 : reg n8 a3 = BitVec.ofNat 32 0x3 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_13]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = kp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_10 : reg n8 a0 = op := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w7_4c]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m8]; exact w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m8]; exact w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m8]; exact w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m8]; exact w7_38
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m8]; exact w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m8]; exact w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m8]; exact w7_4c
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m8]; exact w7_54
  have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m8]; exact w7_58
  have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m8]; exact w7_5c
  have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m8]; exact w7_60
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m8]; exact w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m8]; exact w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m8]; exact w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m8]; exact w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m8]; exact w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m8]; exact w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m8]; exact w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m8]; exact w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m8]; exact w7_8c
  have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m8]; exact w7_90
  have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m8]; exact w7_94
  have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m8]; exact w7_98
  have w8_9c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m8]; exact w7_9c
  have w8_a0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m8]; exact w7_a0
  have w8_a4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m8]; exact w7_a4
  have w8_150 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m8]; exact w7_150
  have w8_154 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m8]; exact w7_154
  have w8_158 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m8]; exact w7_158
  have w8_15c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m8]; exact w7_15c
  clear w7_15c w7_158 w7_154 w7_150 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_4c w7_48 w7_44 w7_38 w7_34 w7_30 w7_2c g7_13 g7_27 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x576: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_576 (off' := 0x578) (by decide)
    (by rw [g8_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x578 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = tbp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
  have g9_10 : reg n9 a0 = op := by rw [u9.regs, upd_ne (by decide) (by decide), g8_10]
  have g9_13 : reg n9 a3 = BitVec.ofNat 32 0x3 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_13]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [u9.regs, upd_ne (by decide) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = sgp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = kp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = sgl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_27 : reg n9 (27 : Fin 32) = tbl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_11 : reg n9 a1 = ol := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w8_48]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m9]; exact w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m9]; exact w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m9]; exact w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m9]; exact w8_38
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m9]; exact w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m9]; exact w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m9]; exact w8_4c
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m9]; exact w8_54
  have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m9]; exact w8_58
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m9]; exact w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m9]; exact w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m9]; exact w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m9]; exact w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m9]; exact w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m9]; exact w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m9]; exact w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m9]; exact w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m9]; exact w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m9]; exact w8_8c
  have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m9]; exact w8_90
  have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m9]; exact w8_94
  have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m9]; exact w8_98
  have w9_9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m9]; exact w8_9c
  have w9_a0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m9]; exact w8_a0
  have w9_a4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m9]; exact w8_a4
  have w9_150 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m9]; exact w8_150
  have w9_154 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m9]; exact w8_154
  have w9_158 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m9]; exact w8_158
  have w9_15c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m9]; exact w8_15c
  clear w8_15c w8_158 w8_154 w8_150 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_4c w8_48 w8_44 w8_38 w8_34 w8_30 w8_2c g8_10 g8_27 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_13 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0x578
  obtain ⟨n10, c10, u10⟩ := s9.block svDp1578 E9.self svDp1578_end
    ⟨trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x580 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svDp1578 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by
    rw [rb10, runBlock_reg _ _ _ sp s9.zero (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (3 : Fin 32) s9.zero (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (4 : Fin 32) s9.zero (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = tbp := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_10 : reg n10 a0 = op := by
    rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
  have g10_11 : reg n10 a1 = ol := by
    rw [rb10, runBlock_reg _ _ _ a1 s9.zero (by decide), g9_11]
  have g10_13 : reg n10 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb10, runBlock_reg _ _ _ a3 s9.zero (by decide), g9_13]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = dg := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = rootp := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = ll := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = sgp := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = kp := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = sgl := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_27 : reg n10 (27 : Fin 32) = tbl := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_12 : reg n10 a2 = BitVec.ofNat 32 (img% svConstExtAddress + 0x9) := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svDp1578, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_10, g9_11, g9_13, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m10]; exact w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m10]; exact w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m10]; exact w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m10]; exact w9_38
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m10]; exact w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m10]; exact w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m10]; exact w9_4c
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m10]; exact w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m10]; exact w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m10]; exact w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m10]; exact w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m10]; exact w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m10]; exact w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m10]; exact w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m10]; exact w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m10]; exact w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m10]; exact w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m10]; exact w9_94
  have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m10]; exact w9_98
  have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m10]; exact w9_9c
  have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m10]; exact w9_a0
  have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m10]; exact w9_a4
  have w10_150 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m10]; exact w9_150
  have w10_154 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m10]; exact w9_154
  have w10_158 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m10]; exact w9_158
  have w10_15c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m10]; exact w9_15c
  clear w9_15c w9_158 w9_154 w9_150 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_4c w9_48 w9_44 w9_38 w9_34 w9_30 w9_2c g9_11 g9_27 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_13 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x580: sv_seqEqF
  obtain ⟨n11, c11, s11, rk11, a0_11, K11, fr11⟩ := sv_seqEqF (pl := ol.toNat) (ql := 3)
    F E10 s10 sv_at_580 sv_at_584 (by decide) (by decide) g10_2
    g10_10 (by rw [g10_11, ofNat_toNat_self]) g10_12 g10_13 (.inl oid_in) (.inr ⟨by decide, by decide⟩)
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keepL K11 (by decide)
  rw [sv_mbRo FW fR10 (.inl oid_in), sv_mbRo FW fR10 (.inr ⟨by decide, by decide⟩)] at a0_11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rk11 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk11 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk11 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk11 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [rk11 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rk11 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rk11 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [rk11 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [rk11 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [rk11 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [rk11 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = kp := by rw [rk11 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [rk11 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_25]
  have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [rk11 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [] := keep_kk10.trans K11
  clear keep_kk10
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K11.w32 (by decide) (by decide)).trans w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K11.w32 (by decide) (by decide)).trans w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K11.w32 (by decide) (by decide)).trans w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K11.w32 (by decide) (by decide)).trans w10_38
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K11.w32 (by decide) (by decide)).trans w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K11.w32 (by decide) (by decide)).trans w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K11.w32 (by decide) (by decide)).trans w10_4c
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K11.w32 (by decide) (by decide)).trans w10_54
  have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K11.w32 (by decide) (by decide)).trans w10_58
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K11.w32 (by decide) (by decide)).trans w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K11.w32 (by decide) (by decide)).trans w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K11.w32 (by decide) (by decide)).trans w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K11.w32 (by decide) (by decide)).trans w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K11.w32 (by decide) (by decide)).trans w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K11.w32 (by decide) (by decide)).trans w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K11.w32 (by decide) (by decide)).trans w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K11.w32 (by decide) (by decide)).trans w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K11.w32 (by decide) (by decide)).trans w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K11.w32 (by decide) (by decide)).trans w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K11.w32 (by decide) (by decide)).trans w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K11.w32 (by decide) (by decide)).trans w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K11.w32 (by decide) (by decide)).trans w10_8c
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K11.w32 (by decide) (by decide)).trans w10_90
  have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K11.w32 (by decide) (by decide)).trans w10_94
  have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K11.w32 (by decide) (by decide)).trans w10_98
  have w11_9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K11.w32 (by decide) (by decide)).trans w10_9c
  have w11_a0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K11.w32 (by decide) (by decide)).trans w10_a0
  have w11_a4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K11.w32 (by decide) (by decide)).trans w10_a4
  have w11_150 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K11.w32 (by decide) (by decide)).trans w10_150
  have w11_154 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K11.w32 (by decide) (by decide)).trans w10_154
  have w11_158 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K11.w32 (by decide) (by decide)).trans w10_158
  have w11_15c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K11.w32 (by decide) (by decide)).trans w10_15c
  clear w10_15c w10_158 w10_154 w10_150 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_4c w10_48 w10_44 w10_38 w10_34 w10_30 w10_2c g10_12 g10_27 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_13 g10_11 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 0 := by rw [a0_11, ite_eq_right heku]; rfl
  -- 0x588: branch, taken
  obtain ⟨n12, d12, u12⟩ := s11.taken E11.self 0x616 sv_at_588
    (by decide) (by rw [g11_10, s11.zero]; decide)
  have s12 : St n12.mem SV n12 0x616 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u12.regs, g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [u12.regs, g11_9]
  have g12_10 : reg n12 a0 = BitVec.ofNat 32 0x0 := by rw [u12.regs, g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [u12.regs, g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [u12.regs, g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [u12.regs, g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [u12.regs, g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = kp := by rw [u12.regs, g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [u12.regs, g11_25]
  have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [u12.regs, g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m12]; exact w11_2c
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m12]; exact w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m12]; exact w11_38
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m12]; exact w11_4c
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m12]; exact w11_54
  have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m12]; exact w11_58
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m12]; exact w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m12]; exact w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m12]; exact w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m12]; exact w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m12]; exact w11_8c
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m12]; exact w11_90
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m12]; exact w11_94
  have w12_98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m12]; exact w11_98
  have w12_9c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m12]; exact w11_9c
  have w12_a0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m12]; exact w11_a0
  have w12_a4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m12]; exact w11_a4
  have w12_150 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m12]; exact w11_150
  have w12_154 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m12]; exact w11_154
  have w12_158 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m12]; exact w11_158
  have w12_15c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m12]; exact w11_15c
  clear w11_15c w11_158 w11_154 w11_150 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_4c w11_48 w11_44 w11_38 w11_34 w11_30 w11_2c g11_27 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 K11 a0_11 rk11 s11 c11
  -- 0x616
  obtain ⟨n13, c13, u13⟩ := s12.block svDp1616 E12.self svDp1616_end
    ⟨trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x618 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svDp1616 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by
    rw [rb13, runBlock_reg _ _ _ sp s12.zero (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (3 : Fin 32) s12.zero (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (4 : Fin 32) s12.zero (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = tbp := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb13, runBlock_reg _ _ _ a0 s12.zero (by decide), g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = dg := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = rootp := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = ll := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = sgp := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = kp := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = sgl := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_27 : reg n13 (27 : Fin 32) = tbl := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_13 : reg n13 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svDp1616, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_10, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m13]; exact w12_2c
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m13]; exact w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m13]; exact w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m13]; exact w12_38
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m13]; exact w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m13]; exact w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m13]; exact w12_4c
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m13]; exact w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m13]; exact w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m13]; exact w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m13]; exact w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m13]; exact w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m13]; exact w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m13]; exact w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m13]; exact w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m13]; exact w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m13]; exact w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m13]; exact w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m13]; exact w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m13]; exact w12_94
  have w13_98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m13]; exact w12_98
  have w13_9c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m13]; exact w12_9c
  have w13_a0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m13]; exact w12_a0
  have w13_a4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m13]; exact w12_a4
  have w13_150 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m13]; exact w12_150
  have w13_154 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m13]; exact w12_154
  have w13_158 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m13]; exact w12_158
  have w13_15c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m13]; exact w12_15c
  clear w12_15c w12_158 w12_154 w12_150 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_4c w12_48 w12_44 w12_38 w12_34 w12_30 w12_2c g12_27 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12 g11_10
  -- 0x618: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_618 (off' := 0x61A) (by decide)
    (by rw [g13_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0x61A (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = tbp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_9]
  have g14_13 : reg n14 a3 = BitVec.ofNat 32 0x3 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_13]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = dg := by rw [u14.regs, upd_ne (by decide) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = rootp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = ll := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = sgp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = kp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = sgl := by rw [u14.regs, upd_ne (by decide) (by decide), g13_25]
  have g14_27 : reg n14 (27 : Fin 32) = tbl := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
  have g14_10 : reg n14 a0 = op := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w13_4c]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m14]; exact w13_2c
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m14]; exact w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m14]; exact w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m14]; exact w13_38
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m14]; exact w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m14]; exact w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m14]; exact w13_4c
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m14]; exact w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m14]; exact w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m14]; exact w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m14]; exact w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m14]; exact w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m14]; exact w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m14]; exact w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m14]; exact w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m14]; exact w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m14]; exact w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m14]; exact w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m14]; exact w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m14]; exact w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m14]; exact w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m14]; exact w13_94
  have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m14]; exact w13_98
  have w14_9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m14]; exact w13_9c
  have w14_a0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m14]; exact w13_a0
  have w14_a4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m14]; exact w13_a4
  have w14_150 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m14]; exact w13_150
  have w14_154 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m14]; exact w13_154
  have w14_158 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m14]; exact w13_158
  have w14_15c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m14]; exact w13_15c
  clear w13_15c w13_158 w13_154 w13_150 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_4c w13_48 w13_44 w13_38 w13_34 w13_30 w13_2c g13_13 g13_27 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x61A: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_61a (off' := 0x61C) (by decide)
    (by rw [g14_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x61C (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = tbp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
  have g15_10 : reg n15 a0 = op := by rw [u15.regs, upd_ne (by decide) (by decide), g14_10]
  have g15_13 : reg n15 a3 = BitVec.ofNat 32 0x3 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_13]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = dg := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = rootp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = ll := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = sgp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = kp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = sgl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_27 : reg n15 (27 : Fin 32) = tbl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_11 : reg n15 a1 = ol := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w14_48]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m15]; exact w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m15]; exact w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m15]; exact w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m15]; exact w14_38
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m15]; exact w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m15]; exact w14_4c
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m15]; exact w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m15]; exact w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m15]; exact w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m15]; exact w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m15]; exact w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m15]; exact w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m15]; exact w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m15]; exact w14_8c
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m15]; exact w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m15]; exact w14_94
  have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m15]; exact w14_98
  have w15_9c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m15]; exact w14_9c
  have w15_a0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m15]; exact w14_a0
  have w15_a4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m15]; exact w14_a4
  have w15_150 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m15]; exact w14_150
  have w15_154 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m15]; exact w14_154
  have w15_158 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m15]; exact w14_158
  have w15_15c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m15]; exact w14_15c
  clear w14_15c w14_158 w14_154 w14_150 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_4c w14_48 w14_44 w14_38 w14_34 w14_30 w14_2c g14_10 g14_27 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_13 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x61C
  obtain ⟨n16, c16, u16⟩ := s15.block svDp161c E15.self svDp161c_end
    ⟨trivial, trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x624 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svDp161c (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by
    rw [rb16, runBlock_reg _ _ _ sp s15.zero (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (3 : Fin 32) s15.zero (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (4 : Fin 32) s15.zero (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb16, runBlock_reg _ _ _ (8 : Fin 32) s15.zero (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = tbp := by
    rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
  have g16_10 : reg n16 a0 = op := by
    rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
  have g16_11 : reg n16 a1 = ol := by
    rw [rb16, runBlock_reg _ _ _ a1 s15.zero (by decide), g15_11]
  have g16_13 : reg n16 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb16, runBlock_reg _ _ _ a3 s15.zero (by decide), g15_13]
  have g16_18 : reg n16 (18 : Fin 32) = out := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by
    rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = dg := by
    rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = rootp := by
    rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = ll := by
    rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = sgp := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = kp := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = sgl := by
    rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
  have g16_27 : reg n16 (27 : Fin 32) = tbl := by
    rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
  have g16_12 : reg n16 a2 = BitVec.ofNat 32 (img% svConstExtAddress + 0x6) := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svDp161c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_9, g15_10, g15_11, g15_13, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk16 : SvKeepL B n0.mem n16.mem [] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m16]; exact w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m16]; exact w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m16]; exact w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m16]; exact w15_38
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m16]; exact w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m16]; exact w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m16]; exact w15_4c
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m16]; exact w15_54
  have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m16]; exact w15_58
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m16]; exact w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m16]; exact w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m16]; exact w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m16]; exact w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m16]; exact w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m16]; exact w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m16]; exact w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m16]; exact w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m16]; exact w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m16]; exact w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m16]; exact w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m16]; exact w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m16]; exact w15_8c
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m16]; exact w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m16]; exact w15_94
  have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m16]; exact w15_98
  have w16_9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m16]; exact w15_9c
  have w16_a0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m16]; exact w15_a0
  have w16_a4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m16]; exact w15_a4
  have w16_150 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m16]; exact w15_150
  have w16_154 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m16]; exact w15_154
  have w16_158 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m16]; exact w15_158
  have w16_15c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m16]; exact w15_15c
  clear w15_15c w15_158 w15_154 w15_150 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_4c w15_48 w15_44 w15_38 w15_34 w15_30 w15_2c g15_11 g15_27 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_13 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x624: sv_seqEqF
  obtain ⟨n17, c17, s17, rk17, a0_17, K17, fr17⟩ := sv_seqEqF (pl := ol.toNat) (ql := 3)
    F E16 s16 sv_at_624 sv_at_628 (by decide) (by decide) g16_2
    g16_10 (by rw [g16_11, ofNat_toNat_self]) g16_12 g16_13 (.inl oid_in) (.inr ⟨by decide, by decide⟩)
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keepL K17 (by decide)
  rw [sv_mbRo FW fR16 (.inl oid_in), sv_mbRo FW fR16 (.inr ⟨by decide, by decide⟩)] at a0_17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rk17 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk17 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk17 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk17 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = tbp := by rw [rk17 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rk17 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rk17 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [rk17 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [rk17 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [rk17 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = sgp := by rw [rk17 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = kp := by rw [rk17 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = sgl := by rw [rk17 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_25]
  have g17_27 : reg n17 (27 : Fin 32) = tbl := by rw [rk17 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [] := keep_kk16.trans K17
  clear keep_kk16
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K17.w32 (by decide) (by decide)).trans w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K17.w32 (by decide) (by decide)).trans w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K17.w32 (by decide) (by decide)).trans w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K17.w32 (by decide) (by decide)).trans w16_38
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K17.w32 (by decide) (by decide)).trans w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K17.w32 (by decide) (by decide)).trans w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K17.w32 (by decide) (by decide)).trans w16_4c
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K17.w32 (by decide) (by decide)).trans w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K17.w32 (by decide) (by decide)).trans w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K17.w32 (by decide) (by decide)).trans w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K17.w32 (by decide) (by decide)).trans w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K17.w32 (by decide) (by decide)).trans w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K17.w32 (by decide) (by decide)).trans w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K17.w32 (by decide) (by decide)).trans w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K17.w32 (by decide) (by decide)).trans w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K17.w32 (by decide) (by decide)).trans w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K17.w32 (by decide) (by decide)).trans w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K17.w32 (by decide) (by decide)).trans w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K17.w32 (by decide) (by decide)).trans w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K17.w32 (by decide) (by decide)).trans w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K17.w32 (by decide) (by decide)).trans w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K17.w32 (by decide) (by decide)).trans w16_8c
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K17.w32 (by decide) (by decide)).trans w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K17.w32 (by decide) (by decide)).trans w16_94
  have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K17.w32 (by decide) (by decide)).trans w16_98
  have w17_9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K17.w32 (by decide) (by decide)).trans w16_9c
  have w17_a0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K17.w32 (by decide) (by decide)).trans w16_a0
  have w17_a4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K17.w32 (by decide) (by decide)).trans w16_a4
  have w17_150 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K17.w32 (by decide) (by decide)).trans w16_150
  have w17_154 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K17.w32 (by decide) (by decide)).trans w16_154
  have w17_158 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K17.w32 (by decide) (by decide)).trans w16_158
  have w17_15c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K17.w32 (by decide) (by decide)).trans w16_15c
  clear w16_15c w16_158 w16_154 w16_150 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_4c w16_48 w16_44 w16_38 w16_34 w16_30 w16_2c g16_12 g16_27 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_13 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  have g17_10 : reg n17 a0 = BitVec.ofNat 32 0 := by rw [a0_17, ite_eq_right hbc]; rfl
  -- 0x62C: branch, taken
  obtain ⟨n18, d18, u18⟩ := s17.taken E17.self 0x6F2 sv_at_62c
    (by decide) (by rw [g17_10, s17.zero]; decide)
  have s18 : St n18.mem SV n18 0x6F2 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u18.regs, g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = tbp := by rw [u18.regs, g17_9]
  have g18_10 : reg n18 a0 = BitVec.ofNat 32 0x0 := by rw [u18.regs, g17_10]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = sgp := by rw [u18.regs, g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = kp := by rw [u18.regs, g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = sgl := by rw [u18.regs, g17_25]
  have g18_27 : reg n18 (27 : Fin 32) = tbl := by rw [u18.regs, g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m18]; exact w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m18]; exact w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m18]; exact w17_38
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m18]; exact w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m18]; exact w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m18]; exact w17_4c
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m18]; exact w17_54
  have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m18]; exact w17_58
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m18]; exact w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m18]; exact w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m18]; exact w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m18]; exact w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m18]; exact w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m18]; exact w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m18]; exact w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m18]; exact w17_8c
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m18]; exact w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m18]; exact w17_94
  have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m18]; exact w17_98
  have w18_9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m18]; exact w17_9c
  have w18_a0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m18]; exact w17_a0
  have w18_a4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m18]; exact w17_a4
  have w18_150 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m18]; exact w17_150
  have w18_154 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m18]; exact w17_154
  have w18_158 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m18]; exact w17_158
  have w18_15c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m18]; exact w17_15c
  clear w17_15c w17_158 w17_154 w17_150 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_4c w17_48 w17_44 w17_38 w17_34 w17_30 w17_2c g17_27 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 K17 a0_17 rk17 s17 c17
  -- 0x6F2
  obtain ⟨n19, c19, u19⟩ := s18.block svDp16f2 E18.self svDp16f2_end
    ⟨trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x6F4 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svDp16f2 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by
    rw [rb19, runBlock_reg _ _ _ sp s18.zero (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (3 : Fin 32) s18.zero (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (4 : Fin 32) s18.zero (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = tbp := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = dg := by
    rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = rootp := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = ll := by
    rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = sgp := by
    rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = kp := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = sgl := by
    rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
  have g19_27 : reg n19 (27 : Fin 32) = tbl := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_10 : reg n19 a0 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svDp16f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_10, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_27, s18.zero])
    all_goals (try simp only [BitVec.ofNat_eq_ofNat])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m19]; exact w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m19]; exact w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m19]; exact w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m19]; exact w18_38
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m19]; exact w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m19]; exact w18_4c
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m19]; exact w18_54
  have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m19]; exact w18_58
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m19]; exact w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m19]; exact w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m19]; exact w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m19]; exact w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m19]; exact w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m19]; exact w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m19]; exact w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m19]; exact w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m19]; exact w18_8c
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m19]; exact w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m19]; exact w18_94
  have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m19]; exact w18_98
  have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m19]; exact w18_9c
  have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m19]; exact w18_a0
  have w19_a4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m19]; exact w18_a4
  have w19_150 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m19]; exact w18_150
  have w19_154 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m19]; exact w18_154
  have w19_158 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m19]; exact w18_158
  have w19_15c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m19]; exact w18_15c
  clear w18_15c w18_158 w18_154 w18_150 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_4c w18_48 w18_44 w18_38 w18_34 w18_30 w18_2c g18_27 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18 g17_10
  -- 0x6F4: sw
  obtain ⟨n20, d20, s20, fr20, K20, W20, rg20⟩ := sv_sw F E19 s19 sv_at_6f4 (off' := 0x6F6) (c := 0x50)
    (by decide) (by rw [g19_2]; sv_addr) (by decide) (by decide)
  have t20 : Steps n0 n20 := t19.trans d20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keep K20 (by decide)
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [rg20 sp, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg20 (3 : Fin 32), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg20 (4 : Fin 32), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg20 (8 : Fin 32), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = tbp := by rw [rg20 (9 : Fin 32), g19_9]
  have g20_10 : reg n20 a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [rg20 a0, g19_10]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rg20 (18 : Fin 32), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rg20 (19 : Fin 32), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = dg := by rw [rg20 (20 : Fin 32), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = rootp := by rw [rg20 (21 : Fin 32), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = ll := by rw [rg20 (22 : Fin 32), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = sgp := by rw [rg20 (23 : Fin 32), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = kp := by rw [rg20 (24 : Fin 32), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = sgl := by rw [rg20 (25 : Fin 32), g19_25]
  have g20_27 : reg n20 (27 : Fin 32) = tbl := by rw [rg20 (27 : Fin 32), g19_27]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x50, 0x4)] := keep_kk19.trans K20.toL
  clear keep_kk19
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K20.w32 (by decide) (by decide)).trans w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K20.w32 (by decide) (by decide)).trans w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K20.w32 (by decide) (by decide)).trans w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K20.w32 (by decide) (by decide)).trans w19_38
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K20.w32 (by decide) (by decide)).trans w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K20.w32 (by decide) (by decide)).trans w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K20.w32 (by decide) (by decide)).trans w19_4c
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K20.w32 (by decide) (by decide)).trans w19_54
  have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K20.w32 (by decide) (by decide)).trans w19_58
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K20.w32 (by decide) (by decide)).trans w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K20.w32 (by decide) (by decide)).trans w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K20.w32 (by decide) (by decide)).trans w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K20.w32 (by decide) (by decide)).trans w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K20.w32 (by decide) (by decide)).trans w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K20.w32 (by decide) (by decide)).trans w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K20.w32 (by decide) (by decide)).trans w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K20.w32 (by decide) (by decide)).trans w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K20.w32 (by decide) (by decide)).trans w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K20.w32 (by decide) (by decide)).trans w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K20.w32 (by decide) (by decide)).trans w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K20.w32 (by decide) (by decide)).trans w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K20.w32 (by decide) (by decide)).trans w19_8c
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K20.w32 (by decide) (by decide)).trans w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K20.w32 (by decide) (by decide)).trans w19_94
  have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K20.w32 (by decide) (by decide)).trans w19_98
  have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K20.w32 (by decide) (by decide)).trans w19_9c
  have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K20.w32 (by decide) (by decide)).trans w19_a0
  have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K20.w32 (by decide) (by decide)).trans w19_a4
  have w20_150 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K20.w32 (by decide) (by decide)).trans w19_150
  have w20_154 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K20.w32 (by decide) (by decide)).trans w19_154
  have w20_158 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K20.w32 (by decide) (by decide)).trans w19_158
  have w20_15c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K20.w32 (by decide) (by decide)).trans w19_15c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [W20, g19_10]
  clear w19_15c w19_158 w19_154 w19_150 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_4c w19_48 w19_44 w19_38 w19_34 w19_30 w19_2c g19_10 g19_27 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x6F6
  obtain ⟨n21, c21, u21⟩ := s20.block svDp16f6 E20.self svDp16f6_end
    ⟨trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x6FE (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svDp16f6 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by
    rw [rb21, runBlock_reg _ _ _ sp s20.zero (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (3 : Fin 32) s20.zero (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (4 : Fin 32) s20.zero (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = tbp := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_10 : reg n21 a0 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb21, runBlock_reg _ _ _ a0 s20.zero (by decide), g20_10]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = dg := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = rootp := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = ll := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = sgp := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = kp := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = sgl := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_27 : reg n21 (27 : Fin 32) = tbl := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_26 : reg n21 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svDp16f6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_10, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x50, 0x4)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m21]; exact w20_2c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m21]; exact w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m21]; exact w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m21]; exact w20_38
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m21]; exact w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m21]; exact w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m21]; exact w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m21]; exact w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m21]; exact w20_54
  have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m21]; exact w20_58
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m21]; exact w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m21]; exact w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m21]; exact w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m21]; exact w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m21]; exact w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m21]; exact w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m21]; exact w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m21]; exact w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m21]; exact w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m21]; exact w20_8c
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m21]; exact w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m21]; exact w20_94
  have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m21]; exact w20_98
  have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m21]; exact w20_9c
  have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m21]; exact w20_a0
  have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m21]; exact w20_a4
  have w21_150 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m21]; exact w20_150
  have w21_154 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m21]; exact w20_154
  have w21_158 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m21]; exact w20_158
  have w21_15c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m21]; exact w20_15c
  clear w20_50 w20_15c w20_158 w20_154 w20_150 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_4c w20_48 w20_44 w20_38 w20_34 w20_30 w20_2c g20_27 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 rg20 W20 K20 fr20 s20 d20
  -- 0x6FE
  obtain ⟨n22, c22, u22⟩ := s21.block svDp16fe E21.self svDp16fe_end
    ⟨trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0x700 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svDp16fe (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by
    rw [rb22, runBlock_reg _ _ _ sp s21.zero (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (3 : Fin 32) s21.zero (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (4 : Fin 32) s21.zero (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = tbp := by
    rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = dg := by
    rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = rootp := by
    rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = ll := by
    rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = sgp := by
    rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = kp := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = sgl := by
    rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = tbl := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x4 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svDp16fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x50, 0x4)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m22]; exact w21_2c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m22]; exact w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m22]; exact w21_38
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m22]; exact w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m22]; exact w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m22]; exact w21_50
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m22]; exact w21_54
  have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m22]; exact w21_58
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m22]; exact w21_5c
  have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m22]; exact w21_60
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m22]; exact w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m22]; exact w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m22]; exact w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m22]; exact w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m22]; exact w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m22]; exact w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m22]; exact w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m22]; exact w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m22]; exact w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m22]; exact w21_8c
  have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m22]; exact w21_90
  have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m22]; exact w21_94
  have w22_98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m22]; exact w21_98
  have w22_9c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m22]; exact w21_9c
  have w22_a0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m22]; exact w21_a0
  have w22_a4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m22]; exact w21_a4
  have w22_150 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m22]; exact w21_150
  have w22_154 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m22]; exact w21_154
  have w22_158 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m22]; exact w21_158
  have w22_15c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m22]; exact w21_15c
  clear w21_15c w21_158 w21_154 w21_150 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_38 w21_34 w21_30 w21_2c g21_26 g21_27 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x700: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_700 (off' := 0x702) (by decide)
    (by rw [g22_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x702 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x4 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = kp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_11 : reg n23 a1 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w22_50]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x50, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m23]; exact w22_2c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m23]; exact w22_38
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m23]; exact w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m23]; exact w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m23]; exact w22_50
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m23]; exact w22_54
  have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m23]; exact w22_58
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m23]; exact w22_5c
  have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m23]; exact w22_60
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m23]; exact w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m23]; exact w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m23]; exact w22_8c
  have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m23]; exact w22_90
  have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m23]; exact w22_94
  have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m23]; exact w22_98
  have w23_9c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m23]; exact w22_9c
  have w23_a0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m23]; exact w22_a0
  have w23_a4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m23]; exact w22_a4
  have w23_150 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m23]; exact w22_150
  have w23_154 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m23]; exact w22_154
  have w23_158 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m23]; exact w22_158
  have w23_15c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m23]; exact w22_15c
  clear w22_15c w22_158 w22_154 w22_150 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_38 w22_34 w22_30 w22_2c g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0x702: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0x706 sv_at_702
    (by decide) (by rw [g23_11, g23_10]; decide)
  have s24 : St n24.mem SV n24 0x706 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [u24.regs, g23_9]
  have g24_10 : reg n24 a0 = BitVec.ofNat 32 0x4 := by rw [u24.regs, g23_10]
  have g24_11 : reg n24 a1 = BitVec.ofNat 32 0xFFFFFFFF := by rw [u24.regs, g23_11]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [u24.regs, g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [u24.regs, g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = kp := by rw [u24.regs, g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [u24.regs, g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x50, 0x4)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m24]; exact w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m24]; exact w23_38
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m24]; exact w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m24]; exact w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m24]; exact w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m24]; exact w23_54
  have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m24]; exact w23_58
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m24]; exact w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m24]; exact w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m24]; exact w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m24]; exact w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m24]; exact w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m24]; exact w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m24]; exact w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m24]; exact w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m24]; exact w23_8c
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m24]; exact w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m24]; exact w23_94
  have w24_98 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m24]; exact w23_98
  have w24_9c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m24]; exact w23_9c
  have w24_a0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m24]; exact w23_a0
  have w24_a4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m24]; exact w23_a4
  have w24_150 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m24]; exact w23_150
  have w24_154 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m24]; exact w23_154
  have w24_158 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m24]; exact w23_158
  have w24_15c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m24]; exact w23_15c
  clear w23_15c w23_158 w23_154 w23_150 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_38 w23_34 w23_30 w23_2c g23_11 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x706: lw of a constant
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_706 (off' := 0x70A) (by decide)
    (by rw [g24_26]; decide)
  have s25 : St n25.mem SV n25 0x70A (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = tbp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
  have g25_11 : reg n25 a1 = BitVec.ofNat 32 0xFFFFFFFF := by rw [u25.regs, upd_ne (by decide) (by decide), g24_11]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = sgp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = kp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = tbl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
  have g25_10 : reg n25 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x2D) := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_26, show BitVec.ofNat 32 (img% svConstExtAddress + 0x61) + 0x0 = BitVec.ofNat 32 svConstExtAddress + BitVec.ofNat 32 0x61 by decide]
    exact CodeIn.w32 (SvData.sv FW SD0 fR24).ext (by decide) (by decide)
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x50, 0x4)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m25]; exact w24_2c
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m25]; exact w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m25]; exact w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m25]; exact w24_38
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m25]; exact w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m25]; exact w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m25]; exact w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m25]; exact w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m25]; exact w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m25]; exact w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m25]; exact w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m25]; exact w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m25]; exact w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m25]; exact w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m25]; exact w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m25]; exact w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m25]; exact w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m25]; exact w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m25]; exact w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m25]; exact w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m25]; exact w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m25]; exact w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m25]; exact w24_8c
  have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m25]; exact w24_90
  have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m25]; exact w24_94
  have w25_98 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m25]; exact w24_98
  have w25_9c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m25]; exact w24_9c
  have w25_a0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m25]; exact w24_a0
  have w25_a4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m25]; exact w24_a4
  have w25_150 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m25]; exact w24_150
  have w25_154 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m25]; exact w24_154
  have w25_158 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m25]; exact w24_158
  have w25_15c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m25]; exact w24_15c
  clear w24_15c w24_158 w24_154 w24_150 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_38 w24_34 w24_30 w24_2c g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_11 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x70A
  obtain ⟨n26, c26, u26⟩ := s25.block svDp170a E25.self svDp170a_end
    ⟨trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem SV n26 0x70C (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock svDp170a (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by
    rw [rb26, runBlock_reg _ _ _ sp s25.zero (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (3 : Fin 32) s25.zero (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (4 : Fin 32) s25.zero (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = tbp := by
    rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
  have g26_10 : reg n26 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x2D) := by
    rw [rb26, runBlock_reg _ _ _ a0 s25.zero (by decide), g25_10]
  have g26_18 : reg n26 (18 : Fin 32) = out := by
    rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by
    rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = dg := by
    rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = rootp := by
    rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = ll := by
    rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = sgp := by
    rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = kp := by
    rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = sgl := by
    rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = tbl := by
    rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
  have g26_11 : reg n26 a1 = BitVec.ofNat 32 0xA := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svDp170a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x50, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m26]; exact w25_2c
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m26]; exact w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m26]; exact w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m26]; exact w25_38
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m26]; exact w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m26]; exact w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m26]; exact w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m26]; exact w25_50
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m26]; exact w25_54
  have w26_58 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m26]; exact w25_58
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m26]; exact w25_5c
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m26]; exact w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m26]; exact w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m26]; exact w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m26]; exact w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m26]; exact w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m26]; exact w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m26]; exact w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m26]; exact w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m26]; exact w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m26]; exact w25_8c
  have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m26]; exact w25_90
  have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m26]; exact w25_94
  have w26_98 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m26]; exact w25_98
  have w26_9c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m26]; exact w25_9c
  have w26_a0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m26]; exact w25_a0
  have w26_a4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m26]; exact w25_a4
  have w26_150 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m26]; exact w25_150
  have w26_154 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m26]; exact w25_154
  have w26_158 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m26]; exact w25_158
  have w26_15c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m26]; exact w25_15c
  clear w25_15c w25_158 w25_154 w25_150 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_38 w25_34 w25_30 w25_2c g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_11 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x70C: lw
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_70c (off' := 0x70E) (by decide)
    (by rw [g26_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s27 : St n27.mem SV n27 0x70E (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = tbp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x2D) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_10]
  have g27_11 : reg n27 a1 = BitVec.ofNat 32 0xA := by rw [u27.regs, upd_ne (by decide) (by decide), g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = dg := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = rootp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = ll := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = sgp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = kp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = sgl := by rw [u27.regs, upd_ne (by decide) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = tbl := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
  have g27_12 : reg n27 a2 = op := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w26_4c]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x50, 0x4)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m27]; exact w26_2c
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m27]; exact w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m27]; exact w26_38
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m27]; exact w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m27]; exact w26_48
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m27]; exact w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m27]; exact w26_50
  have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m27]; exact w26_54
  have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m27]; exact w26_58
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m27]; exact w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m27]; exact w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m27]; exact w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m27]; exact w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m27]; exact w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m27]; exact w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m27]; exact w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m27]; exact w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m27]; exact w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m27]; exact w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m27]; exact w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m27]; exact w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m27]; exact w26_8c
  have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m27]; exact w26_90
  have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m27]; exact w26_94
  have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m27]; exact w26_98
  have w27_9c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m27]; exact w26_9c
  have w27_a0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m27]; exact w26_a0
  have w27_a4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m27]; exact w26_a4
  have w27_150 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m27]; exact w26_150
  have w27_154 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m27]; exact w26_154
  have w27_158 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m27]; exact w26_158
  have w27_15c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m27]; exact w26_15c
  clear w26_15c w26_158 w26_154 w26_150 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_38 w26_34 w26_30 w26_2c g26_11 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
  -- 0x70E: lw
  obtain ⟨n28, d28, u28⟩ := s27.lw E27.self sv_at_70e (off' := 0x710) (by decide)
    (by rw [g27_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s28 : St n28.mem SV n28 0x710 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = tbp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x2D) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_10]
  have g28_11 : reg n28 a1 = BitVec.ofNat 32 0xA := by rw [u28.regs, upd_ne (by decide) (by decide), g27_11]
  have g28_12 : reg n28 a2 = op := by rw [u28.regs, upd_ne (by decide) (by decide), g27_12]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [u28.regs, upd_ne (by decide) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [u28.regs, upd_ne (by decide) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = sgp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = kp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = sgl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = tbl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
  have g28_13 : reg n28 a3 = ol := by
    rw [u28.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g27_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w27_48]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x50, 0x4)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m28]; exact w27_2c
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m28]; exact w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m28]; exact w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m28]; exact w27_38
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m28]; exact w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m28]; exact w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m28]; exact w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m28]; exact w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m28]; exact w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m28]; exact w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m28]; exact w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m28]; exact w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m28]; exact w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m28]; exact w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m28]; exact w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m28]; exact w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m28]; exact w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m28]; exact w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m28]; exact w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m28]; exact w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m28]; exact w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m28]; exact w27_88
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m28]; exact w27_8c
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m28]; exact w27_90
  have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m28]; exact w27_94
  have w28_98 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m28]; exact w27_98
  have w28_9c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m28]; exact w27_9c
  have w28_a0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m28]; exact w27_a0
  have w28_a4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m28]; exact w27_a4
  have w28_150 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m28]; exact w27_150
  have w28_154 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m28]; exact w27_154
  have w28_158 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m28]; exact w27_158
  have w28_15c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m28]; exact w27_15c
  clear w27_15c w27_158 w27_154 w27_150 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_38 w27_34 w27_30 w27_2c g27_12 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0x710: sv_seqEqF
  obtain ⟨n29, c29, s29, rk29, a0_29, K29, fr29⟩ := sv_seqEqF (pl := 10) (ql := ol.toNat)
    F E28 s28 sv_at_710 sv_at_714 (by decide) (by decide) g28_2
    g28_10 g28_11 g28_12 (by rw [g28_13, ofNat_toNat_self]) (.inr ⟨by decide, by decide⟩) (.inl oid_in)
  have t29 : Steps n0 n29 := t28.trans c29
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.keepL K29 (by decide)
  rw [sv_mbRo FW fR28 (.inr ⟨by decide, by decide⟩), sv_mbRo FW fR28 (.inl oid_in)] at a0_29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [rk29 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk29 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk29 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk29 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = tbp := by rw [rk29 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [rk29 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [rk29 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = dg := by rw [rk29 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = rootp := by rw [rk29 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = ll := by rw [rk29 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = sgp := by rw [rk29 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = kp := by rw [rk29 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = sgl := by rw [rk29 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by rw [rk29 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = tbl := by rw [rk29 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g28_27]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x50, 0x4)] := keep_kk28.trans K29
  clear keep_kk28
  have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K29.w32 (by decide) (by decide)).trans w28_2c
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K29.w32 (by decide) (by decide)).trans w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K29.w32 (by decide) (by decide)).trans w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K29.w32 (by decide) (by decide)).trans w28_38
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K29.w32 (by decide) (by decide)).trans w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K29.w32 (by decide) (by decide)).trans w28_48
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K29.w32 (by decide) (by decide)).trans w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := (K29.w32 (by decide) (by decide)).trans w28_50
  have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K29.w32 (by decide) (by decide)).trans w28_54
  have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K29.w32 (by decide) (by decide)).trans w28_58
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K29.w32 (by decide) (by decide)).trans w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K29.w32 (by decide) (by decide)).trans w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K29.w32 (by decide) (by decide)).trans w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K29.w32 (by decide) (by decide)).trans w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K29.w32 (by decide) (by decide)).trans w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K29.w32 (by decide) (by decide)).trans w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K29.w32 (by decide) (by decide)).trans w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K29.w32 (by decide) (by decide)).trans w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K29.w32 (by decide) (by decide)).trans w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K29.w32 (by decide) (by decide)).trans w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K29.w32 (by decide) (by decide)).trans w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K29.w32 (by decide) (by decide)).trans w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K29.w32 (by decide) (by decide)).trans w28_8c
  have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K29.w32 (by decide) (by decide)).trans w28_90
  have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K29.w32 (by decide) (by decide)).trans w28_94
  have w29_98 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K29.w32 (by decide) (by decide)).trans w28_98
  have w29_9c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K29.w32 (by decide) (by decide)).trans w28_9c
  have w29_a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K29.w32 (by decide) (by decide)).trans w28_a0
  have w29_a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K29.w32 (by decide) (by decide)).trans w28_a4
  have w29_150 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K29.w32 (by decide) (by decide)).trans w28_150
  have w29_154 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K29.w32 (by decide) (by decide)).trans w28_154
  have w29_158 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K29.w32 (by decide) (by decide)).trans w28_158
  have w29_15c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K29.w32 (by decide) (by decide)).trans w28_15c
  clear w28_15c w28_158 w28_154 w28_150 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_38 w28_34 w28_30 w28_2c g28_13 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_12 g28_11 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 0 := by rw [a0_29, ite_eq_right hp0]; rfl
  -- 0x718: lw
  obtain ⟨n30, d30, u30⟩ := s29.lw E29.self sv_at_718 (off' := 0x71A) (by decide)
    (by rw [g29_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s30 : St n30.mem SV n30 0x71A (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = tbp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_9]
  have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x0 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, upd_ne (by decide) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [u30.regs, upd_ne (by decide) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [u30.regs, upd_ne (by decide) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = sgp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = kp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = sgl := by rw [u30.regs, upd_ne (by decide) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = tbl := by rw [u30.regs, upd_ne (by decide) (by decide), g29_27]
  have g30_11 : reg n30 a1 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [u30.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g29_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w29_50]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x50, 0x4)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m30]; exact w29_2c
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m30]; exact w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m30]; exact w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m30]; exact w29_38
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m30]; exact w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m30]; exact w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m30]; exact w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m30]; exact w29_50
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m30]; exact w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m30]; exact w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m30]; exact w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m30]; exact w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m30]; exact w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m30]; exact w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m30]; exact w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m30]; exact w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m30]; exact w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m30]; exact w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m30]; exact w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m30]; exact w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m30]; exact w29_84
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m30]; exact w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m30]; exact w29_8c
  have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m30]; exact w29_90
  have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m30]; exact w29_94
  have w30_98 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m30]; exact w29_98
  have w30_9c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m30]; exact w29_9c
  have w30_a0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m30]; exact w29_a0
  have w30_a4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m30]; exact w29_a4
  have w30_150 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m30]; exact w29_150
  have w30_154 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m30]; exact w29_154
  have w30_158 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m30]; exact w29_158
  have w30_15c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m30]; exact w29_15c
  clear w29_15c w29_158 w29_154 w29_150 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_38 w29_34 w29_30 w29_2c g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 K29 a0_29 rk29 s29 c29
  -- 0x71A
  obtain ⟨n31, c31, u31⟩ := s30.block svDp171a E30.self svDp171a_end
    ⟨trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem SV n31 0x71C (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock svDp171a (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans c31
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by
    rw [rb31, runBlock_reg _ _ _ sp s30.zero (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (3 : Fin 32) s30.zero (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (4 : Fin 32) s30.zero (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb31, runBlock_reg _ _ _ (8 : Fin 32) s30.zero (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = tbp := by
    rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
  have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb31, runBlock_reg _ _ _ a0 s30.zero (by decide), g30_10]
  have g31_18 : reg n31 (18 : Fin 32) = out := by
    rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by
    rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = dg := by
    rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = rootp := by
    rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = ll := by
    rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = sgp := by
    rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = kp := by
    rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = sgl := by
    rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by
    rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = tbl := by
    rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
  have g31_11 : reg n31 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svDp171a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_11, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x50, 0x4)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m31]; exact w30_2c
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m31]; exact w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m31]; exact w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m31]; exact w30_38
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m31]; exact w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m31]; exact w30_48
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m31]; exact w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m31]; exact w30_50
  have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m31]; exact w30_54
  have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m31]; exact w30_58
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m31]; exact w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m31]; exact w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m31]; exact w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m31]; exact w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m31]; exact w30_70
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m31]; exact w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m31]; exact w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m31]; exact w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m31]; exact w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m31]; exact w30_84
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m31]; exact w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m31]; exact w30_8c
  have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m31]; exact w30_90
  have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m31]; exact w30_94
  have w31_98 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m31]; exact w30_98
  have w31_9c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m31]; exact w30_9c
  have w31_a0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m31]; exact w30_a0
  have w31_a4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m31]; exact w30_a4
  have w31_150 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m31]; exact w30_150
  have w31_154 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m31]; exact w30_154
  have w31_158 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m31]; exact w30_158
  have w31_15c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m31]; exact w30_15c
  clear w30_15c w30_158 w30_154 w30_150 w30_a4 w30_a0 w30_9c w30_98 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_44 w30_38 w30_34 w30_30 w30_2c g30_11 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30 g29_10
  -- 0x71C: sw
  obtain ⟨n32, d32, s32, fr32, K32, W32, rg32⟩ := sv_sw F E31 s31 sv_at_71c (off' := 0x71E) (c := 0x50)
    (by decide) (by rw [g31_2]; sv_addr) (by decide) (by decide)
  have t32 : Steps n0 n32 := t31.trans d32
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.keep K32 (by decide)
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [rg32 sp, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg32 (3 : Fin 32), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg32 (4 : Fin 32), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg32 (8 : Fin 32), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [rg32 (9 : Fin 32), g31_9]
  have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x0 := by rw [rg32 a0, g31_10]
  have g32_11 : reg n32 a1 = BitVec.ofNat 32 0x0 := by rw [rg32 a1, g31_11]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [rg32 (18 : Fin 32), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [rg32 (19 : Fin 32), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [rg32 (20 : Fin 32), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [rg32 (21 : Fin 32), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [rg32 (22 : Fin 32), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [rg32 (23 : Fin 32), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = kp := by rw [rg32 (24 : Fin 32), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [rg32 (25 : Fin 32), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x61) := by rw [rg32 (26 : Fin 32), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [rg32 (27 : Fin 32), g31_27]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x50, 0x4), (0x50, 0x4)] := keep_kk31.trans K32.toL
  clear keep_kk31
  have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K32.w32 (by decide) (by decide)).trans w31_2c
  have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K32.w32 (by decide) (by decide)).trans w31_30
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K32.w32 (by decide) (by decide)).trans w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K32.w32 (by decide) (by decide)).trans w31_38
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K32.w32 (by decide) (by decide)).trans w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K32.w32 (by decide) (by decide)).trans w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K32.w32 (by decide) (by decide)).trans w31_4c
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K32.w32 (by decide) (by decide)).trans w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K32.w32 (by decide) (by decide)).trans w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K32.w32 (by decide) (by decide)).trans w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K32.w32 (by decide) (by decide)).trans w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K32.w32 (by decide) (by decide)).trans w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K32.w32 (by decide) (by decide)).trans w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K32.w32 (by decide) (by decide)).trans w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K32.w32 (by decide) (by decide)).trans w31_70
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K32.w32 (by decide) (by decide)).trans w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K32.w32 (by decide) (by decide)).trans w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K32.w32 (by decide) (by decide)).trans w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K32.w32 (by decide) (by decide)).trans w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K32.w32 (by decide) (by decide)).trans w31_84
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K32.w32 (by decide) (by decide)).trans w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K32.w32 (by decide) (by decide)).trans w31_8c
  have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K32.w32 (by decide) (by decide)).trans w31_90
  have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K32.w32 (by decide) (by decide)).trans w31_94
  have w32_98 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K32.w32 (by decide) (by decide)).trans w31_98
  have w32_9c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K32.w32 (by decide) (by decide)).trans w31_9c
  have w32_a0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K32.w32 (by decide) (by decide)).trans w31_a0
  have w32_a4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K32.w32 (by decide) (by decide)).trans w31_a4
  have w32_150 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K32.w32 (by decide) (by decide)).trans w31_150
  have w32_154 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K32.w32 (by decide) (by decide)).trans w31_154
  have w32_158 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K32.w32 (by decide) (by decide)).trans w31_158
  have w32_15c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K32.w32 (by decide) (by decide)).trans w31_15c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [W32, g31_11]
  clear w31_15c w31_158 w31_154 w31_150 w31_a4 w31_a0 w31_9c w31_98 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_44 w31_38 w31_34 w31_30 w31_2c g31_11 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
  -- 0x71E
  obtain ⟨n33, c33, u33⟩ := s32.block svDp171e E32.self svDp171e_end
    ⟨trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0x720 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svDp171e (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans c33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by
    rw [rb33, runBlock_reg _ _ _ sp s32.zero (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (3 : Fin 32) s32.zero (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (4 : Fin 32) s32.zero (by decide), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb33, runBlock_reg _ _ _ (8 : Fin 32) s32.zero (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = tbp := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb33, runBlock_reg _ _ _ a0 s32.zero (by decide), g32_10]
  have g33_11 : reg n33 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb33, runBlock_reg _ _ _ a1 s32.zero (by decide), g32_11]
  have g33_18 : reg n33 (18 : Fin 32) = out := by
    rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by
    rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = dg := by
    rw [rb33, runBlock_reg _ _ _ (20 : Fin 32) s32.zero (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = rootp := by
    rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = ll := by
    rw [rb33, runBlock_reg _ _ _ (22 : Fin 32) s32.zero (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = sgp := by
    rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = kp := by
    rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = sgl := by
    rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
  have g33_27 : reg n33 (27 : Fin 32) = tbl := by
    rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
  have g33_26 : reg n33 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svDp171e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_11, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m33]; exact w32_2c
  have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m33]; exact w32_30
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m33]; exact w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m33]; exact w32_38
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m33]; exact w32_44
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m33]; exact w32_48
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m33]; exact w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m33]; exact w32_50
  have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m33]; exact w32_54
  have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m33]; exact w32_58
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m33]; exact w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m33]; exact w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m33]; exact w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m33]; exact w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m33]; exact w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m33]; exact w32_70
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m33]; exact w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m33]; exact w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m33]; exact w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m33]; exact w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m33]; exact w32_84
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m33]; exact w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m33]; exact w32_8c
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m33]; exact w32_90
  have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m33]; exact w32_94
  have w33_98 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m33]; exact w32_98
  have w33_9c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m33]; exact w32_9c
  have w33_a0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m33]; exact w32_a0
  have w33_a4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m33]; exact w32_a4
  have w33_150 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m33]; exact w32_150
  have w33_154 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m33]; exact w32_154
  have w33_158 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m33]; exact w32_158
  have w33_15c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m33]; exact w32_15c
  clear w32_50 w32_15c w32_158 w32_154 w32_150 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_4c w32_48 w32_44 w32_38 w32_34 w32_30 w32_2c g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 rg32 W32 K32 fr32 s32 d32
  -- 0x720: branch, taken
  obtain ⟨n34, d34, u34⟩ := s33.taken E33.self 0x6FE sv_at_720
    (by decide) (by rw [g33_10, s33.zero]; decide)
  have s34 : St n34.mem SV n34 0x6FE (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u34.regs, g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = tbp := by rw [u34.regs, g33_9]
  have g34_10 : reg n34 a0 = BitVec.ofNat 32 0x0 := by rw [u34.regs, g33_10]
  have g34_11 : reg n34 a1 = BitVec.ofNat 32 0x0 := by rw [u34.regs, g33_11]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = dg := by rw [u34.regs, g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = rootp := by rw [u34.regs, g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = ll := by rw [u34.regs, g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = sgp := by rw [u34.regs, g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = kp := by rw [u34.regs, g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = sgl := by rw [u34.regs, g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by rw [u34.regs, g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = tbl := by rw [u34.regs, g33_27]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m34]; exact w33_2c
  have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m34]; exact w33_30
  have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m34]; exact w33_34
  have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m34]; exact w33_38
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m34]; exact w33_44
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m34]; exact w33_48
  have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m34]; exact w33_4c
  have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m34]; exact w33_50
  have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m34]; exact w33_54
  have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m34]; exact w33_58
  have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m34]; exact w33_5c
  have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m34]; exact w33_60
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m34]; exact w33_64
  have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m34]; exact w33_68
  have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m34]; exact w33_6c
  have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m34]; exact w33_70
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m34]; exact w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m34]; exact w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m34]; exact w33_7c
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m34]; exact w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m34]; exact w33_84
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m34]; exact w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m34]; exact w33_8c
  have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m34]; exact w33_90
  have w34_94 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m34]; exact w33_94
  have w34_98 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m34]; exact w33_98
  have w34_9c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m34]; exact w33_9c
  have w34_a0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m34]; exact w33_a0
  have w34_a4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m34]; exact w33_a4
  have w34_150 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m34]; exact w33_150
  have w34_154 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m34]; exact w33_154
  have w34_158 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m34]; exact w33_158
  have w34_15c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m34]; exact w33_15c
  clear w33_15c w33_158 w33_154 w33_150 w33_a4 w33_a0 w33_9c w33_98 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_44 w33_38 w33_34 w33_30 w33_2c g33_26 g33_27 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_11 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x6FE
  obtain ⟨n35, c35, u35⟩ := s34.block svDp16fe E34.self svDp16fe_end
    ⟨trivial, trivial⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have s35 : St n35.mem SV n35 0x700 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have rb35 : ∀ q, reg n35 q = (runBlock svDp16fe (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans c35
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by
    rw [rb35, runBlock_reg _ _ _ sp s34.zero (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (3 : Fin 32) s34.zero (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (4 : Fin 32) s34.zero (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb35, runBlock_reg _ _ _ (8 : Fin 32) s34.zero (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = tbp := by
    rw [rb35, runBlock_reg _ _ _ (9 : Fin 32) s34.zero (by decide), g34_9]
  have g35_11 : reg n35 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb35, runBlock_reg _ _ _ a1 s34.zero (by decide), g34_11]
  have g35_18 : reg n35 (18 : Fin 32) = out := by
    rw [rb35, runBlock_reg _ _ _ (18 : Fin 32) s34.zero (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by
    rw [rb35, runBlock_reg _ _ _ (19 : Fin 32) s34.zero (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = dg := by
    rw [rb35, runBlock_reg _ _ _ (20 : Fin 32) s34.zero (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = rootp := by
    rw [rb35, runBlock_reg _ _ _ (21 : Fin 32) s34.zero (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = ll := by
    rw [rb35, runBlock_reg _ _ _ (22 : Fin 32) s34.zero (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = sgp := by
    rw [rb35, runBlock_reg _ _ _ (23 : Fin 32) s34.zero (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = kp := by
    rw [rb35, runBlock_reg _ _ _ (24 : Fin 32) s34.zero (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = sgl := by
    rw [rb35, runBlock_reg _ _ _ (25 : Fin 32) s34.zero (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by
    rw [rb35, runBlock_reg _ _ _ (26 : Fin 32) s34.zero (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = tbl := by
    rw [rb35, runBlock_reg _ _ _ (27 : Fin 32) s34.zero (by decide), g34_27]
  have g35_10 : reg n35 a0 = BitVec.ofNat 32 0x4 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svDp16fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_10, g34_11, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, s34.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m35]; exact w34_2c
  have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m35]; exact w34_30
  have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m35]; exact w34_34
  have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m35]; exact w34_38
  have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m35]; exact w34_44
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m35]; exact w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m35]; exact w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m35]; exact w34_50
  have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m35]; exact w34_54
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m35]; exact w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m35]; exact w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m35]; exact w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m35]; exact w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m35]; exact w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m35]; exact w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m35]; exact w34_70
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m35]; exact w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m35]; exact w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m35]; exact w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m35]; exact w34_84
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m35]; exact w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m35]; exact w34_8c
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m35]; exact w34_90
  have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m35]; exact w34_94
  have w35_98 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m35]; exact w34_98
  have w35_9c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m35]; exact w34_9c
  have w35_a0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m35]; exact w34_a0
  have w35_a4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m35]; exact w34_a4
  have w35_150 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m35]; exact w34_150
  have w35_154 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m35]; exact w34_154
  have w35_158 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m35]; exact w34_158
  have w35_15c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m35]; exact w34_15c
  clear w34_15c w34_158 w34_154 w34_150 w34_a4 w34_a0 w34_9c w34_98 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_44 w34_38 w34_34 w34_30 w34_2c g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_11 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
  -- 0x700: lw
  obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_700 (off' := 0x702) (by decide)
    (by rw [g35_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s36 : St n36.mem SV n36 0x702 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = tbp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
  have g36_10 : reg n36 a0 = BitVec.ofNat 32 0x4 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_10]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = dg := by rw [u36.regs, upd_ne (by decide) (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = rootp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = ll := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = sgp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = kp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = sgl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = tbl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
  have g36_11 : reg n36 a1 = BitVec.ofNat 32 0x0 := by
    rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g35_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w35_50]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m36]; exact w35_2c
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m36]; exact w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m36]; exact w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m36]; exact w35_38
  have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m36]; exact w35_44
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m36]; exact w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m36]; exact w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m36]; exact w35_50
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m36]; exact w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m36]; exact w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m36]; exact w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m36]; exact w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m36]; exact w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m36]; exact w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m36]; exact w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m36]; exact w35_70
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m36]; exact w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m36]; exact w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m36]; exact w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m36]; exact w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m36]; exact w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m36]; exact w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m36]; exact w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m36]; exact w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m36]; exact w35_94
  have w36_98 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m36]; exact w35_98
  have w36_9c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m36]; exact w35_9c
  have w36_a0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m36]; exact w35_a0
  have w36_a4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m36]; exact w35_a4
  have w36_150 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m36]; exact w35_150
  have w36_154 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m36]; exact w35_154
  have w36_158 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m36]; exact w35_158
  have w36_15c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m36]; exact w35_15c
  clear w35_15c w35_158 w35_154 w35_150 w35_a4 w35_a0 w35_9c w35_98 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_44 w35_38 w35_34 w35_30 w35_2c g35_10 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_11 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 rb35 s35 m35 u35 c35
  -- 0x702: branch, not taken
  obtain ⟨n37, d37, u37⟩ := s36.notTaken E36.self 0x706 sv_at_702
    (by decide) (by rw [g36_11, g36_10]; decide)
  have s37 : St n37.mem SV n37 0x706 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u37.regs, g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = tbp := by rw [u37.regs, g36_9]
  have g37_10 : reg n37 a0 = BitVec.ofNat 32 0x4 := by rw [u37.regs, g36_10]
  have g37_11 : reg n37 a1 = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_11]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = dg := by rw [u37.regs, g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = rootp := by rw [u37.regs, g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = ll := by rw [u37.regs, g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = sgp := by rw [u37.regs, g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = kp := by rw [u37.regs, g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = sgl := by rw [u37.regs, g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by rw [u37.regs, g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = tbl := by rw [u37.regs, g36_27]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m37]; exact w36_2c
  have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m37]; exact w36_30
  have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m37]; exact w36_34
  have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m37]; exact w36_38
  have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m37]; exact w36_44
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m37]; exact w36_48
  have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m37]; exact w36_4c
  have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m37]; exact w36_50
  have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
  have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
  have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
  have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m37]; exact w36_60
  have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m37]; exact w36_64
  have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m37]; exact w36_68
  have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
  have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m37]; exact w36_70
  have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m37]; exact w36_74
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m37]; exact w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m37]; exact w36_7c
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m37]; exact w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m37]; exact w36_84
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m37]; exact w36_88
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m37]; exact w36_8c
  have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m37]; exact w36_90
  have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m37]; exact w36_94
  have w37_98 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m37]; exact w36_98
  have w37_9c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m37]; exact w36_9c
  have w37_a0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m37]; exact w36_a0
  have w37_a4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m37]; exact w36_a4
  have w37_150 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m37]; exact w36_150
  have w37_154 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m37]; exact w36_154
  have w37_158 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m37]; exact w36_158
  have w37_15c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m37]; exact w36_15c
  clear w36_15c w36_158 w36_154 w36_150 w36_a4 w36_a0 w36_9c w36_98 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_38 w36_34 w36_30 w36_2c g36_11 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_10 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  -- 0x706: lw of a constant
  obtain ⟨n38, d38, u38⟩ := s37.lw E37.self sv_at_706 (off' := 0x70A) (by decide)
    (by rw [g37_26]; decide)
  have s38 : St n38.mem SV n38 0x70A (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans (.single d38)
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = tbp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_9]
  have g38_11 : reg n38 a1 = BitVec.ofNat 32 0x0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_11]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, upd_ne (by decide) (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = dg := by rw [u38.regs, upd_ne (by decide) (by decide), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = rootp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = ll := by rw [u38.regs, upd_ne (by decide) (by decide), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = sgp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = kp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = sgl := by rw [u38.regs, upd_ne (by decide) (by decide), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = tbl := by rw [u38.regs, upd_ne (by decide) (by decide), g37_27]
  have g38_10 : reg n38 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x37) := by
    rw [u38.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g37_26, show BitVec.ofNat 32 (img% svConstExtAddress + 0x69) + 0x0 = BitVec.ofNat 32 svConstExtAddress + BitVec.ofNat 32 0x69 by decide]
    exact CodeIn.w32 (SvData.sv FW SD0 fR37).ext (by decide) (by decide)
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have w38_2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m38]; exact w37_2c
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m38]; exact w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m38]; exact w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m38]; exact w37_38
  have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m38]; exact w37_44
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m38]; exact w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m38]; exact w37_4c
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m38]; exact w37_50
  have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m38]; exact w37_54
  have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m38]; exact w37_58
  have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m38]; exact w37_5c
  have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m38]; exact w37_60
  have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m38]; exact w37_64
  have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m38]; exact w37_68
  have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m38]; exact w37_6c
  have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m38]; exact w37_70
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m38]; exact w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m38]; exact w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m38]; exact w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m38]; exact w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m38]; exact w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m38]; exact w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m38]; exact w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m38]; exact w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m38]; exact w37_94
  have w38_98 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m38]; exact w37_98
  have w38_9c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m38]; exact w37_9c
  have w38_a0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m38]; exact w37_a0
  have w38_a4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m38]; exact w37_a4
  have w38_150 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m38]; exact w37_150
  have w38_154 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m38]; exact w37_154
  have w38_158 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m38]; exact w37_158
  have w38_15c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m38]; exact w37_15c
  clear w37_15c w37_158 w37_154 w37_150 w37_a4 w37_a0 w37_9c w37_98 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_44 w37_38 w37_34 w37_30 w37_2c g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_11 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  -- 0x70A
  obtain ⟨n39, c39, u39⟩ := s38.block svDp170a E38.self svDp170a_end
    ⟨trivial, trivial⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have s39 : St n39.mem SV n39 0x70C (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have rb39 : ∀ q, reg n39 q = (runBlock svDp170a (n38.mem, reg n38)).2 q := fun q => by rw [u39.regs]
  have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
  have t39 : Steps n0 n39 := t38.trans c39
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.same m39
  have g39_2 : reg n39 sp = B + 0x21A0 := by
    rw [rb39, runBlock_reg _ _ _ sp s38.zero (by decide), g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb39, runBlock_reg _ _ _ (3 : Fin 32) s38.zero (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb39, runBlock_reg _ _ _ (4 : Fin 32) s38.zero (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb39, runBlock_reg _ _ _ (8 : Fin 32) s38.zero (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = tbp := by
    rw [rb39, runBlock_reg _ _ _ (9 : Fin 32) s38.zero (by decide), g38_9]
  have g39_10 : reg n39 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x37) := by
    rw [rb39, runBlock_reg _ _ _ a0 s38.zero (by decide), g38_10]
  have g39_18 : reg n39 (18 : Fin 32) = out := by
    rw [rb39, runBlock_reg _ _ _ (18 : Fin 32) s38.zero (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by
    rw [rb39, runBlock_reg _ _ _ (19 : Fin 32) s38.zero (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = dg := by
    rw [rb39, runBlock_reg _ _ _ (20 : Fin 32) s38.zero (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = rootp := by
    rw [rb39, runBlock_reg _ _ _ (21 : Fin 32) s38.zero (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = ll := by
    rw [rb39, runBlock_reg _ _ _ (22 : Fin 32) s38.zero (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = sgp := by
    rw [rb39, runBlock_reg _ _ _ (23 : Fin 32) s38.zero (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = kp := by
    rw [rb39, runBlock_reg _ _ _ (24 : Fin 32) s38.zero (by decide), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = sgl := by
    rw [rb39, runBlock_reg _ _ _ (25 : Fin 32) s38.zero (by decide), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by
    rw [rb39, runBlock_reg _ _ _ (26 : Fin 32) s38.zero (by decide), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = tbl := by
    rw [rb39, runBlock_reg _ _ _ (27 : Fin 32) s38.zero (by decide), g38_27]
  have g39_11 : reg n39 a1 = BitVec.ofNat 32 0xA := by
    rw [rb39]; simp +decide only [runBlock, BInstr.run, svDp170a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g38_2, g38_3, g38_4, g38_8, g38_9, g38_10, g38_11, g38_18, g38_19, g38_20, g38_21, g38_22, g38_23, g38_24, g38_25, g38_26, g38_27, s38.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m39]; exact keep_kk38
  clear keep_kk38
  have w39_2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m39]; exact w38_2c
  have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m39]; exact w38_30
  have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m39]; exact w38_34
  have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m39]; exact w38_38
  have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m39]; exact w38_44
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m39]; exact w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m39]; exact w38_4c
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m39]; exact w38_50
  have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m39]; exact w38_54
  have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m39]; exact w38_58
  have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m39]; exact w38_5c
  have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m39]; exact w38_60
  have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m39]; exact w38_64
  have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m39]; exact w38_68
  have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m39]; exact w38_6c
  have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m39]; exact w38_70
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m39]; exact w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m39]; exact w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m39]; exact w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m39]; exact w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m39]; exact w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m39]; exact w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m39]; exact w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m39]; exact w38_90
  have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m39]; exact w38_94
  have w39_98 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m39]; exact w38_98
  have w39_9c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m39]; exact w38_9c
  have w39_a0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m39]; exact w38_a0
  have w39_a4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m39]; exact w38_a4
  have w39_150 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m39]; exact w38_150
  have w39_154 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m39]; exact w38_154
  have w39_158 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m39]; exact w38_158
  have w39_15c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m39]; exact w38_15c
  clear w38_15c w38_158 w38_154 w38_150 w38_a4 w38_a0 w38_9c w38_98 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_44 w38_38 w38_34 w38_30 w38_2c g38_10 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_11 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38
  -- 0x70C: lw
  obtain ⟨n40, d40, u40⟩ := s39.lw E39.self sv_at_70c (off' := 0x70E) (by decide)
    (by rw [g39_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s40 : St n40.mem SV n40 0x70E (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have fr40 : ∀ x, SvR B x → n40.mem x = n39.mem x := fun x _ => by rw [m40]
  have t40 : Steps n0 n40 := t39.trans (.single d40)
  have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.same m40
  have g40_2 : reg n40 sp = B + 0x21A0 := by rw [u40.regs, upd_ne (by decide) (by decide), g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u40.regs, upd_ne (by decide) (by decide), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u40.regs, upd_ne (by decide) (by decide), g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u40.regs, upd_ne (by decide) (by decide), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = tbp := by rw [u40.regs, upd_ne (by decide) (by decide), g39_9]
  have g40_10 : reg n40 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x37) := by rw [u40.regs, upd_ne (by decide) (by decide), g39_10]
  have g40_11 : reg n40 a1 = BitVec.ofNat 32 0xA := by rw [u40.regs, upd_ne (by decide) (by decide), g39_11]
  have g40_18 : reg n40 (18 : Fin 32) = out := by rw [u40.regs, upd_ne (by decide) (by decide), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [u40.regs, upd_ne (by decide) (by decide), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = dg := by rw [u40.regs, upd_ne (by decide) (by decide), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = rootp := by rw [u40.regs, upd_ne (by decide) (by decide), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = ll := by rw [u40.regs, upd_ne (by decide) (by decide), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = sgp := by rw [u40.regs, upd_ne (by decide) (by decide), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = kp := by rw [u40.regs, upd_ne (by decide) (by decide), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = sgl := by rw [u40.regs, upd_ne (by decide) (by decide), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by rw [u40.regs, upd_ne (by decide) (by decide), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = tbl := by rw [u40.regs, upd_ne (by decide) (by decide), g39_27]
  have g40_12 : reg n40 a2 = op := by
    rw [u40.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g39_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w39_4c]
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m40]; exact keep_kk39
  clear keep_kk39
  have w40_2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m40]; exact w39_2c
  have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m40]; exact w39_30
  have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m40]; exact w39_34
  have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m40]; exact w39_38
  have w40_44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m40]; exact w39_44
  have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m40]; exact w39_48
  have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m40]; exact w39_4c
  have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m40]; exact w39_50
  have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m40]; exact w39_54
  have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m40]; exact w39_58
  have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m40]; exact w39_5c
  have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m40]; exact w39_60
  have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m40]; exact w39_64
  have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m40]; exact w39_68
  have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m40]; exact w39_6c
  have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m40]; exact w39_70
  have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m40]; exact w39_74
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m40]; exact w39_78
  have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m40]; exact w39_7c
  have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m40]; exact w39_80
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m40]; exact w39_84
  have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m40]; exact w39_88
  have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m40]; exact w39_8c
  have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m40]; exact w39_90
  have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m40]; exact w39_94
  have w40_98 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m40]; exact w39_98
  have w40_9c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m40]; exact w39_9c
  have w40_a0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m40]; exact w39_a0
  have w40_a4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m40]; exact w39_a4
  have w40_150 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m40]; exact w39_150
  have w40_154 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m40]; exact w39_154
  have w40_158 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m40]; exact w39_158
  have w40_15c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m40]; exact w39_15c
  clear w39_15c w39_158 w39_154 w39_150 w39_a4 w39_a0 w39_9c w39_98 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_5c w39_58 w39_54 w39_50 w39_4c w39_48 w39_44 w39_38 w39_34 w39_30 w39_2c g39_11 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 rb39 s39 m39 u39 c39
  -- 0x70E: lw
  obtain ⟨n41, d41, u41⟩ := s40.lw E40.self sv_at_70e (off' := 0x710) (by decide)
    (by rw [g40_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s41 : St n41.mem SV n41 0x710 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
  have t41 : Steps n0 n41 := t40.trans (.single d41)
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.same m41
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, upd_ne (by decide) (by decide), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, upd_ne (by decide) (by decide), g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = tbp := by rw [u41.regs, upd_ne (by decide) (by decide), g40_9]
  have g41_10 : reg n41 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x37) := by rw [u41.regs, upd_ne (by decide) (by decide), g40_10]
  have g41_11 : reg n41 a1 = BitVec.ofNat 32 0xA := by rw [u41.regs, upd_ne (by decide) (by decide), g40_11]
  have g41_12 : reg n41 a2 = op := by rw [u41.regs, upd_ne (by decide) (by decide), g40_12]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, upd_ne (by decide) (by decide), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, upd_ne (by decide) (by decide), g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = dg := by rw [u41.regs, upd_ne (by decide) (by decide), g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = rootp := by rw [u41.regs, upd_ne (by decide) (by decide), g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = ll := by rw [u41.regs, upd_ne (by decide) (by decide), g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = sgp := by rw [u41.regs, upd_ne (by decide) (by decide), g40_23]
  have g41_24 : reg n41 (24 : Fin 32) = kp := by rw [u41.regs, upd_ne (by decide) (by decide), g40_24]
  have g41_25 : reg n41 (25 : Fin 32) = sgl := by rw [u41.regs, upd_ne (by decide) (by decide), g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by rw [u41.regs, upd_ne (by decide) (by decide), g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = tbl := by rw [u41.regs, upd_ne (by decide) (by decide), g40_27]
  have g41_13 : reg n41 a3 = ol := by
    rw [u41.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g40_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w40_48]
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have w41_2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m41]; exact w40_2c
  have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m41]; exact w40_30
  have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m41]; exact w40_34
  have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m41]; exact w40_38
  have w41_44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m41]; exact w40_44
  have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m41]; exact w40_48
  have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m41]; exact w40_4c
  have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m41]; exact w40_50
  have w41_54 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m41]; exact w40_54
  have w41_58 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m41]; exact w40_58
  have w41_5c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m41]; exact w40_5c
  have w41_60 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m41]; exact w40_60
  have w41_64 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m41]; exact w40_64
  have w41_68 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m41]; exact w40_68
  have w41_6c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m41]; exact w40_6c
  have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m41]; exact w40_70
  have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m41]; exact w40_74
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m41]; exact w40_78
  have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m41]; exact w40_7c
  have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m41]; exact w40_80
  have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m41]; exact w40_84
  have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m41]; exact w40_88
  have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m41]; exact w40_8c
  have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m41]; exact w40_90
  have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m41]; exact w40_94
  have w41_98 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m41]; exact w40_98
  have w41_9c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m41]; exact w40_9c
  have w41_a0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m41]; exact w40_a0
  have w41_a4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m41]; exact w40_a4
  have w41_150 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m41]; exact w40_150
  have w41_154 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m41]; exact w40_154
  have w41_158 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m41]; exact w40_158
  have w41_15c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m41]; exact w40_15c
  clear w40_15c w40_158 w40_154 w40_150 w40_a4 w40_a0 w40_9c w40_98 w40_94 w40_90 w40_8c w40_88 w40_84 w40_80 w40_7c w40_78 w40_74 w40_70 w40_6c w40_68 w40_64 w40_60 w40_5c w40_58 w40_54 w40_50 w40_4c w40_48 w40_44 w40_38 w40_34 w40_30 w40_2c g40_12 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_11 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 m40 s40 u40 d40
  -- 0x710: sv_seqEqF
  obtain ⟨n42, c42, s42, rk42, a0_42, K42, fr42⟩ := sv_seqEqF (pl := 10) (ql := ol.toNat)
    F E41 s41 sv_at_710 sv_at_714 (by decide) (by decide) g41_2
    g41_10 g41_11 g41_12 (by rw [g41_13, ofNat_toNat_self]) (.inr ⟨by decide, by decide⟩) (.inl oid_in)
  have t42 : Steps n0 n42 := t41.trans c42
  have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : SvCode n42.mem := E41.fr F fr42
  have V42 : SvSaves B n42.mem v := V41.keepL K42 (by decide)
  rw [sv_mbRo FW fR41 (.inr ⟨by decide, by decide⟩), sv_mbRo FW fR41 (.inl oid_in)] at a0_42
  have g42_2 : reg n42 sp = B + 0x21A0 := by rw [rk42 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_2]
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk42 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk42 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_4]
  have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk42 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = tbp := by rw [rk42 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_9]
  have g42_18 : reg n42 (18 : Fin 32) = out := by rw [rk42 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [rk42 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = dg := by rw [rk42 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = rootp := by rw [rk42 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = ll := by rw [rk42 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = sgp := by rw [rk42 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_23]
  have g42_24 : reg n42 (24 : Fin 32) = kp := by rw [rk42 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_24]
  have g42_25 : reg n42 (25 : Fin 32) = sgl := by rw [rk42 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by rw [rk42 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = tbl := by rw [rk42 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g41_27]
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x50, 0x4), (0x50, 0x4)] := keep_kk41.trans K42
  clear keep_kk41
  have w42_2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K42.w32 (by decide) (by decide)).trans w41_2c
  have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K42.w32 (by decide) (by decide)).trans w41_30
  have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K42.w32 (by decide) (by decide)).trans w41_34
  have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K42.w32 (by decide) (by decide)).trans w41_38
  have w42_44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K42.w32 (by decide) (by decide)).trans w41_44
  have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K42.w32 (by decide) (by decide)).trans w41_48
  have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K42.w32 (by decide) (by decide)).trans w41_4c
  have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := (K42.w32 (by decide) (by decide)).trans w41_50
  have w42_54 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K42.w32 (by decide) (by decide)).trans w41_54
  have w42_58 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K42.w32 (by decide) (by decide)).trans w41_58
  have w42_5c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K42.w32 (by decide) (by decide)).trans w41_5c
  have w42_60 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K42.w32 (by decide) (by decide)).trans w41_60
  have w42_64 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K42.w32 (by decide) (by decide)).trans w41_64
  have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K42.w32 (by decide) (by decide)).trans w41_68
  have w42_6c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K42.w32 (by decide) (by decide)).trans w41_6c
  have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K42.w32 (by decide) (by decide)).trans w41_70
  have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K42.w32 (by decide) (by decide)).trans w41_74
  have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K42.w32 (by decide) (by decide)).trans w41_78
  have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K42.w32 (by decide) (by decide)).trans w41_7c
  have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K42.w32 (by decide) (by decide)).trans w41_80
  have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K42.w32 (by decide) (by decide)).trans w41_84
  have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K42.w32 (by decide) (by decide)).trans w41_88
  have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K42.w32 (by decide) (by decide)).trans w41_8c
  have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K42.w32 (by decide) (by decide)).trans w41_90
  have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K42.w32 (by decide) (by decide)).trans w41_94
  have w42_98 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K42.w32 (by decide) (by decide)).trans w41_98
  have w42_9c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K42.w32 (by decide) (by decide)).trans w41_9c
  have w42_a0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K42.w32 (by decide) (by decide)).trans w41_a0
  have w42_a4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K42.w32 (by decide) (by decide)).trans w41_a4
  have w42_150 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K42.w32 (by decide) (by decide)).trans w41_150
  have w42_154 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K42.w32 (by decide) (by decide)).trans w41_154
  have w42_158 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K42.w32 (by decide) (by decide)).trans w41_158
  have w42_15c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K42.w32 (by decide) (by decide)).trans w41_15c
  clear w41_15c w41_158 w41_154 w41_150 w41_a4 w41_a0 w41_9c w41_98 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_74 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_44 w41_38 w41_34 w41_30 w41_2c g41_13 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_12 g41_11 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
  have g42_10 : reg n42 a0 = BitVec.ofNat 32 1 := by rw [a0_42, ite_eq_left hp1]; rfl
  -- 0x718: lw
  obtain ⟨n43, d43, u43⟩ := s42.lw E42.self sv_at_718 (off' := 0x71A) (by decide)
    (by rw [g42_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s43 : St n43.mem SV n43 0x71A (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
  have m43 : n43.mem = n42.mem := u43.mem
  have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
  have t43 : Steps n0 n43 := t42.trans (.single d43)
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.same m43
  have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, upd_ne (by decide) (by decide), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, upd_ne (by decide) (by decide), g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = tbp := by rw [u43.regs, upd_ne (by decide) (by decide), g42_9]
  have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x1 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_10]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, upd_ne (by decide) (by decide), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, upd_ne (by decide) (by decide), g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = dg := by rw [u43.regs, upd_ne (by decide) (by decide), g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = rootp := by rw [u43.regs, upd_ne (by decide) (by decide), g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = ll := by rw [u43.regs, upd_ne (by decide) (by decide), g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = sgp := by rw [u43.regs, upd_ne (by decide) (by decide), g42_23]
  have g43_24 : reg n43 (24 : Fin 32) = kp := by rw [u43.regs, upd_ne (by decide) (by decide), g42_24]
  have g43_25 : reg n43 (25 : Fin 32) = sgl := by rw [u43.regs, upd_ne (by decide) (by decide), g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by rw [u43.regs, upd_ne (by decide) (by decide), g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = tbl := by rw [u43.regs, upd_ne (by decide) (by decide), g42_27]
  have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x0 := by
    rw [u43.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g42_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w42_50]
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m43]; exact keep_kk42
  clear keep_kk42
  have w43_2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m43]; exact w42_2c
  have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m43]; exact w42_30
  have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m43]; exact w42_34
  have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m43]; exact w42_38
  have w43_44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m43]; exact w42_44
  have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m43]; exact w42_48
  have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m43]; exact w42_4c
  have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m43]; exact w42_50
  have w43_54 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m43]; exact w42_54
  have w43_58 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m43]; exact w42_58
  have w43_5c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m43]; exact w42_5c
  have w43_60 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m43]; exact w42_60
  have w43_64 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m43]; exact w42_64
  have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m43]; exact w42_68
  have w43_6c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m43]; exact w42_6c
  have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m43]; exact w42_70
  have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m43]; exact w42_74
  have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m43]; exact w42_78
  have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m43]; exact w42_7c
  have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m43]; exact w42_80
  have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m43]; exact w42_84
  have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m43]; exact w42_88
  have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m43]; exact w42_8c
  have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m43]; exact w42_90
  have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m43]; exact w42_94
  have w43_98 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m43]; exact w42_98
  have w43_9c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m43]; exact w42_9c
  have w43_a0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m43]; exact w42_a0
  have w43_a4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m43]; exact w42_a4
  have w43_150 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m43]; exact w42_150
  have w43_154 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m43]; exact w42_154
  have w43_158 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m43]; exact w42_158
  have w43_15c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m43]; exact w42_15c
  clear w42_15c w42_158 w42_154 w42_150 w42_a4 w42_a0 w42_9c w42_98 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_44 w42_38 w42_34 w42_30 w42_2c g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 K42 a0_42 rk42 s42 c42
  -- 0x71A
  obtain ⟨n44, c44, u44⟩ := s43.block svDp171a E43.self svDp171a_end
    ⟨trivial, trivial⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have s44 : St n44.mem SV n44 0x71C (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have rb44 : ∀ q, reg n44 q = (runBlock svDp171a (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
  have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
  have t44 : Steps n0 n44 := t43.trans c44
  have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : SvCode n44.mem := E43.fr F fr44
  have V44 : SvSaves B n44.mem v := V43.same m44
  have g44_2 : reg n44 sp = B + 0x21A0 := by
    rw [rb44, runBlock_reg _ _ _ sp s43.zero (by decide), g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb44, runBlock_reg _ _ _ (3 : Fin 32) s43.zero (by decide), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb44, runBlock_reg _ _ _ (4 : Fin 32) s43.zero (by decide), g43_4]
  have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb44, runBlock_reg _ _ _ (8 : Fin 32) s43.zero (by decide), g43_8]
  have g44_9 : reg n44 (9 : Fin 32) = tbp := by
    rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
  have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb44, runBlock_reg _ _ _ a0 s43.zero (by decide), g43_10]
  have g44_18 : reg n44 (18 : Fin 32) = out := by
    rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by
    rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
  have g44_20 : reg n44 (20 : Fin 32) = dg := by
    rw [rb44, runBlock_reg _ _ _ (20 : Fin 32) s43.zero (by decide), g43_20]
  have g44_21 : reg n44 (21 : Fin 32) = rootp := by
    rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
  have g44_22 : reg n44 (22 : Fin 32) = ll := by
    rw [rb44, runBlock_reg _ _ _ (22 : Fin 32) s43.zero (by decide), g43_22]
  have g44_23 : reg n44 (23 : Fin 32) = sgp := by
    rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
  have g44_24 : reg n44 (24 : Fin 32) = kp := by
    rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
  have g44_25 : reg n44 (25 : Fin 32) = sgl := by
    rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by
    rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = tbl := by
    rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
  have g44_11 : reg n44 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svDp171a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x50, 0x4), (0x50, 0x4)] := by rw [m44]; exact keep_kk43
  clear keep_kk43
  have w44_2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m44]; exact w43_2c
  have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m44]; exact w43_30
  have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m44]; exact w43_34
  have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m44]; exact w43_38
  have w44_44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m44]; exact w43_44
  have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m44]; exact w43_48
  have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m44]; exact w43_4c
  have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x0 := by rw [m44]; exact w43_50
  have w44_54 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m44]; exact w43_54
  have w44_58 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m44]; exact w43_58
  have w44_5c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m44]; exact w43_5c
  have w44_60 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m44]; exact w43_60
  have w44_64 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m44]; exact w43_64
  have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m44]; exact w43_68
  have w44_6c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m44]; exact w43_6c
  have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m44]; exact w43_70
  have w44_74 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m44]; exact w43_74
  have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m44]; exact w43_78
  have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m44]; exact w43_7c
  have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m44]; exact w43_80
  have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m44]; exact w43_84
  have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m44]; exact w43_88
  have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m44]; exact w43_8c
  have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m44]; exact w43_90
  have w44_94 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m44]; exact w43_94
  have w44_98 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m44]; exact w43_98
  have w44_9c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m44]; exact w43_9c
  have w44_a0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m44]; exact w43_a0
  have w44_a4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m44]; exact w43_a4
  have w44_150 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m44]; exact w43_150
  have w44_154 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m44]; exact w43_154
  have w44_158 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m44]; exact w43_158
  have w44_15c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m44]; exact w43_15c
  clear w43_15c w43_158 w43_154 w43_150 w43_a4 w43_a0 w43_9c w43_98 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_74 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_44 w43_38 w43_34 w43_30 w43_2c g43_11 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 m43 s43 u43 d43 g42_10
  -- 0x71C: sw
  obtain ⟨n45, d45, s45, fr45, K45, W45, rg45⟩ := sv_sw F E44 s44 sv_at_71c (off' := 0x71E) (c := 0x50)
    (by decide) (by rw [g44_2]; sv_addr) (by decide) (by decide)
  have t45 : Steps n0 n45 := t44.trans d45
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.keep K45 (by decide)
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [rg45 sp, g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg45 (3 : Fin 32), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg45 (4 : Fin 32), g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg45 (8 : Fin 32), g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = tbp := by rw [rg45 (9 : Fin 32), g44_9]
  have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x1 := by rw [rg45 a0, g44_10]
  have g45_11 : reg n45 a1 = BitVec.ofNat 32 0x1 := by rw [rg45 a1, g44_11]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [rg45 (18 : Fin 32), g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [rg45 (19 : Fin 32), g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = dg := by rw [rg45 (20 : Fin 32), g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = rootp := by rw [rg45 (21 : Fin 32), g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = ll := by rw [rg45 (22 : Fin 32), g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = sgp := by rw [rg45 (23 : Fin 32), g44_23]
  have g45_24 : reg n45 (24 : Fin 32) = kp := by rw [rg45 (24 : Fin 32), g44_24]
  have g45_25 : reg n45 (25 : Fin 32) = sgl := by rw [rg45 (25 : Fin 32), g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x69) := by rw [rg45 (26 : Fin 32), g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = tbl := by rw [rg45 (27 : Fin 32), g44_27]
  have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := keep_kk44.trans K45.toL
  clear keep_kk44
  have w45_2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K45.w32 (by decide) (by decide)).trans w44_2c
  have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K45.w32 (by decide) (by decide)).trans w44_30
  have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K45.w32 (by decide) (by decide)).trans w44_34
  have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K45.w32 (by decide) (by decide)).trans w44_38
  have w45_44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K45.w32 (by decide) (by decide)).trans w44_44
  have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K45.w32 (by decide) (by decide)).trans w44_48
  have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K45.w32 (by decide) (by decide)).trans w44_4c
  have w45_54 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K45.w32 (by decide) (by decide)).trans w44_54
  have w45_58 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K45.w32 (by decide) (by decide)).trans w44_58
  have w45_5c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K45.w32 (by decide) (by decide)).trans w44_5c
  have w45_60 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K45.w32 (by decide) (by decide)).trans w44_60
  have w45_64 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K45.w32 (by decide) (by decide)).trans w44_64
  have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K45.w32 (by decide) (by decide)).trans w44_68
  have w45_6c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K45.w32 (by decide) (by decide)).trans w44_6c
  have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K45.w32 (by decide) (by decide)).trans w44_70
  have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K45.w32 (by decide) (by decide)).trans w44_74
  have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K45.w32 (by decide) (by decide)).trans w44_78
  have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K45.w32 (by decide) (by decide)).trans w44_7c
  have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K45.w32 (by decide) (by decide)).trans w44_80
  have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K45.w32 (by decide) (by decide)).trans w44_84
  have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K45.w32 (by decide) (by decide)).trans w44_88
  have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K45.w32 (by decide) (by decide)).trans w44_8c
  have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K45.w32 (by decide) (by decide)).trans w44_90
  have w45_94 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K45.w32 (by decide) (by decide)).trans w44_94
  have w45_98 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K45.w32 (by decide) (by decide)).trans w44_98
  have w45_9c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K45.w32 (by decide) (by decide)).trans w44_9c
  have w45_a0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K45.w32 (by decide) (by decide)).trans w44_a0
  have w45_a4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K45.w32 (by decide) (by decide)).trans w44_a4
  have w45_150 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K45.w32 (by decide) (by decide)).trans w44_150
  have w45_154 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K45.w32 (by decide) (by decide)).trans w44_154
  have w45_158 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K45.w32 (by decide) (by decide)).trans w44_158
  have w45_15c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K45.w32 (by decide) (by decide)).trans w44_15c
  have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [W45, g44_11]
  clear w44_15c w44_158 w44_154 w44_150 w44_a4 w44_a0 w44_9c w44_98 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_74 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_44 w44_38 w44_34 w44_30 w44_2c g44_11 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_10 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
  -- 0x71E
  obtain ⟨n46, c46, u46⟩ := s45.block svDp171e E45.self svDp171e_end
    ⟨trivial, trivial⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have s46 : St n46.mem SV n46 0x720 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have rb46 : ∀ q, reg n46 q = (runBlock svDp171e (n45.mem, reg n45)).2 q := fun q => by rw [u46.regs]
  have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans c46
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by
    rw [rb46, runBlock_reg _ _ _ sp s45.zero (by decide), g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb46, runBlock_reg _ _ _ (3 : Fin 32) s45.zero (by decide), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb46, runBlock_reg _ _ _ (4 : Fin 32) s45.zero (by decide), g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb46, runBlock_reg _ _ _ (8 : Fin 32) s45.zero (by decide), g45_8]
  have g46_9 : reg n46 (9 : Fin 32) = tbp := by
    rw [rb46, runBlock_reg _ _ _ (9 : Fin 32) s45.zero (by decide), g45_9]
  have g46_10 : reg n46 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb46, runBlock_reg _ _ _ a0 s45.zero (by decide), g45_10]
  have g46_11 : reg n46 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb46, runBlock_reg _ _ _ a1 s45.zero (by decide), g45_11]
  have g46_18 : reg n46 (18 : Fin 32) = out := by
    rw [rb46, runBlock_reg _ _ _ (18 : Fin 32) s45.zero (by decide), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by
    rw [rb46, runBlock_reg _ _ _ (19 : Fin 32) s45.zero (by decide), g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = dg := by
    rw [rb46, runBlock_reg _ _ _ (20 : Fin 32) s45.zero (by decide), g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = rootp := by
    rw [rb46, runBlock_reg _ _ _ (21 : Fin 32) s45.zero (by decide), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = ll := by
    rw [rb46, runBlock_reg _ _ _ (22 : Fin 32) s45.zero (by decide), g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = sgp := by
    rw [rb46, runBlock_reg _ _ _ (23 : Fin 32) s45.zero (by decide), g45_23]
  have g46_24 : reg n46 (24 : Fin 32) = kp := by
    rw [rb46, runBlock_reg _ _ _ (24 : Fin 32) s45.zero (by decide), g45_24]
  have g46_25 : reg n46 (25 : Fin 32) = sgl := by
    rw [rb46, runBlock_reg _ _ _ (25 : Fin 32) s45.zero (by decide), g45_25]
  have g46_27 : reg n46 (27 : Fin 32) = tbl := by
    rw [rb46, runBlock_reg _ _ _ (27 : Fin 32) s45.zero (by decide), g45_27]
  have g46_26 : reg n46 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by
    rw [rb46]; simp +decide only [runBlock, BInstr.run, svDp171e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_10, g45_11, g45_18, g45_19, g45_20, g45_21, g45_22, g45_23, g45_24, g45_25, g45_26, g45_27, s45.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m46]; exact keep_kk45
  clear keep_kk45
  have w46_2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m46]; exact w45_2c
  have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m46]; exact w45_30
  have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m46]; exact w45_34
  have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m46]; exact w45_38
  have w46_44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m46]; exact w45_44
  have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m46]; exact w45_48
  have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m46]; exact w45_4c
  have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m46]; exact w45_50
  have w46_54 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m46]; exact w45_54
  have w46_58 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m46]; exact w45_58
  have w46_5c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m46]; exact w45_5c
  have w46_60 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m46]; exact w45_60
  have w46_64 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m46]; exact w45_64
  have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m46]; exact w45_68
  have w46_6c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m46]; exact w45_6c
  have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m46]; exact w45_70
  have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m46]; exact w45_74
  have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m46]; exact w45_78
  have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m46]; exact w45_7c
  have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m46]; exact w45_80
  have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m46]; exact w45_84
  have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m46]; exact w45_88
  have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m46]; exact w45_8c
  have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m46]; exact w45_90
  have w46_94 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m46]; exact w45_94
  have w46_98 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m46]; exact w45_98
  have w46_9c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m46]; exact w45_9c
  have w46_a0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m46]; exact w45_a0
  have w46_a4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m46]; exact w45_a4
  have w46_150 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m46]; exact w45_150
  have w46_154 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m46]; exact w45_154
  have w46_158 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m46]; exact w45_158
  have w46_15c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m46]; exact w45_15c
  clear w45_50 w45_15c w45_158 w45_154 w45_150 w45_a4 w45_a0 w45_9c w45_98 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_74 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_4c w45_48 w45_44 w45_38 w45_34 w45_30 w45_2c g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_11 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 rg45 W45 K45 fr45 s45 d45
  -- 0x720: branch, not taken
  obtain ⟨n47, d47, u47⟩ := s46.notTaken E46.self 0x722 sv_at_720
    (by decide) (by rw [g46_10, s46.zero]; decide)
  have s47 : St n47.mem SV n47 0x722 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans (.single d47)
  have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u47.regs, g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = tbp := by rw [u47.regs, g46_9]
  have g47_10 : reg n47 a0 = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_10]
  have g47_11 : reg n47 a1 = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_11]
  have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = dg := by rw [u47.regs, g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = rootp := by rw [u47.regs, g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = ll := by rw [u47.regs, g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = sgp := by rw [u47.regs, g46_23]
  have g47_24 : reg n47 (24 : Fin 32) = kp := by rw [u47.regs, g46_24]
  have g47_25 : reg n47 (25 : Fin 32) = sgl := by rw [u47.regs, g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u47.regs, g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = tbl := by rw [u47.regs, g46_27]
  have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m47]; exact keep_kk46
  clear keep_kk46
  have w47_2c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m47]; exact w46_2c
  have w47_30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m47]; exact w46_30
  have w47_34 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m47]; exact w46_34
  have w47_38 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m47]; exact w46_38
  have w47_44 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m47]; exact w46_44
  have w47_48 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m47]; exact w46_48
  have w47_4c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m47]; exact w46_4c
  have w47_50 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m47]; exact w46_50
  have w47_54 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m47]; exact w46_54
  have w47_58 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m47]; exact w46_58
  have w47_5c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m47]; exact w46_5c
  have w47_60 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m47]; exact w46_60
  have w47_64 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m47]; exact w46_64
  have w47_68 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m47]; exact w46_68
  have w47_6c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m47]; exact w46_6c
  have w47_70 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m47]; exact w46_70
  have w47_74 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m47]; exact w46_74
  have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m47]; exact w46_78
  have w47_7c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m47]; exact w46_7c
  have w47_80 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m47]; exact w46_80
  have w47_84 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m47]; exact w46_84
  have w47_88 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m47]; exact w46_88
  have w47_8c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m47]; exact w46_8c
  have w47_90 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m47]; exact w46_90
  have w47_94 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m47]; exact w46_94
  have w47_98 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m47]; exact w46_98
  have w47_9c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m47]; exact w46_9c
  have w47_a0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m47]; exact w46_a0
  have w47_a4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m47]; exact w46_a4
  have w47_150 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m47]; exact w46_150
  have w47_154 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m47]; exact w46_154
  have w47_158 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m47]; exact w46_158
  have w47_15c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m47]; exact w46_15c
  clear w46_15c w46_158 w46_154 w46_150 w46_a4 w46_a0 w46_9c w46_98 w46_94 w46_90 w46_8c w46_88 w46_84 w46_80 w46_7c w46_78 w46_74 w46_70 w46_6c w46_68 w46_64 w46_60 w46_5c w46_58 w46_54 w46_50 w46_4c w46_48 w46_44 w46_38 w46_34 w46_30 w46_2c g46_26 g46_27 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_11 g46_10 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 rb46 s46 m46 u46 c46
  -- 0x722: lw
  obtain ⟨n48, d48, u48⟩ := s47.lw E47.self sv_at_722 (off' := 0x724) (by decide)
    (by rw [g47_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s48 : St n48.mem SV n48 0x724 (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
  have m48 : n48.mem = n47.mem := u48.mem
  have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
  have t48 : Steps n0 n48 := t47.trans (.single d48)
  have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : SvCode n48.mem := E47.fr F fr48
  have V48 : SvSaves B n48.mem v := V47.same m48
  have g48_2 : reg n48 sp = B + 0x21A0 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = tbp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_9]
  have g48_11 : reg n48 a1 = BitVec.ofNat 32 0x1 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_11]
  have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, upd_ne (by decide) (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = dg := by rw [u48.regs, upd_ne (by decide) (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = rootp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = ll := by rw [u48.regs, upd_ne (by decide) (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = sgp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_23]
  have g48_24 : reg n48 (24 : Fin 32) = kp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_24]
  have g48_25 : reg n48 (25 : Fin 32) = sgl := by rw [u48.regs, upd_ne (by decide) (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = tbl := by rw [u48.regs, upd_ne (by decide) (by decide), g47_27]
  have g48_10 : reg n48 a0 = vp := by
    rw [u48.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g47_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr, w47_38]
  have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m48]; exact keep_kk47
  clear keep_kk47
  have w48_2c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m48]; exact w47_2c
  have w48_30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m48]; exact w47_30
  have w48_34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m48]; exact w47_34
  have w48_38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m48]; exact w47_38
  have w48_44 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m48]; exact w47_44
  have w48_48 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m48]; exact w47_48
  have w48_4c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m48]; exact w47_4c
  have w48_50 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m48]; exact w47_50
  have w48_54 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m48]; exact w47_54
  have w48_58 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m48]; exact w47_58
  have w48_5c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m48]; exact w47_5c
  have w48_60 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m48]; exact w47_60
  have w48_64 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m48]; exact w47_64
  have w48_68 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m48]; exact w47_68
  have w48_6c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m48]; exact w47_6c
  have w48_70 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m48]; exact w47_70
  have w48_74 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m48]; exact w47_74
  have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m48]; exact w47_78
  have w48_7c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m48]; exact w47_7c
  have w48_80 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m48]; exact w47_80
  have w48_84 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m48]; exact w47_84
  have w48_88 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m48]; exact w47_88
  have w48_8c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m48]; exact w47_8c
  have w48_90 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m48]; exact w47_90
  have w48_94 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m48]; exact w47_94
  have w48_98 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m48]; exact w47_98
  have w48_9c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m48]; exact w47_9c
  have w48_a0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m48]; exact w47_a0
  have w48_a4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m48]; exact w47_a4
  have w48_150 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m48]; exact w47_150
  have w48_154 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m48]; exact w47_154
  have w48_158 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m48]; exact w47_158
  have w48_15c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m48]; exact w47_15c
  clear w47_15c w47_158 w47_154 w47_150 w47_a4 w47_a0 w47_9c w47_98 w47_94 w47_90 w47_8c w47_88 w47_84 w47_80 w47_7c w47_78 w47_74 w47_70 w47_6c w47_68 w47_64 w47_60 w47_5c w47_58 w47_54 w47_50 w47_4c w47_48 w47_44 w47_38 w47_34 w47_30 w47_2c g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_11 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
  -- 0x724
  obtain ⟨n49, c49, u49⟩ := s48.block svDp1724 E48.self svDp1724_end
    ⟨trivial, trivial⟩
  have m49 : n49.mem = n48.mem := u49.mem
  have s49 : St n49.mem SV n49 0x726 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
  have rb49 : ∀ q, reg n49 q = (runBlock svDp1724 (n48.mem, reg n48)).2 q := fun q => by rw [u49.regs]
  have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
  have t49 : Steps n0 n49 := t48.trans c49
  have fR49 : ∀ x, SvR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.same m49
  have g49_2 : reg n49 sp = B + 0x21A0 := by
    rw [rb49, runBlock_reg _ _ _ sp s48.zero (by decide), g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb49, runBlock_reg _ _ _ (3 : Fin 32) s48.zero (by decide), g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb49, runBlock_reg _ _ _ (4 : Fin 32) s48.zero (by decide), g48_4]
  have g49_8 : reg n49 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb49, runBlock_reg _ _ _ (8 : Fin 32) s48.zero (by decide), g48_8]
  have g49_9 : reg n49 (9 : Fin 32) = tbp := by
    rw [rb49, runBlock_reg _ _ _ (9 : Fin 32) s48.zero (by decide), g48_9]
  have g49_10 : reg n49 a0 = vp := by
    rw [rb49, runBlock_reg _ _ _ a0 s48.zero (by decide), g48_10]
  have g49_11 : reg n49 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb49, runBlock_reg _ _ _ a1 s48.zero (by decide), g48_11]
  have g49_18 : reg n49 (18 : Fin 32) = out := by
    rw [rb49, runBlock_reg _ _ _ (18 : Fin 32) s48.zero (by decide), g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by
    rw [rb49, runBlock_reg _ _ _ (19 : Fin 32) s48.zero (by decide), g48_19]
  have g49_20 : reg n49 (20 : Fin 32) = dg := by
    rw [rb49, runBlock_reg _ _ _ (20 : Fin 32) s48.zero (by decide), g48_20]
  have g49_21 : reg n49 (21 : Fin 32) = rootp := by
    rw [rb49, runBlock_reg _ _ _ (21 : Fin 32) s48.zero (by decide), g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = ll := by
    rw [rb49, runBlock_reg _ _ _ (22 : Fin 32) s48.zero (by decide), g48_22]
  have g49_23 : reg n49 (23 : Fin 32) = sgp := by
    rw [rb49, runBlock_reg _ _ _ (23 : Fin 32) s48.zero (by decide), g48_23]
  have g49_24 : reg n49 (24 : Fin 32) = kp := by
    rw [rb49, runBlock_reg _ _ _ (24 : Fin 32) s48.zero (by decide), g48_24]
  have g49_25 : reg n49 (25 : Fin 32) = sgl := by
    rw [rb49, runBlock_reg _ _ _ (25 : Fin 32) s48.zero (by decide), g48_25]
  have g49_26 : reg n49 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by
    rw [rb49, runBlock_reg _ _ _ (26 : Fin 32) s48.zero (by decide), g48_26]
  have g49_27 : reg n49 (27 : Fin 32) = tbl := by
    rw [rb49, runBlock_reg _ _ _ (27 : Fin 32) s48.zero (by decide), g48_27]
  have g49_12 : reg n49 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb49]; simp +decide only [runBlock, BInstr.run, svDp1724, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g48_2, g48_3, g48_4, g48_8, g48_9, g48_10, g48_11, g48_18, g48_19, g48_20, g48_21, g48_22, g48_23, g48_24, g48_25, g48_26, g48_27, s48.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m49]; exact keep_kk48
  clear keep_kk48
  have w49_2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m49]; exact w48_2c
  have w49_30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m49]; exact w48_30
  have w49_34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m49]; exact w48_34
  have w49_38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m49]; exact w48_38
  have w49_44 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m49]; exact w48_44
  have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m49]; exact w48_48
  have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m49]; exact w48_4c
  have w49_50 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m49]; exact w48_50
  have w49_54 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m49]; exact w48_54
  have w49_58 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m49]; exact w48_58
  have w49_5c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m49]; exact w48_5c
  have w49_60 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m49]; exact w48_60
  have w49_64 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m49]; exact w48_64
  have w49_68 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m49]; exact w48_68
  have w49_6c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m49]; exact w48_6c
  have w49_70 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m49]; exact w48_70
  have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m49]; exact w48_74
  have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m49]; exact w48_78
  have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m49]; exact w48_7c
  have w49_80 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m49]; exact w48_80
  have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m49]; exact w48_84
  have w49_88 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m49]; exact w48_88
  have w49_8c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m49]; exact w48_8c
  have w49_90 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m49]; exact w48_90
  have w49_94 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m49]; exact w48_94
  have w49_98 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m49]; exact w48_98
  have w49_9c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m49]; exact w48_9c
  have w49_a0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m49]; exact w48_a0
  have w49_a4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m49]; exact w48_a4
  have w49_150 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m49]; exact w48_150
  have w49_154 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m49]; exact w48_154
  have w49_158 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m49]; exact w48_158
  have w49_15c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m49]; exact w48_15c
  clear w48_15c w48_158 w48_154 w48_150 w48_a4 w48_a0 w48_9c w48_98 w48_94 w48_90 w48_8c w48_88 w48_84 w48_80 w48_7c w48_78 w48_74 w48_70 w48_6c w48_68 w48_64 w48_60 w48_5c w48_58 w48_54 w48_50 w48_4c w48_48 w48_44 w48_38 w48_34 w48_30 w48_2c g48_10 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_11 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
  -- 0x726: sw
  obtain ⟨n50, d50, s50, fr50, K50, W50, rg50⟩ := sv_sw F E49 s49 sv_at_726 (off' := 0x728) (c := 0x380)
    (by decide) (by rw [g49_12]; sv_addr) (by decide) (by decide)
  have t50 : Steps n0 n50 := t49.trans d50
  have fR50 : ∀ x, SvR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : SvCode n50.mem := E49.fr F fr50
  have V50 : SvSaves B n50.mem v := V49.keep K50 (by decide)
  have g50_2 : reg n50 sp = B + 0x21A0 := by rw [rg50 sp, g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg50 (3 : Fin 32), g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg50 (4 : Fin 32), g49_4]
  have g50_8 : reg n50 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg50 (8 : Fin 32), g49_8]
  have g50_9 : reg n50 (9 : Fin 32) = tbp := by rw [rg50 (9 : Fin 32), g49_9]
  have g50_10 : reg n50 a0 = vp := by rw [rg50 a0, g49_10]
  have g50_11 : reg n50 a1 = BitVec.ofNat 32 0x1 := by rw [rg50 a1, g49_11]
  have g50_12 : reg n50 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg50 a2, g49_12]
  have g50_18 : reg n50 (18 : Fin 32) = out := by rw [rg50 (18 : Fin 32), g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [rg50 (19 : Fin 32), g49_19]
  have g50_20 : reg n50 (20 : Fin 32) = dg := by rw [rg50 (20 : Fin 32), g49_20]
  have g50_21 : reg n50 (21 : Fin 32) = rootp := by rw [rg50 (21 : Fin 32), g49_21]
  have g50_22 : reg n50 (22 : Fin 32) = ll := by rw [rg50 (22 : Fin 32), g49_22]
  have g50_23 : reg n50 (23 : Fin 32) = sgp := by rw [rg50 (23 : Fin 32), g49_23]
  have g50_24 : reg n50 (24 : Fin 32) = kp := by rw [rg50 (24 : Fin 32), g49_24]
  have g50_25 : reg n50 (25 : Fin 32) = sgl := by rw [rg50 (25 : Fin 32), g49_25]
  have g50_26 : reg n50 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rg50 (26 : Fin 32), g49_26]
  have g50_27 : reg n50 (27 : Fin 32) = tbl := by rw [rg50 (27 : Fin 32), g49_27]
  have keep_kk50 : SvKeepL B n0.mem n50.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4)] := keep_kk49.trans K50.toL
  clear keep_kk49
  have w50_2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K50.w32 (by decide) (by decide)).trans w49_2c
  have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K50.w32 (by decide) (by decide)).trans w49_30
  have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K50.w32 (by decide) (by decide)).trans w49_34
  have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K50.w32 (by decide) (by decide)).trans w49_38
  have w50_44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K50.w32 (by decide) (by decide)).trans w49_44
  have w50_48 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K50.w32 (by decide) (by decide)).trans w49_48
  have w50_4c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K50.w32 (by decide) (by decide)).trans w49_4c
  have w50_50 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K50.w32 (by decide) (by decide)).trans w49_50
  have w50_54 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K50.w32 (by decide) (by decide)).trans w49_54
  have w50_58 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K50.w32 (by decide) (by decide)).trans w49_58
  have w50_5c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K50.w32 (by decide) (by decide)).trans w49_5c
  have w50_60 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K50.w32 (by decide) (by decide)).trans w49_60
  have w50_64 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K50.w32 (by decide) (by decide)).trans w49_64
  have w50_68 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K50.w32 (by decide) (by decide)).trans w49_68
  have w50_6c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K50.w32 (by decide) (by decide)).trans w49_6c
  have w50_70 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K50.w32 (by decide) (by decide)).trans w49_70
  have w50_74 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K50.w32 (by decide) (by decide)).trans w49_74
  have w50_78 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K50.w32 (by decide) (by decide)).trans w49_78
  have w50_7c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K50.w32 (by decide) (by decide)).trans w49_7c
  have w50_80 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K50.w32 (by decide) (by decide)).trans w49_80
  have w50_84 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K50.w32 (by decide) (by decide)).trans w49_84
  have w50_88 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K50.w32 (by decide) (by decide)).trans w49_88
  have w50_8c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K50.w32 (by decide) (by decide)).trans w49_8c
  have w50_90 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K50.w32 (by decide) (by decide)).trans w49_90
  have w50_94 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K50.w32 (by decide) (by decide)).trans w49_94
  have w50_98 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K50.w32 (by decide) (by decide)).trans w49_98
  have w50_9c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K50.w32 (by decide) (by decide)).trans w49_9c
  have w50_a0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K50.w32 (by decide) (by decide)).trans w49_a0
  have w50_a4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K50.w32 (by decide) (by decide)).trans w49_a4
  have w50_150 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K50.w32 (by decide) (by decide)).trans w49_150
  have w50_154 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K50.w32 (by decide) (by decide)).trans w49_154
  have w50_158 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K50.w32 (by decide) (by decide)).trans w49_158
  have w50_15c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K50.w32 (by decide) (by decide)).trans w49_15c
  have w50_380 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [W50, g49_10]
  clear w49_15c w49_158 w49_154 w49_150 w49_a4 w49_a0 w49_9c w49_98 w49_94 w49_90 w49_8c w49_88 w49_84 w49_80 w49_7c w49_78 w49_74 w49_70 w49_6c w49_68 w49_64 w49_60 w49_5c w49_58 w49_54 w49_50 w49_4c w49_48 w49_44 w49_38 w49_34 w49_30 w49_2c g49_12 g49_27 g49_26 g49_25 g49_24 g49_23 g49_22 g49_21 g49_20 g49_19 g49_18 g49_11 g49_10 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 rb49 s49 m49 u49 c49
  -- 0x728: lw
  obtain ⟨n51, d51, u51⟩ := s50.lw E50.self sv_at_728 (off' := 0x72A) (by decide)
    (by rw [g50_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s51 : St n51.mem SV n51 0x72A (reg n51) := ⟨u51.pc, rfl, fun _ => rfl⟩
  have m51 : n51.mem = n50.mem := u51.mem
  have fr51 : ∀ x, SvR B x → n51.mem x = n50.mem x := fun x _ => by rw [m51]
  have t51 : Steps n0 n51 := t50.trans (.single d51)
  have fR51 : ∀ x, SvR B x → n51.mem x = M0 x := fun x hx => (fr51 x hx).trans (fR50 x hx)
  have E51 : SvCode n51.mem := E50.fr F fr51
  have V51 : SvSaves B n51.mem v := V50.same m51
  have g51_2 : reg n51 sp = B + 0x21A0 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_2]
  have g51_3 : reg n51 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u51.regs, upd_ne (by decide) (by decide), g50_3]
  have g51_4 : reg n51 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u51.regs, upd_ne (by decide) (by decide), g50_4]
  have g51_8 : reg n51 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_8]
  have g51_9 : reg n51 (9 : Fin 32) = tbp := by rw [u51.regs, upd_ne (by decide) (by decide), g50_9]
  have g51_10 : reg n51 a0 = vp := by rw [u51.regs, upd_ne (by decide) (by decide), g50_10]
  have g51_12 : reg n51 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_12]
  have g51_18 : reg n51 (18 : Fin 32) = out := by rw [u51.regs, upd_ne (by decide) (by decide), g50_18]
  have g51_19 : reg n51 (19 : Fin 32) = bp := by rw [u51.regs, upd_ne (by decide) (by decide), g50_19]
  have g51_20 : reg n51 (20 : Fin 32) = dg := by rw [u51.regs, upd_ne (by decide) (by decide), g50_20]
  have g51_21 : reg n51 (21 : Fin 32) = rootp := by rw [u51.regs, upd_ne (by decide) (by decide), g50_21]
  have g51_22 : reg n51 (22 : Fin 32) = ll := by rw [u51.regs, upd_ne (by decide) (by decide), g50_22]
  have g51_23 : reg n51 (23 : Fin 32) = sgp := by rw [u51.regs, upd_ne (by decide) (by decide), g50_23]
  have g51_24 : reg n51 (24 : Fin 32) = kp := by rw [u51.regs, upd_ne (by decide) (by decide), g50_24]
  have g51_25 : reg n51 (25 : Fin 32) = sgl := by rw [u51.regs, upd_ne (by decide) (by decide), g50_25]
  have g51_26 : reg n51 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u51.regs, upd_ne (by decide) (by decide), g50_26]
  have g51_27 : reg n51 (27 : Fin 32) = tbl := by rw [u51.regs, upd_ne (by decide) (by decide), g50_27]
  have g51_11 : reg n51 a1 = vl := by
    rw [u51.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g50_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr, w50_34]
  have keep_kk51 : SvKeepL B n0.mem n51.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4)] := by rw [m51]; exact keep_kk50
  clear keep_kk50
  have w51_2c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m51]; exact w50_2c
  have w51_30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m51]; exact w50_30
  have w51_34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m51]; exact w50_34
  have w51_38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m51]; exact w50_38
  have w51_44 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m51]; exact w50_44
  have w51_48 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m51]; exact w50_48
  have w51_4c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m51]; exact w50_4c
  have w51_50 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m51]; exact w50_50
  have w51_54 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m51]; exact w50_54
  have w51_58 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m51]; exact w50_58
  have w51_5c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m51]; exact w50_5c
  have w51_60 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m51]; exact w50_60
  have w51_64 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m51]; exact w50_64
  have w51_68 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m51]; exact w50_68
  have w51_6c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m51]; exact w50_6c
  have w51_70 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m51]; exact w50_70
  have w51_74 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m51]; exact w50_74
  have w51_78 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m51]; exact w50_78
  have w51_7c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m51]; exact w50_7c
  have w51_80 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m51]; exact w50_80
  have w51_84 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m51]; exact w50_84
  have w51_88 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m51]; exact w50_88
  have w51_8c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m51]; exact w50_8c
  have w51_90 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m51]; exact w50_90
  have w51_94 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m51]; exact w50_94
  have w51_98 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m51]; exact w50_98
  have w51_9c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m51]; exact w50_9c
  have w51_a0 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m51]; exact w50_a0
  have w51_a4 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m51]; exact w50_a4
  have w51_150 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m51]; exact w50_150
  have w51_154 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m51]; exact w50_154
  have w51_158 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m51]; exact w50_158
  have w51_15c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m51]; exact w50_15c
  have w51_380 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m51]; exact w50_380
  clear w50_380 w50_15c w50_158 w50_154 w50_150 w50_a4 w50_a0 w50_9c w50_98 w50_94 w50_90 w50_8c w50_88 w50_84 w50_80 w50_7c w50_78 w50_74 w50_70 w50_6c w50_68 w50_64 w50_60 w50_5c w50_58 w50_54 w50_50 w50_4c w50_48 w50_44 w50_38 w50_34 w50_30 w50_2c g50_27 g50_26 g50_25 g50_24 g50_23 g50_22 g50_21 g50_20 g50_19 g50_18 g50_12 g50_11 g50_10 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 rg50 W50 K50 fr50 s50 d50
  -- 0x72A: sw
  obtain ⟨n52, d52, s52, fr52, K52, W52, rg52⟩ := sv_sw F E51 s51 sv_at_72a (off' := 0x72C) (c := 0x384)
    (by decide) (by rw [g51_12]; sv_addr) (by decide) (by decide)
  have t52 : Steps n0 n52 := t51.trans d52
  have fR52 : ∀ x, SvR B x → n52.mem x = M0 x := fun x hx => (fr52 x hx).trans (fR51 x hx)
  have E52 : SvCode n52.mem := E51.fr F fr52
  have V52 : SvSaves B n52.mem v := V51.keep K52 (by decide)
  have g52_2 : reg n52 sp = B + 0x21A0 := by rw [rg52 sp, g51_2]
  have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg52 (3 : Fin 32), g51_3]
  have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg52 (4 : Fin 32), g51_4]
  have g52_8 : reg n52 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg52 (8 : Fin 32), g51_8]
  have g52_9 : reg n52 (9 : Fin 32) = tbp := by rw [rg52 (9 : Fin 32), g51_9]
  have g52_10 : reg n52 a0 = vp := by rw [rg52 a0, g51_10]
  have g52_11 : reg n52 a1 = vl := by rw [rg52 a1, g51_11]
  have g52_12 : reg n52 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg52 a2, g51_12]
  have g52_18 : reg n52 (18 : Fin 32) = out := by rw [rg52 (18 : Fin 32), g51_18]
  have g52_19 : reg n52 (19 : Fin 32) = bp := by rw [rg52 (19 : Fin 32), g51_19]
  have g52_20 : reg n52 (20 : Fin 32) = dg := by rw [rg52 (20 : Fin 32), g51_20]
  have g52_21 : reg n52 (21 : Fin 32) = rootp := by rw [rg52 (21 : Fin 32), g51_21]
  have g52_22 : reg n52 (22 : Fin 32) = ll := by rw [rg52 (22 : Fin 32), g51_22]
  have g52_23 : reg n52 (23 : Fin 32) = sgp := by rw [rg52 (23 : Fin 32), g51_23]
  have g52_24 : reg n52 (24 : Fin 32) = kp := by rw [rg52 (24 : Fin 32), g51_24]
  have g52_25 : reg n52 (25 : Fin 32) = sgl := by rw [rg52 (25 : Fin 32), g51_25]
  have g52_26 : reg n52 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rg52 (26 : Fin 32), g51_26]
  have g52_27 : reg n52 (27 : Fin 32) = tbl := by rw [rg52 (27 : Fin 32), g51_27]
  have keep_kk52 : SvKeepL B n0.mem n52.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4)] := keep_kk51.trans K52.toL
  clear keep_kk51
  have w52_2c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K52.w32 (by decide) (by decide)).trans w51_2c
  have w52_30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K52.w32 (by decide) (by decide)).trans w51_30
  have w52_34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K52.w32 (by decide) (by decide)).trans w51_34
  have w52_38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K52.w32 (by decide) (by decide)).trans w51_38
  have w52_44 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K52.w32 (by decide) (by decide)).trans w51_44
  have w52_48 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K52.w32 (by decide) (by decide)).trans w51_48
  have w52_4c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K52.w32 (by decide) (by decide)).trans w51_4c
  have w52_50 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K52.w32 (by decide) (by decide)).trans w51_50
  have w52_54 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K52.w32 (by decide) (by decide)).trans w51_54
  have w52_58 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K52.w32 (by decide) (by decide)).trans w51_58
  have w52_5c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K52.w32 (by decide) (by decide)).trans w51_5c
  have w52_60 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K52.w32 (by decide) (by decide)).trans w51_60
  have w52_64 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K52.w32 (by decide) (by decide)).trans w51_64
  have w52_68 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K52.w32 (by decide) (by decide)).trans w51_68
  have w52_6c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K52.w32 (by decide) (by decide)).trans w51_6c
  have w52_70 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K52.w32 (by decide) (by decide)).trans w51_70
  have w52_74 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K52.w32 (by decide) (by decide)).trans w51_74
  have w52_78 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K52.w32 (by decide) (by decide)).trans w51_78
  have w52_7c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K52.w32 (by decide) (by decide)).trans w51_7c
  have w52_80 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K52.w32 (by decide) (by decide)).trans w51_80
  have w52_84 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K52.w32 (by decide) (by decide)).trans w51_84
  have w52_88 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K52.w32 (by decide) (by decide)).trans w51_88
  have w52_8c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K52.w32 (by decide) (by decide)).trans w51_8c
  have w52_90 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K52.w32 (by decide) (by decide)).trans w51_90
  have w52_94 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K52.w32 (by decide) (by decide)).trans w51_94
  have w52_98 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K52.w32 (by decide) (by decide)).trans w51_98
  have w52_9c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K52.w32 (by decide) (by decide)).trans w51_9c
  have w52_a0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K52.w32 (by decide) (by decide)).trans w51_a0
  have w52_a4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K52.w32 (by decide) (by decide)).trans w51_a4
  have w52_150 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K52.w32 (by decide) (by decide)).trans w51_150
  have w52_154 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K52.w32 (by decide) (by decide)).trans w51_154
  have w52_158 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K52.w32 (by decide) (by decide)).trans w51_158
  have w52_15c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K52.w32 (by decide) (by decide)).trans w51_15c
  have w52_380 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K52.w32 (by decide) (by decide)).trans w51_380
  have w52_384 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [W52, g51_11]
  clear w51_380 w51_15c w51_158 w51_154 w51_150 w51_a4 w51_a0 w51_9c w51_98 w51_94 w51_90 w51_8c w51_88 w51_84 w51_80 w51_7c w51_78 w51_74 w51_70 w51_6c w51_68 w51_64 w51_60 w51_5c w51_58 w51_54 w51_50 w51_4c w51_48 w51_44 w51_38 w51_34 w51_30 w51_2c g51_11 g51_27 g51_26 g51_25 g51_24 g51_23 g51_22 g51_21 g51_20 g51_19 g51_18 g51_12 g51_10 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 m51 s51 u51 d51
  -- 0x72C: sw
  obtain ⟨n53, d53, s53, fr53, K53, W53, rg53⟩ := sv_sw F E52 s52 sv_at_72c (off' := 0x72E) (c := 0x388)
    (by decide) (by rw [g52_12]; sv_addr) (by decide) (by decide)
  have t53 : Steps n0 n53 := t52.trans d53
  have fR53 : ∀ x, SvR B x → n53.mem x = M0 x := fun x hx => (fr53 x hx).trans (fR52 x hx)
  have E53 : SvCode n53.mem := E52.fr F fr53
  have V53 : SvSaves B n53.mem v := V52.keep K53 (by decide)
  have g53_2 : reg n53 sp = B + 0x21A0 := by rw [rg53 sp, g52_2]
  have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg53 (3 : Fin 32), g52_3]
  have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg53 (4 : Fin 32), g52_4]
  have g53_8 : reg n53 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg53 (8 : Fin 32), g52_8]
  have g53_9 : reg n53 (9 : Fin 32) = tbp := by rw [rg53 (9 : Fin 32), g52_9]
  have g53_10 : reg n53 a0 = vp := by rw [rg53 a0, g52_10]
  have g53_11 : reg n53 a1 = vl := by rw [rg53 a1, g52_11]
  have g53_12 : reg n53 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg53 a2, g52_12]
  have g53_18 : reg n53 (18 : Fin 32) = out := by rw [rg53 (18 : Fin 32), g52_18]
  have g53_19 : reg n53 (19 : Fin 32) = bp := by rw [rg53 (19 : Fin 32), g52_19]
  have g53_20 : reg n53 (20 : Fin 32) = dg := by rw [rg53 (20 : Fin 32), g52_20]
  have g53_21 : reg n53 (21 : Fin 32) = rootp := by rw [rg53 (21 : Fin 32), g52_21]
  have g53_22 : reg n53 (22 : Fin 32) = ll := by rw [rg53 (22 : Fin 32), g52_22]
  have g53_23 : reg n53 (23 : Fin 32) = sgp := by rw [rg53 (23 : Fin 32), g52_23]
  have g53_24 : reg n53 (24 : Fin 32) = kp := by rw [rg53 (24 : Fin 32), g52_24]
  have g53_25 : reg n53 (25 : Fin 32) = sgl := by rw [rg53 (25 : Fin 32), g52_25]
  have g53_26 : reg n53 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rg53 (26 : Fin 32), g52_26]
  have g53_27 : reg n53 (27 : Fin 32) = tbl := by rw [rg53 (27 : Fin 32), g52_27]
  have keep_kk53 : SvKeepL B n0.mem n53.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4)] := keep_kk52.trans K53.toL
  clear keep_kk52
  have w53_2c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K53.w32 (by decide) (by decide)).trans w52_2c
  have w53_30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K53.w32 (by decide) (by decide)).trans w52_30
  have w53_34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K53.w32 (by decide) (by decide)).trans w52_34
  have w53_38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K53.w32 (by decide) (by decide)).trans w52_38
  have w53_44 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K53.w32 (by decide) (by decide)).trans w52_44
  have w53_48 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K53.w32 (by decide) (by decide)).trans w52_48
  have w53_4c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K53.w32 (by decide) (by decide)).trans w52_4c
  have w53_50 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K53.w32 (by decide) (by decide)).trans w52_50
  have w53_54 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K53.w32 (by decide) (by decide)).trans w52_54
  have w53_58 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K53.w32 (by decide) (by decide)).trans w52_58
  have w53_5c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K53.w32 (by decide) (by decide)).trans w52_5c
  have w53_60 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K53.w32 (by decide) (by decide)).trans w52_60
  have w53_64 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K53.w32 (by decide) (by decide)).trans w52_64
  have w53_68 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K53.w32 (by decide) (by decide)).trans w52_68
  have w53_6c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K53.w32 (by decide) (by decide)).trans w52_6c
  have w53_70 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K53.w32 (by decide) (by decide)).trans w52_70
  have w53_74 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K53.w32 (by decide) (by decide)).trans w52_74
  have w53_78 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K53.w32 (by decide) (by decide)).trans w52_78
  have w53_7c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K53.w32 (by decide) (by decide)).trans w52_7c
  have w53_80 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K53.w32 (by decide) (by decide)).trans w52_80
  have w53_84 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K53.w32 (by decide) (by decide)).trans w52_84
  have w53_88 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K53.w32 (by decide) (by decide)).trans w52_88
  have w53_8c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K53.w32 (by decide) (by decide)).trans w52_8c
  have w53_90 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K53.w32 (by decide) (by decide)).trans w52_90
  have w53_94 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K53.w32 (by decide) (by decide)).trans w52_94
  have w53_98 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K53.w32 (by decide) (by decide)).trans w52_98
  have w53_9c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K53.w32 (by decide) (by decide)).trans w52_9c
  have w53_a0 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K53.w32 (by decide) (by decide)).trans w52_a0
  have w53_a4 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K53.w32 (by decide) (by decide)).trans w52_a4
  have w53_150 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K53.w32 (by decide) (by decide)).trans w52_150
  have w53_154 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K53.w32 (by decide) (by decide)).trans w52_154
  have w53_158 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K53.w32 (by decide) (by decide)).trans w52_158
  have w53_15c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K53.w32 (by decide) (by decide)).trans w52_15c
  have w53_380 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K53.w32 (by decide) (by decide)).trans w52_380
  have w53_384 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K53.w32 (by decide) (by decide)).trans w52_384
  have w53_388 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = vp := by rw [W53, g52_10]
  clear w52_384 w52_380 w52_15c w52_158 w52_154 w52_150 w52_a4 w52_a0 w52_9c w52_98 w52_94 w52_90 w52_8c w52_88 w52_84 w52_80 w52_7c w52_78 w52_74 w52_70 w52_6c w52_68 w52_64 w52_60 w52_5c w52_58 w52_54 w52_50 w52_4c w52_48 w52_44 w52_38 w52_34 w52_30 w52_2c g52_27 g52_26 g52_25 g52_24 g52_23 g52_22 g52_21 g52_20 g52_19 g52_18 g52_12 g52_11 g52_10 g52_9 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 rg52 W52 K52 fr52 s52 d52
  -- 0x72E: sw
  obtain ⟨n54, d54, s54, fr54, K54, W54, rg54⟩ := sv_sw F E53 s53 sv_at_72e (off' := 0x730) (c := 0x38C)
    (by decide) (by rw [g53_12]; sv_addr) (by decide) (by decide)
  have t54 : Steps n0 n54 := t53.trans d54
  have fR54 : ∀ x, SvR B x → n54.mem x = M0 x := fun x hx => (fr54 x hx).trans (fR53 x hx)
  have E54 : SvCode n54.mem := E53.fr F fr54
  have V54 : SvSaves B n54.mem v := V53.keep K54 (by decide)
  have g54_2 : reg n54 sp = B + 0x21A0 := by rw [rg54 sp, g53_2]
  have g54_3 : reg n54 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg54 (3 : Fin 32), g53_3]
  have g54_4 : reg n54 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg54 (4 : Fin 32), g53_4]
  have g54_8 : reg n54 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg54 (8 : Fin 32), g53_8]
  have g54_9 : reg n54 (9 : Fin 32) = tbp := by rw [rg54 (9 : Fin 32), g53_9]
  have g54_10 : reg n54 a0 = vp := by rw [rg54 a0, g53_10]
  have g54_11 : reg n54 a1 = vl := by rw [rg54 a1, g53_11]
  have g54_12 : reg n54 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg54 a2, g53_12]
  have g54_18 : reg n54 (18 : Fin 32) = out := by rw [rg54 (18 : Fin 32), g53_18]
  have g54_19 : reg n54 (19 : Fin 32) = bp := by rw [rg54 (19 : Fin 32), g53_19]
  have g54_20 : reg n54 (20 : Fin 32) = dg := by rw [rg54 (20 : Fin 32), g53_20]
  have g54_21 : reg n54 (21 : Fin 32) = rootp := by rw [rg54 (21 : Fin 32), g53_21]
  have g54_22 : reg n54 (22 : Fin 32) = ll := by rw [rg54 (22 : Fin 32), g53_22]
  have g54_23 : reg n54 (23 : Fin 32) = sgp := by rw [rg54 (23 : Fin 32), g53_23]
  have g54_24 : reg n54 (24 : Fin 32) = kp := by rw [rg54 (24 : Fin 32), g53_24]
  have g54_25 : reg n54 (25 : Fin 32) = sgl := by rw [rg54 (25 : Fin 32), g53_25]
  have g54_26 : reg n54 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rg54 (26 : Fin 32), g53_26]
  have g54_27 : reg n54 (27 : Fin 32) = tbl := by rw [rg54 (27 : Fin 32), g53_27]
  have keep_kk54 : SvKeepL B n0.mem n54.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4)] := keep_kk53.trans K54.toL
  clear keep_kk53
  have w54_2c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K54.w32 (by decide) (by decide)).trans w53_2c
  have w54_30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K54.w32 (by decide) (by decide)).trans w53_30
  have w54_34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K54.w32 (by decide) (by decide)).trans w53_34
  have w54_38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K54.w32 (by decide) (by decide)).trans w53_38
  have w54_44 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K54.w32 (by decide) (by decide)).trans w53_44
  have w54_48 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K54.w32 (by decide) (by decide)).trans w53_48
  have w54_4c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K54.w32 (by decide) (by decide)).trans w53_4c
  have w54_50 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K54.w32 (by decide) (by decide)).trans w53_50
  have w54_54 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K54.w32 (by decide) (by decide)).trans w53_54
  have w54_58 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K54.w32 (by decide) (by decide)).trans w53_58
  have w54_5c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K54.w32 (by decide) (by decide)).trans w53_5c
  have w54_60 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K54.w32 (by decide) (by decide)).trans w53_60
  have w54_64 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K54.w32 (by decide) (by decide)).trans w53_64
  have w54_68 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K54.w32 (by decide) (by decide)).trans w53_68
  have w54_6c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K54.w32 (by decide) (by decide)).trans w53_6c
  have w54_70 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K54.w32 (by decide) (by decide)).trans w53_70
  have w54_74 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K54.w32 (by decide) (by decide)).trans w53_74
  have w54_78 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K54.w32 (by decide) (by decide)).trans w53_78
  have w54_7c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K54.w32 (by decide) (by decide)).trans w53_7c
  have w54_80 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K54.w32 (by decide) (by decide)).trans w53_80
  have w54_84 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K54.w32 (by decide) (by decide)).trans w53_84
  have w54_88 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K54.w32 (by decide) (by decide)).trans w53_88
  have w54_8c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K54.w32 (by decide) (by decide)).trans w53_8c
  have w54_90 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K54.w32 (by decide) (by decide)).trans w53_90
  have w54_94 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K54.w32 (by decide) (by decide)).trans w53_94
  have w54_98 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K54.w32 (by decide) (by decide)).trans w53_98
  have w54_9c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K54.w32 (by decide) (by decide)).trans w53_9c
  have w54_a0 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K54.w32 (by decide) (by decide)).trans w53_a0
  have w54_a4 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K54.w32 (by decide) (by decide)).trans w53_a4
  have w54_150 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K54.w32 (by decide) (by decide)).trans w53_150
  have w54_154 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K54.w32 (by decide) (by decide)).trans w53_154
  have w54_158 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K54.w32 (by decide) (by decide)).trans w53_158
  have w54_15c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K54.w32 (by decide) (by decide)).trans w53_15c
  have w54_380 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K54.w32 (by decide) (by decide)).trans w53_380
  have w54_384 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K54.w32 (by decide) (by decide)).trans w53_384
  have w54_388 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = vp := (K54.w32 (by decide) (by decide)).trans w53_388
  have w54_38c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = vl := by rw [W54, g53_11]
  clear w53_388 w53_384 w53_380 w53_15c w53_158 w53_154 w53_150 w53_a4 w53_a0 w53_9c w53_98 w53_94 w53_90 w53_8c w53_88 w53_84 w53_80 w53_7c w53_78 w53_74 w53_70 w53_6c w53_68 w53_64 w53_60 w53_5c w53_58 w53_54 w53_50 w53_4c w53_48 w53_44 w53_38 w53_34 w53_30 w53_2c g53_27 g53_26 g53_25 g53_24 g53_23 g53_22 g53_21 g53_20 g53_19 g53_18 g53_12 g53_11 g53_10 g53_9 g53_8 g53_4 g53_3 g53_2 V53 E53 fR53 t53 rg53 W53 K53 fr53 s53 d53
  -- 0x730
  obtain ⟨n55, c55, u55⟩ := s54.block svDp1730 E54.self svDp1730_end
    ⟨trivial, trivial, trivial⟩
  have m55 : n55.mem = n54.mem := u55.mem
  have s55 : St n55.mem SV n55 0x736 (reg n55) := ⟨u55.pc, rfl, fun _ => rfl⟩
  have rb55 : ∀ q, reg n55 q = (runBlock svDp1730 (n54.mem, reg n54)).2 q := fun q => by rw [u55.regs]
  have fr55 : ∀ x, SvR B x → n55.mem x = n54.mem x := fun x _ => by rw [m55]
  have t55 : Steps n0 n55 := t54.trans c55
  have fR55 : ∀ x, SvR B x → n55.mem x = M0 x := fun x hx => (fr55 x hx).trans (fR54 x hx)
  have E55 : SvCode n55.mem := E54.fr F fr55
  have V55 : SvSaves B n55.mem v := V54.same m55
  have g55_2 : reg n55 sp = B + 0x21A0 := by
    rw [rb55, runBlock_reg _ _ _ sp s54.zero (by decide), g54_2]
  have g55_3 : reg n55 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb55, runBlock_reg _ _ _ (3 : Fin 32) s54.zero (by decide), g54_3]
  have g55_4 : reg n55 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb55, runBlock_reg _ _ _ (4 : Fin 32) s54.zero (by decide), g54_4]
  have g55_8 : reg n55 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb55, runBlock_reg _ _ _ (8 : Fin 32) s54.zero (by decide), g54_8]
  have g55_9 : reg n55 (9 : Fin 32) = tbp := by
    rw [rb55, runBlock_reg _ _ _ (9 : Fin 32) s54.zero (by decide), g54_9]
  have g55_12 : reg n55 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb55, runBlock_reg _ _ _ a2 s54.zero (by decide), g54_12]
  have g55_18 : reg n55 (18 : Fin 32) = out := by
    rw [rb55, runBlock_reg _ _ _ (18 : Fin 32) s54.zero (by decide), g54_18]
  have g55_19 : reg n55 (19 : Fin 32) = bp := by
    rw [rb55, runBlock_reg _ _ _ (19 : Fin 32) s54.zero (by decide), g54_19]
  have g55_20 : reg n55 (20 : Fin 32) = dg := by
    rw [rb55, runBlock_reg _ _ _ (20 : Fin 32) s54.zero (by decide), g54_20]
  have g55_21 : reg n55 (21 : Fin 32) = rootp := by
    rw [rb55, runBlock_reg _ _ _ (21 : Fin 32) s54.zero (by decide), g54_21]
  have g55_22 : reg n55 (22 : Fin 32) = ll := by
    rw [rb55, runBlock_reg _ _ _ (22 : Fin 32) s54.zero (by decide), g54_22]
  have g55_23 : reg n55 (23 : Fin 32) = sgp := by
    rw [rb55, runBlock_reg _ _ _ (23 : Fin 32) s54.zero (by decide), g54_23]
  have g55_24 : reg n55 (24 : Fin 32) = kp := by
    rw [rb55, runBlock_reg _ _ _ (24 : Fin 32) s54.zero (by decide), g54_24]
  have g55_25 : reg n55 (25 : Fin 32) = sgl := by
    rw [rb55, runBlock_reg _ _ _ (25 : Fin 32) s54.zero (by decide), g54_25]
  have g55_26 : reg n55 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by
    rw [rb55, runBlock_reg _ _ _ (26 : Fin 32) s54.zero (by decide), g54_26]
  have g55_27 : reg n55 (27 : Fin 32) = tbl := by
    rw [rb55, runBlock_reg _ _ _ (27 : Fin 32) s54.zero (by decide), g54_27]
  have g55_10 : reg n55 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, svDp1730, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_10, g54_11, g54_12, g54_18, g54_19, g54_20, g54_21, g54_22, g54_23, g54_24, g54_25, g54_26, g54_27, s54.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g55_11 : reg n55 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb55]; simp +decide only [runBlock, BInstr.run, svDp1730, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g54_2, g54_3, g54_4, g54_8, g54_9, g54_10, g54_11, g54_12, g54_18, g54_19, g54_20, g54_21, g54_22, g54_23, g54_24, g54_25, g54_26, g54_27, s54.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk55 : SvKeepL B n0.mem n55.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4)] := by rw [m55]; exact keep_kk54
  clear keep_kk54
  have w55_2c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m55]; exact w54_2c
  have w55_30 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m55]; exact w54_30
  have w55_34 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m55]; exact w54_34
  have w55_38 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m55]; exact w54_38
  have w55_44 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m55]; exact w54_44
  have w55_48 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m55]; exact w54_48
  have w55_4c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m55]; exact w54_4c
  have w55_50 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m55]; exact w54_50
  have w55_54 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m55]; exact w54_54
  have w55_58 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m55]; exact w54_58
  have w55_5c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m55]; exact w54_5c
  have w55_60 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m55]; exact w54_60
  have w55_64 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m55]; exact w54_64
  have w55_68 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m55]; exact w54_68
  have w55_6c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m55]; exact w54_6c
  have w55_70 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m55]; exact w54_70
  have w55_74 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m55]; exact w54_74
  have w55_78 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m55]; exact w54_78
  have w55_7c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m55]; exact w54_7c
  have w55_80 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m55]; exact w54_80
  have w55_84 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m55]; exact w54_84
  have w55_88 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m55]; exact w54_88
  have w55_8c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m55]; exact w54_8c
  have w55_90 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m55]; exact w54_90
  have w55_94 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m55]; exact w54_94
  have w55_98 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m55]; exact w54_98
  have w55_9c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m55]; exact w54_9c
  have w55_a0 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m55]; exact w54_a0
  have w55_a4 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m55]; exact w54_a4
  have w55_150 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m55]; exact w54_150
  have w55_154 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m55]; exact w54_154
  have w55_158 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m55]; exact w54_158
  have w55_15c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m55]; exact w54_15c
  have w55_380 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m55]; exact w54_380
  have w55_384 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m55]; exact w54_384
  have w55_388 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = vp := by rw [m55]; exact w54_388
  have w55_38c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = vl := by rw [m55]; exact w54_38c
  clear w54_38c w54_388 w54_384 w54_380 w54_15c w54_158 w54_154 w54_150 w54_a4 w54_a0 w54_9c w54_98 w54_94 w54_90 w54_8c w54_88 w54_84 w54_80 w54_7c w54_78 w54_74 w54_70 w54_6c w54_68 w54_64 w54_60 w54_5c w54_58 w54_54 w54_50 w54_4c w54_48 w54_44 w54_38 w54_34 w54_30 w54_2c g54_27 g54_26 g54_25 g54_24 g54_23 g54_22 g54_21 g54_20 g54_19 g54_18 g54_12 g54_11 g54_10 g54_9 g54_8 g54_4 g54_3 g54_2 V54 E54 fR54 t54 rg54 W54 K54 fr54 s54 d54
  -- 0x736: sv_tlvF
  obtain ⟨n56, c56, s56, rk56, K56, Ok56, Er56, fr56⟩ := sv_tlvF (oc := 0x420) (dc := 0x380)
    F E55 s55 sv_at_736 sv_at_73a (by decide) (by decide) g55_10
    g55_11 (by decide) (by decide) (by decide) (by decide) (by decide)
    w55_388 w55_38c
  have t56 : Steps n0 n56 := t55.trans c56
  have fR56 : ∀ x, SvR B x → n56.mem x = M0 x := fun x hx => (fr56 x hx).trans (fR55 x hx)
  have E56 : SvCode n56.mem := E55.fr F fr56
  have V56 : SvSaves B n56.mem v := V55.keepL K56 (by decide)
  rw [sv_mb fR55 val_in] at Ok56 Er56
  have g56_2 : reg n56 sp = B + 0x21A0 := by rw [rk56 sp (by decide) (by decide), g55_2]
  have g56_3 : reg n56 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk56 (3 : Fin 32) (by decide) (by decide), g55_3]
  have g56_4 : reg n56 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk56 (4 : Fin 32) (by decide) (by decide), g55_4]
  have g56_8 : reg n56 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk56 (8 : Fin 32) (by decide) (by decide), g55_8]
  have g56_9 : reg n56 (9 : Fin 32) = tbp := by rw [rk56 (9 : Fin 32) (by decide) (by decide), g55_9]
  have g56_10 : reg n56 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [rk56 a0 (by decide) (by decide), g55_10]
  have g56_18 : reg n56 (18 : Fin 32) = out := by rw [rk56 (18 : Fin 32) (by decide) (by decide), g55_18]
  have g56_19 : reg n56 (19 : Fin 32) = bp := by rw [rk56 (19 : Fin 32) (by decide) (by decide), g55_19]
  have g56_20 : reg n56 (20 : Fin 32) = dg := by rw [rk56 (20 : Fin 32) (by decide) (by decide), g55_20]
  have g56_21 : reg n56 (21 : Fin 32) = rootp := by rw [rk56 (21 : Fin 32) (by decide) (by decide), g55_21]
  have g56_22 : reg n56 (22 : Fin 32) = ll := by rw [rk56 (22 : Fin 32) (by decide) (by decide), g55_22]
  have g56_23 : reg n56 (23 : Fin 32) = sgp := by rw [rk56 (23 : Fin 32) (by decide) (by decide), g55_23]
  have g56_24 : reg n56 (24 : Fin 32) = kp := by rw [rk56 (24 : Fin 32) (by decide) (by decide), g55_24]
  have g56_25 : reg n56 (25 : Fin 32) = sgl := by rw [rk56 (25 : Fin 32) (by decide) (by decide), g55_25]
  have g56_26 : reg n56 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rk56 (26 : Fin 32) (by decide) (by decide), g55_26]
  have g56_27 : reg n56 (27 : Fin 32) = tbl := by rw [rk56 (27 : Fin 32) (by decide) (by decide), g55_27]
  obtain ⟨r56, hr56⟩ : ∃ r, derTlv (memBytes M0 (vp) (vl).toNat) = r := ⟨_, rfl⟩
  rcases r56 with er56 | tl56
  · obtain ⟨zhr56, ezhr56⟩ := Er56 er56 hr56
    have keep_kk56 : SvKeepL B n0.mem n56.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := keep_kk55.trans K56
    clear keep_kk55
    have w56_2c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K56.w32 (by decide) (by decide)).trans w55_2c
    have w56_30 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K56.w32 (by decide) (by decide)).trans w55_30
    have w56_34 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K56.w32 (by decide) (by decide)).trans w55_34
    have w56_38 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K56.w32 (by decide) (by decide)).trans w55_38
    have w56_44 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K56.w32 (by decide) (by decide)).trans w55_44
    have w56_48 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K56.w32 (by decide) (by decide)).trans w55_48
    have w56_4c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K56.w32 (by decide) (by decide)).trans w55_4c
    have w56_50 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K56.w32 (by decide) (by decide)).trans w55_50
    have w56_54 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K56.w32 (by decide) (by decide)).trans w55_54
    have w56_58 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K56.w32 (by decide) (by decide)).trans w55_58
    have w56_5c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K56.w32 (by decide) (by decide)).trans w55_5c
    have w56_60 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K56.w32 (by decide) (by decide)).trans w55_60
    have w56_64 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K56.w32 (by decide) (by decide)).trans w55_64
    have w56_68 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K56.w32 (by decide) (by decide)).trans w55_68
    have w56_6c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K56.w32 (by decide) (by decide)).trans w55_6c
    have w56_70 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K56.w32 (by decide) (by decide)).trans w55_70
    have w56_74 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K56.w32 (by decide) (by decide)).trans w55_74
    have w56_78 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K56.w32 (by decide) (by decide)).trans w55_78
    have w56_7c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K56.w32 (by decide) (by decide)).trans w55_7c
    have w56_80 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K56.w32 (by decide) (by decide)).trans w55_80
    have w56_84 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K56.w32 (by decide) (by decide)).trans w55_84
    have w56_88 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K56.w32 (by decide) (by decide)).trans w55_88
    have w56_8c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K56.w32 (by decide) (by decide)).trans w55_8c
    have w56_90 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K56.w32 (by decide) (by decide)).trans w55_90
    have w56_94 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K56.w32 (by decide) (by decide)).trans w55_94
    have w56_98 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K56.w32 (by decide) (by decide)).trans w55_98
    have w56_9c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K56.w32 (by decide) (by decide)).trans w55_9c
    have w56_a0 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K56.w32 (by decide) (by decide)).trans w55_a0
    have w56_a4 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K56.w32 (by decide) (by decide)).trans w55_a4
    have w56_150 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K56.w32 (by decide) (by decide)).trans w55_150
    have w56_154 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K56.w32 (by decide) (by decide)).trans w55_154
    have w56_158 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K56.w32 (by decide) (by decide)).trans w55_158
    have w56_15c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K56.w32 (by decide) (by decide)).trans w55_15c
    have w56_380 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K56.w32 (by decide) (by decide)).trans w55_380
    have w56_384 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K56.w32 (by decide) (by decide)).trans w55_384
    have w56_420 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := zhr56
    have b56_424 : n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er56 := ezhr56
    clear w55_38c w55_388 w55_384 w55_380 w55_15c w55_158 w55_154 w55_150 w55_a4 w55_a0 w55_9c w55_98 w55_94 w55_90 w55_8c w55_88 w55_84 w55_80 w55_7c w55_78 w55_74 w55_70 w55_6c w55_68 w55_64 w55_60 w55_5c w55_58 w55_54 w55_50 w55_4c w55_48 w55_44 w55_38 w55_34 w55_30 w55_2c g55_11 g55_10 g55_27 g55_26 g55_25 g55_24 g55_23 g55_22 g55_21 g55_20 g55_19 g55_18 g55_12 g55_9 g55_8 g55_4 g55_3 g55_2 V55 E55 fR55 t55 fr55 rb55 s55 m55 u55 c55
    -- 0x73E: lw
    obtain ⟨n57, d57, u57⟩ := s56.lw E56.self sv_at_73e (off' := 0x742) (by decide)
      (by rw [g56_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s57 : St n57.mem SV n57 0x742 (reg n57) := ⟨u57.pc, rfl, fun _ => rfl⟩
    have m57 : n57.mem = n56.mem := u57.mem
    have fr57 : ∀ x, SvR B x → n57.mem x = n56.mem x := fun x _ => by rw [m57]
    have t57 : Steps n0 n57 := t56.trans (.single d57)
    have fR57 : ∀ x, SvR B x → n57.mem x = M0 x := fun x hx => (fr57 x hx).trans (fR56 x hx)
    have E57 : SvCode n57.mem := E56.fr F fr57
    have V57 : SvSaves B n57.mem v := V56.same m57
    have g57_2 : reg n57 sp = B + 0x21A0 := by rw [u57.regs, upd_ne (by decide) (by decide), g56_2]
    have g57_3 : reg n57 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u57.regs, upd_ne (by decide) (by decide), g56_3]
    have g57_4 : reg n57 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u57.regs, upd_ne (by decide) (by decide), g56_4]
    have g57_8 : reg n57 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u57.regs, upd_ne (by decide) (by decide), g56_8]
    have g57_9 : reg n57 (9 : Fin 32) = tbp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_9]
    have g57_18 : reg n57 (18 : Fin 32) = out := by rw [u57.regs, upd_ne (by decide) (by decide), g56_18]
    have g57_19 : reg n57 (19 : Fin 32) = bp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_19]
    have g57_20 : reg n57 (20 : Fin 32) = dg := by rw [u57.regs, upd_ne (by decide) (by decide), g56_20]
    have g57_21 : reg n57 (21 : Fin 32) = rootp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_21]
    have g57_22 : reg n57 (22 : Fin 32) = ll := by rw [u57.regs, upd_ne (by decide) (by decide), g56_22]
    have g57_23 : reg n57 (23 : Fin 32) = sgp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_23]
    have g57_24 : reg n57 (24 : Fin 32) = kp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_24]
    have g57_25 : reg n57 (25 : Fin 32) = sgl := by rw [u57.regs, upd_ne (by decide) (by decide), g56_25]
    have g57_26 : reg n57 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u57.regs, upd_ne (by decide) (by decide), g56_26]
    have g57_27 : reg n57 (27 : Fin 32) = tbl := by rw [u57.regs, upd_ne (by decide) (by decide), g56_27]
    have g57_10 : reg n57 a0 = 0 := by
      rw [u57.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g56_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w56_420]
    have keep_kk57 : SvKeepL B n0.mem n57.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m57]; exact keep_kk56
    clear keep_kk56
    have w57_2c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m57]; exact w56_2c
    have w57_30 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m57]; exact w56_30
    have w57_34 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m57]; exact w56_34
    have w57_38 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m57]; exact w56_38
    have w57_44 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m57]; exact w56_44
    have w57_48 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m57]; exact w56_48
    have w57_4c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m57]; exact w56_4c
    have w57_50 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m57]; exact w56_50
    have w57_54 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m57]; exact w56_54
    have w57_58 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m57]; exact w56_58
    have w57_5c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m57]; exact w56_5c
    have w57_60 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m57]; exact w56_60
    have w57_64 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m57]; exact w56_64
    have w57_68 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m57]; exact w56_68
    have w57_6c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m57]; exact w56_6c
    have w57_70 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m57]; exact w56_70
    have w57_74 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m57]; exact w56_74
    have w57_78 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m57]; exact w56_78
    have w57_7c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m57]; exact w56_7c
    have w57_80 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m57]; exact w56_80
    have w57_84 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m57]; exact w56_84
    have w57_88 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m57]; exact w56_88
    have w57_8c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m57]; exact w56_8c
    have w57_90 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m57]; exact w56_90
    have w57_94 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m57]; exact w56_94
    have w57_98 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m57]; exact w56_98
    have w57_9c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m57]; exact w56_9c
    have w57_a0 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m57]; exact w56_a0
    have w57_a4 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m57]; exact w56_a4
    have w57_150 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m57]; exact w56_150
    have w57_154 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m57]; exact w56_154
    have w57_158 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m57]; exact w56_158
    have w57_15c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m57]; exact w56_15c
    have w57_380 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m57]; exact w56_380
    have w57_384 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m57]; exact w56_384
    have w57_420 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m57]; exact w56_420
    have b57_424 : n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er56 := by rw [m57]; exact b56_424
    clear b56_424 w56_420 w56_384 w56_380 w56_15c w56_158 w56_154 w56_150 w56_a4 w56_a0 w56_9c w56_98 w56_94 w56_90 w56_8c w56_88 w56_84 w56_80 w56_7c w56_78 w56_74 w56_70 w56_6c w56_68 w56_64 w56_60 w56_5c w56_58 w56_54 w56_50 w56_4c w56_48 w56_44 w56_38 w56_34 w56_30 w56_2c ezhr56 zhr56
    -- 0x742: branch, taken
    obtain ⟨n58, d58, u58⟩ := s57.taken E57.self 0x7F2 sv_at_742
      (by decide) (by rw [g57_10, s57.zero]; rfl)
    have s58 : St n58.mem SV n58 0x7F2 (reg n58) := ⟨u58.pc, rfl, fun _ => rfl⟩
    have m58 : n58.mem = n57.mem := u58.mem
    have fr58 : ∀ x, SvR B x → n58.mem x = n57.mem x := fun x _ => by rw [m58]
    have t58 : Steps n0 n58 := t57.trans (.single d58)
    have fR58 : ∀ x, SvR B x → n58.mem x = M0 x := fun x hx => (fr58 x hx).trans (fR57 x hx)
    have E58 : SvCode n58.mem := E57.fr F fr58
    have V58 : SvSaves B n58.mem v := V57.same m58
    have g58_2 : reg n58 sp = B + 0x21A0 := by rw [u58.regs, g57_2]
    have g58_3 : reg n58 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u58.regs, g57_3]
    have g58_4 : reg n58 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u58.regs, g57_4]
    have g58_8 : reg n58 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u58.regs, g57_8]
    have g58_9 : reg n58 (9 : Fin 32) = tbp := by rw [u58.regs, g57_9]
    have g58_10 : reg n58 a0 = 0 := by rw [u58.regs, g57_10]
    have g58_18 : reg n58 (18 : Fin 32) = out := by rw [u58.regs, g57_18]
    have g58_19 : reg n58 (19 : Fin 32) = bp := by rw [u58.regs, g57_19]
    have g58_20 : reg n58 (20 : Fin 32) = dg := by rw [u58.regs, g57_20]
    have g58_21 : reg n58 (21 : Fin 32) = rootp := by rw [u58.regs, g57_21]
    have g58_22 : reg n58 (22 : Fin 32) = ll := by rw [u58.regs, g57_22]
    have g58_23 : reg n58 (23 : Fin 32) = sgp := by rw [u58.regs, g57_23]
    have g58_24 : reg n58 (24 : Fin 32) = kp := by rw [u58.regs, g57_24]
    have g58_25 : reg n58 (25 : Fin 32) = sgl := by rw [u58.regs, g57_25]
    have g58_26 : reg n58 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u58.regs, g57_26]
    have g58_27 : reg n58 (27 : Fin 32) = tbl := by rw [u58.regs, g57_27]
    have keep_kk58 : SvKeepL B n0.mem n58.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m58]; exact keep_kk57
    clear keep_kk57
    have w58_2c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m58]; exact w57_2c
    have w58_30 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m58]; exact w57_30
    have w58_34 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m58]; exact w57_34
    have w58_38 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m58]; exact w57_38
    have w58_44 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m58]; exact w57_44
    have w58_48 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m58]; exact w57_48
    have w58_4c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m58]; exact w57_4c
    have w58_50 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m58]; exact w57_50
    have w58_54 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m58]; exact w57_54
    have w58_58 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m58]; exact w57_58
    have w58_5c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m58]; exact w57_5c
    have w58_60 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m58]; exact w57_60
    have w58_64 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m58]; exact w57_64
    have w58_68 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m58]; exact w57_68
    have w58_6c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m58]; exact w57_6c
    have w58_70 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m58]; exact w57_70
    have w58_74 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m58]; exact w57_74
    have w58_78 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m58]; exact w57_78
    have w58_7c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m58]; exact w57_7c
    have w58_80 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m58]; exact w57_80
    have w58_84 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m58]; exact w57_84
    have w58_88 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m58]; exact w57_88
    have w58_8c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m58]; exact w57_8c
    have w58_90 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m58]; exact w57_90
    have w58_94 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m58]; exact w57_94
    have w58_98 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m58]; exact w57_98
    have w58_9c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m58]; exact w57_9c
    have w58_a0 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m58]; exact w57_a0
    have w58_a4 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m58]; exact w57_a4
    have w58_150 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m58]; exact w57_150
    have w58_154 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m58]; exact w57_154
    have w58_158 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m58]; exact w57_158
    have w58_15c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m58]; exact w57_15c
    have w58_380 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m58]; exact w57_380
    have w58_384 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m58]; exact w57_384
    have w58_420 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m58]; exact w57_420
    have b58_424 : n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er56 := by rw [m58]; exact b57_424
    clear b57_424 w57_420 w57_384 w57_380 w57_15c w57_158 w57_154 w57_150 w57_a4 w57_a0 w57_9c w57_98 w57_94 w57_90 w57_8c w57_88 w57_84 w57_80 w57_7c w57_78 w57_74 w57_70 w57_6c w57_68 w57_64 w57_60 w57_5c w57_58 w57_54 w57_50 w57_4c w57_48 w57_44 w57_38 w57_34 w57_30 w57_2c g57_10 g57_27 g57_26 g57_25 g57_24 g57_23 g57_22 g57_21 g57_20 g57_19 g57_18 g57_9 g57_8 g57_4 g57_3 g57_2 V57 E57 fR57 t57 fr57 m57 s57 u57 d57
    -- 0x7F2: lbu
    obtain ⟨n59, d59, u59⟩ := s58.lbu E58.self sv_at_7f2 (off' := 0x7F6) (by decide)
    have s59 : St n59.mem SV n59 0x7F6 (reg n59) := ⟨u59.pc, rfl, fun _ => rfl⟩
    have m59 : n59.mem = n58.mem := u59.mem
    have fr59 : ∀ x, SvR B x → n59.mem x = n58.mem x := fun x _ => by rw [m59]
    have t59 : Steps n0 n59 := t58.trans (.single d59)
    have fR59 : ∀ x, SvR B x → n59.mem x = M0 x := fun x hx => (fr59 x hx).trans (fR58 x hx)
    have E59 : SvCode n59.mem := E58.fr F fr59
    have V59 : SvSaves B n59.mem v := V58.same m59
    have g59_2 : reg n59 sp = B + 0x21A0 := by rw [u59.regs, upd_ne (by decide) (by decide), g58_2]
    have g59_3 : reg n59 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u59.regs, upd_ne (by decide) (by decide), g58_3]
    have g59_4 : reg n59 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u59.regs, upd_ne (by decide) (by decide), g58_4]
    have g59_8 : reg n59 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u59.regs, upd_ne (by decide) (by decide), g58_8]
    have g59_9 : reg n59 (9 : Fin 32) = tbp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_9]
    have g59_18 : reg n59 (18 : Fin 32) = out := by rw [u59.regs, upd_ne (by decide) (by decide), g58_18]
    have g59_19 : reg n59 (19 : Fin 32) = bp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_19]
    have g59_20 : reg n59 (20 : Fin 32) = dg := by rw [u59.regs, upd_ne (by decide) (by decide), g58_20]
    have g59_21 : reg n59 (21 : Fin 32) = rootp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_21]
    have g59_22 : reg n59 (22 : Fin 32) = ll := by rw [u59.regs, upd_ne (by decide) (by decide), g58_22]
    have g59_23 : reg n59 (23 : Fin 32) = sgp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_23]
    have g59_24 : reg n59 (24 : Fin 32) = kp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_24]
    have g59_25 : reg n59 (25 : Fin 32) = sgl := by rw [u59.regs, upd_ne (by decide) (by decide), g58_25]
    have g59_26 : reg n59 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u59.regs, upd_ne (by decide) (by decide), g58_26]
    have g59_27 : reg n59 (27 : Fin 32) = tbl := by rw [u59.regs, upd_ne (by decide) (by decide), g58_27]
    have g59_10 : reg n59 a0 = (derErrByte er56).zeroExtend 32 := by
      rw [u59.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g58_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b58_424]
    have keep_kk59 : SvKeepL B n0.mem n59.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m59]; exact keep_kk58
    clear keep_kk58
    have w59_2c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m59]; exact w58_2c
    have w59_30 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m59]; exact w58_30
    have w59_34 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m59]; exact w58_34
    have w59_38 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m59]; exact w58_38
    have w59_44 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m59]; exact w58_44
    have w59_48 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m59]; exact w58_48
    have w59_4c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m59]; exact w58_4c
    have w59_50 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m59]; exact w58_50
    have w59_54 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m59]; exact w58_54
    have w59_58 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m59]; exact w58_58
    have w59_5c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m59]; exact w58_5c
    have w59_60 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m59]; exact w58_60
    have w59_64 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m59]; exact w58_64
    have w59_68 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m59]; exact w58_68
    have w59_6c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m59]; exact w58_6c
    have w59_70 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m59]; exact w58_70
    have w59_74 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m59]; exact w58_74
    have w59_78 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m59]; exact w58_78
    have w59_7c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m59]; exact w58_7c
    have w59_80 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m59]; exact w58_80
    have w59_84 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m59]; exact w58_84
    have w59_88 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m59]; exact w58_88
    have w59_8c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m59]; exact w58_8c
    have w59_90 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m59]; exact w58_90
    have w59_94 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m59]; exact w58_94
    have w59_98 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m59]; exact w58_98
    have w59_9c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m59]; exact w58_9c
    have w59_a0 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m59]; exact w58_a0
    have w59_a4 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m59]; exact w58_a4
    have w59_150 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m59]; exact w58_150
    have w59_154 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m59]; exact w58_154
    have w59_158 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m59]; exact w58_158
    have w59_15c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m59]; exact w58_15c
    have w59_380 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m59]; exact w58_380
    have w59_384 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m59]; exact w58_384
    have w59_420 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m59]; exact w58_420
    have b59_424 : n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er56 := by rw [m59]; exact b58_424
    clear b58_424 w58_420 w58_384 w58_380 w58_15c w58_158 w58_154 w58_150 w58_a4 w58_a0 w58_9c w58_98 w58_94 w58_90 w58_8c w58_88 w58_84 w58_80 w58_7c w58_78 w58_74 w58_70 w58_6c w58_68 w58_64 w58_60 w58_5c w58_58 w58_54 w58_50 w58_4c w58_48 w58_44 w58_38 w58_34 w58_30 w58_2c g58_27 g58_26 g58_25 g58_24 g58_23 g58_22 g58_21 g58_20 g58_19 g58_18 g58_10 g58_9 g58_8 g58_4 g58_3 g58_2 V58 E58 fR58 t58 fr58 m58 s58 u58 d58
    -- 0x7F6: j
    obtain ⟨n60, d60, u60⟩ := s59.jump E59.self sv_at_7f6 (off' := 0x942) (by decide)
      (by rw [s59.pc]; decide)
    have s60 : St n60.mem SV n60 0x942 (reg n60) := ⟨u60.pc, rfl, fun _ => rfl⟩
    have m60 : n60.mem = n59.mem := u60.mem
    have fr60 : ∀ x, SvR B x → n60.mem x = n59.mem x := fun x _ => by rw [m60]
    have t60 : Steps n0 n60 := t59.trans (.single d60)
    have fR60 : ∀ x, SvR B x → n60.mem x = M0 x := fun x hx => (fr60 x hx).trans (fR59 x hx)
    have E60 : SvCode n60.mem := E59.fr F fr60
    have V60 : SvSaves B n60.mem v := V59.same m60
    have g60_2 : reg n60 sp = B + 0x21A0 := by rw [u60.regs, g59_2]
    have g60_3 : reg n60 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u60.regs, g59_3]
    have g60_4 : reg n60 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u60.regs, g59_4]
    have g60_8 : reg n60 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u60.regs, g59_8]
    have g60_9 : reg n60 (9 : Fin 32) = tbp := by rw [u60.regs, g59_9]
    have g60_10 : reg n60 a0 = (derErrByte er56).zeroExtend 32 := by rw [u60.regs, g59_10]
    have g60_18 : reg n60 (18 : Fin 32) = out := by rw [u60.regs, g59_18]
    have g60_19 : reg n60 (19 : Fin 32) = bp := by rw [u60.regs, g59_19]
    have g60_20 : reg n60 (20 : Fin 32) = dg := by rw [u60.regs, g59_20]
    have g60_21 : reg n60 (21 : Fin 32) = rootp := by rw [u60.regs, g59_21]
    have g60_22 : reg n60 (22 : Fin 32) = ll := by rw [u60.regs, g59_22]
    have g60_23 : reg n60 (23 : Fin 32) = sgp := by rw [u60.regs, g59_23]
    have g60_24 : reg n60 (24 : Fin 32) = kp := by rw [u60.regs, g59_24]
    have g60_25 : reg n60 (25 : Fin 32) = sgl := by rw [u60.regs, g59_25]
    have g60_26 : reg n60 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u60.regs, g59_26]
    have g60_27 : reg n60 (27 : Fin 32) = tbl := by rw [u60.regs, g59_27]
    have keep_kk60 : SvKeepL B n0.mem n60.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m60]; exact keep_kk59
    clear keep_kk59
    have w60_2c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m60]; exact w59_2c
    have w60_30 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m60]; exact w59_30
    have w60_34 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m60]; exact w59_34
    have w60_38 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m60]; exact w59_38
    have w60_44 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m60]; exact w59_44
    have w60_48 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m60]; exact w59_48
    have w60_4c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m60]; exact w59_4c
    have w60_50 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m60]; exact w59_50
    have w60_54 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m60]; exact w59_54
    have w60_58 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m60]; exact w59_58
    have w60_5c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m60]; exact w59_5c
    have w60_60 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m60]; exact w59_60
    have w60_64 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m60]; exact w59_64
    have w60_68 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m60]; exact w59_68
    have w60_6c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m60]; exact w59_6c
    have w60_70 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m60]; exact w59_70
    have w60_74 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m60]; exact w59_74
    have w60_78 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m60]; exact w59_78
    have w60_7c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m60]; exact w59_7c
    have w60_80 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m60]; exact w59_80
    have w60_84 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m60]; exact w59_84
    have w60_88 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m60]; exact w59_88
    have w60_8c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m60]; exact w59_8c
    have w60_90 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m60]; exact w59_90
    have w60_94 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m60]; exact w59_94
    have w60_98 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m60]; exact w59_98
    have w60_9c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m60]; exact w59_9c
    have w60_a0 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m60]; exact w59_a0
    have w60_a4 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m60]; exact w59_a4
    have w60_150 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m60]; exact w59_150
    have w60_154 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m60]; exact w59_154
    have w60_158 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m60]; exact w59_158
    have w60_15c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m60]; exact w59_15c
    have w60_380 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m60]; exact w59_380
    have w60_384 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m60]; exact w59_384
    have w60_420 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m60]; exact w59_420
    have b60_424 : n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er56 := by rw [m60]; exact b59_424
    clear b59_424 w59_420 w59_384 w59_380 w59_15c w59_158 w59_154 w59_150 w59_a4 w59_a0 w59_9c w59_98 w59_94 w59_90 w59_8c w59_88 w59_84 w59_80 w59_7c w59_78 w59_74 w59_70 w59_6c w59_68 w59_64 w59_60 w59_5c w59_58 w59_54 w59_50 w59_4c w59_48 w59_44 w59_38 w59_34 w59_30 w59_2c g59_10 g59_27 g59_26 g59_25 g59_24 g59_23 g59_22 g59_21 g59_20 g59_19 g59_18 g59_9 g59_8 g59_4 g59_3 g59_2 V59 E59 fR59 t59 fr59 m59 s59 u59 d59
    -- 0x942: sw
    obtain ⟨n61, d61, s61, fr61, K61, W61, rg61⟩ := sv_sw F E60 s60 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g60_2]; sv_addr) (by decide) (by decide)
    have t61 : Steps n0 n61 := t60.trans d61
    have fR61 : ∀ x, SvR B x → n61.mem x = M0 x := fun x hx => (fr61 x hx).trans (fR60 x hx)
    have E61 : SvCode n61.mem := E60.fr F fr61
    have V61 : SvSaves B n61.mem v := V60.keep K61 (by decide)
    have g61_2 : reg n61 sp = B + 0x21A0 := by rw [rg61 sp, g60_2]
    have g61_3 : reg n61 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg61 (3 : Fin 32), g60_3]
    have g61_4 : reg n61 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg61 (4 : Fin 32), g60_4]
    have g61_8 : reg n61 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg61 (8 : Fin 32), g60_8]
    have g61_9 : reg n61 (9 : Fin 32) = tbp := by rw [rg61 (9 : Fin 32), g60_9]
    have g61_10 : reg n61 a0 = (derErrByte er56).zeroExtend 32 := by rw [rg61 a0, g60_10]
    have g61_18 : reg n61 (18 : Fin 32) = out := by rw [rg61 (18 : Fin 32), g60_18]
    have g61_19 : reg n61 (19 : Fin 32) = bp := by rw [rg61 (19 : Fin 32), g60_19]
    have g61_20 : reg n61 (20 : Fin 32) = dg := by rw [rg61 (20 : Fin 32), g60_20]
    have g61_21 : reg n61 (21 : Fin 32) = rootp := by rw [rg61 (21 : Fin 32), g60_21]
    have g61_22 : reg n61 (22 : Fin 32) = ll := by rw [rg61 (22 : Fin 32), g60_22]
    have g61_23 : reg n61 (23 : Fin 32) = sgp := by rw [rg61 (23 : Fin 32), g60_23]
    have g61_24 : reg n61 (24 : Fin 32) = kp := by rw [rg61 (24 : Fin 32), g60_24]
    have g61_25 : reg n61 (25 : Fin 32) = sgl := by rw [rg61 (25 : Fin 32), g60_25]
    have g61_26 : reg n61 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rg61 (26 : Fin 32), g60_26]
    have g61_27 : reg n61 (27 : Fin 32) = tbl := by rw [rg61 (27 : Fin 32), g60_27]
    have keep_kk61 : SvKeepL B n0.mem n61.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := keep_kk60.trans K61.toL
    clear keep_kk60
    have w61_2c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K61.w32 (by decide) (by decide)).trans w60_2c
    have w61_30 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K61.w32 (by decide) (by decide)).trans w60_30
    have w61_34 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K61.w32 (by decide) (by decide)).trans w60_34
    have w61_38 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K61.w32 (by decide) (by decide)).trans w60_38
    have w61_48 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K61.w32 (by decide) (by decide)).trans w60_48
    have w61_4c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K61.w32 (by decide) (by decide)).trans w60_4c
    have w61_50 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K61.w32 (by decide) (by decide)).trans w60_50
    have w61_54 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K61.w32 (by decide) (by decide)).trans w60_54
    have w61_58 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K61.w32 (by decide) (by decide)).trans w60_58
    have w61_5c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K61.w32 (by decide) (by decide)).trans w60_5c
    have w61_60 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K61.w32 (by decide) (by decide)).trans w60_60
    have w61_64 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K61.w32 (by decide) (by decide)).trans w60_64
    have w61_68 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K61.w32 (by decide) (by decide)).trans w60_68
    have w61_6c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K61.w32 (by decide) (by decide)).trans w60_6c
    have w61_70 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K61.w32 (by decide) (by decide)).trans w60_70
    have w61_74 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K61.w32 (by decide) (by decide)).trans w60_74
    have w61_78 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K61.w32 (by decide) (by decide)).trans w60_78
    have w61_7c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K61.w32 (by decide) (by decide)).trans w60_7c
    have w61_80 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K61.w32 (by decide) (by decide)).trans w60_80
    have w61_84 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K61.w32 (by decide) (by decide)).trans w60_84
    have w61_88 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K61.w32 (by decide) (by decide)).trans w60_88
    have w61_8c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K61.w32 (by decide) (by decide)).trans w60_8c
    have w61_90 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K61.w32 (by decide) (by decide)).trans w60_90
    have w61_94 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K61.w32 (by decide) (by decide)).trans w60_94
    have w61_98 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K61.w32 (by decide) (by decide)).trans w60_98
    have w61_9c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K61.w32 (by decide) (by decide)).trans w60_9c
    have w61_a0 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K61.w32 (by decide) (by decide)).trans w60_a0
    have w61_a4 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K61.w32 (by decide) (by decide)).trans w60_a4
    have w61_150 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K61.w32 (by decide) (by decide)).trans w60_150
    have w61_154 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K61.w32 (by decide) (by decide)).trans w60_154
    have w61_158 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K61.w32 (by decide) (by decide)).trans w60_158
    have w61_15c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K61.w32 (by decide) (by decide)).trans w60_15c
    have w61_380 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K61.w32 (by decide) (by decide)).trans w60_380
    have w61_384 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K61.w32 (by decide) (by decide)).trans w60_384
    have w61_420 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K61.w32 (by decide) (by decide)).trans w60_420
    have b61_424 : n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er56 := (K61.b8 (by decide) (by decide)).trans b60_424
    have w61_44 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er56).zeroExtend 32 := by rw [W61, g60_10]
    clear b60_424 w60_420 w60_384 w60_380 w60_15c w60_158 w60_154 w60_150 w60_a4 w60_a0 w60_9c w60_98 w60_94 w60_90 w60_8c w60_88 w60_84 w60_80 w60_7c w60_78 w60_74 w60_70 w60_6c w60_68 w60_64 w60_60 w60_5c w60_58 w60_54 w60_50 w60_4c w60_48 w60_44 w60_38 w60_34 w60_30 w60_2c g60_27 g60_26 g60_25 g60_24 g60_23 g60_22 g60_21 g60_20 g60_19 g60_18 g60_10 g60_9 g60_8 g60_4 g60_3 g60_2 V60 E60 fR60 t60 fr60 m60 s60 u60 d60
    -- 0x944: lw
    obtain ⟨n62, d62, u62⟩ := s61.lw E61.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g61_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s62 : St n62.mem SV n62 0x946 (reg n62) := ⟨u62.pc, rfl, fun _ => rfl⟩
    have m62 : n62.mem = n61.mem := u62.mem
    have fr62 : ∀ x, SvR B x → n62.mem x = n61.mem x := fun x _ => by rw [m62]
    have t62 : Steps n0 n62 := t61.trans (.single d62)
    have fR62 : ∀ x, SvR B x → n62.mem x = M0 x := fun x hx => (fr62 x hx).trans (fR61 x hx)
    have E62 : SvCode n62.mem := E61.fr F fr62
    have V62 : SvSaves B n62.mem v := V61.same m62
    have g62_2 : reg n62 sp = B + 0x21A0 := by rw [u62.regs, upd_ne (by decide) (by decide), g61_2]
    have g62_3 : reg n62 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u62.regs, upd_ne (by decide) (by decide), g61_3]
    have g62_4 : reg n62 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u62.regs, upd_ne (by decide) (by decide), g61_4]
    have g62_9 : reg n62 (9 : Fin 32) = tbp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_9]
    have g62_10 : reg n62 a0 = (derErrByte er56).zeroExtend 32 := by rw [u62.regs, upd_ne (by decide) (by decide), g61_10]
    have g62_18 : reg n62 (18 : Fin 32) = out := by rw [u62.regs, upd_ne (by decide) (by decide), g61_18]
    have g62_19 : reg n62 (19 : Fin 32) = bp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_19]
    have g62_20 : reg n62 (20 : Fin 32) = dg := by rw [u62.regs, upd_ne (by decide) (by decide), g61_20]
    have g62_21 : reg n62 (21 : Fin 32) = rootp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_21]
    have g62_22 : reg n62 (22 : Fin 32) = ll := by rw [u62.regs, upd_ne (by decide) (by decide), g61_22]
    have g62_23 : reg n62 (23 : Fin 32) = sgp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_23]
    have g62_24 : reg n62 (24 : Fin 32) = kp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_24]
    have g62_25 : reg n62 (25 : Fin 32) = sgl := by rw [u62.regs, upd_ne (by decide) (by decide), g61_25]
    have g62_26 : reg n62 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u62.regs, upd_ne (by decide) (by decide), g61_26]
    have g62_27 : reg n62 (27 : Fin 32) = tbl := by rw [u62.regs, upd_ne (by decide) (by decide), g61_27]
    have g62_8 : reg n62 (8 : Fin 32) = (derErrByte er56).zeroExtend 32 := by
      rw [u62.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g61_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w61_44]
    have keep_kk62 : SvKeepL B n0.mem n62.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m62]; exact keep_kk61
    clear keep_kk61
    have w62_2c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m62]; exact w61_2c
    have w62_30 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m62]; exact w61_30
    have w62_34 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m62]; exact w61_34
    have w62_38 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m62]; exact w61_38
    have w62_44 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er56).zeroExtend 32 := by rw [m62]; exact w61_44
    have w62_48 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m62]; exact w61_48
    have w62_4c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m62]; exact w61_4c
    have w62_50 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m62]; exact w61_50
    have w62_54 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m62]; exact w61_54
    have w62_58 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m62]; exact w61_58
    have w62_5c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m62]; exact w61_5c
    have w62_60 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m62]; exact w61_60
    have w62_64 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m62]; exact w61_64
    have w62_68 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m62]; exact w61_68
    have w62_6c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m62]; exact w61_6c
    have w62_70 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m62]; exact w61_70
    have w62_74 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m62]; exact w61_74
    have w62_78 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m62]; exact w61_78
    have w62_7c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m62]; exact w61_7c
    have w62_80 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m62]; exact w61_80
    have w62_84 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m62]; exact w61_84
    have w62_88 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m62]; exact w61_88
    have w62_8c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m62]; exact w61_8c
    have w62_90 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m62]; exact w61_90
    have w62_94 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m62]; exact w61_94
    have w62_98 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m62]; exact w61_98
    have w62_9c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m62]; exact w61_9c
    have w62_a0 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m62]; exact w61_a0
    have w62_a4 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m62]; exact w61_a4
    have w62_150 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m62]; exact w61_150
    have w62_154 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m62]; exact w61_154
    have w62_158 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m62]; exact w61_158
    have w62_15c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m62]; exact w61_15c
    have w62_380 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m62]; exact w61_380
    have w62_384 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m62]; exact w61_384
    have w62_420 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m62]; exact w61_420
    have b62_424 : n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er56 := by rw [m62]; exact b61_424
    clear w61_44 b61_424 w61_420 w61_384 w61_380 w61_15c w61_158 w61_154 w61_150 w61_a4 w61_a0 w61_9c w61_98 w61_94 w61_90 w61_8c w61_88 w61_84 w61_80 w61_7c w61_78 w61_74 w61_70 w61_6c w61_68 w61_64 w61_60 w61_5c w61_58 w61_54 w61_50 w61_4c w61_48 w61_38 w61_34 w61_30 w61_2c g61_27 g61_26 g61_25 g61_24 g61_23 g61_22 g61_21 g61_20 g61_19 g61_18 g61_10 g61_9 g61_8 g61_4 g61_3 g61_2 V61 E61 fR61 t61 rg61 W61 K61 fr61 s61 d61
    -- 0x946: j
    obtain ⟨n63, d63, u63⟩ := s62.jump E62.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s62.pc]; decide)
    have s63 : St n63.mem SV n63 0x7A4 (reg n63) := ⟨u63.pc, rfl, fun _ => rfl⟩
    have m63 : n63.mem = n62.mem := u63.mem
    have fr63 : ∀ x, SvR B x → n63.mem x = n62.mem x := fun x _ => by rw [m63]
    have t63 : Steps n0 n63 := t62.trans (.single d63)
    have fR63 : ∀ x, SvR B x → n63.mem x = M0 x := fun x hx => (fr63 x hx).trans (fR62 x hx)
    have E63 : SvCode n63.mem := E62.fr F fr63
    have V63 : SvSaves B n63.mem v := V62.same m63
    have g63_2 : reg n63 sp = B + 0x21A0 := by rw [u63.regs, g62_2]
    have g63_3 : reg n63 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u63.regs, g62_3]
    have g63_4 : reg n63 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u63.regs, g62_4]
    have g63_8 : reg n63 (8 : Fin 32) = (derErrByte er56).zeroExtend 32 := by rw [u63.regs, g62_8]
    have g63_9 : reg n63 (9 : Fin 32) = tbp := by rw [u63.regs, g62_9]
    have g63_10 : reg n63 a0 = (derErrByte er56).zeroExtend 32 := by rw [u63.regs, g62_10]
    have g63_18 : reg n63 (18 : Fin 32) = out := by rw [u63.regs, g62_18]
    have g63_19 : reg n63 (19 : Fin 32) = bp := by rw [u63.regs, g62_19]
    have g63_20 : reg n63 (20 : Fin 32) = dg := by rw [u63.regs, g62_20]
    have g63_21 : reg n63 (21 : Fin 32) = rootp := by rw [u63.regs, g62_21]
    have g63_22 : reg n63 (22 : Fin 32) = ll := by rw [u63.regs, g62_22]
    have g63_23 : reg n63 (23 : Fin 32) = sgp := by rw [u63.regs, g62_23]
    have g63_24 : reg n63 (24 : Fin 32) = kp := by rw [u63.regs, g62_24]
    have g63_25 : reg n63 (25 : Fin 32) = sgl := by rw [u63.regs, g62_25]
    have g63_26 : reg n63 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u63.regs, g62_26]
    have g63_27 : reg n63 (27 : Fin 32) = tbl := by rw [u63.regs, g62_27]
    have keep_kk63 : SvKeepL B n0.mem n63.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m63]; exact keep_kk62
    clear keep_kk62
    have w63_2c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m63]; exact w62_2c
    have w63_30 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m63]; exact w62_30
    have w63_34 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m63]; exact w62_34
    have w63_38 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m63]; exact w62_38
    have w63_44 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er56).zeroExtend 32 := by rw [m63]; exact w62_44
    have w63_48 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m63]; exact w62_48
    have w63_4c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m63]; exact w62_4c
    have w63_50 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m63]; exact w62_50
    have w63_54 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m63]; exact w62_54
    have w63_58 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m63]; exact w62_58
    have w63_5c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m63]; exact w62_5c
    have w63_60 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m63]; exact w62_60
    have w63_64 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m63]; exact w62_64
    have w63_68 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m63]; exact w62_68
    have w63_6c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m63]; exact w62_6c
    have w63_70 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m63]; exact w62_70
    have w63_74 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m63]; exact w62_74
    have w63_78 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m63]; exact w62_78
    have w63_7c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m63]; exact w62_7c
    have w63_80 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m63]; exact w62_80
    have w63_84 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m63]; exact w62_84
    have w63_88 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m63]; exact w62_88
    have w63_8c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m63]; exact w62_8c
    have w63_90 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m63]; exact w62_90
    have w63_94 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m63]; exact w62_94
    have w63_98 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m63]; exact w62_98
    have w63_9c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m63]; exact w62_9c
    have w63_a0 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m63]; exact w62_a0
    have w63_a4 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m63]; exact w62_a4
    have w63_150 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m63]; exact w62_150
    have w63_154 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m63]; exact w62_154
    have w63_158 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m63]; exact w62_158
    have w63_15c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m63]; exact w62_15c
    have w63_380 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m63]; exact w62_380
    have w63_384 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m63]; exact w62_384
    have w63_420 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m63]; exact w62_420
    have b63_424 : n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er56 := by rw [m63]; exact b62_424
    clear b62_424 w62_420 w62_384 w62_380 w62_15c w62_158 w62_154 w62_150 w62_a4 w62_a0 w62_9c w62_98 w62_94 w62_90 w62_8c w62_88 w62_84 w62_80 w62_7c w62_78 w62_74 w62_70 w62_6c w62_68 w62_64 w62_60 w62_5c w62_58 w62_54 w62_50 w62_4c w62_48 w62_44 w62_38 w62_34 w62_30 w62_2c g62_8 g62_27 g62_26 g62_25 g62_24 g62_23 g62_22 g62_21 g62_20 g62_19 g62_18 g62_10 g62_9 g62_4 g62_3 g62_2 V62 E62 fR62 t62 fr62 m62 s62 u62 d62
    exact .inl ⟨(fun ⟨tl56', h0', _⟩ => by rw [hr56] at h0'; cases h0'), sv_fail F E63 s63 t63 (fun x hx => (fR63 x hx).trans (fM x hx).symm) V63 hret g63_2 g63_18 hO g63_3 g63_4 (by rw [g63_8]; sv_code)⟩
  obtain ⟨o0_56, o4_56, o8_56, o12_56, o16_56, d8_56, d12_56⟩ := Ok56 tl56 hr56
  have keep_kk56 : SvKeepL B n0.mem n56.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := keep_kk55.trans K56
  clear keep_kk55
  have w56_2c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K56.w32 (by decide) (by decide)).trans w55_2c
  have w56_30 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K56.w32 (by decide) (by decide)).trans w55_30
  have w56_34 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K56.w32 (by decide) (by decide)).trans w55_34
  have w56_38 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K56.w32 (by decide) (by decide)).trans w55_38
  have w56_44 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K56.w32 (by decide) (by decide)).trans w55_44
  have w56_48 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K56.w32 (by decide) (by decide)).trans w55_48
  have w56_4c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K56.w32 (by decide) (by decide)).trans w55_4c
  have w56_50 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K56.w32 (by decide) (by decide)).trans w55_50
  have w56_54 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K56.w32 (by decide) (by decide)).trans w55_54
  have w56_58 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K56.w32 (by decide) (by decide)).trans w55_58
  have w56_5c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K56.w32 (by decide) (by decide)).trans w55_5c
  have w56_60 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K56.w32 (by decide) (by decide)).trans w55_60
  have w56_64 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K56.w32 (by decide) (by decide)).trans w55_64
  have w56_68 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K56.w32 (by decide) (by decide)).trans w55_68
  have w56_6c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K56.w32 (by decide) (by decide)).trans w55_6c
  have w56_70 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K56.w32 (by decide) (by decide)).trans w55_70
  have w56_74 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K56.w32 (by decide) (by decide)).trans w55_74
  have w56_78 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K56.w32 (by decide) (by decide)).trans w55_78
  have w56_7c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K56.w32 (by decide) (by decide)).trans w55_7c
  have w56_80 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K56.w32 (by decide) (by decide)).trans w55_80
  have w56_84 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K56.w32 (by decide) (by decide)).trans w55_84
  have w56_88 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K56.w32 (by decide) (by decide)).trans w55_88
  have w56_8c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K56.w32 (by decide) (by decide)).trans w55_8c
  have w56_90 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K56.w32 (by decide) (by decide)).trans w55_90
  have w56_94 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K56.w32 (by decide) (by decide)).trans w55_94
  have w56_98 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K56.w32 (by decide) (by decide)).trans w55_98
  have w56_9c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K56.w32 (by decide) (by decide)).trans w55_9c
  have w56_a0 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K56.w32 (by decide) (by decide)).trans w55_a0
  have w56_a4 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K56.w32 (by decide) (by decide)).trans w55_a4
  have w56_150 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K56.w32 (by decide) (by decide)).trans w55_150
  have w56_154 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K56.w32 (by decide) (by decide)).trans w55_154
  have w56_158 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K56.w32 (by decide) (by decide)).trans w55_158
  have w56_15c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K56.w32 (by decide) (by decide)).trans w55_15c
  have w56_380 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K56.w32 (by decide) (by decide)).trans w55_380
  have w56_384 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K56.w32 (by decide) (by decide)).trans w55_384
  have w56_388 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := d8_56
  have w56_38c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := d12_56
  have w56_420 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := o0_56
  have w56_424 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := o4_56
  have w56_428 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := o8_56
  have w56_42c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := o12_56
  have b56_430 : n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := o16_56
  clear w55_38c w55_388 w55_384 w55_380 w55_15c w55_158 w55_154 w55_150 w55_a4 w55_a0 w55_9c w55_98 w55_94 w55_90 w55_8c w55_88 w55_84 w55_80 w55_7c w55_78 w55_74 w55_70 w55_6c w55_68 w55_64 w55_60 w55_5c w55_58 w55_54 w55_50 w55_4c w55_48 w55_44 w55_38 w55_34 w55_30 w55_2c g55_11 g55_10 g55_27 g55_26 g55_25 g55_24 g55_23 g55_22 g55_21 g55_20 g55_19 g55_18 g55_12 g55_9 g55_8 g55_4 g55_3 g55_2 V55 E55 fR55 t55 fr55 rb55 s55 m55 u55 c55
  -- 0x73E: lw
  obtain ⟨n57, d57, u57⟩ := s56.lw E56.self sv_at_73e (off' := 0x742) (by decide)
    (by rw [g56_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s57 : St n57.mem SV n57 0x742 (reg n57) := ⟨u57.pc, rfl, fun _ => rfl⟩
  have m57 : n57.mem = n56.mem := u57.mem
  have fr57 : ∀ x, SvR B x → n57.mem x = n56.mem x := fun x _ => by rw [m57]
  have t57 : Steps n0 n57 := t56.trans (.single d57)
  have fR57 : ∀ x, SvR B x → n57.mem x = M0 x := fun x hx => (fr57 x hx).trans (fR56 x hx)
  have E57 : SvCode n57.mem := E56.fr F fr57
  have V57 : SvSaves B n57.mem v := V56.same m57
  have g57_2 : reg n57 sp = B + 0x21A0 := by rw [u57.regs, upd_ne (by decide) (by decide), g56_2]
  have g57_3 : reg n57 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u57.regs, upd_ne (by decide) (by decide), g56_3]
  have g57_4 : reg n57 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u57.regs, upd_ne (by decide) (by decide), g56_4]
  have g57_8 : reg n57 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u57.regs, upd_ne (by decide) (by decide), g56_8]
  have g57_9 : reg n57 (9 : Fin 32) = tbp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_9]
  have g57_18 : reg n57 (18 : Fin 32) = out := by rw [u57.regs, upd_ne (by decide) (by decide), g56_18]
  have g57_19 : reg n57 (19 : Fin 32) = bp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_19]
  have g57_20 : reg n57 (20 : Fin 32) = dg := by rw [u57.regs, upd_ne (by decide) (by decide), g56_20]
  have g57_21 : reg n57 (21 : Fin 32) = rootp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_21]
  have g57_22 : reg n57 (22 : Fin 32) = ll := by rw [u57.regs, upd_ne (by decide) (by decide), g56_22]
  have g57_23 : reg n57 (23 : Fin 32) = sgp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_23]
  have g57_24 : reg n57 (24 : Fin 32) = kp := by rw [u57.regs, upd_ne (by decide) (by decide), g56_24]
  have g57_25 : reg n57 (25 : Fin 32) = sgl := by rw [u57.regs, upd_ne (by decide) (by decide), g56_25]
  have g57_26 : reg n57 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u57.regs, upd_ne (by decide) (by decide), g56_26]
  have g57_27 : reg n57 (27 : Fin 32) = tbl := by rw [u57.regs, upd_ne (by decide) (by decide), g56_27]
  have g57_10 : reg n57 a0 = (vp) + BitVec.ofNat 32 tl56.header := by
    rw [u57.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g56_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w56_420]
  have keep_kk57 : SvKeepL B n0.mem n57.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m57]; exact keep_kk56
  clear keep_kk56
  have w57_2c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m57]; exact w56_2c
  have w57_30 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m57]; exact w56_30
  have w57_34 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m57]; exact w56_34
  have w57_38 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m57]; exact w56_38
  have w57_44 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m57]; exact w56_44
  have w57_48 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m57]; exact w56_48
  have w57_4c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m57]; exact w56_4c
  have w57_50 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m57]; exact w56_50
  have w57_54 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m57]; exact w56_54
  have w57_58 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m57]; exact w56_58
  have w57_5c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m57]; exact w56_5c
  have w57_60 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m57]; exact w56_60
  have w57_64 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m57]; exact w56_64
  have w57_68 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m57]; exact w56_68
  have w57_6c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m57]; exact w56_6c
  have w57_70 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m57]; exact w56_70
  have w57_74 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m57]; exact w56_74
  have w57_78 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m57]; exact w56_78
  have w57_7c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m57]; exact w56_7c
  have w57_80 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m57]; exact w56_80
  have w57_84 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m57]; exact w56_84
  have w57_88 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m57]; exact w56_88
  have w57_8c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m57]; exact w56_8c
  have w57_90 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m57]; exact w56_90
  have w57_94 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m57]; exact w56_94
  have w57_98 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m57]; exact w56_98
  have w57_9c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m57]; exact w56_9c
  have w57_a0 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m57]; exact w56_a0
  have w57_a4 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m57]; exact w56_a4
  have w57_150 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m57]; exact w56_150
  have w57_154 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m57]; exact w56_154
  have w57_158 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m57]; exact w56_158
  have w57_15c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m57]; exact w56_15c
  have w57_380 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m57]; exact w56_380
  have w57_384 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m57]; exact w56_384
  have w57_388 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m57]; exact w56_388
  have w57_38c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m57]; exact w56_38c
  have w57_420 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m57]; exact w56_420
  have w57_424 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m57]; exact w56_424
  have w57_428 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m57]; exact w56_428
  have w57_42c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m57]; exact w56_42c
  have b57_430 : n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m57]; exact b56_430
  clear b56_430 w56_42c w56_428 w56_424 w56_420 w56_38c w56_388 w56_384 w56_380 w56_15c w56_158 w56_154 w56_150 w56_a4 w56_a0 w56_9c w56_98 w56_94 w56_90 w56_8c w56_88 w56_84 w56_80 w56_7c w56_78 w56_74 w56_70 w56_6c w56_68 w56_64 w56_60 w56_5c w56_58 w56_54 w56_50 w56_4c w56_48 w56_44 w56_38 w56_34 w56_30 w56_2c d12_56 d8_56 o16_56 o12_56 o8_56 o4_56 o0_56 g56_27 g56_26 g56_25 g56_24 g56_23 g56_22 g56_21 g56_20 g56_19 g56_18 g56_10 g56_9 g56_8 g56_4 g56_3 g56_2 V56 E56 fR56 t56 fr56 Er56 Ok56 K56 rk56 s56 c56
  -- 0x742: branch, not taken
  obtain ⟨n58, d58, u58⟩ := s57.notTaken E57.self 0x744 sv_at_742
    (by decide) (by rw [g57_10, s57.zero]; exact br_beq_f (val_in.tlv_ne hr56))
  have s58 : St n58.mem SV n58 0x744 (reg n58) := ⟨u58.pc, rfl, fun _ => rfl⟩
  have m58 : n58.mem = n57.mem := u58.mem
  have fr58 : ∀ x, SvR B x → n58.mem x = n57.mem x := fun x _ => by rw [m58]
  have t58 : Steps n0 n58 := t57.trans (.single d58)
  have fR58 : ∀ x, SvR B x → n58.mem x = M0 x := fun x hx => (fr58 x hx).trans (fR57 x hx)
  have E58 : SvCode n58.mem := E57.fr F fr58
  have V58 : SvSaves B n58.mem v := V57.same m58
  have g58_2 : reg n58 sp = B + 0x21A0 := by rw [u58.regs, g57_2]
  have g58_3 : reg n58 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u58.regs, g57_3]
  have g58_4 : reg n58 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u58.regs, g57_4]
  have g58_8 : reg n58 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u58.regs, g57_8]
  have g58_9 : reg n58 (9 : Fin 32) = tbp := by rw [u58.regs, g57_9]
  have g58_10 : reg n58 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u58.regs, g57_10]
  have g58_18 : reg n58 (18 : Fin 32) = out := by rw [u58.regs, g57_18]
  have g58_19 : reg n58 (19 : Fin 32) = bp := by rw [u58.regs, g57_19]
  have g58_20 : reg n58 (20 : Fin 32) = dg := by rw [u58.regs, g57_20]
  have g58_21 : reg n58 (21 : Fin 32) = rootp := by rw [u58.regs, g57_21]
  have g58_22 : reg n58 (22 : Fin 32) = ll := by rw [u58.regs, g57_22]
  have g58_23 : reg n58 (23 : Fin 32) = sgp := by rw [u58.regs, g57_23]
  have g58_24 : reg n58 (24 : Fin 32) = kp := by rw [u58.regs, g57_24]
  have g58_25 : reg n58 (25 : Fin 32) = sgl := by rw [u58.regs, g57_25]
  have g58_26 : reg n58 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u58.regs, g57_26]
  have g58_27 : reg n58 (27 : Fin 32) = tbl := by rw [u58.regs, g57_27]
  have keep_kk58 : SvKeepL B n0.mem n58.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m58]; exact keep_kk57
  clear keep_kk57
  have w58_2c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m58]; exact w57_2c
  have w58_30 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m58]; exact w57_30
  have w58_34 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m58]; exact w57_34
  have w58_38 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m58]; exact w57_38
  have w58_44 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m58]; exact w57_44
  have w58_48 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m58]; exact w57_48
  have w58_4c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m58]; exact w57_4c
  have w58_50 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m58]; exact w57_50
  have w58_54 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m58]; exact w57_54
  have w58_58 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m58]; exact w57_58
  have w58_5c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m58]; exact w57_5c
  have w58_60 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m58]; exact w57_60
  have w58_64 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m58]; exact w57_64
  have w58_68 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m58]; exact w57_68
  have w58_6c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m58]; exact w57_6c
  have w58_70 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m58]; exact w57_70
  have w58_74 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m58]; exact w57_74
  have w58_78 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m58]; exact w57_78
  have w58_7c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m58]; exact w57_7c
  have w58_80 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m58]; exact w57_80
  have w58_84 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m58]; exact w57_84
  have w58_88 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m58]; exact w57_88
  have w58_8c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m58]; exact w57_8c
  have w58_90 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m58]; exact w57_90
  have w58_94 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m58]; exact w57_94
  have w58_98 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m58]; exact w57_98
  have w58_9c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m58]; exact w57_9c
  have w58_a0 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m58]; exact w57_a0
  have w58_a4 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m58]; exact w57_a4
  have w58_150 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m58]; exact w57_150
  have w58_154 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m58]; exact w57_154
  have w58_158 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m58]; exact w57_158
  have w58_15c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m58]; exact w57_15c
  have w58_380 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m58]; exact w57_380
  have w58_384 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m58]; exact w57_384
  have w58_388 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m58]; exact w57_388
  have w58_38c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m58]; exact w57_38c
  have w58_420 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m58]; exact w57_420
  have w58_424 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m58]; exact w57_424
  have w58_428 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m58]; exact w57_428
  have w58_42c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m58]; exact w57_42c
  have b58_430 : n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m58]; exact b57_430
  clear b57_430 w57_42c w57_428 w57_424 w57_420 w57_38c w57_388 w57_384 w57_380 w57_15c w57_158 w57_154 w57_150 w57_a4 w57_a0 w57_9c w57_98 w57_94 w57_90 w57_8c w57_88 w57_84 w57_80 w57_7c w57_78 w57_74 w57_70 w57_6c w57_68 w57_64 w57_60 w57_5c w57_58 w57_54 w57_50 w57_4c w57_48 w57_44 w57_38 w57_34 w57_30 w57_2c g57_10 g57_27 g57_26 g57_25 g57_24 g57_23 g57_22 g57_21 g57_20 g57_19 g57_18 g57_9 g57_8 g57_4 g57_3 g57_2 V57 E57 fR57 t57 fr57 m57 s57 u57 d57
  -- 0x744: lbu
  obtain ⟨n59, d59, u59⟩ := s58.lbu E58.self sv_at_744 (off' := 0x748) (by decide)
  have s59 : St n59.mem SV n59 0x748 (reg n59) := ⟨u59.pc, rfl, fun _ => rfl⟩
  have m59 : n59.mem = n58.mem := u59.mem
  have fr59 : ∀ x, SvR B x → n59.mem x = n58.mem x := fun x _ => by rw [m59]
  have t59 : Steps n0 n59 := t58.trans (.single d59)
  have fR59 : ∀ x, SvR B x → n59.mem x = M0 x := fun x hx => (fr59 x hx).trans (fR58 x hx)
  have E59 : SvCode n59.mem := E58.fr F fr59
  have V59 : SvSaves B n59.mem v := V58.same m59
  have g59_2 : reg n59 sp = B + 0x21A0 := by rw [u59.regs, upd_ne (by decide) (by decide), g58_2]
  have g59_3 : reg n59 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u59.regs, upd_ne (by decide) (by decide), g58_3]
  have g59_4 : reg n59 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u59.regs, upd_ne (by decide) (by decide), g58_4]
  have g59_8 : reg n59 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u59.regs, upd_ne (by decide) (by decide), g58_8]
  have g59_9 : reg n59 (9 : Fin 32) = tbp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_9]
  have g59_10 : reg n59 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u59.regs, upd_ne (by decide) (by decide), g58_10]
  have g59_18 : reg n59 (18 : Fin 32) = out := by rw [u59.regs, upd_ne (by decide) (by decide), g58_18]
  have g59_19 : reg n59 (19 : Fin 32) = bp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_19]
  have g59_20 : reg n59 (20 : Fin 32) = dg := by rw [u59.regs, upd_ne (by decide) (by decide), g58_20]
  have g59_21 : reg n59 (21 : Fin 32) = rootp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_21]
  have g59_22 : reg n59 (22 : Fin 32) = ll := by rw [u59.regs, upd_ne (by decide) (by decide), g58_22]
  have g59_23 : reg n59 (23 : Fin 32) = sgp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_23]
  have g59_24 : reg n59 (24 : Fin 32) = kp := by rw [u59.regs, upd_ne (by decide) (by decide), g58_24]
  have g59_25 : reg n59 (25 : Fin 32) = sgl := by rw [u59.regs, upd_ne (by decide) (by decide), g58_25]
  have g59_26 : reg n59 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u59.regs, upd_ne (by decide) (by decide), g58_26]
  have g59_27 : reg n59 (27 : Fin 32) = tbl := by rw [u59.regs, upd_ne (by decide) (by decide), g58_27]
  have g59_11 : reg n59 a1 = (BitVec.ofNat 8 tl56.tag).zeroExtend 32 := by
    rw [u59.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g58_2, show B + 0x21A0 + 0x430 = B + 0x21A0 + BitVec.ofNat 32 0x430 by sv_addr, b58_430]
  have keep_kk59 : SvKeepL B n0.mem n59.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m59]; exact keep_kk58
  clear keep_kk58
  have w59_2c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m59]; exact w58_2c
  have w59_30 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m59]; exact w58_30
  have w59_34 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m59]; exact w58_34
  have w59_38 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m59]; exact w58_38
  have w59_44 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m59]; exact w58_44
  have w59_48 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m59]; exact w58_48
  have w59_4c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m59]; exact w58_4c
  have w59_50 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m59]; exact w58_50
  have w59_54 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m59]; exact w58_54
  have w59_58 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m59]; exact w58_58
  have w59_5c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m59]; exact w58_5c
  have w59_60 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m59]; exact w58_60
  have w59_64 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m59]; exact w58_64
  have w59_68 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m59]; exact w58_68
  have w59_6c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m59]; exact w58_6c
  have w59_70 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m59]; exact w58_70
  have w59_74 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m59]; exact w58_74
  have w59_78 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m59]; exact w58_78
  have w59_7c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m59]; exact w58_7c
  have w59_80 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m59]; exact w58_80
  have w59_84 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m59]; exact w58_84
  have w59_88 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m59]; exact w58_88
  have w59_8c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m59]; exact w58_8c
  have w59_90 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m59]; exact w58_90
  have w59_94 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m59]; exact w58_94
  have w59_98 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m59]; exact w58_98
  have w59_9c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m59]; exact w58_9c
  have w59_a0 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m59]; exact w58_a0
  have w59_a4 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m59]; exact w58_a4
  have w59_150 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m59]; exact w58_150
  have w59_154 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m59]; exact w58_154
  have w59_158 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m59]; exact w58_158
  have w59_15c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m59]; exact w58_15c
  have w59_380 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m59]; exact w58_380
  have w59_384 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m59]; exact w58_384
  have w59_388 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m59]; exact w58_388
  have w59_38c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m59]; exact w58_38c
  have w59_420 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m59]; exact w58_420
  have w59_424 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m59]; exact w58_424
  have w59_428 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m59]; exact w58_428
  have w59_42c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m59]; exact w58_42c
  have b59_430 : n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m59]; exact b58_430
  clear b58_430 w58_42c w58_428 w58_424 w58_420 w58_38c w58_388 w58_384 w58_380 w58_15c w58_158 w58_154 w58_150 w58_a4 w58_a0 w58_9c w58_98 w58_94 w58_90 w58_8c w58_88 w58_84 w58_80 w58_7c w58_78 w58_74 w58_70 w58_6c w58_68 w58_64 w58_60 w58_5c w58_58 w58_54 w58_50 w58_4c w58_48 w58_44 w58_38 w58_34 w58_30 w58_2c g58_27 g58_26 g58_25 g58_24 g58_23 g58_22 g58_21 g58_20 g58_19 g58_18 g58_10 g58_9 g58_8 g58_4 g58_3 g58_2 V58 E58 fR58 t58 fr58 m58 s58 u58 d58
  -- 0x748
  obtain ⟨n60, c60, u60⟩ := s59.block svDp1748 E59.self svDp1748_end
    ⟨trivial, trivial⟩
  have m60 : n60.mem = n59.mem := u60.mem
  have s60 : St n60.mem SV n60 0x74A (reg n60) := ⟨u60.pc, rfl, fun _ => rfl⟩
  have rb60 : ∀ q, reg n60 q = (runBlock svDp1748 (n59.mem, reg n59)).2 q := fun q => by rw [u60.regs]
  have fr60 : ∀ x, SvR B x → n60.mem x = n59.mem x := fun x _ => by rw [m60]
  have t60 : Steps n0 n60 := t59.trans c60
  have fR60 : ∀ x, SvR B x → n60.mem x = M0 x := fun x hx => (fr60 x hx).trans (fR59 x hx)
  have E60 : SvCode n60.mem := E59.fr F fr60
  have V60 : SvSaves B n60.mem v := V59.same m60
  have g60_2 : reg n60 sp = B + 0x21A0 := by
    rw [rb60, runBlock_reg _ _ _ sp s59.zero (by decide), g59_2]
  have g60_3 : reg n60 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb60, runBlock_reg _ _ _ (3 : Fin 32) s59.zero (by decide), g59_3]
  have g60_4 : reg n60 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb60, runBlock_reg _ _ _ (4 : Fin 32) s59.zero (by decide), g59_4]
  have g60_8 : reg n60 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb60, runBlock_reg _ _ _ (8 : Fin 32) s59.zero (by decide), g59_8]
  have g60_9 : reg n60 (9 : Fin 32) = tbp := by
    rw [rb60, runBlock_reg _ _ _ (9 : Fin 32) s59.zero (by decide), g59_9]
  have g60_10 : reg n60 a0 = (vp) + BitVec.ofNat 32 tl56.header := by
    rw [rb60, runBlock_reg _ _ _ a0 s59.zero (by decide), g59_10]
  have g60_11 : reg n60 a1 = (BitVec.ofNat 8 tl56.tag).zeroExtend 32 := by
    rw [rb60, runBlock_reg _ _ _ a1 s59.zero (by decide), g59_11]
  have g60_18 : reg n60 (18 : Fin 32) = out := by
    rw [rb60, runBlock_reg _ _ _ (18 : Fin 32) s59.zero (by decide), g59_18]
  have g60_19 : reg n60 (19 : Fin 32) = bp := by
    rw [rb60, runBlock_reg _ _ _ (19 : Fin 32) s59.zero (by decide), g59_19]
  have g60_20 : reg n60 (20 : Fin 32) = dg := by
    rw [rb60, runBlock_reg _ _ _ (20 : Fin 32) s59.zero (by decide), g59_20]
  have g60_21 : reg n60 (21 : Fin 32) = rootp := by
    rw [rb60, runBlock_reg _ _ _ (21 : Fin 32) s59.zero (by decide), g59_21]
  have g60_22 : reg n60 (22 : Fin 32) = ll := by
    rw [rb60, runBlock_reg _ _ _ (22 : Fin 32) s59.zero (by decide), g59_22]
  have g60_23 : reg n60 (23 : Fin 32) = sgp := by
    rw [rb60, runBlock_reg _ _ _ (23 : Fin 32) s59.zero (by decide), g59_23]
  have g60_24 : reg n60 (24 : Fin 32) = kp := by
    rw [rb60, runBlock_reg _ _ _ (24 : Fin 32) s59.zero (by decide), g59_24]
  have g60_25 : reg n60 (25 : Fin 32) = sgl := by
    rw [rb60, runBlock_reg _ _ _ (25 : Fin 32) s59.zero (by decide), g59_25]
  have g60_26 : reg n60 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by
    rw [rb60, runBlock_reg _ _ _ (26 : Fin 32) s59.zero (by decide), g59_26]
  have g60_27 : reg n60 (27 : Fin 32) = tbl := by
    rw [rb60, runBlock_reg _ _ _ (27 : Fin 32) s59.zero (by decide), g59_27]
  have g60_12 : reg n60 a2 = BitVec.ofNat 32 0xC := by
    rw [rb60]; simp +decide only [runBlock, BInstr.run, svDp1748, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g59_2, g59_3, g59_4, g59_8, g59_9, g59_10, g59_11, g59_18, g59_19, g59_20, g59_21, g59_22, g59_23, g59_24, g59_25, g59_26, g59_27, s59.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk60 : SvKeepL B n0.mem n60.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m60]; exact keep_kk59
  clear keep_kk59
  have w60_2c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m60]; exact w59_2c
  have w60_30 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m60]; exact w59_30
  have w60_34 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m60]; exact w59_34
  have w60_38 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m60]; exact w59_38
  have w60_44 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m60]; exact w59_44
  have w60_48 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m60]; exact w59_48
  have w60_4c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m60]; exact w59_4c
  have w60_50 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m60]; exact w59_50
  have w60_54 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m60]; exact w59_54
  have w60_58 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m60]; exact w59_58
  have w60_5c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m60]; exact w59_5c
  have w60_60 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m60]; exact w59_60
  have w60_64 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m60]; exact w59_64
  have w60_68 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m60]; exact w59_68
  have w60_6c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m60]; exact w59_6c
  have w60_70 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m60]; exact w59_70
  have w60_74 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m60]; exact w59_74
  have w60_78 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m60]; exact w59_78
  have w60_7c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m60]; exact w59_7c
  have w60_80 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m60]; exact w59_80
  have w60_84 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m60]; exact w59_84
  have w60_88 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m60]; exact w59_88
  have w60_8c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m60]; exact w59_8c
  have w60_90 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m60]; exact w59_90
  have w60_94 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m60]; exact w59_94
  have w60_98 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m60]; exact w59_98
  have w60_9c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m60]; exact w59_9c
  have w60_a0 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m60]; exact w59_a0
  have w60_a4 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m60]; exact w59_a4
  have w60_150 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m60]; exact w59_150
  have w60_154 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m60]; exact w59_154
  have w60_158 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m60]; exact w59_158
  have w60_15c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m60]; exact w59_15c
  have w60_380 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m60]; exact w59_380
  have w60_384 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m60]; exact w59_384
  have w60_388 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m60]; exact w59_388
  have w60_38c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m60]; exact w59_38c
  have w60_420 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m60]; exact w59_420
  have w60_424 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m60]; exact w59_424
  have w60_428 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m60]; exact w59_428
  have w60_42c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m60]; exact w59_42c
  have b60_430 : n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m60]; exact b59_430
  clear b59_430 w59_42c w59_428 w59_424 w59_420 w59_38c w59_388 w59_384 w59_380 w59_15c w59_158 w59_154 w59_150 w59_a4 w59_a0 w59_9c w59_98 w59_94 w59_90 w59_8c w59_88 w59_84 w59_80 w59_7c w59_78 w59_74 w59_70 w59_6c w59_68 w59_64 w59_60 w59_5c w59_58 w59_54 w59_50 w59_4c w59_48 w59_44 w59_38 w59_34 w59_30 w59_2c g59_11 g59_27 g59_26 g59_25 g59_24 g59_23 g59_22 g59_21 g59_20 g59_19 g59_18 g59_10 g59_9 g59_8 g59_4 g59_3 g59_2 V59 E59 fR59 t59 fr59 m59 s59 u59 d59
  by_cases hz_60 : BitVec.ofNat 8 tl56.tag = BitVec.ofNat 8 0xC
  rotate_left
  · -- 0x74A: branch, taken
    obtain ⟨n61, d61, u61⟩ := s60.taken E60.self 0x958 sv_at_74a
      (by decide) (by rw [g60_11, g60_12]; exact br_bne_byte_t (by decide) hz_60)
    have s61 : St n61.mem SV n61 0x958 (reg n61) := ⟨u61.pc, rfl, fun _ => rfl⟩
    have m61 : n61.mem = n60.mem := u61.mem
    have fr61 : ∀ x, SvR B x → n61.mem x = n60.mem x := fun x _ => by rw [m61]
    have t61 : Steps n0 n61 := t60.trans (.single d61)
    have fR61 : ∀ x, SvR B x → n61.mem x = M0 x := fun x hx => (fr61 x hx).trans (fR60 x hx)
    have E61 : SvCode n61.mem := E60.fr F fr61
    have V61 : SvSaves B n61.mem v := V60.same m61
    have g61_2 : reg n61 sp = B + 0x21A0 := by rw [u61.regs, g60_2]
    have g61_3 : reg n61 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u61.regs, g60_3]
    have g61_4 : reg n61 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u61.regs, g60_4]
    have g61_8 : reg n61 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u61.regs, g60_8]
    have g61_9 : reg n61 (9 : Fin 32) = tbp := by rw [u61.regs, g60_9]
    have g61_10 : reg n61 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u61.regs, g60_10]
    have g61_11 : reg n61 a1 = (BitVec.ofNat 8 tl56.tag).zeroExtend 32 := by rw [u61.regs, g60_11]
    have g61_12 : reg n61 a2 = BitVec.ofNat 32 0xC := by rw [u61.regs, g60_12]
    have g61_18 : reg n61 (18 : Fin 32) = out := by rw [u61.regs, g60_18]
    have g61_19 : reg n61 (19 : Fin 32) = bp := by rw [u61.regs, g60_19]
    have g61_20 : reg n61 (20 : Fin 32) = dg := by rw [u61.regs, g60_20]
    have g61_21 : reg n61 (21 : Fin 32) = rootp := by rw [u61.regs, g60_21]
    have g61_22 : reg n61 (22 : Fin 32) = ll := by rw [u61.regs, g60_22]
    have g61_23 : reg n61 (23 : Fin 32) = sgp := by rw [u61.regs, g60_23]
    have g61_24 : reg n61 (24 : Fin 32) = kp := by rw [u61.regs, g60_24]
    have g61_25 : reg n61 (25 : Fin 32) = sgl := by rw [u61.regs, g60_25]
    have g61_26 : reg n61 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u61.regs, g60_26]
    have g61_27 : reg n61 (27 : Fin 32) = tbl := by rw [u61.regs, g60_27]
    have keep_kk61 : SvKeepL B n0.mem n61.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m61]; exact keep_kk60
    clear keep_kk60
    have w61_2c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m61]; exact w60_2c
    have w61_30 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m61]; exact w60_30
    have w61_34 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m61]; exact w60_34
    have w61_38 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m61]; exact w60_38
    have w61_44 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m61]; exact w60_44
    have w61_48 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m61]; exact w60_48
    have w61_4c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m61]; exact w60_4c
    have w61_50 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m61]; exact w60_50
    have w61_54 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m61]; exact w60_54
    have w61_58 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m61]; exact w60_58
    have w61_5c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m61]; exact w60_5c
    have w61_60 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m61]; exact w60_60
    have w61_64 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m61]; exact w60_64
    have w61_68 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m61]; exact w60_68
    have w61_6c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m61]; exact w60_6c
    have w61_70 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m61]; exact w60_70
    have w61_74 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m61]; exact w60_74
    have w61_78 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m61]; exact w60_78
    have w61_7c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m61]; exact w60_7c
    have w61_80 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m61]; exact w60_80
    have w61_84 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m61]; exact w60_84
    have w61_88 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m61]; exact w60_88
    have w61_8c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m61]; exact w60_8c
    have w61_90 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m61]; exact w60_90
    have w61_94 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m61]; exact w60_94
    have w61_98 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m61]; exact w60_98
    have w61_9c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m61]; exact w60_9c
    have w61_a0 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m61]; exact w60_a0
    have w61_a4 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m61]; exact w60_a4
    have w61_150 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m61]; exact w60_150
    have w61_154 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m61]; exact w60_154
    have w61_158 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m61]; exact w60_158
    have w61_15c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m61]; exact w60_15c
    have w61_380 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m61]; exact w60_380
    have w61_384 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m61]; exact w60_384
    have w61_388 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m61]; exact w60_388
    have w61_38c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m61]; exact w60_38c
    have w61_420 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m61]; exact w60_420
    have w61_424 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m61]; exact w60_424
    have w61_428 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m61]; exact w60_428
    have w61_42c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m61]; exact w60_42c
    have b61_430 : n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m61]; exact b60_430
    clear b60_430 w60_42c w60_428 w60_424 w60_420 w60_38c w60_388 w60_384 w60_380 w60_15c w60_158 w60_154 w60_150 w60_a4 w60_a0 w60_9c w60_98 w60_94 w60_90 w60_8c w60_88 w60_84 w60_80 w60_7c w60_78 w60_74 w60_70 w60_6c w60_68 w60_64 w60_60 w60_5c w60_58 w60_54 w60_50 w60_4c w60_48 w60_44 w60_38 w60_34 w60_30 w60_2c g60_12 g60_27 g60_26 g60_25 g60_24 g60_23 g60_22 g60_21 g60_20 g60_19 g60_18 g60_11 g60_10 g60_9 g60_8 g60_4 g60_3 g60_2 V60 E60 fR60 t60 fr60 rb60 s60 m60 u60 c60
    -- 0x958
    obtain ⟨n62, c62, u62⟩ := s61.block svDp1958 E61.self svDp1958_end
      ⟨trivial, trivial⟩
    have m62 : n62.mem = n61.mem := u62.mem
    have s62 : St n62.mem SV n62 0x95A (reg n62) := ⟨u62.pc, rfl, fun _ => rfl⟩
    have rb62 : ∀ q, reg n62 q = (runBlock svDp1958 (n61.mem, reg n61)).2 q := fun q => by rw [u62.regs]
    have fr62 : ∀ x, SvR B x → n62.mem x = n61.mem x := fun x _ => by rw [m62]
    have t62 : Steps n0 n62 := t61.trans c62
    have fR62 : ∀ x, SvR B x → n62.mem x = M0 x := fun x hx => (fr62 x hx).trans (fR61 x hx)
    have E62 : SvCode n62.mem := E61.fr F fr62
    have V62 : SvSaves B n62.mem v := V61.same m62
    have g62_2 : reg n62 sp = B + 0x21A0 := by
      rw [rb62, runBlock_reg _ _ _ sp s61.zero (by decide), g61_2]
    have g62_3 : reg n62 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb62, runBlock_reg _ _ _ (3 : Fin 32) s61.zero (by decide), g61_3]
    have g62_4 : reg n62 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb62, runBlock_reg _ _ _ (4 : Fin 32) s61.zero (by decide), g61_4]
    have g62_8 : reg n62 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb62, runBlock_reg _ _ _ (8 : Fin 32) s61.zero (by decide), g61_8]
    have g62_9 : reg n62 (9 : Fin 32) = tbp := by
      rw [rb62, runBlock_reg _ _ _ (9 : Fin 32) s61.zero (by decide), g61_9]
    have g62_11 : reg n62 a1 = (BitVec.ofNat 8 tl56.tag).zeroExtend 32 := by
      rw [rb62, runBlock_reg _ _ _ a1 s61.zero (by decide), g61_11]
    have g62_12 : reg n62 a2 = BitVec.ofNat 32 0xC := by
      rw [rb62, runBlock_reg _ _ _ a2 s61.zero (by decide), g61_12]
    have g62_18 : reg n62 (18 : Fin 32) = out := by
      rw [rb62, runBlock_reg _ _ _ (18 : Fin 32) s61.zero (by decide), g61_18]
    have g62_19 : reg n62 (19 : Fin 32) = bp := by
      rw [rb62, runBlock_reg _ _ _ (19 : Fin 32) s61.zero (by decide), g61_19]
    have g62_20 : reg n62 (20 : Fin 32) = dg := by
      rw [rb62, runBlock_reg _ _ _ (20 : Fin 32) s61.zero (by decide), g61_20]
    have g62_21 : reg n62 (21 : Fin 32) = rootp := by
      rw [rb62, runBlock_reg _ _ _ (21 : Fin 32) s61.zero (by decide), g61_21]
    have g62_22 : reg n62 (22 : Fin 32) = ll := by
      rw [rb62, runBlock_reg _ _ _ (22 : Fin 32) s61.zero (by decide), g61_22]
    have g62_23 : reg n62 (23 : Fin 32) = sgp := by
      rw [rb62, runBlock_reg _ _ _ (23 : Fin 32) s61.zero (by decide), g61_23]
    have g62_24 : reg n62 (24 : Fin 32) = kp := by
      rw [rb62, runBlock_reg _ _ _ (24 : Fin 32) s61.zero (by decide), g61_24]
    have g62_25 : reg n62 (25 : Fin 32) = sgl := by
      rw [rb62, runBlock_reg _ _ _ (25 : Fin 32) s61.zero (by decide), g61_25]
    have g62_26 : reg n62 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by
      rw [rb62, runBlock_reg _ _ _ (26 : Fin 32) s61.zero (by decide), g61_26]
    have g62_27 : reg n62 (27 : Fin 32) = tbl := by
      rw [rb62, runBlock_reg _ _ _ (27 : Fin 32) s61.zero (by decide), g61_27]
    have g62_10 : reg n62 a0 = BitVec.ofNat 32 0x16 := by
      rw [rb62]; simp +decide only [runBlock, BInstr.run, svDp1958, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g61_2, g61_3, g61_4, g61_8, g61_9, g61_10, g61_11, g61_12, g61_18, g61_19, g61_20, g61_21, g61_22, g61_23, g61_24, g61_25, g61_26, g61_27, s61.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk62 : SvKeepL B n0.mem n62.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m62]; exact keep_kk61
    clear keep_kk61
    have w62_2c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m62]; exact w61_2c
    have w62_30 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m62]; exact w61_30
    have w62_34 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m62]; exact w61_34
    have w62_38 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m62]; exact w61_38
    have w62_44 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m62]; exact w61_44
    have w62_48 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m62]; exact w61_48
    have w62_4c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m62]; exact w61_4c
    have w62_50 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m62]; exact w61_50
    have w62_54 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m62]; exact w61_54
    have w62_58 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m62]; exact w61_58
    have w62_5c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m62]; exact w61_5c
    have w62_60 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m62]; exact w61_60
    have w62_64 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m62]; exact w61_64
    have w62_68 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m62]; exact w61_68
    have w62_6c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m62]; exact w61_6c
    have w62_70 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m62]; exact w61_70
    have w62_74 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m62]; exact w61_74
    have w62_78 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m62]; exact w61_78
    have w62_7c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m62]; exact w61_7c
    have w62_80 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m62]; exact w61_80
    have w62_84 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m62]; exact w61_84
    have w62_88 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m62]; exact w61_88
    have w62_8c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m62]; exact w61_8c
    have w62_90 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m62]; exact w61_90
    have w62_94 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m62]; exact w61_94
    have w62_98 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m62]; exact w61_98
    have w62_9c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m62]; exact w61_9c
    have w62_a0 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m62]; exact w61_a0
    have w62_a4 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m62]; exact w61_a4
    have w62_150 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m62]; exact w61_150
    have w62_154 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m62]; exact w61_154
    have w62_158 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m62]; exact w61_158
    have w62_15c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m62]; exact w61_15c
    have w62_380 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m62]; exact w61_380
    have w62_384 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m62]; exact w61_384
    have w62_388 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m62]; exact w61_388
    have w62_38c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m62]; exact w61_38c
    have w62_420 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m62]; exact w61_420
    have w62_424 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m62]; exact w61_424
    have w62_428 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m62]; exact w61_428
    have w62_42c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m62]; exact w61_42c
    have b62_430 : n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m62]; exact b61_430
    clear b61_430 w61_42c w61_428 w61_424 w61_420 w61_38c w61_388 w61_384 w61_380 w61_15c w61_158 w61_154 w61_150 w61_a4 w61_a0 w61_9c w61_98 w61_94 w61_90 w61_8c w61_88 w61_84 w61_80 w61_7c w61_78 w61_74 w61_70 w61_6c w61_68 w61_64 w61_60 w61_5c w61_58 w61_54 w61_50 w61_4c w61_48 w61_44 w61_38 w61_34 w61_30 w61_2c g61_27 g61_26 g61_25 g61_24 g61_23 g61_22 g61_21 g61_20 g61_19 g61_18 g61_12 g61_11 g61_10 g61_9 g61_8 g61_4 g61_3 g61_2 V61 E61 fR61 t61 fr61 m61 s61 u61 d61
    -- 0x95A: j
    obtain ⟨n63, d63, u63⟩ := s62.jump E62.self sv_at_95a (off' := 0x942) (by decide)
      (by rw [s62.pc]; decide)
    have s63 : St n63.mem SV n63 0x942 (reg n63) := ⟨u63.pc, rfl, fun _ => rfl⟩
    have m63 : n63.mem = n62.mem := u63.mem
    have fr63 : ∀ x, SvR B x → n63.mem x = n62.mem x := fun x _ => by rw [m63]
    have t63 : Steps n0 n63 := t62.trans (.single d63)
    have fR63 : ∀ x, SvR B x → n63.mem x = M0 x := fun x hx => (fr63 x hx).trans (fR62 x hx)
    have E63 : SvCode n63.mem := E62.fr F fr63
    have V63 : SvSaves B n63.mem v := V62.same m63
    have g63_2 : reg n63 sp = B + 0x21A0 := by rw [u63.regs, g62_2]
    have g63_3 : reg n63 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u63.regs, g62_3]
    have g63_4 : reg n63 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u63.regs, g62_4]
    have g63_8 : reg n63 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u63.regs, g62_8]
    have g63_9 : reg n63 (9 : Fin 32) = tbp := by rw [u63.regs, g62_9]
    have g63_10 : reg n63 a0 = BitVec.ofNat 32 0x16 := by rw [u63.regs, g62_10]
    have g63_11 : reg n63 a1 = (BitVec.ofNat 8 tl56.tag).zeroExtend 32 := by rw [u63.regs, g62_11]
    have g63_12 : reg n63 a2 = BitVec.ofNat 32 0xC := by rw [u63.regs, g62_12]
    have g63_18 : reg n63 (18 : Fin 32) = out := by rw [u63.regs, g62_18]
    have g63_19 : reg n63 (19 : Fin 32) = bp := by rw [u63.regs, g62_19]
    have g63_20 : reg n63 (20 : Fin 32) = dg := by rw [u63.regs, g62_20]
    have g63_21 : reg n63 (21 : Fin 32) = rootp := by rw [u63.regs, g62_21]
    have g63_22 : reg n63 (22 : Fin 32) = ll := by rw [u63.regs, g62_22]
    have g63_23 : reg n63 (23 : Fin 32) = sgp := by rw [u63.regs, g62_23]
    have g63_24 : reg n63 (24 : Fin 32) = kp := by rw [u63.regs, g62_24]
    have g63_25 : reg n63 (25 : Fin 32) = sgl := by rw [u63.regs, g62_25]
    have g63_26 : reg n63 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u63.regs, g62_26]
    have g63_27 : reg n63 (27 : Fin 32) = tbl := by rw [u63.regs, g62_27]
    have keep_kk63 : SvKeepL B n0.mem n63.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m63]; exact keep_kk62
    clear keep_kk62
    have w63_2c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m63]; exact w62_2c
    have w63_30 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m63]; exact w62_30
    have w63_34 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m63]; exact w62_34
    have w63_38 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m63]; exact w62_38
    have w63_44 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m63]; exact w62_44
    have w63_48 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m63]; exact w62_48
    have w63_4c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m63]; exact w62_4c
    have w63_50 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m63]; exact w62_50
    have w63_54 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m63]; exact w62_54
    have w63_58 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m63]; exact w62_58
    have w63_5c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m63]; exact w62_5c
    have w63_60 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m63]; exact w62_60
    have w63_64 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m63]; exact w62_64
    have w63_68 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m63]; exact w62_68
    have w63_6c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m63]; exact w62_6c
    have w63_70 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m63]; exact w62_70
    have w63_74 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m63]; exact w62_74
    have w63_78 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m63]; exact w62_78
    have w63_7c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m63]; exact w62_7c
    have w63_80 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m63]; exact w62_80
    have w63_84 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m63]; exact w62_84
    have w63_88 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m63]; exact w62_88
    have w63_8c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m63]; exact w62_8c
    have w63_90 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m63]; exact w62_90
    have w63_94 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m63]; exact w62_94
    have w63_98 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m63]; exact w62_98
    have w63_9c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m63]; exact w62_9c
    have w63_a0 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m63]; exact w62_a0
    have w63_a4 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m63]; exact w62_a4
    have w63_150 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m63]; exact w62_150
    have w63_154 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m63]; exact w62_154
    have w63_158 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m63]; exact w62_158
    have w63_15c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m63]; exact w62_15c
    have w63_380 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m63]; exact w62_380
    have w63_384 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m63]; exact w62_384
    have w63_388 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m63]; exact w62_388
    have w63_38c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m63]; exact w62_38c
    have w63_420 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m63]; exact w62_420
    have w63_424 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m63]; exact w62_424
    have w63_428 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m63]; exact w62_428
    have w63_42c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m63]; exact w62_42c
    have b63_430 : n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m63]; exact b62_430
    clear b62_430 w62_42c w62_428 w62_424 w62_420 w62_38c w62_388 w62_384 w62_380 w62_15c w62_158 w62_154 w62_150 w62_a4 w62_a0 w62_9c w62_98 w62_94 w62_90 w62_8c w62_88 w62_84 w62_80 w62_7c w62_78 w62_74 w62_70 w62_6c w62_68 w62_64 w62_60 w62_5c w62_58 w62_54 w62_50 w62_4c w62_48 w62_44 w62_38 w62_34 w62_30 w62_2c g62_10 g62_27 g62_26 g62_25 g62_24 g62_23 g62_22 g62_21 g62_20 g62_19 g62_18 g62_12 g62_11 g62_9 g62_8 g62_4 g62_3 g62_2 V62 E62 fR62 t62 fr62 rb62 s62 m62 u62 c62
    -- 0x942: sw
    obtain ⟨n64, d64, s64, fr64, K64, W64, rg64⟩ := sv_sw F E63 s63 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g63_2]; sv_addr) (by decide) (by decide)
    have t64 : Steps n0 n64 := t63.trans d64
    have fR64 : ∀ x, SvR B x → n64.mem x = M0 x := fun x hx => (fr64 x hx).trans (fR63 x hx)
    have E64 : SvCode n64.mem := E63.fr F fr64
    have V64 : SvSaves B n64.mem v := V63.keep K64 (by decide)
    have g64_2 : reg n64 sp = B + 0x21A0 := by rw [rg64 sp, g63_2]
    have g64_3 : reg n64 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg64 (3 : Fin 32), g63_3]
    have g64_4 : reg n64 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg64 (4 : Fin 32), g63_4]
    have g64_8 : reg n64 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg64 (8 : Fin 32), g63_8]
    have g64_9 : reg n64 (9 : Fin 32) = tbp := by rw [rg64 (9 : Fin 32), g63_9]
    have g64_10 : reg n64 a0 = BitVec.ofNat 32 0x16 := by rw [rg64 a0, g63_10]
    have g64_11 : reg n64 a1 = (BitVec.ofNat 8 tl56.tag).zeroExtend 32 := by rw [rg64 a1, g63_11]
    have g64_12 : reg n64 a2 = BitVec.ofNat 32 0xC := by rw [rg64 a2, g63_12]
    have g64_18 : reg n64 (18 : Fin 32) = out := by rw [rg64 (18 : Fin 32), g63_18]
    have g64_19 : reg n64 (19 : Fin 32) = bp := by rw [rg64 (19 : Fin 32), g63_19]
    have g64_20 : reg n64 (20 : Fin 32) = dg := by rw [rg64 (20 : Fin 32), g63_20]
    have g64_21 : reg n64 (21 : Fin 32) = rootp := by rw [rg64 (21 : Fin 32), g63_21]
    have g64_22 : reg n64 (22 : Fin 32) = ll := by rw [rg64 (22 : Fin 32), g63_22]
    have g64_23 : reg n64 (23 : Fin 32) = sgp := by rw [rg64 (23 : Fin 32), g63_23]
    have g64_24 : reg n64 (24 : Fin 32) = kp := by rw [rg64 (24 : Fin 32), g63_24]
    have g64_25 : reg n64 (25 : Fin 32) = sgl := by rw [rg64 (25 : Fin 32), g63_25]
    have g64_26 : reg n64 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rg64 (26 : Fin 32), g63_26]
    have g64_27 : reg n64 (27 : Fin 32) = tbl := by rw [rg64 (27 : Fin 32), g63_27]
    have keep_kk64 : SvKeepL B n0.mem n64.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := keep_kk63.trans K64.toL
    clear keep_kk63
    have w64_2c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K64.w32 (by decide) (by decide)).trans w63_2c
    have w64_30 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K64.w32 (by decide) (by decide)).trans w63_30
    have w64_34 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K64.w32 (by decide) (by decide)).trans w63_34
    have w64_38 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K64.w32 (by decide) (by decide)).trans w63_38
    have w64_48 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K64.w32 (by decide) (by decide)).trans w63_48
    have w64_4c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K64.w32 (by decide) (by decide)).trans w63_4c
    have w64_50 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K64.w32 (by decide) (by decide)).trans w63_50
    have w64_54 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K64.w32 (by decide) (by decide)).trans w63_54
    have w64_58 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K64.w32 (by decide) (by decide)).trans w63_58
    have w64_5c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K64.w32 (by decide) (by decide)).trans w63_5c
    have w64_60 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K64.w32 (by decide) (by decide)).trans w63_60
    have w64_64 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K64.w32 (by decide) (by decide)).trans w63_64
    have w64_68 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K64.w32 (by decide) (by decide)).trans w63_68
    have w64_6c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K64.w32 (by decide) (by decide)).trans w63_6c
    have w64_70 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K64.w32 (by decide) (by decide)).trans w63_70
    have w64_74 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K64.w32 (by decide) (by decide)).trans w63_74
    have w64_78 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K64.w32 (by decide) (by decide)).trans w63_78
    have w64_7c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K64.w32 (by decide) (by decide)).trans w63_7c
    have w64_80 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K64.w32 (by decide) (by decide)).trans w63_80
    have w64_84 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K64.w32 (by decide) (by decide)).trans w63_84
    have w64_88 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K64.w32 (by decide) (by decide)).trans w63_88
    have w64_8c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K64.w32 (by decide) (by decide)).trans w63_8c
    have w64_90 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K64.w32 (by decide) (by decide)).trans w63_90
    have w64_94 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K64.w32 (by decide) (by decide)).trans w63_94
    have w64_98 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K64.w32 (by decide) (by decide)).trans w63_98
    have w64_9c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K64.w32 (by decide) (by decide)).trans w63_9c
    have w64_a0 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K64.w32 (by decide) (by decide)).trans w63_a0
    have w64_a4 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K64.w32 (by decide) (by decide)).trans w63_a4
    have w64_150 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K64.w32 (by decide) (by decide)).trans w63_150
    have w64_154 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K64.w32 (by decide) (by decide)).trans w63_154
    have w64_158 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K64.w32 (by decide) (by decide)).trans w63_158
    have w64_15c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K64.w32 (by decide) (by decide)).trans w63_15c
    have w64_380 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K64.w32 (by decide) (by decide)).trans w63_380
    have w64_384 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K64.w32 (by decide) (by decide)).trans w63_384
    have w64_388 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := (K64.w32 (by decide) (by decide)).trans w63_388
    have w64_38c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := (K64.w32 (by decide) (by decide)).trans w63_38c
    have w64_420 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := (K64.w32 (by decide) (by decide)).trans w63_420
    have w64_424 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := (K64.w32 (by decide) (by decide)).trans w63_424
    have w64_428 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K64.w32 (by decide) (by decide)).trans w63_428
    have w64_42c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := (K64.w32 (by decide) (by decide)).trans w63_42c
    have b64_430 : n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := (K64.b8 (by decide) (by decide)).trans b63_430
    have w64_44 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [W64, g63_10]
    clear b63_430 w63_42c w63_428 w63_424 w63_420 w63_38c w63_388 w63_384 w63_380 w63_15c w63_158 w63_154 w63_150 w63_a4 w63_a0 w63_9c w63_98 w63_94 w63_90 w63_8c w63_88 w63_84 w63_80 w63_7c w63_78 w63_74 w63_70 w63_6c w63_68 w63_64 w63_60 w63_5c w63_58 w63_54 w63_50 w63_4c w63_48 w63_44 w63_38 w63_34 w63_30 w63_2c g63_27 g63_26 g63_25 g63_24 g63_23 g63_22 g63_21 g63_20 g63_19 g63_18 g63_12 g63_11 g63_10 g63_9 g63_8 g63_4 g63_3 g63_2 V63 E63 fR63 t63 fr63 m63 s63 u63 d63
    -- 0x944: lw
    obtain ⟨n65, d65, u65⟩ := s64.lw E64.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g64_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s65 : St n65.mem SV n65 0x946 (reg n65) := ⟨u65.pc, rfl, fun _ => rfl⟩
    have m65 : n65.mem = n64.mem := u65.mem
    have fr65 : ∀ x, SvR B x → n65.mem x = n64.mem x := fun x _ => by rw [m65]
    have t65 : Steps n0 n65 := t64.trans (.single d65)
    have fR65 : ∀ x, SvR B x → n65.mem x = M0 x := fun x hx => (fr65 x hx).trans (fR64 x hx)
    have E65 : SvCode n65.mem := E64.fr F fr65
    have V65 : SvSaves B n65.mem v := V64.same m65
    have g65_2 : reg n65 sp = B + 0x21A0 := by rw [u65.regs, upd_ne (by decide) (by decide), g64_2]
    have g65_3 : reg n65 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u65.regs, upd_ne (by decide) (by decide), g64_3]
    have g65_4 : reg n65 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u65.regs, upd_ne (by decide) (by decide), g64_4]
    have g65_9 : reg n65 (9 : Fin 32) = tbp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_9]
    have g65_10 : reg n65 a0 = BitVec.ofNat 32 0x16 := by rw [u65.regs, upd_ne (by decide) (by decide), g64_10]
    have g65_11 : reg n65 a1 = (BitVec.ofNat 8 tl56.tag).zeroExtend 32 := by rw [u65.regs, upd_ne (by decide) (by decide), g64_11]
    have g65_12 : reg n65 a2 = BitVec.ofNat 32 0xC := by rw [u65.regs, upd_ne (by decide) (by decide), g64_12]
    have g65_18 : reg n65 (18 : Fin 32) = out := by rw [u65.regs, upd_ne (by decide) (by decide), g64_18]
    have g65_19 : reg n65 (19 : Fin 32) = bp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_19]
    have g65_20 : reg n65 (20 : Fin 32) = dg := by rw [u65.regs, upd_ne (by decide) (by decide), g64_20]
    have g65_21 : reg n65 (21 : Fin 32) = rootp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_21]
    have g65_22 : reg n65 (22 : Fin 32) = ll := by rw [u65.regs, upd_ne (by decide) (by decide), g64_22]
    have g65_23 : reg n65 (23 : Fin 32) = sgp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_23]
    have g65_24 : reg n65 (24 : Fin 32) = kp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_24]
    have g65_25 : reg n65 (25 : Fin 32) = sgl := by rw [u65.regs, upd_ne (by decide) (by decide), g64_25]
    have g65_26 : reg n65 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u65.regs, upd_ne (by decide) (by decide), g64_26]
    have g65_27 : reg n65 (27 : Fin 32) = tbl := by rw [u65.regs, upd_ne (by decide) (by decide), g64_27]
    have g65_8 : reg n65 (8 : Fin 32) = BitVec.ofNat 32 0x16 := by
      rw [u65.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g64_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w64_44]
    have keep_kk65 : SvKeepL B n0.mem n65.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m65]; exact keep_kk64
    clear keep_kk64
    have w65_2c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m65]; exact w64_2c
    have w65_30 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m65]; exact w64_30
    have w65_34 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m65]; exact w64_34
    have w65_38 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m65]; exact w64_38
    have w65_44 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m65]; exact w64_44
    have w65_48 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m65]; exact w64_48
    have w65_4c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m65]; exact w64_4c
    have w65_50 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m65]; exact w64_50
    have w65_54 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m65]; exact w64_54
    have w65_58 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m65]; exact w64_58
    have w65_5c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m65]; exact w64_5c
    have w65_60 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m65]; exact w64_60
    have w65_64 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m65]; exact w64_64
    have w65_68 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m65]; exact w64_68
    have w65_6c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m65]; exact w64_6c
    have w65_70 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m65]; exact w64_70
    have w65_74 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m65]; exact w64_74
    have w65_78 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m65]; exact w64_78
    have w65_7c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m65]; exact w64_7c
    have w65_80 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m65]; exact w64_80
    have w65_84 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m65]; exact w64_84
    have w65_88 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m65]; exact w64_88
    have w65_8c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m65]; exact w64_8c
    have w65_90 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m65]; exact w64_90
    have w65_94 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m65]; exact w64_94
    have w65_98 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m65]; exact w64_98
    have w65_9c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m65]; exact w64_9c
    have w65_a0 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m65]; exact w64_a0
    have w65_a4 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m65]; exact w64_a4
    have w65_150 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m65]; exact w64_150
    have w65_154 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m65]; exact w64_154
    have w65_158 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m65]; exact w64_158
    have w65_15c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m65]; exact w64_15c
    have w65_380 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m65]; exact w64_380
    have w65_384 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m65]; exact w64_384
    have w65_388 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m65]; exact w64_388
    have w65_38c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m65]; exact w64_38c
    have w65_420 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m65]; exact w64_420
    have w65_424 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m65]; exact w64_424
    have w65_428 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m65]; exact w64_428
    have w65_42c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m65]; exact w64_42c
    have b65_430 : n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m65]; exact b64_430
    clear w64_44 b64_430 w64_42c w64_428 w64_424 w64_420 w64_38c w64_388 w64_384 w64_380 w64_15c w64_158 w64_154 w64_150 w64_a4 w64_a0 w64_9c w64_98 w64_94 w64_90 w64_8c w64_88 w64_84 w64_80 w64_7c w64_78 w64_74 w64_70 w64_6c w64_68 w64_64 w64_60 w64_5c w64_58 w64_54 w64_50 w64_4c w64_48 w64_38 w64_34 w64_30 w64_2c g64_27 g64_26 g64_25 g64_24 g64_23 g64_22 g64_21 g64_20 g64_19 g64_18 g64_12 g64_11 g64_10 g64_9 g64_8 g64_4 g64_3 g64_2 V64 E64 fR64 t64 rg64 W64 K64 fr64 s64 d64
    -- 0x946: j
    obtain ⟨n66, d66, u66⟩ := s65.jump E65.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s65.pc]; decide)
    have s66 : St n66.mem SV n66 0x7A4 (reg n66) := ⟨u66.pc, rfl, fun _ => rfl⟩
    have m66 : n66.mem = n65.mem := u66.mem
    have fr66 : ∀ x, SvR B x → n66.mem x = n65.mem x := fun x _ => by rw [m66]
    have t66 : Steps n0 n66 := t65.trans (.single d66)
    have fR66 : ∀ x, SvR B x → n66.mem x = M0 x := fun x hx => (fr66 x hx).trans (fR65 x hx)
    have E66 : SvCode n66.mem := E65.fr F fr66
    have V66 : SvSaves B n66.mem v := V65.same m66
    have g66_2 : reg n66 sp = B + 0x21A0 := by rw [u66.regs, g65_2]
    have g66_3 : reg n66 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u66.regs, g65_3]
    have g66_4 : reg n66 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u66.regs, g65_4]
    have g66_8 : reg n66 (8 : Fin 32) = BitVec.ofNat 32 0x16 := by rw [u66.regs, g65_8]
    have g66_9 : reg n66 (9 : Fin 32) = tbp := by rw [u66.regs, g65_9]
    have g66_10 : reg n66 a0 = BitVec.ofNat 32 0x16 := by rw [u66.regs, g65_10]
    have g66_11 : reg n66 a1 = (BitVec.ofNat 8 tl56.tag).zeroExtend 32 := by rw [u66.regs, g65_11]
    have g66_12 : reg n66 a2 = BitVec.ofNat 32 0xC := by rw [u66.regs, g65_12]
    have g66_18 : reg n66 (18 : Fin 32) = out := by rw [u66.regs, g65_18]
    have g66_19 : reg n66 (19 : Fin 32) = bp := by rw [u66.regs, g65_19]
    have g66_20 : reg n66 (20 : Fin 32) = dg := by rw [u66.regs, g65_20]
    have g66_21 : reg n66 (21 : Fin 32) = rootp := by rw [u66.regs, g65_21]
    have g66_22 : reg n66 (22 : Fin 32) = ll := by rw [u66.regs, g65_22]
    have g66_23 : reg n66 (23 : Fin 32) = sgp := by rw [u66.regs, g65_23]
    have g66_24 : reg n66 (24 : Fin 32) = kp := by rw [u66.regs, g65_24]
    have g66_25 : reg n66 (25 : Fin 32) = sgl := by rw [u66.regs, g65_25]
    have g66_26 : reg n66 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u66.regs, g65_26]
    have g66_27 : reg n66 (27 : Fin 32) = tbl := by rw [u66.regs, g65_27]
    have keep_kk66 : SvKeepL B n0.mem n66.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m66]; exact keep_kk65
    clear keep_kk65
    have w66_2c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m66]; exact w65_2c
    have w66_30 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m66]; exact w65_30
    have w66_34 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m66]; exact w65_34
    have w66_38 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m66]; exact w65_38
    have w66_44 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m66]; exact w65_44
    have w66_48 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m66]; exact w65_48
    have w66_4c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m66]; exact w65_4c
    have w66_50 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m66]; exact w65_50
    have w66_54 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m66]; exact w65_54
    have w66_58 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m66]; exact w65_58
    have w66_5c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m66]; exact w65_5c
    have w66_60 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m66]; exact w65_60
    have w66_64 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m66]; exact w65_64
    have w66_68 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m66]; exact w65_68
    have w66_6c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m66]; exact w65_6c
    have w66_70 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m66]; exact w65_70
    have w66_74 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m66]; exact w65_74
    have w66_78 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m66]; exact w65_78
    have w66_7c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m66]; exact w65_7c
    have w66_80 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m66]; exact w65_80
    have w66_84 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m66]; exact w65_84
    have w66_88 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m66]; exact w65_88
    have w66_8c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m66]; exact w65_8c
    have w66_90 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m66]; exact w65_90
    have w66_94 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m66]; exact w65_94
    have w66_98 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m66]; exact w65_98
    have w66_9c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m66]; exact w65_9c
    have w66_a0 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m66]; exact w65_a0
    have w66_a4 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m66]; exact w65_a4
    have w66_150 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m66]; exact w65_150
    have w66_154 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m66]; exact w65_154
    have w66_158 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m66]; exact w65_158
    have w66_15c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m66]; exact w65_15c
    have w66_380 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m66]; exact w65_380
    have w66_384 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m66]; exact w65_384
    have w66_388 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m66]; exact w65_388
    have w66_38c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m66]; exact w65_38c
    have w66_420 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m66]; exact w65_420
    have w66_424 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m66]; exact w65_424
    have w66_428 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m66]; exact w65_428
    have w66_42c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m66]; exact w65_42c
    have b66_430 : n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m66]; exact b65_430
    clear b65_430 w65_42c w65_428 w65_424 w65_420 w65_38c w65_388 w65_384 w65_380 w65_15c w65_158 w65_154 w65_150 w65_a4 w65_a0 w65_9c w65_98 w65_94 w65_90 w65_8c w65_88 w65_84 w65_80 w65_7c w65_78 w65_74 w65_70 w65_6c w65_68 w65_64 w65_60 w65_5c w65_58 w65_54 w65_50 w65_4c w65_48 w65_44 w65_38 w65_34 w65_30 w65_2c g65_8 g65_27 g65_26 g65_25 g65_24 g65_23 g65_22 g65_21 g65_20 g65_19 g65_18 g65_12 g65_11 g65_10 g65_9 g65_4 g65_3 g65_2 V65 E65 fR65 t65 fr65 m65 s65 u65 d65
    exact .inl ⟨(fun ⟨tl56', h0', h1', _⟩ => by rw [hr56] at h0'; cases h0'; exact hz_60 h1'), sv_fail F E66 s66 t66 (fun x hx => (fR66 x hx).trans (fM x hx).symm) V66 hret g66_2 g66_18 hO g66_3 g66_4 (by rw [g66_8]; sv_code)⟩
  -- 0x74A: branch, not taken
  obtain ⟨n61, d61, u61⟩ := s60.notTaken E60.self 0x74E sv_at_74a
    (by decide) (by rw [g60_11, g60_12]; exact br_bne_byte_f (by decide) hz_60)
  have s61 : St n61.mem SV n61 0x74E (reg n61) := ⟨u61.pc, rfl, fun _ => rfl⟩
  have m61 : n61.mem = n60.mem := u61.mem
  have fr61 : ∀ x, SvR B x → n61.mem x = n60.mem x := fun x _ => by rw [m61]
  have t61 : Steps n0 n61 := t60.trans (.single d61)
  have fR61 : ∀ x, SvR B x → n61.mem x = M0 x := fun x hx => (fr61 x hx).trans (fR60 x hx)
  have E61 : SvCode n61.mem := E60.fr F fr61
  have V61 : SvSaves B n61.mem v := V60.same m61
  have g61_2 : reg n61 sp = B + 0x21A0 := by rw [u61.regs, g60_2]
  have g61_3 : reg n61 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u61.regs, g60_3]
  have g61_4 : reg n61 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u61.regs, g60_4]
  have g61_8 : reg n61 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u61.regs, g60_8]
  have g61_9 : reg n61 (9 : Fin 32) = tbp := by rw [u61.regs, g60_9]
  have g61_10 : reg n61 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u61.regs, g60_10]
  have g61_11 : reg n61 a1 = (BitVec.ofNat 8 tl56.tag).zeroExtend 32 := by rw [u61.regs, g60_11]
  have g61_12 : reg n61 a2 = BitVec.ofNat 32 0xC := by rw [u61.regs, g60_12]
  have g61_18 : reg n61 (18 : Fin 32) = out := by rw [u61.regs, g60_18]
  have g61_19 : reg n61 (19 : Fin 32) = bp := by rw [u61.regs, g60_19]
  have g61_20 : reg n61 (20 : Fin 32) = dg := by rw [u61.regs, g60_20]
  have g61_21 : reg n61 (21 : Fin 32) = rootp := by rw [u61.regs, g60_21]
  have g61_22 : reg n61 (22 : Fin 32) = ll := by rw [u61.regs, g60_22]
  have g61_23 : reg n61 (23 : Fin 32) = sgp := by rw [u61.regs, g60_23]
  have g61_24 : reg n61 (24 : Fin 32) = kp := by rw [u61.regs, g60_24]
  have g61_25 : reg n61 (25 : Fin 32) = sgl := by rw [u61.regs, g60_25]
  have g61_26 : reg n61 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u61.regs, g60_26]
  have g61_27 : reg n61 (27 : Fin 32) = tbl := by rw [u61.regs, g60_27]
  have keep_kk61 : SvKeepL B n0.mem n61.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m61]; exact keep_kk60
  clear keep_kk60
  have w61_2c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m61]; exact w60_2c
  have w61_30 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m61]; exact w60_30
  have w61_34 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m61]; exact w60_34
  have w61_38 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m61]; exact w60_38
  have w61_44 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m61]; exact w60_44
  have w61_48 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m61]; exact w60_48
  have w61_4c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m61]; exact w60_4c
  have w61_50 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m61]; exact w60_50
  have w61_54 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m61]; exact w60_54
  have w61_58 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m61]; exact w60_58
  have w61_5c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m61]; exact w60_5c
  have w61_60 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m61]; exact w60_60
  have w61_64 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m61]; exact w60_64
  have w61_68 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m61]; exact w60_68
  have w61_6c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m61]; exact w60_6c
  have w61_70 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m61]; exact w60_70
  have w61_74 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m61]; exact w60_74
  have w61_78 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m61]; exact w60_78
  have w61_7c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m61]; exact w60_7c
  have w61_80 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m61]; exact w60_80
  have w61_84 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m61]; exact w60_84
  have w61_88 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m61]; exact w60_88
  have w61_8c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m61]; exact w60_8c
  have w61_90 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m61]; exact w60_90
  have w61_94 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m61]; exact w60_94
  have w61_98 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m61]; exact w60_98
  have w61_9c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m61]; exact w60_9c
  have w61_a0 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m61]; exact w60_a0
  have w61_a4 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m61]; exact w60_a4
  have w61_150 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m61]; exact w60_150
  have w61_154 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m61]; exact w60_154
  have w61_158 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m61]; exact w60_158
  have w61_15c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m61]; exact w60_15c
  have w61_380 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m61]; exact w60_380
  have w61_384 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m61]; exact w60_384
  have w61_388 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m61]; exact w60_388
  have w61_38c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m61]; exact w60_38c
  have w61_420 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m61]; exact w60_420
  have w61_424 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m61]; exact w60_424
  have w61_428 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m61]; exact w60_428
  have w61_42c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m61]; exact w60_42c
  have b61_430 : n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m61]; exact b60_430
  clear b60_430 w60_42c w60_428 w60_424 w60_420 w60_38c w60_388 w60_384 w60_380 w60_15c w60_158 w60_154 w60_150 w60_a4 w60_a0 w60_9c w60_98 w60_94 w60_90 w60_8c w60_88 w60_84 w60_80 w60_7c w60_78 w60_74 w60_70 w60_6c w60_68 w60_64 w60_60 w60_5c w60_58 w60_54 w60_50 w60_4c w60_48 w60_44 w60_38 w60_34 w60_30 w60_2c g60_12 g60_27 g60_26 g60_25 g60_24 g60_23 g60_22 g60_21 g60_20 g60_19 g60_18 g60_11 g60_10 g60_9 g60_8 g60_4 g60_3 g60_2 V60 E60 fR60 t60 fr60 rb60 s60 m60 u60 c60
  -- 0x74E: lw
  obtain ⟨n62, d62, u62⟩ := s61.lw E61.self sv_at_74e (off' := 0x752) (by decide)
    (by rw [g61_2, show B + 0x21A0 + 0x38C = B + 0x21A0 + BitVec.ofNat 32 0x38C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s62 : St n62.mem SV n62 0x752 (reg n62) := ⟨u62.pc, rfl, fun _ => rfl⟩
  have m62 : n62.mem = n61.mem := u62.mem
  have fr62 : ∀ x, SvR B x → n62.mem x = n61.mem x := fun x _ => by rw [m62]
  have t62 : Steps n0 n62 := t61.trans (.single d62)
  have fR62 : ∀ x, SvR B x → n62.mem x = M0 x := fun x hx => (fr62 x hx).trans (fR61 x hx)
  have E62 : SvCode n62.mem := E61.fr F fr62
  have V62 : SvSaves B n62.mem v := V61.same m62
  have g62_2 : reg n62 sp = B + 0x21A0 := by rw [u62.regs, upd_ne (by decide) (by decide), g61_2]
  have g62_3 : reg n62 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u62.regs, upd_ne (by decide) (by decide), g61_3]
  have g62_4 : reg n62 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u62.regs, upd_ne (by decide) (by decide), g61_4]
  have g62_8 : reg n62 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u62.regs, upd_ne (by decide) (by decide), g61_8]
  have g62_9 : reg n62 (9 : Fin 32) = tbp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_9]
  have g62_10 : reg n62 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u62.regs, upd_ne (by decide) (by decide), g61_10]
  have g62_12 : reg n62 a2 = BitVec.ofNat 32 0xC := by rw [u62.regs, upd_ne (by decide) (by decide), g61_12]
  have g62_18 : reg n62 (18 : Fin 32) = out := by rw [u62.regs, upd_ne (by decide) (by decide), g61_18]
  have g62_19 : reg n62 (19 : Fin 32) = bp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_19]
  have g62_20 : reg n62 (20 : Fin 32) = dg := by rw [u62.regs, upd_ne (by decide) (by decide), g61_20]
  have g62_21 : reg n62 (21 : Fin 32) = rootp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_21]
  have g62_22 : reg n62 (22 : Fin 32) = ll := by rw [u62.regs, upd_ne (by decide) (by decide), g61_22]
  have g62_23 : reg n62 (23 : Fin 32) = sgp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_23]
  have g62_24 : reg n62 (24 : Fin 32) = kp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_24]
  have g62_25 : reg n62 (25 : Fin 32) = sgl := by rw [u62.regs, upd_ne (by decide) (by decide), g61_25]
  have g62_26 : reg n62 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u62.regs, upd_ne (by decide) (by decide), g61_26]
  have g62_27 : reg n62 (27 : Fin 32) = tbl := by rw [u62.regs, upd_ne (by decide) (by decide), g61_27]
  have g62_11 : reg n62 a1 = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by
    rw [u62.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g61_2, show B + 0x21A0 + 0x38C = B + 0x21A0 + BitVec.ofNat 32 0x38C by sv_addr, w61_38c]
  have keep_kk62 : SvKeepL B n0.mem n62.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m62]; exact keep_kk61
  clear keep_kk61
  have w62_2c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m62]; exact w61_2c
  have w62_30 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m62]; exact w61_30
  have w62_34 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m62]; exact w61_34
  have w62_38 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m62]; exact w61_38
  have w62_44 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m62]; exact w61_44
  have w62_48 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m62]; exact w61_48
  have w62_4c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m62]; exact w61_4c
  have w62_50 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m62]; exact w61_50
  have w62_54 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m62]; exact w61_54
  have w62_58 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m62]; exact w61_58
  have w62_5c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m62]; exact w61_5c
  have w62_60 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m62]; exact w61_60
  have w62_64 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m62]; exact w61_64
  have w62_68 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m62]; exact w61_68
  have w62_6c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m62]; exact w61_6c
  have w62_70 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m62]; exact w61_70
  have w62_74 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m62]; exact w61_74
  have w62_78 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m62]; exact w61_78
  have w62_7c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m62]; exact w61_7c
  have w62_80 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m62]; exact w61_80
  have w62_84 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m62]; exact w61_84
  have w62_88 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m62]; exact w61_88
  have w62_8c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m62]; exact w61_8c
  have w62_90 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m62]; exact w61_90
  have w62_94 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m62]; exact w61_94
  have w62_98 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m62]; exact w61_98
  have w62_9c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m62]; exact w61_9c
  have w62_a0 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m62]; exact w61_a0
  have w62_a4 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m62]; exact w61_a4
  have w62_150 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m62]; exact w61_150
  have w62_154 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m62]; exact w61_154
  have w62_158 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m62]; exact w61_158
  have w62_15c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m62]; exact w61_15c
  have w62_380 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m62]; exact w61_380
  have w62_384 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m62]; exact w61_384
  have w62_388 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m62]; exact w61_388
  have w62_38c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m62]; exact w61_38c
  have w62_420 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m62]; exact w61_420
  have w62_424 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m62]; exact w61_424
  have w62_428 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m62]; exact w61_428
  have w62_42c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m62]; exact w61_42c
  have b62_430 : n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m62]; exact b61_430
  clear b61_430 w61_42c w61_428 w61_424 w61_420 w61_38c w61_388 w61_384 w61_380 w61_15c w61_158 w61_154 w61_150 w61_a4 w61_a0 w61_9c w61_98 w61_94 w61_90 w61_8c w61_88 w61_84 w61_80 w61_7c w61_78 w61_74 w61_70 w61_6c w61_68 w61_64 w61_60 w61_5c w61_58 w61_54 w61_50 w61_4c w61_48 w61_44 w61_38 w61_34 w61_30 w61_2c g61_27 g61_26 g61_25 g61_24 g61_23 g61_22 g61_21 g61_20 g61_19 g61_18 g61_12 g61_11 g61_10 g61_9 g61_8 g61_4 g61_3 g61_2 V61 E61 fR61 t61 fr61 m61 s61 u61 d61
  by_cases hz_62 : (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) = 0
  rotate_left
  · -- 0x752: branch, taken
    obtain ⟨n63, d63, u63⟩ := s62.taken E62.self 0x940 sv_at_752
      (by decide) (by rw [g62_11, s62.zero]; exact br_bne_t hz_62)
    have s63 : St n63.mem SV n63 0x940 (reg n63) := ⟨u63.pc, rfl, fun _ => rfl⟩
    have m63 : n63.mem = n62.mem := u63.mem
    have fr63 : ∀ x, SvR B x → n63.mem x = n62.mem x := fun x _ => by rw [m63]
    have t63 : Steps n0 n63 := t62.trans (.single d63)
    have fR63 : ∀ x, SvR B x → n63.mem x = M0 x := fun x hx => (fr63 x hx).trans (fR62 x hx)
    have E63 : SvCode n63.mem := E62.fr F fr63
    have V63 : SvSaves B n63.mem v := V62.same m63
    have g63_2 : reg n63 sp = B + 0x21A0 := by rw [u63.regs, g62_2]
    have g63_3 : reg n63 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u63.regs, g62_3]
    have g63_4 : reg n63 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u63.regs, g62_4]
    have g63_8 : reg n63 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u63.regs, g62_8]
    have g63_9 : reg n63 (9 : Fin 32) = tbp := by rw [u63.regs, g62_9]
    have g63_10 : reg n63 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u63.regs, g62_10]
    have g63_11 : reg n63 a1 = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [u63.regs, g62_11]
    have g63_12 : reg n63 a2 = BitVec.ofNat 32 0xC := by rw [u63.regs, g62_12]
    have g63_18 : reg n63 (18 : Fin 32) = out := by rw [u63.regs, g62_18]
    have g63_19 : reg n63 (19 : Fin 32) = bp := by rw [u63.regs, g62_19]
    have g63_20 : reg n63 (20 : Fin 32) = dg := by rw [u63.regs, g62_20]
    have g63_21 : reg n63 (21 : Fin 32) = rootp := by rw [u63.regs, g62_21]
    have g63_22 : reg n63 (22 : Fin 32) = ll := by rw [u63.regs, g62_22]
    have g63_23 : reg n63 (23 : Fin 32) = sgp := by rw [u63.regs, g62_23]
    have g63_24 : reg n63 (24 : Fin 32) = kp := by rw [u63.regs, g62_24]
    have g63_25 : reg n63 (25 : Fin 32) = sgl := by rw [u63.regs, g62_25]
    have g63_26 : reg n63 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u63.regs, g62_26]
    have g63_27 : reg n63 (27 : Fin 32) = tbl := by rw [u63.regs, g62_27]
    have keep_kk63 : SvKeepL B n0.mem n63.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m63]; exact keep_kk62
    clear keep_kk62
    have w63_2c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m63]; exact w62_2c
    have w63_30 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m63]; exact w62_30
    have w63_34 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m63]; exact w62_34
    have w63_38 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m63]; exact w62_38
    have w63_44 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m63]; exact w62_44
    have w63_48 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m63]; exact w62_48
    have w63_4c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m63]; exact w62_4c
    have w63_50 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m63]; exact w62_50
    have w63_54 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m63]; exact w62_54
    have w63_58 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m63]; exact w62_58
    have w63_5c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m63]; exact w62_5c
    have w63_60 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m63]; exact w62_60
    have w63_64 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m63]; exact w62_64
    have w63_68 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m63]; exact w62_68
    have w63_6c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m63]; exact w62_6c
    have w63_70 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m63]; exact w62_70
    have w63_74 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m63]; exact w62_74
    have w63_78 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m63]; exact w62_78
    have w63_7c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m63]; exact w62_7c
    have w63_80 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m63]; exact w62_80
    have w63_84 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m63]; exact w62_84
    have w63_88 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m63]; exact w62_88
    have w63_8c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m63]; exact w62_8c
    have w63_90 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m63]; exact w62_90
    have w63_94 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m63]; exact w62_94
    have w63_98 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m63]; exact w62_98
    have w63_9c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m63]; exact w62_9c
    have w63_a0 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m63]; exact w62_a0
    have w63_a4 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m63]; exact w62_a4
    have w63_150 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m63]; exact w62_150
    have w63_154 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m63]; exact w62_154
    have w63_158 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m63]; exact w62_158
    have w63_15c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m63]; exact w62_15c
    have w63_380 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m63]; exact w62_380
    have w63_384 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m63]; exact w62_384
    have w63_388 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m63]; exact w62_388
    have w63_38c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m63]; exact w62_38c
    have w63_420 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m63]; exact w62_420
    have w63_424 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m63]; exact w62_424
    have w63_428 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m63]; exact w62_428
    have w63_42c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m63]; exact w62_42c
    have b63_430 : n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m63]; exact b62_430
    clear b62_430 w62_42c w62_428 w62_424 w62_420 w62_38c w62_388 w62_384 w62_380 w62_15c w62_158 w62_154 w62_150 w62_a4 w62_a0 w62_9c w62_98 w62_94 w62_90 w62_8c w62_88 w62_84 w62_80 w62_7c w62_78 w62_74 w62_70 w62_6c w62_68 w62_64 w62_60 w62_5c w62_58 w62_54 w62_50 w62_4c w62_48 w62_44 w62_38 w62_34 w62_30 w62_2c g62_11 g62_27 g62_26 g62_25 g62_24 g62_23 g62_22 g62_21 g62_20 g62_19 g62_18 g62_12 g62_10 g62_9 g62_8 g62_4 g62_3 g62_2 V62 E62 fR62 t62 fr62 m62 s62 u62 d62
    -- 0x940
    obtain ⟨n64, c64, u64⟩ := s63.block svDp1940 E63.self svDp1940_end
      ⟨trivial, trivial⟩
    have m64 : n64.mem = n63.mem := u64.mem
    have s64 : St n64.mem SV n64 0x942 (reg n64) := ⟨u64.pc, rfl, fun _ => rfl⟩
    have rb64 : ∀ q, reg n64 q = (runBlock svDp1940 (n63.mem, reg n63)).2 q := fun q => by rw [u64.regs]
    have fr64 : ∀ x, SvR B x → n64.mem x = n63.mem x := fun x _ => by rw [m64]
    have t64 : Steps n0 n64 := t63.trans c64
    have fR64 : ∀ x, SvR B x → n64.mem x = M0 x := fun x hx => (fr64 x hx).trans (fR63 x hx)
    have E64 : SvCode n64.mem := E63.fr F fr64
    have V64 : SvSaves B n64.mem v := V63.same m64
    have g64_2 : reg n64 sp = B + 0x21A0 := by
      rw [rb64, runBlock_reg _ _ _ sp s63.zero (by decide), g63_2]
    have g64_3 : reg n64 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb64, runBlock_reg _ _ _ (3 : Fin 32) s63.zero (by decide), g63_3]
    have g64_4 : reg n64 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb64, runBlock_reg _ _ _ (4 : Fin 32) s63.zero (by decide), g63_4]
    have g64_8 : reg n64 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb64, runBlock_reg _ _ _ (8 : Fin 32) s63.zero (by decide), g63_8]
    have g64_9 : reg n64 (9 : Fin 32) = tbp := by
      rw [rb64, runBlock_reg _ _ _ (9 : Fin 32) s63.zero (by decide), g63_9]
    have g64_11 : reg n64 a1 = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by
      rw [rb64, runBlock_reg _ _ _ a1 s63.zero (by decide), g63_11]
    have g64_12 : reg n64 a2 = BitVec.ofNat 32 0xC := by
      rw [rb64, runBlock_reg _ _ _ a2 s63.zero (by decide), g63_12]
    have g64_18 : reg n64 (18 : Fin 32) = out := by
      rw [rb64, runBlock_reg _ _ _ (18 : Fin 32) s63.zero (by decide), g63_18]
    have g64_19 : reg n64 (19 : Fin 32) = bp := by
      rw [rb64, runBlock_reg _ _ _ (19 : Fin 32) s63.zero (by decide), g63_19]
    have g64_20 : reg n64 (20 : Fin 32) = dg := by
      rw [rb64, runBlock_reg _ _ _ (20 : Fin 32) s63.zero (by decide), g63_20]
    have g64_21 : reg n64 (21 : Fin 32) = rootp := by
      rw [rb64, runBlock_reg _ _ _ (21 : Fin 32) s63.zero (by decide), g63_21]
    have g64_22 : reg n64 (22 : Fin 32) = ll := by
      rw [rb64, runBlock_reg _ _ _ (22 : Fin 32) s63.zero (by decide), g63_22]
    have g64_23 : reg n64 (23 : Fin 32) = sgp := by
      rw [rb64, runBlock_reg _ _ _ (23 : Fin 32) s63.zero (by decide), g63_23]
    have g64_24 : reg n64 (24 : Fin 32) = kp := by
      rw [rb64, runBlock_reg _ _ _ (24 : Fin 32) s63.zero (by decide), g63_24]
    have g64_25 : reg n64 (25 : Fin 32) = sgl := by
      rw [rb64, runBlock_reg _ _ _ (25 : Fin 32) s63.zero (by decide), g63_25]
    have g64_26 : reg n64 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by
      rw [rb64, runBlock_reg _ _ _ (26 : Fin 32) s63.zero (by decide), g63_26]
    have g64_27 : reg n64 (27 : Fin 32) = tbl := by
      rw [rb64, runBlock_reg _ _ _ (27 : Fin 32) s63.zero (by decide), g63_27]
    have g64_10 : reg n64 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb64]; simp +decide only [runBlock, BInstr.run, svDp1940, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g63_2, g63_3, g63_4, g63_8, g63_9, g63_10, g63_11, g63_12, g63_18, g63_19, g63_20, g63_21, g63_22, g63_23, g63_24, g63_25, g63_26, g63_27, s63.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk64 : SvKeepL B n0.mem n64.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m64]; exact keep_kk63
    clear keep_kk63
    have w64_2c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m64]; exact w63_2c
    have w64_30 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m64]; exact w63_30
    have w64_34 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m64]; exact w63_34
    have w64_38 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m64]; exact w63_38
    have w64_44 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m64]; exact w63_44
    have w64_48 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m64]; exact w63_48
    have w64_4c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m64]; exact w63_4c
    have w64_50 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m64]; exact w63_50
    have w64_54 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m64]; exact w63_54
    have w64_58 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m64]; exact w63_58
    have w64_5c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m64]; exact w63_5c
    have w64_60 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m64]; exact w63_60
    have w64_64 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m64]; exact w63_64
    have w64_68 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m64]; exact w63_68
    have w64_6c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m64]; exact w63_6c
    have w64_70 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m64]; exact w63_70
    have w64_74 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m64]; exact w63_74
    have w64_78 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m64]; exact w63_78
    have w64_7c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m64]; exact w63_7c
    have w64_80 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m64]; exact w63_80
    have w64_84 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m64]; exact w63_84
    have w64_88 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m64]; exact w63_88
    have w64_8c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m64]; exact w63_8c
    have w64_90 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m64]; exact w63_90
    have w64_94 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m64]; exact w63_94
    have w64_98 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m64]; exact w63_98
    have w64_9c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m64]; exact w63_9c
    have w64_a0 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m64]; exact w63_a0
    have w64_a4 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m64]; exact w63_a4
    have w64_150 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m64]; exact w63_150
    have w64_154 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m64]; exact w63_154
    have w64_158 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m64]; exact w63_158
    have w64_15c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m64]; exact w63_15c
    have w64_380 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m64]; exact w63_380
    have w64_384 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m64]; exact w63_384
    have w64_388 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m64]; exact w63_388
    have w64_38c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m64]; exact w63_38c
    have w64_420 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m64]; exact w63_420
    have w64_424 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m64]; exact w63_424
    have w64_428 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m64]; exact w63_428
    have w64_42c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m64]; exact w63_42c
    have b64_430 : n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m64]; exact b63_430
    clear b63_430 w63_42c w63_428 w63_424 w63_420 w63_38c w63_388 w63_384 w63_380 w63_15c w63_158 w63_154 w63_150 w63_a4 w63_a0 w63_9c w63_98 w63_94 w63_90 w63_8c w63_88 w63_84 w63_80 w63_7c w63_78 w63_74 w63_70 w63_6c w63_68 w63_64 w63_60 w63_5c w63_58 w63_54 w63_50 w63_4c w63_48 w63_44 w63_38 w63_34 w63_30 w63_2c g63_27 g63_26 g63_25 g63_24 g63_23 g63_22 g63_21 g63_20 g63_19 g63_18 g63_12 g63_11 g63_10 g63_9 g63_8 g63_4 g63_3 g63_2 V63 E63 fR63 t63 fr63 m63 s63 u63 d63
    -- 0x942: sw
    obtain ⟨n65, d65, s65, fr65, K65, W65, rg65⟩ := sv_sw F E64 s64 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g64_2]; sv_addr) (by decide) (by decide)
    have t65 : Steps n0 n65 := t64.trans d65
    have fR65 : ∀ x, SvR B x → n65.mem x = M0 x := fun x hx => (fr65 x hx).trans (fR64 x hx)
    have E65 : SvCode n65.mem := E64.fr F fr65
    have V65 : SvSaves B n65.mem v := V64.keep K65 (by decide)
    have g65_2 : reg n65 sp = B + 0x21A0 := by rw [rg65 sp, g64_2]
    have g65_3 : reg n65 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg65 (3 : Fin 32), g64_3]
    have g65_4 : reg n65 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg65 (4 : Fin 32), g64_4]
    have g65_8 : reg n65 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg65 (8 : Fin 32), g64_8]
    have g65_9 : reg n65 (9 : Fin 32) = tbp := by rw [rg65 (9 : Fin 32), g64_9]
    have g65_10 : reg n65 a0 = BitVec.ofNat 32 0x1 := by rw [rg65 a0, g64_10]
    have g65_11 : reg n65 a1 = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [rg65 a1, g64_11]
    have g65_12 : reg n65 a2 = BitVec.ofNat 32 0xC := by rw [rg65 a2, g64_12]
    have g65_18 : reg n65 (18 : Fin 32) = out := by rw [rg65 (18 : Fin 32), g64_18]
    have g65_19 : reg n65 (19 : Fin 32) = bp := by rw [rg65 (19 : Fin 32), g64_19]
    have g65_20 : reg n65 (20 : Fin 32) = dg := by rw [rg65 (20 : Fin 32), g64_20]
    have g65_21 : reg n65 (21 : Fin 32) = rootp := by rw [rg65 (21 : Fin 32), g64_21]
    have g65_22 : reg n65 (22 : Fin 32) = ll := by rw [rg65 (22 : Fin 32), g64_22]
    have g65_23 : reg n65 (23 : Fin 32) = sgp := by rw [rg65 (23 : Fin 32), g64_23]
    have g65_24 : reg n65 (24 : Fin 32) = kp := by rw [rg65 (24 : Fin 32), g64_24]
    have g65_25 : reg n65 (25 : Fin 32) = sgl := by rw [rg65 (25 : Fin 32), g64_25]
    have g65_26 : reg n65 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rg65 (26 : Fin 32), g64_26]
    have g65_27 : reg n65 (27 : Fin 32) = tbl := by rw [rg65 (27 : Fin 32), g64_27]
    have keep_kk65 : SvKeepL B n0.mem n65.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := keep_kk64.trans K65.toL
    clear keep_kk64
    have w65_2c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K65.w32 (by decide) (by decide)).trans w64_2c
    have w65_30 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K65.w32 (by decide) (by decide)).trans w64_30
    have w65_34 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K65.w32 (by decide) (by decide)).trans w64_34
    have w65_38 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K65.w32 (by decide) (by decide)).trans w64_38
    have w65_48 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K65.w32 (by decide) (by decide)).trans w64_48
    have w65_4c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K65.w32 (by decide) (by decide)).trans w64_4c
    have w65_50 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K65.w32 (by decide) (by decide)).trans w64_50
    have w65_54 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K65.w32 (by decide) (by decide)).trans w64_54
    have w65_58 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K65.w32 (by decide) (by decide)).trans w64_58
    have w65_5c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K65.w32 (by decide) (by decide)).trans w64_5c
    have w65_60 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K65.w32 (by decide) (by decide)).trans w64_60
    have w65_64 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K65.w32 (by decide) (by decide)).trans w64_64
    have w65_68 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K65.w32 (by decide) (by decide)).trans w64_68
    have w65_6c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K65.w32 (by decide) (by decide)).trans w64_6c
    have w65_70 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K65.w32 (by decide) (by decide)).trans w64_70
    have w65_74 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K65.w32 (by decide) (by decide)).trans w64_74
    have w65_78 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K65.w32 (by decide) (by decide)).trans w64_78
    have w65_7c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K65.w32 (by decide) (by decide)).trans w64_7c
    have w65_80 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K65.w32 (by decide) (by decide)).trans w64_80
    have w65_84 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K65.w32 (by decide) (by decide)).trans w64_84
    have w65_88 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K65.w32 (by decide) (by decide)).trans w64_88
    have w65_8c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K65.w32 (by decide) (by decide)).trans w64_8c
    have w65_90 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K65.w32 (by decide) (by decide)).trans w64_90
    have w65_94 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K65.w32 (by decide) (by decide)).trans w64_94
    have w65_98 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K65.w32 (by decide) (by decide)).trans w64_98
    have w65_9c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K65.w32 (by decide) (by decide)).trans w64_9c
    have w65_a0 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K65.w32 (by decide) (by decide)).trans w64_a0
    have w65_a4 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K65.w32 (by decide) (by decide)).trans w64_a4
    have w65_150 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K65.w32 (by decide) (by decide)).trans w64_150
    have w65_154 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K65.w32 (by decide) (by decide)).trans w64_154
    have w65_158 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K65.w32 (by decide) (by decide)).trans w64_158
    have w65_15c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K65.w32 (by decide) (by decide)).trans w64_15c
    have w65_380 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K65.w32 (by decide) (by decide)).trans w64_380
    have w65_384 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K65.w32 (by decide) (by decide)).trans w64_384
    have w65_388 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := (K65.w32 (by decide) (by decide)).trans w64_388
    have w65_38c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := (K65.w32 (by decide) (by decide)).trans w64_38c
    have w65_420 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := (K65.w32 (by decide) (by decide)).trans w64_420
    have w65_424 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := (K65.w32 (by decide) (by decide)).trans w64_424
    have w65_428 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K65.w32 (by decide) (by decide)).trans w64_428
    have w65_42c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := (K65.w32 (by decide) (by decide)).trans w64_42c
    have b65_430 : n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := (K65.b8 (by decide) (by decide)).trans b64_430
    have w65_44 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [W65, g64_10]
    clear b64_430 w64_42c w64_428 w64_424 w64_420 w64_38c w64_388 w64_384 w64_380 w64_15c w64_158 w64_154 w64_150 w64_a4 w64_a0 w64_9c w64_98 w64_94 w64_90 w64_8c w64_88 w64_84 w64_80 w64_7c w64_78 w64_74 w64_70 w64_6c w64_68 w64_64 w64_60 w64_5c w64_58 w64_54 w64_50 w64_4c w64_48 w64_44 w64_38 w64_34 w64_30 w64_2c g64_10 g64_27 g64_26 g64_25 g64_24 g64_23 g64_22 g64_21 g64_20 g64_19 g64_18 g64_12 g64_11 g64_9 g64_8 g64_4 g64_3 g64_2 V64 E64 fR64 t64 fr64 rb64 s64 m64 u64 c64
    -- 0x944: lw
    obtain ⟨n66, d66, u66⟩ := s65.lw E65.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g65_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s66 : St n66.mem SV n66 0x946 (reg n66) := ⟨u66.pc, rfl, fun _ => rfl⟩
    have m66 : n66.mem = n65.mem := u66.mem
    have fr66 : ∀ x, SvR B x → n66.mem x = n65.mem x := fun x _ => by rw [m66]
    have t66 : Steps n0 n66 := t65.trans (.single d66)
    have fR66 : ∀ x, SvR B x → n66.mem x = M0 x := fun x hx => (fr66 x hx).trans (fR65 x hx)
    have E66 : SvCode n66.mem := E65.fr F fr66
    have V66 : SvSaves B n66.mem v := V65.same m66
    have g66_2 : reg n66 sp = B + 0x21A0 := by rw [u66.regs, upd_ne (by decide) (by decide), g65_2]
    have g66_3 : reg n66 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u66.regs, upd_ne (by decide) (by decide), g65_3]
    have g66_4 : reg n66 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u66.regs, upd_ne (by decide) (by decide), g65_4]
    have g66_9 : reg n66 (9 : Fin 32) = tbp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_9]
    have g66_10 : reg n66 a0 = BitVec.ofNat 32 0x1 := by rw [u66.regs, upd_ne (by decide) (by decide), g65_10]
    have g66_11 : reg n66 a1 = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [u66.regs, upd_ne (by decide) (by decide), g65_11]
    have g66_12 : reg n66 a2 = BitVec.ofNat 32 0xC := by rw [u66.regs, upd_ne (by decide) (by decide), g65_12]
    have g66_18 : reg n66 (18 : Fin 32) = out := by rw [u66.regs, upd_ne (by decide) (by decide), g65_18]
    have g66_19 : reg n66 (19 : Fin 32) = bp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_19]
    have g66_20 : reg n66 (20 : Fin 32) = dg := by rw [u66.regs, upd_ne (by decide) (by decide), g65_20]
    have g66_21 : reg n66 (21 : Fin 32) = rootp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_21]
    have g66_22 : reg n66 (22 : Fin 32) = ll := by rw [u66.regs, upd_ne (by decide) (by decide), g65_22]
    have g66_23 : reg n66 (23 : Fin 32) = sgp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_23]
    have g66_24 : reg n66 (24 : Fin 32) = kp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_24]
    have g66_25 : reg n66 (25 : Fin 32) = sgl := by rw [u66.regs, upd_ne (by decide) (by decide), g65_25]
    have g66_26 : reg n66 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u66.regs, upd_ne (by decide) (by decide), g65_26]
    have g66_27 : reg n66 (27 : Fin 32) = tbl := by rw [u66.regs, upd_ne (by decide) (by decide), g65_27]
    have g66_8 : reg n66 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [u66.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g65_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w65_44]
    have keep_kk66 : SvKeepL B n0.mem n66.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m66]; exact keep_kk65
    clear keep_kk65
    have w66_2c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m66]; exact w65_2c
    have w66_30 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m66]; exact w65_30
    have w66_34 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m66]; exact w65_34
    have w66_38 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m66]; exact w65_38
    have w66_44 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m66]; exact w65_44
    have w66_48 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m66]; exact w65_48
    have w66_4c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m66]; exact w65_4c
    have w66_50 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m66]; exact w65_50
    have w66_54 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m66]; exact w65_54
    have w66_58 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m66]; exact w65_58
    have w66_5c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m66]; exact w65_5c
    have w66_60 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m66]; exact w65_60
    have w66_64 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m66]; exact w65_64
    have w66_68 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m66]; exact w65_68
    have w66_6c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m66]; exact w65_6c
    have w66_70 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m66]; exact w65_70
    have w66_74 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m66]; exact w65_74
    have w66_78 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m66]; exact w65_78
    have w66_7c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m66]; exact w65_7c
    have w66_80 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m66]; exact w65_80
    have w66_84 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m66]; exact w65_84
    have w66_88 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m66]; exact w65_88
    have w66_8c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m66]; exact w65_8c
    have w66_90 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m66]; exact w65_90
    have w66_94 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m66]; exact w65_94
    have w66_98 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m66]; exact w65_98
    have w66_9c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m66]; exact w65_9c
    have w66_a0 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m66]; exact w65_a0
    have w66_a4 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m66]; exact w65_a4
    have w66_150 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m66]; exact w65_150
    have w66_154 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m66]; exact w65_154
    have w66_158 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m66]; exact w65_158
    have w66_15c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m66]; exact w65_15c
    have w66_380 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m66]; exact w65_380
    have w66_384 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m66]; exact w65_384
    have w66_388 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m66]; exact w65_388
    have w66_38c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m66]; exact w65_38c
    have w66_420 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m66]; exact w65_420
    have w66_424 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m66]; exact w65_424
    have w66_428 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m66]; exact w65_428
    have w66_42c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m66]; exact w65_42c
    have b66_430 : n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m66]; exact b65_430
    clear w65_44 b65_430 w65_42c w65_428 w65_424 w65_420 w65_38c w65_388 w65_384 w65_380 w65_15c w65_158 w65_154 w65_150 w65_a4 w65_a0 w65_9c w65_98 w65_94 w65_90 w65_8c w65_88 w65_84 w65_80 w65_7c w65_78 w65_74 w65_70 w65_6c w65_68 w65_64 w65_60 w65_5c w65_58 w65_54 w65_50 w65_4c w65_48 w65_38 w65_34 w65_30 w65_2c g65_27 g65_26 g65_25 g65_24 g65_23 g65_22 g65_21 g65_20 g65_19 g65_18 g65_12 g65_11 g65_10 g65_9 g65_8 g65_4 g65_3 g65_2 V65 E65 fR65 t65 rg65 W65 K65 fr65 s65 d65
    -- 0x946: j
    obtain ⟨n67, d67, u67⟩ := s66.jump E66.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s66.pc]; decide)
    have s67 : St n67.mem SV n67 0x7A4 (reg n67) := ⟨u67.pc, rfl, fun _ => rfl⟩
    have m67 : n67.mem = n66.mem := u67.mem
    have fr67 : ∀ x, SvR B x → n67.mem x = n66.mem x := fun x _ => by rw [m67]
    have t67 : Steps n0 n67 := t66.trans (.single d67)
    have fR67 : ∀ x, SvR B x → n67.mem x = M0 x := fun x hx => (fr67 x hx).trans (fR66 x hx)
    have E67 : SvCode n67.mem := E66.fr F fr67
    have V67 : SvSaves B n67.mem v := V66.same m67
    have g67_2 : reg n67 sp = B + 0x21A0 := by rw [u67.regs, g66_2]
    have g67_3 : reg n67 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u67.regs, g66_3]
    have g67_4 : reg n67 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u67.regs, g66_4]
    have g67_8 : reg n67 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u67.regs, g66_8]
    have g67_9 : reg n67 (9 : Fin 32) = tbp := by rw [u67.regs, g66_9]
    have g67_10 : reg n67 a0 = BitVec.ofNat 32 0x1 := by rw [u67.regs, g66_10]
    have g67_11 : reg n67 a1 = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [u67.regs, g66_11]
    have g67_12 : reg n67 a2 = BitVec.ofNat 32 0xC := by rw [u67.regs, g66_12]
    have g67_18 : reg n67 (18 : Fin 32) = out := by rw [u67.regs, g66_18]
    have g67_19 : reg n67 (19 : Fin 32) = bp := by rw [u67.regs, g66_19]
    have g67_20 : reg n67 (20 : Fin 32) = dg := by rw [u67.regs, g66_20]
    have g67_21 : reg n67 (21 : Fin 32) = rootp := by rw [u67.regs, g66_21]
    have g67_22 : reg n67 (22 : Fin 32) = ll := by rw [u67.regs, g66_22]
    have g67_23 : reg n67 (23 : Fin 32) = sgp := by rw [u67.regs, g66_23]
    have g67_24 : reg n67 (24 : Fin 32) = kp := by rw [u67.regs, g66_24]
    have g67_25 : reg n67 (25 : Fin 32) = sgl := by rw [u67.regs, g66_25]
    have g67_26 : reg n67 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u67.regs, g66_26]
    have g67_27 : reg n67 (27 : Fin 32) = tbl := by rw [u67.regs, g66_27]
    have keep_kk67 : SvKeepL B n0.mem n67.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m67]; exact keep_kk66
    clear keep_kk66
    have w67_2c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m67]; exact w66_2c
    have w67_30 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m67]; exact w66_30
    have w67_34 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m67]; exact w66_34
    have w67_38 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m67]; exact w66_38
    have w67_44 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m67]; exact w66_44
    have w67_48 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m67]; exact w66_48
    have w67_4c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m67]; exact w66_4c
    have w67_50 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m67]; exact w66_50
    have w67_54 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m67]; exact w66_54
    have w67_58 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m67]; exact w66_58
    have w67_5c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m67]; exact w66_5c
    have w67_60 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m67]; exact w66_60
    have w67_64 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m67]; exact w66_64
    have w67_68 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m67]; exact w66_68
    have w67_6c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m67]; exact w66_6c
    have w67_70 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m67]; exact w66_70
    have w67_74 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m67]; exact w66_74
    have w67_78 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m67]; exact w66_78
    have w67_7c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m67]; exact w66_7c
    have w67_80 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m67]; exact w66_80
    have w67_84 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m67]; exact w66_84
    have w67_88 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m67]; exact w66_88
    have w67_8c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m67]; exact w66_8c
    have w67_90 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m67]; exact w66_90
    have w67_94 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m67]; exact w66_94
    have w67_98 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m67]; exact w66_98
    have w67_9c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m67]; exact w66_9c
    have w67_a0 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m67]; exact w66_a0
    have w67_a4 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m67]; exact w66_a4
    have w67_150 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m67]; exact w66_150
    have w67_154 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m67]; exact w66_154
    have w67_158 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m67]; exact w66_158
    have w67_15c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m67]; exact w66_15c
    have w67_380 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m67]; exact w66_380
    have w67_384 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m67]; exact w66_384
    have w67_388 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m67]; exact w66_388
    have w67_38c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m67]; exact w66_38c
    have w67_420 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m67]; exact w66_420
    have w67_424 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m67]; exact w66_424
    have w67_428 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m67]; exact w66_428
    have w67_42c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m67]; exact w66_42c
    have b67_430 : n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m67]; exact b66_430
    clear b66_430 w66_42c w66_428 w66_424 w66_420 w66_38c w66_388 w66_384 w66_380 w66_15c w66_158 w66_154 w66_150 w66_a4 w66_a0 w66_9c w66_98 w66_94 w66_90 w66_8c w66_88 w66_84 w66_80 w66_7c w66_78 w66_74 w66_70 w66_6c w66_68 w66_64 w66_60 w66_5c w66_58 w66_54 w66_50 w66_4c w66_48 w66_44 w66_38 w66_34 w66_30 w66_2c g66_8 g66_27 g66_26 g66_25 g66_24 g66_23 g66_22 g66_21 g66_20 g66_19 g66_18 g66_12 g66_11 g66_10 g66_9 g66_4 g66_3 g66_2 V66 E66 fR66 t66 fr66 m66 s66 u66 d66
    exact .inl ⟨(fun ⟨tl56', h0', h1', h2', _⟩ => by rw [hr56] at h0'; cases h0'; exact hz_62 h2'), sv_fail F E67 s67 t67 (fun x hx => (fR67 x hx).trans (fM x hx).symm) V67 hret g67_2 g67_18 hO g67_3 g67_4 (by rw [g67_8]; sv_code)⟩
  -- 0x752: branch, not taken
  obtain ⟨n63, d63, u63⟩ := s62.notTaken E62.self 0x756 sv_at_752
    (by decide) (by rw [g62_11, s62.zero]; exact br_bne_f hz_62)
  have s63 : St n63.mem SV n63 0x756 (reg n63) := ⟨u63.pc, rfl, fun _ => rfl⟩
  have m63 : n63.mem = n62.mem := u63.mem
  have fr63 : ∀ x, SvR B x → n63.mem x = n62.mem x := fun x _ => by rw [m63]
  have t63 : Steps n0 n63 := t62.trans (.single d63)
  have fR63 : ∀ x, SvR B x → n63.mem x = M0 x := fun x hx => (fr63 x hx).trans (fR62 x hx)
  have E63 : SvCode n63.mem := E62.fr F fr63
  have V63 : SvSaves B n63.mem v := V62.same m63
  have g63_2 : reg n63 sp = B + 0x21A0 := by rw [u63.regs, g62_2]
  have g63_3 : reg n63 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u63.regs, g62_3]
  have g63_4 : reg n63 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u63.regs, g62_4]
  have g63_8 : reg n63 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u63.regs, g62_8]
  have g63_9 : reg n63 (9 : Fin 32) = tbp := by rw [u63.regs, g62_9]
  have g63_10 : reg n63 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u63.regs, g62_10]
  have g63_11 : reg n63 a1 = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [u63.regs, g62_11]
  have g63_12 : reg n63 a2 = BitVec.ofNat 32 0xC := by rw [u63.regs, g62_12]
  have g63_18 : reg n63 (18 : Fin 32) = out := by rw [u63.regs, g62_18]
  have g63_19 : reg n63 (19 : Fin 32) = bp := by rw [u63.regs, g62_19]
  have g63_20 : reg n63 (20 : Fin 32) = dg := by rw [u63.regs, g62_20]
  have g63_21 : reg n63 (21 : Fin 32) = rootp := by rw [u63.regs, g62_21]
  have g63_22 : reg n63 (22 : Fin 32) = ll := by rw [u63.regs, g62_22]
  have g63_23 : reg n63 (23 : Fin 32) = sgp := by rw [u63.regs, g62_23]
  have g63_24 : reg n63 (24 : Fin 32) = kp := by rw [u63.regs, g62_24]
  have g63_25 : reg n63 (25 : Fin 32) = sgl := by rw [u63.regs, g62_25]
  have g63_26 : reg n63 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u63.regs, g62_26]
  have g63_27 : reg n63 (27 : Fin 32) = tbl := by rw [u63.regs, g62_27]
  have keep_kk63 : SvKeepL B n0.mem n63.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m63]; exact keep_kk62
  clear keep_kk62
  have w63_2c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m63]; exact w62_2c
  have w63_30 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m63]; exact w62_30
  have w63_34 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m63]; exact w62_34
  have w63_38 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m63]; exact w62_38
  have w63_44 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m63]; exact w62_44
  have w63_48 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m63]; exact w62_48
  have w63_4c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m63]; exact w62_4c
  have w63_50 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m63]; exact w62_50
  have w63_54 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m63]; exact w62_54
  have w63_58 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m63]; exact w62_58
  have w63_5c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m63]; exact w62_5c
  have w63_60 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m63]; exact w62_60
  have w63_64 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m63]; exact w62_64
  have w63_68 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m63]; exact w62_68
  have w63_6c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m63]; exact w62_6c
  have w63_70 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m63]; exact w62_70
  have w63_74 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m63]; exact w62_74
  have w63_78 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m63]; exact w62_78
  have w63_7c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m63]; exact w62_7c
  have w63_80 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m63]; exact w62_80
  have w63_84 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m63]; exact w62_84
  have w63_88 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m63]; exact w62_88
  have w63_8c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m63]; exact w62_8c
  have w63_90 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m63]; exact w62_90
  have w63_94 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m63]; exact w62_94
  have w63_98 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m63]; exact w62_98
  have w63_9c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m63]; exact w62_9c
  have w63_a0 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m63]; exact w62_a0
  have w63_a4 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m63]; exact w62_a4
  have w63_150 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m63]; exact w62_150
  have w63_154 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m63]; exact w62_154
  have w63_158 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m63]; exact w62_158
  have w63_15c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m63]; exact w62_15c
  have w63_380 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m63]; exact w62_380
  have w63_384 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m63]; exact w62_384
  have w63_388 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m63]; exact w62_388
  have w63_38c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m63]; exact w62_38c
  have w63_420 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m63]; exact w62_420
  have w63_424 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m63]; exact w62_424
  have w63_428 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m63]; exact w62_428
  have w63_42c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m63]; exact w62_42c
  have b63_430 : n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m63]; exact b62_430
  clear b62_430 w62_42c w62_428 w62_424 w62_420 w62_38c w62_388 w62_384 w62_380 w62_15c w62_158 w62_154 w62_150 w62_a4 w62_a0 w62_9c w62_98 w62_94 w62_90 w62_8c w62_88 w62_84 w62_80 w62_7c w62_78 w62_74 w62_70 w62_6c w62_68 w62_64 w62_60 w62_5c w62_58 w62_54 w62_50 w62_4c w62_48 w62_44 w62_38 w62_34 w62_30 w62_2c g62_11 g62_27 g62_26 g62_25 g62_24 g62_23 g62_22 g62_21 g62_20 g62_19 g62_18 g62_12 g62_10 g62_9 g62_8 g62_4 g62_3 g62_2 V62 E62 fR62 t62 fr62 m62 s62 u62 d62
  -- 0x756: lw
  obtain ⟨n64, d64, u64⟩ := s63.lw E63.self sv_at_756 (off' := 0x75A) (by decide)
    (by rw [g63_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s64 : St n64.mem SV n64 0x75A (reg n64) := ⟨u64.pc, rfl, fun _ => rfl⟩
  have m64 : n64.mem = n63.mem := u64.mem
  have fr64 : ∀ x, SvR B x → n64.mem x = n63.mem x := fun x _ => by rw [m64]
  have t64 : Steps n0 n64 := t63.trans (.single d64)
  have fR64 : ∀ x, SvR B x → n64.mem x = M0 x := fun x hx => (fr64 x hx).trans (fR63 x hx)
  have E64 : SvCode n64.mem := E63.fr F fr64
  have V64 : SvSaves B n64.mem v := V63.same m64
  have g64_2 : reg n64 sp = B + 0x21A0 := by rw [u64.regs, upd_ne (by decide) (by decide), g63_2]
  have g64_3 : reg n64 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u64.regs, upd_ne (by decide) (by decide), g63_3]
  have g64_4 : reg n64 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u64.regs, upd_ne (by decide) (by decide), g63_4]
  have g64_8 : reg n64 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u64.regs, upd_ne (by decide) (by decide), g63_8]
  have g64_9 : reg n64 (9 : Fin 32) = tbp := by rw [u64.regs, upd_ne (by decide) (by decide), g63_9]
  have g64_10 : reg n64 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u64.regs, upd_ne (by decide) (by decide), g63_10]
  have g64_12 : reg n64 a2 = BitVec.ofNat 32 0xC := by rw [u64.regs, upd_ne (by decide) (by decide), g63_12]
  have g64_18 : reg n64 (18 : Fin 32) = out := by rw [u64.regs, upd_ne (by decide) (by decide), g63_18]
  have g64_19 : reg n64 (19 : Fin 32) = bp := by rw [u64.regs, upd_ne (by decide) (by decide), g63_19]
  have g64_20 : reg n64 (20 : Fin 32) = dg := by rw [u64.regs, upd_ne (by decide) (by decide), g63_20]
  have g64_21 : reg n64 (21 : Fin 32) = rootp := by rw [u64.regs, upd_ne (by decide) (by decide), g63_21]
  have g64_22 : reg n64 (22 : Fin 32) = ll := by rw [u64.regs, upd_ne (by decide) (by decide), g63_22]
  have g64_23 : reg n64 (23 : Fin 32) = sgp := by rw [u64.regs, upd_ne (by decide) (by decide), g63_23]
  have g64_24 : reg n64 (24 : Fin 32) = kp := by rw [u64.regs, upd_ne (by decide) (by decide), g63_24]
  have g64_25 : reg n64 (25 : Fin 32) = sgl := by rw [u64.regs, upd_ne (by decide) (by decide), g63_25]
  have g64_26 : reg n64 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u64.regs, upd_ne (by decide) (by decide), g63_26]
  have g64_27 : reg n64 (27 : Fin 32) = tbl := by rw [u64.regs, upd_ne (by decide) (by decide), g63_27]
  have g64_11 : reg n64 a1 = BitVec.ofNat 32 tl56.len := by
    rw [u64.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g63_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w63_424]
  have keep_kk64 : SvKeepL B n0.mem n64.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m64]; exact keep_kk63
  clear keep_kk63
  have w64_2c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m64]; exact w63_2c
  have w64_30 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m64]; exact w63_30
  have w64_34 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m64]; exact w63_34
  have w64_38 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m64]; exact w63_38
  have w64_44 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m64]; exact w63_44
  have w64_48 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m64]; exact w63_48
  have w64_4c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m64]; exact w63_4c
  have w64_50 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m64]; exact w63_50
  have w64_54 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m64]; exact w63_54
  have w64_58 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m64]; exact w63_58
  have w64_5c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m64]; exact w63_5c
  have w64_60 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m64]; exact w63_60
  have w64_64 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m64]; exact w63_64
  have w64_68 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m64]; exact w63_68
  have w64_6c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m64]; exact w63_6c
  have w64_70 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m64]; exact w63_70
  have w64_74 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m64]; exact w63_74
  have w64_78 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m64]; exact w63_78
  have w64_7c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m64]; exact w63_7c
  have w64_80 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m64]; exact w63_80
  have w64_84 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m64]; exact w63_84
  have w64_88 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m64]; exact w63_88
  have w64_8c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m64]; exact w63_8c
  have w64_90 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m64]; exact w63_90
  have w64_94 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m64]; exact w63_94
  have w64_98 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m64]; exact w63_98
  have w64_9c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m64]; exact w63_9c
  have w64_a0 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m64]; exact w63_a0
  have w64_a4 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m64]; exact w63_a4
  have w64_150 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m64]; exact w63_150
  have w64_154 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m64]; exact w63_154
  have w64_158 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m64]; exact w63_158
  have w64_15c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m64]; exact w63_15c
  have w64_380 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m64]; exact w63_380
  have w64_384 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m64]; exact w63_384
  have w64_388 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m64]; exact w63_388
  have w64_38c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m64]; exact w63_38c
  have w64_420 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m64]; exact w63_420
  have w64_424 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m64]; exact w63_424
  have w64_428 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m64]; exact w63_428
  have w64_42c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m64]; exact w63_42c
  have b64_430 : n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m64]; exact b63_430
  clear b63_430 w63_42c w63_428 w63_424 w63_420 w63_38c w63_388 w63_384 w63_380 w63_15c w63_158 w63_154 w63_150 w63_a4 w63_a0 w63_9c w63_98 w63_94 w63_90 w63_8c w63_88 w63_84 w63_80 w63_7c w63_78 w63_74 w63_70 w63_6c w63_68 w63_64 w63_60 w63_5c w63_58 w63_54 w63_50 w63_4c w63_48 w63_44 w63_38 w63_34 w63_30 w63_2c g63_27 g63_26 g63_25 g63_24 g63_23 g63_22 g63_21 g63_20 g63_19 g63_18 g63_12 g63_11 g63_10 g63_9 g63_8 g63_4 g63_3 g63_2 V63 E63 fR63 t63 fr63 m63 s63 u63 d63
  -- 0x75A: lw
  obtain ⟨n65, d65, u65⟩ := s64.lw E64.self sv_at_75a (off' := 0x75C) (by decide)
    (by rw [g64_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s65 : St n65.mem SV n65 0x75C (reg n65) := ⟨u65.pc, rfl, fun _ => rfl⟩
  have m65 : n65.mem = n64.mem := u65.mem
  have fr65 : ∀ x, SvR B x → n65.mem x = n64.mem x := fun x _ => by rw [m65]
  have t65 : Steps n0 n65 := t64.trans (.single d65)
  have fR65 : ∀ x, SvR B x → n65.mem x = M0 x := fun x hx => (fr65 x hx).trans (fR64 x hx)
  have E65 : SvCode n65.mem := E64.fr F fr65
  have V65 : SvSaves B n65.mem v := V64.same m65
  have g65_2 : reg n65 sp = B + 0x21A0 := by rw [u65.regs, upd_ne (by decide) (by decide), g64_2]
  have g65_3 : reg n65 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u65.regs, upd_ne (by decide) (by decide), g64_3]
  have g65_4 : reg n65 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u65.regs, upd_ne (by decide) (by decide), g64_4]
  have g65_8 : reg n65 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u65.regs, upd_ne (by decide) (by decide), g64_8]
  have g65_9 : reg n65 (9 : Fin 32) = tbp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_9]
  have g65_10 : reg n65 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u65.regs, upd_ne (by decide) (by decide), g64_10]
  have g65_11 : reg n65 a1 = BitVec.ofNat 32 tl56.len := by rw [u65.regs, upd_ne (by decide) (by decide), g64_11]
  have g65_12 : reg n65 a2 = BitVec.ofNat 32 0xC := by rw [u65.regs, upd_ne (by decide) (by decide), g64_12]
  have g65_18 : reg n65 (18 : Fin 32) = out := by rw [u65.regs, upd_ne (by decide) (by decide), g64_18]
  have g65_19 : reg n65 (19 : Fin 32) = bp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_19]
  have g65_20 : reg n65 (20 : Fin 32) = dg := by rw [u65.regs, upd_ne (by decide) (by decide), g64_20]
  have g65_21 : reg n65 (21 : Fin 32) = rootp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_21]
  have g65_22 : reg n65 (22 : Fin 32) = ll := by rw [u65.regs, upd_ne (by decide) (by decide), g64_22]
  have g65_23 : reg n65 (23 : Fin 32) = sgp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_23]
  have g65_24 : reg n65 (24 : Fin 32) = kp := by rw [u65.regs, upd_ne (by decide) (by decide), g64_24]
  have g65_25 : reg n65 (25 : Fin 32) = sgl := by rw [u65.regs, upd_ne (by decide) (by decide), g64_25]
  have g65_27 : reg n65 (27 : Fin 32) = tbl := by rw [u65.regs, upd_ne (by decide) (by decide), g64_27]
  have g65_26 : reg n65 (26 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [u65.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g64_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w64_50]
  have keep_kk65 : SvKeepL B n0.mem n65.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m65]; exact keep_kk64
  clear keep_kk64
  have w65_2c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m65]; exact w64_2c
  have w65_30 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m65]; exact w64_30
  have w65_34 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m65]; exact w64_34
  have w65_38 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m65]; exact w64_38
  have w65_44 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m65]; exact w64_44
  have w65_48 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m65]; exact w64_48
  have w65_4c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m65]; exact w64_4c
  have w65_50 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m65]; exact w64_50
  have w65_54 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m65]; exact w64_54
  have w65_58 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m65]; exact w64_58
  have w65_5c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m65]; exact w64_5c
  have w65_60 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m65]; exact w64_60
  have w65_64 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m65]; exact w64_64
  have w65_68 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m65]; exact w64_68
  have w65_6c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m65]; exact w64_6c
  have w65_70 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m65]; exact w64_70
  have w65_74 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m65]; exact w64_74
  have w65_78 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m65]; exact w64_78
  have w65_7c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m65]; exact w64_7c
  have w65_80 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m65]; exact w64_80
  have w65_84 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m65]; exact w64_84
  have w65_88 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m65]; exact w64_88
  have w65_8c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m65]; exact w64_8c
  have w65_90 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m65]; exact w64_90
  have w65_94 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m65]; exact w64_94
  have w65_98 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m65]; exact w64_98
  have w65_9c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m65]; exact w64_9c
  have w65_a0 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m65]; exact w64_a0
  have w65_a4 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m65]; exact w64_a4
  have w65_150 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m65]; exact w64_150
  have w65_154 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m65]; exact w64_154
  have w65_158 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m65]; exact w64_158
  have w65_15c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m65]; exact w64_15c
  have w65_380 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m65]; exact w64_380
  have w65_384 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m65]; exact w64_384
  have w65_388 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m65]; exact w64_388
  have w65_38c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m65]; exact w64_38c
  have w65_420 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m65]; exact w64_420
  have w65_424 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m65]; exact w64_424
  have w65_428 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m65]; exact w64_428
  have w65_42c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m65]; exact w64_42c
  have b65_430 : n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m65]; exact b64_430
  clear b64_430 w64_42c w64_428 w64_424 w64_420 w64_38c w64_388 w64_384 w64_380 w64_15c w64_158 w64_154 w64_150 w64_a4 w64_a0 w64_9c w64_98 w64_94 w64_90 w64_8c w64_88 w64_84 w64_80 w64_7c w64_78 w64_74 w64_70 w64_6c w64_68 w64_64 w64_60 w64_5c w64_58 w64_54 w64_50 w64_4c w64_48 w64_44 w64_38 w64_34 w64_30 w64_2c g64_11 g64_27 g64_26 g64_25 g64_24 g64_23 g64_22 g64_21 g64_20 g64_19 g64_18 g64_12 g64_10 g64_9 g64_8 g64_4 g64_3 g64_2 V64 E64 fR64 t64 fr64 m64 s64 u64 d64
  -- 0x75C
  obtain ⟨n66, c66, u66⟩ := s65.block svDp175c E65.self svDp175c_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m66 : n66.mem = n65.mem := u66.mem
  have s66 : St n66.mem SV n66 0x764 (reg n66) := ⟨u66.pc, rfl, fun _ => rfl⟩
  have rb66 : ∀ q, reg n66 q = (runBlock svDp175c (n65.mem, reg n65)).2 q := fun q => by rw [u66.regs]
  have fr66 : ∀ x, SvR B x → n66.mem x = n65.mem x := fun x _ => by rw [m66]
  have t66 : Steps n0 n66 := t65.trans c66
  have fR66 : ∀ x, SvR B x → n66.mem x = M0 x := fun x hx => (fr66 x hx).trans (fR65 x hx)
  have E66 : SvCode n66.mem := E65.fr F fr66
  have V66 : SvSaves B n66.mem v := V65.same m66
  have g66_2 : reg n66 sp = B + 0x21A0 := by
    rw [rb66, runBlock_reg _ _ _ sp s65.zero (by decide), g65_2]
  have g66_3 : reg n66 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb66, runBlock_reg _ _ _ (3 : Fin 32) s65.zero (by decide), g65_3]
  have g66_4 : reg n66 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb66, runBlock_reg _ _ _ (4 : Fin 32) s65.zero (by decide), g65_4]
  have g66_8 : reg n66 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb66, runBlock_reg _ _ _ (8 : Fin 32) s65.zero (by decide), g65_8]
  have g66_9 : reg n66 (9 : Fin 32) = tbp := by
    rw [rb66, runBlock_reg _ _ _ (9 : Fin 32) s65.zero (by decide), g65_9]
  have g66_10 : reg n66 a0 = (vp) + BitVec.ofNat 32 tl56.header := by
    rw [rb66, runBlock_reg _ _ _ a0 s65.zero (by decide), g65_10]
  have g66_11 : reg n66 a1 = BitVec.ofNat 32 tl56.len := by
    rw [rb66, runBlock_reg _ _ _ a1 s65.zero (by decide), g65_11]
  have g66_18 : reg n66 (18 : Fin 32) = out := by
    rw [rb66, runBlock_reg _ _ _ (18 : Fin 32) s65.zero (by decide), g65_18]
  have g66_19 : reg n66 (19 : Fin 32) = bp := by
    rw [rb66, runBlock_reg _ _ _ (19 : Fin 32) s65.zero (by decide), g65_19]
  have g66_20 : reg n66 (20 : Fin 32) = dg := by
    rw [rb66, runBlock_reg _ _ _ (20 : Fin 32) s65.zero (by decide), g65_20]
  have g66_21 : reg n66 (21 : Fin 32) = rootp := by
    rw [rb66, runBlock_reg _ _ _ (21 : Fin 32) s65.zero (by decide), g65_21]
  have g66_22 : reg n66 (22 : Fin 32) = ll := by
    rw [rb66, runBlock_reg _ _ _ (22 : Fin 32) s65.zero (by decide), g65_22]
  have g66_23 : reg n66 (23 : Fin 32) = sgp := by
    rw [rb66, runBlock_reg _ _ _ (23 : Fin 32) s65.zero (by decide), g65_23]
  have g66_24 : reg n66 (24 : Fin 32) = kp := by
    rw [rb66, runBlock_reg _ _ _ (24 : Fin 32) s65.zero (by decide), g65_24]
  have g66_25 : reg n66 (25 : Fin 32) = sgl := by
    rw [rb66, runBlock_reg _ _ _ (25 : Fin 32) s65.zero (by decide), g65_25]
  have g66_27 : reg n66 (27 : Fin 32) = tbl := by
    rw [rb66, runBlock_reg _ _ _ (27 : Fin 32) s65.zero (by decide), g65_27]
  have g66_12 : reg n66 a2 = B + 0x21A0 + BitVec.ofNat 32 0x88 := by
    rw [rb66]; simp +decide only [runBlock, BInstr.run, svDp175c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g65_2, g65_3, g65_4, g65_8, g65_9, g65_10, g65_11, g65_12, g65_18, g65_19, g65_20, g65_21, g65_22, g65_23, g65_24, g65_25, g65_26, g65_27, s65.zero])
    all_goals (try simp only [BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceHShiftLeft])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g66_26 : reg n66 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x88 := by
    rw [rb66]; simp +decide only [runBlock, BInstr.run, svDp175c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g65_2, g65_3, g65_4, g65_8, g65_9, g65_10, g65_11, g65_12, g65_18, g65_19, g65_20, g65_21, g65_22, g65_23, g65_24, g65_25, g65_26, g65_27, s65.zero])
    all_goals (try simp only [BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceHShiftLeft])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk66 : SvKeepL B n0.mem n66.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m66]; exact keep_kk65
  clear keep_kk65
  have w66_2c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m66]; exact w65_2c
  have w66_30 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m66]; exact w65_30
  have w66_34 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m66]; exact w65_34
  have w66_38 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m66]; exact w65_38
  have w66_44 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m66]; exact w65_44
  have w66_48 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m66]; exact w65_48
  have w66_4c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m66]; exact w65_4c
  have w66_50 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m66]; exact w65_50
  have w66_54 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m66]; exact w65_54
  have w66_58 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m66]; exact w65_58
  have w66_5c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m66]; exact w65_5c
  have w66_60 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m66]; exact w65_60
  have w66_64 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m66]; exact w65_64
  have w66_68 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m66]; exact w65_68
  have w66_6c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m66]; exact w65_6c
  have w66_70 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m66]; exact w65_70
  have w66_74 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m66]; exact w65_74
  have w66_78 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m66]; exact w65_78
  have w66_7c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m66]; exact w65_7c
  have w66_80 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m66]; exact w65_80
  have w66_84 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m66]; exact w65_84
  have w66_88 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m66]; exact w65_88
  have w66_8c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m66]; exact w65_8c
  have w66_90 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m66]; exact w65_90
  have w66_94 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m66]; exact w65_94
  have w66_98 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m66]; exact w65_98
  have w66_9c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m66]; exact w65_9c
  have w66_a0 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m66]; exact w65_a0
  have w66_a4 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m66]; exact w65_a4
  have w66_150 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m66]; exact w65_150
  have w66_154 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m66]; exact w65_154
  have w66_158 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m66]; exact w65_158
  have w66_15c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m66]; exact w65_15c
  have w66_380 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m66]; exact w65_380
  have w66_384 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m66]; exact w65_384
  have w66_388 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m66]; exact w65_388
  have w66_38c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m66]; exact w65_38c
  have w66_420 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m66]; exact w65_420
  have w66_424 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m66]; exact w65_424
  have w66_428 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m66]; exact w65_428
  have w66_42c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m66]; exact w65_42c
  have b66_430 : n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m66]; exact b65_430
  clear b65_430 w65_42c w65_428 w65_424 w65_420 w65_38c w65_388 w65_384 w65_380 w65_15c w65_158 w65_154 w65_150 w65_a4 w65_a0 w65_9c w65_98 w65_94 w65_90 w65_8c w65_88 w65_84 w65_80 w65_7c w65_78 w65_74 w65_70 w65_6c w65_68 w65_64 w65_60 w65_5c w65_58 w65_54 w65_50 w65_4c w65_48 w65_44 w65_38 w65_34 w65_30 w65_2c g65_26 g65_27 g65_25 g65_24 g65_23 g65_22 g65_21 g65_20 g65_19 g65_18 g65_12 g65_11 g65_10 g65_9 g65_8 g65_4 g65_3 g65_2 V65 E65 fR65 t65 fr65 m65 s65 u65 d65
  -- 0x764: sw
  obtain ⟨n67, d67, s67, fr67, K67, W67, rg67⟩ := sv_sw F E66 s66 sv_at_764 (off' := 0x766) (c := 0x88)
    (by decide) (by rw [g66_12]; sv_addr) (by decide) (by decide)
  have t67 : Steps n0 n67 := t66.trans d67
  have fR67 : ∀ x, SvR B x → n67.mem x = M0 x := fun x hx => (fr67 x hx).trans (fR66 x hx)
  have E67 : SvCode n67.mem := E66.fr F fr67
  have V67 : SvSaves B n67.mem v := V66.keep K67 (by decide)
  have g67_2 : reg n67 sp = B + 0x21A0 := by rw [rg67 sp, g66_2]
  have g67_3 : reg n67 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg67 (3 : Fin 32), g66_3]
  have g67_4 : reg n67 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg67 (4 : Fin 32), g66_4]
  have g67_8 : reg n67 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg67 (8 : Fin 32), g66_8]
  have g67_9 : reg n67 (9 : Fin 32) = tbp := by rw [rg67 (9 : Fin 32), g66_9]
  have g67_10 : reg n67 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [rg67 a0, g66_10]
  have g67_11 : reg n67 a1 = BitVec.ofNat 32 tl56.len := by rw [rg67 a1, g66_11]
  have g67_12 : reg n67 a2 = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [rg67 a2, g66_12]
  have g67_18 : reg n67 (18 : Fin 32) = out := by rw [rg67 (18 : Fin 32), g66_18]
  have g67_19 : reg n67 (19 : Fin 32) = bp := by rw [rg67 (19 : Fin 32), g66_19]
  have g67_20 : reg n67 (20 : Fin 32) = dg := by rw [rg67 (20 : Fin 32), g66_20]
  have g67_21 : reg n67 (21 : Fin 32) = rootp := by rw [rg67 (21 : Fin 32), g66_21]
  have g67_22 : reg n67 (22 : Fin 32) = ll := by rw [rg67 (22 : Fin 32), g66_22]
  have g67_23 : reg n67 (23 : Fin 32) = sgp := by rw [rg67 (23 : Fin 32), g66_23]
  have g67_24 : reg n67 (24 : Fin 32) = kp := by rw [rg67 (24 : Fin 32), g66_24]
  have g67_25 : reg n67 (25 : Fin 32) = sgl := by rw [rg67 (25 : Fin 32), g66_25]
  have g67_26 : reg n67 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [rg67 (26 : Fin 32), g66_26]
  have g67_27 : reg n67 (27 : Fin 32) = tbl := by rw [rg67 (27 : Fin 32), g66_27]
  have keep_kk67 : SvKeepL B n0.mem n67.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x88, 0x4)] := keep_kk66.trans K67.toL
  clear keep_kk66
  have w67_2c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K67.w32 (by decide) (by decide)).trans w66_2c
  have w67_30 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K67.w32 (by decide) (by decide)).trans w66_30
  have w67_34 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K67.w32 (by decide) (by decide)).trans w66_34
  have w67_38 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K67.w32 (by decide) (by decide)).trans w66_38
  have w67_44 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K67.w32 (by decide) (by decide)).trans w66_44
  have w67_48 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K67.w32 (by decide) (by decide)).trans w66_48
  have w67_4c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K67.w32 (by decide) (by decide)).trans w66_4c
  have w67_50 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K67.w32 (by decide) (by decide)).trans w66_50
  have w67_54 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K67.w32 (by decide) (by decide)).trans w66_54
  have w67_58 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K67.w32 (by decide) (by decide)).trans w66_58
  have w67_5c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K67.w32 (by decide) (by decide)).trans w66_5c
  have w67_60 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K67.w32 (by decide) (by decide)).trans w66_60
  have w67_64 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K67.w32 (by decide) (by decide)).trans w66_64
  have w67_68 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K67.w32 (by decide) (by decide)).trans w66_68
  have w67_6c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K67.w32 (by decide) (by decide)).trans w66_6c
  have w67_70 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K67.w32 (by decide) (by decide)).trans w66_70
  have w67_74 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K67.w32 (by decide) (by decide)).trans w66_74
  have w67_78 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K67.w32 (by decide) (by decide)).trans w66_78
  have w67_7c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K67.w32 (by decide) (by decide)).trans w66_7c
  have w67_80 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K67.w32 (by decide) (by decide)).trans w66_80
  have w67_84 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K67.w32 (by decide) (by decide)).trans w66_84
  have w67_8c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K67.w32 (by decide) (by decide)).trans w66_8c
  have w67_90 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K67.w32 (by decide) (by decide)).trans w66_90
  have w67_94 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K67.w32 (by decide) (by decide)).trans w66_94
  have w67_98 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K67.w32 (by decide) (by decide)).trans w66_98
  have w67_9c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K67.w32 (by decide) (by decide)).trans w66_9c
  have w67_a0 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K67.w32 (by decide) (by decide)).trans w66_a0
  have w67_a4 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K67.w32 (by decide) (by decide)).trans w66_a4
  have w67_150 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K67.w32 (by decide) (by decide)).trans w66_150
  have w67_154 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K67.w32 (by decide) (by decide)).trans w66_154
  have w67_158 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K67.w32 (by decide) (by decide)).trans w66_158
  have w67_15c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K67.w32 (by decide) (by decide)).trans w66_15c
  have w67_380 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K67.w32 (by decide) (by decide)).trans w66_380
  have w67_384 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K67.w32 (by decide) (by decide)).trans w66_384
  have w67_388 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := (K67.w32 (by decide) (by decide)).trans w66_388
  have w67_38c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := (K67.w32 (by decide) (by decide)).trans w66_38c
  have w67_420 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := (K67.w32 (by decide) (by decide)).trans w66_420
  have w67_424 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := (K67.w32 (by decide) (by decide)).trans w66_424
  have w67_428 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K67.w32 (by decide) (by decide)).trans w66_428
  have w67_42c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := (K67.w32 (by decide) (by decide)).trans w66_42c
  have b67_430 : n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := (K67.b8 (by decide) (by decide)).trans b66_430
  have w67_88 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (vp) + BitVec.ofNat 32 tl56.header := by rw [W67, g66_10]
  clear b66_430 w66_42c w66_428 w66_424 w66_420 w66_38c w66_388 w66_384 w66_380 w66_15c w66_158 w66_154 w66_150 w66_a4 w66_a0 w66_9c w66_98 w66_94 w66_90 w66_8c w66_88 w66_84 w66_80 w66_7c w66_78 w66_74 w66_70 w66_6c w66_68 w66_64 w66_60 w66_5c w66_58 w66_54 w66_50 w66_4c w66_48 w66_44 w66_38 w66_34 w66_30 w66_2c g66_26 g66_12 g66_27 g66_25 g66_24 g66_23 g66_22 g66_21 g66_20 g66_19 g66_18 g66_11 g66_10 g66_9 g66_8 g66_4 g66_3 g66_2 V66 E66 fR66 t66 fr66 rb66 s66 m66 u66 c66
  -- 0x766: sw
  obtain ⟨n68, d68, s68, fr68, K68, W68, rg68⟩ := sv_sw F E67 s67 sv_at_766 (off' := 0x768) (c := 0x8C)
    (by decide) (by rw [g67_12]; sv_addr) (by decide) (by decide)
  have t68 : Steps n0 n68 := t67.trans d68
  have fR68 : ∀ x, SvR B x → n68.mem x = M0 x := fun x hx => (fr68 x hx).trans (fR67 x hx)
  have E68 : SvCode n68.mem := E67.fr F fr68
  have V68 : SvSaves B n68.mem v := V67.keep K68 (by decide)
  have g68_2 : reg n68 sp = B + 0x21A0 := by rw [rg68 sp, g67_2]
  have g68_3 : reg n68 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg68 (3 : Fin 32), g67_3]
  have g68_4 : reg n68 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg68 (4 : Fin 32), g67_4]
  have g68_8 : reg n68 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg68 (8 : Fin 32), g67_8]
  have g68_9 : reg n68 (9 : Fin 32) = tbp := by rw [rg68 (9 : Fin 32), g67_9]
  have g68_10 : reg n68 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [rg68 a0, g67_10]
  have g68_11 : reg n68 a1 = BitVec.ofNat 32 tl56.len := by rw [rg68 a1, g67_11]
  have g68_12 : reg n68 a2 = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [rg68 a2, g67_12]
  have g68_18 : reg n68 (18 : Fin 32) = out := by rw [rg68 (18 : Fin 32), g67_18]
  have g68_19 : reg n68 (19 : Fin 32) = bp := by rw [rg68 (19 : Fin 32), g67_19]
  have g68_20 : reg n68 (20 : Fin 32) = dg := by rw [rg68 (20 : Fin 32), g67_20]
  have g68_21 : reg n68 (21 : Fin 32) = rootp := by rw [rg68 (21 : Fin 32), g67_21]
  have g68_22 : reg n68 (22 : Fin 32) = ll := by rw [rg68 (22 : Fin 32), g67_22]
  have g68_23 : reg n68 (23 : Fin 32) = sgp := by rw [rg68 (23 : Fin 32), g67_23]
  have g68_24 : reg n68 (24 : Fin 32) = kp := by rw [rg68 (24 : Fin 32), g67_24]
  have g68_25 : reg n68 (25 : Fin 32) = sgl := by rw [rg68 (25 : Fin 32), g67_25]
  have g68_26 : reg n68 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [rg68 (26 : Fin 32), g67_26]
  have g68_27 : reg n68 (27 : Fin 32) = tbl := by rw [rg68 (27 : Fin 32), g67_27]
  have keep_kk68 : SvKeepL B n0.mem n68.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x88, 0x4), (0x8C, 0x4)] := keep_kk67.trans K68.toL
  clear keep_kk67
  have w68_2c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K68.w32 (by decide) (by decide)).trans w67_2c
  have w68_30 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K68.w32 (by decide) (by decide)).trans w67_30
  have w68_34 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K68.w32 (by decide) (by decide)).trans w67_34
  have w68_38 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K68.w32 (by decide) (by decide)).trans w67_38
  have w68_44 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K68.w32 (by decide) (by decide)).trans w67_44
  have w68_48 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K68.w32 (by decide) (by decide)).trans w67_48
  have w68_4c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K68.w32 (by decide) (by decide)).trans w67_4c
  have w68_50 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K68.w32 (by decide) (by decide)).trans w67_50
  have w68_54 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K68.w32 (by decide) (by decide)).trans w67_54
  have w68_58 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K68.w32 (by decide) (by decide)).trans w67_58
  have w68_5c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K68.w32 (by decide) (by decide)).trans w67_5c
  have w68_60 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K68.w32 (by decide) (by decide)).trans w67_60
  have w68_64 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K68.w32 (by decide) (by decide)).trans w67_64
  have w68_68 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K68.w32 (by decide) (by decide)).trans w67_68
  have w68_6c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K68.w32 (by decide) (by decide)).trans w67_6c
  have w68_70 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K68.w32 (by decide) (by decide)).trans w67_70
  have w68_74 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K68.w32 (by decide) (by decide)).trans w67_74
  have w68_78 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K68.w32 (by decide) (by decide)).trans w67_78
  have w68_7c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K68.w32 (by decide) (by decide)).trans w67_7c
  have w68_80 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K68.w32 (by decide) (by decide)).trans w67_80
  have w68_84 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K68.w32 (by decide) (by decide)).trans w67_84
  have w68_88 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (vp) + BitVec.ofNat 32 tl56.header := (K68.w32 (by decide) (by decide)).trans w67_88
  have w68_90 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K68.w32 (by decide) (by decide)).trans w67_90
  have w68_94 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K68.w32 (by decide) (by decide)).trans w67_94
  have w68_98 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K68.w32 (by decide) (by decide)).trans w67_98
  have w68_9c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K68.w32 (by decide) (by decide)).trans w67_9c
  have w68_a0 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K68.w32 (by decide) (by decide)).trans w67_a0
  have w68_a4 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K68.w32 (by decide) (by decide)).trans w67_a4
  have w68_150 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K68.w32 (by decide) (by decide)).trans w67_150
  have w68_154 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K68.w32 (by decide) (by decide)).trans w67_154
  have w68_158 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K68.w32 (by decide) (by decide)).trans w67_158
  have w68_15c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K68.w32 (by decide) (by decide)).trans w67_15c
  have w68_380 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K68.w32 (by decide) (by decide)).trans w67_380
  have w68_384 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K68.w32 (by decide) (by decide)).trans w67_384
  have w68_388 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := (K68.w32 (by decide) (by decide)).trans w67_388
  have w68_38c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := (K68.w32 (by decide) (by decide)).trans w67_38c
  have w68_420 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := (K68.w32 (by decide) (by decide)).trans w67_420
  have w68_424 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := (K68.w32 (by decide) (by decide)).trans w67_424
  have w68_428 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K68.w32 (by decide) (by decide)).trans w67_428
  have w68_42c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := (K68.w32 (by decide) (by decide)).trans w67_42c
  have b68_430 : n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := (K68.b8 (by decide) (by decide)).trans b67_430
  have w68_8c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl56.len := by rw [W68, g67_11]
  clear w67_88 b67_430 w67_42c w67_428 w67_424 w67_420 w67_38c w67_388 w67_384 w67_380 w67_15c w67_158 w67_154 w67_150 w67_a4 w67_a0 w67_9c w67_98 w67_94 w67_90 w67_8c w67_84 w67_80 w67_7c w67_78 w67_74 w67_70 w67_6c w67_68 w67_64 w67_60 w67_5c w67_58 w67_54 w67_50 w67_4c w67_48 w67_44 w67_38 w67_34 w67_30 w67_2c g67_27 g67_26 g67_25 g67_24 g67_23 g67_22 g67_21 g67_20 g67_19 g67_18 g67_12 g67_11 g67_10 g67_9 g67_8 g67_4 g67_3 g67_2 V67 E67 fR67 t67 rg67 W67 K67 fr67 s67 d67
  -- 0x768: j
  obtain ⟨n69, d69, u69⟩ := s68.jump E68.self sv_at_768 (off' := 0x798) (by decide)
    (by rw [s68.pc]; decide)
  have s69 : St n69.mem SV n69 0x798 (reg n69) := ⟨u69.pc, rfl, fun _ => rfl⟩
  have m69 : n69.mem = n68.mem := u69.mem
  have fr69 : ∀ x, SvR B x → n69.mem x = n68.mem x := fun x _ => by rw [m69]
  have t69 : Steps n0 n69 := t68.trans (.single d69)
  have fR69 : ∀ x, SvR B x → n69.mem x = M0 x := fun x hx => (fr69 x hx).trans (fR68 x hx)
  have E69 : SvCode n69.mem := E68.fr F fr69
  have V69 : SvSaves B n69.mem v := V68.same m69
  have g69_2 : reg n69 sp = B + 0x21A0 := by rw [u69.regs, g68_2]
  have g69_3 : reg n69 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u69.regs, g68_3]
  have g69_4 : reg n69 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u69.regs, g68_4]
  have g69_8 : reg n69 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u69.regs, g68_8]
  have g69_9 : reg n69 (9 : Fin 32) = tbp := by rw [u69.regs, g68_9]
  have g69_10 : reg n69 a0 = (vp) + BitVec.ofNat 32 tl56.header := by rw [u69.regs, g68_10]
  have g69_11 : reg n69 a1 = BitVec.ofNat 32 tl56.len := by rw [u69.regs, g68_11]
  have g69_12 : reg n69 a2 = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [u69.regs, g68_12]
  have g69_18 : reg n69 (18 : Fin 32) = out := by rw [u69.regs, g68_18]
  have g69_19 : reg n69 (19 : Fin 32) = bp := by rw [u69.regs, g68_19]
  have g69_20 : reg n69 (20 : Fin 32) = dg := by rw [u69.regs, g68_20]
  have g69_21 : reg n69 (21 : Fin 32) = rootp := by rw [u69.regs, g68_21]
  have g69_22 : reg n69 (22 : Fin 32) = ll := by rw [u69.regs, g68_22]
  have g69_23 : reg n69 (23 : Fin 32) = sgp := by rw [u69.regs, g68_23]
  have g69_24 : reg n69 (24 : Fin 32) = kp := by rw [u69.regs, g68_24]
  have g69_25 : reg n69 (25 : Fin 32) = sgl := by rw [u69.regs, g68_25]
  have g69_26 : reg n69 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [u69.regs, g68_26]
  have g69_27 : reg n69 (27 : Fin 32) = tbl := by rw [u69.regs, g68_27]
  have keep_kk69 : SvKeepL B n0.mem n69.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x88, 0x4), (0x8C, 0x4)] := by rw [m69]; exact keep_kk68
  clear keep_kk68
  have w69_2c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m69]; exact w68_2c
  have w69_30 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m69]; exact w68_30
  have w69_34 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m69]; exact w68_34
  have w69_38 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m69]; exact w68_38
  have w69_44 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m69]; exact w68_44
  have w69_48 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m69]; exact w68_48
  have w69_4c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m69]; exact w68_4c
  have w69_50 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m69]; exact w68_50
  have w69_54 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m69]; exact w68_54
  have w69_58 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m69]; exact w68_58
  have w69_5c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m69]; exact w68_5c
  have w69_60 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m69]; exact w68_60
  have w69_64 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m69]; exact w68_64
  have w69_68 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m69]; exact w68_68
  have w69_6c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m69]; exact w68_6c
  have w69_70 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m69]; exact w68_70
  have w69_74 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m69]; exact w68_74
  have w69_78 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m69]; exact w68_78
  have w69_7c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m69]; exact w68_7c
  have w69_80 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m69]; exact w68_80
  have w69_84 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m69]; exact w68_84
  have w69_88 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m69]; exact w68_88
  have w69_8c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl56.len := by rw [m69]; exact w68_8c
  have w69_90 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m69]; exact w68_90
  have w69_94 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m69]; exact w68_94
  have w69_98 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m69]; exact w68_98
  have w69_9c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m69]; exact w68_9c
  have w69_a0 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m69]; exact w68_a0
  have w69_a4 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m69]; exact w68_a4
  have w69_150 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m69]; exact w68_150
  have w69_154 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m69]; exact w68_154
  have w69_158 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m69]; exact w68_158
  have w69_15c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m69]; exact w68_15c
  have w69_380 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m69]; exact w68_380
  have w69_384 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m69]; exact w68_384
  have w69_388 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m69]; exact w68_388
  have w69_38c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m69]; exact w68_38c
  have w69_420 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m69]; exact w68_420
  have w69_424 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m69]; exact w68_424
  have w69_428 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m69]; exact w68_428
  have w69_42c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m69]; exact w68_42c
  have b69_430 : n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m69]; exact b68_430
  clear w68_8c b68_430 w68_42c w68_428 w68_424 w68_420 w68_38c w68_388 w68_384 w68_380 w68_15c w68_158 w68_154 w68_150 w68_a4 w68_a0 w68_9c w68_98 w68_94 w68_90 w68_88 w68_84 w68_80 w68_7c w68_78 w68_74 w68_70 w68_6c w68_68 w68_64 w68_60 w68_5c w68_58 w68_54 w68_50 w68_4c w68_48 w68_44 w68_38 w68_34 w68_30 w68_2c g68_27 g68_26 g68_25 g68_24 g68_23 g68_22 g68_21 g68_20 g68_19 g68_18 g68_12 g68_11 g68_10 g68_9 g68_8 g68_4 g68_3 g68_2 V68 E68 fR68 t68 rg68 W68 K68 fr68 s68 d68
  -- 0x798: lw
  obtain ⟨n70, d70, u70⟩ := s69.lw E69.self sv_at_798 (off' := 0x79C) (by decide)
    (by rw [g69_2, show B + 0x21A0 + 0x15C = B + 0x21A0 + BitVec.ofNat 32 0x15C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s70 : St n70.mem SV n70 0x79C (reg n70) := ⟨u70.pc, rfl, fun _ => rfl⟩
  have m70 : n70.mem = n69.mem := u70.mem
  have fr70 : ∀ x, SvR B x → n70.mem x = n69.mem x := fun x _ => by rw [m70]
  have t70 : Steps n0 n70 := t69.trans (.single d70)
  have fR70 : ∀ x, SvR B x → n70.mem x = M0 x := fun x hx => (fr70 x hx).trans (fR69 x hx)
  have E70 : SvCode n70.mem := E69.fr F fr70
  have V70 : SvSaves B n70.mem v := V69.same m70
  have g70_2 : reg n70 sp = B + 0x21A0 := by rw [u70.regs, upd_ne (by decide) (by decide), g69_2]
  have g70_3 : reg n70 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u70.regs, upd_ne (by decide) (by decide), g69_3]
  have g70_4 : reg n70 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u70.regs, upd_ne (by decide) (by decide), g69_4]
  have g70_8 : reg n70 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u70.regs, upd_ne (by decide) (by decide), g69_8]
  have g70_9 : reg n70 (9 : Fin 32) = tbp := by rw [u70.regs, upd_ne (by decide) (by decide), g69_9]
  have g70_11 : reg n70 a1 = BitVec.ofNat 32 tl56.len := by rw [u70.regs, upd_ne (by decide) (by decide), g69_11]
  have g70_12 : reg n70 a2 = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [u70.regs, upd_ne (by decide) (by decide), g69_12]
  have g70_18 : reg n70 (18 : Fin 32) = out := by rw [u70.regs, upd_ne (by decide) (by decide), g69_18]
  have g70_19 : reg n70 (19 : Fin 32) = bp := by rw [u70.regs, upd_ne (by decide) (by decide), g69_19]
  have g70_20 : reg n70 (20 : Fin 32) = dg := by rw [u70.regs, upd_ne (by decide) (by decide), g69_20]
  have g70_21 : reg n70 (21 : Fin 32) = rootp := by rw [u70.regs, upd_ne (by decide) (by decide), g69_21]
  have g70_22 : reg n70 (22 : Fin 32) = ll := by rw [u70.regs, upd_ne (by decide) (by decide), g69_22]
  have g70_23 : reg n70 (23 : Fin 32) = sgp := by rw [u70.regs, upd_ne (by decide) (by decide), g69_23]
  have g70_24 : reg n70 (24 : Fin 32) = kp := by rw [u70.regs, upd_ne (by decide) (by decide), g69_24]
  have g70_25 : reg n70 (25 : Fin 32) = sgl := by rw [u70.regs, upd_ne (by decide) (by decide), g69_25]
  have g70_26 : reg n70 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [u70.regs, upd_ne (by decide) (by decide), g69_26]
  have g70_27 : reg n70 (27 : Fin 32) = tbl := by rw [u70.regs, upd_ne (by decide) (by decide), g69_27]
  have g70_10 : reg n70 a0 = rest := by
    rw [u70.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g69_2, show B + 0x21A0 + 0x15C = B + 0x21A0 + BitVec.ofNat 32 0x15C by sv_addr, w69_15c]
  have keep_kk70 : SvKeepL B n0.mem n70.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x88, 0x4), (0x8C, 0x4)] := by rw [m70]; exact keep_kk69
  clear keep_kk69
  have w70_2c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m70]; exact w69_2c
  have w70_30 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m70]; exact w69_30
  have w70_34 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m70]; exact w69_34
  have w70_38 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m70]; exact w69_38
  have w70_44 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m70]; exact w69_44
  have w70_48 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m70]; exact w69_48
  have w70_4c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m70]; exact w69_4c
  have w70_50 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m70]; exact w69_50
  have w70_54 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m70]; exact w69_54
  have w70_58 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m70]; exact w69_58
  have w70_5c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m70]; exact w69_5c
  have w70_60 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m70]; exact w69_60
  have w70_64 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m70]; exact w69_64
  have w70_68 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m70]; exact w69_68
  have w70_6c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m70]; exact w69_6c
  have w70_70 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m70]; exact w69_70
  have w70_74 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m70]; exact w69_74
  have w70_78 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m70]; exact w69_78
  have w70_7c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m70]; exact w69_7c
  have w70_80 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m70]; exact w69_80
  have w70_84 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m70]; exact w69_84
  have w70_88 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m70]; exact w69_88
  have w70_8c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl56.len := by rw [m70]; exact w69_8c
  have w70_90 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m70]; exact w69_90
  have w70_94 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m70]; exact w69_94
  have w70_98 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m70]; exact w69_98
  have w70_9c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m70]; exact w69_9c
  have w70_a0 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m70]; exact w69_a0
  have w70_a4 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m70]; exact w69_a4
  have w70_150 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m70]; exact w69_150
  have w70_154 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m70]; exact w69_154
  have w70_158 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m70]; exact w69_158
  have w70_15c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m70]; exact w69_15c
  have w70_380 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m70]; exact w69_380
  have w70_384 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m70]; exact w69_384
  have w70_388 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m70]; exact w69_388
  have w70_38c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m70]; exact w69_38c
  have w70_420 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m70]; exact w69_420
  have w70_424 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m70]; exact w69_424
  have w70_428 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m70]; exact w69_428
  have w70_42c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m70]; exact w69_42c
  have b70_430 : n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m70]; exact b69_430
  clear b69_430 w69_42c w69_428 w69_424 w69_420 w69_38c w69_388 w69_384 w69_380 w69_15c w69_158 w69_154 w69_150 w69_a4 w69_a0 w69_9c w69_98 w69_94 w69_90 w69_8c w69_88 w69_84 w69_80 w69_7c w69_78 w69_74 w69_70 w69_6c w69_68 w69_64 w69_60 w69_5c w69_58 w69_54 w69_50 w69_4c w69_48 w69_44 w69_38 w69_34 w69_30 w69_2c g69_27 g69_26 g69_25 g69_24 g69_23 g69_22 g69_21 g69_20 g69_19 g69_18 g69_12 g69_11 g69_10 g69_9 g69_8 g69_4 g69_3 g69_2 V69 E69 fR69 t69 fr69 m69 s69 u69 d69
  -- 0x79C: sw
  obtain ⟨n71, d71, s71, fr71, K71, W71, rg71⟩ := sv_sw F E70 s70 sv_at_79c (off' := 0x79E) (c := 0x50)
    (by decide) (by rw [g70_2]; sv_addr) (by decide) (by decide)
  have t71 : Steps n0 n71 := t70.trans d71
  have fR71 : ∀ x, SvR B x → n71.mem x = M0 x := fun x hx => (fr71 x hx).trans (fR70 x hx)
  have E71 : SvCode n71.mem := E70.fr F fr71
  have V71 : SvSaves B n71.mem v := V70.keep K71 (by decide)
  have g71_2 : reg n71 sp = B + 0x21A0 := by rw [rg71 sp, g70_2]
  have g71_3 : reg n71 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg71 (3 : Fin 32), g70_3]
  have g71_4 : reg n71 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg71 (4 : Fin 32), g70_4]
  have g71_8 : reg n71 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg71 (8 : Fin 32), g70_8]
  have g71_9 : reg n71 (9 : Fin 32) = tbp := by rw [rg71 (9 : Fin 32), g70_9]
  have g71_10 : reg n71 a0 = rest := by rw [rg71 a0, g70_10]
  have g71_11 : reg n71 a1 = BitVec.ofNat 32 tl56.len := by rw [rg71 a1, g70_11]
  have g71_12 : reg n71 a2 = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [rg71 a2, g70_12]
  have g71_18 : reg n71 (18 : Fin 32) = out := by rw [rg71 (18 : Fin 32), g70_18]
  have g71_19 : reg n71 (19 : Fin 32) = bp := by rw [rg71 (19 : Fin 32), g70_19]
  have g71_20 : reg n71 (20 : Fin 32) = dg := by rw [rg71 (20 : Fin 32), g70_20]
  have g71_21 : reg n71 (21 : Fin 32) = rootp := by rw [rg71 (21 : Fin 32), g70_21]
  have g71_22 : reg n71 (22 : Fin 32) = ll := by rw [rg71 (22 : Fin 32), g70_22]
  have g71_23 : reg n71 (23 : Fin 32) = sgp := by rw [rg71 (23 : Fin 32), g70_23]
  have g71_24 : reg n71 (24 : Fin 32) = kp := by rw [rg71 (24 : Fin 32), g70_24]
  have g71_25 : reg n71 (25 : Fin 32) = sgl := by rw [rg71 (25 : Fin 32), g70_25]
  have g71_26 : reg n71 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [rg71 (26 : Fin 32), g70_26]
  have g71_27 : reg n71 (27 : Fin 32) = tbl := by rw [rg71 (27 : Fin 32), g70_27]
  have keep_kk71 : SvKeepL B n0.mem n71.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x88, 0x4), (0x8C, 0x4), (0x50, 0x4)] := keep_kk70.trans K71.toL
  clear keep_kk70
  have w71_2c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K71.w32 (by decide) (by decide)).trans w70_2c
  have w71_30 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K71.w32 (by decide) (by decide)).trans w70_30
  have w71_34 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K71.w32 (by decide) (by decide)).trans w70_34
  have w71_38 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K71.w32 (by decide) (by decide)).trans w70_38
  have w71_44 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K71.w32 (by decide) (by decide)).trans w70_44
  have w71_48 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K71.w32 (by decide) (by decide)).trans w70_48
  have w71_4c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K71.w32 (by decide) (by decide)).trans w70_4c
  have w71_54 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K71.w32 (by decide) (by decide)).trans w70_54
  have w71_58 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K71.w32 (by decide) (by decide)).trans w70_58
  have w71_5c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K71.w32 (by decide) (by decide)).trans w70_5c
  have w71_60 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K71.w32 (by decide) (by decide)).trans w70_60
  have w71_64 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K71.w32 (by decide) (by decide)).trans w70_64
  have w71_68 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K71.w32 (by decide) (by decide)).trans w70_68
  have w71_6c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K71.w32 (by decide) (by decide)).trans w70_6c
  have w71_70 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K71.w32 (by decide) (by decide)).trans w70_70
  have w71_74 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K71.w32 (by decide) (by decide)).trans w70_74
  have w71_78 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K71.w32 (by decide) (by decide)).trans w70_78
  have w71_7c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K71.w32 (by decide) (by decide)).trans w70_7c
  have w71_80 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K71.w32 (by decide) (by decide)).trans w70_80
  have w71_84 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K71.w32 (by decide) (by decide)).trans w70_84
  have w71_88 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (vp) + BitVec.ofNat 32 tl56.header := (K71.w32 (by decide) (by decide)).trans w70_88
  have w71_8c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl56.len := (K71.w32 (by decide) (by decide)).trans w70_8c
  have w71_90 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K71.w32 (by decide) (by decide)).trans w70_90
  have w71_94 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K71.w32 (by decide) (by decide)).trans w70_94
  have w71_98 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K71.w32 (by decide) (by decide)).trans w70_98
  have w71_9c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K71.w32 (by decide) (by decide)).trans w70_9c
  have w71_a0 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K71.w32 (by decide) (by decide)).trans w70_a0
  have w71_a4 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K71.w32 (by decide) (by decide)).trans w70_a4
  have w71_150 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K71.w32 (by decide) (by decide)).trans w70_150
  have w71_154 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K71.w32 (by decide) (by decide)).trans w70_154
  have w71_158 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K71.w32 (by decide) (by decide)).trans w70_158
  have w71_15c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K71.w32 (by decide) (by decide)).trans w70_15c
  have w71_380 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K71.w32 (by decide) (by decide)).trans w70_380
  have w71_384 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K71.w32 (by decide) (by decide)).trans w70_384
  have w71_388 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := (K71.w32 (by decide) (by decide)).trans w70_388
  have w71_38c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := (K71.w32 (by decide) (by decide)).trans w70_38c
  have w71_420 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := (K71.w32 (by decide) (by decide)).trans w70_420
  have w71_424 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := (K71.w32 (by decide) (by decide)).trans w70_424
  have w71_428 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K71.w32 (by decide) (by decide)).trans w70_428
  have w71_42c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := (K71.w32 (by decide) (by decide)).trans w70_42c
  have b71_430 : n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := (K71.b8 (by decide) (by decide)).trans b70_430
  have w71_50 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rest := by rw [W71, g70_10]
  clear b70_430 w70_42c w70_428 w70_424 w70_420 w70_38c w70_388 w70_384 w70_380 w70_15c w70_158 w70_154 w70_150 w70_a4 w70_a0 w70_9c w70_98 w70_94 w70_90 w70_8c w70_88 w70_84 w70_80 w70_7c w70_78 w70_74 w70_70 w70_6c w70_68 w70_64 w70_60 w70_5c w70_58 w70_54 w70_50 w70_4c w70_48 w70_44 w70_38 w70_34 w70_30 w70_2c g70_10 g70_27 g70_26 g70_25 g70_24 g70_23 g70_22 g70_21 g70_20 g70_19 g70_18 g70_12 g70_11 g70_9 g70_8 g70_4 g70_3 g70_2 V70 E70 fR70 t70 fr70 m70 s70 u70 d70
  -- 0x79E: j
  obtain ⟨n72, d72, u72⟩ := s71.jump E71.self sv_at_79e (off' := 0x3B8) (by decide)
    (by rw [s71.pc]; decide)
  have s72 : St n72.mem SV n72 0x3B8 (reg n72) := ⟨u72.pc, rfl, fun _ => rfl⟩
  have m72 : n72.mem = n71.mem := u72.mem
  have fr72 : ∀ x, SvR B x → n72.mem x = n71.mem x := fun x _ => by rw [m72]
  have t72 : Steps n0 n72 := t71.trans (.single d72)
  have fR72 : ∀ x, SvR B x → n72.mem x = M0 x := fun x hx => (fr72 x hx).trans (fR71 x hx)
  have E72 : SvCode n72.mem := E71.fr F fr72
  have V72 : SvSaves B n72.mem v := V71.same m72
  have g72_2 : reg n72 sp = B + 0x21A0 := by rw [u72.regs, g71_2]
  have g72_3 : reg n72 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u72.regs, g71_3]
  have g72_4 : reg n72 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u72.regs, g71_4]
  have g72_8 : reg n72 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u72.regs, g71_8]
  have g72_9 : reg n72 (9 : Fin 32) = tbp := by rw [u72.regs, g71_9]
  have g72_10 : reg n72 a0 = rest := by rw [u72.regs, g71_10]
  have g72_11 : reg n72 a1 = BitVec.ofNat 32 tl56.len := by rw [u72.regs, g71_11]
  have g72_12 : reg n72 a2 = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [u72.regs, g71_12]
  have g72_18 : reg n72 (18 : Fin 32) = out := by rw [u72.regs, g71_18]
  have g72_19 : reg n72 (19 : Fin 32) = bp := by rw [u72.regs, g71_19]
  have g72_20 : reg n72 (20 : Fin 32) = dg := by rw [u72.regs, g71_20]
  have g72_21 : reg n72 (21 : Fin 32) = rootp := by rw [u72.regs, g71_21]
  have g72_22 : reg n72 (22 : Fin 32) = ll := by rw [u72.regs, g71_22]
  have g72_23 : reg n72 (23 : Fin 32) = sgp := by rw [u72.regs, g71_23]
  have g72_24 : reg n72 (24 : Fin 32) = kp := by rw [u72.regs, g71_24]
  have g72_25 : reg n72 (25 : Fin 32) = sgl := by rw [u72.regs, g71_25]
  have g72_26 : reg n72 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x88 := by rw [u72.regs, g71_26]
  have g72_27 : reg n72 (27 : Fin 32) = tbl := by rw [u72.regs, g71_27]
  have keep_kk72 : SvKeepL B n0.mem n72.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x88, 0x4), (0x8C, 0x4), (0x50, 0x4)] := by rw [m72]; exact keep_kk71
  clear keep_kk71
  have w72_2c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m72]; exact w71_2c
  have w72_30 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m72]; exact w71_30
  have w72_34 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m72]; exact w71_34
  have w72_38 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m72]; exact w71_38
  have w72_44 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m72]; exact w71_44
  have w72_48 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m72]; exact w71_48
  have w72_4c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m72]; exact w71_4c
  have w72_50 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rest := by rw [m72]; exact w71_50
  have w72_54 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m72]; exact w71_54
  have w72_58 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m72]; exact w71_58
  have w72_5c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m72]; exact w71_5c
  have w72_60 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m72]; exact w71_60
  have w72_64 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m72]; exact w71_64
  have w72_68 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m72]; exact w71_68
  have w72_6c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m72]; exact w71_6c
  have w72_70 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m72]; exact w71_70
  have w72_74 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m72]; exact w71_74
  have w72_78 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m72]; exact w71_78
  have w72_7c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m72]; exact w71_7c
  have w72_80 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m72]; exact w71_80
  have w72_84 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m72]; exact w71_84
  have w72_88 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m72]; exact w71_88
  have w72_8c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl56.len := by rw [m72]; exact w71_8c
  have w72_90 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m72]; exact w71_90
  have w72_94 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m72]; exact w71_94
  have w72_98 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m72]; exact w71_98
  have w72_9c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m72]; exact w71_9c
  have w72_a0 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m72]; exact w71_a0
  have w72_a4 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m72]; exact w71_a4
  have w72_150 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m72]; exact w71_150
  have w72_154 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m72]; exact w71_154
  have w72_158 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m72]; exact w71_158
  have w72_15c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m72]; exact w71_15c
  have w72_380 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m72]; exact w71_380
  have w72_384 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m72]; exact w71_384
  have w72_388 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m72]; exact w71_388
  have w72_38c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m72]; exact w71_38c
  have w72_420 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl56.header := by rw [m72]; exact w71_420
  have w72_424 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl56.len := by rw [m72]; exact w71_424
  have w72_428 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m72]; exact w71_428
  have w72_42c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl56.header + tl56.len) := by rw [m72]; exact w71_42c
  have b72_430 : n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl56.tag := by rw [m72]; exact b71_430
  clear w71_50 b71_430 w71_42c w71_428 w71_424 w71_420 w71_38c w71_388 w71_384 w71_380 w71_15c w71_158 w71_154 w71_150 w71_a4 w71_a0 w71_9c w71_98 w71_94 w71_90 w71_8c w71_88 w71_84 w71_80 w71_7c w71_78 w71_74 w71_70 w71_6c w71_68 w71_64 w71_60 w71_5c w71_58 w71_54 w71_4c w71_48 w71_44 w71_38 w71_34 w71_30 w71_2c g71_27 g71_26 g71_25 g71_24 g71_23 g71_22 g71_21 g71_20 g71_19 g71_18 g71_12 g71_11 g71_10 g71_9 g71_8 g71_4 g71_3 g71_2 V71 E71 fR71 t71 rg71 W71 K71 fr71 s71 d71
  exact .inr ⟨tl56, hr56, hz_60, hz_62, n72, t72, s72, E72, V72, fR72, g72_2, g72_3, g72_4, g72_8, g72_9, g72_18, g72_19, g72_20, g72_21, g72_22, g72_23, g72_24, g72_25, g72_27, w72_2c, w72_30, w72_50, w72_54, w72_58, w72_5c, w72_60, w72_64, w72_68, w72_6c, w72_70, w72_74, w72_78, w72_7c, w72_80, w72_84, w72_88, w72_8c, w72_90, w72_94, w72_98, w72_9c, w72_a0, w72_a4, w72_150, w72_154, w72_158, w72_15c, keep_kk72.mono (by decide)⟩

end C3.RV32.Sv
