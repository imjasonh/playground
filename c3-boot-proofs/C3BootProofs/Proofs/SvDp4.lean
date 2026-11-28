import C3BootProofs.Proofs.SvData

/-!
# `sigstore::verify`: an extension with policy OID 4

From the OID tests at 0x4E2 back to the loop head at 0x3B8, for an extension with policy OID 4: its value must be one `UTF8String`, which fills policy slot 4.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svDp44e2 : List BInstr :=
  [.aluImm .add a3 x0 0x3]
theorem svDp44e2_end : blockEnd sigstoreVerifyCode 0x4E2 svDp44e2 = some 0x4E4 := by
  simp only [svDp44e2]
  rw [blockEnd, sv_at_4e2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp44e8 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF8F7]
theorem svDp44e8_end : blockEnd sigstoreVerifyCode 0x4E8 svDp44e8 = some 0x4F0 := by
  simp only [svDp44e8]
  rw [blockEnd, sv_at_4e8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp4572 : List BInstr :=
  [.aluImm .add a3 x0 0x3]
theorem svDp4572_end : blockEnd sigstoreVerifyCode 0x572 svDp4572 = some 0x574 := by
  simp only [svDp4572]
  rw [blockEnd, sv_at_572]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp4578 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF900]
theorem svDp4578_end : blockEnd sigstoreVerifyCode 0x578 svDp4578 = some 0x580 := by
  simp only [svDp4578]
  rw [blockEnd, sv_at_578]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_57c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp4616 : List BInstr :=
  [.aluImm .add a3 x0 0x3]
theorem svDp4616_end : blockEnd sigstoreVerifyCode 0x616 svDp4616 = some 0x618 := by
  simp only [svDp4616]
  rw [blockEnd, sv_at_616]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp461c : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF8FD]
theorem svDp461c_end : blockEnd sigstoreVerifyCode 0x61C svDp461c = some 0x624 := by
  simp only [svDp461c]
  rw [blockEnd, sv_at_61c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_620]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp46f2 : List BInstr :=
  [.aluImm .add a0 x0 0xFFFFFFFF]
theorem svDp46f2_end : blockEnd sigstoreVerifyCode 0x6F2 svDp46f2 = some 0x6F4 := by
  simp only [svDp46f2]
  rw [blockEnd, sv_at_6f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp46f6 : List BInstr :=
  [.lui (26 : Fin 32) 0x3FCC5000, .aluImm .add (26 : Fin 32) (26 : Fin 32) 0xFFFFF958]
theorem svDp46f6_end : blockEnd sigstoreVerifyCode 0x6F6 svDp46f6 = some 0x6FE := by
  simp only [svDp46f6]
  rw [blockEnd, sv_at_6f6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_6fa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp46fe : List BInstr :=
  [.aluImm .add a0 x0 0x4]
theorem svDp46fe_end : blockEnd sigstoreVerifyCode 0x6FE svDp46fe = some 0x700 := by
  simp only [svDp46fe]
  rw [blockEnd, sv_at_6fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp470a : List BInstr :=
  [.aluImm .add a1 x0 0xA]
theorem svDp470a_end : blockEnd sigstoreVerifyCode 0x70A svDp470a = some 0x70C := by
  simp only [svDp470a]
  rw [blockEnd, sv_at_70a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp471a : List BInstr :=
  [.aluImm .add a1 a1 0x1]
theorem svDp471a_end : blockEnd sigstoreVerifyCode 0x71A svDp471a = some 0x71C := by
  simp only [svDp471a]
  rw [blockEnd, sv_at_71a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp471e : List BInstr :=
  [.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x8]
theorem svDp471e_end : blockEnd sigstoreVerifyCode 0x71E svDp471e = some 0x720 := by
  simp only [svDp471e]
  rw [blockEnd, sv_at_71e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp4724 : List BInstr :=
  [.aluImm .add a2 sp 0x380]
theorem svDp4724_end : blockEnd sigstoreVerifyCode 0x724 svDp4724 = some 0x726 := by
  simp only [svDp4724]
  rw [blockEnd, sv_at_724]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp4730 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x380]
theorem svDp4730_end : blockEnd sigstoreVerifyCode 0x730 svDp4730 = some 0x736 := by
  simp only [svDp4730]
  rw [blockEnd, sv_at_730]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_734]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp4748 : List BInstr :=
  [.aluImm .add a2 x0 0xC]
theorem svDp4748_end : blockEnd sigstoreVerifyCode 0x748 svDp4748 = some 0x74A := by
  simp only [svDp4748]
  rw [blockEnd, sv_at_748]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp4958 : List BInstr :=
  [.aluImm .add a0 x0 0x16]
theorem svDp4958_end : blockEnd sigstoreVerifyCode 0x958 svDp4958 = some 0x95A := by
  simp only [svDp4958]
  rw [blockEnd, sv_at_958]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp4940 : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem svDp4940_end : blockEnd sigstoreVerifyCode 0x940 svDp4940 = some 0x942 := by
  simp only [svDp4940]
  rw [blockEnd, sv_at_940]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp475c : List BInstr :=
  [.aluImm .sll (26 : Fin 32) (26 : Fin 32) 0x3, .aluImm .add a2 sp 0x80, .alu .add (26 : Fin 32) (26 : Fin 32) a2, .alu .add a2 x0 (26 : Fin 32)]
theorem svDp475c_end : blockEnd sigstoreVerifyCode 0x75C svDp475c = some 0x764 := by
  simp only [svDp475c]
  rw [blockEnd, sv_at_75c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_75e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_760]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_762]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_dp4 {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c op ol vp vl rest : Word} {v : Nat → Word} {n0 : Machine}
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
    (hp1 : ¬ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op ol.toNat)
    (hp2 : ¬ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op ol.toNat)
    (hp3 : ¬ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op ol.toNat)
    (hp4 : memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x55)) 10 = memBytes M0 op ol.toNat) :
    (¬ (∃ tl95, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl95 ∧ (BitVec.ofNat 8 tl95.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl95.header + tl95.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl95, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl95 ∧
    (BitVec.ofNat 8 tl95.tag = BitVec.ofNat 8 0xC) ∧
    ((vl) - BitVec.ofNat 32 (tl95.header + tl95.len) = 0) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = (vp) + BitVec.ofNat 32 tl95.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = BitVec.ofNat 32 tl95.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest ∧
        SvKeepL B n0.mem n'.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0xA0, 0x4), (0xA4, 0x4), (0x50, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x4E2
  obtain ⟨n1, c1, u1⟩ := s0.block svDp44e2 E0.self svDp44e2_end
    ⟨trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x4E4 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svDp44e2 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svDp44e2, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n4, c4, u4⟩ := s3.block svDp44e8 E3.self svDp44e8_end
    ⟨trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x4F0 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svDp44e8 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svDp44e8, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n7, c7, u7⟩ := s6.block svDp4572 E6.self svDp4572_end
    ⟨trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x574 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svDp4572 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svDp4572, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n10, c10, u10⟩ := s9.block svDp4578 E9.self svDp4578_end
    ⟨trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x580 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svDp4578 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svDp4578, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n13, c13, u13⟩ := s12.block svDp4616 E12.self svDp4616_end
    ⟨trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x618 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svDp4616 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svDp4616, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n16, c16, u16⟩ := s15.block svDp461c E15.self svDp461c_end
    ⟨trivial, trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x624 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svDp461c (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
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
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svDp461c, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n19, c19, u19⟩ := s18.block svDp46f2 E18.self svDp46f2_end
    ⟨trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x6F4 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svDp46f2 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svDp46f2, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n21, c21, u21⟩ := s20.block svDp46f6 E20.self svDp46f6_end
    ⟨trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x6FE (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svDp46f6 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svDp46f6, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n22, c22, u22⟩ := s21.block svDp46fe E21.self svDp46fe_end
    ⟨trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0x700 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svDp46fe (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svDp46fe, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n26, c26, u26⟩ := s25.block svDp470a E25.self svDp470a_end
    ⟨trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem SV n26 0x70C (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock svDp470a (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
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
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svDp470a, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n31, c31, u31⟩ := s30.block svDp471a E30.self svDp471a_end
    ⟨trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem SV n31 0x71C (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock svDp471a (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
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
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svDp471a, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n33, c33, u33⟩ := s32.block svDp471e E32.self svDp471e_end
    ⟨trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0x720 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svDp471e (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
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
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svDp471e, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n35, c35, u35⟩ := s34.block svDp46fe E34.self svDp46fe_end
    ⟨trivial, trivial⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have s35 : St n35.mem SV n35 0x700 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have rb35 : ∀ q, reg n35 q = (runBlock svDp46fe (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
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
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svDp46fe, upd, ↓reduceIte, aluEval]
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
  obtain ⟨n39, c39, u39⟩ := s38.block svDp470a E38.self svDp470a_end
    ⟨trivial, trivial⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have s39 : St n39.mem SV n39 0x70C (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have rb39 : ∀ q, reg n39 q = (runBlock svDp470a (n38.mem, reg n38)).2 q := fun q => by rw [u39.regs]
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
    rw [rb39]; simp +decide only [runBlock, BInstr.run, svDp470a, upd, ↓reduceIte, aluEval]
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
  have g42_10 : reg n42 a0 = BitVec.ofNat 32 0 := by rw [a0_42, ite_eq_right hp1]; rfl
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
  have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x0 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_10]
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
  obtain ⟨n44, c44, u44⟩ := s43.block svDp471a E43.self svDp471a_end
    ⟨trivial, trivial⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have s44 : St n44.mem SV n44 0x71C (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have rb44 : ∀ q, reg n44 q = (runBlock svDp471a (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
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
  have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x0 := by
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
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svDp471a, upd, ↓reduceIte, aluEval]
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
  have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x0 := by rw [rg45 a0, g44_10]
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
  obtain ⟨n46, c46, u46⟩ := s45.block svDp471e E45.self svDp471e_end
    ⟨trivial, trivial⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have s46 : St n46.mem SV n46 0x720 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have rb46 : ∀ q, reg n46 q = (runBlock svDp471e (n45.mem, reg n45)).2 q := fun q => by rw [u46.regs]
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
  have g46_10 : reg n46 a0 = BitVec.ofNat 32 0x0 := by
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
    rw [rb46]; simp +decide only [runBlock, BInstr.run, svDp471e, upd, ↓reduceIte, aluEval]
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
  -- 0x720: branch, taken
  obtain ⟨n47, d47, u47⟩ := s46.taken E46.self 0x6FE sv_at_720
    (by decide) (by rw [g46_10, s46.zero]; decide)
  have s47 : St n47.mem SV n47 0x6FE (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
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
  have g47_10 : reg n47 a0 = BitVec.ofNat 32 0x0 := by rw [u47.regs, g46_10]
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
  -- 0x6FE
  obtain ⟨n48, c48, u48⟩ := s47.block svDp46fe E47.self svDp46fe_end
    ⟨trivial, trivial⟩
  have m48 : n48.mem = n47.mem := u48.mem
  have s48 : St n48.mem SV n48 0x700 (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
  have rb48 : ∀ q, reg n48 q = (runBlock svDp46fe (n47.mem, reg n47)).2 q := fun q => by rw [u48.regs]
  have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
  have t48 : Steps n0 n48 := t47.trans c48
  have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : SvCode n48.mem := E47.fr F fr48
  have V48 : SvSaves B n48.mem v := V47.same m48
  have g48_2 : reg n48 sp = B + 0x21A0 := by
    rw [rb48, runBlock_reg _ _ _ sp s47.zero (by decide), g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb48, runBlock_reg _ _ _ (3 : Fin 32) s47.zero (by decide), g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb48, runBlock_reg _ _ _ (4 : Fin 32) s47.zero (by decide), g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb48, runBlock_reg _ _ _ (8 : Fin 32) s47.zero (by decide), g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = tbp := by
    rw [rb48, runBlock_reg _ _ _ (9 : Fin 32) s47.zero (by decide), g47_9]
  have g48_11 : reg n48 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb48, runBlock_reg _ _ _ a1 s47.zero (by decide), g47_11]
  have g48_18 : reg n48 (18 : Fin 32) = out := by
    rw [rb48, runBlock_reg _ _ _ (18 : Fin 32) s47.zero (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by
    rw [rb48, runBlock_reg _ _ _ (19 : Fin 32) s47.zero (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = dg := by
    rw [rb48, runBlock_reg _ _ _ (20 : Fin 32) s47.zero (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = rootp := by
    rw [rb48, runBlock_reg _ _ _ (21 : Fin 32) s47.zero (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = ll := by
    rw [rb48, runBlock_reg _ _ _ (22 : Fin 32) s47.zero (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = sgp := by
    rw [rb48, runBlock_reg _ _ _ (23 : Fin 32) s47.zero (by decide), g47_23]
  have g48_24 : reg n48 (24 : Fin 32) = kp := by
    rw [rb48, runBlock_reg _ _ _ (24 : Fin 32) s47.zero (by decide), g47_24]
  have g48_25 : reg n48 (25 : Fin 32) = sgl := by
    rw [rb48, runBlock_reg _ _ _ (25 : Fin 32) s47.zero (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by
    rw [rb48, runBlock_reg _ _ _ (26 : Fin 32) s47.zero (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = tbl := by
    rw [rb48, runBlock_reg _ _ _ (27 : Fin 32) s47.zero (by decide), g47_27]
  have g48_10 : reg n48 a0 = BitVec.ofNat 32 0x4 := by
    rw [rb48]; simp +decide only [runBlock, BInstr.run, svDp46fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g47_2, g47_3, g47_4, g47_8, g47_9, g47_10, g47_11, g47_18, g47_19, g47_20, g47_21, g47_22, g47_23, g47_24, g47_25, g47_26, g47_27, s47.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  -- 0x700: lw
  obtain ⟨n49, d49, u49⟩ := s48.lw E48.self sv_at_700 (off' := 0x702) (by decide)
    (by rw [g48_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s49 : St n49.mem SV n49 0x702 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
  have m49 : n49.mem = n48.mem := u49.mem
  have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
  have t49 : Steps n0 n49 := t48.trans (.single d49)
  have fR49 : ∀ x, SvR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.same m49
  have g49_2 : reg n49 sp = B + 0x21A0 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u49.regs, upd_ne (by decide) (by decide), g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u49.regs, upd_ne (by decide) (by decide), g48_4]
  have g49_8 : reg n49 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_8]
  have g49_9 : reg n49 (9 : Fin 32) = tbp := by rw [u49.regs, upd_ne (by decide) (by decide), g48_9]
  have g49_10 : reg n49 a0 = BitVec.ofNat 32 0x4 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_10]
  have g49_18 : reg n49 (18 : Fin 32) = out := by rw [u49.regs, upd_ne (by decide) (by decide), g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [u49.regs, upd_ne (by decide) (by decide), g48_19]
  have g49_20 : reg n49 (20 : Fin 32) = dg := by rw [u49.regs, upd_ne (by decide) (by decide), g48_20]
  have g49_21 : reg n49 (21 : Fin 32) = rootp := by rw [u49.regs, upd_ne (by decide) (by decide), g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = ll := by rw [u49.regs, upd_ne (by decide) (by decide), g48_22]
  have g49_23 : reg n49 (23 : Fin 32) = sgp := by rw [u49.regs, upd_ne (by decide) (by decide), g48_23]
  have g49_24 : reg n49 (24 : Fin 32) = kp := by rw [u49.regs, upd_ne (by decide) (by decide), g48_24]
  have g49_25 : reg n49 (25 : Fin 32) = sgl := by rw [u49.regs, upd_ne (by decide) (by decide), g48_25]
  have g49_26 : reg n49 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u49.regs, upd_ne (by decide) (by decide), g48_26]
  have g49_27 : reg n49 (27 : Fin 32) = tbl := by rw [u49.regs, upd_ne (by decide) (by decide), g48_27]
  have g49_11 : reg n49 a1 = BitVec.ofNat 32 0x1 := by
    rw [u49.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g48_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w48_50]
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
  clear w48_15c w48_158 w48_154 w48_150 w48_a4 w48_a0 w48_9c w48_98 w48_94 w48_90 w48_8c w48_88 w48_84 w48_80 w48_7c w48_78 w48_74 w48_70 w48_6c w48_68 w48_64 w48_60 w48_5c w48_58 w48_54 w48_50 w48_4c w48_48 w48_44 w48_38 w48_34 w48_30 w48_2c g48_10 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_11 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 rb48 s48 m48 u48 c48
  -- 0x702: branch, not taken
  obtain ⟨n50, d50, u50⟩ := s49.notTaken E49.self 0x706 sv_at_702
    (by decide) (by rw [g49_11, g49_10]; decide)
  have s50 : St n50.mem SV n50 0x706 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
  have m50 : n50.mem = n49.mem := u50.mem
  have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
  have t50 : Steps n0 n50 := t49.trans (.single d50)
  have fR50 : ∀ x, SvR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : SvCode n50.mem := E49.fr F fr50
  have V50 : SvSaves B n50.mem v := V49.same m50
  have g50_2 : reg n50 sp = B + 0x21A0 := by rw [u50.regs, g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u50.regs, g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u50.regs, g49_4]
  have g50_8 : reg n50 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u50.regs, g49_8]
  have g50_9 : reg n50 (9 : Fin 32) = tbp := by rw [u50.regs, g49_9]
  have g50_10 : reg n50 a0 = BitVec.ofNat 32 0x4 := by rw [u50.regs, g49_10]
  have g50_11 : reg n50 a1 = BitVec.ofNat 32 0x1 := by rw [u50.regs, g49_11]
  have g50_18 : reg n50 (18 : Fin 32) = out := by rw [u50.regs, g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [u50.regs, g49_19]
  have g50_20 : reg n50 (20 : Fin 32) = dg := by rw [u50.regs, g49_20]
  have g50_21 : reg n50 (21 : Fin 32) = rootp := by rw [u50.regs, g49_21]
  have g50_22 : reg n50 (22 : Fin 32) = ll := by rw [u50.regs, g49_22]
  have g50_23 : reg n50 (23 : Fin 32) = sgp := by rw [u50.regs, g49_23]
  have g50_24 : reg n50 (24 : Fin 32) = kp := by rw [u50.regs, g49_24]
  have g50_25 : reg n50 (25 : Fin 32) = sgl := by rw [u50.regs, g49_25]
  have g50_26 : reg n50 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u50.regs, g49_26]
  have g50_27 : reg n50 (27 : Fin 32) = tbl := by rw [u50.regs, g49_27]
  have keep_kk50 : SvKeepL B n0.mem n50.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m50]; exact keep_kk49
  clear keep_kk49
  have w50_2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m50]; exact w49_2c
  have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m50]; exact w49_30
  have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m50]; exact w49_34
  have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m50]; exact w49_38
  have w50_44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m50]; exact w49_44
  have w50_48 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m50]; exact w49_48
  have w50_4c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m50]; exact w49_4c
  have w50_50 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m50]; exact w49_50
  have w50_54 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m50]; exact w49_54
  have w50_58 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m50]; exact w49_58
  have w50_5c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m50]; exact w49_5c
  have w50_60 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m50]; exact w49_60
  have w50_64 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m50]; exact w49_64
  have w50_68 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m50]; exact w49_68
  have w50_6c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m50]; exact w49_6c
  have w50_70 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m50]; exact w49_70
  have w50_74 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m50]; exact w49_74
  have w50_78 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m50]; exact w49_78
  have w50_7c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m50]; exact w49_7c
  have w50_80 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m50]; exact w49_80
  have w50_84 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m50]; exact w49_84
  have w50_88 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m50]; exact w49_88
  have w50_8c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m50]; exact w49_8c
  have w50_90 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m50]; exact w49_90
  have w50_94 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m50]; exact w49_94
  have w50_98 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m50]; exact w49_98
  have w50_9c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m50]; exact w49_9c
  have w50_a0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m50]; exact w49_a0
  have w50_a4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m50]; exact w49_a4
  have w50_150 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m50]; exact w49_150
  have w50_154 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m50]; exact w49_154
  have w50_158 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m50]; exact w49_158
  have w50_15c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m50]; exact w49_15c
  clear w49_15c w49_158 w49_154 w49_150 w49_a4 w49_a0 w49_9c w49_98 w49_94 w49_90 w49_8c w49_88 w49_84 w49_80 w49_7c w49_78 w49_74 w49_70 w49_6c w49_68 w49_64 w49_60 w49_5c w49_58 w49_54 w49_50 w49_4c w49_48 w49_44 w49_38 w49_34 w49_30 w49_2c g49_11 g49_27 g49_26 g49_25 g49_24 g49_23 g49_22 g49_21 g49_20 g49_19 g49_18 g49_10 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 m49 s49 u49 d49
  -- 0x706: lw of a constant
  obtain ⟨n51, d51, u51⟩ := s50.lw E50.self sv_at_706 (off' := 0x70A) (by decide)
    (by rw [g50_26]; decide)
  have s51 : St n51.mem SV n51 0x70A (reg n51) := ⟨u51.pc, rfl, fun _ => rfl⟩
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
  have g51_11 : reg n51 a1 = BitVec.ofNat 32 0x1 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_11]
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
  have g51_10 : reg n51 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x41) := by
    rw [u51.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g50_26, show BitVec.ofNat 32 (img% svConstExtAddress + 0x71) + 0x0 = BitVec.ofNat 32 svConstExtAddress + BitVec.ofNat 32 0x71 by decide]
    exact CodeIn.w32 (SvData.sv FW SD0 fR50).ext (by decide) (by decide)
  have keep_kk51 : SvKeepL B n0.mem n51.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m51]; exact keep_kk50
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
  clear w50_15c w50_158 w50_154 w50_150 w50_a4 w50_a0 w50_9c w50_98 w50_94 w50_90 w50_8c w50_88 w50_84 w50_80 w50_7c w50_78 w50_74 w50_70 w50_6c w50_68 w50_64 w50_60 w50_5c w50_58 w50_54 w50_50 w50_4c w50_48 w50_44 w50_38 w50_34 w50_30 w50_2c g50_27 g50_26 g50_25 g50_24 g50_23 g50_22 g50_21 g50_20 g50_19 g50_18 g50_11 g50_10 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 fr50 m50 s50 u50 d50
  -- 0x70A
  obtain ⟨n52, c52, u52⟩ := s51.block svDp470a E51.self svDp470a_end
    ⟨trivial, trivial⟩
  have m52 : n52.mem = n51.mem := u52.mem
  have s52 : St n52.mem SV n52 0x70C (reg n52) := ⟨u52.pc, rfl, fun _ => rfl⟩
  have rb52 : ∀ q, reg n52 q = (runBlock svDp470a (n51.mem, reg n51)).2 q := fun q => by rw [u52.regs]
  have fr52 : ∀ x, SvR B x → n52.mem x = n51.mem x := fun x _ => by rw [m52]
  have t52 : Steps n0 n52 := t51.trans c52
  have fR52 : ∀ x, SvR B x → n52.mem x = M0 x := fun x hx => (fr52 x hx).trans (fR51 x hx)
  have E52 : SvCode n52.mem := E51.fr F fr52
  have V52 : SvSaves B n52.mem v := V51.same m52
  have g52_2 : reg n52 sp = B + 0x21A0 := by
    rw [rb52, runBlock_reg _ _ _ sp s51.zero (by decide), g51_2]
  have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb52, runBlock_reg _ _ _ (3 : Fin 32) s51.zero (by decide), g51_3]
  have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb52, runBlock_reg _ _ _ (4 : Fin 32) s51.zero (by decide), g51_4]
  have g52_8 : reg n52 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb52, runBlock_reg _ _ _ (8 : Fin 32) s51.zero (by decide), g51_8]
  have g52_9 : reg n52 (9 : Fin 32) = tbp := by
    rw [rb52, runBlock_reg _ _ _ (9 : Fin 32) s51.zero (by decide), g51_9]
  have g52_10 : reg n52 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x41) := by
    rw [rb52, runBlock_reg _ _ _ a0 s51.zero (by decide), g51_10]
  have g52_18 : reg n52 (18 : Fin 32) = out := by
    rw [rb52, runBlock_reg _ _ _ (18 : Fin 32) s51.zero (by decide), g51_18]
  have g52_19 : reg n52 (19 : Fin 32) = bp := by
    rw [rb52, runBlock_reg _ _ _ (19 : Fin 32) s51.zero (by decide), g51_19]
  have g52_20 : reg n52 (20 : Fin 32) = dg := by
    rw [rb52, runBlock_reg _ _ _ (20 : Fin 32) s51.zero (by decide), g51_20]
  have g52_21 : reg n52 (21 : Fin 32) = rootp := by
    rw [rb52, runBlock_reg _ _ _ (21 : Fin 32) s51.zero (by decide), g51_21]
  have g52_22 : reg n52 (22 : Fin 32) = ll := by
    rw [rb52, runBlock_reg _ _ _ (22 : Fin 32) s51.zero (by decide), g51_22]
  have g52_23 : reg n52 (23 : Fin 32) = sgp := by
    rw [rb52, runBlock_reg _ _ _ (23 : Fin 32) s51.zero (by decide), g51_23]
  have g52_24 : reg n52 (24 : Fin 32) = kp := by
    rw [rb52, runBlock_reg _ _ _ (24 : Fin 32) s51.zero (by decide), g51_24]
  have g52_25 : reg n52 (25 : Fin 32) = sgl := by
    rw [rb52, runBlock_reg _ _ _ (25 : Fin 32) s51.zero (by decide), g51_25]
  have g52_26 : reg n52 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by
    rw [rb52, runBlock_reg _ _ _ (26 : Fin 32) s51.zero (by decide), g51_26]
  have g52_27 : reg n52 (27 : Fin 32) = tbl := by
    rw [rb52, runBlock_reg _ _ _ (27 : Fin 32) s51.zero (by decide), g51_27]
  have g52_11 : reg n52 a1 = BitVec.ofNat 32 0xA := by
    rw [rb52]; simp +decide only [runBlock, BInstr.run, svDp470a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g51_2, g51_3, g51_4, g51_8, g51_9, g51_10, g51_11, g51_18, g51_19, g51_20, g51_21, g51_22, g51_23, g51_24, g51_25, g51_26, g51_27, s51.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk52 : SvKeepL B n0.mem n52.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m52]; exact keep_kk51
  clear keep_kk51
  have w52_2c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m52]; exact w51_2c
  have w52_30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m52]; exact w51_30
  have w52_34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m52]; exact w51_34
  have w52_38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m52]; exact w51_38
  have w52_44 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m52]; exact w51_44
  have w52_48 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m52]; exact w51_48
  have w52_4c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m52]; exact w51_4c
  have w52_50 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m52]; exact w51_50
  have w52_54 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m52]; exact w51_54
  have w52_58 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m52]; exact w51_58
  have w52_5c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m52]; exact w51_5c
  have w52_60 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m52]; exact w51_60
  have w52_64 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m52]; exact w51_64
  have w52_68 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m52]; exact w51_68
  have w52_6c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m52]; exact w51_6c
  have w52_70 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m52]; exact w51_70
  have w52_74 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m52]; exact w51_74
  have w52_78 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m52]; exact w51_78
  have w52_7c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m52]; exact w51_7c
  have w52_80 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m52]; exact w51_80
  have w52_84 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m52]; exact w51_84
  have w52_88 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m52]; exact w51_88
  have w52_8c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m52]; exact w51_8c
  have w52_90 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m52]; exact w51_90
  have w52_94 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m52]; exact w51_94
  have w52_98 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m52]; exact w51_98
  have w52_9c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m52]; exact w51_9c
  have w52_a0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m52]; exact w51_a0
  have w52_a4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m52]; exact w51_a4
  have w52_150 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m52]; exact w51_150
  have w52_154 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m52]; exact w51_154
  have w52_158 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m52]; exact w51_158
  have w52_15c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m52]; exact w51_15c
  clear w51_15c w51_158 w51_154 w51_150 w51_a4 w51_a0 w51_9c w51_98 w51_94 w51_90 w51_8c w51_88 w51_84 w51_80 w51_7c w51_78 w51_74 w51_70 w51_6c w51_68 w51_64 w51_60 w51_5c w51_58 w51_54 w51_50 w51_4c w51_48 w51_44 w51_38 w51_34 w51_30 w51_2c g51_10 g51_27 g51_26 g51_25 g51_24 g51_23 g51_22 g51_21 g51_20 g51_19 g51_18 g51_11 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 m51 s51 u51 d51
  -- 0x70C: lw
  obtain ⟨n53, d53, u53⟩ := s52.lw E52.self sv_at_70c (off' := 0x70E) (by decide)
    (by rw [g52_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s53 : St n53.mem SV n53 0x70E (reg n53) := ⟨u53.pc, rfl, fun _ => rfl⟩
  have m53 : n53.mem = n52.mem := u53.mem
  have fr53 : ∀ x, SvR B x → n53.mem x = n52.mem x := fun x _ => by rw [m53]
  have t53 : Steps n0 n53 := t52.trans (.single d53)
  have fR53 : ∀ x, SvR B x → n53.mem x = M0 x := fun x hx => (fr53 x hx).trans (fR52 x hx)
  have E53 : SvCode n53.mem := E52.fr F fr53
  have V53 : SvSaves B n53.mem v := V52.same m53
  have g53_2 : reg n53 sp = B + 0x21A0 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_2]
  have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u53.regs, upd_ne (by decide) (by decide), g52_3]
  have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u53.regs, upd_ne (by decide) (by decide), g52_4]
  have g53_8 : reg n53 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_8]
  have g53_9 : reg n53 (9 : Fin 32) = tbp := by rw [u53.regs, upd_ne (by decide) (by decide), g52_9]
  have g53_10 : reg n53 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x41) := by rw [u53.regs, upd_ne (by decide) (by decide), g52_10]
  have g53_11 : reg n53 a1 = BitVec.ofNat 32 0xA := by rw [u53.regs, upd_ne (by decide) (by decide), g52_11]
  have g53_18 : reg n53 (18 : Fin 32) = out := by rw [u53.regs, upd_ne (by decide) (by decide), g52_18]
  have g53_19 : reg n53 (19 : Fin 32) = bp := by rw [u53.regs, upd_ne (by decide) (by decide), g52_19]
  have g53_20 : reg n53 (20 : Fin 32) = dg := by rw [u53.regs, upd_ne (by decide) (by decide), g52_20]
  have g53_21 : reg n53 (21 : Fin 32) = rootp := by rw [u53.regs, upd_ne (by decide) (by decide), g52_21]
  have g53_22 : reg n53 (22 : Fin 32) = ll := by rw [u53.regs, upd_ne (by decide) (by decide), g52_22]
  have g53_23 : reg n53 (23 : Fin 32) = sgp := by rw [u53.regs, upd_ne (by decide) (by decide), g52_23]
  have g53_24 : reg n53 (24 : Fin 32) = kp := by rw [u53.regs, upd_ne (by decide) (by decide), g52_24]
  have g53_25 : reg n53 (25 : Fin 32) = sgl := by rw [u53.regs, upd_ne (by decide) (by decide), g52_25]
  have g53_26 : reg n53 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u53.regs, upd_ne (by decide) (by decide), g52_26]
  have g53_27 : reg n53 (27 : Fin 32) = tbl := by rw [u53.regs, upd_ne (by decide) (by decide), g52_27]
  have g53_12 : reg n53 a2 = op := by
    rw [u53.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g52_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w52_4c]
  have keep_kk53 : SvKeepL B n0.mem n53.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m53]; exact keep_kk52
  clear keep_kk52
  have w53_2c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m53]; exact w52_2c
  have w53_30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m53]; exact w52_30
  have w53_34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m53]; exact w52_34
  have w53_38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m53]; exact w52_38
  have w53_44 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m53]; exact w52_44
  have w53_48 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m53]; exact w52_48
  have w53_4c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m53]; exact w52_4c
  have w53_50 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m53]; exact w52_50
  have w53_54 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m53]; exact w52_54
  have w53_58 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m53]; exact w52_58
  have w53_5c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m53]; exact w52_5c
  have w53_60 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m53]; exact w52_60
  have w53_64 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m53]; exact w52_64
  have w53_68 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m53]; exact w52_68
  have w53_6c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m53]; exact w52_6c
  have w53_70 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m53]; exact w52_70
  have w53_74 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m53]; exact w52_74
  have w53_78 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m53]; exact w52_78
  have w53_7c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m53]; exact w52_7c
  have w53_80 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m53]; exact w52_80
  have w53_84 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m53]; exact w52_84
  have w53_88 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m53]; exact w52_88
  have w53_8c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m53]; exact w52_8c
  have w53_90 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m53]; exact w52_90
  have w53_94 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m53]; exact w52_94
  have w53_98 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m53]; exact w52_98
  have w53_9c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m53]; exact w52_9c
  have w53_a0 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m53]; exact w52_a0
  have w53_a4 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m53]; exact w52_a4
  have w53_150 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m53]; exact w52_150
  have w53_154 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m53]; exact w52_154
  have w53_158 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m53]; exact w52_158
  have w53_15c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m53]; exact w52_15c
  clear w52_15c w52_158 w52_154 w52_150 w52_a4 w52_a0 w52_9c w52_98 w52_94 w52_90 w52_8c w52_88 w52_84 w52_80 w52_7c w52_78 w52_74 w52_70 w52_6c w52_68 w52_64 w52_60 w52_5c w52_58 w52_54 w52_50 w52_4c w52_48 w52_44 w52_38 w52_34 w52_30 w52_2c g52_11 g52_27 g52_26 g52_25 g52_24 g52_23 g52_22 g52_21 g52_20 g52_19 g52_18 g52_10 g52_9 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 fr52 rb52 s52 m52 u52 c52
  -- 0x70E: lw
  obtain ⟨n54, d54, u54⟩ := s53.lw E53.self sv_at_70e (off' := 0x710) (by decide)
    (by rw [g53_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s54 : St n54.mem SV n54 0x710 (reg n54) := ⟨u54.pc, rfl, fun _ => rfl⟩
  have m54 : n54.mem = n53.mem := u54.mem
  have fr54 : ∀ x, SvR B x → n54.mem x = n53.mem x := fun x _ => by rw [m54]
  have t54 : Steps n0 n54 := t53.trans (.single d54)
  have fR54 : ∀ x, SvR B x → n54.mem x = M0 x := fun x hx => (fr54 x hx).trans (fR53 x hx)
  have E54 : SvCode n54.mem := E53.fr F fr54
  have V54 : SvSaves B n54.mem v := V53.same m54
  have g54_2 : reg n54 sp = B + 0x21A0 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_2]
  have g54_3 : reg n54 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u54.regs, upd_ne (by decide) (by decide), g53_3]
  have g54_4 : reg n54 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u54.regs, upd_ne (by decide) (by decide), g53_4]
  have g54_8 : reg n54 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_8]
  have g54_9 : reg n54 (9 : Fin 32) = tbp := by rw [u54.regs, upd_ne (by decide) (by decide), g53_9]
  have g54_10 : reg n54 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x41) := by rw [u54.regs, upd_ne (by decide) (by decide), g53_10]
  have g54_11 : reg n54 a1 = BitVec.ofNat 32 0xA := by rw [u54.regs, upd_ne (by decide) (by decide), g53_11]
  have g54_12 : reg n54 a2 = op := by rw [u54.regs, upd_ne (by decide) (by decide), g53_12]
  have g54_18 : reg n54 (18 : Fin 32) = out := by rw [u54.regs, upd_ne (by decide) (by decide), g53_18]
  have g54_19 : reg n54 (19 : Fin 32) = bp := by rw [u54.regs, upd_ne (by decide) (by decide), g53_19]
  have g54_20 : reg n54 (20 : Fin 32) = dg := by rw [u54.regs, upd_ne (by decide) (by decide), g53_20]
  have g54_21 : reg n54 (21 : Fin 32) = rootp := by rw [u54.regs, upd_ne (by decide) (by decide), g53_21]
  have g54_22 : reg n54 (22 : Fin 32) = ll := by rw [u54.regs, upd_ne (by decide) (by decide), g53_22]
  have g54_23 : reg n54 (23 : Fin 32) = sgp := by rw [u54.regs, upd_ne (by decide) (by decide), g53_23]
  have g54_24 : reg n54 (24 : Fin 32) = kp := by rw [u54.regs, upd_ne (by decide) (by decide), g53_24]
  have g54_25 : reg n54 (25 : Fin 32) = sgl := by rw [u54.regs, upd_ne (by decide) (by decide), g53_25]
  have g54_26 : reg n54 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u54.regs, upd_ne (by decide) (by decide), g53_26]
  have g54_27 : reg n54 (27 : Fin 32) = tbl := by rw [u54.regs, upd_ne (by decide) (by decide), g53_27]
  have g54_13 : reg n54 a3 = ol := by
    rw [u54.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g53_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w53_48]
  have keep_kk54 : SvKeepL B n0.mem n54.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m54]; exact keep_kk53
  clear keep_kk53
  have w54_2c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m54]; exact w53_2c
  have w54_30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m54]; exact w53_30
  have w54_34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m54]; exact w53_34
  have w54_38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m54]; exact w53_38
  have w54_44 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m54]; exact w53_44
  have w54_48 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m54]; exact w53_48
  have w54_4c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m54]; exact w53_4c
  have w54_50 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m54]; exact w53_50
  have w54_54 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m54]; exact w53_54
  have w54_58 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m54]; exact w53_58
  have w54_5c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m54]; exact w53_5c
  have w54_60 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m54]; exact w53_60
  have w54_64 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m54]; exact w53_64
  have w54_68 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m54]; exact w53_68
  have w54_6c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m54]; exact w53_6c
  have w54_70 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m54]; exact w53_70
  have w54_74 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m54]; exact w53_74
  have w54_78 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m54]; exact w53_78
  have w54_7c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m54]; exact w53_7c
  have w54_80 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m54]; exact w53_80
  have w54_84 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m54]; exact w53_84
  have w54_88 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m54]; exact w53_88
  have w54_8c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m54]; exact w53_8c
  have w54_90 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m54]; exact w53_90
  have w54_94 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m54]; exact w53_94
  have w54_98 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m54]; exact w53_98
  have w54_9c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m54]; exact w53_9c
  have w54_a0 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m54]; exact w53_a0
  have w54_a4 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m54]; exact w53_a4
  have w54_150 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m54]; exact w53_150
  have w54_154 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m54]; exact w53_154
  have w54_158 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m54]; exact w53_158
  have w54_15c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m54]; exact w53_15c
  clear w53_15c w53_158 w53_154 w53_150 w53_a4 w53_a0 w53_9c w53_98 w53_94 w53_90 w53_8c w53_88 w53_84 w53_80 w53_7c w53_78 w53_74 w53_70 w53_6c w53_68 w53_64 w53_60 w53_5c w53_58 w53_54 w53_50 w53_4c w53_48 w53_44 w53_38 w53_34 w53_30 w53_2c g53_12 g53_27 g53_26 g53_25 g53_24 g53_23 g53_22 g53_21 g53_20 g53_19 g53_18 g53_11 g53_10 g53_9 g53_8 g53_4 g53_3 g53_2 V53 E53 fR53 t53 fr53 m53 s53 u53 d53
  -- 0x710: sv_seqEqF
  obtain ⟨n55, c55, s55, rk55, a0_55, K55, fr55⟩ := sv_seqEqF (pl := 10) (ql := ol.toNat)
    F E54 s54 sv_at_710 sv_at_714 (by decide) (by decide) g54_2
    g54_10 g54_11 g54_12 (by rw [g54_13, ofNat_toNat_self]) (.inr ⟨by decide, by decide⟩) (.inl oid_in)
  have t55 : Steps n0 n55 := t54.trans c55
  have fR55 : ∀ x, SvR B x → n55.mem x = M0 x := fun x hx => (fr55 x hx).trans (fR54 x hx)
  have E55 : SvCode n55.mem := E54.fr F fr55
  have V55 : SvSaves B n55.mem v := V54.keepL K55 (by decide)
  rw [sv_mbRo FW fR54 (.inr ⟨by decide, by decide⟩), sv_mbRo FW fR54 (.inl oid_in)] at a0_55
  have g55_2 : reg n55 sp = B + 0x21A0 := by rw [rk55 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_2]
  have g55_3 : reg n55 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk55 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_3]
  have g55_4 : reg n55 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk55 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_4]
  have g55_8 : reg n55 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk55 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_8]
  have g55_9 : reg n55 (9 : Fin 32) = tbp := by rw [rk55 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_9]
  have g55_18 : reg n55 (18 : Fin 32) = out := by rw [rk55 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_18]
  have g55_19 : reg n55 (19 : Fin 32) = bp := by rw [rk55 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_19]
  have g55_20 : reg n55 (20 : Fin 32) = dg := by rw [rk55 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_20]
  have g55_21 : reg n55 (21 : Fin 32) = rootp := by rw [rk55 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_21]
  have g55_22 : reg n55 (22 : Fin 32) = ll := by rw [rk55 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_22]
  have g55_23 : reg n55 (23 : Fin 32) = sgp := by rw [rk55 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_23]
  have g55_24 : reg n55 (24 : Fin 32) = kp := by rw [rk55 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_24]
  have g55_25 : reg n55 (25 : Fin 32) = sgl := by rw [rk55 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_25]
  have g55_26 : reg n55 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rk55 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_26]
  have g55_27 : reg n55 (27 : Fin 32) = tbl := by rw [rk55 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g54_27]
  have keep_kk55 : SvKeepL B n0.mem n55.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := keep_kk54.trans K55
  clear keep_kk54
  have w55_2c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K55.w32 (by decide) (by decide)).trans w54_2c
  have w55_30 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K55.w32 (by decide) (by decide)).trans w54_30
  have w55_34 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K55.w32 (by decide) (by decide)).trans w54_34
  have w55_38 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K55.w32 (by decide) (by decide)).trans w54_38
  have w55_44 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K55.w32 (by decide) (by decide)).trans w54_44
  have w55_48 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K55.w32 (by decide) (by decide)).trans w54_48
  have w55_4c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K55.w32 (by decide) (by decide)).trans w54_4c
  have w55_50 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := (K55.w32 (by decide) (by decide)).trans w54_50
  have w55_54 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K55.w32 (by decide) (by decide)).trans w54_54
  have w55_58 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K55.w32 (by decide) (by decide)).trans w54_58
  have w55_5c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K55.w32 (by decide) (by decide)).trans w54_5c
  have w55_60 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K55.w32 (by decide) (by decide)).trans w54_60
  have w55_64 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K55.w32 (by decide) (by decide)).trans w54_64
  have w55_68 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K55.w32 (by decide) (by decide)).trans w54_68
  have w55_6c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K55.w32 (by decide) (by decide)).trans w54_6c
  have w55_70 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K55.w32 (by decide) (by decide)).trans w54_70
  have w55_74 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K55.w32 (by decide) (by decide)).trans w54_74
  have w55_78 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K55.w32 (by decide) (by decide)).trans w54_78
  have w55_7c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K55.w32 (by decide) (by decide)).trans w54_7c
  have w55_80 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K55.w32 (by decide) (by decide)).trans w54_80
  have w55_84 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K55.w32 (by decide) (by decide)).trans w54_84
  have w55_88 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K55.w32 (by decide) (by decide)).trans w54_88
  have w55_8c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K55.w32 (by decide) (by decide)).trans w54_8c
  have w55_90 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K55.w32 (by decide) (by decide)).trans w54_90
  have w55_94 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K55.w32 (by decide) (by decide)).trans w54_94
  have w55_98 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K55.w32 (by decide) (by decide)).trans w54_98
  have w55_9c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K55.w32 (by decide) (by decide)).trans w54_9c
  have w55_a0 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K55.w32 (by decide) (by decide)).trans w54_a0
  have w55_a4 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K55.w32 (by decide) (by decide)).trans w54_a4
  have w55_150 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K55.w32 (by decide) (by decide)).trans w54_150
  have w55_154 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K55.w32 (by decide) (by decide)).trans w54_154
  have w55_158 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K55.w32 (by decide) (by decide)).trans w54_158
  have w55_15c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K55.w32 (by decide) (by decide)).trans w54_15c
  clear w54_15c w54_158 w54_154 w54_150 w54_a4 w54_a0 w54_9c w54_98 w54_94 w54_90 w54_8c w54_88 w54_84 w54_80 w54_7c w54_78 w54_74 w54_70 w54_6c w54_68 w54_64 w54_60 w54_5c w54_58 w54_54 w54_50 w54_4c w54_48 w54_44 w54_38 w54_34 w54_30 w54_2c g54_13 g54_27 g54_26 g54_25 g54_24 g54_23 g54_22 g54_21 g54_20 g54_19 g54_18 g54_12 g54_11 g54_10 g54_9 g54_8 g54_4 g54_3 g54_2 V54 E54 fR54 t54 fr54 m54 s54 u54 d54
  have g55_10 : reg n55 a0 = BitVec.ofNat 32 0 := by rw [a0_55, ite_eq_right hp2]; rfl
  -- 0x718: lw
  obtain ⟨n56, d56, u56⟩ := s55.lw E55.self sv_at_718 (off' := 0x71A) (by decide)
    (by rw [g55_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s56 : St n56.mem SV n56 0x71A (reg n56) := ⟨u56.pc, rfl, fun _ => rfl⟩
  have m56 : n56.mem = n55.mem := u56.mem
  have fr56 : ∀ x, SvR B x → n56.mem x = n55.mem x := fun x _ => by rw [m56]
  have t56 : Steps n0 n56 := t55.trans (.single d56)
  have fR56 : ∀ x, SvR B x → n56.mem x = M0 x := fun x hx => (fr56 x hx).trans (fR55 x hx)
  have E56 : SvCode n56.mem := E55.fr F fr56
  have V56 : SvSaves B n56.mem v := V55.same m56
  have g56_2 : reg n56 sp = B + 0x21A0 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_2]
  have g56_3 : reg n56 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u56.regs, upd_ne (by decide) (by decide), g55_3]
  have g56_4 : reg n56 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u56.regs, upd_ne (by decide) (by decide), g55_4]
  have g56_8 : reg n56 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_8]
  have g56_9 : reg n56 (9 : Fin 32) = tbp := by rw [u56.regs, upd_ne (by decide) (by decide), g55_9]
  have g56_10 : reg n56 a0 = BitVec.ofNat 32 0x0 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_10]
  have g56_18 : reg n56 (18 : Fin 32) = out := by rw [u56.regs, upd_ne (by decide) (by decide), g55_18]
  have g56_19 : reg n56 (19 : Fin 32) = bp := by rw [u56.regs, upd_ne (by decide) (by decide), g55_19]
  have g56_20 : reg n56 (20 : Fin 32) = dg := by rw [u56.regs, upd_ne (by decide) (by decide), g55_20]
  have g56_21 : reg n56 (21 : Fin 32) = rootp := by rw [u56.regs, upd_ne (by decide) (by decide), g55_21]
  have g56_22 : reg n56 (22 : Fin 32) = ll := by rw [u56.regs, upd_ne (by decide) (by decide), g55_22]
  have g56_23 : reg n56 (23 : Fin 32) = sgp := by rw [u56.regs, upd_ne (by decide) (by decide), g55_23]
  have g56_24 : reg n56 (24 : Fin 32) = kp := by rw [u56.regs, upd_ne (by decide) (by decide), g55_24]
  have g56_25 : reg n56 (25 : Fin 32) = sgl := by rw [u56.regs, upd_ne (by decide) (by decide), g55_25]
  have g56_26 : reg n56 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [u56.regs, upd_ne (by decide) (by decide), g55_26]
  have g56_27 : reg n56 (27 : Fin 32) = tbl := by rw [u56.regs, upd_ne (by decide) (by decide), g55_27]
  have g56_11 : reg n56 a1 = BitVec.ofNat 32 0x1 := by
    rw [u56.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g55_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w55_50]
  have keep_kk56 : SvKeepL B n0.mem n56.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m56]; exact keep_kk55
  clear keep_kk55
  have w56_2c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m56]; exact w55_2c
  have w56_30 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m56]; exact w55_30
  have w56_34 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m56]; exact w55_34
  have w56_38 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m56]; exact w55_38
  have w56_44 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m56]; exact w55_44
  have w56_48 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m56]; exact w55_48
  have w56_4c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m56]; exact w55_4c
  have w56_50 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x1 := by rw [m56]; exact w55_50
  have w56_54 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m56]; exact w55_54
  have w56_58 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m56]; exact w55_58
  have w56_5c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m56]; exact w55_5c
  have w56_60 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m56]; exact w55_60
  have w56_64 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m56]; exact w55_64
  have w56_68 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m56]; exact w55_68
  have w56_6c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m56]; exact w55_6c
  have w56_70 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m56]; exact w55_70
  have w56_74 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m56]; exact w55_74
  have w56_78 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m56]; exact w55_78
  have w56_7c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m56]; exact w55_7c
  have w56_80 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m56]; exact w55_80
  have w56_84 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m56]; exact w55_84
  have w56_88 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m56]; exact w55_88
  have w56_8c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m56]; exact w55_8c
  have w56_90 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m56]; exact w55_90
  have w56_94 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m56]; exact w55_94
  have w56_98 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m56]; exact w55_98
  have w56_9c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m56]; exact w55_9c
  have w56_a0 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m56]; exact w55_a0
  have w56_a4 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m56]; exact w55_a4
  have w56_150 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m56]; exact w55_150
  have w56_154 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m56]; exact w55_154
  have w56_158 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m56]; exact w55_158
  have w56_15c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m56]; exact w55_15c
  clear w55_15c w55_158 w55_154 w55_150 w55_a4 w55_a0 w55_9c w55_98 w55_94 w55_90 w55_8c w55_88 w55_84 w55_80 w55_7c w55_78 w55_74 w55_70 w55_6c w55_68 w55_64 w55_60 w55_5c w55_58 w55_54 w55_50 w55_4c w55_48 w55_44 w55_38 w55_34 w55_30 w55_2c g55_27 g55_26 g55_25 g55_24 g55_23 g55_22 g55_21 g55_20 g55_19 g55_18 g55_9 g55_8 g55_4 g55_3 g55_2 V55 E55 fR55 t55 fr55 K55 a0_55 rk55 s55 c55
  -- 0x71A
  obtain ⟨n57, c57, u57⟩ := s56.block svDp471a E56.self svDp471a_end
    ⟨trivial, trivial⟩
  have m57 : n57.mem = n56.mem := u57.mem
  have s57 : St n57.mem SV n57 0x71C (reg n57) := ⟨u57.pc, rfl, fun _ => rfl⟩
  have rb57 : ∀ q, reg n57 q = (runBlock svDp471a (n56.mem, reg n56)).2 q := fun q => by rw [u57.regs]
  have fr57 : ∀ x, SvR B x → n57.mem x = n56.mem x := fun x _ => by rw [m57]
  have t57 : Steps n0 n57 := t56.trans c57
  have fR57 : ∀ x, SvR B x → n57.mem x = M0 x := fun x hx => (fr57 x hx).trans (fR56 x hx)
  have E57 : SvCode n57.mem := E56.fr F fr57
  have V57 : SvSaves B n57.mem v := V56.same m57
  have g57_2 : reg n57 sp = B + 0x21A0 := by
    rw [rb57, runBlock_reg _ _ _ sp s56.zero (by decide), g56_2]
  have g57_3 : reg n57 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb57, runBlock_reg _ _ _ (3 : Fin 32) s56.zero (by decide), g56_3]
  have g57_4 : reg n57 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb57, runBlock_reg _ _ _ (4 : Fin 32) s56.zero (by decide), g56_4]
  have g57_8 : reg n57 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb57, runBlock_reg _ _ _ (8 : Fin 32) s56.zero (by decide), g56_8]
  have g57_9 : reg n57 (9 : Fin 32) = tbp := by
    rw [rb57, runBlock_reg _ _ _ (9 : Fin 32) s56.zero (by decide), g56_9]
  have g57_10 : reg n57 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb57, runBlock_reg _ _ _ a0 s56.zero (by decide), g56_10]
  have g57_18 : reg n57 (18 : Fin 32) = out := by
    rw [rb57, runBlock_reg _ _ _ (18 : Fin 32) s56.zero (by decide), g56_18]
  have g57_19 : reg n57 (19 : Fin 32) = bp := by
    rw [rb57, runBlock_reg _ _ _ (19 : Fin 32) s56.zero (by decide), g56_19]
  have g57_20 : reg n57 (20 : Fin 32) = dg := by
    rw [rb57, runBlock_reg _ _ _ (20 : Fin 32) s56.zero (by decide), g56_20]
  have g57_21 : reg n57 (21 : Fin 32) = rootp := by
    rw [rb57, runBlock_reg _ _ _ (21 : Fin 32) s56.zero (by decide), g56_21]
  have g57_22 : reg n57 (22 : Fin 32) = ll := by
    rw [rb57, runBlock_reg _ _ _ (22 : Fin 32) s56.zero (by decide), g56_22]
  have g57_23 : reg n57 (23 : Fin 32) = sgp := by
    rw [rb57, runBlock_reg _ _ _ (23 : Fin 32) s56.zero (by decide), g56_23]
  have g57_24 : reg n57 (24 : Fin 32) = kp := by
    rw [rb57, runBlock_reg _ _ _ (24 : Fin 32) s56.zero (by decide), g56_24]
  have g57_25 : reg n57 (25 : Fin 32) = sgl := by
    rw [rb57, runBlock_reg _ _ _ (25 : Fin 32) s56.zero (by decide), g56_25]
  have g57_26 : reg n57 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by
    rw [rb57, runBlock_reg _ _ _ (26 : Fin 32) s56.zero (by decide), g56_26]
  have g57_27 : reg n57 (27 : Fin 32) = tbl := by
    rw [rb57, runBlock_reg _ _ _ (27 : Fin 32) s56.zero (by decide), g56_27]
  have g57_11 : reg n57 a1 = BitVec.ofNat 32 0x2 := by
    rw [rb57]; simp +decide only [runBlock, BInstr.run, svDp471a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g56_2, g56_3, g56_4, g56_8, g56_9, g56_10, g56_11, g56_18, g56_19, g56_20, g56_21, g56_22, g56_23, g56_24, g56_25, g56_26, g56_27, s56.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk57 : SvKeepL B n0.mem n57.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m57]; exact keep_kk56
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
  clear w56_15c w56_158 w56_154 w56_150 w56_a4 w56_a0 w56_9c w56_98 w56_94 w56_90 w56_8c w56_88 w56_84 w56_80 w56_7c w56_78 w56_74 w56_70 w56_6c w56_68 w56_64 w56_60 w56_5c w56_58 w56_54 w56_50 w56_4c w56_48 w56_44 w56_38 w56_34 w56_30 w56_2c g56_11 g56_27 g56_26 g56_25 g56_24 g56_23 g56_22 g56_21 g56_20 g56_19 g56_18 g56_10 g56_9 g56_8 g56_4 g56_3 g56_2 V56 E56 fR56 t56 fr56 m56 s56 u56 d56 g55_10
  -- 0x71C: sw
  obtain ⟨n58, d58, s58, fr58, K58, W58, rg58⟩ := sv_sw F E57 s57 sv_at_71c (off' := 0x71E) (c := 0x50)
    (by decide) (by rw [g57_2]; sv_addr) (by decide) (by decide)
  have t58 : Steps n0 n58 := t57.trans d58
  have fR58 : ∀ x, SvR B x → n58.mem x = M0 x := fun x hx => (fr58 x hx).trans (fR57 x hx)
  have E58 : SvCode n58.mem := E57.fr F fr58
  have V58 : SvSaves B n58.mem v := V57.keep K58 (by decide)
  have g58_2 : reg n58 sp = B + 0x21A0 := by rw [rg58 sp, g57_2]
  have g58_3 : reg n58 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg58 (3 : Fin 32), g57_3]
  have g58_4 : reg n58 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg58 (4 : Fin 32), g57_4]
  have g58_8 : reg n58 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg58 (8 : Fin 32), g57_8]
  have g58_9 : reg n58 (9 : Fin 32) = tbp := by rw [rg58 (9 : Fin 32), g57_9]
  have g58_10 : reg n58 a0 = BitVec.ofNat 32 0x0 := by rw [rg58 a0, g57_10]
  have g58_11 : reg n58 a1 = BitVec.ofNat 32 0x2 := by rw [rg58 a1, g57_11]
  have g58_18 : reg n58 (18 : Fin 32) = out := by rw [rg58 (18 : Fin 32), g57_18]
  have g58_19 : reg n58 (19 : Fin 32) = bp := by rw [rg58 (19 : Fin 32), g57_19]
  have g58_20 : reg n58 (20 : Fin 32) = dg := by rw [rg58 (20 : Fin 32), g57_20]
  have g58_21 : reg n58 (21 : Fin 32) = rootp := by rw [rg58 (21 : Fin 32), g57_21]
  have g58_22 : reg n58 (22 : Fin 32) = ll := by rw [rg58 (22 : Fin 32), g57_22]
  have g58_23 : reg n58 (23 : Fin 32) = sgp := by rw [rg58 (23 : Fin 32), g57_23]
  have g58_24 : reg n58 (24 : Fin 32) = kp := by rw [rg58 (24 : Fin 32), g57_24]
  have g58_25 : reg n58 (25 : Fin 32) = sgl := by rw [rg58 (25 : Fin 32), g57_25]
  have g58_26 : reg n58 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x71) := by rw [rg58 (26 : Fin 32), g57_26]
  have g58_27 : reg n58 (27 : Fin 32) = tbl := by rw [rg58 (27 : Fin 32), g57_27]
  have keep_kk58 : SvKeepL B n0.mem n58.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := keep_kk57.trans K58.toL
  clear keep_kk57
  have w58_2c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K58.w32 (by decide) (by decide)).trans w57_2c
  have w58_30 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K58.w32 (by decide) (by decide)).trans w57_30
  have w58_34 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K58.w32 (by decide) (by decide)).trans w57_34
  have w58_38 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K58.w32 (by decide) (by decide)).trans w57_38
  have w58_44 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K58.w32 (by decide) (by decide)).trans w57_44
  have w58_48 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K58.w32 (by decide) (by decide)).trans w57_48
  have w58_4c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K58.w32 (by decide) (by decide)).trans w57_4c
  have w58_54 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K58.w32 (by decide) (by decide)).trans w57_54
  have w58_58 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K58.w32 (by decide) (by decide)).trans w57_58
  have w58_5c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K58.w32 (by decide) (by decide)).trans w57_5c
  have w58_60 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K58.w32 (by decide) (by decide)).trans w57_60
  have w58_64 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K58.w32 (by decide) (by decide)).trans w57_64
  have w58_68 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K58.w32 (by decide) (by decide)).trans w57_68
  have w58_6c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K58.w32 (by decide) (by decide)).trans w57_6c
  have w58_70 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K58.w32 (by decide) (by decide)).trans w57_70
  have w58_74 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K58.w32 (by decide) (by decide)).trans w57_74
  have w58_78 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K58.w32 (by decide) (by decide)).trans w57_78
  have w58_7c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K58.w32 (by decide) (by decide)).trans w57_7c
  have w58_80 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K58.w32 (by decide) (by decide)).trans w57_80
  have w58_84 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K58.w32 (by decide) (by decide)).trans w57_84
  have w58_88 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K58.w32 (by decide) (by decide)).trans w57_88
  have w58_8c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K58.w32 (by decide) (by decide)).trans w57_8c
  have w58_90 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K58.w32 (by decide) (by decide)).trans w57_90
  have w58_94 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K58.w32 (by decide) (by decide)).trans w57_94
  have w58_98 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K58.w32 (by decide) (by decide)).trans w57_98
  have w58_9c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K58.w32 (by decide) (by decide)).trans w57_9c
  have w58_a0 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K58.w32 (by decide) (by decide)).trans w57_a0
  have w58_a4 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K58.w32 (by decide) (by decide)).trans w57_a4
  have w58_150 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K58.w32 (by decide) (by decide)).trans w57_150
  have w58_154 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K58.w32 (by decide) (by decide)).trans w57_154
  have w58_158 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K58.w32 (by decide) (by decide)).trans w57_158
  have w58_15c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K58.w32 (by decide) (by decide)).trans w57_15c
  have w58_50 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [W58, g57_11]
  clear w57_15c w57_158 w57_154 w57_150 w57_a4 w57_a0 w57_9c w57_98 w57_94 w57_90 w57_8c w57_88 w57_84 w57_80 w57_7c w57_78 w57_74 w57_70 w57_6c w57_68 w57_64 w57_60 w57_5c w57_58 w57_54 w57_50 w57_4c w57_48 w57_44 w57_38 w57_34 w57_30 w57_2c g57_11 g57_27 g57_26 g57_25 g57_24 g57_23 g57_22 g57_21 g57_20 g57_19 g57_18 g57_10 g57_9 g57_8 g57_4 g57_3 g57_2 V57 E57 fR57 t57 fr57 rb57 s57 m57 u57 c57
  -- 0x71E
  obtain ⟨n59, c59, u59⟩ := s58.block svDp471e E58.self svDp471e_end
    ⟨trivial, trivial⟩
  have m59 : n59.mem = n58.mem := u59.mem
  have s59 : St n59.mem SV n59 0x720 (reg n59) := ⟨u59.pc, rfl, fun _ => rfl⟩
  have rb59 : ∀ q, reg n59 q = (runBlock svDp471e (n58.mem, reg n58)).2 q := fun q => by rw [u59.regs]
  have fr59 : ∀ x, SvR B x → n59.mem x = n58.mem x := fun x _ => by rw [m59]
  have t59 : Steps n0 n59 := t58.trans c59
  have fR59 : ∀ x, SvR B x → n59.mem x = M0 x := fun x hx => (fr59 x hx).trans (fR58 x hx)
  have E59 : SvCode n59.mem := E58.fr F fr59
  have V59 : SvSaves B n59.mem v := V58.same m59
  have g59_2 : reg n59 sp = B + 0x21A0 := by
    rw [rb59, runBlock_reg _ _ _ sp s58.zero (by decide), g58_2]
  have g59_3 : reg n59 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb59, runBlock_reg _ _ _ (3 : Fin 32) s58.zero (by decide), g58_3]
  have g59_4 : reg n59 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb59, runBlock_reg _ _ _ (4 : Fin 32) s58.zero (by decide), g58_4]
  have g59_8 : reg n59 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb59, runBlock_reg _ _ _ (8 : Fin 32) s58.zero (by decide), g58_8]
  have g59_9 : reg n59 (9 : Fin 32) = tbp := by
    rw [rb59, runBlock_reg _ _ _ (9 : Fin 32) s58.zero (by decide), g58_9]
  have g59_10 : reg n59 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb59, runBlock_reg _ _ _ a0 s58.zero (by decide), g58_10]
  have g59_11 : reg n59 a1 = BitVec.ofNat 32 0x2 := by
    rw [rb59, runBlock_reg _ _ _ a1 s58.zero (by decide), g58_11]
  have g59_18 : reg n59 (18 : Fin 32) = out := by
    rw [rb59, runBlock_reg _ _ _ (18 : Fin 32) s58.zero (by decide), g58_18]
  have g59_19 : reg n59 (19 : Fin 32) = bp := by
    rw [rb59, runBlock_reg _ _ _ (19 : Fin 32) s58.zero (by decide), g58_19]
  have g59_20 : reg n59 (20 : Fin 32) = dg := by
    rw [rb59, runBlock_reg _ _ _ (20 : Fin 32) s58.zero (by decide), g58_20]
  have g59_21 : reg n59 (21 : Fin 32) = rootp := by
    rw [rb59, runBlock_reg _ _ _ (21 : Fin 32) s58.zero (by decide), g58_21]
  have g59_22 : reg n59 (22 : Fin 32) = ll := by
    rw [rb59, runBlock_reg _ _ _ (22 : Fin 32) s58.zero (by decide), g58_22]
  have g59_23 : reg n59 (23 : Fin 32) = sgp := by
    rw [rb59, runBlock_reg _ _ _ (23 : Fin 32) s58.zero (by decide), g58_23]
  have g59_24 : reg n59 (24 : Fin 32) = kp := by
    rw [rb59, runBlock_reg _ _ _ (24 : Fin 32) s58.zero (by decide), g58_24]
  have g59_25 : reg n59 (25 : Fin 32) = sgl := by
    rw [rb59, runBlock_reg _ _ _ (25 : Fin 32) s58.zero (by decide), g58_25]
  have g59_27 : reg n59 (27 : Fin 32) = tbl := by
    rw [rb59, runBlock_reg _ _ _ (27 : Fin 32) s58.zero (by decide), g58_27]
  have g59_26 : reg n59 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by
    rw [rb59]; simp +decide only [runBlock, BInstr.run, svDp471e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g58_2, g58_3, g58_4, g58_8, g58_9, g58_10, g58_11, g58_18, g58_19, g58_20, g58_21, g58_22, g58_23, g58_24, g58_25, g58_26, g58_27, s58.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk59 : SvKeepL B n0.mem n59.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m59]; exact keep_kk58
  clear keep_kk58
  have w59_2c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m59]; exact w58_2c
  have w59_30 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m59]; exact w58_30
  have w59_34 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m59]; exact w58_34
  have w59_38 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m59]; exact w58_38
  have w59_44 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m59]; exact w58_44
  have w59_48 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m59]; exact w58_48
  have w59_4c : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m59]; exact w58_4c
  have w59_50 : memLoad32 n59.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m59]; exact w58_50
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
  clear w58_50 w58_15c w58_158 w58_154 w58_150 w58_a4 w58_a0 w58_9c w58_98 w58_94 w58_90 w58_8c w58_88 w58_84 w58_80 w58_7c w58_78 w58_74 w58_70 w58_6c w58_68 w58_64 w58_60 w58_5c w58_58 w58_54 w58_4c w58_48 w58_44 w58_38 w58_34 w58_30 w58_2c g58_27 g58_26 g58_25 g58_24 g58_23 g58_22 g58_21 g58_20 g58_19 g58_18 g58_11 g58_10 g58_9 g58_8 g58_4 g58_3 g58_2 V58 E58 fR58 t58 rg58 W58 K58 fr58 s58 d58
  -- 0x720: branch, taken
  obtain ⟨n60, d60, u60⟩ := s59.taken E59.self 0x6FE sv_at_720
    (by decide) (by rw [g59_10, s59.zero]; decide)
  have s60 : St n60.mem SV n60 0x6FE (reg n60) := ⟨u60.pc, rfl, fun _ => rfl⟩
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
  have g60_10 : reg n60 a0 = BitVec.ofNat 32 0x0 := by rw [u60.regs, g59_10]
  have g60_11 : reg n60 a1 = BitVec.ofNat 32 0x2 := by rw [u60.regs, g59_11]
  have g60_18 : reg n60 (18 : Fin 32) = out := by rw [u60.regs, g59_18]
  have g60_19 : reg n60 (19 : Fin 32) = bp := by rw [u60.regs, g59_19]
  have g60_20 : reg n60 (20 : Fin 32) = dg := by rw [u60.regs, g59_20]
  have g60_21 : reg n60 (21 : Fin 32) = rootp := by rw [u60.regs, g59_21]
  have g60_22 : reg n60 (22 : Fin 32) = ll := by rw [u60.regs, g59_22]
  have g60_23 : reg n60 (23 : Fin 32) = sgp := by rw [u60.regs, g59_23]
  have g60_24 : reg n60 (24 : Fin 32) = kp := by rw [u60.regs, g59_24]
  have g60_25 : reg n60 (25 : Fin 32) = sgl := by rw [u60.regs, g59_25]
  have g60_26 : reg n60 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by rw [u60.regs, g59_26]
  have g60_27 : reg n60 (27 : Fin 32) = tbl := by rw [u60.regs, g59_27]
  have keep_kk60 : SvKeepL B n0.mem n60.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m60]; exact keep_kk59
  clear keep_kk59
  have w60_2c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m60]; exact w59_2c
  have w60_30 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m60]; exact w59_30
  have w60_34 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m60]; exact w59_34
  have w60_38 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m60]; exact w59_38
  have w60_44 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m60]; exact w59_44
  have w60_48 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m60]; exact w59_48
  have w60_4c : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m60]; exact w59_4c
  have w60_50 : memLoad32 n60.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m60]; exact w59_50
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
  clear w59_15c w59_158 w59_154 w59_150 w59_a4 w59_a0 w59_9c w59_98 w59_94 w59_90 w59_8c w59_88 w59_84 w59_80 w59_7c w59_78 w59_74 w59_70 w59_6c w59_68 w59_64 w59_60 w59_5c w59_58 w59_54 w59_50 w59_4c w59_48 w59_44 w59_38 w59_34 w59_30 w59_2c g59_26 g59_27 g59_25 g59_24 g59_23 g59_22 g59_21 g59_20 g59_19 g59_18 g59_11 g59_10 g59_9 g59_8 g59_4 g59_3 g59_2 V59 E59 fR59 t59 fr59 rb59 s59 m59 u59 c59
  -- 0x6FE
  obtain ⟨n61, c61, u61⟩ := s60.block svDp46fe E60.self svDp46fe_end
    ⟨trivial, trivial⟩
  have m61 : n61.mem = n60.mem := u61.mem
  have s61 : St n61.mem SV n61 0x700 (reg n61) := ⟨u61.pc, rfl, fun _ => rfl⟩
  have rb61 : ∀ q, reg n61 q = (runBlock svDp46fe (n60.mem, reg n60)).2 q := fun q => by rw [u61.regs]
  have fr61 : ∀ x, SvR B x → n61.mem x = n60.mem x := fun x _ => by rw [m61]
  have t61 : Steps n0 n61 := t60.trans c61
  have fR61 : ∀ x, SvR B x → n61.mem x = M0 x := fun x hx => (fr61 x hx).trans (fR60 x hx)
  have E61 : SvCode n61.mem := E60.fr F fr61
  have V61 : SvSaves B n61.mem v := V60.same m61
  have g61_2 : reg n61 sp = B + 0x21A0 := by
    rw [rb61, runBlock_reg _ _ _ sp s60.zero (by decide), g60_2]
  have g61_3 : reg n61 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb61, runBlock_reg _ _ _ (3 : Fin 32) s60.zero (by decide), g60_3]
  have g61_4 : reg n61 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb61, runBlock_reg _ _ _ (4 : Fin 32) s60.zero (by decide), g60_4]
  have g61_8 : reg n61 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb61, runBlock_reg _ _ _ (8 : Fin 32) s60.zero (by decide), g60_8]
  have g61_9 : reg n61 (9 : Fin 32) = tbp := by
    rw [rb61, runBlock_reg _ _ _ (9 : Fin 32) s60.zero (by decide), g60_9]
  have g61_11 : reg n61 a1 = BitVec.ofNat 32 0x2 := by
    rw [rb61, runBlock_reg _ _ _ a1 s60.zero (by decide), g60_11]
  have g61_18 : reg n61 (18 : Fin 32) = out := by
    rw [rb61, runBlock_reg _ _ _ (18 : Fin 32) s60.zero (by decide), g60_18]
  have g61_19 : reg n61 (19 : Fin 32) = bp := by
    rw [rb61, runBlock_reg _ _ _ (19 : Fin 32) s60.zero (by decide), g60_19]
  have g61_20 : reg n61 (20 : Fin 32) = dg := by
    rw [rb61, runBlock_reg _ _ _ (20 : Fin 32) s60.zero (by decide), g60_20]
  have g61_21 : reg n61 (21 : Fin 32) = rootp := by
    rw [rb61, runBlock_reg _ _ _ (21 : Fin 32) s60.zero (by decide), g60_21]
  have g61_22 : reg n61 (22 : Fin 32) = ll := by
    rw [rb61, runBlock_reg _ _ _ (22 : Fin 32) s60.zero (by decide), g60_22]
  have g61_23 : reg n61 (23 : Fin 32) = sgp := by
    rw [rb61, runBlock_reg _ _ _ (23 : Fin 32) s60.zero (by decide), g60_23]
  have g61_24 : reg n61 (24 : Fin 32) = kp := by
    rw [rb61, runBlock_reg _ _ _ (24 : Fin 32) s60.zero (by decide), g60_24]
  have g61_25 : reg n61 (25 : Fin 32) = sgl := by
    rw [rb61, runBlock_reg _ _ _ (25 : Fin 32) s60.zero (by decide), g60_25]
  have g61_26 : reg n61 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by
    rw [rb61, runBlock_reg _ _ _ (26 : Fin 32) s60.zero (by decide), g60_26]
  have g61_27 : reg n61 (27 : Fin 32) = tbl := by
    rw [rb61, runBlock_reg _ _ _ (27 : Fin 32) s60.zero (by decide), g60_27]
  have g61_10 : reg n61 a0 = BitVec.ofNat 32 0x4 := by
    rw [rb61]; simp +decide only [runBlock, BInstr.run, svDp46fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g60_2, g60_3, g60_4, g60_8, g60_9, g60_10, g60_11, g60_18, g60_19, g60_20, g60_21, g60_22, g60_23, g60_24, g60_25, g60_26, g60_27, s60.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk61 : SvKeepL B n0.mem n61.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m61]; exact keep_kk60
  clear keep_kk60
  have w61_2c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m61]; exact w60_2c
  have w61_30 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m61]; exact w60_30
  have w61_34 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m61]; exact w60_34
  have w61_38 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m61]; exact w60_38
  have w61_44 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m61]; exact w60_44
  have w61_48 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m61]; exact w60_48
  have w61_4c : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m61]; exact w60_4c
  have w61_50 : memLoad32 n61.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m61]; exact w60_50
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
  clear w60_15c w60_158 w60_154 w60_150 w60_a4 w60_a0 w60_9c w60_98 w60_94 w60_90 w60_8c w60_88 w60_84 w60_80 w60_7c w60_78 w60_74 w60_70 w60_6c w60_68 w60_64 w60_60 w60_5c w60_58 w60_54 w60_50 w60_4c w60_48 w60_44 w60_38 w60_34 w60_30 w60_2c g60_27 g60_26 g60_25 g60_24 g60_23 g60_22 g60_21 g60_20 g60_19 g60_18 g60_11 g60_10 g60_9 g60_8 g60_4 g60_3 g60_2 V60 E60 fR60 t60 fr60 m60 s60 u60 d60
  -- 0x700: lw
  obtain ⟨n62, d62, u62⟩ := s61.lw E61.self sv_at_700 (off' := 0x702) (by decide)
    (by rw [g61_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s62 : St n62.mem SV n62 0x702 (reg n62) := ⟨u62.pc, rfl, fun _ => rfl⟩
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
  have g62_10 : reg n62 a0 = BitVec.ofNat 32 0x4 := by rw [u62.regs, upd_ne (by decide) (by decide), g61_10]
  have g62_18 : reg n62 (18 : Fin 32) = out := by rw [u62.regs, upd_ne (by decide) (by decide), g61_18]
  have g62_19 : reg n62 (19 : Fin 32) = bp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_19]
  have g62_20 : reg n62 (20 : Fin 32) = dg := by rw [u62.regs, upd_ne (by decide) (by decide), g61_20]
  have g62_21 : reg n62 (21 : Fin 32) = rootp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_21]
  have g62_22 : reg n62 (22 : Fin 32) = ll := by rw [u62.regs, upd_ne (by decide) (by decide), g61_22]
  have g62_23 : reg n62 (23 : Fin 32) = sgp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_23]
  have g62_24 : reg n62 (24 : Fin 32) = kp := by rw [u62.regs, upd_ne (by decide) (by decide), g61_24]
  have g62_25 : reg n62 (25 : Fin 32) = sgl := by rw [u62.regs, upd_ne (by decide) (by decide), g61_25]
  have g62_26 : reg n62 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by rw [u62.regs, upd_ne (by decide) (by decide), g61_26]
  have g62_27 : reg n62 (27 : Fin 32) = tbl := by rw [u62.regs, upd_ne (by decide) (by decide), g61_27]
  have g62_11 : reg n62 a1 = BitVec.ofNat 32 0x2 := by
    rw [u62.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g61_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w61_50]
  have keep_kk62 : SvKeepL B n0.mem n62.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m62]; exact keep_kk61
  clear keep_kk61
  have w62_2c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m62]; exact w61_2c
  have w62_30 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m62]; exact w61_30
  have w62_34 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m62]; exact w61_34
  have w62_38 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m62]; exact w61_38
  have w62_44 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m62]; exact w61_44
  have w62_48 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m62]; exact w61_48
  have w62_4c : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m62]; exact w61_4c
  have w62_50 : memLoad32 n62.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m62]; exact w61_50
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
  clear w61_15c w61_158 w61_154 w61_150 w61_a4 w61_a0 w61_9c w61_98 w61_94 w61_90 w61_8c w61_88 w61_84 w61_80 w61_7c w61_78 w61_74 w61_70 w61_6c w61_68 w61_64 w61_60 w61_5c w61_58 w61_54 w61_50 w61_4c w61_48 w61_44 w61_38 w61_34 w61_30 w61_2c g61_10 g61_27 g61_26 g61_25 g61_24 g61_23 g61_22 g61_21 g61_20 g61_19 g61_18 g61_11 g61_9 g61_8 g61_4 g61_3 g61_2 V61 E61 fR61 t61 fr61 rb61 s61 m61 u61 c61
  -- 0x702: branch, not taken
  obtain ⟨n63, d63, u63⟩ := s62.notTaken E62.self 0x706 sv_at_702
    (by decide) (by rw [g62_11, g62_10]; decide)
  have s63 : St n63.mem SV n63 0x706 (reg n63) := ⟨u63.pc, rfl, fun _ => rfl⟩
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
  have g63_10 : reg n63 a0 = BitVec.ofNat 32 0x4 := by rw [u63.regs, g62_10]
  have g63_11 : reg n63 a1 = BitVec.ofNat 32 0x2 := by rw [u63.regs, g62_11]
  have g63_18 : reg n63 (18 : Fin 32) = out := by rw [u63.regs, g62_18]
  have g63_19 : reg n63 (19 : Fin 32) = bp := by rw [u63.regs, g62_19]
  have g63_20 : reg n63 (20 : Fin 32) = dg := by rw [u63.regs, g62_20]
  have g63_21 : reg n63 (21 : Fin 32) = rootp := by rw [u63.regs, g62_21]
  have g63_22 : reg n63 (22 : Fin 32) = ll := by rw [u63.regs, g62_22]
  have g63_23 : reg n63 (23 : Fin 32) = sgp := by rw [u63.regs, g62_23]
  have g63_24 : reg n63 (24 : Fin 32) = kp := by rw [u63.regs, g62_24]
  have g63_25 : reg n63 (25 : Fin 32) = sgl := by rw [u63.regs, g62_25]
  have g63_26 : reg n63 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by rw [u63.regs, g62_26]
  have g63_27 : reg n63 (27 : Fin 32) = tbl := by rw [u63.regs, g62_27]
  have keep_kk63 : SvKeepL B n0.mem n63.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m63]; exact keep_kk62
  clear keep_kk62
  have w63_2c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m63]; exact w62_2c
  have w63_30 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m63]; exact w62_30
  have w63_34 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m63]; exact w62_34
  have w63_38 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m63]; exact w62_38
  have w63_44 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m63]; exact w62_44
  have w63_48 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m63]; exact w62_48
  have w63_4c : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m63]; exact w62_4c
  have w63_50 : memLoad32 n63.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m63]; exact w62_50
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
  clear w62_15c w62_158 w62_154 w62_150 w62_a4 w62_a0 w62_9c w62_98 w62_94 w62_90 w62_8c w62_88 w62_84 w62_80 w62_7c w62_78 w62_74 w62_70 w62_6c w62_68 w62_64 w62_60 w62_5c w62_58 w62_54 w62_50 w62_4c w62_48 w62_44 w62_38 w62_34 w62_30 w62_2c g62_11 g62_27 g62_26 g62_25 g62_24 g62_23 g62_22 g62_21 g62_20 g62_19 g62_18 g62_10 g62_9 g62_8 g62_4 g62_3 g62_2 V62 E62 fR62 t62 fr62 m62 s62 u62 d62
  -- 0x706: lw of a constant
  obtain ⟨n64, d64, u64⟩ := s63.lw E63.self sv_at_706 (off' := 0x70A) (by decide)
    (by rw [g63_26]; decide)
  have s64 : St n64.mem SV n64 0x70A (reg n64) := ⟨u64.pc, rfl, fun _ => rfl⟩
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
  have g64_11 : reg n64 a1 = BitVec.ofNat 32 0x2 := by rw [u64.regs, upd_ne (by decide) (by decide), g63_11]
  have g64_18 : reg n64 (18 : Fin 32) = out := by rw [u64.regs, upd_ne (by decide) (by decide), g63_18]
  have g64_19 : reg n64 (19 : Fin 32) = bp := by rw [u64.regs, upd_ne (by decide) (by decide), g63_19]
  have g64_20 : reg n64 (20 : Fin 32) = dg := by rw [u64.regs, upd_ne (by decide) (by decide), g63_20]
  have g64_21 : reg n64 (21 : Fin 32) = rootp := by rw [u64.regs, upd_ne (by decide) (by decide), g63_21]
  have g64_22 : reg n64 (22 : Fin 32) = ll := by rw [u64.regs, upd_ne (by decide) (by decide), g63_22]
  have g64_23 : reg n64 (23 : Fin 32) = sgp := by rw [u64.regs, upd_ne (by decide) (by decide), g63_23]
  have g64_24 : reg n64 (24 : Fin 32) = kp := by rw [u64.regs, upd_ne (by decide) (by decide), g63_24]
  have g64_25 : reg n64 (25 : Fin 32) = sgl := by rw [u64.regs, upd_ne (by decide) (by decide), g63_25]
  have g64_26 : reg n64 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by rw [u64.regs, upd_ne (by decide) (by decide), g63_26]
  have g64_27 : reg n64 (27 : Fin 32) = tbl := by rw [u64.regs, upd_ne (by decide) (by decide), g63_27]
  have g64_10 : reg n64 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x4B) := by
    rw [u64.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g63_26, show BitVec.ofNat 32 (img% svConstExtAddress + 0x79) + 0x0 = BitVec.ofNat 32 svConstExtAddress + BitVec.ofNat 32 0x79 by decide]
    exact CodeIn.w32 (SvData.sv FW SD0 fR63).ext (by decide) (by decide)
  have keep_kk64 : SvKeepL B n0.mem n64.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m64]; exact keep_kk63
  clear keep_kk63
  have w64_2c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m64]; exact w63_2c
  have w64_30 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m64]; exact w63_30
  have w64_34 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m64]; exact w63_34
  have w64_38 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m64]; exact w63_38
  have w64_44 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m64]; exact w63_44
  have w64_48 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m64]; exact w63_48
  have w64_4c : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m64]; exact w63_4c
  have w64_50 : memLoad32 n64.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m64]; exact w63_50
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
  clear w63_15c w63_158 w63_154 w63_150 w63_a4 w63_a0 w63_9c w63_98 w63_94 w63_90 w63_8c w63_88 w63_84 w63_80 w63_7c w63_78 w63_74 w63_70 w63_6c w63_68 w63_64 w63_60 w63_5c w63_58 w63_54 w63_50 w63_4c w63_48 w63_44 w63_38 w63_34 w63_30 w63_2c g63_27 g63_26 g63_25 g63_24 g63_23 g63_22 g63_21 g63_20 g63_19 g63_18 g63_11 g63_10 g63_9 g63_8 g63_4 g63_3 g63_2 V63 E63 fR63 t63 fr63 m63 s63 u63 d63
  -- 0x70A
  obtain ⟨n65, c65, u65⟩ := s64.block svDp470a E64.self svDp470a_end
    ⟨trivial, trivial⟩
  have m65 : n65.mem = n64.mem := u65.mem
  have s65 : St n65.mem SV n65 0x70C (reg n65) := ⟨u65.pc, rfl, fun _ => rfl⟩
  have rb65 : ∀ q, reg n65 q = (runBlock svDp470a (n64.mem, reg n64)).2 q := fun q => by rw [u65.regs]
  have fr65 : ∀ x, SvR B x → n65.mem x = n64.mem x := fun x _ => by rw [m65]
  have t65 : Steps n0 n65 := t64.trans c65
  have fR65 : ∀ x, SvR B x → n65.mem x = M0 x := fun x hx => (fr65 x hx).trans (fR64 x hx)
  have E65 : SvCode n65.mem := E64.fr F fr65
  have V65 : SvSaves B n65.mem v := V64.same m65
  have g65_2 : reg n65 sp = B + 0x21A0 := by
    rw [rb65, runBlock_reg _ _ _ sp s64.zero (by decide), g64_2]
  have g65_3 : reg n65 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb65, runBlock_reg _ _ _ (3 : Fin 32) s64.zero (by decide), g64_3]
  have g65_4 : reg n65 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb65, runBlock_reg _ _ _ (4 : Fin 32) s64.zero (by decide), g64_4]
  have g65_8 : reg n65 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb65, runBlock_reg _ _ _ (8 : Fin 32) s64.zero (by decide), g64_8]
  have g65_9 : reg n65 (9 : Fin 32) = tbp := by
    rw [rb65, runBlock_reg _ _ _ (9 : Fin 32) s64.zero (by decide), g64_9]
  have g65_10 : reg n65 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x4B) := by
    rw [rb65, runBlock_reg _ _ _ a0 s64.zero (by decide), g64_10]
  have g65_18 : reg n65 (18 : Fin 32) = out := by
    rw [rb65, runBlock_reg _ _ _ (18 : Fin 32) s64.zero (by decide), g64_18]
  have g65_19 : reg n65 (19 : Fin 32) = bp := by
    rw [rb65, runBlock_reg _ _ _ (19 : Fin 32) s64.zero (by decide), g64_19]
  have g65_20 : reg n65 (20 : Fin 32) = dg := by
    rw [rb65, runBlock_reg _ _ _ (20 : Fin 32) s64.zero (by decide), g64_20]
  have g65_21 : reg n65 (21 : Fin 32) = rootp := by
    rw [rb65, runBlock_reg _ _ _ (21 : Fin 32) s64.zero (by decide), g64_21]
  have g65_22 : reg n65 (22 : Fin 32) = ll := by
    rw [rb65, runBlock_reg _ _ _ (22 : Fin 32) s64.zero (by decide), g64_22]
  have g65_23 : reg n65 (23 : Fin 32) = sgp := by
    rw [rb65, runBlock_reg _ _ _ (23 : Fin 32) s64.zero (by decide), g64_23]
  have g65_24 : reg n65 (24 : Fin 32) = kp := by
    rw [rb65, runBlock_reg _ _ _ (24 : Fin 32) s64.zero (by decide), g64_24]
  have g65_25 : reg n65 (25 : Fin 32) = sgl := by
    rw [rb65, runBlock_reg _ _ _ (25 : Fin 32) s64.zero (by decide), g64_25]
  have g65_26 : reg n65 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by
    rw [rb65, runBlock_reg _ _ _ (26 : Fin 32) s64.zero (by decide), g64_26]
  have g65_27 : reg n65 (27 : Fin 32) = tbl := by
    rw [rb65, runBlock_reg _ _ _ (27 : Fin 32) s64.zero (by decide), g64_27]
  have g65_11 : reg n65 a1 = BitVec.ofNat 32 0xA := by
    rw [rb65]; simp +decide only [runBlock, BInstr.run, svDp470a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g64_2, g64_3, g64_4, g64_8, g64_9, g64_10, g64_11, g64_18, g64_19, g64_20, g64_21, g64_22, g64_23, g64_24, g64_25, g64_26, g64_27, s64.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk65 : SvKeepL B n0.mem n65.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m65]; exact keep_kk64
  clear keep_kk64
  have w65_2c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m65]; exact w64_2c
  have w65_30 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m65]; exact w64_30
  have w65_34 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m65]; exact w64_34
  have w65_38 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m65]; exact w64_38
  have w65_44 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m65]; exact w64_44
  have w65_48 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m65]; exact w64_48
  have w65_4c : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m65]; exact w64_4c
  have w65_50 : memLoad32 n65.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m65]; exact w64_50
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
  clear w64_15c w64_158 w64_154 w64_150 w64_a4 w64_a0 w64_9c w64_98 w64_94 w64_90 w64_8c w64_88 w64_84 w64_80 w64_7c w64_78 w64_74 w64_70 w64_6c w64_68 w64_64 w64_60 w64_5c w64_58 w64_54 w64_50 w64_4c w64_48 w64_44 w64_38 w64_34 w64_30 w64_2c g64_10 g64_27 g64_26 g64_25 g64_24 g64_23 g64_22 g64_21 g64_20 g64_19 g64_18 g64_11 g64_9 g64_8 g64_4 g64_3 g64_2 V64 E64 fR64 t64 fr64 m64 s64 u64 d64
  -- 0x70C: lw
  obtain ⟨n66, d66, u66⟩ := s65.lw E65.self sv_at_70c (off' := 0x70E) (by decide)
    (by rw [g65_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s66 : St n66.mem SV n66 0x70E (reg n66) := ⟨u66.pc, rfl, fun _ => rfl⟩
  have m66 : n66.mem = n65.mem := u66.mem
  have fr66 : ∀ x, SvR B x → n66.mem x = n65.mem x := fun x _ => by rw [m66]
  have t66 : Steps n0 n66 := t65.trans (.single d66)
  have fR66 : ∀ x, SvR B x → n66.mem x = M0 x := fun x hx => (fr66 x hx).trans (fR65 x hx)
  have E66 : SvCode n66.mem := E65.fr F fr66
  have V66 : SvSaves B n66.mem v := V65.same m66
  have g66_2 : reg n66 sp = B + 0x21A0 := by rw [u66.regs, upd_ne (by decide) (by decide), g65_2]
  have g66_3 : reg n66 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u66.regs, upd_ne (by decide) (by decide), g65_3]
  have g66_4 : reg n66 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u66.regs, upd_ne (by decide) (by decide), g65_4]
  have g66_8 : reg n66 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u66.regs, upd_ne (by decide) (by decide), g65_8]
  have g66_9 : reg n66 (9 : Fin 32) = tbp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_9]
  have g66_10 : reg n66 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x4B) := by rw [u66.regs, upd_ne (by decide) (by decide), g65_10]
  have g66_11 : reg n66 a1 = BitVec.ofNat 32 0xA := by rw [u66.regs, upd_ne (by decide) (by decide), g65_11]
  have g66_18 : reg n66 (18 : Fin 32) = out := by rw [u66.regs, upd_ne (by decide) (by decide), g65_18]
  have g66_19 : reg n66 (19 : Fin 32) = bp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_19]
  have g66_20 : reg n66 (20 : Fin 32) = dg := by rw [u66.regs, upd_ne (by decide) (by decide), g65_20]
  have g66_21 : reg n66 (21 : Fin 32) = rootp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_21]
  have g66_22 : reg n66 (22 : Fin 32) = ll := by rw [u66.regs, upd_ne (by decide) (by decide), g65_22]
  have g66_23 : reg n66 (23 : Fin 32) = sgp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_23]
  have g66_24 : reg n66 (24 : Fin 32) = kp := by rw [u66.regs, upd_ne (by decide) (by decide), g65_24]
  have g66_25 : reg n66 (25 : Fin 32) = sgl := by rw [u66.regs, upd_ne (by decide) (by decide), g65_25]
  have g66_26 : reg n66 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by rw [u66.regs, upd_ne (by decide) (by decide), g65_26]
  have g66_27 : reg n66 (27 : Fin 32) = tbl := by rw [u66.regs, upd_ne (by decide) (by decide), g65_27]
  have g66_12 : reg n66 a2 = op := by
    rw [u66.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g65_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w65_4c]
  have keep_kk66 : SvKeepL B n0.mem n66.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m66]; exact keep_kk65
  clear keep_kk65
  have w66_2c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m66]; exact w65_2c
  have w66_30 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m66]; exact w65_30
  have w66_34 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m66]; exact w65_34
  have w66_38 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m66]; exact w65_38
  have w66_44 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m66]; exact w65_44
  have w66_48 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m66]; exact w65_48
  have w66_4c : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m66]; exact w65_4c
  have w66_50 : memLoad32 n66.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m66]; exact w65_50
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
  clear w65_15c w65_158 w65_154 w65_150 w65_a4 w65_a0 w65_9c w65_98 w65_94 w65_90 w65_8c w65_88 w65_84 w65_80 w65_7c w65_78 w65_74 w65_70 w65_6c w65_68 w65_64 w65_60 w65_5c w65_58 w65_54 w65_50 w65_4c w65_48 w65_44 w65_38 w65_34 w65_30 w65_2c g65_11 g65_27 g65_26 g65_25 g65_24 g65_23 g65_22 g65_21 g65_20 g65_19 g65_18 g65_10 g65_9 g65_8 g65_4 g65_3 g65_2 V65 E65 fR65 t65 fr65 rb65 s65 m65 u65 c65
  -- 0x70E: lw
  obtain ⟨n67, d67, u67⟩ := s66.lw E66.self sv_at_70e (off' := 0x710) (by decide)
    (by rw [g66_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s67 : St n67.mem SV n67 0x710 (reg n67) := ⟨u67.pc, rfl, fun _ => rfl⟩
  have m67 : n67.mem = n66.mem := u67.mem
  have fr67 : ∀ x, SvR B x → n67.mem x = n66.mem x := fun x _ => by rw [m67]
  have t67 : Steps n0 n67 := t66.trans (.single d67)
  have fR67 : ∀ x, SvR B x → n67.mem x = M0 x := fun x hx => (fr67 x hx).trans (fR66 x hx)
  have E67 : SvCode n67.mem := E66.fr F fr67
  have V67 : SvSaves B n67.mem v := V66.same m67
  have g67_2 : reg n67 sp = B + 0x21A0 := by rw [u67.regs, upd_ne (by decide) (by decide), g66_2]
  have g67_3 : reg n67 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u67.regs, upd_ne (by decide) (by decide), g66_3]
  have g67_4 : reg n67 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u67.regs, upd_ne (by decide) (by decide), g66_4]
  have g67_8 : reg n67 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u67.regs, upd_ne (by decide) (by decide), g66_8]
  have g67_9 : reg n67 (9 : Fin 32) = tbp := by rw [u67.regs, upd_ne (by decide) (by decide), g66_9]
  have g67_10 : reg n67 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x4B) := by rw [u67.regs, upd_ne (by decide) (by decide), g66_10]
  have g67_11 : reg n67 a1 = BitVec.ofNat 32 0xA := by rw [u67.regs, upd_ne (by decide) (by decide), g66_11]
  have g67_12 : reg n67 a2 = op := by rw [u67.regs, upd_ne (by decide) (by decide), g66_12]
  have g67_18 : reg n67 (18 : Fin 32) = out := by rw [u67.regs, upd_ne (by decide) (by decide), g66_18]
  have g67_19 : reg n67 (19 : Fin 32) = bp := by rw [u67.regs, upd_ne (by decide) (by decide), g66_19]
  have g67_20 : reg n67 (20 : Fin 32) = dg := by rw [u67.regs, upd_ne (by decide) (by decide), g66_20]
  have g67_21 : reg n67 (21 : Fin 32) = rootp := by rw [u67.regs, upd_ne (by decide) (by decide), g66_21]
  have g67_22 : reg n67 (22 : Fin 32) = ll := by rw [u67.regs, upd_ne (by decide) (by decide), g66_22]
  have g67_23 : reg n67 (23 : Fin 32) = sgp := by rw [u67.regs, upd_ne (by decide) (by decide), g66_23]
  have g67_24 : reg n67 (24 : Fin 32) = kp := by rw [u67.regs, upd_ne (by decide) (by decide), g66_24]
  have g67_25 : reg n67 (25 : Fin 32) = sgl := by rw [u67.regs, upd_ne (by decide) (by decide), g66_25]
  have g67_26 : reg n67 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by rw [u67.regs, upd_ne (by decide) (by decide), g66_26]
  have g67_27 : reg n67 (27 : Fin 32) = tbl := by rw [u67.regs, upd_ne (by decide) (by decide), g66_27]
  have g67_13 : reg n67 a3 = ol := by
    rw [u67.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g66_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w66_48]
  have keep_kk67 : SvKeepL B n0.mem n67.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m67]; exact keep_kk66
  clear keep_kk66
  have w67_2c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m67]; exact w66_2c
  have w67_30 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m67]; exact w66_30
  have w67_34 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m67]; exact w66_34
  have w67_38 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m67]; exact w66_38
  have w67_44 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m67]; exact w66_44
  have w67_48 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m67]; exact w66_48
  have w67_4c : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m67]; exact w66_4c
  have w67_50 : memLoad32 n67.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m67]; exact w66_50
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
  clear w66_15c w66_158 w66_154 w66_150 w66_a4 w66_a0 w66_9c w66_98 w66_94 w66_90 w66_8c w66_88 w66_84 w66_80 w66_7c w66_78 w66_74 w66_70 w66_6c w66_68 w66_64 w66_60 w66_5c w66_58 w66_54 w66_50 w66_4c w66_48 w66_44 w66_38 w66_34 w66_30 w66_2c g66_12 g66_27 g66_26 g66_25 g66_24 g66_23 g66_22 g66_21 g66_20 g66_19 g66_18 g66_11 g66_10 g66_9 g66_8 g66_4 g66_3 g66_2 V66 E66 fR66 t66 fr66 m66 s66 u66 d66
  -- 0x710: sv_seqEqF
  obtain ⟨n68, c68, s68, rk68, a0_68, K68, fr68⟩ := sv_seqEqF (pl := 10) (ql := ol.toNat)
    F E67 s67 sv_at_710 sv_at_714 (by decide) (by decide) g67_2
    g67_10 g67_11 g67_12 (by rw [g67_13, ofNat_toNat_self]) (.inr ⟨by decide, by decide⟩) (.inl oid_in)
  have t68 : Steps n0 n68 := t67.trans c68
  have fR68 : ∀ x, SvR B x → n68.mem x = M0 x := fun x hx => (fr68 x hx).trans (fR67 x hx)
  have E68 : SvCode n68.mem := E67.fr F fr68
  have V68 : SvSaves B n68.mem v := V67.keepL K68 (by decide)
  rw [sv_mbRo FW fR67 (.inr ⟨by decide, by decide⟩), sv_mbRo FW fR67 (.inl oid_in)] at a0_68
  have g68_2 : reg n68 sp = B + 0x21A0 := by rw [rk68 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_2]
  have g68_3 : reg n68 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk68 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_3]
  have g68_4 : reg n68 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk68 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_4]
  have g68_8 : reg n68 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk68 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_8]
  have g68_9 : reg n68 (9 : Fin 32) = tbp := by rw [rk68 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_9]
  have g68_18 : reg n68 (18 : Fin 32) = out := by rw [rk68 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_18]
  have g68_19 : reg n68 (19 : Fin 32) = bp := by rw [rk68 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_19]
  have g68_20 : reg n68 (20 : Fin 32) = dg := by rw [rk68 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_20]
  have g68_21 : reg n68 (21 : Fin 32) = rootp := by rw [rk68 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_21]
  have g68_22 : reg n68 (22 : Fin 32) = ll := by rw [rk68 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_22]
  have g68_23 : reg n68 (23 : Fin 32) = sgp := by rw [rk68 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_23]
  have g68_24 : reg n68 (24 : Fin 32) = kp := by rw [rk68 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_24]
  have g68_25 : reg n68 (25 : Fin 32) = sgl := by rw [rk68 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_25]
  have g68_26 : reg n68 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by rw [rk68 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_26]
  have g68_27 : reg n68 (27 : Fin 32) = tbl := by rw [rk68 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g67_27]
  have keep_kk68 : SvKeepL B n0.mem n68.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := keep_kk67.trans K68
  clear keep_kk67
  have w68_2c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K68.w32 (by decide) (by decide)).trans w67_2c
  have w68_30 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K68.w32 (by decide) (by decide)).trans w67_30
  have w68_34 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K68.w32 (by decide) (by decide)).trans w67_34
  have w68_38 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K68.w32 (by decide) (by decide)).trans w67_38
  have w68_44 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K68.w32 (by decide) (by decide)).trans w67_44
  have w68_48 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K68.w32 (by decide) (by decide)).trans w67_48
  have w68_4c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K68.w32 (by decide) (by decide)).trans w67_4c
  have w68_50 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := (K68.w32 (by decide) (by decide)).trans w67_50
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
  have w68_88 : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K68.w32 (by decide) (by decide)).trans w67_88
  have w68_8c : memLoad32 n68.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K68.w32 (by decide) (by decide)).trans w67_8c
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
  clear w67_15c w67_158 w67_154 w67_150 w67_a4 w67_a0 w67_9c w67_98 w67_94 w67_90 w67_8c w67_88 w67_84 w67_80 w67_7c w67_78 w67_74 w67_70 w67_6c w67_68 w67_64 w67_60 w67_5c w67_58 w67_54 w67_50 w67_4c w67_48 w67_44 w67_38 w67_34 w67_30 w67_2c g67_13 g67_27 g67_26 g67_25 g67_24 g67_23 g67_22 g67_21 g67_20 g67_19 g67_18 g67_12 g67_11 g67_10 g67_9 g67_8 g67_4 g67_3 g67_2 V67 E67 fR67 t67 fr67 m67 s67 u67 d67
  have g68_10 : reg n68 a0 = BitVec.ofNat 32 0 := by rw [a0_68, ite_eq_right hp3]; rfl
  -- 0x718: lw
  obtain ⟨n69, d69, u69⟩ := s68.lw E68.self sv_at_718 (off' := 0x71A) (by decide)
    (by rw [g68_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s69 : St n69.mem SV n69 0x71A (reg n69) := ⟨u69.pc, rfl, fun _ => rfl⟩
  have m69 : n69.mem = n68.mem := u69.mem
  have fr69 : ∀ x, SvR B x → n69.mem x = n68.mem x := fun x _ => by rw [m69]
  have t69 : Steps n0 n69 := t68.trans (.single d69)
  have fR69 : ∀ x, SvR B x → n69.mem x = M0 x := fun x hx => (fr69 x hx).trans (fR68 x hx)
  have E69 : SvCode n69.mem := E68.fr F fr69
  have V69 : SvSaves B n69.mem v := V68.same m69
  have g69_2 : reg n69 sp = B + 0x21A0 := by rw [u69.regs, upd_ne (by decide) (by decide), g68_2]
  have g69_3 : reg n69 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u69.regs, upd_ne (by decide) (by decide), g68_3]
  have g69_4 : reg n69 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u69.regs, upd_ne (by decide) (by decide), g68_4]
  have g69_8 : reg n69 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u69.regs, upd_ne (by decide) (by decide), g68_8]
  have g69_9 : reg n69 (9 : Fin 32) = tbp := by rw [u69.regs, upd_ne (by decide) (by decide), g68_9]
  have g69_10 : reg n69 a0 = BitVec.ofNat 32 0x0 := by rw [u69.regs, upd_ne (by decide) (by decide), g68_10]
  have g69_18 : reg n69 (18 : Fin 32) = out := by rw [u69.regs, upd_ne (by decide) (by decide), g68_18]
  have g69_19 : reg n69 (19 : Fin 32) = bp := by rw [u69.regs, upd_ne (by decide) (by decide), g68_19]
  have g69_20 : reg n69 (20 : Fin 32) = dg := by rw [u69.regs, upd_ne (by decide) (by decide), g68_20]
  have g69_21 : reg n69 (21 : Fin 32) = rootp := by rw [u69.regs, upd_ne (by decide) (by decide), g68_21]
  have g69_22 : reg n69 (22 : Fin 32) = ll := by rw [u69.regs, upd_ne (by decide) (by decide), g68_22]
  have g69_23 : reg n69 (23 : Fin 32) = sgp := by rw [u69.regs, upd_ne (by decide) (by decide), g68_23]
  have g69_24 : reg n69 (24 : Fin 32) = kp := by rw [u69.regs, upd_ne (by decide) (by decide), g68_24]
  have g69_25 : reg n69 (25 : Fin 32) = sgl := by rw [u69.regs, upd_ne (by decide) (by decide), g68_25]
  have g69_26 : reg n69 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by rw [u69.regs, upd_ne (by decide) (by decide), g68_26]
  have g69_27 : reg n69 (27 : Fin 32) = tbl := by rw [u69.regs, upd_ne (by decide) (by decide), g68_27]
  have g69_11 : reg n69 a1 = BitVec.ofNat 32 0x2 := by
    rw [u69.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g68_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w68_50]
  have keep_kk69 : SvKeepL B n0.mem n69.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m69]; exact keep_kk68
  clear keep_kk68
  have w69_2c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m69]; exact w68_2c
  have w69_30 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m69]; exact w68_30
  have w69_34 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m69]; exact w68_34
  have w69_38 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m69]; exact w68_38
  have w69_44 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m69]; exact w68_44
  have w69_48 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m69]; exact w68_48
  have w69_4c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m69]; exact w68_4c
  have w69_50 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m69]; exact w68_50
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
  have w69_88 : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m69]; exact w68_88
  have w69_8c : memLoad32 n69.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m69]; exact w68_8c
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
  clear w68_15c w68_158 w68_154 w68_150 w68_a4 w68_a0 w68_9c w68_98 w68_94 w68_90 w68_8c w68_88 w68_84 w68_80 w68_7c w68_78 w68_74 w68_70 w68_6c w68_68 w68_64 w68_60 w68_5c w68_58 w68_54 w68_50 w68_4c w68_48 w68_44 w68_38 w68_34 w68_30 w68_2c g68_27 g68_26 g68_25 g68_24 g68_23 g68_22 g68_21 g68_20 g68_19 g68_18 g68_9 g68_8 g68_4 g68_3 g68_2 V68 E68 fR68 t68 fr68 K68 a0_68 rk68 s68 c68
  -- 0x71A
  obtain ⟨n70, c70, u70⟩ := s69.block svDp471a E69.self svDp471a_end
    ⟨trivial, trivial⟩
  have m70 : n70.mem = n69.mem := u70.mem
  have s70 : St n70.mem SV n70 0x71C (reg n70) := ⟨u70.pc, rfl, fun _ => rfl⟩
  have rb70 : ∀ q, reg n70 q = (runBlock svDp471a (n69.mem, reg n69)).2 q := fun q => by rw [u70.regs]
  have fr70 : ∀ x, SvR B x → n70.mem x = n69.mem x := fun x _ => by rw [m70]
  have t70 : Steps n0 n70 := t69.trans c70
  have fR70 : ∀ x, SvR B x → n70.mem x = M0 x := fun x hx => (fr70 x hx).trans (fR69 x hx)
  have E70 : SvCode n70.mem := E69.fr F fr70
  have V70 : SvSaves B n70.mem v := V69.same m70
  have g70_2 : reg n70 sp = B + 0x21A0 := by
    rw [rb70, runBlock_reg _ _ _ sp s69.zero (by decide), g69_2]
  have g70_3 : reg n70 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb70, runBlock_reg _ _ _ (3 : Fin 32) s69.zero (by decide), g69_3]
  have g70_4 : reg n70 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb70, runBlock_reg _ _ _ (4 : Fin 32) s69.zero (by decide), g69_4]
  have g70_8 : reg n70 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb70, runBlock_reg _ _ _ (8 : Fin 32) s69.zero (by decide), g69_8]
  have g70_9 : reg n70 (9 : Fin 32) = tbp := by
    rw [rb70, runBlock_reg _ _ _ (9 : Fin 32) s69.zero (by decide), g69_9]
  have g70_10 : reg n70 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb70, runBlock_reg _ _ _ a0 s69.zero (by decide), g69_10]
  have g70_18 : reg n70 (18 : Fin 32) = out := by
    rw [rb70, runBlock_reg _ _ _ (18 : Fin 32) s69.zero (by decide), g69_18]
  have g70_19 : reg n70 (19 : Fin 32) = bp := by
    rw [rb70, runBlock_reg _ _ _ (19 : Fin 32) s69.zero (by decide), g69_19]
  have g70_20 : reg n70 (20 : Fin 32) = dg := by
    rw [rb70, runBlock_reg _ _ _ (20 : Fin 32) s69.zero (by decide), g69_20]
  have g70_21 : reg n70 (21 : Fin 32) = rootp := by
    rw [rb70, runBlock_reg _ _ _ (21 : Fin 32) s69.zero (by decide), g69_21]
  have g70_22 : reg n70 (22 : Fin 32) = ll := by
    rw [rb70, runBlock_reg _ _ _ (22 : Fin 32) s69.zero (by decide), g69_22]
  have g70_23 : reg n70 (23 : Fin 32) = sgp := by
    rw [rb70, runBlock_reg _ _ _ (23 : Fin 32) s69.zero (by decide), g69_23]
  have g70_24 : reg n70 (24 : Fin 32) = kp := by
    rw [rb70, runBlock_reg _ _ _ (24 : Fin 32) s69.zero (by decide), g69_24]
  have g70_25 : reg n70 (25 : Fin 32) = sgl := by
    rw [rb70, runBlock_reg _ _ _ (25 : Fin 32) s69.zero (by decide), g69_25]
  have g70_26 : reg n70 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by
    rw [rb70, runBlock_reg _ _ _ (26 : Fin 32) s69.zero (by decide), g69_26]
  have g70_27 : reg n70 (27 : Fin 32) = tbl := by
    rw [rb70, runBlock_reg _ _ _ (27 : Fin 32) s69.zero (by decide), g69_27]
  have g70_11 : reg n70 a1 = BitVec.ofNat 32 0x3 := by
    rw [rb70]; simp +decide only [runBlock, BInstr.run, svDp471a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g69_2, g69_3, g69_4, g69_8, g69_9, g69_10, g69_11, g69_18, g69_19, g69_20, g69_21, g69_22, g69_23, g69_24, g69_25, g69_26, g69_27, s69.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk70 : SvKeepL B n0.mem n70.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m70]; exact keep_kk69
  clear keep_kk69
  have w70_2c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m70]; exact w69_2c
  have w70_30 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m70]; exact w69_30
  have w70_34 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m70]; exact w69_34
  have w70_38 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m70]; exact w69_38
  have w70_44 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m70]; exact w69_44
  have w70_48 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m70]; exact w69_48
  have w70_4c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m70]; exact w69_4c
  have w70_50 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x2 := by rw [m70]; exact w69_50
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
  have w70_88 : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m70]; exact w69_88
  have w70_8c : memLoad32 n70.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m70]; exact w69_8c
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
  clear w69_15c w69_158 w69_154 w69_150 w69_a4 w69_a0 w69_9c w69_98 w69_94 w69_90 w69_8c w69_88 w69_84 w69_80 w69_7c w69_78 w69_74 w69_70 w69_6c w69_68 w69_64 w69_60 w69_5c w69_58 w69_54 w69_50 w69_4c w69_48 w69_44 w69_38 w69_34 w69_30 w69_2c g69_11 g69_27 g69_26 g69_25 g69_24 g69_23 g69_22 g69_21 g69_20 g69_19 g69_18 g69_10 g69_9 g69_8 g69_4 g69_3 g69_2 V69 E69 fR69 t69 fr69 m69 s69 u69 d69 g68_10
  -- 0x71C: sw
  obtain ⟨n71, d71, s71, fr71, K71, W71, rg71⟩ := sv_sw F E70 s70 sv_at_71c (off' := 0x71E) (c := 0x50)
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
  have g71_10 : reg n71 a0 = BitVec.ofNat 32 0x0 := by rw [rg71 a0, g70_10]
  have g71_11 : reg n71 a1 = BitVec.ofNat 32 0x3 := by rw [rg71 a1, g70_11]
  have g71_18 : reg n71 (18 : Fin 32) = out := by rw [rg71 (18 : Fin 32), g70_18]
  have g71_19 : reg n71 (19 : Fin 32) = bp := by rw [rg71 (19 : Fin 32), g70_19]
  have g71_20 : reg n71 (20 : Fin 32) = dg := by rw [rg71 (20 : Fin 32), g70_20]
  have g71_21 : reg n71 (21 : Fin 32) = rootp := by rw [rg71 (21 : Fin 32), g70_21]
  have g71_22 : reg n71 (22 : Fin 32) = ll := by rw [rg71 (22 : Fin 32), g70_22]
  have g71_23 : reg n71 (23 : Fin 32) = sgp := by rw [rg71 (23 : Fin 32), g70_23]
  have g71_24 : reg n71 (24 : Fin 32) = kp := by rw [rg71 (24 : Fin 32), g70_24]
  have g71_25 : reg n71 (25 : Fin 32) = sgl := by rw [rg71 (25 : Fin 32), g70_25]
  have g71_26 : reg n71 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x79) := by rw [rg71 (26 : Fin 32), g70_26]
  have g71_27 : reg n71 (27 : Fin 32) = tbl := by rw [rg71 (27 : Fin 32), g70_27]
  have keep_kk71 : SvKeepL B n0.mem n71.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := keep_kk70.trans K71.toL
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
  have w71_88 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K71.w32 (by decide) (by decide)).trans w70_88
  have w71_8c : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K71.w32 (by decide) (by decide)).trans w70_8c
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
  have w71_50 : memLoad32 n71.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [W71, g70_11]
  clear w70_15c w70_158 w70_154 w70_150 w70_a4 w70_a0 w70_9c w70_98 w70_94 w70_90 w70_8c w70_88 w70_84 w70_80 w70_7c w70_78 w70_74 w70_70 w70_6c w70_68 w70_64 w70_60 w70_5c w70_58 w70_54 w70_50 w70_4c w70_48 w70_44 w70_38 w70_34 w70_30 w70_2c g70_11 g70_27 g70_26 g70_25 g70_24 g70_23 g70_22 g70_21 g70_20 g70_19 g70_18 g70_10 g70_9 g70_8 g70_4 g70_3 g70_2 V70 E70 fR70 t70 fr70 rb70 s70 m70 u70 c70
  -- 0x71E
  obtain ⟨n72, c72, u72⟩ := s71.block svDp471e E71.self svDp471e_end
    ⟨trivial, trivial⟩
  have m72 : n72.mem = n71.mem := u72.mem
  have s72 : St n72.mem SV n72 0x720 (reg n72) := ⟨u72.pc, rfl, fun _ => rfl⟩
  have rb72 : ∀ q, reg n72 q = (runBlock svDp471e (n71.mem, reg n71)).2 q := fun q => by rw [u72.regs]
  have fr72 : ∀ x, SvR B x → n72.mem x = n71.mem x := fun x _ => by rw [m72]
  have t72 : Steps n0 n72 := t71.trans c72
  have fR72 : ∀ x, SvR B x → n72.mem x = M0 x := fun x hx => (fr72 x hx).trans (fR71 x hx)
  have E72 : SvCode n72.mem := E71.fr F fr72
  have V72 : SvSaves B n72.mem v := V71.same m72
  have g72_2 : reg n72 sp = B + 0x21A0 := by
    rw [rb72, runBlock_reg _ _ _ sp s71.zero (by decide), g71_2]
  have g72_3 : reg n72 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb72, runBlock_reg _ _ _ (3 : Fin 32) s71.zero (by decide), g71_3]
  have g72_4 : reg n72 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb72, runBlock_reg _ _ _ (4 : Fin 32) s71.zero (by decide), g71_4]
  have g72_8 : reg n72 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb72, runBlock_reg _ _ _ (8 : Fin 32) s71.zero (by decide), g71_8]
  have g72_9 : reg n72 (9 : Fin 32) = tbp := by
    rw [rb72, runBlock_reg _ _ _ (9 : Fin 32) s71.zero (by decide), g71_9]
  have g72_10 : reg n72 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb72, runBlock_reg _ _ _ a0 s71.zero (by decide), g71_10]
  have g72_11 : reg n72 a1 = BitVec.ofNat 32 0x3 := by
    rw [rb72, runBlock_reg _ _ _ a1 s71.zero (by decide), g71_11]
  have g72_18 : reg n72 (18 : Fin 32) = out := by
    rw [rb72, runBlock_reg _ _ _ (18 : Fin 32) s71.zero (by decide), g71_18]
  have g72_19 : reg n72 (19 : Fin 32) = bp := by
    rw [rb72, runBlock_reg _ _ _ (19 : Fin 32) s71.zero (by decide), g71_19]
  have g72_20 : reg n72 (20 : Fin 32) = dg := by
    rw [rb72, runBlock_reg _ _ _ (20 : Fin 32) s71.zero (by decide), g71_20]
  have g72_21 : reg n72 (21 : Fin 32) = rootp := by
    rw [rb72, runBlock_reg _ _ _ (21 : Fin 32) s71.zero (by decide), g71_21]
  have g72_22 : reg n72 (22 : Fin 32) = ll := by
    rw [rb72, runBlock_reg _ _ _ (22 : Fin 32) s71.zero (by decide), g71_22]
  have g72_23 : reg n72 (23 : Fin 32) = sgp := by
    rw [rb72, runBlock_reg _ _ _ (23 : Fin 32) s71.zero (by decide), g71_23]
  have g72_24 : reg n72 (24 : Fin 32) = kp := by
    rw [rb72, runBlock_reg _ _ _ (24 : Fin 32) s71.zero (by decide), g71_24]
  have g72_25 : reg n72 (25 : Fin 32) = sgl := by
    rw [rb72, runBlock_reg _ _ _ (25 : Fin 32) s71.zero (by decide), g71_25]
  have g72_27 : reg n72 (27 : Fin 32) = tbl := by
    rw [rb72, runBlock_reg _ _ _ (27 : Fin 32) s71.zero (by decide), g71_27]
  have g72_26 : reg n72 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by
    rw [rb72]; simp +decide only [runBlock, BInstr.run, svDp471e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g71_2, g71_3, g71_4, g71_8, g71_9, g71_10, g71_11, g71_18, g71_19, g71_20, g71_21, g71_22, g71_23, g71_24, g71_25, g71_26, g71_27, s71.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk72 : SvKeepL B n0.mem n72.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m72]; exact keep_kk71
  clear keep_kk71
  have w72_2c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m72]; exact w71_2c
  have w72_30 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m72]; exact w71_30
  have w72_34 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m72]; exact w71_34
  have w72_38 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m72]; exact w71_38
  have w72_44 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m72]; exact w71_44
  have w72_48 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m72]; exact w71_48
  have w72_4c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m72]; exact w71_4c
  have w72_50 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m72]; exact w71_50
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
  have w72_88 : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m72]; exact w71_88
  have w72_8c : memLoad32 n72.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m72]; exact w71_8c
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
  clear w71_50 w71_15c w71_158 w71_154 w71_150 w71_a4 w71_a0 w71_9c w71_98 w71_94 w71_90 w71_8c w71_88 w71_84 w71_80 w71_7c w71_78 w71_74 w71_70 w71_6c w71_68 w71_64 w71_60 w71_5c w71_58 w71_54 w71_4c w71_48 w71_44 w71_38 w71_34 w71_30 w71_2c g71_27 g71_26 g71_25 g71_24 g71_23 g71_22 g71_21 g71_20 g71_19 g71_18 g71_11 g71_10 g71_9 g71_8 g71_4 g71_3 g71_2 V71 E71 fR71 t71 rg71 W71 K71 fr71 s71 d71
  -- 0x720: branch, taken
  obtain ⟨n73, d73, u73⟩ := s72.taken E72.self 0x6FE sv_at_720
    (by decide) (by rw [g72_10, s72.zero]; decide)
  have s73 : St n73.mem SV n73 0x6FE (reg n73) := ⟨u73.pc, rfl, fun _ => rfl⟩
  have m73 : n73.mem = n72.mem := u73.mem
  have fr73 : ∀ x, SvR B x → n73.mem x = n72.mem x := fun x _ => by rw [m73]
  have t73 : Steps n0 n73 := t72.trans (.single d73)
  have fR73 : ∀ x, SvR B x → n73.mem x = M0 x := fun x hx => (fr73 x hx).trans (fR72 x hx)
  have E73 : SvCode n73.mem := E72.fr F fr73
  have V73 : SvSaves B n73.mem v := V72.same m73
  have g73_2 : reg n73 sp = B + 0x21A0 := by rw [u73.regs, g72_2]
  have g73_3 : reg n73 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u73.regs, g72_3]
  have g73_4 : reg n73 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u73.regs, g72_4]
  have g73_8 : reg n73 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u73.regs, g72_8]
  have g73_9 : reg n73 (9 : Fin 32) = tbp := by rw [u73.regs, g72_9]
  have g73_10 : reg n73 a0 = BitVec.ofNat 32 0x0 := by rw [u73.regs, g72_10]
  have g73_11 : reg n73 a1 = BitVec.ofNat 32 0x3 := by rw [u73.regs, g72_11]
  have g73_18 : reg n73 (18 : Fin 32) = out := by rw [u73.regs, g72_18]
  have g73_19 : reg n73 (19 : Fin 32) = bp := by rw [u73.regs, g72_19]
  have g73_20 : reg n73 (20 : Fin 32) = dg := by rw [u73.regs, g72_20]
  have g73_21 : reg n73 (21 : Fin 32) = rootp := by rw [u73.regs, g72_21]
  have g73_22 : reg n73 (22 : Fin 32) = ll := by rw [u73.regs, g72_22]
  have g73_23 : reg n73 (23 : Fin 32) = sgp := by rw [u73.regs, g72_23]
  have g73_24 : reg n73 (24 : Fin 32) = kp := by rw [u73.regs, g72_24]
  have g73_25 : reg n73 (25 : Fin 32) = sgl := by rw [u73.regs, g72_25]
  have g73_26 : reg n73 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by rw [u73.regs, g72_26]
  have g73_27 : reg n73 (27 : Fin 32) = tbl := by rw [u73.regs, g72_27]
  have keep_kk73 : SvKeepL B n0.mem n73.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m73]; exact keep_kk72
  clear keep_kk72
  have w73_2c : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m73]; exact w72_2c
  have w73_30 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m73]; exact w72_30
  have w73_34 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m73]; exact w72_34
  have w73_38 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m73]; exact w72_38
  have w73_44 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m73]; exact w72_44
  have w73_48 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m73]; exact w72_48
  have w73_4c : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m73]; exact w72_4c
  have w73_50 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m73]; exact w72_50
  have w73_54 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m73]; exact w72_54
  have w73_58 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m73]; exact w72_58
  have w73_5c : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m73]; exact w72_5c
  have w73_60 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m73]; exact w72_60
  have w73_64 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m73]; exact w72_64
  have w73_68 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m73]; exact w72_68
  have w73_6c : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m73]; exact w72_6c
  have w73_70 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m73]; exact w72_70
  have w73_74 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m73]; exact w72_74
  have w73_78 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m73]; exact w72_78
  have w73_7c : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m73]; exact w72_7c
  have w73_80 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m73]; exact w72_80
  have w73_84 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m73]; exact w72_84
  have w73_88 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m73]; exact w72_88
  have w73_8c : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m73]; exact w72_8c
  have w73_90 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m73]; exact w72_90
  have w73_94 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m73]; exact w72_94
  have w73_98 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m73]; exact w72_98
  have w73_9c : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m73]; exact w72_9c
  have w73_a0 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m73]; exact w72_a0
  have w73_a4 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m73]; exact w72_a4
  have w73_150 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m73]; exact w72_150
  have w73_154 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m73]; exact w72_154
  have w73_158 : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m73]; exact w72_158
  have w73_15c : memLoad32 n73.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m73]; exact w72_15c
  clear w72_15c w72_158 w72_154 w72_150 w72_a4 w72_a0 w72_9c w72_98 w72_94 w72_90 w72_8c w72_88 w72_84 w72_80 w72_7c w72_78 w72_74 w72_70 w72_6c w72_68 w72_64 w72_60 w72_5c w72_58 w72_54 w72_50 w72_4c w72_48 w72_44 w72_38 w72_34 w72_30 w72_2c g72_26 g72_27 g72_25 g72_24 g72_23 g72_22 g72_21 g72_20 g72_19 g72_18 g72_11 g72_10 g72_9 g72_8 g72_4 g72_3 g72_2 V72 E72 fR72 t72 fr72 rb72 s72 m72 u72 c72
  -- 0x6FE
  obtain ⟨n74, c74, u74⟩ := s73.block svDp46fe E73.self svDp46fe_end
    ⟨trivial, trivial⟩
  have m74 : n74.mem = n73.mem := u74.mem
  have s74 : St n74.mem SV n74 0x700 (reg n74) := ⟨u74.pc, rfl, fun _ => rfl⟩
  have rb74 : ∀ q, reg n74 q = (runBlock svDp46fe (n73.mem, reg n73)).2 q := fun q => by rw [u74.regs]
  have fr74 : ∀ x, SvR B x → n74.mem x = n73.mem x := fun x _ => by rw [m74]
  have t74 : Steps n0 n74 := t73.trans c74
  have fR74 : ∀ x, SvR B x → n74.mem x = M0 x := fun x hx => (fr74 x hx).trans (fR73 x hx)
  have E74 : SvCode n74.mem := E73.fr F fr74
  have V74 : SvSaves B n74.mem v := V73.same m74
  have g74_2 : reg n74 sp = B + 0x21A0 := by
    rw [rb74, runBlock_reg _ _ _ sp s73.zero (by decide), g73_2]
  have g74_3 : reg n74 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb74, runBlock_reg _ _ _ (3 : Fin 32) s73.zero (by decide), g73_3]
  have g74_4 : reg n74 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb74, runBlock_reg _ _ _ (4 : Fin 32) s73.zero (by decide), g73_4]
  have g74_8 : reg n74 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb74, runBlock_reg _ _ _ (8 : Fin 32) s73.zero (by decide), g73_8]
  have g74_9 : reg n74 (9 : Fin 32) = tbp := by
    rw [rb74, runBlock_reg _ _ _ (9 : Fin 32) s73.zero (by decide), g73_9]
  have g74_11 : reg n74 a1 = BitVec.ofNat 32 0x3 := by
    rw [rb74, runBlock_reg _ _ _ a1 s73.zero (by decide), g73_11]
  have g74_18 : reg n74 (18 : Fin 32) = out := by
    rw [rb74, runBlock_reg _ _ _ (18 : Fin 32) s73.zero (by decide), g73_18]
  have g74_19 : reg n74 (19 : Fin 32) = bp := by
    rw [rb74, runBlock_reg _ _ _ (19 : Fin 32) s73.zero (by decide), g73_19]
  have g74_20 : reg n74 (20 : Fin 32) = dg := by
    rw [rb74, runBlock_reg _ _ _ (20 : Fin 32) s73.zero (by decide), g73_20]
  have g74_21 : reg n74 (21 : Fin 32) = rootp := by
    rw [rb74, runBlock_reg _ _ _ (21 : Fin 32) s73.zero (by decide), g73_21]
  have g74_22 : reg n74 (22 : Fin 32) = ll := by
    rw [rb74, runBlock_reg _ _ _ (22 : Fin 32) s73.zero (by decide), g73_22]
  have g74_23 : reg n74 (23 : Fin 32) = sgp := by
    rw [rb74, runBlock_reg _ _ _ (23 : Fin 32) s73.zero (by decide), g73_23]
  have g74_24 : reg n74 (24 : Fin 32) = kp := by
    rw [rb74, runBlock_reg _ _ _ (24 : Fin 32) s73.zero (by decide), g73_24]
  have g74_25 : reg n74 (25 : Fin 32) = sgl := by
    rw [rb74, runBlock_reg _ _ _ (25 : Fin 32) s73.zero (by decide), g73_25]
  have g74_26 : reg n74 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by
    rw [rb74, runBlock_reg _ _ _ (26 : Fin 32) s73.zero (by decide), g73_26]
  have g74_27 : reg n74 (27 : Fin 32) = tbl := by
    rw [rb74, runBlock_reg _ _ _ (27 : Fin 32) s73.zero (by decide), g73_27]
  have g74_10 : reg n74 a0 = BitVec.ofNat 32 0x4 := by
    rw [rb74]; simp +decide only [runBlock, BInstr.run, svDp46fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g73_2, g73_3, g73_4, g73_8, g73_9, g73_10, g73_11, g73_18, g73_19, g73_20, g73_21, g73_22, g73_23, g73_24, g73_25, g73_26, g73_27, s73.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk74 : SvKeepL B n0.mem n74.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m74]; exact keep_kk73
  clear keep_kk73
  have w74_2c : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m74]; exact w73_2c
  have w74_30 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m74]; exact w73_30
  have w74_34 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m74]; exact w73_34
  have w74_38 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m74]; exact w73_38
  have w74_44 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m74]; exact w73_44
  have w74_48 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m74]; exact w73_48
  have w74_4c : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m74]; exact w73_4c
  have w74_50 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m74]; exact w73_50
  have w74_54 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m74]; exact w73_54
  have w74_58 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m74]; exact w73_58
  have w74_5c : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m74]; exact w73_5c
  have w74_60 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m74]; exact w73_60
  have w74_64 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m74]; exact w73_64
  have w74_68 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m74]; exact w73_68
  have w74_6c : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m74]; exact w73_6c
  have w74_70 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m74]; exact w73_70
  have w74_74 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m74]; exact w73_74
  have w74_78 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m74]; exact w73_78
  have w74_7c : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m74]; exact w73_7c
  have w74_80 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m74]; exact w73_80
  have w74_84 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m74]; exact w73_84
  have w74_88 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m74]; exact w73_88
  have w74_8c : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m74]; exact w73_8c
  have w74_90 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m74]; exact w73_90
  have w74_94 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m74]; exact w73_94
  have w74_98 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m74]; exact w73_98
  have w74_9c : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m74]; exact w73_9c
  have w74_a0 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m74]; exact w73_a0
  have w74_a4 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m74]; exact w73_a4
  have w74_150 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m74]; exact w73_150
  have w74_154 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m74]; exact w73_154
  have w74_158 : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m74]; exact w73_158
  have w74_15c : memLoad32 n74.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m74]; exact w73_15c
  clear w73_15c w73_158 w73_154 w73_150 w73_a4 w73_a0 w73_9c w73_98 w73_94 w73_90 w73_8c w73_88 w73_84 w73_80 w73_7c w73_78 w73_74 w73_70 w73_6c w73_68 w73_64 w73_60 w73_5c w73_58 w73_54 w73_50 w73_4c w73_48 w73_44 w73_38 w73_34 w73_30 w73_2c g73_27 g73_26 g73_25 g73_24 g73_23 g73_22 g73_21 g73_20 g73_19 g73_18 g73_11 g73_10 g73_9 g73_8 g73_4 g73_3 g73_2 V73 E73 fR73 t73 fr73 m73 s73 u73 d73
  -- 0x700: lw
  obtain ⟨n75, d75, u75⟩ := s74.lw E74.self sv_at_700 (off' := 0x702) (by decide)
    (by rw [g74_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s75 : St n75.mem SV n75 0x702 (reg n75) := ⟨u75.pc, rfl, fun _ => rfl⟩
  have m75 : n75.mem = n74.mem := u75.mem
  have fr75 : ∀ x, SvR B x → n75.mem x = n74.mem x := fun x _ => by rw [m75]
  have t75 : Steps n0 n75 := t74.trans (.single d75)
  have fR75 : ∀ x, SvR B x → n75.mem x = M0 x := fun x hx => (fr75 x hx).trans (fR74 x hx)
  have E75 : SvCode n75.mem := E74.fr F fr75
  have V75 : SvSaves B n75.mem v := V74.same m75
  have g75_2 : reg n75 sp = B + 0x21A0 := by rw [u75.regs, upd_ne (by decide) (by decide), g74_2]
  have g75_3 : reg n75 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u75.regs, upd_ne (by decide) (by decide), g74_3]
  have g75_4 : reg n75 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u75.regs, upd_ne (by decide) (by decide), g74_4]
  have g75_8 : reg n75 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u75.regs, upd_ne (by decide) (by decide), g74_8]
  have g75_9 : reg n75 (9 : Fin 32) = tbp := by rw [u75.regs, upd_ne (by decide) (by decide), g74_9]
  have g75_10 : reg n75 a0 = BitVec.ofNat 32 0x4 := by rw [u75.regs, upd_ne (by decide) (by decide), g74_10]
  have g75_18 : reg n75 (18 : Fin 32) = out := by rw [u75.regs, upd_ne (by decide) (by decide), g74_18]
  have g75_19 : reg n75 (19 : Fin 32) = bp := by rw [u75.regs, upd_ne (by decide) (by decide), g74_19]
  have g75_20 : reg n75 (20 : Fin 32) = dg := by rw [u75.regs, upd_ne (by decide) (by decide), g74_20]
  have g75_21 : reg n75 (21 : Fin 32) = rootp := by rw [u75.regs, upd_ne (by decide) (by decide), g74_21]
  have g75_22 : reg n75 (22 : Fin 32) = ll := by rw [u75.regs, upd_ne (by decide) (by decide), g74_22]
  have g75_23 : reg n75 (23 : Fin 32) = sgp := by rw [u75.regs, upd_ne (by decide) (by decide), g74_23]
  have g75_24 : reg n75 (24 : Fin 32) = kp := by rw [u75.regs, upd_ne (by decide) (by decide), g74_24]
  have g75_25 : reg n75 (25 : Fin 32) = sgl := by rw [u75.regs, upd_ne (by decide) (by decide), g74_25]
  have g75_26 : reg n75 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by rw [u75.regs, upd_ne (by decide) (by decide), g74_26]
  have g75_27 : reg n75 (27 : Fin 32) = tbl := by rw [u75.regs, upd_ne (by decide) (by decide), g74_27]
  have g75_11 : reg n75 a1 = BitVec.ofNat 32 0x3 := by
    rw [u75.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g74_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w74_50]
  have keep_kk75 : SvKeepL B n0.mem n75.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m75]; exact keep_kk74
  clear keep_kk74
  have w75_2c : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m75]; exact w74_2c
  have w75_30 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m75]; exact w74_30
  have w75_34 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m75]; exact w74_34
  have w75_38 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m75]; exact w74_38
  have w75_44 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m75]; exact w74_44
  have w75_48 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m75]; exact w74_48
  have w75_4c : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m75]; exact w74_4c
  have w75_50 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m75]; exact w74_50
  have w75_54 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m75]; exact w74_54
  have w75_58 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m75]; exact w74_58
  have w75_5c : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m75]; exact w74_5c
  have w75_60 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m75]; exact w74_60
  have w75_64 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m75]; exact w74_64
  have w75_68 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m75]; exact w74_68
  have w75_6c : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m75]; exact w74_6c
  have w75_70 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m75]; exact w74_70
  have w75_74 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m75]; exact w74_74
  have w75_78 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m75]; exact w74_78
  have w75_7c : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m75]; exact w74_7c
  have w75_80 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m75]; exact w74_80
  have w75_84 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m75]; exact w74_84
  have w75_88 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m75]; exact w74_88
  have w75_8c : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m75]; exact w74_8c
  have w75_90 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m75]; exact w74_90
  have w75_94 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m75]; exact w74_94
  have w75_98 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m75]; exact w74_98
  have w75_9c : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m75]; exact w74_9c
  have w75_a0 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m75]; exact w74_a0
  have w75_a4 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m75]; exact w74_a4
  have w75_150 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m75]; exact w74_150
  have w75_154 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m75]; exact w74_154
  have w75_158 : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m75]; exact w74_158
  have w75_15c : memLoad32 n75.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m75]; exact w74_15c
  clear w74_15c w74_158 w74_154 w74_150 w74_a4 w74_a0 w74_9c w74_98 w74_94 w74_90 w74_8c w74_88 w74_84 w74_80 w74_7c w74_78 w74_74 w74_70 w74_6c w74_68 w74_64 w74_60 w74_5c w74_58 w74_54 w74_50 w74_4c w74_48 w74_44 w74_38 w74_34 w74_30 w74_2c g74_10 g74_27 g74_26 g74_25 g74_24 g74_23 g74_22 g74_21 g74_20 g74_19 g74_18 g74_11 g74_9 g74_8 g74_4 g74_3 g74_2 V74 E74 fR74 t74 fr74 rb74 s74 m74 u74 c74
  -- 0x702: branch, not taken
  obtain ⟨n76, d76, u76⟩ := s75.notTaken E75.self 0x706 sv_at_702
    (by decide) (by rw [g75_11, g75_10]; decide)
  have s76 : St n76.mem SV n76 0x706 (reg n76) := ⟨u76.pc, rfl, fun _ => rfl⟩
  have m76 : n76.mem = n75.mem := u76.mem
  have fr76 : ∀ x, SvR B x → n76.mem x = n75.mem x := fun x _ => by rw [m76]
  have t76 : Steps n0 n76 := t75.trans (.single d76)
  have fR76 : ∀ x, SvR B x → n76.mem x = M0 x := fun x hx => (fr76 x hx).trans (fR75 x hx)
  have E76 : SvCode n76.mem := E75.fr F fr76
  have V76 : SvSaves B n76.mem v := V75.same m76
  have g76_2 : reg n76 sp = B + 0x21A0 := by rw [u76.regs, g75_2]
  have g76_3 : reg n76 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u76.regs, g75_3]
  have g76_4 : reg n76 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u76.regs, g75_4]
  have g76_8 : reg n76 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u76.regs, g75_8]
  have g76_9 : reg n76 (9 : Fin 32) = tbp := by rw [u76.regs, g75_9]
  have g76_10 : reg n76 a0 = BitVec.ofNat 32 0x4 := by rw [u76.regs, g75_10]
  have g76_11 : reg n76 a1 = BitVec.ofNat 32 0x3 := by rw [u76.regs, g75_11]
  have g76_18 : reg n76 (18 : Fin 32) = out := by rw [u76.regs, g75_18]
  have g76_19 : reg n76 (19 : Fin 32) = bp := by rw [u76.regs, g75_19]
  have g76_20 : reg n76 (20 : Fin 32) = dg := by rw [u76.regs, g75_20]
  have g76_21 : reg n76 (21 : Fin 32) = rootp := by rw [u76.regs, g75_21]
  have g76_22 : reg n76 (22 : Fin 32) = ll := by rw [u76.regs, g75_22]
  have g76_23 : reg n76 (23 : Fin 32) = sgp := by rw [u76.regs, g75_23]
  have g76_24 : reg n76 (24 : Fin 32) = kp := by rw [u76.regs, g75_24]
  have g76_25 : reg n76 (25 : Fin 32) = sgl := by rw [u76.regs, g75_25]
  have g76_26 : reg n76 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by rw [u76.regs, g75_26]
  have g76_27 : reg n76 (27 : Fin 32) = tbl := by rw [u76.regs, g75_27]
  have keep_kk76 : SvKeepL B n0.mem n76.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m76]; exact keep_kk75
  clear keep_kk75
  have w76_2c : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m76]; exact w75_2c
  have w76_30 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m76]; exact w75_30
  have w76_34 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m76]; exact w75_34
  have w76_38 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m76]; exact w75_38
  have w76_44 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m76]; exact w75_44
  have w76_48 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m76]; exact w75_48
  have w76_4c : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m76]; exact w75_4c
  have w76_50 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m76]; exact w75_50
  have w76_54 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m76]; exact w75_54
  have w76_58 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m76]; exact w75_58
  have w76_5c : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m76]; exact w75_5c
  have w76_60 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m76]; exact w75_60
  have w76_64 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m76]; exact w75_64
  have w76_68 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m76]; exact w75_68
  have w76_6c : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m76]; exact w75_6c
  have w76_70 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m76]; exact w75_70
  have w76_74 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m76]; exact w75_74
  have w76_78 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m76]; exact w75_78
  have w76_7c : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m76]; exact w75_7c
  have w76_80 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m76]; exact w75_80
  have w76_84 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m76]; exact w75_84
  have w76_88 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m76]; exact w75_88
  have w76_8c : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m76]; exact w75_8c
  have w76_90 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m76]; exact w75_90
  have w76_94 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m76]; exact w75_94
  have w76_98 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m76]; exact w75_98
  have w76_9c : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m76]; exact w75_9c
  have w76_a0 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m76]; exact w75_a0
  have w76_a4 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m76]; exact w75_a4
  have w76_150 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m76]; exact w75_150
  have w76_154 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m76]; exact w75_154
  have w76_158 : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m76]; exact w75_158
  have w76_15c : memLoad32 n76.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m76]; exact w75_15c
  clear w75_15c w75_158 w75_154 w75_150 w75_a4 w75_a0 w75_9c w75_98 w75_94 w75_90 w75_8c w75_88 w75_84 w75_80 w75_7c w75_78 w75_74 w75_70 w75_6c w75_68 w75_64 w75_60 w75_5c w75_58 w75_54 w75_50 w75_4c w75_48 w75_44 w75_38 w75_34 w75_30 w75_2c g75_11 g75_27 g75_26 g75_25 g75_24 g75_23 g75_22 g75_21 g75_20 g75_19 g75_18 g75_10 g75_9 g75_8 g75_4 g75_3 g75_2 V75 E75 fR75 t75 fr75 m75 s75 u75 d75
  -- 0x706: lw of a constant
  obtain ⟨n77, d77, u77⟩ := s76.lw E76.self sv_at_706 (off' := 0x70A) (by decide)
    (by rw [g76_26]; decide)
  have s77 : St n77.mem SV n77 0x70A (reg n77) := ⟨u77.pc, rfl, fun _ => rfl⟩
  have m77 : n77.mem = n76.mem := u77.mem
  have fr77 : ∀ x, SvR B x → n77.mem x = n76.mem x := fun x _ => by rw [m77]
  have t77 : Steps n0 n77 := t76.trans (.single d77)
  have fR77 : ∀ x, SvR B x → n77.mem x = M0 x := fun x hx => (fr77 x hx).trans (fR76 x hx)
  have E77 : SvCode n77.mem := E76.fr F fr77
  have V77 : SvSaves B n77.mem v := V76.same m77
  have g77_2 : reg n77 sp = B + 0x21A0 := by rw [u77.regs, upd_ne (by decide) (by decide), g76_2]
  have g77_3 : reg n77 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u77.regs, upd_ne (by decide) (by decide), g76_3]
  have g77_4 : reg n77 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u77.regs, upd_ne (by decide) (by decide), g76_4]
  have g77_8 : reg n77 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u77.regs, upd_ne (by decide) (by decide), g76_8]
  have g77_9 : reg n77 (9 : Fin 32) = tbp := by rw [u77.regs, upd_ne (by decide) (by decide), g76_9]
  have g77_11 : reg n77 a1 = BitVec.ofNat 32 0x3 := by rw [u77.regs, upd_ne (by decide) (by decide), g76_11]
  have g77_18 : reg n77 (18 : Fin 32) = out := by rw [u77.regs, upd_ne (by decide) (by decide), g76_18]
  have g77_19 : reg n77 (19 : Fin 32) = bp := by rw [u77.regs, upd_ne (by decide) (by decide), g76_19]
  have g77_20 : reg n77 (20 : Fin 32) = dg := by rw [u77.regs, upd_ne (by decide) (by decide), g76_20]
  have g77_21 : reg n77 (21 : Fin 32) = rootp := by rw [u77.regs, upd_ne (by decide) (by decide), g76_21]
  have g77_22 : reg n77 (22 : Fin 32) = ll := by rw [u77.regs, upd_ne (by decide) (by decide), g76_22]
  have g77_23 : reg n77 (23 : Fin 32) = sgp := by rw [u77.regs, upd_ne (by decide) (by decide), g76_23]
  have g77_24 : reg n77 (24 : Fin 32) = kp := by rw [u77.regs, upd_ne (by decide) (by decide), g76_24]
  have g77_25 : reg n77 (25 : Fin 32) = sgl := by rw [u77.regs, upd_ne (by decide) (by decide), g76_25]
  have g77_26 : reg n77 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by rw [u77.regs, upd_ne (by decide) (by decide), g76_26]
  have g77_27 : reg n77 (27 : Fin 32) = tbl := by rw [u77.regs, upd_ne (by decide) (by decide), g76_27]
  have g77_10 : reg n77 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x55) := by
    rw [u77.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g76_26, show BitVec.ofNat 32 (img% svConstExtAddress + 0x81) + 0x0 = BitVec.ofNat 32 svConstExtAddress + BitVec.ofNat 32 0x81 by decide]
    exact CodeIn.w32 (SvData.sv FW SD0 fR76).ext (by decide) (by decide)
  have keep_kk77 : SvKeepL B n0.mem n77.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m77]; exact keep_kk76
  clear keep_kk76
  have w77_2c : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m77]; exact w76_2c
  have w77_30 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m77]; exact w76_30
  have w77_34 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m77]; exact w76_34
  have w77_38 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m77]; exact w76_38
  have w77_44 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m77]; exact w76_44
  have w77_48 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m77]; exact w76_48
  have w77_4c : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m77]; exact w76_4c
  have w77_50 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m77]; exact w76_50
  have w77_54 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m77]; exact w76_54
  have w77_58 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m77]; exact w76_58
  have w77_5c : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m77]; exact w76_5c
  have w77_60 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m77]; exact w76_60
  have w77_64 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m77]; exact w76_64
  have w77_68 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m77]; exact w76_68
  have w77_6c : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m77]; exact w76_6c
  have w77_70 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m77]; exact w76_70
  have w77_74 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m77]; exact w76_74
  have w77_78 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m77]; exact w76_78
  have w77_7c : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m77]; exact w76_7c
  have w77_80 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m77]; exact w76_80
  have w77_84 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m77]; exact w76_84
  have w77_88 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m77]; exact w76_88
  have w77_8c : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m77]; exact w76_8c
  have w77_90 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m77]; exact w76_90
  have w77_94 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m77]; exact w76_94
  have w77_98 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m77]; exact w76_98
  have w77_9c : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m77]; exact w76_9c
  have w77_a0 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m77]; exact w76_a0
  have w77_a4 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m77]; exact w76_a4
  have w77_150 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m77]; exact w76_150
  have w77_154 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m77]; exact w76_154
  have w77_158 : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m77]; exact w76_158
  have w77_15c : memLoad32 n77.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m77]; exact w76_15c
  clear w76_15c w76_158 w76_154 w76_150 w76_a4 w76_a0 w76_9c w76_98 w76_94 w76_90 w76_8c w76_88 w76_84 w76_80 w76_7c w76_78 w76_74 w76_70 w76_6c w76_68 w76_64 w76_60 w76_5c w76_58 w76_54 w76_50 w76_4c w76_48 w76_44 w76_38 w76_34 w76_30 w76_2c g76_27 g76_26 g76_25 g76_24 g76_23 g76_22 g76_21 g76_20 g76_19 g76_18 g76_11 g76_10 g76_9 g76_8 g76_4 g76_3 g76_2 V76 E76 fR76 t76 fr76 m76 s76 u76 d76
  -- 0x70A
  obtain ⟨n78, c78, u78⟩ := s77.block svDp470a E77.self svDp470a_end
    ⟨trivial, trivial⟩
  have m78 : n78.mem = n77.mem := u78.mem
  have s78 : St n78.mem SV n78 0x70C (reg n78) := ⟨u78.pc, rfl, fun _ => rfl⟩
  have rb78 : ∀ q, reg n78 q = (runBlock svDp470a (n77.mem, reg n77)).2 q := fun q => by rw [u78.regs]
  have fr78 : ∀ x, SvR B x → n78.mem x = n77.mem x := fun x _ => by rw [m78]
  have t78 : Steps n0 n78 := t77.trans c78
  have fR78 : ∀ x, SvR B x → n78.mem x = M0 x := fun x hx => (fr78 x hx).trans (fR77 x hx)
  have E78 : SvCode n78.mem := E77.fr F fr78
  have V78 : SvSaves B n78.mem v := V77.same m78
  have g78_2 : reg n78 sp = B + 0x21A0 := by
    rw [rb78, runBlock_reg _ _ _ sp s77.zero (by decide), g77_2]
  have g78_3 : reg n78 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb78, runBlock_reg _ _ _ (3 : Fin 32) s77.zero (by decide), g77_3]
  have g78_4 : reg n78 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb78, runBlock_reg _ _ _ (4 : Fin 32) s77.zero (by decide), g77_4]
  have g78_8 : reg n78 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb78, runBlock_reg _ _ _ (8 : Fin 32) s77.zero (by decide), g77_8]
  have g78_9 : reg n78 (9 : Fin 32) = tbp := by
    rw [rb78, runBlock_reg _ _ _ (9 : Fin 32) s77.zero (by decide), g77_9]
  have g78_10 : reg n78 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x55) := by
    rw [rb78, runBlock_reg _ _ _ a0 s77.zero (by decide), g77_10]
  have g78_18 : reg n78 (18 : Fin 32) = out := by
    rw [rb78, runBlock_reg _ _ _ (18 : Fin 32) s77.zero (by decide), g77_18]
  have g78_19 : reg n78 (19 : Fin 32) = bp := by
    rw [rb78, runBlock_reg _ _ _ (19 : Fin 32) s77.zero (by decide), g77_19]
  have g78_20 : reg n78 (20 : Fin 32) = dg := by
    rw [rb78, runBlock_reg _ _ _ (20 : Fin 32) s77.zero (by decide), g77_20]
  have g78_21 : reg n78 (21 : Fin 32) = rootp := by
    rw [rb78, runBlock_reg _ _ _ (21 : Fin 32) s77.zero (by decide), g77_21]
  have g78_22 : reg n78 (22 : Fin 32) = ll := by
    rw [rb78, runBlock_reg _ _ _ (22 : Fin 32) s77.zero (by decide), g77_22]
  have g78_23 : reg n78 (23 : Fin 32) = sgp := by
    rw [rb78, runBlock_reg _ _ _ (23 : Fin 32) s77.zero (by decide), g77_23]
  have g78_24 : reg n78 (24 : Fin 32) = kp := by
    rw [rb78, runBlock_reg _ _ _ (24 : Fin 32) s77.zero (by decide), g77_24]
  have g78_25 : reg n78 (25 : Fin 32) = sgl := by
    rw [rb78, runBlock_reg _ _ _ (25 : Fin 32) s77.zero (by decide), g77_25]
  have g78_26 : reg n78 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by
    rw [rb78, runBlock_reg _ _ _ (26 : Fin 32) s77.zero (by decide), g77_26]
  have g78_27 : reg n78 (27 : Fin 32) = tbl := by
    rw [rb78, runBlock_reg _ _ _ (27 : Fin 32) s77.zero (by decide), g77_27]
  have g78_11 : reg n78 a1 = BitVec.ofNat 32 0xA := by
    rw [rb78]; simp +decide only [runBlock, BInstr.run, svDp470a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g77_2, g77_3, g77_4, g77_8, g77_9, g77_10, g77_11, g77_18, g77_19, g77_20, g77_21, g77_22, g77_23, g77_24, g77_25, g77_26, g77_27, s77.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk78 : SvKeepL B n0.mem n78.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m78]; exact keep_kk77
  clear keep_kk77
  have w78_2c : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m78]; exact w77_2c
  have w78_30 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m78]; exact w77_30
  have w78_34 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m78]; exact w77_34
  have w78_38 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m78]; exact w77_38
  have w78_44 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m78]; exact w77_44
  have w78_48 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m78]; exact w77_48
  have w78_4c : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m78]; exact w77_4c
  have w78_50 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m78]; exact w77_50
  have w78_54 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m78]; exact w77_54
  have w78_58 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m78]; exact w77_58
  have w78_5c : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m78]; exact w77_5c
  have w78_60 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m78]; exact w77_60
  have w78_64 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m78]; exact w77_64
  have w78_68 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m78]; exact w77_68
  have w78_6c : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m78]; exact w77_6c
  have w78_70 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m78]; exact w77_70
  have w78_74 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m78]; exact w77_74
  have w78_78 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m78]; exact w77_78
  have w78_7c : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m78]; exact w77_7c
  have w78_80 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m78]; exact w77_80
  have w78_84 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m78]; exact w77_84
  have w78_88 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m78]; exact w77_88
  have w78_8c : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m78]; exact w77_8c
  have w78_90 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m78]; exact w77_90
  have w78_94 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m78]; exact w77_94
  have w78_98 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m78]; exact w77_98
  have w78_9c : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m78]; exact w77_9c
  have w78_a0 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m78]; exact w77_a0
  have w78_a4 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m78]; exact w77_a4
  have w78_150 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m78]; exact w77_150
  have w78_154 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m78]; exact w77_154
  have w78_158 : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m78]; exact w77_158
  have w78_15c : memLoad32 n78.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m78]; exact w77_15c
  clear w77_15c w77_158 w77_154 w77_150 w77_a4 w77_a0 w77_9c w77_98 w77_94 w77_90 w77_8c w77_88 w77_84 w77_80 w77_7c w77_78 w77_74 w77_70 w77_6c w77_68 w77_64 w77_60 w77_5c w77_58 w77_54 w77_50 w77_4c w77_48 w77_44 w77_38 w77_34 w77_30 w77_2c g77_10 g77_27 g77_26 g77_25 g77_24 g77_23 g77_22 g77_21 g77_20 g77_19 g77_18 g77_11 g77_9 g77_8 g77_4 g77_3 g77_2 V77 E77 fR77 t77 fr77 m77 s77 u77 d77
  -- 0x70C: lw
  obtain ⟨n79, d79, u79⟩ := s78.lw E78.self sv_at_70c (off' := 0x70E) (by decide)
    (by rw [g78_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s79 : St n79.mem SV n79 0x70E (reg n79) := ⟨u79.pc, rfl, fun _ => rfl⟩
  have m79 : n79.mem = n78.mem := u79.mem
  have fr79 : ∀ x, SvR B x → n79.mem x = n78.mem x := fun x _ => by rw [m79]
  have t79 : Steps n0 n79 := t78.trans (.single d79)
  have fR79 : ∀ x, SvR B x → n79.mem x = M0 x := fun x hx => (fr79 x hx).trans (fR78 x hx)
  have E79 : SvCode n79.mem := E78.fr F fr79
  have V79 : SvSaves B n79.mem v := V78.same m79
  have g79_2 : reg n79 sp = B + 0x21A0 := by rw [u79.regs, upd_ne (by decide) (by decide), g78_2]
  have g79_3 : reg n79 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u79.regs, upd_ne (by decide) (by decide), g78_3]
  have g79_4 : reg n79 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u79.regs, upd_ne (by decide) (by decide), g78_4]
  have g79_8 : reg n79 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u79.regs, upd_ne (by decide) (by decide), g78_8]
  have g79_9 : reg n79 (9 : Fin 32) = tbp := by rw [u79.regs, upd_ne (by decide) (by decide), g78_9]
  have g79_10 : reg n79 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x55) := by rw [u79.regs, upd_ne (by decide) (by decide), g78_10]
  have g79_11 : reg n79 a1 = BitVec.ofNat 32 0xA := by rw [u79.regs, upd_ne (by decide) (by decide), g78_11]
  have g79_18 : reg n79 (18 : Fin 32) = out := by rw [u79.regs, upd_ne (by decide) (by decide), g78_18]
  have g79_19 : reg n79 (19 : Fin 32) = bp := by rw [u79.regs, upd_ne (by decide) (by decide), g78_19]
  have g79_20 : reg n79 (20 : Fin 32) = dg := by rw [u79.regs, upd_ne (by decide) (by decide), g78_20]
  have g79_21 : reg n79 (21 : Fin 32) = rootp := by rw [u79.regs, upd_ne (by decide) (by decide), g78_21]
  have g79_22 : reg n79 (22 : Fin 32) = ll := by rw [u79.regs, upd_ne (by decide) (by decide), g78_22]
  have g79_23 : reg n79 (23 : Fin 32) = sgp := by rw [u79.regs, upd_ne (by decide) (by decide), g78_23]
  have g79_24 : reg n79 (24 : Fin 32) = kp := by rw [u79.regs, upd_ne (by decide) (by decide), g78_24]
  have g79_25 : reg n79 (25 : Fin 32) = sgl := by rw [u79.regs, upd_ne (by decide) (by decide), g78_25]
  have g79_26 : reg n79 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by rw [u79.regs, upd_ne (by decide) (by decide), g78_26]
  have g79_27 : reg n79 (27 : Fin 32) = tbl := by rw [u79.regs, upd_ne (by decide) (by decide), g78_27]
  have g79_12 : reg n79 a2 = op := by
    rw [u79.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g78_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w78_4c]
  have keep_kk79 : SvKeepL B n0.mem n79.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m79]; exact keep_kk78
  clear keep_kk78
  have w79_2c : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m79]; exact w78_2c
  have w79_30 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m79]; exact w78_30
  have w79_34 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m79]; exact w78_34
  have w79_38 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m79]; exact w78_38
  have w79_44 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m79]; exact w78_44
  have w79_48 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m79]; exact w78_48
  have w79_4c : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m79]; exact w78_4c
  have w79_50 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m79]; exact w78_50
  have w79_54 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m79]; exact w78_54
  have w79_58 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m79]; exact w78_58
  have w79_5c : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m79]; exact w78_5c
  have w79_60 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m79]; exact w78_60
  have w79_64 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m79]; exact w78_64
  have w79_68 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m79]; exact w78_68
  have w79_6c : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m79]; exact w78_6c
  have w79_70 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m79]; exact w78_70
  have w79_74 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m79]; exact w78_74
  have w79_78 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m79]; exact w78_78
  have w79_7c : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m79]; exact w78_7c
  have w79_80 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m79]; exact w78_80
  have w79_84 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m79]; exact w78_84
  have w79_88 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m79]; exact w78_88
  have w79_8c : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m79]; exact w78_8c
  have w79_90 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m79]; exact w78_90
  have w79_94 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m79]; exact w78_94
  have w79_98 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m79]; exact w78_98
  have w79_9c : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m79]; exact w78_9c
  have w79_a0 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m79]; exact w78_a0
  have w79_a4 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m79]; exact w78_a4
  have w79_150 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m79]; exact w78_150
  have w79_154 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m79]; exact w78_154
  have w79_158 : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m79]; exact w78_158
  have w79_15c : memLoad32 n79.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m79]; exact w78_15c
  clear w78_15c w78_158 w78_154 w78_150 w78_a4 w78_a0 w78_9c w78_98 w78_94 w78_90 w78_8c w78_88 w78_84 w78_80 w78_7c w78_78 w78_74 w78_70 w78_6c w78_68 w78_64 w78_60 w78_5c w78_58 w78_54 w78_50 w78_4c w78_48 w78_44 w78_38 w78_34 w78_30 w78_2c g78_11 g78_27 g78_26 g78_25 g78_24 g78_23 g78_22 g78_21 g78_20 g78_19 g78_18 g78_10 g78_9 g78_8 g78_4 g78_3 g78_2 V78 E78 fR78 t78 fr78 rb78 s78 m78 u78 c78
  -- 0x70E: lw
  obtain ⟨n80, d80, u80⟩ := s79.lw E79.self sv_at_70e (off' := 0x710) (by decide)
    (by rw [g79_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s80 : St n80.mem SV n80 0x710 (reg n80) := ⟨u80.pc, rfl, fun _ => rfl⟩
  have m80 : n80.mem = n79.mem := u80.mem
  have fr80 : ∀ x, SvR B x → n80.mem x = n79.mem x := fun x _ => by rw [m80]
  have t80 : Steps n0 n80 := t79.trans (.single d80)
  have fR80 : ∀ x, SvR B x → n80.mem x = M0 x := fun x hx => (fr80 x hx).trans (fR79 x hx)
  have E80 : SvCode n80.mem := E79.fr F fr80
  have V80 : SvSaves B n80.mem v := V79.same m80
  have g80_2 : reg n80 sp = B + 0x21A0 := by rw [u80.regs, upd_ne (by decide) (by decide), g79_2]
  have g80_3 : reg n80 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u80.regs, upd_ne (by decide) (by decide), g79_3]
  have g80_4 : reg n80 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u80.regs, upd_ne (by decide) (by decide), g79_4]
  have g80_8 : reg n80 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u80.regs, upd_ne (by decide) (by decide), g79_8]
  have g80_9 : reg n80 (9 : Fin 32) = tbp := by rw [u80.regs, upd_ne (by decide) (by decide), g79_9]
  have g80_10 : reg n80 a0 = BitVec.ofNat 32 (img% svConstExtAddress + 0x55) := by rw [u80.regs, upd_ne (by decide) (by decide), g79_10]
  have g80_11 : reg n80 a1 = BitVec.ofNat 32 0xA := by rw [u80.regs, upd_ne (by decide) (by decide), g79_11]
  have g80_12 : reg n80 a2 = op := by rw [u80.regs, upd_ne (by decide) (by decide), g79_12]
  have g80_18 : reg n80 (18 : Fin 32) = out := by rw [u80.regs, upd_ne (by decide) (by decide), g79_18]
  have g80_19 : reg n80 (19 : Fin 32) = bp := by rw [u80.regs, upd_ne (by decide) (by decide), g79_19]
  have g80_20 : reg n80 (20 : Fin 32) = dg := by rw [u80.regs, upd_ne (by decide) (by decide), g79_20]
  have g80_21 : reg n80 (21 : Fin 32) = rootp := by rw [u80.regs, upd_ne (by decide) (by decide), g79_21]
  have g80_22 : reg n80 (22 : Fin 32) = ll := by rw [u80.regs, upd_ne (by decide) (by decide), g79_22]
  have g80_23 : reg n80 (23 : Fin 32) = sgp := by rw [u80.regs, upd_ne (by decide) (by decide), g79_23]
  have g80_24 : reg n80 (24 : Fin 32) = kp := by rw [u80.regs, upd_ne (by decide) (by decide), g79_24]
  have g80_25 : reg n80 (25 : Fin 32) = sgl := by rw [u80.regs, upd_ne (by decide) (by decide), g79_25]
  have g80_26 : reg n80 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by rw [u80.regs, upd_ne (by decide) (by decide), g79_26]
  have g80_27 : reg n80 (27 : Fin 32) = tbl := by rw [u80.regs, upd_ne (by decide) (by decide), g79_27]
  have g80_13 : reg n80 a3 = ol := by
    rw [u80.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g79_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w79_48]
  have keep_kk80 : SvKeepL B n0.mem n80.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m80]; exact keep_kk79
  clear keep_kk79
  have w80_2c : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m80]; exact w79_2c
  have w80_30 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m80]; exact w79_30
  have w80_34 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m80]; exact w79_34
  have w80_38 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m80]; exact w79_38
  have w80_44 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m80]; exact w79_44
  have w80_48 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m80]; exact w79_48
  have w80_4c : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m80]; exact w79_4c
  have w80_50 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m80]; exact w79_50
  have w80_54 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m80]; exact w79_54
  have w80_58 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m80]; exact w79_58
  have w80_5c : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m80]; exact w79_5c
  have w80_60 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m80]; exact w79_60
  have w80_64 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m80]; exact w79_64
  have w80_68 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m80]; exact w79_68
  have w80_6c : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m80]; exact w79_6c
  have w80_70 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m80]; exact w79_70
  have w80_74 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m80]; exact w79_74
  have w80_78 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m80]; exact w79_78
  have w80_7c : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m80]; exact w79_7c
  have w80_80 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m80]; exact w79_80
  have w80_84 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m80]; exact w79_84
  have w80_88 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m80]; exact w79_88
  have w80_8c : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m80]; exact w79_8c
  have w80_90 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m80]; exact w79_90
  have w80_94 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m80]; exact w79_94
  have w80_98 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m80]; exact w79_98
  have w80_9c : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m80]; exact w79_9c
  have w80_a0 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m80]; exact w79_a0
  have w80_a4 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m80]; exact w79_a4
  have w80_150 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m80]; exact w79_150
  have w80_154 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m80]; exact w79_154
  have w80_158 : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m80]; exact w79_158
  have w80_15c : memLoad32 n80.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m80]; exact w79_15c
  clear w79_15c w79_158 w79_154 w79_150 w79_a4 w79_a0 w79_9c w79_98 w79_94 w79_90 w79_8c w79_88 w79_84 w79_80 w79_7c w79_78 w79_74 w79_70 w79_6c w79_68 w79_64 w79_60 w79_5c w79_58 w79_54 w79_50 w79_4c w79_48 w79_44 w79_38 w79_34 w79_30 w79_2c g79_12 g79_27 g79_26 g79_25 g79_24 g79_23 g79_22 g79_21 g79_20 g79_19 g79_18 g79_11 g79_10 g79_9 g79_8 g79_4 g79_3 g79_2 V79 E79 fR79 t79 fr79 m79 s79 u79 d79
  -- 0x710: sv_seqEqF
  obtain ⟨n81, c81, s81, rk81, a0_81, K81, fr81⟩ := sv_seqEqF (pl := 10) (ql := ol.toNat)
    F E80 s80 sv_at_710 sv_at_714 (by decide) (by decide) g80_2
    g80_10 g80_11 g80_12 (by rw [g80_13, ofNat_toNat_self]) (.inr ⟨by decide, by decide⟩) (.inl oid_in)
  have t81 : Steps n0 n81 := t80.trans c81
  have fR81 : ∀ x, SvR B x → n81.mem x = M0 x := fun x hx => (fr81 x hx).trans (fR80 x hx)
  have E81 : SvCode n81.mem := E80.fr F fr81
  have V81 : SvSaves B n81.mem v := V80.keepL K81 (by decide)
  rw [sv_mbRo FW fR80 (.inr ⟨by decide, by decide⟩), sv_mbRo FW fR80 (.inl oid_in)] at a0_81
  have g81_2 : reg n81 sp = B + 0x21A0 := by rw [rk81 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_2]
  have g81_3 : reg n81 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk81 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_3]
  have g81_4 : reg n81 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk81 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_4]
  have g81_8 : reg n81 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk81 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_8]
  have g81_9 : reg n81 (9 : Fin 32) = tbp := by rw [rk81 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_9]
  have g81_18 : reg n81 (18 : Fin 32) = out := by rw [rk81 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_18]
  have g81_19 : reg n81 (19 : Fin 32) = bp := by rw [rk81 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_19]
  have g81_20 : reg n81 (20 : Fin 32) = dg := by rw [rk81 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_20]
  have g81_21 : reg n81 (21 : Fin 32) = rootp := by rw [rk81 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_21]
  have g81_22 : reg n81 (22 : Fin 32) = ll := by rw [rk81 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_22]
  have g81_23 : reg n81 (23 : Fin 32) = sgp := by rw [rk81 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_23]
  have g81_24 : reg n81 (24 : Fin 32) = kp := by rw [rk81 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_24]
  have g81_25 : reg n81 (25 : Fin 32) = sgl := by rw [rk81 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_25]
  have g81_26 : reg n81 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by rw [rk81 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_26]
  have g81_27 : reg n81 (27 : Fin 32) = tbl := by rw [rk81 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g80_27]
  have keep_kk81 : SvKeepL B n0.mem n81.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := keep_kk80.trans K81
  clear keep_kk80
  have w81_2c : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K81.w32 (by decide) (by decide)).trans w80_2c
  have w81_30 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K81.w32 (by decide) (by decide)).trans w80_30
  have w81_34 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K81.w32 (by decide) (by decide)).trans w80_34
  have w81_38 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K81.w32 (by decide) (by decide)).trans w80_38
  have w81_44 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K81.w32 (by decide) (by decide)).trans w80_44
  have w81_48 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K81.w32 (by decide) (by decide)).trans w80_48
  have w81_4c : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K81.w32 (by decide) (by decide)).trans w80_4c
  have w81_50 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := (K81.w32 (by decide) (by decide)).trans w80_50
  have w81_54 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K81.w32 (by decide) (by decide)).trans w80_54
  have w81_58 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K81.w32 (by decide) (by decide)).trans w80_58
  have w81_5c : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K81.w32 (by decide) (by decide)).trans w80_5c
  have w81_60 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K81.w32 (by decide) (by decide)).trans w80_60
  have w81_64 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K81.w32 (by decide) (by decide)).trans w80_64
  have w81_68 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K81.w32 (by decide) (by decide)).trans w80_68
  have w81_6c : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K81.w32 (by decide) (by decide)).trans w80_6c
  have w81_70 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K81.w32 (by decide) (by decide)).trans w80_70
  have w81_74 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K81.w32 (by decide) (by decide)).trans w80_74
  have w81_78 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K81.w32 (by decide) (by decide)).trans w80_78
  have w81_7c : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K81.w32 (by decide) (by decide)).trans w80_7c
  have w81_80 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K81.w32 (by decide) (by decide)).trans w80_80
  have w81_84 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K81.w32 (by decide) (by decide)).trans w80_84
  have w81_88 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K81.w32 (by decide) (by decide)).trans w80_88
  have w81_8c : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K81.w32 (by decide) (by decide)).trans w80_8c
  have w81_90 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K81.w32 (by decide) (by decide)).trans w80_90
  have w81_94 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K81.w32 (by decide) (by decide)).trans w80_94
  have w81_98 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K81.w32 (by decide) (by decide)).trans w80_98
  have w81_9c : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K81.w32 (by decide) (by decide)).trans w80_9c
  have w81_a0 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K81.w32 (by decide) (by decide)).trans w80_a0
  have w81_a4 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K81.w32 (by decide) (by decide)).trans w80_a4
  have w81_150 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K81.w32 (by decide) (by decide)).trans w80_150
  have w81_154 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K81.w32 (by decide) (by decide)).trans w80_154
  have w81_158 : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K81.w32 (by decide) (by decide)).trans w80_158
  have w81_15c : memLoad32 n81.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K81.w32 (by decide) (by decide)).trans w80_15c
  clear w80_15c w80_158 w80_154 w80_150 w80_a4 w80_a0 w80_9c w80_98 w80_94 w80_90 w80_8c w80_88 w80_84 w80_80 w80_7c w80_78 w80_74 w80_70 w80_6c w80_68 w80_64 w80_60 w80_5c w80_58 w80_54 w80_50 w80_4c w80_48 w80_44 w80_38 w80_34 w80_30 w80_2c g80_13 g80_27 g80_26 g80_25 g80_24 g80_23 g80_22 g80_21 g80_20 g80_19 g80_18 g80_12 g80_11 g80_10 g80_9 g80_8 g80_4 g80_3 g80_2 V80 E80 fR80 t80 fr80 m80 s80 u80 d80
  have g81_10 : reg n81 a0 = BitVec.ofNat 32 1 := by rw [a0_81, ite_eq_left hp4]; rfl
  -- 0x718: lw
  obtain ⟨n82, d82, u82⟩ := s81.lw E81.self sv_at_718 (off' := 0x71A) (by decide)
    (by rw [g81_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s82 : St n82.mem SV n82 0x71A (reg n82) := ⟨u82.pc, rfl, fun _ => rfl⟩
  have m82 : n82.mem = n81.mem := u82.mem
  have fr82 : ∀ x, SvR B x → n82.mem x = n81.mem x := fun x _ => by rw [m82]
  have t82 : Steps n0 n82 := t81.trans (.single d82)
  have fR82 : ∀ x, SvR B x → n82.mem x = M0 x := fun x hx => (fr82 x hx).trans (fR81 x hx)
  have E82 : SvCode n82.mem := E81.fr F fr82
  have V82 : SvSaves B n82.mem v := V81.same m82
  have g82_2 : reg n82 sp = B + 0x21A0 := by rw [u82.regs, upd_ne (by decide) (by decide), g81_2]
  have g82_3 : reg n82 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u82.regs, upd_ne (by decide) (by decide), g81_3]
  have g82_4 : reg n82 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u82.regs, upd_ne (by decide) (by decide), g81_4]
  have g82_8 : reg n82 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u82.regs, upd_ne (by decide) (by decide), g81_8]
  have g82_9 : reg n82 (9 : Fin 32) = tbp := by rw [u82.regs, upd_ne (by decide) (by decide), g81_9]
  have g82_10 : reg n82 a0 = BitVec.ofNat 32 0x1 := by rw [u82.regs, upd_ne (by decide) (by decide), g81_10]
  have g82_18 : reg n82 (18 : Fin 32) = out := by rw [u82.regs, upd_ne (by decide) (by decide), g81_18]
  have g82_19 : reg n82 (19 : Fin 32) = bp := by rw [u82.regs, upd_ne (by decide) (by decide), g81_19]
  have g82_20 : reg n82 (20 : Fin 32) = dg := by rw [u82.regs, upd_ne (by decide) (by decide), g81_20]
  have g82_21 : reg n82 (21 : Fin 32) = rootp := by rw [u82.regs, upd_ne (by decide) (by decide), g81_21]
  have g82_22 : reg n82 (22 : Fin 32) = ll := by rw [u82.regs, upd_ne (by decide) (by decide), g81_22]
  have g82_23 : reg n82 (23 : Fin 32) = sgp := by rw [u82.regs, upd_ne (by decide) (by decide), g81_23]
  have g82_24 : reg n82 (24 : Fin 32) = kp := by rw [u82.regs, upd_ne (by decide) (by decide), g81_24]
  have g82_25 : reg n82 (25 : Fin 32) = sgl := by rw [u82.regs, upd_ne (by decide) (by decide), g81_25]
  have g82_26 : reg n82 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by rw [u82.regs, upd_ne (by decide) (by decide), g81_26]
  have g82_27 : reg n82 (27 : Fin 32) = tbl := by rw [u82.regs, upd_ne (by decide) (by decide), g81_27]
  have g82_11 : reg n82 a1 = BitVec.ofNat 32 0x3 := by
    rw [u82.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g81_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w81_50]
  have keep_kk82 : SvKeepL B n0.mem n82.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m82]; exact keep_kk81
  clear keep_kk81
  have w82_2c : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m82]; exact w81_2c
  have w82_30 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m82]; exact w81_30
  have w82_34 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m82]; exact w81_34
  have w82_38 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m82]; exact w81_38
  have w82_44 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m82]; exact w81_44
  have w82_48 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m82]; exact w81_48
  have w82_4c : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m82]; exact w81_4c
  have w82_50 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m82]; exact w81_50
  have w82_54 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m82]; exact w81_54
  have w82_58 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m82]; exact w81_58
  have w82_5c : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m82]; exact w81_5c
  have w82_60 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m82]; exact w81_60
  have w82_64 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m82]; exact w81_64
  have w82_68 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m82]; exact w81_68
  have w82_6c : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m82]; exact w81_6c
  have w82_70 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m82]; exact w81_70
  have w82_74 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m82]; exact w81_74
  have w82_78 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m82]; exact w81_78
  have w82_7c : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m82]; exact w81_7c
  have w82_80 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m82]; exact w81_80
  have w82_84 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m82]; exact w81_84
  have w82_88 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m82]; exact w81_88
  have w82_8c : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m82]; exact w81_8c
  have w82_90 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m82]; exact w81_90
  have w82_94 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m82]; exact w81_94
  have w82_98 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m82]; exact w81_98
  have w82_9c : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m82]; exact w81_9c
  have w82_a0 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m82]; exact w81_a0
  have w82_a4 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m82]; exact w81_a4
  have w82_150 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m82]; exact w81_150
  have w82_154 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m82]; exact w81_154
  have w82_158 : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m82]; exact w81_158
  have w82_15c : memLoad32 n82.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m82]; exact w81_15c
  clear w81_15c w81_158 w81_154 w81_150 w81_a4 w81_a0 w81_9c w81_98 w81_94 w81_90 w81_8c w81_88 w81_84 w81_80 w81_7c w81_78 w81_74 w81_70 w81_6c w81_68 w81_64 w81_60 w81_5c w81_58 w81_54 w81_50 w81_4c w81_48 w81_44 w81_38 w81_34 w81_30 w81_2c g81_27 g81_26 g81_25 g81_24 g81_23 g81_22 g81_21 g81_20 g81_19 g81_18 g81_9 g81_8 g81_4 g81_3 g81_2 V81 E81 fR81 t81 fr81 K81 a0_81 rk81 s81 c81
  -- 0x71A
  obtain ⟨n83, c83, u83⟩ := s82.block svDp471a E82.self svDp471a_end
    ⟨trivial, trivial⟩
  have m83 : n83.mem = n82.mem := u83.mem
  have s83 : St n83.mem SV n83 0x71C (reg n83) := ⟨u83.pc, rfl, fun _ => rfl⟩
  have rb83 : ∀ q, reg n83 q = (runBlock svDp471a (n82.mem, reg n82)).2 q := fun q => by rw [u83.regs]
  have fr83 : ∀ x, SvR B x → n83.mem x = n82.mem x := fun x _ => by rw [m83]
  have t83 : Steps n0 n83 := t82.trans c83
  have fR83 : ∀ x, SvR B x → n83.mem x = M0 x := fun x hx => (fr83 x hx).trans (fR82 x hx)
  have E83 : SvCode n83.mem := E82.fr F fr83
  have V83 : SvSaves B n83.mem v := V82.same m83
  have g83_2 : reg n83 sp = B + 0x21A0 := by
    rw [rb83, runBlock_reg _ _ _ sp s82.zero (by decide), g82_2]
  have g83_3 : reg n83 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb83, runBlock_reg _ _ _ (3 : Fin 32) s82.zero (by decide), g82_3]
  have g83_4 : reg n83 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb83, runBlock_reg _ _ _ (4 : Fin 32) s82.zero (by decide), g82_4]
  have g83_8 : reg n83 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb83, runBlock_reg _ _ _ (8 : Fin 32) s82.zero (by decide), g82_8]
  have g83_9 : reg n83 (9 : Fin 32) = tbp := by
    rw [rb83, runBlock_reg _ _ _ (9 : Fin 32) s82.zero (by decide), g82_9]
  have g83_10 : reg n83 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb83, runBlock_reg _ _ _ a0 s82.zero (by decide), g82_10]
  have g83_18 : reg n83 (18 : Fin 32) = out := by
    rw [rb83, runBlock_reg _ _ _ (18 : Fin 32) s82.zero (by decide), g82_18]
  have g83_19 : reg n83 (19 : Fin 32) = bp := by
    rw [rb83, runBlock_reg _ _ _ (19 : Fin 32) s82.zero (by decide), g82_19]
  have g83_20 : reg n83 (20 : Fin 32) = dg := by
    rw [rb83, runBlock_reg _ _ _ (20 : Fin 32) s82.zero (by decide), g82_20]
  have g83_21 : reg n83 (21 : Fin 32) = rootp := by
    rw [rb83, runBlock_reg _ _ _ (21 : Fin 32) s82.zero (by decide), g82_21]
  have g83_22 : reg n83 (22 : Fin 32) = ll := by
    rw [rb83, runBlock_reg _ _ _ (22 : Fin 32) s82.zero (by decide), g82_22]
  have g83_23 : reg n83 (23 : Fin 32) = sgp := by
    rw [rb83, runBlock_reg _ _ _ (23 : Fin 32) s82.zero (by decide), g82_23]
  have g83_24 : reg n83 (24 : Fin 32) = kp := by
    rw [rb83, runBlock_reg _ _ _ (24 : Fin 32) s82.zero (by decide), g82_24]
  have g83_25 : reg n83 (25 : Fin 32) = sgl := by
    rw [rb83, runBlock_reg _ _ _ (25 : Fin 32) s82.zero (by decide), g82_25]
  have g83_26 : reg n83 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by
    rw [rb83, runBlock_reg _ _ _ (26 : Fin 32) s82.zero (by decide), g82_26]
  have g83_27 : reg n83 (27 : Fin 32) = tbl := by
    rw [rb83, runBlock_reg _ _ _ (27 : Fin 32) s82.zero (by decide), g82_27]
  have g83_11 : reg n83 a1 = BitVec.ofNat 32 0x4 := by
    rw [rb83]; simp +decide only [runBlock, BInstr.run, svDp471a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g82_2, g82_3, g82_4, g82_8, g82_9, g82_10, g82_11, g82_18, g82_19, g82_20, g82_21, g82_22, g82_23, g82_24, g82_25, g82_26, g82_27, s82.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk83 : SvKeepL B n0.mem n83.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m83]; exact keep_kk82
  clear keep_kk82
  have w83_2c : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m83]; exact w82_2c
  have w83_30 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m83]; exact w82_30
  have w83_34 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m83]; exact w82_34
  have w83_38 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m83]; exact w82_38
  have w83_44 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m83]; exact w82_44
  have w83_48 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m83]; exact w82_48
  have w83_4c : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m83]; exact w82_4c
  have w83_50 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x3 := by rw [m83]; exact w82_50
  have w83_54 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m83]; exact w82_54
  have w83_58 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m83]; exact w82_58
  have w83_5c : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m83]; exact w82_5c
  have w83_60 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m83]; exact w82_60
  have w83_64 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m83]; exact w82_64
  have w83_68 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m83]; exact w82_68
  have w83_6c : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m83]; exact w82_6c
  have w83_70 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m83]; exact w82_70
  have w83_74 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m83]; exact w82_74
  have w83_78 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m83]; exact w82_78
  have w83_7c : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m83]; exact w82_7c
  have w83_80 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m83]; exact w82_80
  have w83_84 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m83]; exact w82_84
  have w83_88 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m83]; exact w82_88
  have w83_8c : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m83]; exact w82_8c
  have w83_90 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m83]; exact w82_90
  have w83_94 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m83]; exact w82_94
  have w83_98 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m83]; exact w82_98
  have w83_9c : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m83]; exact w82_9c
  have w83_a0 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m83]; exact w82_a0
  have w83_a4 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m83]; exact w82_a4
  have w83_150 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m83]; exact w82_150
  have w83_154 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m83]; exact w82_154
  have w83_158 : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m83]; exact w82_158
  have w83_15c : memLoad32 n83.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m83]; exact w82_15c
  clear w82_15c w82_158 w82_154 w82_150 w82_a4 w82_a0 w82_9c w82_98 w82_94 w82_90 w82_8c w82_88 w82_84 w82_80 w82_7c w82_78 w82_74 w82_70 w82_6c w82_68 w82_64 w82_60 w82_5c w82_58 w82_54 w82_50 w82_4c w82_48 w82_44 w82_38 w82_34 w82_30 w82_2c g82_11 g82_27 g82_26 g82_25 g82_24 g82_23 g82_22 g82_21 g82_20 g82_19 g82_18 g82_10 g82_9 g82_8 g82_4 g82_3 g82_2 V82 E82 fR82 t82 fr82 m82 s82 u82 d82 g81_10
  -- 0x71C: sw
  obtain ⟨n84, d84, s84, fr84, K84, W84, rg84⟩ := sv_sw F E83 s83 sv_at_71c (off' := 0x71E) (c := 0x50)
    (by decide) (by rw [g83_2]; sv_addr) (by decide) (by decide)
  have t84 : Steps n0 n84 := t83.trans d84
  have fR84 : ∀ x, SvR B x → n84.mem x = M0 x := fun x hx => (fr84 x hx).trans (fR83 x hx)
  have E84 : SvCode n84.mem := E83.fr F fr84
  have V84 : SvSaves B n84.mem v := V83.keep K84 (by decide)
  have g84_2 : reg n84 sp = B + 0x21A0 := by rw [rg84 sp, g83_2]
  have g84_3 : reg n84 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg84 (3 : Fin 32), g83_3]
  have g84_4 : reg n84 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg84 (4 : Fin 32), g83_4]
  have g84_8 : reg n84 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg84 (8 : Fin 32), g83_8]
  have g84_9 : reg n84 (9 : Fin 32) = tbp := by rw [rg84 (9 : Fin 32), g83_9]
  have g84_10 : reg n84 a0 = BitVec.ofNat 32 0x1 := by rw [rg84 a0, g83_10]
  have g84_11 : reg n84 a1 = BitVec.ofNat 32 0x4 := by rw [rg84 a1, g83_11]
  have g84_18 : reg n84 (18 : Fin 32) = out := by rw [rg84 (18 : Fin 32), g83_18]
  have g84_19 : reg n84 (19 : Fin 32) = bp := by rw [rg84 (19 : Fin 32), g83_19]
  have g84_20 : reg n84 (20 : Fin 32) = dg := by rw [rg84 (20 : Fin 32), g83_20]
  have g84_21 : reg n84 (21 : Fin 32) = rootp := by rw [rg84 (21 : Fin 32), g83_21]
  have g84_22 : reg n84 (22 : Fin 32) = ll := by rw [rg84 (22 : Fin 32), g83_22]
  have g84_23 : reg n84 (23 : Fin 32) = sgp := by rw [rg84 (23 : Fin 32), g83_23]
  have g84_24 : reg n84 (24 : Fin 32) = kp := by rw [rg84 (24 : Fin 32), g83_24]
  have g84_25 : reg n84 (25 : Fin 32) = sgl := by rw [rg84 (25 : Fin 32), g83_25]
  have g84_26 : reg n84 (26 : Fin 32) = BitVec.ofNat 32 (img% svConstExtAddress + 0x81) := by rw [rg84 (26 : Fin 32), g83_26]
  have g84_27 : reg n84 (27 : Fin 32) = tbl := by rw [rg84 (27 : Fin 32), g83_27]
  have keep_kk84 : SvKeepL B n0.mem n84.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := keep_kk83.trans K84.toL
  clear keep_kk83
  have w84_2c : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K84.w32 (by decide) (by decide)).trans w83_2c
  have w84_30 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K84.w32 (by decide) (by decide)).trans w83_30
  have w84_34 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K84.w32 (by decide) (by decide)).trans w83_34
  have w84_38 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K84.w32 (by decide) (by decide)).trans w83_38
  have w84_44 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K84.w32 (by decide) (by decide)).trans w83_44
  have w84_48 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K84.w32 (by decide) (by decide)).trans w83_48
  have w84_4c : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K84.w32 (by decide) (by decide)).trans w83_4c
  have w84_54 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K84.w32 (by decide) (by decide)).trans w83_54
  have w84_58 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K84.w32 (by decide) (by decide)).trans w83_58
  have w84_5c : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K84.w32 (by decide) (by decide)).trans w83_5c
  have w84_60 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K84.w32 (by decide) (by decide)).trans w83_60
  have w84_64 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K84.w32 (by decide) (by decide)).trans w83_64
  have w84_68 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K84.w32 (by decide) (by decide)).trans w83_68
  have w84_6c : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K84.w32 (by decide) (by decide)).trans w83_6c
  have w84_70 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K84.w32 (by decide) (by decide)).trans w83_70
  have w84_74 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K84.w32 (by decide) (by decide)).trans w83_74
  have w84_78 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K84.w32 (by decide) (by decide)).trans w83_78
  have w84_7c : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K84.w32 (by decide) (by decide)).trans w83_7c
  have w84_80 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K84.w32 (by decide) (by decide)).trans w83_80
  have w84_84 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K84.w32 (by decide) (by decide)).trans w83_84
  have w84_88 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K84.w32 (by decide) (by decide)).trans w83_88
  have w84_8c : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K84.w32 (by decide) (by decide)).trans w83_8c
  have w84_90 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K84.w32 (by decide) (by decide)).trans w83_90
  have w84_94 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K84.w32 (by decide) (by decide)).trans w83_94
  have w84_98 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K84.w32 (by decide) (by decide)).trans w83_98
  have w84_9c : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K84.w32 (by decide) (by decide)).trans w83_9c
  have w84_a0 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K84.w32 (by decide) (by decide)).trans w83_a0
  have w84_a4 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K84.w32 (by decide) (by decide)).trans w83_a4
  have w84_150 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K84.w32 (by decide) (by decide)).trans w83_150
  have w84_154 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K84.w32 (by decide) (by decide)).trans w83_154
  have w84_158 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K84.w32 (by decide) (by decide)).trans w83_158
  have w84_15c : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K84.w32 (by decide) (by decide)).trans w83_15c
  have w84_50 : memLoad32 n84.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [W84, g83_11]
  clear w83_15c w83_158 w83_154 w83_150 w83_a4 w83_a0 w83_9c w83_98 w83_94 w83_90 w83_8c w83_88 w83_84 w83_80 w83_7c w83_78 w83_74 w83_70 w83_6c w83_68 w83_64 w83_60 w83_5c w83_58 w83_54 w83_50 w83_4c w83_48 w83_44 w83_38 w83_34 w83_30 w83_2c g83_11 g83_27 g83_26 g83_25 g83_24 g83_23 g83_22 g83_21 g83_20 g83_19 g83_18 g83_10 g83_9 g83_8 g83_4 g83_3 g83_2 V83 E83 fR83 t83 fr83 rb83 s83 m83 u83 c83
  -- 0x71E
  obtain ⟨n85, c85, u85⟩ := s84.block svDp471e E84.self svDp471e_end
    ⟨trivial, trivial⟩
  have m85 : n85.mem = n84.mem := u85.mem
  have s85 : St n85.mem SV n85 0x720 (reg n85) := ⟨u85.pc, rfl, fun _ => rfl⟩
  have rb85 : ∀ q, reg n85 q = (runBlock svDp471e (n84.mem, reg n84)).2 q := fun q => by rw [u85.regs]
  have fr85 : ∀ x, SvR B x → n85.mem x = n84.mem x := fun x _ => by rw [m85]
  have t85 : Steps n0 n85 := t84.trans c85
  have fR85 : ∀ x, SvR B x → n85.mem x = M0 x := fun x hx => (fr85 x hx).trans (fR84 x hx)
  have E85 : SvCode n85.mem := E84.fr F fr85
  have V85 : SvSaves B n85.mem v := V84.same m85
  have g85_2 : reg n85 sp = B + 0x21A0 := by
    rw [rb85, runBlock_reg _ _ _ sp s84.zero (by decide), g84_2]
  have g85_3 : reg n85 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb85, runBlock_reg _ _ _ (3 : Fin 32) s84.zero (by decide), g84_3]
  have g85_4 : reg n85 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb85, runBlock_reg _ _ _ (4 : Fin 32) s84.zero (by decide), g84_4]
  have g85_8 : reg n85 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb85, runBlock_reg _ _ _ (8 : Fin 32) s84.zero (by decide), g84_8]
  have g85_9 : reg n85 (9 : Fin 32) = tbp := by
    rw [rb85, runBlock_reg _ _ _ (9 : Fin 32) s84.zero (by decide), g84_9]
  have g85_10 : reg n85 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb85, runBlock_reg _ _ _ a0 s84.zero (by decide), g84_10]
  have g85_11 : reg n85 a1 = BitVec.ofNat 32 0x4 := by
    rw [rb85, runBlock_reg _ _ _ a1 s84.zero (by decide), g84_11]
  have g85_18 : reg n85 (18 : Fin 32) = out := by
    rw [rb85, runBlock_reg _ _ _ (18 : Fin 32) s84.zero (by decide), g84_18]
  have g85_19 : reg n85 (19 : Fin 32) = bp := by
    rw [rb85, runBlock_reg _ _ _ (19 : Fin 32) s84.zero (by decide), g84_19]
  have g85_20 : reg n85 (20 : Fin 32) = dg := by
    rw [rb85, runBlock_reg _ _ _ (20 : Fin 32) s84.zero (by decide), g84_20]
  have g85_21 : reg n85 (21 : Fin 32) = rootp := by
    rw [rb85, runBlock_reg _ _ _ (21 : Fin 32) s84.zero (by decide), g84_21]
  have g85_22 : reg n85 (22 : Fin 32) = ll := by
    rw [rb85, runBlock_reg _ _ _ (22 : Fin 32) s84.zero (by decide), g84_22]
  have g85_23 : reg n85 (23 : Fin 32) = sgp := by
    rw [rb85, runBlock_reg _ _ _ (23 : Fin 32) s84.zero (by decide), g84_23]
  have g85_24 : reg n85 (24 : Fin 32) = kp := by
    rw [rb85, runBlock_reg _ _ _ (24 : Fin 32) s84.zero (by decide), g84_24]
  have g85_25 : reg n85 (25 : Fin 32) = sgl := by
    rw [rb85, runBlock_reg _ _ _ (25 : Fin 32) s84.zero (by decide), g84_25]
  have g85_27 : reg n85 (27 : Fin 32) = tbl := by
    rw [rb85, runBlock_reg _ _ _ (27 : Fin 32) s84.zero (by decide), g84_27]
  have g85_26 : reg n85 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by
    rw [rb85]; simp +decide only [runBlock, BInstr.run, svDp471e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g84_2, g84_3, g84_4, g84_8, g84_9, g84_10, g84_11, g84_18, g84_19, g84_20, g84_21, g84_22, g84_23, g84_24, g84_25, g84_26, g84_27, s84.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk85 : SvKeepL B n0.mem n85.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m85]; exact keep_kk84
  clear keep_kk84
  have w85_2c : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m85]; exact w84_2c
  have w85_30 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m85]; exact w84_30
  have w85_34 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m85]; exact w84_34
  have w85_38 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m85]; exact w84_38
  have w85_44 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m85]; exact w84_44
  have w85_48 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m85]; exact w84_48
  have w85_4c : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m85]; exact w84_4c
  have w85_50 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m85]; exact w84_50
  have w85_54 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m85]; exact w84_54
  have w85_58 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m85]; exact w84_58
  have w85_5c : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m85]; exact w84_5c
  have w85_60 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m85]; exact w84_60
  have w85_64 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m85]; exact w84_64
  have w85_68 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m85]; exact w84_68
  have w85_6c : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m85]; exact w84_6c
  have w85_70 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m85]; exact w84_70
  have w85_74 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m85]; exact w84_74
  have w85_78 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m85]; exact w84_78
  have w85_7c : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m85]; exact w84_7c
  have w85_80 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m85]; exact w84_80
  have w85_84 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m85]; exact w84_84
  have w85_88 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m85]; exact w84_88
  have w85_8c : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m85]; exact w84_8c
  have w85_90 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m85]; exact w84_90
  have w85_94 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m85]; exact w84_94
  have w85_98 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m85]; exact w84_98
  have w85_9c : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m85]; exact w84_9c
  have w85_a0 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m85]; exact w84_a0
  have w85_a4 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m85]; exact w84_a4
  have w85_150 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m85]; exact w84_150
  have w85_154 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m85]; exact w84_154
  have w85_158 : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m85]; exact w84_158
  have w85_15c : memLoad32 n85.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m85]; exact w84_15c
  clear w84_50 w84_15c w84_158 w84_154 w84_150 w84_a4 w84_a0 w84_9c w84_98 w84_94 w84_90 w84_8c w84_88 w84_84 w84_80 w84_7c w84_78 w84_74 w84_70 w84_6c w84_68 w84_64 w84_60 w84_5c w84_58 w84_54 w84_4c w84_48 w84_44 w84_38 w84_34 w84_30 w84_2c g84_27 g84_26 g84_25 g84_24 g84_23 g84_22 g84_21 g84_20 g84_19 g84_18 g84_11 g84_10 g84_9 g84_8 g84_4 g84_3 g84_2 V84 E84 fR84 t84 rg84 W84 K84 fr84 s84 d84
  -- 0x720: branch, not taken
  obtain ⟨n86, d86, u86⟩ := s85.notTaken E85.self 0x722 sv_at_720
    (by decide) (by rw [g85_10, s85.zero]; decide)
  have s86 : St n86.mem SV n86 0x722 (reg n86) := ⟨u86.pc, rfl, fun _ => rfl⟩
  have m86 : n86.mem = n85.mem := u86.mem
  have fr86 : ∀ x, SvR B x → n86.mem x = n85.mem x := fun x _ => by rw [m86]
  have t86 : Steps n0 n86 := t85.trans (.single d86)
  have fR86 : ∀ x, SvR B x → n86.mem x = M0 x := fun x hx => (fr86 x hx).trans (fR85 x hx)
  have E86 : SvCode n86.mem := E85.fr F fr86
  have V86 : SvSaves B n86.mem v := V85.same m86
  have g86_2 : reg n86 sp = B + 0x21A0 := by rw [u86.regs, g85_2]
  have g86_3 : reg n86 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u86.regs, g85_3]
  have g86_4 : reg n86 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u86.regs, g85_4]
  have g86_8 : reg n86 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u86.regs, g85_8]
  have g86_9 : reg n86 (9 : Fin 32) = tbp := by rw [u86.regs, g85_9]
  have g86_10 : reg n86 a0 = BitVec.ofNat 32 0x1 := by rw [u86.regs, g85_10]
  have g86_11 : reg n86 a1 = BitVec.ofNat 32 0x4 := by rw [u86.regs, g85_11]
  have g86_18 : reg n86 (18 : Fin 32) = out := by rw [u86.regs, g85_18]
  have g86_19 : reg n86 (19 : Fin 32) = bp := by rw [u86.regs, g85_19]
  have g86_20 : reg n86 (20 : Fin 32) = dg := by rw [u86.regs, g85_20]
  have g86_21 : reg n86 (21 : Fin 32) = rootp := by rw [u86.regs, g85_21]
  have g86_22 : reg n86 (22 : Fin 32) = ll := by rw [u86.regs, g85_22]
  have g86_23 : reg n86 (23 : Fin 32) = sgp := by rw [u86.regs, g85_23]
  have g86_24 : reg n86 (24 : Fin 32) = kp := by rw [u86.regs, g85_24]
  have g86_25 : reg n86 (25 : Fin 32) = sgl := by rw [u86.regs, g85_25]
  have g86_26 : reg n86 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u86.regs, g85_26]
  have g86_27 : reg n86 (27 : Fin 32) = tbl := by rw [u86.regs, g85_27]
  have keep_kk86 : SvKeepL B n0.mem n86.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m86]; exact keep_kk85
  clear keep_kk85
  have w86_2c : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m86]; exact w85_2c
  have w86_30 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m86]; exact w85_30
  have w86_34 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m86]; exact w85_34
  have w86_38 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m86]; exact w85_38
  have w86_44 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m86]; exact w85_44
  have w86_48 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m86]; exact w85_48
  have w86_4c : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m86]; exact w85_4c
  have w86_50 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m86]; exact w85_50
  have w86_54 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m86]; exact w85_54
  have w86_58 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m86]; exact w85_58
  have w86_5c : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m86]; exact w85_5c
  have w86_60 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m86]; exact w85_60
  have w86_64 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m86]; exact w85_64
  have w86_68 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m86]; exact w85_68
  have w86_6c : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m86]; exact w85_6c
  have w86_70 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m86]; exact w85_70
  have w86_74 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m86]; exact w85_74
  have w86_78 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m86]; exact w85_78
  have w86_7c : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m86]; exact w85_7c
  have w86_80 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m86]; exact w85_80
  have w86_84 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m86]; exact w85_84
  have w86_88 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m86]; exact w85_88
  have w86_8c : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m86]; exact w85_8c
  have w86_90 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m86]; exact w85_90
  have w86_94 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m86]; exact w85_94
  have w86_98 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m86]; exact w85_98
  have w86_9c : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m86]; exact w85_9c
  have w86_a0 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m86]; exact w85_a0
  have w86_a4 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m86]; exact w85_a4
  have w86_150 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m86]; exact w85_150
  have w86_154 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m86]; exact w85_154
  have w86_158 : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m86]; exact w85_158
  have w86_15c : memLoad32 n86.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m86]; exact w85_15c
  clear w85_15c w85_158 w85_154 w85_150 w85_a4 w85_a0 w85_9c w85_98 w85_94 w85_90 w85_8c w85_88 w85_84 w85_80 w85_7c w85_78 w85_74 w85_70 w85_6c w85_68 w85_64 w85_60 w85_5c w85_58 w85_54 w85_50 w85_4c w85_48 w85_44 w85_38 w85_34 w85_30 w85_2c g85_26 g85_27 g85_25 g85_24 g85_23 g85_22 g85_21 g85_20 g85_19 g85_18 g85_11 g85_10 g85_9 g85_8 g85_4 g85_3 g85_2 V85 E85 fR85 t85 fr85 rb85 s85 m85 u85 c85
  -- 0x722: lw
  obtain ⟨n87, d87, u87⟩ := s86.lw E86.self sv_at_722 (off' := 0x724) (by decide)
    (by rw [g86_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s87 : St n87.mem SV n87 0x724 (reg n87) := ⟨u87.pc, rfl, fun _ => rfl⟩
  have m87 : n87.mem = n86.mem := u87.mem
  have fr87 : ∀ x, SvR B x → n87.mem x = n86.mem x := fun x _ => by rw [m87]
  have t87 : Steps n0 n87 := t86.trans (.single d87)
  have fR87 : ∀ x, SvR B x → n87.mem x = M0 x := fun x hx => (fr87 x hx).trans (fR86 x hx)
  have E87 : SvCode n87.mem := E86.fr F fr87
  have V87 : SvSaves B n87.mem v := V86.same m87
  have g87_2 : reg n87 sp = B + 0x21A0 := by rw [u87.regs, upd_ne (by decide) (by decide), g86_2]
  have g87_3 : reg n87 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u87.regs, upd_ne (by decide) (by decide), g86_3]
  have g87_4 : reg n87 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u87.regs, upd_ne (by decide) (by decide), g86_4]
  have g87_8 : reg n87 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u87.regs, upd_ne (by decide) (by decide), g86_8]
  have g87_9 : reg n87 (9 : Fin 32) = tbp := by rw [u87.regs, upd_ne (by decide) (by decide), g86_9]
  have g87_11 : reg n87 a1 = BitVec.ofNat 32 0x4 := by rw [u87.regs, upd_ne (by decide) (by decide), g86_11]
  have g87_18 : reg n87 (18 : Fin 32) = out := by rw [u87.regs, upd_ne (by decide) (by decide), g86_18]
  have g87_19 : reg n87 (19 : Fin 32) = bp := by rw [u87.regs, upd_ne (by decide) (by decide), g86_19]
  have g87_20 : reg n87 (20 : Fin 32) = dg := by rw [u87.regs, upd_ne (by decide) (by decide), g86_20]
  have g87_21 : reg n87 (21 : Fin 32) = rootp := by rw [u87.regs, upd_ne (by decide) (by decide), g86_21]
  have g87_22 : reg n87 (22 : Fin 32) = ll := by rw [u87.regs, upd_ne (by decide) (by decide), g86_22]
  have g87_23 : reg n87 (23 : Fin 32) = sgp := by rw [u87.regs, upd_ne (by decide) (by decide), g86_23]
  have g87_24 : reg n87 (24 : Fin 32) = kp := by rw [u87.regs, upd_ne (by decide) (by decide), g86_24]
  have g87_25 : reg n87 (25 : Fin 32) = sgl := by rw [u87.regs, upd_ne (by decide) (by decide), g86_25]
  have g87_26 : reg n87 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u87.regs, upd_ne (by decide) (by decide), g86_26]
  have g87_27 : reg n87 (27 : Fin 32) = tbl := by rw [u87.regs, upd_ne (by decide) (by decide), g86_27]
  have g87_10 : reg n87 a0 = vp := by
    rw [u87.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g86_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr, w86_38]
  have keep_kk87 : SvKeepL B n0.mem n87.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m87]; exact keep_kk86
  clear keep_kk86
  have w87_2c : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m87]; exact w86_2c
  have w87_30 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m87]; exact w86_30
  have w87_34 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m87]; exact w86_34
  have w87_38 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m87]; exact w86_38
  have w87_44 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m87]; exact w86_44
  have w87_48 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m87]; exact w86_48
  have w87_4c : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m87]; exact w86_4c
  have w87_50 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m87]; exact w86_50
  have w87_54 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m87]; exact w86_54
  have w87_58 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m87]; exact w86_58
  have w87_5c : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m87]; exact w86_5c
  have w87_60 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m87]; exact w86_60
  have w87_64 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m87]; exact w86_64
  have w87_68 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m87]; exact w86_68
  have w87_6c : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m87]; exact w86_6c
  have w87_70 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m87]; exact w86_70
  have w87_74 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m87]; exact w86_74
  have w87_78 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m87]; exact w86_78
  have w87_7c : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m87]; exact w86_7c
  have w87_80 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m87]; exact w86_80
  have w87_84 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m87]; exact w86_84
  have w87_88 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m87]; exact w86_88
  have w87_8c : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m87]; exact w86_8c
  have w87_90 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m87]; exact w86_90
  have w87_94 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m87]; exact w86_94
  have w87_98 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m87]; exact w86_98
  have w87_9c : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m87]; exact w86_9c
  have w87_a0 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m87]; exact w86_a0
  have w87_a4 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m87]; exact w86_a4
  have w87_150 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m87]; exact w86_150
  have w87_154 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m87]; exact w86_154
  have w87_158 : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m87]; exact w86_158
  have w87_15c : memLoad32 n87.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m87]; exact w86_15c
  clear w86_15c w86_158 w86_154 w86_150 w86_a4 w86_a0 w86_9c w86_98 w86_94 w86_90 w86_8c w86_88 w86_84 w86_80 w86_7c w86_78 w86_74 w86_70 w86_6c w86_68 w86_64 w86_60 w86_5c w86_58 w86_54 w86_50 w86_4c w86_48 w86_44 w86_38 w86_34 w86_30 w86_2c g86_27 g86_26 g86_25 g86_24 g86_23 g86_22 g86_21 g86_20 g86_19 g86_18 g86_11 g86_10 g86_9 g86_8 g86_4 g86_3 g86_2 V86 E86 fR86 t86 fr86 m86 s86 u86 d86
  -- 0x724
  obtain ⟨n88, c88, u88⟩ := s87.block svDp4724 E87.self svDp4724_end
    ⟨trivial, trivial⟩
  have m88 : n88.mem = n87.mem := u88.mem
  have s88 : St n88.mem SV n88 0x726 (reg n88) := ⟨u88.pc, rfl, fun _ => rfl⟩
  have rb88 : ∀ q, reg n88 q = (runBlock svDp4724 (n87.mem, reg n87)).2 q := fun q => by rw [u88.regs]
  have fr88 : ∀ x, SvR B x → n88.mem x = n87.mem x := fun x _ => by rw [m88]
  have t88 : Steps n0 n88 := t87.trans c88
  have fR88 : ∀ x, SvR B x → n88.mem x = M0 x := fun x hx => (fr88 x hx).trans (fR87 x hx)
  have E88 : SvCode n88.mem := E87.fr F fr88
  have V88 : SvSaves B n88.mem v := V87.same m88
  have g88_2 : reg n88 sp = B + 0x21A0 := by
    rw [rb88, runBlock_reg _ _ _ sp s87.zero (by decide), g87_2]
  have g88_3 : reg n88 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb88, runBlock_reg _ _ _ (3 : Fin 32) s87.zero (by decide), g87_3]
  have g88_4 : reg n88 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb88, runBlock_reg _ _ _ (4 : Fin 32) s87.zero (by decide), g87_4]
  have g88_8 : reg n88 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb88, runBlock_reg _ _ _ (8 : Fin 32) s87.zero (by decide), g87_8]
  have g88_9 : reg n88 (9 : Fin 32) = tbp := by
    rw [rb88, runBlock_reg _ _ _ (9 : Fin 32) s87.zero (by decide), g87_9]
  have g88_10 : reg n88 a0 = vp := by
    rw [rb88, runBlock_reg _ _ _ a0 s87.zero (by decide), g87_10]
  have g88_11 : reg n88 a1 = BitVec.ofNat 32 0x4 := by
    rw [rb88, runBlock_reg _ _ _ a1 s87.zero (by decide), g87_11]
  have g88_18 : reg n88 (18 : Fin 32) = out := by
    rw [rb88, runBlock_reg _ _ _ (18 : Fin 32) s87.zero (by decide), g87_18]
  have g88_19 : reg n88 (19 : Fin 32) = bp := by
    rw [rb88, runBlock_reg _ _ _ (19 : Fin 32) s87.zero (by decide), g87_19]
  have g88_20 : reg n88 (20 : Fin 32) = dg := by
    rw [rb88, runBlock_reg _ _ _ (20 : Fin 32) s87.zero (by decide), g87_20]
  have g88_21 : reg n88 (21 : Fin 32) = rootp := by
    rw [rb88, runBlock_reg _ _ _ (21 : Fin 32) s87.zero (by decide), g87_21]
  have g88_22 : reg n88 (22 : Fin 32) = ll := by
    rw [rb88, runBlock_reg _ _ _ (22 : Fin 32) s87.zero (by decide), g87_22]
  have g88_23 : reg n88 (23 : Fin 32) = sgp := by
    rw [rb88, runBlock_reg _ _ _ (23 : Fin 32) s87.zero (by decide), g87_23]
  have g88_24 : reg n88 (24 : Fin 32) = kp := by
    rw [rb88, runBlock_reg _ _ _ (24 : Fin 32) s87.zero (by decide), g87_24]
  have g88_25 : reg n88 (25 : Fin 32) = sgl := by
    rw [rb88, runBlock_reg _ _ _ (25 : Fin 32) s87.zero (by decide), g87_25]
  have g88_26 : reg n88 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by
    rw [rb88, runBlock_reg _ _ _ (26 : Fin 32) s87.zero (by decide), g87_26]
  have g88_27 : reg n88 (27 : Fin 32) = tbl := by
    rw [rb88, runBlock_reg _ _ _ (27 : Fin 32) s87.zero (by decide), g87_27]
  have g88_12 : reg n88 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb88]; simp +decide only [runBlock, BInstr.run, svDp4724, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g87_2, g87_3, g87_4, g87_8, g87_9, g87_10, g87_11, g87_18, g87_19, g87_20, g87_21, g87_22, g87_23, g87_24, g87_25, g87_26, g87_27, s87.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk88 : SvKeepL B n0.mem n88.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4)] := by rw [m88]; exact keep_kk87
  clear keep_kk87
  have w88_2c : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m88]; exact w87_2c
  have w88_30 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m88]; exact w87_30
  have w88_34 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m88]; exact w87_34
  have w88_38 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m88]; exact w87_38
  have w88_44 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m88]; exact w87_44
  have w88_48 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m88]; exact w87_48
  have w88_4c : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m88]; exact w87_4c
  have w88_50 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m88]; exact w87_50
  have w88_54 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m88]; exact w87_54
  have w88_58 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m88]; exact w87_58
  have w88_5c : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m88]; exact w87_5c
  have w88_60 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m88]; exact w87_60
  have w88_64 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m88]; exact w87_64
  have w88_68 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m88]; exact w87_68
  have w88_6c : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m88]; exact w87_6c
  have w88_70 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m88]; exact w87_70
  have w88_74 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m88]; exact w87_74
  have w88_78 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m88]; exact w87_78
  have w88_7c : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m88]; exact w87_7c
  have w88_80 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m88]; exact w87_80
  have w88_84 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m88]; exact w87_84
  have w88_88 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m88]; exact w87_88
  have w88_8c : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m88]; exact w87_8c
  have w88_90 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m88]; exact w87_90
  have w88_94 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m88]; exact w87_94
  have w88_98 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m88]; exact w87_98
  have w88_9c : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m88]; exact w87_9c
  have w88_a0 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m88]; exact w87_a0
  have w88_a4 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m88]; exact w87_a4
  have w88_150 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m88]; exact w87_150
  have w88_154 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m88]; exact w87_154
  have w88_158 : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m88]; exact w87_158
  have w88_15c : memLoad32 n88.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m88]; exact w87_15c
  clear w87_15c w87_158 w87_154 w87_150 w87_a4 w87_a0 w87_9c w87_98 w87_94 w87_90 w87_8c w87_88 w87_84 w87_80 w87_7c w87_78 w87_74 w87_70 w87_6c w87_68 w87_64 w87_60 w87_5c w87_58 w87_54 w87_50 w87_4c w87_48 w87_44 w87_38 w87_34 w87_30 w87_2c g87_10 g87_27 g87_26 g87_25 g87_24 g87_23 g87_22 g87_21 g87_20 g87_19 g87_18 g87_11 g87_9 g87_8 g87_4 g87_3 g87_2 V87 E87 fR87 t87 fr87 m87 s87 u87 d87
  -- 0x726: sw
  obtain ⟨n89, d89, s89, fr89, K89, W89, rg89⟩ := sv_sw F E88 s88 sv_at_726 (off' := 0x728) (c := 0x380)
    (by decide) (by rw [g88_12]; sv_addr) (by decide) (by decide)
  have t89 : Steps n0 n89 := t88.trans d89
  have fR89 : ∀ x, SvR B x → n89.mem x = M0 x := fun x hx => (fr89 x hx).trans (fR88 x hx)
  have E89 : SvCode n89.mem := E88.fr F fr89
  have V89 : SvSaves B n89.mem v := V88.keep K89 (by decide)
  have g89_2 : reg n89 sp = B + 0x21A0 := by rw [rg89 sp, g88_2]
  have g89_3 : reg n89 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg89 (3 : Fin 32), g88_3]
  have g89_4 : reg n89 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg89 (4 : Fin 32), g88_4]
  have g89_8 : reg n89 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg89 (8 : Fin 32), g88_8]
  have g89_9 : reg n89 (9 : Fin 32) = tbp := by rw [rg89 (9 : Fin 32), g88_9]
  have g89_10 : reg n89 a0 = vp := by rw [rg89 a0, g88_10]
  have g89_11 : reg n89 a1 = BitVec.ofNat 32 0x4 := by rw [rg89 a1, g88_11]
  have g89_12 : reg n89 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg89 a2, g88_12]
  have g89_18 : reg n89 (18 : Fin 32) = out := by rw [rg89 (18 : Fin 32), g88_18]
  have g89_19 : reg n89 (19 : Fin 32) = bp := by rw [rg89 (19 : Fin 32), g88_19]
  have g89_20 : reg n89 (20 : Fin 32) = dg := by rw [rg89 (20 : Fin 32), g88_20]
  have g89_21 : reg n89 (21 : Fin 32) = rootp := by rw [rg89 (21 : Fin 32), g88_21]
  have g89_22 : reg n89 (22 : Fin 32) = ll := by rw [rg89 (22 : Fin 32), g88_22]
  have g89_23 : reg n89 (23 : Fin 32) = sgp := by rw [rg89 (23 : Fin 32), g88_23]
  have g89_24 : reg n89 (24 : Fin 32) = kp := by rw [rg89 (24 : Fin 32), g88_24]
  have g89_25 : reg n89 (25 : Fin 32) = sgl := by rw [rg89 (25 : Fin 32), g88_25]
  have g89_26 : reg n89 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [rg89 (26 : Fin 32), g88_26]
  have g89_27 : reg n89 (27 : Fin 32) = tbl := by rw [rg89 (27 : Fin 32), g88_27]
  have keep_kk89 : SvKeepL B n0.mem n89.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4)] := keep_kk88.trans K89.toL
  clear keep_kk88
  have w89_2c : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K89.w32 (by decide) (by decide)).trans w88_2c
  have w89_30 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K89.w32 (by decide) (by decide)).trans w88_30
  have w89_34 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K89.w32 (by decide) (by decide)).trans w88_34
  have w89_38 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K89.w32 (by decide) (by decide)).trans w88_38
  have w89_44 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K89.w32 (by decide) (by decide)).trans w88_44
  have w89_48 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K89.w32 (by decide) (by decide)).trans w88_48
  have w89_4c : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K89.w32 (by decide) (by decide)).trans w88_4c
  have w89_50 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K89.w32 (by decide) (by decide)).trans w88_50
  have w89_54 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K89.w32 (by decide) (by decide)).trans w88_54
  have w89_58 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K89.w32 (by decide) (by decide)).trans w88_58
  have w89_5c : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K89.w32 (by decide) (by decide)).trans w88_5c
  have w89_60 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K89.w32 (by decide) (by decide)).trans w88_60
  have w89_64 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K89.w32 (by decide) (by decide)).trans w88_64
  have w89_68 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K89.w32 (by decide) (by decide)).trans w88_68
  have w89_6c : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K89.w32 (by decide) (by decide)).trans w88_6c
  have w89_70 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K89.w32 (by decide) (by decide)).trans w88_70
  have w89_74 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K89.w32 (by decide) (by decide)).trans w88_74
  have w89_78 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K89.w32 (by decide) (by decide)).trans w88_78
  have w89_7c : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K89.w32 (by decide) (by decide)).trans w88_7c
  have w89_80 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K89.w32 (by decide) (by decide)).trans w88_80
  have w89_84 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K89.w32 (by decide) (by decide)).trans w88_84
  have w89_88 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K89.w32 (by decide) (by decide)).trans w88_88
  have w89_8c : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K89.w32 (by decide) (by decide)).trans w88_8c
  have w89_90 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K89.w32 (by decide) (by decide)).trans w88_90
  have w89_94 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K89.w32 (by decide) (by decide)).trans w88_94
  have w89_98 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K89.w32 (by decide) (by decide)).trans w88_98
  have w89_9c : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K89.w32 (by decide) (by decide)).trans w88_9c
  have w89_a0 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K89.w32 (by decide) (by decide)).trans w88_a0
  have w89_a4 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K89.w32 (by decide) (by decide)).trans w88_a4
  have w89_150 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K89.w32 (by decide) (by decide)).trans w88_150
  have w89_154 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K89.w32 (by decide) (by decide)).trans w88_154
  have w89_158 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K89.w32 (by decide) (by decide)).trans w88_158
  have w89_15c : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K89.w32 (by decide) (by decide)).trans w88_15c
  have w89_380 : memLoad32 n89.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [W89, g88_10]
  clear w88_15c w88_158 w88_154 w88_150 w88_a4 w88_a0 w88_9c w88_98 w88_94 w88_90 w88_8c w88_88 w88_84 w88_80 w88_7c w88_78 w88_74 w88_70 w88_6c w88_68 w88_64 w88_60 w88_5c w88_58 w88_54 w88_50 w88_4c w88_48 w88_44 w88_38 w88_34 w88_30 w88_2c g88_12 g88_27 g88_26 g88_25 g88_24 g88_23 g88_22 g88_21 g88_20 g88_19 g88_18 g88_11 g88_10 g88_9 g88_8 g88_4 g88_3 g88_2 V88 E88 fR88 t88 fr88 rb88 s88 m88 u88 c88
  -- 0x728: lw
  obtain ⟨n90, d90, u90⟩ := s89.lw E89.self sv_at_728 (off' := 0x72A) (by decide)
    (by rw [g89_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s90 : St n90.mem SV n90 0x72A (reg n90) := ⟨u90.pc, rfl, fun _ => rfl⟩
  have m90 : n90.mem = n89.mem := u90.mem
  have fr90 : ∀ x, SvR B x → n90.mem x = n89.mem x := fun x _ => by rw [m90]
  have t90 : Steps n0 n90 := t89.trans (.single d90)
  have fR90 : ∀ x, SvR B x → n90.mem x = M0 x := fun x hx => (fr90 x hx).trans (fR89 x hx)
  have E90 : SvCode n90.mem := E89.fr F fr90
  have V90 : SvSaves B n90.mem v := V89.same m90
  have g90_2 : reg n90 sp = B + 0x21A0 := by rw [u90.regs, upd_ne (by decide) (by decide), g89_2]
  have g90_3 : reg n90 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u90.regs, upd_ne (by decide) (by decide), g89_3]
  have g90_4 : reg n90 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u90.regs, upd_ne (by decide) (by decide), g89_4]
  have g90_8 : reg n90 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u90.regs, upd_ne (by decide) (by decide), g89_8]
  have g90_9 : reg n90 (9 : Fin 32) = tbp := by rw [u90.regs, upd_ne (by decide) (by decide), g89_9]
  have g90_10 : reg n90 a0 = vp := by rw [u90.regs, upd_ne (by decide) (by decide), g89_10]
  have g90_12 : reg n90 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [u90.regs, upd_ne (by decide) (by decide), g89_12]
  have g90_18 : reg n90 (18 : Fin 32) = out := by rw [u90.regs, upd_ne (by decide) (by decide), g89_18]
  have g90_19 : reg n90 (19 : Fin 32) = bp := by rw [u90.regs, upd_ne (by decide) (by decide), g89_19]
  have g90_20 : reg n90 (20 : Fin 32) = dg := by rw [u90.regs, upd_ne (by decide) (by decide), g89_20]
  have g90_21 : reg n90 (21 : Fin 32) = rootp := by rw [u90.regs, upd_ne (by decide) (by decide), g89_21]
  have g90_22 : reg n90 (22 : Fin 32) = ll := by rw [u90.regs, upd_ne (by decide) (by decide), g89_22]
  have g90_23 : reg n90 (23 : Fin 32) = sgp := by rw [u90.regs, upd_ne (by decide) (by decide), g89_23]
  have g90_24 : reg n90 (24 : Fin 32) = kp := by rw [u90.regs, upd_ne (by decide) (by decide), g89_24]
  have g90_25 : reg n90 (25 : Fin 32) = sgl := by rw [u90.regs, upd_ne (by decide) (by decide), g89_25]
  have g90_26 : reg n90 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u90.regs, upd_ne (by decide) (by decide), g89_26]
  have g90_27 : reg n90 (27 : Fin 32) = tbl := by rw [u90.regs, upd_ne (by decide) (by decide), g89_27]
  have g90_11 : reg n90 a1 = vl := by
    rw [u90.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g89_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr, w89_34]
  have keep_kk90 : SvKeepL B n0.mem n90.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4)] := by rw [m90]; exact keep_kk89
  clear keep_kk89
  have w90_2c : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m90]; exact w89_2c
  have w90_30 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m90]; exact w89_30
  have w90_34 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m90]; exact w89_34
  have w90_38 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m90]; exact w89_38
  have w90_44 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m90]; exact w89_44
  have w90_48 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m90]; exact w89_48
  have w90_4c : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m90]; exact w89_4c
  have w90_50 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m90]; exact w89_50
  have w90_54 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m90]; exact w89_54
  have w90_58 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m90]; exact w89_58
  have w90_5c : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m90]; exact w89_5c
  have w90_60 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m90]; exact w89_60
  have w90_64 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m90]; exact w89_64
  have w90_68 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m90]; exact w89_68
  have w90_6c : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m90]; exact w89_6c
  have w90_70 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m90]; exact w89_70
  have w90_74 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m90]; exact w89_74
  have w90_78 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m90]; exact w89_78
  have w90_7c : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m90]; exact w89_7c
  have w90_80 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m90]; exact w89_80
  have w90_84 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m90]; exact w89_84
  have w90_88 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m90]; exact w89_88
  have w90_8c : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m90]; exact w89_8c
  have w90_90 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m90]; exact w89_90
  have w90_94 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m90]; exact w89_94
  have w90_98 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m90]; exact w89_98
  have w90_9c : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m90]; exact w89_9c
  have w90_a0 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m90]; exact w89_a0
  have w90_a4 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m90]; exact w89_a4
  have w90_150 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m90]; exact w89_150
  have w90_154 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m90]; exact w89_154
  have w90_158 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m90]; exact w89_158
  have w90_15c : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m90]; exact w89_15c
  have w90_380 : memLoad32 n90.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m90]; exact w89_380
  clear w89_380 w89_15c w89_158 w89_154 w89_150 w89_a4 w89_a0 w89_9c w89_98 w89_94 w89_90 w89_8c w89_88 w89_84 w89_80 w89_7c w89_78 w89_74 w89_70 w89_6c w89_68 w89_64 w89_60 w89_5c w89_58 w89_54 w89_50 w89_4c w89_48 w89_44 w89_38 w89_34 w89_30 w89_2c g89_27 g89_26 g89_25 g89_24 g89_23 g89_22 g89_21 g89_20 g89_19 g89_18 g89_12 g89_11 g89_10 g89_9 g89_8 g89_4 g89_3 g89_2 V89 E89 fR89 t89 rg89 W89 K89 fr89 s89 d89
  -- 0x72A: sw
  obtain ⟨n91, d91, s91, fr91, K91, W91, rg91⟩ := sv_sw F E90 s90 sv_at_72a (off' := 0x72C) (c := 0x384)
    (by decide) (by rw [g90_12]; sv_addr) (by decide) (by decide)
  have t91 : Steps n0 n91 := t90.trans d91
  have fR91 : ∀ x, SvR B x → n91.mem x = M0 x := fun x hx => (fr91 x hx).trans (fR90 x hx)
  have E91 : SvCode n91.mem := E90.fr F fr91
  have V91 : SvSaves B n91.mem v := V90.keep K91 (by decide)
  have g91_2 : reg n91 sp = B + 0x21A0 := by rw [rg91 sp, g90_2]
  have g91_3 : reg n91 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg91 (3 : Fin 32), g90_3]
  have g91_4 : reg n91 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg91 (4 : Fin 32), g90_4]
  have g91_8 : reg n91 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg91 (8 : Fin 32), g90_8]
  have g91_9 : reg n91 (9 : Fin 32) = tbp := by rw [rg91 (9 : Fin 32), g90_9]
  have g91_10 : reg n91 a0 = vp := by rw [rg91 a0, g90_10]
  have g91_11 : reg n91 a1 = vl := by rw [rg91 a1, g90_11]
  have g91_12 : reg n91 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg91 a2, g90_12]
  have g91_18 : reg n91 (18 : Fin 32) = out := by rw [rg91 (18 : Fin 32), g90_18]
  have g91_19 : reg n91 (19 : Fin 32) = bp := by rw [rg91 (19 : Fin 32), g90_19]
  have g91_20 : reg n91 (20 : Fin 32) = dg := by rw [rg91 (20 : Fin 32), g90_20]
  have g91_21 : reg n91 (21 : Fin 32) = rootp := by rw [rg91 (21 : Fin 32), g90_21]
  have g91_22 : reg n91 (22 : Fin 32) = ll := by rw [rg91 (22 : Fin 32), g90_22]
  have g91_23 : reg n91 (23 : Fin 32) = sgp := by rw [rg91 (23 : Fin 32), g90_23]
  have g91_24 : reg n91 (24 : Fin 32) = kp := by rw [rg91 (24 : Fin 32), g90_24]
  have g91_25 : reg n91 (25 : Fin 32) = sgl := by rw [rg91 (25 : Fin 32), g90_25]
  have g91_26 : reg n91 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [rg91 (26 : Fin 32), g90_26]
  have g91_27 : reg n91 (27 : Fin 32) = tbl := by rw [rg91 (27 : Fin 32), g90_27]
  have keep_kk91 : SvKeepL B n0.mem n91.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4)] := keep_kk90.trans K91.toL
  clear keep_kk90
  have w91_2c : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K91.w32 (by decide) (by decide)).trans w90_2c
  have w91_30 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K91.w32 (by decide) (by decide)).trans w90_30
  have w91_34 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K91.w32 (by decide) (by decide)).trans w90_34
  have w91_38 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K91.w32 (by decide) (by decide)).trans w90_38
  have w91_44 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K91.w32 (by decide) (by decide)).trans w90_44
  have w91_48 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K91.w32 (by decide) (by decide)).trans w90_48
  have w91_4c : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K91.w32 (by decide) (by decide)).trans w90_4c
  have w91_50 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K91.w32 (by decide) (by decide)).trans w90_50
  have w91_54 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K91.w32 (by decide) (by decide)).trans w90_54
  have w91_58 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K91.w32 (by decide) (by decide)).trans w90_58
  have w91_5c : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K91.w32 (by decide) (by decide)).trans w90_5c
  have w91_60 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K91.w32 (by decide) (by decide)).trans w90_60
  have w91_64 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K91.w32 (by decide) (by decide)).trans w90_64
  have w91_68 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K91.w32 (by decide) (by decide)).trans w90_68
  have w91_6c : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K91.w32 (by decide) (by decide)).trans w90_6c
  have w91_70 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K91.w32 (by decide) (by decide)).trans w90_70
  have w91_74 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K91.w32 (by decide) (by decide)).trans w90_74
  have w91_78 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K91.w32 (by decide) (by decide)).trans w90_78
  have w91_7c : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K91.w32 (by decide) (by decide)).trans w90_7c
  have w91_80 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K91.w32 (by decide) (by decide)).trans w90_80
  have w91_84 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K91.w32 (by decide) (by decide)).trans w90_84
  have w91_88 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K91.w32 (by decide) (by decide)).trans w90_88
  have w91_8c : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K91.w32 (by decide) (by decide)).trans w90_8c
  have w91_90 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K91.w32 (by decide) (by decide)).trans w90_90
  have w91_94 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K91.w32 (by decide) (by decide)).trans w90_94
  have w91_98 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K91.w32 (by decide) (by decide)).trans w90_98
  have w91_9c : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K91.w32 (by decide) (by decide)).trans w90_9c
  have w91_a0 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K91.w32 (by decide) (by decide)).trans w90_a0
  have w91_a4 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K91.w32 (by decide) (by decide)).trans w90_a4
  have w91_150 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K91.w32 (by decide) (by decide)).trans w90_150
  have w91_154 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K91.w32 (by decide) (by decide)).trans w90_154
  have w91_158 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K91.w32 (by decide) (by decide)).trans w90_158
  have w91_15c : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K91.w32 (by decide) (by decide)).trans w90_15c
  have w91_380 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K91.w32 (by decide) (by decide)).trans w90_380
  have w91_384 : memLoad32 n91.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [W91, g90_11]
  clear w90_380 w90_15c w90_158 w90_154 w90_150 w90_a4 w90_a0 w90_9c w90_98 w90_94 w90_90 w90_8c w90_88 w90_84 w90_80 w90_7c w90_78 w90_74 w90_70 w90_6c w90_68 w90_64 w90_60 w90_5c w90_58 w90_54 w90_50 w90_4c w90_48 w90_44 w90_38 w90_34 w90_30 w90_2c g90_11 g90_27 g90_26 g90_25 g90_24 g90_23 g90_22 g90_21 g90_20 g90_19 g90_18 g90_12 g90_10 g90_9 g90_8 g90_4 g90_3 g90_2 V90 E90 fR90 t90 fr90 m90 s90 u90 d90
  -- 0x72C: sw
  obtain ⟨n92, d92, s92, fr92, K92, W92, rg92⟩ := sv_sw F E91 s91 sv_at_72c (off' := 0x72E) (c := 0x388)
    (by decide) (by rw [g91_12]; sv_addr) (by decide) (by decide)
  have t92 : Steps n0 n92 := t91.trans d92
  have fR92 : ∀ x, SvR B x → n92.mem x = M0 x := fun x hx => (fr92 x hx).trans (fR91 x hx)
  have E92 : SvCode n92.mem := E91.fr F fr92
  have V92 : SvSaves B n92.mem v := V91.keep K92 (by decide)
  have g92_2 : reg n92 sp = B + 0x21A0 := by rw [rg92 sp, g91_2]
  have g92_3 : reg n92 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg92 (3 : Fin 32), g91_3]
  have g92_4 : reg n92 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg92 (4 : Fin 32), g91_4]
  have g92_8 : reg n92 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg92 (8 : Fin 32), g91_8]
  have g92_9 : reg n92 (9 : Fin 32) = tbp := by rw [rg92 (9 : Fin 32), g91_9]
  have g92_10 : reg n92 a0 = vp := by rw [rg92 a0, g91_10]
  have g92_11 : reg n92 a1 = vl := by rw [rg92 a1, g91_11]
  have g92_12 : reg n92 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg92 a2, g91_12]
  have g92_18 : reg n92 (18 : Fin 32) = out := by rw [rg92 (18 : Fin 32), g91_18]
  have g92_19 : reg n92 (19 : Fin 32) = bp := by rw [rg92 (19 : Fin 32), g91_19]
  have g92_20 : reg n92 (20 : Fin 32) = dg := by rw [rg92 (20 : Fin 32), g91_20]
  have g92_21 : reg n92 (21 : Fin 32) = rootp := by rw [rg92 (21 : Fin 32), g91_21]
  have g92_22 : reg n92 (22 : Fin 32) = ll := by rw [rg92 (22 : Fin 32), g91_22]
  have g92_23 : reg n92 (23 : Fin 32) = sgp := by rw [rg92 (23 : Fin 32), g91_23]
  have g92_24 : reg n92 (24 : Fin 32) = kp := by rw [rg92 (24 : Fin 32), g91_24]
  have g92_25 : reg n92 (25 : Fin 32) = sgl := by rw [rg92 (25 : Fin 32), g91_25]
  have g92_26 : reg n92 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [rg92 (26 : Fin 32), g91_26]
  have g92_27 : reg n92 (27 : Fin 32) = tbl := by rw [rg92 (27 : Fin 32), g91_27]
  have keep_kk92 : SvKeepL B n0.mem n92.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4)] := keep_kk91.trans K92.toL
  clear keep_kk91
  have w92_2c : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K92.w32 (by decide) (by decide)).trans w91_2c
  have w92_30 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K92.w32 (by decide) (by decide)).trans w91_30
  have w92_34 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K92.w32 (by decide) (by decide)).trans w91_34
  have w92_38 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K92.w32 (by decide) (by decide)).trans w91_38
  have w92_44 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K92.w32 (by decide) (by decide)).trans w91_44
  have w92_48 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K92.w32 (by decide) (by decide)).trans w91_48
  have w92_4c : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K92.w32 (by decide) (by decide)).trans w91_4c
  have w92_50 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K92.w32 (by decide) (by decide)).trans w91_50
  have w92_54 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K92.w32 (by decide) (by decide)).trans w91_54
  have w92_58 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K92.w32 (by decide) (by decide)).trans w91_58
  have w92_5c : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K92.w32 (by decide) (by decide)).trans w91_5c
  have w92_60 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K92.w32 (by decide) (by decide)).trans w91_60
  have w92_64 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K92.w32 (by decide) (by decide)).trans w91_64
  have w92_68 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K92.w32 (by decide) (by decide)).trans w91_68
  have w92_6c : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K92.w32 (by decide) (by decide)).trans w91_6c
  have w92_70 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K92.w32 (by decide) (by decide)).trans w91_70
  have w92_74 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K92.w32 (by decide) (by decide)).trans w91_74
  have w92_78 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K92.w32 (by decide) (by decide)).trans w91_78
  have w92_7c : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K92.w32 (by decide) (by decide)).trans w91_7c
  have w92_80 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K92.w32 (by decide) (by decide)).trans w91_80
  have w92_84 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K92.w32 (by decide) (by decide)).trans w91_84
  have w92_88 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K92.w32 (by decide) (by decide)).trans w91_88
  have w92_8c : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K92.w32 (by decide) (by decide)).trans w91_8c
  have w92_90 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K92.w32 (by decide) (by decide)).trans w91_90
  have w92_94 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K92.w32 (by decide) (by decide)).trans w91_94
  have w92_98 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K92.w32 (by decide) (by decide)).trans w91_98
  have w92_9c : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K92.w32 (by decide) (by decide)).trans w91_9c
  have w92_a0 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K92.w32 (by decide) (by decide)).trans w91_a0
  have w92_a4 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K92.w32 (by decide) (by decide)).trans w91_a4
  have w92_150 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K92.w32 (by decide) (by decide)).trans w91_150
  have w92_154 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K92.w32 (by decide) (by decide)).trans w91_154
  have w92_158 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K92.w32 (by decide) (by decide)).trans w91_158
  have w92_15c : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K92.w32 (by decide) (by decide)).trans w91_15c
  have w92_380 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K92.w32 (by decide) (by decide)).trans w91_380
  have w92_384 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K92.w32 (by decide) (by decide)).trans w91_384
  have w92_388 : memLoad32 n92.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = vp := by rw [W92, g91_10]
  clear w91_384 w91_380 w91_15c w91_158 w91_154 w91_150 w91_a4 w91_a0 w91_9c w91_98 w91_94 w91_90 w91_8c w91_88 w91_84 w91_80 w91_7c w91_78 w91_74 w91_70 w91_6c w91_68 w91_64 w91_60 w91_5c w91_58 w91_54 w91_50 w91_4c w91_48 w91_44 w91_38 w91_34 w91_30 w91_2c g91_27 g91_26 g91_25 g91_24 g91_23 g91_22 g91_21 g91_20 g91_19 g91_18 g91_12 g91_11 g91_10 g91_9 g91_8 g91_4 g91_3 g91_2 V91 E91 fR91 t91 rg91 W91 K91 fr91 s91 d91
  -- 0x72E: sw
  obtain ⟨n93, d93, s93, fr93, K93, W93, rg93⟩ := sv_sw F E92 s92 sv_at_72e (off' := 0x730) (c := 0x38C)
    (by decide) (by rw [g92_12]; sv_addr) (by decide) (by decide)
  have t93 : Steps n0 n93 := t92.trans d93
  have fR93 : ∀ x, SvR B x → n93.mem x = M0 x := fun x hx => (fr93 x hx).trans (fR92 x hx)
  have E93 : SvCode n93.mem := E92.fr F fr93
  have V93 : SvSaves B n93.mem v := V92.keep K93 (by decide)
  have g93_2 : reg n93 sp = B + 0x21A0 := by rw [rg93 sp, g92_2]
  have g93_3 : reg n93 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg93 (3 : Fin 32), g92_3]
  have g93_4 : reg n93 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg93 (4 : Fin 32), g92_4]
  have g93_8 : reg n93 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg93 (8 : Fin 32), g92_8]
  have g93_9 : reg n93 (9 : Fin 32) = tbp := by rw [rg93 (9 : Fin 32), g92_9]
  have g93_10 : reg n93 a0 = vp := by rw [rg93 a0, g92_10]
  have g93_11 : reg n93 a1 = vl := by rw [rg93 a1, g92_11]
  have g93_12 : reg n93 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg93 a2, g92_12]
  have g93_18 : reg n93 (18 : Fin 32) = out := by rw [rg93 (18 : Fin 32), g92_18]
  have g93_19 : reg n93 (19 : Fin 32) = bp := by rw [rg93 (19 : Fin 32), g92_19]
  have g93_20 : reg n93 (20 : Fin 32) = dg := by rw [rg93 (20 : Fin 32), g92_20]
  have g93_21 : reg n93 (21 : Fin 32) = rootp := by rw [rg93 (21 : Fin 32), g92_21]
  have g93_22 : reg n93 (22 : Fin 32) = ll := by rw [rg93 (22 : Fin 32), g92_22]
  have g93_23 : reg n93 (23 : Fin 32) = sgp := by rw [rg93 (23 : Fin 32), g92_23]
  have g93_24 : reg n93 (24 : Fin 32) = kp := by rw [rg93 (24 : Fin 32), g92_24]
  have g93_25 : reg n93 (25 : Fin 32) = sgl := by rw [rg93 (25 : Fin 32), g92_25]
  have g93_26 : reg n93 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [rg93 (26 : Fin 32), g92_26]
  have g93_27 : reg n93 (27 : Fin 32) = tbl := by rw [rg93 (27 : Fin 32), g92_27]
  have keep_kk93 : SvKeepL B n0.mem n93.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4)] := keep_kk92.trans K93.toL
  clear keep_kk92
  have w93_2c : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K93.w32 (by decide) (by decide)).trans w92_2c
  have w93_30 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K93.w32 (by decide) (by decide)).trans w92_30
  have w93_34 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K93.w32 (by decide) (by decide)).trans w92_34
  have w93_38 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K93.w32 (by decide) (by decide)).trans w92_38
  have w93_44 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K93.w32 (by decide) (by decide)).trans w92_44
  have w93_48 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K93.w32 (by decide) (by decide)).trans w92_48
  have w93_4c : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K93.w32 (by decide) (by decide)).trans w92_4c
  have w93_50 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K93.w32 (by decide) (by decide)).trans w92_50
  have w93_54 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K93.w32 (by decide) (by decide)).trans w92_54
  have w93_58 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K93.w32 (by decide) (by decide)).trans w92_58
  have w93_5c : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K93.w32 (by decide) (by decide)).trans w92_5c
  have w93_60 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K93.w32 (by decide) (by decide)).trans w92_60
  have w93_64 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K93.w32 (by decide) (by decide)).trans w92_64
  have w93_68 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K93.w32 (by decide) (by decide)).trans w92_68
  have w93_6c : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K93.w32 (by decide) (by decide)).trans w92_6c
  have w93_70 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K93.w32 (by decide) (by decide)).trans w92_70
  have w93_74 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K93.w32 (by decide) (by decide)).trans w92_74
  have w93_78 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K93.w32 (by decide) (by decide)).trans w92_78
  have w93_7c : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K93.w32 (by decide) (by decide)).trans w92_7c
  have w93_80 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K93.w32 (by decide) (by decide)).trans w92_80
  have w93_84 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K93.w32 (by decide) (by decide)).trans w92_84
  have w93_88 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K93.w32 (by decide) (by decide)).trans w92_88
  have w93_8c : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K93.w32 (by decide) (by decide)).trans w92_8c
  have w93_90 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K93.w32 (by decide) (by decide)).trans w92_90
  have w93_94 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K93.w32 (by decide) (by decide)).trans w92_94
  have w93_98 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K93.w32 (by decide) (by decide)).trans w92_98
  have w93_9c : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K93.w32 (by decide) (by decide)).trans w92_9c
  have w93_a0 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K93.w32 (by decide) (by decide)).trans w92_a0
  have w93_a4 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K93.w32 (by decide) (by decide)).trans w92_a4
  have w93_150 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K93.w32 (by decide) (by decide)).trans w92_150
  have w93_154 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K93.w32 (by decide) (by decide)).trans w92_154
  have w93_158 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K93.w32 (by decide) (by decide)).trans w92_158
  have w93_15c : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K93.w32 (by decide) (by decide)).trans w92_15c
  have w93_380 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K93.w32 (by decide) (by decide)).trans w92_380
  have w93_384 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K93.w32 (by decide) (by decide)).trans w92_384
  have w93_388 : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = vp := (K93.w32 (by decide) (by decide)).trans w92_388
  have w93_38c : memLoad32 n93.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = vl := by rw [W93, g92_11]
  clear w92_388 w92_384 w92_380 w92_15c w92_158 w92_154 w92_150 w92_a4 w92_a0 w92_9c w92_98 w92_94 w92_90 w92_8c w92_88 w92_84 w92_80 w92_7c w92_78 w92_74 w92_70 w92_6c w92_68 w92_64 w92_60 w92_5c w92_58 w92_54 w92_50 w92_4c w92_48 w92_44 w92_38 w92_34 w92_30 w92_2c g92_27 g92_26 g92_25 g92_24 g92_23 g92_22 g92_21 g92_20 g92_19 g92_18 g92_12 g92_11 g92_10 g92_9 g92_8 g92_4 g92_3 g92_2 V92 E92 fR92 t92 rg92 W92 K92 fr92 s92 d92
  -- 0x730
  obtain ⟨n94, c94, u94⟩ := s93.block svDp4730 E93.self svDp4730_end
    ⟨trivial, trivial, trivial⟩
  have m94 : n94.mem = n93.mem := u94.mem
  have s94 : St n94.mem SV n94 0x736 (reg n94) := ⟨u94.pc, rfl, fun _ => rfl⟩
  have rb94 : ∀ q, reg n94 q = (runBlock svDp4730 (n93.mem, reg n93)).2 q := fun q => by rw [u94.regs]
  have fr94 : ∀ x, SvR B x → n94.mem x = n93.mem x := fun x _ => by rw [m94]
  have t94 : Steps n0 n94 := t93.trans c94
  have fR94 : ∀ x, SvR B x → n94.mem x = M0 x := fun x hx => (fr94 x hx).trans (fR93 x hx)
  have E94 : SvCode n94.mem := E93.fr F fr94
  have V94 : SvSaves B n94.mem v := V93.same m94
  have g94_2 : reg n94 sp = B + 0x21A0 := by
    rw [rb94, runBlock_reg _ _ _ sp s93.zero (by decide), g93_2]
  have g94_3 : reg n94 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb94, runBlock_reg _ _ _ (3 : Fin 32) s93.zero (by decide), g93_3]
  have g94_4 : reg n94 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb94, runBlock_reg _ _ _ (4 : Fin 32) s93.zero (by decide), g93_4]
  have g94_8 : reg n94 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb94, runBlock_reg _ _ _ (8 : Fin 32) s93.zero (by decide), g93_8]
  have g94_9 : reg n94 (9 : Fin 32) = tbp := by
    rw [rb94, runBlock_reg _ _ _ (9 : Fin 32) s93.zero (by decide), g93_9]
  have g94_12 : reg n94 a2 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb94, runBlock_reg _ _ _ a2 s93.zero (by decide), g93_12]
  have g94_18 : reg n94 (18 : Fin 32) = out := by
    rw [rb94, runBlock_reg _ _ _ (18 : Fin 32) s93.zero (by decide), g93_18]
  have g94_19 : reg n94 (19 : Fin 32) = bp := by
    rw [rb94, runBlock_reg _ _ _ (19 : Fin 32) s93.zero (by decide), g93_19]
  have g94_20 : reg n94 (20 : Fin 32) = dg := by
    rw [rb94, runBlock_reg _ _ _ (20 : Fin 32) s93.zero (by decide), g93_20]
  have g94_21 : reg n94 (21 : Fin 32) = rootp := by
    rw [rb94, runBlock_reg _ _ _ (21 : Fin 32) s93.zero (by decide), g93_21]
  have g94_22 : reg n94 (22 : Fin 32) = ll := by
    rw [rb94, runBlock_reg _ _ _ (22 : Fin 32) s93.zero (by decide), g93_22]
  have g94_23 : reg n94 (23 : Fin 32) = sgp := by
    rw [rb94, runBlock_reg _ _ _ (23 : Fin 32) s93.zero (by decide), g93_23]
  have g94_24 : reg n94 (24 : Fin 32) = kp := by
    rw [rb94, runBlock_reg _ _ _ (24 : Fin 32) s93.zero (by decide), g93_24]
  have g94_25 : reg n94 (25 : Fin 32) = sgl := by
    rw [rb94, runBlock_reg _ _ _ (25 : Fin 32) s93.zero (by decide), g93_25]
  have g94_26 : reg n94 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by
    rw [rb94, runBlock_reg _ _ _ (26 : Fin 32) s93.zero (by decide), g93_26]
  have g94_27 : reg n94 (27 : Fin 32) = tbl := by
    rw [rb94, runBlock_reg _ _ _ (27 : Fin 32) s93.zero (by decide), g93_27]
  have g94_10 : reg n94 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb94]; simp +decide only [runBlock, BInstr.run, svDp4730, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g93_2, g93_3, g93_4, g93_8, g93_9, g93_10, g93_11, g93_12, g93_18, g93_19, g93_20, g93_21, g93_22, g93_23, g93_24, g93_25, g93_26, g93_27, s93.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g94_11 : reg n94 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb94]; simp +decide only [runBlock, BInstr.run, svDp4730, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g93_2, g93_3, g93_4, g93_8, g93_9, g93_10, g93_11, g93_12, g93_18, g93_19, g93_20, g93_21, g93_22, g93_23, g93_24, g93_25, g93_26, g93_27, s93.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk94 : SvKeepL B n0.mem n94.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4)] := by rw [m94]; exact keep_kk93
  clear keep_kk93
  have w94_2c : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m94]; exact w93_2c
  have w94_30 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m94]; exact w93_30
  have w94_34 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m94]; exact w93_34
  have w94_38 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m94]; exact w93_38
  have w94_44 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m94]; exact w93_44
  have w94_48 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m94]; exact w93_48
  have w94_4c : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m94]; exact w93_4c
  have w94_50 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m94]; exact w93_50
  have w94_54 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m94]; exact w93_54
  have w94_58 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m94]; exact w93_58
  have w94_5c : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m94]; exact w93_5c
  have w94_60 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m94]; exact w93_60
  have w94_64 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m94]; exact w93_64
  have w94_68 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m94]; exact w93_68
  have w94_6c : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m94]; exact w93_6c
  have w94_70 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m94]; exact w93_70
  have w94_74 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m94]; exact w93_74
  have w94_78 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m94]; exact w93_78
  have w94_7c : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m94]; exact w93_7c
  have w94_80 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m94]; exact w93_80
  have w94_84 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m94]; exact w93_84
  have w94_88 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m94]; exact w93_88
  have w94_8c : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m94]; exact w93_8c
  have w94_90 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m94]; exact w93_90
  have w94_94 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m94]; exact w93_94
  have w94_98 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m94]; exact w93_98
  have w94_9c : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m94]; exact w93_9c
  have w94_a0 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m94]; exact w93_a0
  have w94_a4 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m94]; exact w93_a4
  have w94_150 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m94]; exact w93_150
  have w94_154 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m94]; exact w93_154
  have w94_158 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m94]; exact w93_158
  have w94_15c : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m94]; exact w93_15c
  have w94_380 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m94]; exact w93_380
  have w94_384 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m94]; exact w93_384
  have w94_388 : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = vp := by rw [m94]; exact w93_388
  have w94_38c : memLoad32 n94.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = vl := by rw [m94]; exact w93_38c
  clear w93_38c w93_388 w93_384 w93_380 w93_15c w93_158 w93_154 w93_150 w93_a4 w93_a0 w93_9c w93_98 w93_94 w93_90 w93_8c w93_88 w93_84 w93_80 w93_7c w93_78 w93_74 w93_70 w93_6c w93_68 w93_64 w93_60 w93_5c w93_58 w93_54 w93_50 w93_4c w93_48 w93_44 w93_38 w93_34 w93_30 w93_2c g93_27 g93_26 g93_25 g93_24 g93_23 g93_22 g93_21 g93_20 g93_19 g93_18 g93_12 g93_11 g93_10 g93_9 g93_8 g93_4 g93_3 g93_2 V93 E93 fR93 t93 rg93 W93 K93 fr93 s93 d93
  -- 0x736: sv_tlvF
  obtain ⟨n95, c95, s95, rk95, K95, Ok95, Er95, fr95⟩ := sv_tlvF (oc := 0x420) (dc := 0x380)
    F E94 s94 sv_at_736 sv_at_73a (by decide) (by decide) g94_10
    g94_11 (by decide) (by decide) (by decide) (by decide) (by decide)
    w94_388 w94_38c
  have t95 : Steps n0 n95 := t94.trans c95
  have fR95 : ∀ x, SvR B x → n95.mem x = M0 x := fun x hx => (fr95 x hx).trans (fR94 x hx)
  have E95 : SvCode n95.mem := E94.fr F fr95
  have V95 : SvSaves B n95.mem v := V94.keepL K95 (by decide)
  rw [sv_mb fR94 val_in] at Ok95 Er95
  have g95_2 : reg n95 sp = B + 0x21A0 := by rw [rk95 sp (by decide) (by decide), g94_2]
  have g95_3 : reg n95 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk95 (3 : Fin 32) (by decide) (by decide), g94_3]
  have g95_4 : reg n95 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk95 (4 : Fin 32) (by decide) (by decide), g94_4]
  have g95_8 : reg n95 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk95 (8 : Fin 32) (by decide) (by decide), g94_8]
  have g95_9 : reg n95 (9 : Fin 32) = tbp := by rw [rk95 (9 : Fin 32) (by decide) (by decide), g94_9]
  have g95_10 : reg n95 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [rk95 a0 (by decide) (by decide), g94_10]
  have g95_18 : reg n95 (18 : Fin 32) = out := by rw [rk95 (18 : Fin 32) (by decide) (by decide), g94_18]
  have g95_19 : reg n95 (19 : Fin 32) = bp := by rw [rk95 (19 : Fin 32) (by decide) (by decide), g94_19]
  have g95_20 : reg n95 (20 : Fin 32) = dg := by rw [rk95 (20 : Fin 32) (by decide) (by decide), g94_20]
  have g95_21 : reg n95 (21 : Fin 32) = rootp := by rw [rk95 (21 : Fin 32) (by decide) (by decide), g94_21]
  have g95_22 : reg n95 (22 : Fin 32) = ll := by rw [rk95 (22 : Fin 32) (by decide) (by decide), g94_22]
  have g95_23 : reg n95 (23 : Fin 32) = sgp := by rw [rk95 (23 : Fin 32) (by decide) (by decide), g94_23]
  have g95_24 : reg n95 (24 : Fin 32) = kp := by rw [rk95 (24 : Fin 32) (by decide) (by decide), g94_24]
  have g95_25 : reg n95 (25 : Fin 32) = sgl := by rw [rk95 (25 : Fin 32) (by decide) (by decide), g94_25]
  have g95_26 : reg n95 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [rk95 (26 : Fin 32) (by decide) (by decide), g94_26]
  have g95_27 : reg n95 (27 : Fin 32) = tbl := by rw [rk95 (27 : Fin 32) (by decide) (by decide), g94_27]
  obtain ⟨r95, hr95⟩ : ∃ r, derTlv (memBytes M0 (vp) (vl).toNat) = r := ⟨_, rfl⟩
  rcases r95 with er95 | tl95
  · obtain ⟨zhr95, ezhr95⟩ := Er95 er95 hr95
    have keep_kk95 : SvKeepL B n0.mem n95.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := keep_kk94.trans K95
    clear keep_kk94
    have w95_2c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K95.w32 (by decide) (by decide)).trans w94_2c
    have w95_30 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K95.w32 (by decide) (by decide)).trans w94_30
    have w95_34 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K95.w32 (by decide) (by decide)).trans w94_34
    have w95_38 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K95.w32 (by decide) (by decide)).trans w94_38
    have w95_44 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K95.w32 (by decide) (by decide)).trans w94_44
    have w95_48 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K95.w32 (by decide) (by decide)).trans w94_48
    have w95_4c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K95.w32 (by decide) (by decide)).trans w94_4c
    have w95_50 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K95.w32 (by decide) (by decide)).trans w94_50
    have w95_54 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K95.w32 (by decide) (by decide)).trans w94_54
    have w95_58 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K95.w32 (by decide) (by decide)).trans w94_58
    have w95_5c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K95.w32 (by decide) (by decide)).trans w94_5c
    have w95_60 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K95.w32 (by decide) (by decide)).trans w94_60
    have w95_64 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K95.w32 (by decide) (by decide)).trans w94_64
    have w95_68 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K95.w32 (by decide) (by decide)).trans w94_68
    have w95_6c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K95.w32 (by decide) (by decide)).trans w94_6c
    have w95_70 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K95.w32 (by decide) (by decide)).trans w94_70
    have w95_74 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K95.w32 (by decide) (by decide)).trans w94_74
    have w95_78 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K95.w32 (by decide) (by decide)).trans w94_78
    have w95_7c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K95.w32 (by decide) (by decide)).trans w94_7c
    have w95_80 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K95.w32 (by decide) (by decide)).trans w94_80
    have w95_84 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K95.w32 (by decide) (by decide)).trans w94_84
    have w95_88 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K95.w32 (by decide) (by decide)).trans w94_88
    have w95_8c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K95.w32 (by decide) (by decide)).trans w94_8c
    have w95_90 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K95.w32 (by decide) (by decide)).trans w94_90
    have w95_94 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K95.w32 (by decide) (by decide)).trans w94_94
    have w95_98 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K95.w32 (by decide) (by decide)).trans w94_98
    have w95_9c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K95.w32 (by decide) (by decide)).trans w94_9c
    have w95_a0 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K95.w32 (by decide) (by decide)).trans w94_a0
    have w95_a4 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K95.w32 (by decide) (by decide)).trans w94_a4
    have w95_150 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K95.w32 (by decide) (by decide)).trans w94_150
    have w95_154 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K95.w32 (by decide) (by decide)).trans w94_154
    have w95_158 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K95.w32 (by decide) (by decide)).trans w94_158
    have w95_15c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K95.w32 (by decide) (by decide)).trans w94_15c
    have w95_380 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K95.w32 (by decide) (by decide)).trans w94_380
    have w95_384 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K95.w32 (by decide) (by decide)).trans w94_384
    have w95_420 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := zhr95
    have b95_424 : n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er95 := ezhr95
    clear w94_38c w94_388 w94_384 w94_380 w94_15c w94_158 w94_154 w94_150 w94_a4 w94_a0 w94_9c w94_98 w94_94 w94_90 w94_8c w94_88 w94_84 w94_80 w94_7c w94_78 w94_74 w94_70 w94_6c w94_68 w94_64 w94_60 w94_5c w94_58 w94_54 w94_50 w94_4c w94_48 w94_44 w94_38 w94_34 w94_30 w94_2c g94_11 g94_10 g94_27 g94_26 g94_25 g94_24 g94_23 g94_22 g94_21 g94_20 g94_19 g94_18 g94_12 g94_9 g94_8 g94_4 g94_3 g94_2 V94 E94 fR94 t94 fr94 rb94 s94 m94 u94 c94
    -- 0x73E: lw
    obtain ⟨n96, d96, u96⟩ := s95.lw E95.self sv_at_73e (off' := 0x742) (by decide)
      (by rw [g95_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s96 : St n96.mem SV n96 0x742 (reg n96) := ⟨u96.pc, rfl, fun _ => rfl⟩
    have m96 : n96.mem = n95.mem := u96.mem
    have fr96 : ∀ x, SvR B x → n96.mem x = n95.mem x := fun x _ => by rw [m96]
    have t96 : Steps n0 n96 := t95.trans (.single d96)
    have fR96 : ∀ x, SvR B x → n96.mem x = M0 x := fun x hx => (fr96 x hx).trans (fR95 x hx)
    have E96 : SvCode n96.mem := E95.fr F fr96
    have V96 : SvSaves B n96.mem v := V95.same m96
    have g96_2 : reg n96 sp = B + 0x21A0 := by rw [u96.regs, upd_ne (by decide) (by decide), g95_2]
    have g96_3 : reg n96 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u96.regs, upd_ne (by decide) (by decide), g95_3]
    have g96_4 : reg n96 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u96.regs, upd_ne (by decide) (by decide), g95_4]
    have g96_8 : reg n96 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u96.regs, upd_ne (by decide) (by decide), g95_8]
    have g96_9 : reg n96 (9 : Fin 32) = tbp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_9]
    have g96_18 : reg n96 (18 : Fin 32) = out := by rw [u96.regs, upd_ne (by decide) (by decide), g95_18]
    have g96_19 : reg n96 (19 : Fin 32) = bp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_19]
    have g96_20 : reg n96 (20 : Fin 32) = dg := by rw [u96.regs, upd_ne (by decide) (by decide), g95_20]
    have g96_21 : reg n96 (21 : Fin 32) = rootp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_21]
    have g96_22 : reg n96 (22 : Fin 32) = ll := by rw [u96.regs, upd_ne (by decide) (by decide), g95_22]
    have g96_23 : reg n96 (23 : Fin 32) = sgp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_23]
    have g96_24 : reg n96 (24 : Fin 32) = kp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_24]
    have g96_25 : reg n96 (25 : Fin 32) = sgl := by rw [u96.regs, upd_ne (by decide) (by decide), g95_25]
    have g96_26 : reg n96 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u96.regs, upd_ne (by decide) (by decide), g95_26]
    have g96_27 : reg n96 (27 : Fin 32) = tbl := by rw [u96.regs, upd_ne (by decide) (by decide), g95_27]
    have g96_10 : reg n96 a0 = 0 := by
      rw [u96.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g95_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w95_420]
    have keep_kk96 : SvKeepL B n0.mem n96.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m96]; exact keep_kk95
    clear keep_kk95
    have w96_2c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m96]; exact w95_2c
    have w96_30 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m96]; exact w95_30
    have w96_34 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m96]; exact w95_34
    have w96_38 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m96]; exact w95_38
    have w96_44 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m96]; exact w95_44
    have w96_48 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m96]; exact w95_48
    have w96_4c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m96]; exact w95_4c
    have w96_50 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m96]; exact w95_50
    have w96_54 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m96]; exact w95_54
    have w96_58 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m96]; exact w95_58
    have w96_5c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m96]; exact w95_5c
    have w96_60 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m96]; exact w95_60
    have w96_64 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m96]; exact w95_64
    have w96_68 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m96]; exact w95_68
    have w96_6c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m96]; exact w95_6c
    have w96_70 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m96]; exact w95_70
    have w96_74 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m96]; exact w95_74
    have w96_78 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m96]; exact w95_78
    have w96_7c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m96]; exact w95_7c
    have w96_80 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m96]; exact w95_80
    have w96_84 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m96]; exact w95_84
    have w96_88 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m96]; exact w95_88
    have w96_8c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m96]; exact w95_8c
    have w96_90 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m96]; exact w95_90
    have w96_94 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m96]; exact w95_94
    have w96_98 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m96]; exact w95_98
    have w96_9c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m96]; exact w95_9c
    have w96_a0 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m96]; exact w95_a0
    have w96_a4 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m96]; exact w95_a4
    have w96_150 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m96]; exact w95_150
    have w96_154 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m96]; exact w95_154
    have w96_158 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m96]; exact w95_158
    have w96_15c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m96]; exact w95_15c
    have w96_380 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m96]; exact w95_380
    have w96_384 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m96]; exact w95_384
    have w96_420 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m96]; exact w95_420
    have b96_424 : n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er95 := by rw [m96]; exact b95_424
    clear b95_424 w95_420 w95_384 w95_380 w95_15c w95_158 w95_154 w95_150 w95_a4 w95_a0 w95_9c w95_98 w95_94 w95_90 w95_8c w95_88 w95_84 w95_80 w95_7c w95_78 w95_74 w95_70 w95_6c w95_68 w95_64 w95_60 w95_5c w95_58 w95_54 w95_50 w95_4c w95_48 w95_44 w95_38 w95_34 w95_30 w95_2c ezhr95 zhr95
    -- 0x742: branch, taken
    obtain ⟨n97, d97, u97⟩ := s96.taken E96.self 0x7F2 sv_at_742
      (by decide) (by rw [g96_10, s96.zero]; rfl)
    have s97 : St n97.mem SV n97 0x7F2 (reg n97) := ⟨u97.pc, rfl, fun _ => rfl⟩
    have m97 : n97.mem = n96.mem := u97.mem
    have fr97 : ∀ x, SvR B x → n97.mem x = n96.mem x := fun x _ => by rw [m97]
    have t97 : Steps n0 n97 := t96.trans (.single d97)
    have fR97 : ∀ x, SvR B x → n97.mem x = M0 x := fun x hx => (fr97 x hx).trans (fR96 x hx)
    have E97 : SvCode n97.mem := E96.fr F fr97
    have V97 : SvSaves B n97.mem v := V96.same m97
    have g97_2 : reg n97 sp = B + 0x21A0 := by rw [u97.regs, g96_2]
    have g97_3 : reg n97 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u97.regs, g96_3]
    have g97_4 : reg n97 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u97.regs, g96_4]
    have g97_8 : reg n97 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u97.regs, g96_8]
    have g97_9 : reg n97 (9 : Fin 32) = tbp := by rw [u97.regs, g96_9]
    have g97_10 : reg n97 a0 = 0 := by rw [u97.regs, g96_10]
    have g97_18 : reg n97 (18 : Fin 32) = out := by rw [u97.regs, g96_18]
    have g97_19 : reg n97 (19 : Fin 32) = bp := by rw [u97.regs, g96_19]
    have g97_20 : reg n97 (20 : Fin 32) = dg := by rw [u97.regs, g96_20]
    have g97_21 : reg n97 (21 : Fin 32) = rootp := by rw [u97.regs, g96_21]
    have g97_22 : reg n97 (22 : Fin 32) = ll := by rw [u97.regs, g96_22]
    have g97_23 : reg n97 (23 : Fin 32) = sgp := by rw [u97.regs, g96_23]
    have g97_24 : reg n97 (24 : Fin 32) = kp := by rw [u97.regs, g96_24]
    have g97_25 : reg n97 (25 : Fin 32) = sgl := by rw [u97.regs, g96_25]
    have g97_26 : reg n97 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u97.regs, g96_26]
    have g97_27 : reg n97 (27 : Fin 32) = tbl := by rw [u97.regs, g96_27]
    have keep_kk97 : SvKeepL B n0.mem n97.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m97]; exact keep_kk96
    clear keep_kk96
    have w97_2c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m97]; exact w96_2c
    have w97_30 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m97]; exact w96_30
    have w97_34 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m97]; exact w96_34
    have w97_38 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m97]; exact w96_38
    have w97_44 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m97]; exact w96_44
    have w97_48 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m97]; exact w96_48
    have w97_4c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m97]; exact w96_4c
    have w97_50 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m97]; exact w96_50
    have w97_54 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m97]; exact w96_54
    have w97_58 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m97]; exact w96_58
    have w97_5c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m97]; exact w96_5c
    have w97_60 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m97]; exact w96_60
    have w97_64 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m97]; exact w96_64
    have w97_68 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m97]; exact w96_68
    have w97_6c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m97]; exact w96_6c
    have w97_70 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m97]; exact w96_70
    have w97_74 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m97]; exact w96_74
    have w97_78 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m97]; exact w96_78
    have w97_7c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m97]; exact w96_7c
    have w97_80 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m97]; exact w96_80
    have w97_84 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m97]; exact w96_84
    have w97_88 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m97]; exact w96_88
    have w97_8c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m97]; exact w96_8c
    have w97_90 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m97]; exact w96_90
    have w97_94 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m97]; exact w96_94
    have w97_98 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m97]; exact w96_98
    have w97_9c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m97]; exact w96_9c
    have w97_a0 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m97]; exact w96_a0
    have w97_a4 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m97]; exact w96_a4
    have w97_150 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m97]; exact w96_150
    have w97_154 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m97]; exact w96_154
    have w97_158 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m97]; exact w96_158
    have w97_15c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m97]; exact w96_15c
    have w97_380 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m97]; exact w96_380
    have w97_384 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m97]; exact w96_384
    have w97_420 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m97]; exact w96_420
    have b97_424 : n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er95 := by rw [m97]; exact b96_424
    clear b96_424 w96_420 w96_384 w96_380 w96_15c w96_158 w96_154 w96_150 w96_a4 w96_a0 w96_9c w96_98 w96_94 w96_90 w96_8c w96_88 w96_84 w96_80 w96_7c w96_78 w96_74 w96_70 w96_6c w96_68 w96_64 w96_60 w96_5c w96_58 w96_54 w96_50 w96_4c w96_48 w96_44 w96_38 w96_34 w96_30 w96_2c g96_10 g96_27 g96_26 g96_25 g96_24 g96_23 g96_22 g96_21 g96_20 g96_19 g96_18 g96_9 g96_8 g96_4 g96_3 g96_2 V96 E96 fR96 t96 fr96 m96 s96 u96 d96
    -- 0x7F2: lbu
    obtain ⟨n98, d98, u98⟩ := s97.lbu E97.self sv_at_7f2 (off' := 0x7F6) (by decide)
    have s98 : St n98.mem SV n98 0x7F6 (reg n98) := ⟨u98.pc, rfl, fun _ => rfl⟩
    have m98 : n98.mem = n97.mem := u98.mem
    have fr98 : ∀ x, SvR B x → n98.mem x = n97.mem x := fun x _ => by rw [m98]
    have t98 : Steps n0 n98 := t97.trans (.single d98)
    have fR98 : ∀ x, SvR B x → n98.mem x = M0 x := fun x hx => (fr98 x hx).trans (fR97 x hx)
    have E98 : SvCode n98.mem := E97.fr F fr98
    have V98 : SvSaves B n98.mem v := V97.same m98
    have g98_2 : reg n98 sp = B + 0x21A0 := by rw [u98.regs, upd_ne (by decide) (by decide), g97_2]
    have g98_3 : reg n98 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u98.regs, upd_ne (by decide) (by decide), g97_3]
    have g98_4 : reg n98 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u98.regs, upd_ne (by decide) (by decide), g97_4]
    have g98_8 : reg n98 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u98.regs, upd_ne (by decide) (by decide), g97_8]
    have g98_9 : reg n98 (9 : Fin 32) = tbp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_9]
    have g98_18 : reg n98 (18 : Fin 32) = out := by rw [u98.regs, upd_ne (by decide) (by decide), g97_18]
    have g98_19 : reg n98 (19 : Fin 32) = bp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_19]
    have g98_20 : reg n98 (20 : Fin 32) = dg := by rw [u98.regs, upd_ne (by decide) (by decide), g97_20]
    have g98_21 : reg n98 (21 : Fin 32) = rootp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_21]
    have g98_22 : reg n98 (22 : Fin 32) = ll := by rw [u98.regs, upd_ne (by decide) (by decide), g97_22]
    have g98_23 : reg n98 (23 : Fin 32) = sgp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_23]
    have g98_24 : reg n98 (24 : Fin 32) = kp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_24]
    have g98_25 : reg n98 (25 : Fin 32) = sgl := by rw [u98.regs, upd_ne (by decide) (by decide), g97_25]
    have g98_26 : reg n98 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u98.regs, upd_ne (by decide) (by decide), g97_26]
    have g98_27 : reg n98 (27 : Fin 32) = tbl := by rw [u98.regs, upd_ne (by decide) (by decide), g97_27]
    have g98_10 : reg n98 a0 = (derErrByte er95).zeroExtend 32 := by
      rw [u98.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g97_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b97_424]
    have keep_kk98 : SvKeepL B n0.mem n98.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m98]; exact keep_kk97
    clear keep_kk97
    have w98_2c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m98]; exact w97_2c
    have w98_30 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m98]; exact w97_30
    have w98_34 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m98]; exact w97_34
    have w98_38 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m98]; exact w97_38
    have w98_44 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m98]; exact w97_44
    have w98_48 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m98]; exact w97_48
    have w98_4c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m98]; exact w97_4c
    have w98_50 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m98]; exact w97_50
    have w98_54 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m98]; exact w97_54
    have w98_58 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m98]; exact w97_58
    have w98_5c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m98]; exact w97_5c
    have w98_60 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m98]; exact w97_60
    have w98_64 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m98]; exact w97_64
    have w98_68 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m98]; exact w97_68
    have w98_6c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m98]; exact w97_6c
    have w98_70 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m98]; exact w97_70
    have w98_74 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m98]; exact w97_74
    have w98_78 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m98]; exact w97_78
    have w98_7c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m98]; exact w97_7c
    have w98_80 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m98]; exact w97_80
    have w98_84 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m98]; exact w97_84
    have w98_88 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m98]; exact w97_88
    have w98_8c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m98]; exact w97_8c
    have w98_90 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m98]; exact w97_90
    have w98_94 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m98]; exact w97_94
    have w98_98 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m98]; exact w97_98
    have w98_9c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m98]; exact w97_9c
    have w98_a0 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m98]; exact w97_a0
    have w98_a4 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m98]; exact w97_a4
    have w98_150 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m98]; exact w97_150
    have w98_154 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m98]; exact w97_154
    have w98_158 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m98]; exact w97_158
    have w98_15c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m98]; exact w97_15c
    have w98_380 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m98]; exact w97_380
    have w98_384 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m98]; exact w97_384
    have w98_420 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m98]; exact w97_420
    have b98_424 : n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er95 := by rw [m98]; exact b97_424
    clear b97_424 w97_420 w97_384 w97_380 w97_15c w97_158 w97_154 w97_150 w97_a4 w97_a0 w97_9c w97_98 w97_94 w97_90 w97_8c w97_88 w97_84 w97_80 w97_7c w97_78 w97_74 w97_70 w97_6c w97_68 w97_64 w97_60 w97_5c w97_58 w97_54 w97_50 w97_4c w97_48 w97_44 w97_38 w97_34 w97_30 w97_2c g97_27 g97_26 g97_25 g97_24 g97_23 g97_22 g97_21 g97_20 g97_19 g97_18 g97_10 g97_9 g97_8 g97_4 g97_3 g97_2 V97 E97 fR97 t97 fr97 m97 s97 u97 d97
    -- 0x7F6: j
    obtain ⟨n99, d99, u99⟩ := s98.jump E98.self sv_at_7f6 (off' := 0x942) (by decide)
      (by rw [s98.pc]; decide)
    have s99 : St n99.mem SV n99 0x942 (reg n99) := ⟨u99.pc, rfl, fun _ => rfl⟩
    have m99 : n99.mem = n98.mem := u99.mem
    have fr99 : ∀ x, SvR B x → n99.mem x = n98.mem x := fun x _ => by rw [m99]
    have t99 : Steps n0 n99 := t98.trans (.single d99)
    have fR99 : ∀ x, SvR B x → n99.mem x = M0 x := fun x hx => (fr99 x hx).trans (fR98 x hx)
    have E99 : SvCode n99.mem := E98.fr F fr99
    have V99 : SvSaves B n99.mem v := V98.same m99
    have g99_2 : reg n99 sp = B + 0x21A0 := by rw [u99.regs, g98_2]
    have g99_3 : reg n99 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u99.regs, g98_3]
    have g99_4 : reg n99 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u99.regs, g98_4]
    have g99_8 : reg n99 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u99.regs, g98_8]
    have g99_9 : reg n99 (9 : Fin 32) = tbp := by rw [u99.regs, g98_9]
    have g99_10 : reg n99 a0 = (derErrByte er95).zeroExtend 32 := by rw [u99.regs, g98_10]
    have g99_18 : reg n99 (18 : Fin 32) = out := by rw [u99.regs, g98_18]
    have g99_19 : reg n99 (19 : Fin 32) = bp := by rw [u99.regs, g98_19]
    have g99_20 : reg n99 (20 : Fin 32) = dg := by rw [u99.regs, g98_20]
    have g99_21 : reg n99 (21 : Fin 32) = rootp := by rw [u99.regs, g98_21]
    have g99_22 : reg n99 (22 : Fin 32) = ll := by rw [u99.regs, g98_22]
    have g99_23 : reg n99 (23 : Fin 32) = sgp := by rw [u99.regs, g98_23]
    have g99_24 : reg n99 (24 : Fin 32) = kp := by rw [u99.regs, g98_24]
    have g99_25 : reg n99 (25 : Fin 32) = sgl := by rw [u99.regs, g98_25]
    have g99_26 : reg n99 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u99.regs, g98_26]
    have g99_27 : reg n99 (27 : Fin 32) = tbl := by rw [u99.regs, g98_27]
    have keep_kk99 : SvKeepL B n0.mem n99.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m99]; exact keep_kk98
    clear keep_kk98
    have w99_2c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m99]; exact w98_2c
    have w99_30 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m99]; exact w98_30
    have w99_34 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m99]; exact w98_34
    have w99_38 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m99]; exact w98_38
    have w99_44 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m99]; exact w98_44
    have w99_48 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m99]; exact w98_48
    have w99_4c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m99]; exact w98_4c
    have w99_50 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m99]; exact w98_50
    have w99_54 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m99]; exact w98_54
    have w99_58 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m99]; exact w98_58
    have w99_5c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m99]; exact w98_5c
    have w99_60 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m99]; exact w98_60
    have w99_64 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m99]; exact w98_64
    have w99_68 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m99]; exact w98_68
    have w99_6c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m99]; exact w98_6c
    have w99_70 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m99]; exact w98_70
    have w99_74 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m99]; exact w98_74
    have w99_78 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m99]; exact w98_78
    have w99_7c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m99]; exact w98_7c
    have w99_80 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m99]; exact w98_80
    have w99_84 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m99]; exact w98_84
    have w99_88 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m99]; exact w98_88
    have w99_8c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m99]; exact w98_8c
    have w99_90 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m99]; exact w98_90
    have w99_94 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m99]; exact w98_94
    have w99_98 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m99]; exact w98_98
    have w99_9c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m99]; exact w98_9c
    have w99_a0 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m99]; exact w98_a0
    have w99_a4 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m99]; exact w98_a4
    have w99_150 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m99]; exact w98_150
    have w99_154 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m99]; exact w98_154
    have w99_158 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m99]; exact w98_158
    have w99_15c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m99]; exact w98_15c
    have w99_380 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m99]; exact w98_380
    have w99_384 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m99]; exact w98_384
    have w99_420 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m99]; exact w98_420
    have b99_424 : n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er95 := by rw [m99]; exact b98_424
    clear b98_424 w98_420 w98_384 w98_380 w98_15c w98_158 w98_154 w98_150 w98_a4 w98_a0 w98_9c w98_98 w98_94 w98_90 w98_8c w98_88 w98_84 w98_80 w98_7c w98_78 w98_74 w98_70 w98_6c w98_68 w98_64 w98_60 w98_5c w98_58 w98_54 w98_50 w98_4c w98_48 w98_44 w98_38 w98_34 w98_30 w98_2c g98_10 g98_27 g98_26 g98_25 g98_24 g98_23 g98_22 g98_21 g98_20 g98_19 g98_18 g98_9 g98_8 g98_4 g98_3 g98_2 V98 E98 fR98 t98 fr98 m98 s98 u98 d98
    -- 0x942: sw
    obtain ⟨n100, d100, s100, fr100, K100, W100, rg100⟩ := sv_sw F E99 s99 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g99_2]; sv_addr) (by decide) (by decide)
    have t100 : Steps n0 n100 := t99.trans d100
    have fR100 : ∀ x, SvR B x → n100.mem x = M0 x := fun x hx => (fr100 x hx).trans (fR99 x hx)
    have E100 : SvCode n100.mem := E99.fr F fr100
    have V100 : SvSaves B n100.mem v := V99.keep K100 (by decide)
    have g100_2 : reg n100 sp = B + 0x21A0 := by rw [rg100 sp, g99_2]
    have g100_3 : reg n100 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg100 (3 : Fin 32), g99_3]
    have g100_4 : reg n100 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg100 (4 : Fin 32), g99_4]
    have g100_8 : reg n100 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg100 (8 : Fin 32), g99_8]
    have g100_9 : reg n100 (9 : Fin 32) = tbp := by rw [rg100 (9 : Fin 32), g99_9]
    have g100_10 : reg n100 a0 = (derErrByte er95).zeroExtend 32 := by rw [rg100 a0, g99_10]
    have g100_18 : reg n100 (18 : Fin 32) = out := by rw [rg100 (18 : Fin 32), g99_18]
    have g100_19 : reg n100 (19 : Fin 32) = bp := by rw [rg100 (19 : Fin 32), g99_19]
    have g100_20 : reg n100 (20 : Fin 32) = dg := by rw [rg100 (20 : Fin 32), g99_20]
    have g100_21 : reg n100 (21 : Fin 32) = rootp := by rw [rg100 (21 : Fin 32), g99_21]
    have g100_22 : reg n100 (22 : Fin 32) = ll := by rw [rg100 (22 : Fin 32), g99_22]
    have g100_23 : reg n100 (23 : Fin 32) = sgp := by rw [rg100 (23 : Fin 32), g99_23]
    have g100_24 : reg n100 (24 : Fin 32) = kp := by rw [rg100 (24 : Fin 32), g99_24]
    have g100_25 : reg n100 (25 : Fin 32) = sgl := by rw [rg100 (25 : Fin 32), g99_25]
    have g100_26 : reg n100 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [rg100 (26 : Fin 32), g99_26]
    have g100_27 : reg n100 (27 : Fin 32) = tbl := by rw [rg100 (27 : Fin 32), g99_27]
    have keep_kk100 : SvKeepL B n0.mem n100.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := keep_kk99.trans K100.toL
    clear keep_kk99
    have w100_2c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K100.w32 (by decide) (by decide)).trans w99_2c
    have w100_30 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K100.w32 (by decide) (by decide)).trans w99_30
    have w100_34 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K100.w32 (by decide) (by decide)).trans w99_34
    have w100_38 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K100.w32 (by decide) (by decide)).trans w99_38
    have w100_48 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K100.w32 (by decide) (by decide)).trans w99_48
    have w100_4c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K100.w32 (by decide) (by decide)).trans w99_4c
    have w100_50 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K100.w32 (by decide) (by decide)).trans w99_50
    have w100_54 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K100.w32 (by decide) (by decide)).trans w99_54
    have w100_58 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K100.w32 (by decide) (by decide)).trans w99_58
    have w100_5c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K100.w32 (by decide) (by decide)).trans w99_5c
    have w100_60 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K100.w32 (by decide) (by decide)).trans w99_60
    have w100_64 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K100.w32 (by decide) (by decide)).trans w99_64
    have w100_68 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K100.w32 (by decide) (by decide)).trans w99_68
    have w100_6c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K100.w32 (by decide) (by decide)).trans w99_6c
    have w100_70 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K100.w32 (by decide) (by decide)).trans w99_70
    have w100_74 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K100.w32 (by decide) (by decide)).trans w99_74
    have w100_78 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K100.w32 (by decide) (by decide)).trans w99_78
    have w100_7c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K100.w32 (by decide) (by decide)).trans w99_7c
    have w100_80 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K100.w32 (by decide) (by decide)).trans w99_80
    have w100_84 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K100.w32 (by decide) (by decide)).trans w99_84
    have w100_88 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K100.w32 (by decide) (by decide)).trans w99_88
    have w100_8c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K100.w32 (by decide) (by decide)).trans w99_8c
    have w100_90 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K100.w32 (by decide) (by decide)).trans w99_90
    have w100_94 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K100.w32 (by decide) (by decide)).trans w99_94
    have w100_98 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K100.w32 (by decide) (by decide)).trans w99_98
    have w100_9c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K100.w32 (by decide) (by decide)).trans w99_9c
    have w100_a0 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K100.w32 (by decide) (by decide)).trans w99_a0
    have w100_a4 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K100.w32 (by decide) (by decide)).trans w99_a4
    have w100_150 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K100.w32 (by decide) (by decide)).trans w99_150
    have w100_154 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K100.w32 (by decide) (by decide)).trans w99_154
    have w100_158 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K100.w32 (by decide) (by decide)).trans w99_158
    have w100_15c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K100.w32 (by decide) (by decide)).trans w99_15c
    have w100_380 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K100.w32 (by decide) (by decide)).trans w99_380
    have w100_384 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K100.w32 (by decide) (by decide)).trans w99_384
    have w100_420 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K100.w32 (by decide) (by decide)).trans w99_420
    have b100_424 : n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er95 := (K100.b8 (by decide) (by decide)).trans b99_424
    have w100_44 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er95).zeroExtend 32 := by rw [W100, g99_10]
    clear b99_424 w99_420 w99_384 w99_380 w99_15c w99_158 w99_154 w99_150 w99_a4 w99_a0 w99_9c w99_98 w99_94 w99_90 w99_8c w99_88 w99_84 w99_80 w99_7c w99_78 w99_74 w99_70 w99_6c w99_68 w99_64 w99_60 w99_5c w99_58 w99_54 w99_50 w99_4c w99_48 w99_44 w99_38 w99_34 w99_30 w99_2c g99_27 g99_26 g99_25 g99_24 g99_23 g99_22 g99_21 g99_20 g99_19 g99_18 g99_10 g99_9 g99_8 g99_4 g99_3 g99_2 V99 E99 fR99 t99 fr99 m99 s99 u99 d99
    -- 0x944: lw
    obtain ⟨n101, d101, u101⟩ := s100.lw E100.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g100_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s101 : St n101.mem SV n101 0x946 (reg n101) := ⟨u101.pc, rfl, fun _ => rfl⟩
    have m101 : n101.mem = n100.mem := u101.mem
    have fr101 : ∀ x, SvR B x → n101.mem x = n100.mem x := fun x _ => by rw [m101]
    have t101 : Steps n0 n101 := t100.trans (.single d101)
    have fR101 : ∀ x, SvR B x → n101.mem x = M0 x := fun x hx => (fr101 x hx).trans (fR100 x hx)
    have E101 : SvCode n101.mem := E100.fr F fr101
    have V101 : SvSaves B n101.mem v := V100.same m101
    have g101_2 : reg n101 sp = B + 0x21A0 := by rw [u101.regs, upd_ne (by decide) (by decide), g100_2]
    have g101_3 : reg n101 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u101.regs, upd_ne (by decide) (by decide), g100_3]
    have g101_4 : reg n101 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u101.regs, upd_ne (by decide) (by decide), g100_4]
    have g101_9 : reg n101 (9 : Fin 32) = tbp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_9]
    have g101_10 : reg n101 a0 = (derErrByte er95).zeroExtend 32 := by rw [u101.regs, upd_ne (by decide) (by decide), g100_10]
    have g101_18 : reg n101 (18 : Fin 32) = out := by rw [u101.regs, upd_ne (by decide) (by decide), g100_18]
    have g101_19 : reg n101 (19 : Fin 32) = bp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_19]
    have g101_20 : reg n101 (20 : Fin 32) = dg := by rw [u101.regs, upd_ne (by decide) (by decide), g100_20]
    have g101_21 : reg n101 (21 : Fin 32) = rootp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_21]
    have g101_22 : reg n101 (22 : Fin 32) = ll := by rw [u101.regs, upd_ne (by decide) (by decide), g100_22]
    have g101_23 : reg n101 (23 : Fin 32) = sgp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_23]
    have g101_24 : reg n101 (24 : Fin 32) = kp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_24]
    have g101_25 : reg n101 (25 : Fin 32) = sgl := by rw [u101.regs, upd_ne (by decide) (by decide), g100_25]
    have g101_26 : reg n101 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u101.regs, upd_ne (by decide) (by decide), g100_26]
    have g101_27 : reg n101 (27 : Fin 32) = tbl := by rw [u101.regs, upd_ne (by decide) (by decide), g100_27]
    have g101_8 : reg n101 (8 : Fin 32) = (derErrByte er95).zeroExtend 32 := by
      rw [u101.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g100_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w100_44]
    have keep_kk101 : SvKeepL B n0.mem n101.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m101]; exact keep_kk100
    clear keep_kk100
    have w101_2c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m101]; exact w100_2c
    have w101_30 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m101]; exact w100_30
    have w101_34 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m101]; exact w100_34
    have w101_38 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m101]; exact w100_38
    have w101_44 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er95).zeroExtend 32 := by rw [m101]; exact w100_44
    have w101_48 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m101]; exact w100_48
    have w101_4c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m101]; exact w100_4c
    have w101_50 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m101]; exact w100_50
    have w101_54 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m101]; exact w100_54
    have w101_58 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m101]; exact w100_58
    have w101_5c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m101]; exact w100_5c
    have w101_60 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m101]; exact w100_60
    have w101_64 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m101]; exact w100_64
    have w101_68 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m101]; exact w100_68
    have w101_6c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m101]; exact w100_6c
    have w101_70 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m101]; exact w100_70
    have w101_74 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m101]; exact w100_74
    have w101_78 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m101]; exact w100_78
    have w101_7c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m101]; exact w100_7c
    have w101_80 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m101]; exact w100_80
    have w101_84 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m101]; exact w100_84
    have w101_88 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m101]; exact w100_88
    have w101_8c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m101]; exact w100_8c
    have w101_90 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m101]; exact w100_90
    have w101_94 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m101]; exact w100_94
    have w101_98 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m101]; exact w100_98
    have w101_9c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m101]; exact w100_9c
    have w101_a0 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m101]; exact w100_a0
    have w101_a4 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m101]; exact w100_a4
    have w101_150 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m101]; exact w100_150
    have w101_154 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m101]; exact w100_154
    have w101_158 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m101]; exact w100_158
    have w101_15c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m101]; exact w100_15c
    have w101_380 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m101]; exact w100_380
    have w101_384 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m101]; exact w100_384
    have w101_420 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m101]; exact w100_420
    have b101_424 : n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er95 := by rw [m101]; exact b100_424
    clear w100_44 b100_424 w100_420 w100_384 w100_380 w100_15c w100_158 w100_154 w100_150 w100_a4 w100_a0 w100_9c w100_98 w100_94 w100_90 w100_8c w100_88 w100_84 w100_80 w100_7c w100_78 w100_74 w100_70 w100_6c w100_68 w100_64 w100_60 w100_5c w100_58 w100_54 w100_50 w100_4c w100_48 w100_38 w100_34 w100_30 w100_2c g100_27 g100_26 g100_25 g100_24 g100_23 g100_22 g100_21 g100_20 g100_19 g100_18 g100_10 g100_9 g100_8 g100_4 g100_3 g100_2 V100 E100 fR100 t100 rg100 W100 K100 fr100 s100 d100
    -- 0x946: j
    obtain ⟨n102, d102, u102⟩ := s101.jump E101.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s101.pc]; decide)
    have s102 : St n102.mem SV n102 0x7A4 (reg n102) := ⟨u102.pc, rfl, fun _ => rfl⟩
    have m102 : n102.mem = n101.mem := u102.mem
    have fr102 : ∀ x, SvR B x → n102.mem x = n101.mem x := fun x _ => by rw [m102]
    have t102 : Steps n0 n102 := t101.trans (.single d102)
    have fR102 : ∀ x, SvR B x → n102.mem x = M0 x := fun x hx => (fr102 x hx).trans (fR101 x hx)
    have E102 : SvCode n102.mem := E101.fr F fr102
    have V102 : SvSaves B n102.mem v := V101.same m102
    have g102_2 : reg n102 sp = B + 0x21A0 := by rw [u102.regs, g101_2]
    have g102_3 : reg n102 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u102.regs, g101_3]
    have g102_4 : reg n102 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u102.regs, g101_4]
    have g102_8 : reg n102 (8 : Fin 32) = (derErrByte er95).zeroExtend 32 := by rw [u102.regs, g101_8]
    have g102_9 : reg n102 (9 : Fin 32) = tbp := by rw [u102.regs, g101_9]
    have g102_10 : reg n102 a0 = (derErrByte er95).zeroExtend 32 := by rw [u102.regs, g101_10]
    have g102_18 : reg n102 (18 : Fin 32) = out := by rw [u102.regs, g101_18]
    have g102_19 : reg n102 (19 : Fin 32) = bp := by rw [u102.regs, g101_19]
    have g102_20 : reg n102 (20 : Fin 32) = dg := by rw [u102.regs, g101_20]
    have g102_21 : reg n102 (21 : Fin 32) = rootp := by rw [u102.regs, g101_21]
    have g102_22 : reg n102 (22 : Fin 32) = ll := by rw [u102.regs, g101_22]
    have g102_23 : reg n102 (23 : Fin 32) = sgp := by rw [u102.regs, g101_23]
    have g102_24 : reg n102 (24 : Fin 32) = kp := by rw [u102.regs, g101_24]
    have g102_25 : reg n102 (25 : Fin 32) = sgl := by rw [u102.regs, g101_25]
    have g102_26 : reg n102 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u102.regs, g101_26]
    have g102_27 : reg n102 (27 : Fin 32) = tbl := by rw [u102.regs, g101_27]
    have keep_kk102 : SvKeepL B n0.mem n102.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m102]; exact keep_kk101
    clear keep_kk101
    have w102_2c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m102]; exact w101_2c
    have w102_30 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m102]; exact w101_30
    have w102_34 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m102]; exact w101_34
    have w102_38 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m102]; exact w101_38
    have w102_44 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (derErrByte er95).zeroExtend 32 := by rw [m102]; exact w101_44
    have w102_48 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m102]; exact w101_48
    have w102_4c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m102]; exact w101_4c
    have w102_50 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m102]; exact w101_50
    have w102_54 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m102]; exact w101_54
    have w102_58 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m102]; exact w101_58
    have w102_5c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m102]; exact w101_5c
    have w102_60 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m102]; exact w101_60
    have w102_64 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m102]; exact w101_64
    have w102_68 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m102]; exact w101_68
    have w102_6c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m102]; exact w101_6c
    have w102_70 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m102]; exact w101_70
    have w102_74 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m102]; exact w101_74
    have w102_78 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m102]; exact w101_78
    have w102_7c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m102]; exact w101_7c
    have w102_80 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m102]; exact w101_80
    have w102_84 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m102]; exact w101_84
    have w102_88 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m102]; exact w101_88
    have w102_8c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m102]; exact w101_8c
    have w102_90 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m102]; exact w101_90
    have w102_94 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m102]; exact w101_94
    have w102_98 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m102]; exact w101_98
    have w102_9c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m102]; exact w101_9c
    have w102_a0 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m102]; exact w101_a0
    have w102_a4 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m102]; exact w101_a4
    have w102_150 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m102]; exact w101_150
    have w102_154 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m102]; exact w101_154
    have w102_158 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m102]; exact w101_158
    have w102_15c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m102]; exact w101_15c
    have w102_380 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m102]; exact w101_380
    have w102_384 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m102]; exact w101_384
    have w102_420 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m102]; exact w101_420
    have b102_424 : n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er95 := by rw [m102]; exact b101_424
    clear b101_424 w101_420 w101_384 w101_380 w101_15c w101_158 w101_154 w101_150 w101_a4 w101_a0 w101_9c w101_98 w101_94 w101_90 w101_8c w101_88 w101_84 w101_80 w101_7c w101_78 w101_74 w101_70 w101_6c w101_68 w101_64 w101_60 w101_5c w101_58 w101_54 w101_50 w101_4c w101_48 w101_44 w101_38 w101_34 w101_30 w101_2c g101_8 g101_27 g101_26 g101_25 g101_24 g101_23 g101_22 g101_21 g101_20 g101_19 g101_18 g101_10 g101_9 g101_4 g101_3 g101_2 V101 E101 fR101 t101 fr101 m101 s101 u101 d101
    exact .inl ⟨(fun ⟨tl95', h0', _⟩ => by rw [hr95] at h0'; cases h0'), sv_fail F E102 s102 t102 (fun x hx => (fR102 x hx).trans (fM x hx).symm) V102 hret g102_2 g102_18 hO g102_3 g102_4 (by rw [g102_8]; sv_code)⟩
  obtain ⟨o0_95, o4_95, o8_95, o12_95, o16_95, d8_95, d12_95⟩ := Ok95 tl95 hr95
  have keep_kk95 : SvKeepL B n0.mem n95.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := keep_kk94.trans K95
  clear keep_kk94
  have w95_2c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K95.w32 (by decide) (by decide)).trans w94_2c
  have w95_30 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K95.w32 (by decide) (by decide)).trans w94_30
  have w95_34 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K95.w32 (by decide) (by decide)).trans w94_34
  have w95_38 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K95.w32 (by decide) (by decide)).trans w94_38
  have w95_44 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K95.w32 (by decide) (by decide)).trans w94_44
  have w95_48 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K95.w32 (by decide) (by decide)).trans w94_48
  have w95_4c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K95.w32 (by decide) (by decide)).trans w94_4c
  have w95_50 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K95.w32 (by decide) (by decide)).trans w94_50
  have w95_54 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K95.w32 (by decide) (by decide)).trans w94_54
  have w95_58 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K95.w32 (by decide) (by decide)).trans w94_58
  have w95_5c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K95.w32 (by decide) (by decide)).trans w94_5c
  have w95_60 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K95.w32 (by decide) (by decide)).trans w94_60
  have w95_64 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K95.w32 (by decide) (by decide)).trans w94_64
  have w95_68 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K95.w32 (by decide) (by decide)).trans w94_68
  have w95_6c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K95.w32 (by decide) (by decide)).trans w94_6c
  have w95_70 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K95.w32 (by decide) (by decide)).trans w94_70
  have w95_74 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K95.w32 (by decide) (by decide)).trans w94_74
  have w95_78 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K95.w32 (by decide) (by decide)).trans w94_78
  have w95_7c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K95.w32 (by decide) (by decide)).trans w94_7c
  have w95_80 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K95.w32 (by decide) (by decide)).trans w94_80
  have w95_84 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K95.w32 (by decide) (by decide)).trans w94_84
  have w95_88 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K95.w32 (by decide) (by decide)).trans w94_88
  have w95_8c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K95.w32 (by decide) (by decide)).trans w94_8c
  have w95_90 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K95.w32 (by decide) (by decide)).trans w94_90
  have w95_94 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K95.w32 (by decide) (by decide)).trans w94_94
  have w95_98 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K95.w32 (by decide) (by decide)).trans w94_98
  have w95_9c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K95.w32 (by decide) (by decide)).trans w94_9c
  have w95_a0 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K95.w32 (by decide) (by decide)).trans w94_a0
  have w95_a4 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K95.w32 (by decide) (by decide)).trans w94_a4
  have w95_150 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K95.w32 (by decide) (by decide)).trans w94_150
  have w95_154 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K95.w32 (by decide) (by decide)).trans w94_154
  have w95_158 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K95.w32 (by decide) (by decide)).trans w94_158
  have w95_15c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K95.w32 (by decide) (by decide)).trans w94_15c
  have w95_380 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K95.w32 (by decide) (by decide)).trans w94_380
  have w95_384 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K95.w32 (by decide) (by decide)).trans w94_384
  have w95_388 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := d8_95
  have w95_38c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := d12_95
  have w95_420 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := o0_95
  have w95_424 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := o4_95
  have w95_428 : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := o8_95
  have w95_42c : memLoad32 n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := o12_95
  have b95_430 : n95.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := o16_95
  clear w94_38c w94_388 w94_384 w94_380 w94_15c w94_158 w94_154 w94_150 w94_a4 w94_a0 w94_9c w94_98 w94_94 w94_90 w94_8c w94_88 w94_84 w94_80 w94_7c w94_78 w94_74 w94_70 w94_6c w94_68 w94_64 w94_60 w94_5c w94_58 w94_54 w94_50 w94_4c w94_48 w94_44 w94_38 w94_34 w94_30 w94_2c g94_11 g94_10 g94_27 g94_26 g94_25 g94_24 g94_23 g94_22 g94_21 g94_20 g94_19 g94_18 g94_12 g94_9 g94_8 g94_4 g94_3 g94_2 V94 E94 fR94 t94 fr94 rb94 s94 m94 u94 c94
  -- 0x73E: lw
  obtain ⟨n96, d96, u96⟩ := s95.lw E95.self sv_at_73e (off' := 0x742) (by decide)
    (by rw [g95_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s96 : St n96.mem SV n96 0x742 (reg n96) := ⟨u96.pc, rfl, fun _ => rfl⟩
  have m96 : n96.mem = n95.mem := u96.mem
  have fr96 : ∀ x, SvR B x → n96.mem x = n95.mem x := fun x _ => by rw [m96]
  have t96 : Steps n0 n96 := t95.trans (.single d96)
  have fR96 : ∀ x, SvR B x → n96.mem x = M0 x := fun x hx => (fr96 x hx).trans (fR95 x hx)
  have E96 : SvCode n96.mem := E95.fr F fr96
  have V96 : SvSaves B n96.mem v := V95.same m96
  have g96_2 : reg n96 sp = B + 0x21A0 := by rw [u96.regs, upd_ne (by decide) (by decide), g95_2]
  have g96_3 : reg n96 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u96.regs, upd_ne (by decide) (by decide), g95_3]
  have g96_4 : reg n96 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u96.regs, upd_ne (by decide) (by decide), g95_4]
  have g96_8 : reg n96 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u96.regs, upd_ne (by decide) (by decide), g95_8]
  have g96_9 : reg n96 (9 : Fin 32) = tbp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_9]
  have g96_18 : reg n96 (18 : Fin 32) = out := by rw [u96.regs, upd_ne (by decide) (by decide), g95_18]
  have g96_19 : reg n96 (19 : Fin 32) = bp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_19]
  have g96_20 : reg n96 (20 : Fin 32) = dg := by rw [u96.regs, upd_ne (by decide) (by decide), g95_20]
  have g96_21 : reg n96 (21 : Fin 32) = rootp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_21]
  have g96_22 : reg n96 (22 : Fin 32) = ll := by rw [u96.regs, upd_ne (by decide) (by decide), g95_22]
  have g96_23 : reg n96 (23 : Fin 32) = sgp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_23]
  have g96_24 : reg n96 (24 : Fin 32) = kp := by rw [u96.regs, upd_ne (by decide) (by decide), g95_24]
  have g96_25 : reg n96 (25 : Fin 32) = sgl := by rw [u96.regs, upd_ne (by decide) (by decide), g95_25]
  have g96_26 : reg n96 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u96.regs, upd_ne (by decide) (by decide), g95_26]
  have g96_27 : reg n96 (27 : Fin 32) = tbl := by rw [u96.regs, upd_ne (by decide) (by decide), g95_27]
  have g96_10 : reg n96 a0 = (vp) + BitVec.ofNat 32 tl95.header := by
    rw [u96.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g95_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w95_420]
  have keep_kk96 : SvKeepL B n0.mem n96.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m96]; exact keep_kk95
  clear keep_kk95
  have w96_2c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m96]; exact w95_2c
  have w96_30 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m96]; exact w95_30
  have w96_34 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m96]; exact w95_34
  have w96_38 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m96]; exact w95_38
  have w96_44 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m96]; exact w95_44
  have w96_48 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m96]; exact w95_48
  have w96_4c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m96]; exact w95_4c
  have w96_50 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m96]; exact w95_50
  have w96_54 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m96]; exact w95_54
  have w96_58 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m96]; exact w95_58
  have w96_5c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m96]; exact w95_5c
  have w96_60 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m96]; exact w95_60
  have w96_64 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m96]; exact w95_64
  have w96_68 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m96]; exact w95_68
  have w96_6c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m96]; exact w95_6c
  have w96_70 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m96]; exact w95_70
  have w96_74 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m96]; exact w95_74
  have w96_78 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m96]; exact w95_78
  have w96_7c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m96]; exact w95_7c
  have w96_80 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m96]; exact w95_80
  have w96_84 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m96]; exact w95_84
  have w96_88 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m96]; exact w95_88
  have w96_8c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m96]; exact w95_8c
  have w96_90 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m96]; exact w95_90
  have w96_94 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m96]; exact w95_94
  have w96_98 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m96]; exact w95_98
  have w96_9c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m96]; exact w95_9c
  have w96_a0 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m96]; exact w95_a0
  have w96_a4 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m96]; exact w95_a4
  have w96_150 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m96]; exact w95_150
  have w96_154 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m96]; exact w95_154
  have w96_158 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m96]; exact w95_158
  have w96_15c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m96]; exact w95_15c
  have w96_380 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m96]; exact w95_380
  have w96_384 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m96]; exact w95_384
  have w96_388 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m96]; exact w95_388
  have w96_38c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m96]; exact w95_38c
  have w96_420 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m96]; exact w95_420
  have w96_424 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m96]; exact w95_424
  have w96_428 : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m96]; exact w95_428
  have w96_42c : memLoad32 n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m96]; exact w95_42c
  have b96_430 : n96.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m96]; exact b95_430
  clear b95_430 w95_42c w95_428 w95_424 w95_420 w95_38c w95_388 w95_384 w95_380 w95_15c w95_158 w95_154 w95_150 w95_a4 w95_a0 w95_9c w95_98 w95_94 w95_90 w95_8c w95_88 w95_84 w95_80 w95_7c w95_78 w95_74 w95_70 w95_6c w95_68 w95_64 w95_60 w95_5c w95_58 w95_54 w95_50 w95_4c w95_48 w95_44 w95_38 w95_34 w95_30 w95_2c d12_95 d8_95 o16_95 o12_95 o8_95 o4_95 o0_95 g95_27 g95_26 g95_25 g95_24 g95_23 g95_22 g95_21 g95_20 g95_19 g95_18 g95_10 g95_9 g95_8 g95_4 g95_3 g95_2 V95 E95 fR95 t95 fr95 Er95 Ok95 K95 rk95 s95 c95
  -- 0x742: branch, not taken
  obtain ⟨n97, d97, u97⟩ := s96.notTaken E96.self 0x744 sv_at_742
    (by decide) (by rw [g96_10, s96.zero]; exact br_beq_f (val_in.tlv_ne hr95))
  have s97 : St n97.mem SV n97 0x744 (reg n97) := ⟨u97.pc, rfl, fun _ => rfl⟩
  have m97 : n97.mem = n96.mem := u97.mem
  have fr97 : ∀ x, SvR B x → n97.mem x = n96.mem x := fun x _ => by rw [m97]
  have t97 : Steps n0 n97 := t96.trans (.single d97)
  have fR97 : ∀ x, SvR B x → n97.mem x = M0 x := fun x hx => (fr97 x hx).trans (fR96 x hx)
  have E97 : SvCode n97.mem := E96.fr F fr97
  have V97 : SvSaves B n97.mem v := V96.same m97
  have g97_2 : reg n97 sp = B + 0x21A0 := by rw [u97.regs, g96_2]
  have g97_3 : reg n97 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u97.regs, g96_3]
  have g97_4 : reg n97 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u97.regs, g96_4]
  have g97_8 : reg n97 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u97.regs, g96_8]
  have g97_9 : reg n97 (9 : Fin 32) = tbp := by rw [u97.regs, g96_9]
  have g97_10 : reg n97 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u97.regs, g96_10]
  have g97_18 : reg n97 (18 : Fin 32) = out := by rw [u97.regs, g96_18]
  have g97_19 : reg n97 (19 : Fin 32) = bp := by rw [u97.regs, g96_19]
  have g97_20 : reg n97 (20 : Fin 32) = dg := by rw [u97.regs, g96_20]
  have g97_21 : reg n97 (21 : Fin 32) = rootp := by rw [u97.regs, g96_21]
  have g97_22 : reg n97 (22 : Fin 32) = ll := by rw [u97.regs, g96_22]
  have g97_23 : reg n97 (23 : Fin 32) = sgp := by rw [u97.regs, g96_23]
  have g97_24 : reg n97 (24 : Fin 32) = kp := by rw [u97.regs, g96_24]
  have g97_25 : reg n97 (25 : Fin 32) = sgl := by rw [u97.regs, g96_25]
  have g97_26 : reg n97 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u97.regs, g96_26]
  have g97_27 : reg n97 (27 : Fin 32) = tbl := by rw [u97.regs, g96_27]
  have keep_kk97 : SvKeepL B n0.mem n97.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m97]; exact keep_kk96
  clear keep_kk96
  have w97_2c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m97]; exact w96_2c
  have w97_30 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m97]; exact w96_30
  have w97_34 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m97]; exact w96_34
  have w97_38 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m97]; exact w96_38
  have w97_44 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m97]; exact w96_44
  have w97_48 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m97]; exact w96_48
  have w97_4c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m97]; exact w96_4c
  have w97_50 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m97]; exact w96_50
  have w97_54 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m97]; exact w96_54
  have w97_58 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m97]; exact w96_58
  have w97_5c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m97]; exact w96_5c
  have w97_60 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m97]; exact w96_60
  have w97_64 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m97]; exact w96_64
  have w97_68 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m97]; exact w96_68
  have w97_6c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m97]; exact w96_6c
  have w97_70 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m97]; exact w96_70
  have w97_74 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m97]; exact w96_74
  have w97_78 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m97]; exact w96_78
  have w97_7c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m97]; exact w96_7c
  have w97_80 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m97]; exact w96_80
  have w97_84 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m97]; exact w96_84
  have w97_88 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m97]; exact w96_88
  have w97_8c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m97]; exact w96_8c
  have w97_90 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m97]; exact w96_90
  have w97_94 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m97]; exact w96_94
  have w97_98 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m97]; exact w96_98
  have w97_9c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m97]; exact w96_9c
  have w97_a0 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m97]; exact w96_a0
  have w97_a4 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m97]; exact w96_a4
  have w97_150 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m97]; exact w96_150
  have w97_154 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m97]; exact w96_154
  have w97_158 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m97]; exact w96_158
  have w97_15c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m97]; exact w96_15c
  have w97_380 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m97]; exact w96_380
  have w97_384 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m97]; exact w96_384
  have w97_388 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m97]; exact w96_388
  have w97_38c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m97]; exact w96_38c
  have w97_420 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m97]; exact w96_420
  have w97_424 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m97]; exact w96_424
  have w97_428 : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m97]; exact w96_428
  have w97_42c : memLoad32 n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m97]; exact w96_42c
  have b97_430 : n97.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m97]; exact b96_430
  clear b96_430 w96_42c w96_428 w96_424 w96_420 w96_38c w96_388 w96_384 w96_380 w96_15c w96_158 w96_154 w96_150 w96_a4 w96_a0 w96_9c w96_98 w96_94 w96_90 w96_8c w96_88 w96_84 w96_80 w96_7c w96_78 w96_74 w96_70 w96_6c w96_68 w96_64 w96_60 w96_5c w96_58 w96_54 w96_50 w96_4c w96_48 w96_44 w96_38 w96_34 w96_30 w96_2c g96_10 g96_27 g96_26 g96_25 g96_24 g96_23 g96_22 g96_21 g96_20 g96_19 g96_18 g96_9 g96_8 g96_4 g96_3 g96_2 V96 E96 fR96 t96 fr96 m96 s96 u96 d96
  -- 0x744: lbu
  obtain ⟨n98, d98, u98⟩ := s97.lbu E97.self sv_at_744 (off' := 0x748) (by decide)
  have s98 : St n98.mem SV n98 0x748 (reg n98) := ⟨u98.pc, rfl, fun _ => rfl⟩
  have m98 : n98.mem = n97.mem := u98.mem
  have fr98 : ∀ x, SvR B x → n98.mem x = n97.mem x := fun x _ => by rw [m98]
  have t98 : Steps n0 n98 := t97.trans (.single d98)
  have fR98 : ∀ x, SvR B x → n98.mem x = M0 x := fun x hx => (fr98 x hx).trans (fR97 x hx)
  have E98 : SvCode n98.mem := E97.fr F fr98
  have V98 : SvSaves B n98.mem v := V97.same m98
  have g98_2 : reg n98 sp = B + 0x21A0 := by rw [u98.regs, upd_ne (by decide) (by decide), g97_2]
  have g98_3 : reg n98 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u98.regs, upd_ne (by decide) (by decide), g97_3]
  have g98_4 : reg n98 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u98.regs, upd_ne (by decide) (by decide), g97_4]
  have g98_8 : reg n98 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u98.regs, upd_ne (by decide) (by decide), g97_8]
  have g98_9 : reg n98 (9 : Fin 32) = tbp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_9]
  have g98_10 : reg n98 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u98.regs, upd_ne (by decide) (by decide), g97_10]
  have g98_18 : reg n98 (18 : Fin 32) = out := by rw [u98.regs, upd_ne (by decide) (by decide), g97_18]
  have g98_19 : reg n98 (19 : Fin 32) = bp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_19]
  have g98_20 : reg n98 (20 : Fin 32) = dg := by rw [u98.regs, upd_ne (by decide) (by decide), g97_20]
  have g98_21 : reg n98 (21 : Fin 32) = rootp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_21]
  have g98_22 : reg n98 (22 : Fin 32) = ll := by rw [u98.regs, upd_ne (by decide) (by decide), g97_22]
  have g98_23 : reg n98 (23 : Fin 32) = sgp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_23]
  have g98_24 : reg n98 (24 : Fin 32) = kp := by rw [u98.regs, upd_ne (by decide) (by decide), g97_24]
  have g98_25 : reg n98 (25 : Fin 32) = sgl := by rw [u98.regs, upd_ne (by decide) (by decide), g97_25]
  have g98_26 : reg n98 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u98.regs, upd_ne (by decide) (by decide), g97_26]
  have g98_27 : reg n98 (27 : Fin 32) = tbl := by rw [u98.regs, upd_ne (by decide) (by decide), g97_27]
  have g98_11 : reg n98 a1 = (BitVec.ofNat 8 tl95.tag).zeroExtend 32 := by
    rw [u98.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g97_2, show B + 0x21A0 + 0x430 = B + 0x21A0 + BitVec.ofNat 32 0x430 by sv_addr, b97_430]
  have keep_kk98 : SvKeepL B n0.mem n98.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m98]; exact keep_kk97
  clear keep_kk97
  have w98_2c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m98]; exact w97_2c
  have w98_30 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m98]; exact w97_30
  have w98_34 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m98]; exact w97_34
  have w98_38 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m98]; exact w97_38
  have w98_44 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m98]; exact w97_44
  have w98_48 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m98]; exact w97_48
  have w98_4c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m98]; exact w97_4c
  have w98_50 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m98]; exact w97_50
  have w98_54 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m98]; exact w97_54
  have w98_58 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m98]; exact w97_58
  have w98_5c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m98]; exact w97_5c
  have w98_60 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m98]; exact w97_60
  have w98_64 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m98]; exact w97_64
  have w98_68 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m98]; exact w97_68
  have w98_6c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m98]; exact w97_6c
  have w98_70 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m98]; exact w97_70
  have w98_74 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m98]; exact w97_74
  have w98_78 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m98]; exact w97_78
  have w98_7c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m98]; exact w97_7c
  have w98_80 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m98]; exact w97_80
  have w98_84 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m98]; exact w97_84
  have w98_88 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m98]; exact w97_88
  have w98_8c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m98]; exact w97_8c
  have w98_90 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m98]; exact w97_90
  have w98_94 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m98]; exact w97_94
  have w98_98 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m98]; exact w97_98
  have w98_9c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m98]; exact w97_9c
  have w98_a0 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m98]; exact w97_a0
  have w98_a4 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m98]; exact w97_a4
  have w98_150 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m98]; exact w97_150
  have w98_154 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m98]; exact w97_154
  have w98_158 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m98]; exact w97_158
  have w98_15c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m98]; exact w97_15c
  have w98_380 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m98]; exact w97_380
  have w98_384 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m98]; exact w97_384
  have w98_388 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m98]; exact w97_388
  have w98_38c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m98]; exact w97_38c
  have w98_420 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m98]; exact w97_420
  have w98_424 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m98]; exact w97_424
  have w98_428 : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m98]; exact w97_428
  have w98_42c : memLoad32 n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m98]; exact w97_42c
  have b98_430 : n98.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m98]; exact b97_430
  clear b97_430 w97_42c w97_428 w97_424 w97_420 w97_38c w97_388 w97_384 w97_380 w97_15c w97_158 w97_154 w97_150 w97_a4 w97_a0 w97_9c w97_98 w97_94 w97_90 w97_8c w97_88 w97_84 w97_80 w97_7c w97_78 w97_74 w97_70 w97_6c w97_68 w97_64 w97_60 w97_5c w97_58 w97_54 w97_50 w97_4c w97_48 w97_44 w97_38 w97_34 w97_30 w97_2c g97_27 g97_26 g97_25 g97_24 g97_23 g97_22 g97_21 g97_20 g97_19 g97_18 g97_10 g97_9 g97_8 g97_4 g97_3 g97_2 V97 E97 fR97 t97 fr97 m97 s97 u97 d97
  -- 0x748
  obtain ⟨n99, c99, u99⟩ := s98.block svDp4748 E98.self svDp4748_end
    ⟨trivial, trivial⟩
  have m99 : n99.mem = n98.mem := u99.mem
  have s99 : St n99.mem SV n99 0x74A (reg n99) := ⟨u99.pc, rfl, fun _ => rfl⟩
  have rb99 : ∀ q, reg n99 q = (runBlock svDp4748 (n98.mem, reg n98)).2 q := fun q => by rw [u99.regs]
  have fr99 : ∀ x, SvR B x → n99.mem x = n98.mem x := fun x _ => by rw [m99]
  have t99 : Steps n0 n99 := t98.trans c99
  have fR99 : ∀ x, SvR B x → n99.mem x = M0 x := fun x hx => (fr99 x hx).trans (fR98 x hx)
  have E99 : SvCode n99.mem := E98.fr F fr99
  have V99 : SvSaves B n99.mem v := V98.same m99
  have g99_2 : reg n99 sp = B + 0x21A0 := by
    rw [rb99, runBlock_reg _ _ _ sp s98.zero (by decide), g98_2]
  have g99_3 : reg n99 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb99, runBlock_reg _ _ _ (3 : Fin 32) s98.zero (by decide), g98_3]
  have g99_4 : reg n99 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb99, runBlock_reg _ _ _ (4 : Fin 32) s98.zero (by decide), g98_4]
  have g99_8 : reg n99 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb99, runBlock_reg _ _ _ (8 : Fin 32) s98.zero (by decide), g98_8]
  have g99_9 : reg n99 (9 : Fin 32) = tbp := by
    rw [rb99, runBlock_reg _ _ _ (9 : Fin 32) s98.zero (by decide), g98_9]
  have g99_10 : reg n99 a0 = (vp) + BitVec.ofNat 32 tl95.header := by
    rw [rb99, runBlock_reg _ _ _ a0 s98.zero (by decide), g98_10]
  have g99_11 : reg n99 a1 = (BitVec.ofNat 8 tl95.tag).zeroExtend 32 := by
    rw [rb99, runBlock_reg _ _ _ a1 s98.zero (by decide), g98_11]
  have g99_18 : reg n99 (18 : Fin 32) = out := by
    rw [rb99, runBlock_reg _ _ _ (18 : Fin 32) s98.zero (by decide), g98_18]
  have g99_19 : reg n99 (19 : Fin 32) = bp := by
    rw [rb99, runBlock_reg _ _ _ (19 : Fin 32) s98.zero (by decide), g98_19]
  have g99_20 : reg n99 (20 : Fin 32) = dg := by
    rw [rb99, runBlock_reg _ _ _ (20 : Fin 32) s98.zero (by decide), g98_20]
  have g99_21 : reg n99 (21 : Fin 32) = rootp := by
    rw [rb99, runBlock_reg _ _ _ (21 : Fin 32) s98.zero (by decide), g98_21]
  have g99_22 : reg n99 (22 : Fin 32) = ll := by
    rw [rb99, runBlock_reg _ _ _ (22 : Fin 32) s98.zero (by decide), g98_22]
  have g99_23 : reg n99 (23 : Fin 32) = sgp := by
    rw [rb99, runBlock_reg _ _ _ (23 : Fin 32) s98.zero (by decide), g98_23]
  have g99_24 : reg n99 (24 : Fin 32) = kp := by
    rw [rb99, runBlock_reg _ _ _ (24 : Fin 32) s98.zero (by decide), g98_24]
  have g99_25 : reg n99 (25 : Fin 32) = sgl := by
    rw [rb99, runBlock_reg _ _ _ (25 : Fin 32) s98.zero (by decide), g98_25]
  have g99_26 : reg n99 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by
    rw [rb99, runBlock_reg _ _ _ (26 : Fin 32) s98.zero (by decide), g98_26]
  have g99_27 : reg n99 (27 : Fin 32) = tbl := by
    rw [rb99, runBlock_reg _ _ _ (27 : Fin 32) s98.zero (by decide), g98_27]
  have g99_12 : reg n99 a2 = BitVec.ofNat 32 0xC := by
    rw [rb99]; simp +decide only [runBlock, BInstr.run, svDp4748, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g98_2, g98_3, g98_4, g98_8, g98_9, g98_10, g98_11, g98_18, g98_19, g98_20, g98_21, g98_22, g98_23, g98_24, g98_25, g98_26, g98_27, s98.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk99 : SvKeepL B n0.mem n99.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m99]; exact keep_kk98
  clear keep_kk98
  have w99_2c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m99]; exact w98_2c
  have w99_30 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m99]; exact w98_30
  have w99_34 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m99]; exact w98_34
  have w99_38 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m99]; exact w98_38
  have w99_44 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m99]; exact w98_44
  have w99_48 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m99]; exact w98_48
  have w99_4c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m99]; exact w98_4c
  have w99_50 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m99]; exact w98_50
  have w99_54 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m99]; exact w98_54
  have w99_58 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m99]; exact w98_58
  have w99_5c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m99]; exact w98_5c
  have w99_60 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m99]; exact w98_60
  have w99_64 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m99]; exact w98_64
  have w99_68 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m99]; exact w98_68
  have w99_6c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m99]; exact w98_6c
  have w99_70 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m99]; exact w98_70
  have w99_74 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m99]; exact w98_74
  have w99_78 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m99]; exact w98_78
  have w99_7c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m99]; exact w98_7c
  have w99_80 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m99]; exact w98_80
  have w99_84 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m99]; exact w98_84
  have w99_88 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m99]; exact w98_88
  have w99_8c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m99]; exact w98_8c
  have w99_90 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m99]; exact w98_90
  have w99_94 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m99]; exact w98_94
  have w99_98 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m99]; exact w98_98
  have w99_9c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m99]; exact w98_9c
  have w99_a0 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m99]; exact w98_a0
  have w99_a4 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m99]; exact w98_a4
  have w99_150 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m99]; exact w98_150
  have w99_154 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m99]; exact w98_154
  have w99_158 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m99]; exact w98_158
  have w99_15c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m99]; exact w98_15c
  have w99_380 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m99]; exact w98_380
  have w99_384 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m99]; exact w98_384
  have w99_388 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m99]; exact w98_388
  have w99_38c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m99]; exact w98_38c
  have w99_420 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m99]; exact w98_420
  have w99_424 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m99]; exact w98_424
  have w99_428 : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m99]; exact w98_428
  have w99_42c : memLoad32 n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m99]; exact w98_42c
  have b99_430 : n99.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m99]; exact b98_430
  clear b98_430 w98_42c w98_428 w98_424 w98_420 w98_38c w98_388 w98_384 w98_380 w98_15c w98_158 w98_154 w98_150 w98_a4 w98_a0 w98_9c w98_98 w98_94 w98_90 w98_8c w98_88 w98_84 w98_80 w98_7c w98_78 w98_74 w98_70 w98_6c w98_68 w98_64 w98_60 w98_5c w98_58 w98_54 w98_50 w98_4c w98_48 w98_44 w98_38 w98_34 w98_30 w98_2c g98_11 g98_27 g98_26 g98_25 g98_24 g98_23 g98_22 g98_21 g98_20 g98_19 g98_18 g98_10 g98_9 g98_8 g98_4 g98_3 g98_2 V98 E98 fR98 t98 fr98 m98 s98 u98 d98
  by_cases hz_99 : BitVec.ofNat 8 tl95.tag = BitVec.ofNat 8 0xC
  rotate_left
  · -- 0x74A: branch, taken
    obtain ⟨n100, d100, u100⟩ := s99.taken E99.self 0x958 sv_at_74a
      (by decide) (by rw [g99_11, g99_12]; exact br_bne_byte_t (by decide) hz_99)
    have s100 : St n100.mem SV n100 0x958 (reg n100) := ⟨u100.pc, rfl, fun _ => rfl⟩
    have m100 : n100.mem = n99.mem := u100.mem
    have fr100 : ∀ x, SvR B x → n100.mem x = n99.mem x := fun x _ => by rw [m100]
    have t100 : Steps n0 n100 := t99.trans (.single d100)
    have fR100 : ∀ x, SvR B x → n100.mem x = M0 x := fun x hx => (fr100 x hx).trans (fR99 x hx)
    have E100 : SvCode n100.mem := E99.fr F fr100
    have V100 : SvSaves B n100.mem v := V99.same m100
    have g100_2 : reg n100 sp = B + 0x21A0 := by rw [u100.regs, g99_2]
    have g100_3 : reg n100 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u100.regs, g99_3]
    have g100_4 : reg n100 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u100.regs, g99_4]
    have g100_8 : reg n100 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u100.regs, g99_8]
    have g100_9 : reg n100 (9 : Fin 32) = tbp := by rw [u100.regs, g99_9]
    have g100_10 : reg n100 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u100.regs, g99_10]
    have g100_11 : reg n100 a1 = (BitVec.ofNat 8 tl95.tag).zeroExtend 32 := by rw [u100.regs, g99_11]
    have g100_12 : reg n100 a2 = BitVec.ofNat 32 0xC := by rw [u100.regs, g99_12]
    have g100_18 : reg n100 (18 : Fin 32) = out := by rw [u100.regs, g99_18]
    have g100_19 : reg n100 (19 : Fin 32) = bp := by rw [u100.regs, g99_19]
    have g100_20 : reg n100 (20 : Fin 32) = dg := by rw [u100.regs, g99_20]
    have g100_21 : reg n100 (21 : Fin 32) = rootp := by rw [u100.regs, g99_21]
    have g100_22 : reg n100 (22 : Fin 32) = ll := by rw [u100.regs, g99_22]
    have g100_23 : reg n100 (23 : Fin 32) = sgp := by rw [u100.regs, g99_23]
    have g100_24 : reg n100 (24 : Fin 32) = kp := by rw [u100.regs, g99_24]
    have g100_25 : reg n100 (25 : Fin 32) = sgl := by rw [u100.regs, g99_25]
    have g100_26 : reg n100 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u100.regs, g99_26]
    have g100_27 : reg n100 (27 : Fin 32) = tbl := by rw [u100.regs, g99_27]
    have keep_kk100 : SvKeepL B n0.mem n100.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m100]; exact keep_kk99
    clear keep_kk99
    have w100_2c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m100]; exact w99_2c
    have w100_30 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m100]; exact w99_30
    have w100_34 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m100]; exact w99_34
    have w100_38 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m100]; exact w99_38
    have w100_44 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m100]; exact w99_44
    have w100_48 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m100]; exact w99_48
    have w100_4c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m100]; exact w99_4c
    have w100_50 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m100]; exact w99_50
    have w100_54 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m100]; exact w99_54
    have w100_58 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m100]; exact w99_58
    have w100_5c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m100]; exact w99_5c
    have w100_60 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m100]; exact w99_60
    have w100_64 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m100]; exact w99_64
    have w100_68 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m100]; exact w99_68
    have w100_6c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m100]; exact w99_6c
    have w100_70 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m100]; exact w99_70
    have w100_74 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m100]; exact w99_74
    have w100_78 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m100]; exact w99_78
    have w100_7c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m100]; exact w99_7c
    have w100_80 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m100]; exact w99_80
    have w100_84 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m100]; exact w99_84
    have w100_88 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m100]; exact w99_88
    have w100_8c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m100]; exact w99_8c
    have w100_90 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m100]; exact w99_90
    have w100_94 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m100]; exact w99_94
    have w100_98 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m100]; exact w99_98
    have w100_9c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m100]; exact w99_9c
    have w100_a0 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m100]; exact w99_a0
    have w100_a4 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m100]; exact w99_a4
    have w100_150 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m100]; exact w99_150
    have w100_154 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m100]; exact w99_154
    have w100_158 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m100]; exact w99_158
    have w100_15c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m100]; exact w99_15c
    have w100_380 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m100]; exact w99_380
    have w100_384 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m100]; exact w99_384
    have w100_388 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m100]; exact w99_388
    have w100_38c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m100]; exact w99_38c
    have w100_420 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m100]; exact w99_420
    have w100_424 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m100]; exact w99_424
    have w100_428 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m100]; exact w99_428
    have w100_42c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m100]; exact w99_42c
    have b100_430 : n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m100]; exact b99_430
    clear b99_430 w99_42c w99_428 w99_424 w99_420 w99_38c w99_388 w99_384 w99_380 w99_15c w99_158 w99_154 w99_150 w99_a4 w99_a0 w99_9c w99_98 w99_94 w99_90 w99_8c w99_88 w99_84 w99_80 w99_7c w99_78 w99_74 w99_70 w99_6c w99_68 w99_64 w99_60 w99_5c w99_58 w99_54 w99_50 w99_4c w99_48 w99_44 w99_38 w99_34 w99_30 w99_2c g99_12 g99_27 g99_26 g99_25 g99_24 g99_23 g99_22 g99_21 g99_20 g99_19 g99_18 g99_11 g99_10 g99_9 g99_8 g99_4 g99_3 g99_2 V99 E99 fR99 t99 fr99 rb99 s99 m99 u99 c99
    -- 0x958
    obtain ⟨n101, c101, u101⟩ := s100.block svDp4958 E100.self svDp4958_end
      ⟨trivial, trivial⟩
    have m101 : n101.mem = n100.mem := u101.mem
    have s101 : St n101.mem SV n101 0x95A (reg n101) := ⟨u101.pc, rfl, fun _ => rfl⟩
    have rb101 : ∀ q, reg n101 q = (runBlock svDp4958 (n100.mem, reg n100)).2 q := fun q => by rw [u101.regs]
    have fr101 : ∀ x, SvR B x → n101.mem x = n100.mem x := fun x _ => by rw [m101]
    have t101 : Steps n0 n101 := t100.trans c101
    have fR101 : ∀ x, SvR B x → n101.mem x = M0 x := fun x hx => (fr101 x hx).trans (fR100 x hx)
    have E101 : SvCode n101.mem := E100.fr F fr101
    have V101 : SvSaves B n101.mem v := V100.same m101
    have g101_2 : reg n101 sp = B + 0x21A0 := by
      rw [rb101, runBlock_reg _ _ _ sp s100.zero (by decide), g100_2]
    have g101_3 : reg n101 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb101, runBlock_reg _ _ _ (3 : Fin 32) s100.zero (by decide), g100_3]
    have g101_4 : reg n101 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb101, runBlock_reg _ _ _ (4 : Fin 32) s100.zero (by decide), g100_4]
    have g101_8 : reg n101 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb101, runBlock_reg _ _ _ (8 : Fin 32) s100.zero (by decide), g100_8]
    have g101_9 : reg n101 (9 : Fin 32) = tbp := by
      rw [rb101, runBlock_reg _ _ _ (9 : Fin 32) s100.zero (by decide), g100_9]
    have g101_11 : reg n101 a1 = (BitVec.ofNat 8 tl95.tag).zeroExtend 32 := by
      rw [rb101, runBlock_reg _ _ _ a1 s100.zero (by decide), g100_11]
    have g101_12 : reg n101 a2 = BitVec.ofNat 32 0xC := by
      rw [rb101, runBlock_reg _ _ _ a2 s100.zero (by decide), g100_12]
    have g101_18 : reg n101 (18 : Fin 32) = out := by
      rw [rb101, runBlock_reg _ _ _ (18 : Fin 32) s100.zero (by decide), g100_18]
    have g101_19 : reg n101 (19 : Fin 32) = bp := by
      rw [rb101, runBlock_reg _ _ _ (19 : Fin 32) s100.zero (by decide), g100_19]
    have g101_20 : reg n101 (20 : Fin 32) = dg := by
      rw [rb101, runBlock_reg _ _ _ (20 : Fin 32) s100.zero (by decide), g100_20]
    have g101_21 : reg n101 (21 : Fin 32) = rootp := by
      rw [rb101, runBlock_reg _ _ _ (21 : Fin 32) s100.zero (by decide), g100_21]
    have g101_22 : reg n101 (22 : Fin 32) = ll := by
      rw [rb101, runBlock_reg _ _ _ (22 : Fin 32) s100.zero (by decide), g100_22]
    have g101_23 : reg n101 (23 : Fin 32) = sgp := by
      rw [rb101, runBlock_reg _ _ _ (23 : Fin 32) s100.zero (by decide), g100_23]
    have g101_24 : reg n101 (24 : Fin 32) = kp := by
      rw [rb101, runBlock_reg _ _ _ (24 : Fin 32) s100.zero (by decide), g100_24]
    have g101_25 : reg n101 (25 : Fin 32) = sgl := by
      rw [rb101, runBlock_reg _ _ _ (25 : Fin 32) s100.zero (by decide), g100_25]
    have g101_26 : reg n101 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by
      rw [rb101, runBlock_reg _ _ _ (26 : Fin 32) s100.zero (by decide), g100_26]
    have g101_27 : reg n101 (27 : Fin 32) = tbl := by
      rw [rb101, runBlock_reg _ _ _ (27 : Fin 32) s100.zero (by decide), g100_27]
    have g101_10 : reg n101 a0 = BitVec.ofNat 32 0x16 := by
      rw [rb101]; simp +decide only [runBlock, BInstr.run, svDp4958, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g100_2, g100_3, g100_4, g100_8, g100_9, g100_10, g100_11, g100_12, g100_18, g100_19, g100_20, g100_21, g100_22, g100_23, g100_24, g100_25, g100_26, g100_27, s100.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk101 : SvKeepL B n0.mem n101.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m101]; exact keep_kk100
    clear keep_kk100
    have w101_2c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m101]; exact w100_2c
    have w101_30 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m101]; exact w100_30
    have w101_34 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m101]; exact w100_34
    have w101_38 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m101]; exact w100_38
    have w101_44 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m101]; exact w100_44
    have w101_48 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m101]; exact w100_48
    have w101_4c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m101]; exact w100_4c
    have w101_50 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m101]; exact w100_50
    have w101_54 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m101]; exact w100_54
    have w101_58 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m101]; exact w100_58
    have w101_5c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m101]; exact w100_5c
    have w101_60 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m101]; exact w100_60
    have w101_64 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m101]; exact w100_64
    have w101_68 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m101]; exact w100_68
    have w101_6c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m101]; exact w100_6c
    have w101_70 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m101]; exact w100_70
    have w101_74 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m101]; exact w100_74
    have w101_78 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m101]; exact w100_78
    have w101_7c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m101]; exact w100_7c
    have w101_80 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m101]; exact w100_80
    have w101_84 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m101]; exact w100_84
    have w101_88 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m101]; exact w100_88
    have w101_8c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m101]; exact w100_8c
    have w101_90 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m101]; exact w100_90
    have w101_94 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m101]; exact w100_94
    have w101_98 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m101]; exact w100_98
    have w101_9c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m101]; exact w100_9c
    have w101_a0 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m101]; exact w100_a0
    have w101_a4 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m101]; exact w100_a4
    have w101_150 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m101]; exact w100_150
    have w101_154 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m101]; exact w100_154
    have w101_158 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m101]; exact w100_158
    have w101_15c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m101]; exact w100_15c
    have w101_380 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m101]; exact w100_380
    have w101_384 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m101]; exact w100_384
    have w101_388 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m101]; exact w100_388
    have w101_38c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m101]; exact w100_38c
    have w101_420 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m101]; exact w100_420
    have w101_424 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m101]; exact w100_424
    have w101_428 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m101]; exact w100_428
    have w101_42c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m101]; exact w100_42c
    have b101_430 : n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m101]; exact b100_430
    clear b100_430 w100_42c w100_428 w100_424 w100_420 w100_38c w100_388 w100_384 w100_380 w100_15c w100_158 w100_154 w100_150 w100_a4 w100_a0 w100_9c w100_98 w100_94 w100_90 w100_8c w100_88 w100_84 w100_80 w100_7c w100_78 w100_74 w100_70 w100_6c w100_68 w100_64 w100_60 w100_5c w100_58 w100_54 w100_50 w100_4c w100_48 w100_44 w100_38 w100_34 w100_30 w100_2c g100_27 g100_26 g100_25 g100_24 g100_23 g100_22 g100_21 g100_20 g100_19 g100_18 g100_12 g100_11 g100_10 g100_9 g100_8 g100_4 g100_3 g100_2 V100 E100 fR100 t100 fr100 m100 s100 u100 d100
    -- 0x95A: j
    obtain ⟨n102, d102, u102⟩ := s101.jump E101.self sv_at_95a (off' := 0x942) (by decide)
      (by rw [s101.pc]; decide)
    have s102 : St n102.mem SV n102 0x942 (reg n102) := ⟨u102.pc, rfl, fun _ => rfl⟩
    have m102 : n102.mem = n101.mem := u102.mem
    have fr102 : ∀ x, SvR B x → n102.mem x = n101.mem x := fun x _ => by rw [m102]
    have t102 : Steps n0 n102 := t101.trans (.single d102)
    have fR102 : ∀ x, SvR B x → n102.mem x = M0 x := fun x hx => (fr102 x hx).trans (fR101 x hx)
    have E102 : SvCode n102.mem := E101.fr F fr102
    have V102 : SvSaves B n102.mem v := V101.same m102
    have g102_2 : reg n102 sp = B + 0x21A0 := by rw [u102.regs, g101_2]
    have g102_3 : reg n102 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u102.regs, g101_3]
    have g102_4 : reg n102 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u102.regs, g101_4]
    have g102_8 : reg n102 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u102.regs, g101_8]
    have g102_9 : reg n102 (9 : Fin 32) = tbp := by rw [u102.regs, g101_9]
    have g102_10 : reg n102 a0 = BitVec.ofNat 32 0x16 := by rw [u102.regs, g101_10]
    have g102_11 : reg n102 a1 = (BitVec.ofNat 8 tl95.tag).zeroExtend 32 := by rw [u102.regs, g101_11]
    have g102_12 : reg n102 a2 = BitVec.ofNat 32 0xC := by rw [u102.regs, g101_12]
    have g102_18 : reg n102 (18 : Fin 32) = out := by rw [u102.regs, g101_18]
    have g102_19 : reg n102 (19 : Fin 32) = bp := by rw [u102.regs, g101_19]
    have g102_20 : reg n102 (20 : Fin 32) = dg := by rw [u102.regs, g101_20]
    have g102_21 : reg n102 (21 : Fin 32) = rootp := by rw [u102.regs, g101_21]
    have g102_22 : reg n102 (22 : Fin 32) = ll := by rw [u102.regs, g101_22]
    have g102_23 : reg n102 (23 : Fin 32) = sgp := by rw [u102.regs, g101_23]
    have g102_24 : reg n102 (24 : Fin 32) = kp := by rw [u102.regs, g101_24]
    have g102_25 : reg n102 (25 : Fin 32) = sgl := by rw [u102.regs, g101_25]
    have g102_26 : reg n102 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u102.regs, g101_26]
    have g102_27 : reg n102 (27 : Fin 32) = tbl := by rw [u102.regs, g101_27]
    have keep_kk102 : SvKeepL B n0.mem n102.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m102]; exact keep_kk101
    clear keep_kk101
    have w102_2c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m102]; exact w101_2c
    have w102_30 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m102]; exact w101_30
    have w102_34 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m102]; exact w101_34
    have w102_38 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m102]; exact w101_38
    have w102_44 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m102]; exact w101_44
    have w102_48 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m102]; exact w101_48
    have w102_4c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m102]; exact w101_4c
    have w102_50 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m102]; exact w101_50
    have w102_54 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m102]; exact w101_54
    have w102_58 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m102]; exact w101_58
    have w102_5c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m102]; exact w101_5c
    have w102_60 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m102]; exact w101_60
    have w102_64 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m102]; exact w101_64
    have w102_68 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m102]; exact w101_68
    have w102_6c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m102]; exact w101_6c
    have w102_70 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m102]; exact w101_70
    have w102_74 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m102]; exact w101_74
    have w102_78 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m102]; exact w101_78
    have w102_7c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m102]; exact w101_7c
    have w102_80 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m102]; exact w101_80
    have w102_84 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m102]; exact w101_84
    have w102_88 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m102]; exact w101_88
    have w102_8c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m102]; exact w101_8c
    have w102_90 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m102]; exact w101_90
    have w102_94 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m102]; exact w101_94
    have w102_98 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m102]; exact w101_98
    have w102_9c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m102]; exact w101_9c
    have w102_a0 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m102]; exact w101_a0
    have w102_a4 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m102]; exact w101_a4
    have w102_150 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m102]; exact w101_150
    have w102_154 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m102]; exact w101_154
    have w102_158 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m102]; exact w101_158
    have w102_15c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m102]; exact w101_15c
    have w102_380 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m102]; exact w101_380
    have w102_384 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m102]; exact w101_384
    have w102_388 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m102]; exact w101_388
    have w102_38c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m102]; exact w101_38c
    have w102_420 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m102]; exact w101_420
    have w102_424 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m102]; exact w101_424
    have w102_428 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m102]; exact w101_428
    have w102_42c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m102]; exact w101_42c
    have b102_430 : n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m102]; exact b101_430
    clear b101_430 w101_42c w101_428 w101_424 w101_420 w101_38c w101_388 w101_384 w101_380 w101_15c w101_158 w101_154 w101_150 w101_a4 w101_a0 w101_9c w101_98 w101_94 w101_90 w101_8c w101_88 w101_84 w101_80 w101_7c w101_78 w101_74 w101_70 w101_6c w101_68 w101_64 w101_60 w101_5c w101_58 w101_54 w101_50 w101_4c w101_48 w101_44 w101_38 w101_34 w101_30 w101_2c g101_10 g101_27 g101_26 g101_25 g101_24 g101_23 g101_22 g101_21 g101_20 g101_19 g101_18 g101_12 g101_11 g101_9 g101_8 g101_4 g101_3 g101_2 V101 E101 fR101 t101 fr101 rb101 s101 m101 u101 c101
    -- 0x942: sw
    obtain ⟨n103, d103, s103, fr103, K103, W103, rg103⟩ := sv_sw F E102 s102 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g102_2]; sv_addr) (by decide) (by decide)
    have t103 : Steps n0 n103 := t102.trans d103
    have fR103 : ∀ x, SvR B x → n103.mem x = M0 x := fun x hx => (fr103 x hx).trans (fR102 x hx)
    have E103 : SvCode n103.mem := E102.fr F fr103
    have V103 : SvSaves B n103.mem v := V102.keep K103 (by decide)
    have g103_2 : reg n103 sp = B + 0x21A0 := by rw [rg103 sp, g102_2]
    have g103_3 : reg n103 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg103 (3 : Fin 32), g102_3]
    have g103_4 : reg n103 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg103 (4 : Fin 32), g102_4]
    have g103_8 : reg n103 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg103 (8 : Fin 32), g102_8]
    have g103_9 : reg n103 (9 : Fin 32) = tbp := by rw [rg103 (9 : Fin 32), g102_9]
    have g103_10 : reg n103 a0 = BitVec.ofNat 32 0x16 := by rw [rg103 a0, g102_10]
    have g103_11 : reg n103 a1 = (BitVec.ofNat 8 tl95.tag).zeroExtend 32 := by rw [rg103 a1, g102_11]
    have g103_12 : reg n103 a2 = BitVec.ofNat 32 0xC := by rw [rg103 a2, g102_12]
    have g103_18 : reg n103 (18 : Fin 32) = out := by rw [rg103 (18 : Fin 32), g102_18]
    have g103_19 : reg n103 (19 : Fin 32) = bp := by rw [rg103 (19 : Fin 32), g102_19]
    have g103_20 : reg n103 (20 : Fin 32) = dg := by rw [rg103 (20 : Fin 32), g102_20]
    have g103_21 : reg n103 (21 : Fin 32) = rootp := by rw [rg103 (21 : Fin 32), g102_21]
    have g103_22 : reg n103 (22 : Fin 32) = ll := by rw [rg103 (22 : Fin 32), g102_22]
    have g103_23 : reg n103 (23 : Fin 32) = sgp := by rw [rg103 (23 : Fin 32), g102_23]
    have g103_24 : reg n103 (24 : Fin 32) = kp := by rw [rg103 (24 : Fin 32), g102_24]
    have g103_25 : reg n103 (25 : Fin 32) = sgl := by rw [rg103 (25 : Fin 32), g102_25]
    have g103_26 : reg n103 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [rg103 (26 : Fin 32), g102_26]
    have g103_27 : reg n103 (27 : Fin 32) = tbl := by rw [rg103 (27 : Fin 32), g102_27]
    have keep_kk103 : SvKeepL B n0.mem n103.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := keep_kk102.trans K103.toL
    clear keep_kk102
    have w103_2c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K103.w32 (by decide) (by decide)).trans w102_2c
    have w103_30 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K103.w32 (by decide) (by decide)).trans w102_30
    have w103_34 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K103.w32 (by decide) (by decide)).trans w102_34
    have w103_38 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K103.w32 (by decide) (by decide)).trans w102_38
    have w103_48 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K103.w32 (by decide) (by decide)).trans w102_48
    have w103_4c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K103.w32 (by decide) (by decide)).trans w102_4c
    have w103_50 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K103.w32 (by decide) (by decide)).trans w102_50
    have w103_54 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K103.w32 (by decide) (by decide)).trans w102_54
    have w103_58 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K103.w32 (by decide) (by decide)).trans w102_58
    have w103_5c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K103.w32 (by decide) (by decide)).trans w102_5c
    have w103_60 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K103.w32 (by decide) (by decide)).trans w102_60
    have w103_64 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K103.w32 (by decide) (by decide)).trans w102_64
    have w103_68 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K103.w32 (by decide) (by decide)).trans w102_68
    have w103_6c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K103.w32 (by decide) (by decide)).trans w102_6c
    have w103_70 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K103.w32 (by decide) (by decide)).trans w102_70
    have w103_74 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K103.w32 (by decide) (by decide)).trans w102_74
    have w103_78 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K103.w32 (by decide) (by decide)).trans w102_78
    have w103_7c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K103.w32 (by decide) (by decide)).trans w102_7c
    have w103_80 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K103.w32 (by decide) (by decide)).trans w102_80
    have w103_84 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K103.w32 (by decide) (by decide)).trans w102_84
    have w103_88 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K103.w32 (by decide) (by decide)).trans w102_88
    have w103_8c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K103.w32 (by decide) (by decide)).trans w102_8c
    have w103_90 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K103.w32 (by decide) (by decide)).trans w102_90
    have w103_94 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K103.w32 (by decide) (by decide)).trans w102_94
    have w103_98 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K103.w32 (by decide) (by decide)).trans w102_98
    have w103_9c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K103.w32 (by decide) (by decide)).trans w102_9c
    have w103_a0 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K103.w32 (by decide) (by decide)).trans w102_a0
    have w103_a4 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K103.w32 (by decide) (by decide)).trans w102_a4
    have w103_150 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K103.w32 (by decide) (by decide)).trans w102_150
    have w103_154 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K103.w32 (by decide) (by decide)).trans w102_154
    have w103_158 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K103.w32 (by decide) (by decide)).trans w102_158
    have w103_15c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K103.w32 (by decide) (by decide)).trans w102_15c
    have w103_380 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K103.w32 (by decide) (by decide)).trans w102_380
    have w103_384 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K103.w32 (by decide) (by decide)).trans w102_384
    have w103_388 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := (K103.w32 (by decide) (by decide)).trans w102_388
    have w103_38c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := (K103.w32 (by decide) (by decide)).trans w102_38c
    have w103_420 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := (K103.w32 (by decide) (by decide)).trans w102_420
    have w103_424 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := (K103.w32 (by decide) (by decide)).trans w102_424
    have w103_428 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K103.w32 (by decide) (by decide)).trans w102_428
    have w103_42c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := (K103.w32 (by decide) (by decide)).trans w102_42c
    have b103_430 : n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := (K103.b8 (by decide) (by decide)).trans b102_430
    have w103_44 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [W103, g102_10]
    clear b102_430 w102_42c w102_428 w102_424 w102_420 w102_38c w102_388 w102_384 w102_380 w102_15c w102_158 w102_154 w102_150 w102_a4 w102_a0 w102_9c w102_98 w102_94 w102_90 w102_8c w102_88 w102_84 w102_80 w102_7c w102_78 w102_74 w102_70 w102_6c w102_68 w102_64 w102_60 w102_5c w102_58 w102_54 w102_50 w102_4c w102_48 w102_44 w102_38 w102_34 w102_30 w102_2c g102_27 g102_26 g102_25 g102_24 g102_23 g102_22 g102_21 g102_20 g102_19 g102_18 g102_12 g102_11 g102_10 g102_9 g102_8 g102_4 g102_3 g102_2 V102 E102 fR102 t102 fr102 m102 s102 u102 d102
    -- 0x944: lw
    obtain ⟨n104, d104, u104⟩ := s103.lw E103.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g103_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s104 : St n104.mem SV n104 0x946 (reg n104) := ⟨u104.pc, rfl, fun _ => rfl⟩
    have m104 : n104.mem = n103.mem := u104.mem
    have fr104 : ∀ x, SvR B x → n104.mem x = n103.mem x := fun x _ => by rw [m104]
    have t104 : Steps n0 n104 := t103.trans (.single d104)
    have fR104 : ∀ x, SvR B x → n104.mem x = M0 x := fun x hx => (fr104 x hx).trans (fR103 x hx)
    have E104 : SvCode n104.mem := E103.fr F fr104
    have V104 : SvSaves B n104.mem v := V103.same m104
    have g104_2 : reg n104 sp = B + 0x21A0 := by rw [u104.regs, upd_ne (by decide) (by decide), g103_2]
    have g104_3 : reg n104 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u104.regs, upd_ne (by decide) (by decide), g103_3]
    have g104_4 : reg n104 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u104.regs, upd_ne (by decide) (by decide), g103_4]
    have g104_9 : reg n104 (9 : Fin 32) = tbp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_9]
    have g104_10 : reg n104 a0 = BitVec.ofNat 32 0x16 := by rw [u104.regs, upd_ne (by decide) (by decide), g103_10]
    have g104_11 : reg n104 a1 = (BitVec.ofNat 8 tl95.tag).zeroExtend 32 := by rw [u104.regs, upd_ne (by decide) (by decide), g103_11]
    have g104_12 : reg n104 a2 = BitVec.ofNat 32 0xC := by rw [u104.regs, upd_ne (by decide) (by decide), g103_12]
    have g104_18 : reg n104 (18 : Fin 32) = out := by rw [u104.regs, upd_ne (by decide) (by decide), g103_18]
    have g104_19 : reg n104 (19 : Fin 32) = bp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_19]
    have g104_20 : reg n104 (20 : Fin 32) = dg := by rw [u104.regs, upd_ne (by decide) (by decide), g103_20]
    have g104_21 : reg n104 (21 : Fin 32) = rootp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_21]
    have g104_22 : reg n104 (22 : Fin 32) = ll := by rw [u104.regs, upd_ne (by decide) (by decide), g103_22]
    have g104_23 : reg n104 (23 : Fin 32) = sgp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_23]
    have g104_24 : reg n104 (24 : Fin 32) = kp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_24]
    have g104_25 : reg n104 (25 : Fin 32) = sgl := by rw [u104.regs, upd_ne (by decide) (by decide), g103_25]
    have g104_26 : reg n104 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u104.regs, upd_ne (by decide) (by decide), g103_26]
    have g104_27 : reg n104 (27 : Fin 32) = tbl := by rw [u104.regs, upd_ne (by decide) (by decide), g103_27]
    have g104_8 : reg n104 (8 : Fin 32) = BitVec.ofNat 32 0x16 := by
      rw [u104.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g103_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w103_44]
    have keep_kk104 : SvKeepL B n0.mem n104.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m104]; exact keep_kk103
    clear keep_kk103
    have w104_2c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m104]; exact w103_2c
    have w104_30 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m104]; exact w103_30
    have w104_34 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m104]; exact w103_34
    have w104_38 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m104]; exact w103_38
    have w104_44 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m104]; exact w103_44
    have w104_48 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m104]; exact w103_48
    have w104_4c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m104]; exact w103_4c
    have w104_50 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m104]; exact w103_50
    have w104_54 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m104]; exact w103_54
    have w104_58 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m104]; exact w103_58
    have w104_5c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m104]; exact w103_5c
    have w104_60 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m104]; exact w103_60
    have w104_64 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m104]; exact w103_64
    have w104_68 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m104]; exact w103_68
    have w104_6c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m104]; exact w103_6c
    have w104_70 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m104]; exact w103_70
    have w104_74 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m104]; exact w103_74
    have w104_78 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m104]; exact w103_78
    have w104_7c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m104]; exact w103_7c
    have w104_80 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m104]; exact w103_80
    have w104_84 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m104]; exact w103_84
    have w104_88 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m104]; exact w103_88
    have w104_8c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m104]; exact w103_8c
    have w104_90 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m104]; exact w103_90
    have w104_94 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m104]; exact w103_94
    have w104_98 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m104]; exact w103_98
    have w104_9c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m104]; exact w103_9c
    have w104_a0 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m104]; exact w103_a0
    have w104_a4 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m104]; exact w103_a4
    have w104_150 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m104]; exact w103_150
    have w104_154 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m104]; exact w103_154
    have w104_158 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m104]; exact w103_158
    have w104_15c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m104]; exact w103_15c
    have w104_380 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m104]; exact w103_380
    have w104_384 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m104]; exact w103_384
    have w104_388 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m104]; exact w103_388
    have w104_38c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m104]; exact w103_38c
    have w104_420 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m104]; exact w103_420
    have w104_424 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m104]; exact w103_424
    have w104_428 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m104]; exact w103_428
    have w104_42c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m104]; exact w103_42c
    have b104_430 : n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m104]; exact b103_430
    clear w103_44 b103_430 w103_42c w103_428 w103_424 w103_420 w103_38c w103_388 w103_384 w103_380 w103_15c w103_158 w103_154 w103_150 w103_a4 w103_a0 w103_9c w103_98 w103_94 w103_90 w103_8c w103_88 w103_84 w103_80 w103_7c w103_78 w103_74 w103_70 w103_6c w103_68 w103_64 w103_60 w103_5c w103_58 w103_54 w103_50 w103_4c w103_48 w103_38 w103_34 w103_30 w103_2c g103_27 g103_26 g103_25 g103_24 g103_23 g103_22 g103_21 g103_20 g103_19 g103_18 g103_12 g103_11 g103_10 g103_9 g103_8 g103_4 g103_3 g103_2 V103 E103 fR103 t103 rg103 W103 K103 fr103 s103 d103
    -- 0x946: j
    obtain ⟨n105, d105, u105⟩ := s104.jump E104.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s104.pc]; decide)
    have s105 : St n105.mem SV n105 0x7A4 (reg n105) := ⟨u105.pc, rfl, fun _ => rfl⟩
    have m105 : n105.mem = n104.mem := u105.mem
    have fr105 : ∀ x, SvR B x → n105.mem x = n104.mem x := fun x _ => by rw [m105]
    have t105 : Steps n0 n105 := t104.trans (.single d105)
    have fR105 : ∀ x, SvR B x → n105.mem x = M0 x := fun x hx => (fr105 x hx).trans (fR104 x hx)
    have E105 : SvCode n105.mem := E104.fr F fr105
    have V105 : SvSaves B n105.mem v := V104.same m105
    have g105_2 : reg n105 sp = B + 0x21A0 := by rw [u105.regs, g104_2]
    have g105_3 : reg n105 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u105.regs, g104_3]
    have g105_4 : reg n105 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u105.regs, g104_4]
    have g105_8 : reg n105 (8 : Fin 32) = BitVec.ofNat 32 0x16 := by rw [u105.regs, g104_8]
    have g105_9 : reg n105 (9 : Fin 32) = tbp := by rw [u105.regs, g104_9]
    have g105_10 : reg n105 a0 = BitVec.ofNat 32 0x16 := by rw [u105.regs, g104_10]
    have g105_11 : reg n105 a1 = (BitVec.ofNat 8 tl95.tag).zeroExtend 32 := by rw [u105.regs, g104_11]
    have g105_12 : reg n105 a2 = BitVec.ofNat 32 0xC := by rw [u105.regs, g104_12]
    have g105_18 : reg n105 (18 : Fin 32) = out := by rw [u105.regs, g104_18]
    have g105_19 : reg n105 (19 : Fin 32) = bp := by rw [u105.regs, g104_19]
    have g105_20 : reg n105 (20 : Fin 32) = dg := by rw [u105.regs, g104_20]
    have g105_21 : reg n105 (21 : Fin 32) = rootp := by rw [u105.regs, g104_21]
    have g105_22 : reg n105 (22 : Fin 32) = ll := by rw [u105.regs, g104_22]
    have g105_23 : reg n105 (23 : Fin 32) = sgp := by rw [u105.regs, g104_23]
    have g105_24 : reg n105 (24 : Fin 32) = kp := by rw [u105.regs, g104_24]
    have g105_25 : reg n105 (25 : Fin 32) = sgl := by rw [u105.regs, g104_25]
    have g105_26 : reg n105 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u105.regs, g104_26]
    have g105_27 : reg n105 (27 : Fin 32) = tbl := by rw [u105.regs, g104_27]
    have keep_kk105 : SvKeepL B n0.mem n105.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m105]; exact keep_kk104
    clear keep_kk104
    have w105_2c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m105]; exact w104_2c
    have w105_30 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m105]; exact w104_30
    have w105_34 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m105]; exact w104_34
    have w105_38 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m105]; exact w104_38
    have w105_44 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m105]; exact w104_44
    have w105_48 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m105]; exact w104_48
    have w105_4c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m105]; exact w104_4c
    have w105_50 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m105]; exact w104_50
    have w105_54 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m105]; exact w104_54
    have w105_58 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m105]; exact w104_58
    have w105_5c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m105]; exact w104_5c
    have w105_60 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m105]; exact w104_60
    have w105_64 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m105]; exact w104_64
    have w105_68 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m105]; exact w104_68
    have w105_6c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m105]; exact w104_6c
    have w105_70 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m105]; exact w104_70
    have w105_74 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m105]; exact w104_74
    have w105_78 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m105]; exact w104_78
    have w105_7c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m105]; exact w104_7c
    have w105_80 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m105]; exact w104_80
    have w105_84 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m105]; exact w104_84
    have w105_88 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m105]; exact w104_88
    have w105_8c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m105]; exact w104_8c
    have w105_90 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m105]; exact w104_90
    have w105_94 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m105]; exact w104_94
    have w105_98 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m105]; exact w104_98
    have w105_9c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m105]; exact w104_9c
    have w105_a0 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m105]; exact w104_a0
    have w105_a4 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m105]; exact w104_a4
    have w105_150 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m105]; exact w104_150
    have w105_154 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m105]; exact w104_154
    have w105_158 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m105]; exact w104_158
    have w105_15c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m105]; exact w104_15c
    have w105_380 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m105]; exact w104_380
    have w105_384 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m105]; exact w104_384
    have w105_388 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m105]; exact w104_388
    have w105_38c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m105]; exact w104_38c
    have w105_420 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m105]; exact w104_420
    have w105_424 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m105]; exact w104_424
    have w105_428 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m105]; exact w104_428
    have w105_42c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m105]; exact w104_42c
    have b105_430 : n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m105]; exact b104_430
    clear b104_430 w104_42c w104_428 w104_424 w104_420 w104_38c w104_388 w104_384 w104_380 w104_15c w104_158 w104_154 w104_150 w104_a4 w104_a0 w104_9c w104_98 w104_94 w104_90 w104_8c w104_88 w104_84 w104_80 w104_7c w104_78 w104_74 w104_70 w104_6c w104_68 w104_64 w104_60 w104_5c w104_58 w104_54 w104_50 w104_4c w104_48 w104_44 w104_38 w104_34 w104_30 w104_2c g104_8 g104_27 g104_26 g104_25 g104_24 g104_23 g104_22 g104_21 g104_20 g104_19 g104_18 g104_12 g104_11 g104_10 g104_9 g104_4 g104_3 g104_2 V104 E104 fR104 t104 fr104 m104 s104 u104 d104
    exact .inl ⟨(fun ⟨tl95', h0', h1', _⟩ => by rw [hr95] at h0'; cases h0'; exact hz_99 h1'), sv_fail F E105 s105 t105 (fun x hx => (fR105 x hx).trans (fM x hx).symm) V105 hret g105_2 g105_18 hO g105_3 g105_4 (by rw [g105_8]; sv_code)⟩
  -- 0x74A: branch, not taken
  obtain ⟨n100, d100, u100⟩ := s99.notTaken E99.self 0x74E sv_at_74a
    (by decide) (by rw [g99_11, g99_12]; exact br_bne_byte_f (by decide) hz_99)
  have s100 : St n100.mem SV n100 0x74E (reg n100) := ⟨u100.pc, rfl, fun _ => rfl⟩
  have m100 : n100.mem = n99.mem := u100.mem
  have fr100 : ∀ x, SvR B x → n100.mem x = n99.mem x := fun x _ => by rw [m100]
  have t100 : Steps n0 n100 := t99.trans (.single d100)
  have fR100 : ∀ x, SvR B x → n100.mem x = M0 x := fun x hx => (fr100 x hx).trans (fR99 x hx)
  have E100 : SvCode n100.mem := E99.fr F fr100
  have V100 : SvSaves B n100.mem v := V99.same m100
  have g100_2 : reg n100 sp = B + 0x21A0 := by rw [u100.regs, g99_2]
  have g100_3 : reg n100 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u100.regs, g99_3]
  have g100_4 : reg n100 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u100.regs, g99_4]
  have g100_8 : reg n100 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u100.regs, g99_8]
  have g100_9 : reg n100 (9 : Fin 32) = tbp := by rw [u100.regs, g99_9]
  have g100_10 : reg n100 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u100.regs, g99_10]
  have g100_11 : reg n100 a1 = (BitVec.ofNat 8 tl95.tag).zeroExtend 32 := by rw [u100.regs, g99_11]
  have g100_12 : reg n100 a2 = BitVec.ofNat 32 0xC := by rw [u100.regs, g99_12]
  have g100_18 : reg n100 (18 : Fin 32) = out := by rw [u100.regs, g99_18]
  have g100_19 : reg n100 (19 : Fin 32) = bp := by rw [u100.regs, g99_19]
  have g100_20 : reg n100 (20 : Fin 32) = dg := by rw [u100.regs, g99_20]
  have g100_21 : reg n100 (21 : Fin 32) = rootp := by rw [u100.regs, g99_21]
  have g100_22 : reg n100 (22 : Fin 32) = ll := by rw [u100.regs, g99_22]
  have g100_23 : reg n100 (23 : Fin 32) = sgp := by rw [u100.regs, g99_23]
  have g100_24 : reg n100 (24 : Fin 32) = kp := by rw [u100.regs, g99_24]
  have g100_25 : reg n100 (25 : Fin 32) = sgl := by rw [u100.regs, g99_25]
  have g100_26 : reg n100 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u100.regs, g99_26]
  have g100_27 : reg n100 (27 : Fin 32) = tbl := by rw [u100.regs, g99_27]
  have keep_kk100 : SvKeepL B n0.mem n100.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m100]; exact keep_kk99
  clear keep_kk99
  have w100_2c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m100]; exact w99_2c
  have w100_30 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m100]; exact w99_30
  have w100_34 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m100]; exact w99_34
  have w100_38 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m100]; exact w99_38
  have w100_44 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m100]; exact w99_44
  have w100_48 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m100]; exact w99_48
  have w100_4c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m100]; exact w99_4c
  have w100_50 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m100]; exact w99_50
  have w100_54 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m100]; exact w99_54
  have w100_58 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m100]; exact w99_58
  have w100_5c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m100]; exact w99_5c
  have w100_60 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m100]; exact w99_60
  have w100_64 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m100]; exact w99_64
  have w100_68 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m100]; exact w99_68
  have w100_6c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m100]; exact w99_6c
  have w100_70 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m100]; exact w99_70
  have w100_74 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m100]; exact w99_74
  have w100_78 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m100]; exact w99_78
  have w100_7c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m100]; exact w99_7c
  have w100_80 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m100]; exact w99_80
  have w100_84 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m100]; exact w99_84
  have w100_88 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m100]; exact w99_88
  have w100_8c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m100]; exact w99_8c
  have w100_90 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m100]; exact w99_90
  have w100_94 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m100]; exact w99_94
  have w100_98 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m100]; exact w99_98
  have w100_9c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m100]; exact w99_9c
  have w100_a0 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m100]; exact w99_a0
  have w100_a4 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m100]; exact w99_a4
  have w100_150 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m100]; exact w99_150
  have w100_154 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m100]; exact w99_154
  have w100_158 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m100]; exact w99_158
  have w100_15c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m100]; exact w99_15c
  have w100_380 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m100]; exact w99_380
  have w100_384 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m100]; exact w99_384
  have w100_388 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m100]; exact w99_388
  have w100_38c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m100]; exact w99_38c
  have w100_420 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m100]; exact w99_420
  have w100_424 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m100]; exact w99_424
  have w100_428 : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m100]; exact w99_428
  have w100_42c : memLoad32 n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m100]; exact w99_42c
  have b100_430 : n100.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m100]; exact b99_430
  clear b99_430 w99_42c w99_428 w99_424 w99_420 w99_38c w99_388 w99_384 w99_380 w99_15c w99_158 w99_154 w99_150 w99_a4 w99_a0 w99_9c w99_98 w99_94 w99_90 w99_8c w99_88 w99_84 w99_80 w99_7c w99_78 w99_74 w99_70 w99_6c w99_68 w99_64 w99_60 w99_5c w99_58 w99_54 w99_50 w99_4c w99_48 w99_44 w99_38 w99_34 w99_30 w99_2c g99_12 g99_27 g99_26 g99_25 g99_24 g99_23 g99_22 g99_21 g99_20 g99_19 g99_18 g99_11 g99_10 g99_9 g99_8 g99_4 g99_3 g99_2 V99 E99 fR99 t99 fr99 rb99 s99 m99 u99 c99
  -- 0x74E: lw
  obtain ⟨n101, d101, u101⟩ := s100.lw E100.self sv_at_74e (off' := 0x752) (by decide)
    (by rw [g100_2, show B + 0x21A0 + 0x38C = B + 0x21A0 + BitVec.ofNat 32 0x38C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s101 : St n101.mem SV n101 0x752 (reg n101) := ⟨u101.pc, rfl, fun _ => rfl⟩
  have m101 : n101.mem = n100.mem := u101.mem
  have fr101 : ∀ x, SvR B x → n101.mem x = n100.mem x := fun x _ => by rw [m101]
  have t101 : Steps n0 n101 := t100.trans (.single d101)
  have fR101 : ∀ x, SvR B x → n101.mem x = M0 x := fun x hx => (fr101 x hx).trans (fR100 x hx)
  have E101 : SvCode n101.mem := E100.fr F fr101
  have V101 : SvSaves B n101.mem v := V100.same m101
  have g101_2 : reg n101 sp = B + 0x21A0 := by rw [u101.regs, upd_ne (by decide) (by decide), g100_2]
  have g101_3 : reg n101 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u101.regs, upd_ne (by decide) (by decide), g100_3]
  have g101_4 : reg n101 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u101.regs, upd_ne (by decide) (by decide), g100_4]
  have g101_8 : reg n101 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u101.regs, upd_ne (by decide) (by decide), g100_8]
  have g101_9 : reg n101 (9 : Fin 32) = tbp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_9]
  have g101_10 : reg n101 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u101.regs, upd_ne (by decide) (by decide), g100_10]
  have g101_12 : reg n101 a2 = BitVec.ofNat 32 0xC := by rw [u101.regs, upd_ne (by decide) (by decide), g100_12]
  have g101_18 : reg n101 (18 : Fin 32) = out := by rw [u101.regs, upd_ne (by decide) (by decide), g100_18]
  have g101_19 : reg n101 (19 : Fin 32) = bp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_19]
  have g101_20 : reg n101 (20 : Fin 32) = dg := by rw [u101.regs, upd_ne (by decide) (by decide), g100_20]
  have g101_21 : reg n101 (21 : Fin 32) = rootp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_21]
  have g101_22 : reg n101 (22 : Fin 32) = ll := by rw [u101.regs, upd_ne (by decide) (by decide), g100_22]
  have g101_23 : reg n101 (23 : Fin 32) = sgp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_23]
  have g101_24 : reg n101 (24 : Fin 32) = kp := by rw [u101.regs, upd_ne (by decide) (by decide), g100_24]
  have g101_25 : reg n101 (25 : Fin 32) = sgl := by rw [u101.regs, upd_ne (by decide) (by decide), g100_25]
  have g101_26 : reg n101 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u101.regs, upd_ne (by decide) (by decide), g100_26]
  have g101_27 : reg n101 (27 : Fin 32) = tbl := by rw [u101.regs, upd_ne (by decide) (by decide), g100_27]
  have g101_11 : reg n101 a1 = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by
    rw [u101.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g100_2, show B + 0x21A0 + 0x38C = B + 0x21A0 + BitVec.ofNat 32 0x38C by sv_addr, w100_38c]
  have keep_kk101 : SvKeepL B n0.mem n101.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m101]; exact keep_kk100
  clear keep_kk100
  have w101_2c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m101]; exact w100_2c
  have w101_30 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m101]; exact w100_30
  have w101_34 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m101]; exact w100_34
  have w101_38 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m101]; exact w100_38
  have w101_44 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m101]; exact w100_44
  have w101_48 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m101]; exact w100_48
  have w101_4c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m101]; exact w100_4c
  have w101_50 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m101]; exact w100_50
  have w101_54 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m101]; exact w100_54
  have w101_58 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m101]; exact w100_58
  have w101_5c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m101]; exact w100_5c
  have w101_60 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m101]; exact w100_60
  have w101_64 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m101]; exact w100_64
  have w101_68 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m101]; exact w100_68
  have w101_6c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m101]; exact w100_6c
  have w101_70 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m101]; exact w100_70
  have w101_74 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m101]; exact w100_74
  have w101_78 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m101]; exact w100_78
  have w101_7c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m101]; exact w100_7c
  have w101_80 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m101]; exact w100_80
  have w101_84 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m101]; exact w100_84
  have w101_88 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m101]; exact w100_88
  have w101_8c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m101]; exact w100_8c
  have w101_90 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m101]; exact w100_90
  have w101_94 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m101]; exact w100_94
  have w101_98 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m101]; exact w100_98
  have w101_9c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m101]; exact w100_9c
  have w101_a0 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m101]; exact w100_a0
  have w101_a4 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m101]; exact w100_a4
  have w101_150 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m101]; exact w100_150
  have w101_154 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m101]; exact w100_154
  have w101_158 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m101]; exact w100_158
  have w101_15c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m101]; exact w100_15c
  have w101_380 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m101]; exact w100_380
  have w101_384 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m101]; exact w100_384
  have w101_388 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m101]; exact w100_388
  have w101_38c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m101]; exact w100_38c
  have w101_420 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m101]; exact w100_420
  have w101_424 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m101]; exact w100_424
  have w101_428 : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m101]; exact w100_428
  have w101_42c : memLoad32 n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m101]; exact w100_42c
  have b101_430 : n101.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m101]; exact b100_430
  clear b100_430 w100_42c w100_428 w100_424 w100_420 w100_38c w100_388 w100_384 w100_380 w100_15c w100_158 w100_154 w100_150 w100_a4 w100_a0 w100_9c w100_98 w100_94 w100_90 w100_8c w100_88 w100_84 w100_80 w100_7c w100_78 w100_74 w100_70 w100_6c w100_68 w100_64 w100_60 w100_5c w100_58 w100_54 w100_50 w100_4c w100_48 w100_44 w100_38 w100_34 w100_30 w100_2c g100_27 g100_26 g100_25 g100_24 g100_23 g100_22 g100_21 g100_20 g100_19 g100_18 g100_12 g100_11 g100_10 g100_9 g100_8 g100_4 g100_3 g100_2 V100 E100 fR100 t100 fr100 m100 s100 u100 d100
  by_cases hz_101 : (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) = 0
  rotate_left
  · -- 0x752: branch, taken
    obtain ⟨n102, d102, u102⟩ := s101.taken E101.self 0x940 sv_at_752
      (by decide) (by rw [g101_11, s101.zero]; exact br_bne_t hz_101)
    have s102 : St n102.mem SV n102 0x940 (reg n102) := ⟨u102.pc, rfl, fun _ => rfl⟩
    have m102 : n102.mem = n101.mem := u102.mem
    have fr102 : ∀ x, SvR B x → n102.mem x = n101.mem x := fun x _ => by rw [m102]
    have t102 : Steps n0 n102 := t101.trans (.single d102)
    have fR102 : ∀ x, SvR B x → n102.mem x = M0 x := fun x hx => (fr102 x hx).trans (fR101 x hx)
    have E102 : SvCode n102.mem := E101.fr F fr102
    have V102 : SvSaves B n102.mem v := V101.same m102
    have g102_2 : reg n102 sp = B + 0x21A0 := by rw [u102.regs, g101_2]
    have g102_3 : reg n102 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u102.regs, g101_3]
    have g102_4 : reg n102 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u102.regs, g101_4]
    have g102_8 : reg n102 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u102.regs, g101_8]
    have g102_9 : reg n102 (9 : Fin 32) = tbp := by rw [u102.regs, g101_9]
    have g102_10 : reg n102 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u102.regs, g101_10]
    have g102_11 : reg n102 a1 = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [u102.regs, g101_11]
    have g102_12 : reg n102 a2 = BitVec.ofNat 32 0xC := by rw [u102.regs, g101_12]
    have g102_18 : reg n102 (18 : Fin 32) = out := by rw [u102.regs, g101_18]
    have g102_19 : reg n102 (19 : Fin 32) = bp := by rw [u102.regs, g101_19]
    have g102_20 : reg n102 (20 : Fin 32) = dg := by rw [u102.regs, g101_20]
    have g102_21 : reg n102 (21 : Fin 32) = rootp := by rw [u102.regs, g101_21]
    have g102_22 : reg n102 (22 : Fin 32) = ll := by rw [u102.regs, g101_22]
    have g102_23 : reg n102 (23 : Fin 32) = sgp := by rw [u102.regs, g101_23]
    have g102_24 : reg n102 (24 : Fin 32) = kp := by rw [u102.regs, g101_24]
    have g102_25 : reg n102 (25 : Fin 32) = sgl := by rw [u102.regs, g101_25]
    have g102_26 : reg n102 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u102.regs, g101_26]
    have g102_27 : reg n102 (27 : Fin 32) = tbl := by rw [u102.regs, g101_27]
    have keep_kk102 : SvKeepL B n0.mem n102.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m102]; exact keep_kk101
    clear keep_kk101
    have w102_2c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m102]; exact w101_2c
    have w102_30 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m102]; exact w101_30
    have w102_34 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m102]; exact w101_34
    have w102_38 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m102]; exact w101_38
    have w102_44 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m102]; exact w101_44
    have w102_48 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m102]; exact w101_48
    have w102_4c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m102]; exact w101_4c
    have w102_50 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m102]; exact w101_50
    have w102_54 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m102]; exact w101_54
    have w102_58 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m102]; exact w101_58
    have w102_5c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m102]; exact w101_5c
    have w102_60 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m102]; exact w101_60
    have w102_64 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m102]; exact w101_64
    have w102_68 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m102]; exact w101_68
    have w102_6c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m102]; exact w101_6c
    have w102_70 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m102]; exact w101_70
    have w102_74 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m102]; exact w101_74
    have w102_78 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m102]; exact w101_78
    have w102_7c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m102]; exact w101_7c
    have w102_80 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m102]; exact w101_80
    have w102_84 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m102]; exact w101_84
    have w102_88 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m102]; exact w101_88
    have w102_8c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m102]; exact w101_8c
    have w102_90 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m102]; exact w101_90
    have w102_94 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m102]; exact w101_94
    have w102_98 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m102]; exact w101_98
    have w102_9c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m102]; exact w101_9c
    have w102_a0 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m102]; exact w101_a0
    have w102_a4 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m102]; exact w101_a4
    have w102_150 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m102]; exact w101_150
    have w102_154 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m102]; exact w101_154
    have w102_158 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m102]; exact w101_158
    have w102_15c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m102]; exact w101_15c
    have w102_380 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m102]; exact w101_380
    have w102_384 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m102]; exact w101_384
    have w102_388 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m102]; exact w101_388
    have w102_38c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m102]; exact w101_38c
    have w102_420 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m102]; exact w101_420
    have w102_424 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m102]; exact w101_424
    have w102_428 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m102]; exact w101_428
    have w102_42c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m102]; exact w101_42c
    have b102_430 : n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m102]; exact b101_430
    clear b101_430 w101_42c w101_428 w101_424 w101_420 w101_38c w101_388 w101_384 w101_380 w101_15c w101_158 w101_154 w101_150 w101_a4 w101_a0 w101_9c w101_98 w101_94 w101_90 w101_8c w101_88 w101_84 w101_80 w101_7c w101_78 w101_74 w101_70 w101_6c w101_68 w101_64 w101_60 w101_5c w101_58 w101_54 w101_50 w101_4c w101_48 w101_44 w101_38 w101_34 w101_30 w101_2c g101_11 g101_27 g101_26 g101_25 g101_24 g101_23 g101_22 g101_21 g101_20 g101_19 g101_18 g101_12 g101_10 g101_9 g101_8 g101_4 g101_3 g101_2 V101 E101 fR101 t101 fr101 m101 s101 u101 d101
    -- 0x940
    obtain ⟨n103, c103, u103⟩ := s102.block svDp4940 E102.self svDp4940_end
      ⟨trivial, trivial⟩
    have m103 : n103.mem = n102.mem := u103.mem
    have s103 : St n103.mem SV n103 0x942 (reg n103) := ⟨u103.pc, rfl, fun _ => rfl⟩
    have rb103 : ∀ q, reg n103 q = (runBlock svDp4940 (n102.mem, reg n102)).2 q := fun q => by rw [u103.regs]
    have fr103 : ∀ x, SvR B x → n103.mem x = n102.mem x := fun x _ => by rw [m103]
    have t103 : Steps n0 n103 := t102.trans c103
    have fR103 : ∀ x, SvR B x → n103.mem x = M0 x := fun x hx => (fr103 x hx).trans (fR102 x hx)
    have E103 : SvCode n103.mem := E102.fr F fr103
    have V103 : SvSaves B n103.mem v := V102.same m103
    have g103_2 : reg n103 sp = B + 0x21A0 := by
      rw [rb103, runBlock_reg _ _ _ sp s102.zero (by decide), g102_2]
    have g103_3 : reg n103 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb103, runBlock_reg _ _ _ (3 : Fin 32) s102.zero (by decide), g102_3]
    have g103_4 : reg n103 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb103, runBlock_reg _ _ _ (4 : Fin 32) s102.zero (by decide), g102_4]
    have g103_8 : reg n103 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb103, runBlock_reg _ _ _ (8 : Fin 32) s102.zero (by decide), g102_8]
    have g103_9 : reg n103 (9 : Fin 32) = tbp := by
      rw [rb103, runBlock_reg _ _ _ (9 : Fin 32) s102.zero (by decide), g102_9]
    have g103_11 : reg n103 a1 = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by
      rw [rb103, runBlock_reg _ _ _ a1 s102.zero (by decide), g102_11]
    have g103_12 : reg n103 a2 = BitVec.ofNat 32 0xC := by
      rw [rb103, runBlock_reg _ _ _ a2 s102.zero (by decide), g102_12]
    have g103_18 : reg n103 (18 : Fin 32) = out := by
      rw [rb103, runBlock_reg _ _ _ (18 : Fin 32) s102.zero (by decide), g102_18]
    have g103_19 : reg n103 (19 : Fin 32) = bp := by
      rw [rb103, runBlock_reg _ _ _ (19 : Fin 32) s102.zero (by decide), g102_19]
    have g103_20 : reg n103 (20 : Fin 32) = dg := by
      rw [rb103, runBlock_reg _ _ _ (20 : Fin 32) s102.zero (by decide), g102_20]
    have g103_21 : reg n103 (21 : Fin 32) = rootp := by
      rw [rb103, runBlock_reg _ _ _ (21 : Fin 32) s102.zero (by decide), g102_21]
    have g103_22 : reg n103 (22 : Fin 32) = ll := by
      rw [rb103, runBlock_reg _ _ _ (22 : Fin 32) s102.zero (by decide), g102_22]
    have g103_23 : reg n103 (23 : Fin 32) = sgp := by
      rw [rb103, runBlock_reg _ _ _ (23 : Fin 32) s102.zero (by decide), g102_23]
    have g103_24 : reg n103 (24 : Fin 32) = kp := by
      rw [rb103, runBlock_reg _ _ _ (24 : Fin 32) s102.zero (by decide), g102_24]
    have g103_25 : reg n103 (25 : Fin 32) = sgl := by
      rw [rb103, runBlock_reg _ _ _ (25 : Fin 32) s102.zero (by decide), g102_25]
    have g103_26 : reg n103 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by
      rw [rb103, runBlock_reg _ _ _ (26 : Fin 32) s102.zero (by decide), g102_26]
    have g103_27 : reg n103 (27 : Fin 32) = tbl := by
      rw [rb103, runBlock_reg _ _ _ (27 : Fin 32) s102.zero (by decide), g102_27]
    have g103_10 : reg n103 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb103]; simp +decide only [runBlock, BInstr.run, svDp4940, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g102_2, g102_3, g102_4, g102_8, g102_9, g102_10, g102_11, g102_12, g102_18, g102_19, g102_20, g102_21, g102_22, g102_23, g102_24, g102_25, g102_26, g102_27, s102.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk103 : SvKeepL B n0.mem n103.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m103]; exact keep_kk102
    clear keep_kk102
    have w103_2c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m103]; exact w102_2c
    have w103_30 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m103]; exact w102_30
    have w103_34 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m103]; exact w102_34
    have w103_38 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m103]; exact w102_38
    have w103_44 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m103]; exact w102_44
    have w103_48 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m103]; exact w102_48
    have w103_4c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m103]; exact w102_4c
    have w103_50 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m103]; exact w102_50
    have w103_54 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m103]; exact w102_54
    have w103_58 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m103]; exact w102_58
    have w103_5c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m103]; exact w102_5c
    have w103_60 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m103]; exact w102_60
    have w103_64 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m103]; exact w102_64
    have w103_68 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m103]; exact w102_68
    have w103_6c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m103]; exact w102_6c
    have w103_70 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m103]; exact w102_70
    have w103_74 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m103]; exact w102_74
    have w103_78 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m103]; exact w102_78
    have w103_7c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m103]; exact w102_7c
    have w103_80 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m103]; exact w102_80
    have w103_84 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m103]; exact w102_84
    have w103_88 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m103]; exact w102_88
    have w103_8c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m103]; exact w102_8c
    have w103_90 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m103]; exact w102_90
    have w103_94 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m103]; exact w102_94
    have w103_98 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m103]; exact w102_98
    have w103_9c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m103]; exact w102_9c
    have w103_a0 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m103]; exact w102_a0
    have w103_a4 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m103]; exact w102_a4
    have w103_150 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m103]; exact w102_150
    have w103_154 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m103]; exact w102_154
    have w103_158 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m103]; exact w102_158
    have w103_15c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m103]; exact w102_15c
    have w103_380 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m103]; exact w102_380
    have w103_384 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m103]; exact w102_384
    have w103_388 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m103]; exact w102_388
    have w103_38c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m103]; exact w102_38c
    have w103_420 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m103]; exact w102_420
    have w103_424 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m103]; exact w102_424
    have w103_428 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m103]; exact w102_428
    have w103_42c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m103]; exact w102_42c
    have b103_430 : n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m103]; exact b102_430
    clear b102_430 w102_42c w102_428 w102_424 w102_420 w102_38c w102_388 w102_384 w102_380 w102_15c w102_158 w102_154 w102_150 w102_a4 w102_a0 w102_9c w102_98 w102_94 w102_90 w102_8c w102_88 w102_84 w102_80 w102_7c w102_78 w102_74 w102_70 w102_6c w102_68 w102_64 w102_60 w102_5c w102_58 w102_54 w102_50 w102_4c w102_48 w102_44 w102_38 w102_34 w102_30 w102_2c g102_27 g102_26 g102_25 g102_24 g102_23 g102_22 g102_21 g102_20 g102_19 g102_18 g102_12 g102_11 g102_10 g102_9 g102_8 g102_4 g102_3 g102_2 V102 E102 fR102 t102 fr102 m102 s102 u102 d102
    -- 0x942: sw
    obtain ⟨n104, d104, s104, fr104, K104, W104, rg104⟩ := sv_sw F E103 s103 sv_at_942 (off' := 0x944) (c := 0x44)
      (by decide) (by rw [g103_2]; sv_addr) (by decide) (by decide)
    have t104 : Steps n0 n104 := t103.trans d104
    have fR104 : ∀ x, SvR B x → n104.mem x = M0 x := fun x hx => (fr104 x hx).trans (fR103 x hx)
    have E104 : SvCode n104.mem := E103.fr F fr104
    have V104 : SvSaves B n104.mem v := V103.keep K104 (by decide)
    have g104_2 : reg n104 sp = B + 0x21A0 := by rw [rg104 sp, g103_2]
    have g104_3 : reg n104 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg104 (3 : Fin 32), g103_3]
    have g104_4 : reg n104 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg104 (4 : Fin 32), g103_4]
    have g104_8 : reg n104 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg104 (8 : Fin 32), g103_8]
    have g104_9 : reg n104 (9 : Fin 32) = tbp := by rw [rg104 (9 : Fin 32), g103_9]
    have g104_10 : reg n104 a0 = BitVec.ofNat 32 0x1 := by rw [rg104 a0, g103_10]
    have g104_11 : reg n104 a1 = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [rg104 a1, g103_11]
    have g104_12 : reg n104 a2 = BitVec.ofNat 32 0xC := by rw [rg104 a2, g103_12]
    have g104_18 : reg n104 (18 : Fin 32) = out := by rw [rg104 (18 : Fin 32), g103_18]
    have g104_19 : reg n104 (19 : Fin 32) = bp := by rw [rg104 (19 : Fin 32), g103_19]
    have g104_20 : reg n104 (20 : Fin 32) = dg := by rw [rg104 (20 : Fin 32), g103_20]
    have g104_21 : reg n104 (21 : Fin 32) = rootp := by rw [rg104 (21 : Fin 32), g103_21]
    have g104_22 : reg n104 (22 : Fin 32) = ll := by rw [rg104 (22 : Fin 32), g103_22]
    have g104_23 : reg n104 (23 : Fin 32) = sgp := by rw [rg104 (23 : Fin 32), g103_23]
    have g104_24 : reg n104 (24 : Fin 32) = kp := by rw [rg104 (24 : Fin 32), g103_24]
    have g104_25 : reg n104 (25 : Fin 32) = sgl := by rw [rg104 (25 : Fin 32), g103_25]
    have g104_26 : reg n104 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [rg104 (26 : Fin 32), g103_26]
    have g104_27 : reg n104 (27 : Fin 32) = tbl := by rw [rg104 (27 : Fin 32), g103_27]
    have keep_kk104 : SvKeepL B n0.mem n104.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := keep_kk103.trans K104.toL
    clear keep_kk103
    have w104_2c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K104.w32 (by decide) (by decide)).trans w103_2c
    have w104_30 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K104.w32 (by decide) (by decide)).trans w103_30
    have w104_34 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K104.w32 (by decide) (by decide)).trans w103_34
    have w104_38 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K104.w32 (by decide) (by decide)).trans w103_38
    have w104_48 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K104.w32 (by decide) (by decide)).trans w103_48
    have w104_4c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K104.w32 (by decide) (by decide)).trans w103_4c
    have w104_50 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K104.w32 (by decide) (by decide)).trans w103_50
    have w104_54 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K104.w32 (by decide) (by decide)).trans w103_54
    have w104_58 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K104.w32 (by decide) (by decide)).trans w103_58
    have w104_5c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K104.w32 (by decide) (by decide)).trans w103_5c
    have w104_60 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K104.w32 (by decide) (by decide)).trans w103_60
    have w104_64 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K104.w32 (by decide) (by decide)).trans w103_64
    have w104_68 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K104.w32 (by decide) (by decide)).trans w103_68
    have w104_6c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K104.w32 (by decide) (by decide)).trans w103_6c
    have w104_70 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K104.w32 (by decide) (by decide)).trans w103_70
    have w104_74 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K104.w32 (by decide) (by decide)).trans w103_74
    have w104_78 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K104.w32 (by decide) (by decide)).trans w103_78
    have w104_7c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K104.w32 (by decide) (by decide)).trans w103_7c
    have w104_80 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K104.w32 (by decide) (by decide)).trans w103_80
    have w104_84 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K104.w32 (by decide) (by decide)).trans w103_84
    have w104_88 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K104.w32 (by decide) (by decide)).trans w103_88
    have w104_8c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K104.w32 (by decide) (by decide)).trans w103_8c
    have w104_90 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K104.w32 (by decide) (by decide)).trans w103_90
    have w104_94 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K104.w32 (by decide) (by decide)).trans w103_94
    have w104_98 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K104.w32 (by decide) (by decide)).trans w103_98
    have w104_9c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K104.w32 (by decide) (by decide)).trans w103_9c
    have w104_a0 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := (K104.w32 (by decide) (by decide)).trans w103_a0
    have w104_a4 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K104.w32 (by decide) (by decide)).trans w103_a4
    have w104_150 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K104.w32 (by decide) (by decide)).trans w103_150
    have w104_154 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K104.w32 (by decide) (by decide)).trans w103_154
    have w104_158 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K104.w32 (by decide) (by decide)).trans w103_158
    have w104_15c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K104.w32 (by decide) (by decide)).trans w103_15c
    have w104_380 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K104.w32 (by decide) (by decide)).trans w103_380
    have w104_384 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K104.w32 (by decide) (by decide)).trans w103_384
    have w104_388 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := (K104.w32 (by decide) (by decide)).trans w103_388
    have w104_38c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := (K104.w32 (by decide) (by decide)).trans w103_38c
    have w104_420 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := (K104.w32 (by decide) (by decide)).trans w103_420
    have w104_424 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := (K104.w32 (by decide) (by decide)).trans w103_424
    have w104_428 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K104.w32 (by decide) (by decide)).trans w103_428
    have w104_42c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := (K104.w32 (by decide) (by decide)).trans w103_42c
    have b104_430 : n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := (K104.b8 (by decide) (by decide)).trans b103_430
    have w104_44 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [W104, g103_10]
    clear b103_430 w103_42c w103_428 w103_424 w103_420 w103_38c w103_388 w103_384 w103_380 w103_15c w103_158 w103_154 w103_150 w103_a4 w103_a0 w103_9c w103_98 w103_94 w103_90 w103_8c w103_88 w103_84 w103_80 w103_7c w103_78 w103_74 w103_70 w103_6c w103_68 w103_64 w103_60 w103_5c w103_58 w103_54 w103_50 w103_4c w103_48 w103_44 w103_38 w103_34 w103_30 w103_2c g103_10 g103_27 g103_26 g103_25 g103_24 g103_23 g103_22 g103_21 g103_20 g103_19 g103_18 g103_12 g103_11 g103_9 g103_8 g103_4 g103_3 g103_2 V103 E103 fR103 t103 fr103 rb103 s103 m103 u103 c103
    -- 0x944: lw
    obtain ⟨n105, d105, u105⟩ := s104.lw E104.self sv_at_944 (off' := 0x946) (by decide)
      (by rw [g104_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s105 : St n105.mem SV n105 0x946 (reg n105) := ⟨u105.pc, rfl, fun _ => rfl⟩
    have m105 : n105.mem = n104.mem := u105.mem
    have fr105 : ∀ x, SvR B x → n105.mem x = n104.mem x := fun x _ => by rw [m105]
    have t105 : Steps n0 n105 := t104.trans (.single d105)
    have fR105 : ∀ x, SvR B x → n105.mem x = M0 x := fun x hx => (fr105 x hx).trans (fR104 x hx)
    have E105 : SvCode n105.mem := E104.fr F fr105
    have V105 : SvSaves B n105.mem v := V104.same m105
    have g105_2 : reg n105 sp = B + 0x21A0 := by rw [u105.regs, upd_ne (by decide) (by decide), g104_2]
    have g105_3 : reg n105 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u105.regs, upd_ne (by decide) (by decide), g104_3]
    have g105_4 : reg n105 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u105.regs, upd_ne (by decide) (by decide), g104_4]
    have g105_9 : reg n105 (9 : Fin 32) = tbp := by rw [u105.regs, upd_ne (by decide) (by decide), g104_9]
    have g105_10 : reg n105 a0 = BitVec.ofNat 32 0x1 := by rw [u105.regs, upd_ne (by decide) (by decide), g104_10]
    have g105_11 : reg n105 a1 = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [u105.regs, upd_ne (by decide) (by decide), g104_11]
    have g105_12 : reg n105 a2 = BitVec.ofNat 32 0xC := by rw [u105.regs, upd_ne (by decide) (by decide), g104_12]
    have g105_18 : reg n105 (18 : Fin 32) = out := by rw [u105.regs, upd_ne (by decide) (by decide), g104_18]
    have g105_19 : reg n105 (19 : Fin 32) = bp := by rw [u105.regs, upd_ne (by decide) (by decide), g104_19]
    have g105_20 : reg n105 (20 : Fin 32) = dg := by rw [u105.regs, upd_ne (by decide) (by decide), g104_20]
    have g105_21 : reg n105 (21 : Fin 32) = rootp := by rw [u105.regs, upd_ne (by decide) (by decide), g104_21]
    have g105_22 : reg n105 (22 : Fin 32) = ll := by rw [u105.regs, upd_ne (by decide) (by decide), g104_22]
    have g105_23 : reg n105 (23 : Fin 32) = sgp := by rw [u105.regs, upd_ne (by decide) (by decide), g104_23]
    have g105_24 : reg n105 (24 : Fin 32) = kp := by rw [u105.regs, upd_ne (by decide) (by decide), g104_24]
    have g105_25 : reg n105 (25 : Fin 32) = sgl := by rw [u105.regs, upd_ne (by decide) (by decide), g104_25]
    have g105_26 : reg n105 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u105.regs, upd_ne (by decide) (by decide), g104_26]
    have g105_27 : reg n105 (27 : Fin 32) = tbl := by rw [u105.regs, upd_ne (by decide) (by decide), g104_27]
    have g105_8 : reg n105 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [u105.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g104_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w104_44]
    have keep_kk105 : SvKeepL B n0.mem n105.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m105]; exact keep_kk104
    clear keep_kk104
    have w105_2c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m105]; exact w104_2c
    have w105_30 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m105]; exact w104_30
    have w105_34 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m105]; exact w104_34
    have w105_38 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m105]; exact w104_38
    have w105_44 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m105]; exact w104_44
    have w105_48 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m105]; exact w104_48
    have w105_4c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m105]; exact w104_4c
    have w105_50 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m105]; exact w104_50
    have w105_54 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m105]; exact w104_54
    have w105_58 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m105]; exact w104_58
    have w105_5c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m105]; exact w104_5c
    have w105_60 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m105]; exact w104_60
    have w105_64 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m105]; exact w104_64
    have w105_68 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m105]; exact w104_68
    have w105_6c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m105]; exact w104_6c
    have w105_70 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m105]; exact w104_70
    have w105_74 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m105]; exact w104_74
    have w105_78 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m105]; exact w104_78
    have w105_7c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m105]; exact w104_7c
    have w105_80 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m105]; exact w104_80
    have w105_84 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m105]; exact w104_84
    have w105_88 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m105]; exact w104_88
    have w105_8c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m105]; exact w104_8c
    have w105_90 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m105]; exact w104_90
    have w105_94 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m105]; exact w104_94
    have w105_98 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m105]; exact w104_98
    have w105_9c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m105]; exact w104_9c
    have w105_a0 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m105]; exact w104_a0
    have w105_a4 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m105]; exact w104_a4
    have w105_150 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m105]; exact w104_150
    have w105_154 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m105]; exact w104_154
    have w105_158 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m105]; exact w104_158
    have w105_15c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m105]; exact w104_15c
    have w105_380 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m105]; exact w104_380
    have w105_384 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m105]; exact w104_384
    have w105_388 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m105]; exact w104_388
    have w105_38c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m105]; exact w104_38c
    have w105_420 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m105]; exact w104_420
    have w105_424 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m105]; exact w104_424
    have w105_428 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m105]; exact w104_428
    have w105_42c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m105]; exact w104_42c
    have b105_430 : n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m105]; exact b104_430
    clear w104_44 b104_430 w104_42c w104_428 w104_424 w104_420 w104_38c w104_388 w104_384 w104_380 w104_15c w104_158 w104_154 w104_150 w104_a4 w104_a0 w104_9c w104_98 w104_94 w104_90 w104_8c w104_88 w104_84 w104_80 w104_7c w104_78 w104_74 w104_70 w104_6c w104_68 w104_64 w104_60 w104_5c w104_58 w104_54 w104_50 w104_4c w104_48 w104_38 w104_34 w104_30 w104_2c g104_27 g104_26 g104_25 g104_24 g104_23 g104_22 g104_21 g104_20 g104_19 g104_18 g104_12 g104_11 g104_10 g104_9 g104_8 g104_4 g104_3 g104_2 V104 E104 fR104 t104 rg104 W104 K104 fr104 s104 d104
    -- 0x946: j
    obtain ⟨n106, d106, u106⟩ := s105.jump E105.self sv_at_946 (off' := 0x7A4) (by decide)
      (by rw [s105.pc]; decide)
    have s106 : St n106.mem SV n106 0x7A4 (reg n106) := ⟨u106.pc, rfl, fun _ => rfl⟩
    have m106 : n106.mem = n105.mem := u106.mem
    have fr106 : ∀ x, SvR B x → n106.mem x = n105.mem x := fun x _ => by rw [m106]
    have t106 : Steps n0 n106 := t105.trans (.single d106)
    have fR106 : ∀ x, SvR B x → n106.mem x = M0 x := fun x hx => (fr106 x hx).trans (fR105 x hx)
    have E106 : SvCode n106.mem := E105.fr F fr106
    have V106 : SvSaves B n106.mem v := V105.same m106
    have g106_2 : reg n106 sp = B + 0x21A0 := by rw [u106.regs, g105_2]
    have g106_3 : reg n106 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u106.regs, g105_3]
    have g106_4 : reg n106 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u106.regs, g105_4]
    have g106_8 : reg n106 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u106.regs, g105_8]
    have g106_9 : reg n106 (9 : Fin 32) = tbp := by rw [u106.regs, g105_9]
    have g106_10 : reg n106 a0 = BitVec.ofNat 32 0x1 := by rw [u106.regs, g105_10]
    have g106_11 : reg n106 a1 = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [u106.regs, g105_11]
    have g106_12 : reg n106 a2 = BitVec.ofNat 32 0xC := by rw [u106.regs, g105_12]
    have g106_18 : reg n106 (18 : Fin 32) = out := by rw [u106.regs, g105_18]
    have g106_19 : reg n106 (19 : Fin 32) = bp := by rw [u106.regs, g105_19]
    have g106_20 : reg n106 (20 : Fin 32) = dg := by rw [u106.regs, g105_20]
    have g106_21 : reg n106 (21 : Fin 32) = rootp := by rw [u106.regs, g105_21]
    have g106_22 : reg n106 (22 : Fin 32) = ll := by rw [u106.regs, g105_22]
    have g106_23 : reg n106 (23 : Fin 32) = sgp := by rw [u106.regs, g105_23]
    have g106_24 : reg n106 (24 : Fin 32) = kp := by rw [u106.regs, g105_24]
    have g106_25 : reg n106 (25 : Fin 32) = sgl := by rw [u106.regs, g105_25]
    have g106_26 : reg n106 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u106.regs, g105_26]
    have g106_27 : reg n106 (27 : Fin 32) = tbl := by rw [u106.regs, g105_27]
    have keep_kk106 : SvKeepL B n0.mem n106.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x44, 0x4)] := by rw [m106]; exact keep_kk105
    clear keep_kk105
    have w106_2c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m106]; exact w105_2c
    have w106_30 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m106]; exact w105_30
    have w106_34 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m106]; exact w105_34
    have w106_38 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m106]; exact w105_38
    have w106_44 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m106]; exact w105_44
    have w106_48 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m106]; exact w105_48
    have w106_4c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m106]; exact w105_4c
    have w106_50 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m106]; exact w105_50
    have w106_54 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m106]; exact w105_54
    have w106_58 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m106]; exact w105_58
    have w106_5c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m106]; exact w105_5c
    have w106_60 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m106]; exact w105_60
    have w106_64 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m106]; exact w105_64
    have w106_68 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m106]; exact w105_68
    have w106_6c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m106]; exact w105_6c
    have w106_70 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m106]; exact w105_70
    have w106_74 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m106]; exact w105_74
    have w106_78 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m106]; exact w105_78
    have w106_7c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m106]; exact w105_7c
    have w106_80 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m106]; exact w105_80
    have w106_84 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m106]; exact w105_84
    have w106_88 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m106]; exact w105_88
    have w106_8c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m106]; exact w105_8c
    have w106_90 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m106]; exact w105_90
    have w106_94 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m106]; exact w105_94
    have w106_98 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m106]; exact w105_98
    have w106_9c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m106]; exact w105_9c
    have w106_a0 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m106]; exact w105_a0
    have w106_a4 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m106]; exact w105_a4
    have w106_150 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m106]; exact w105_150
    have w106_154 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m106]; exact w105_154
    have w106_158 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m106]; exact w105_158
    have w106_15c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m106]; exact w105_15c
    have w106_380 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m106]; exact w105_380
    have w106_384 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m106]; exact w105_384
    have w106_388 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m106]; exact w105_388
    have w106_38c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m106]; exact w105_38c
    have w106_420 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m106]; exact w105_420
    have w106_424 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m106]; exact w105_424
    have w106_428 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m106]; exact w105_428
    have w106_42c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m106]; exact w105_42c
    have b106_430 : n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m106]; exact b105_430
    clear b105_430 w105_42c w105_428 w105_424 w105_420 w105_38c w105_388 w105_384 w105_380 w105_15c w105_158 w105_154 w105_150 w105_a4 w105_a0 w105_9c w105_98 w105_94 w105_90 w105_8c w105_88 w105_84 w105_80 w105_7c w105_78 w105_74 w105_70 w105_6c w105_68 w105_64 w105_60 w105_5c w105_58 w105_54 w105_50 w105_4c w105_48 w105_44 w105_38 w105_34 w105_30 w105_2c g105_8 g105_27 g105_26 g105_25 g105_24 g105_23 g105_22 g105_21 g105_20 g105_19 g105_18 g105_12 g105_11 g105_10 g105_9 g105_4 g105_3 g105_2 V105 E105 fR105 t105 fr105 m105 s105 u105 d105
    exact .inl ⟨(fun ⟨tl95', h0', h1', h2', _⟩ => by rw [hr95] at h0'; cases h0'; exact hz_101 h2'), sv_fail F E106 s106 t106 (fun x hx => (fR106 x hx).trans (fM x hx).symm) V106 hret g106_2 g106_18 hO g106_3 g106_4 (by rw [g106_8]; sv_code)⟩
  -- 0x752: branch, not taken
  obtain ⟨n102, d102, u102⟩ := s101.notTaken E101.self 0x756 sv_at_752
    (by decide) (by rw [g101_11, s101.zero]; exact br_bne_f hz_101)
  have s102 : St n102.mem SV n102 0x756 (reg n102) := ⟨u102.pc, rfl, fun _ => rfl⟩
  have m102 : n102.mem = n101.mem := u102.mem
  have fr102 : ∀ x, SvR B x → n102.mem x = n101.mem x := fun x _ => by rw [m102]
  have t102 : Steps n0 n102 := t101.trans (.single d102)
  have fR102 : ∀ x, SvR B x → n102.mem x = M0 x := fun x hx => (fr102 x hx).trans (fR101 x hx)
  have E102 : SvCode n102.mem := E101.fr F fr102
  have V102 : SvSaves B n102.mem v := V101.same m102
  have g102_2 : reg n102 sp = B + 0x21A0 := by rw [u102.regs, g101_2]
  have g102_3 : reg n102 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u102.regs, g101_3]
  have g102_4 : reg n102 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u102.regs, g101_4]
  have g102_8 : reg n102 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u102.regs, g101_8]
  have g102_9 : reg n102 (9 : Fin 32) = tbp := by rw [u102.regs, g101_9]
  have g102_10 : reg n102 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u102.regs, g101_10]
  have g102_11 : reg n102 a1 = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [u102.regs, g101_11]
  have g102_12 : reg n102 a2 = BitVec.ofNat 32 0xC := by rw [u102.regs, g101_12]
  have g102_18 : reg n102 (18 : Fin 32) = out := by rw [u102.regs, g101_18]
  have g102_19 : reg n102 (19 : Fin 32) = bp := by rw [u102.regs, g101_19]
  have g102_20 : reg n102 (20 : Fin 32) = dg := by rw [u102.regs, g101_20]
  have g102_21 : reg n102 (21 : Fin 32) = rootp := by rw [u102.regs, g101_21]
  have g102_22 : reg n102 (22 : Fin 32) = ll := by rw [u102.regs, g101_22]
  have g102_23 : reg n102 (23 : Fin 32) = sgp := by rw [u102.regs, g101_23]
  have g102_24 : reg n102 (24 : Fin 32) = kp := by rw [u102.regs, g101_24]
  have g102_25 : reg n102 (25 : Fin 32) = sgl := by rw [u102.regs, g101_25]
  have g102_26 : reg n102 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u102.regs, g101_26]
  have g102_27 : reg n102 (27 : Fin 32) = tbl := by rw [u102.regs, g101_27]
  have keep_kk102 : SvKeepL B n0.mem n102.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m102]; exact keep_kk101
  clear keep_kk101
  have w102_2c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m102]; exact w101_2c
  have w102_30 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m102]; exact w101_30
  have w102_34 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m102]; exact w101_34
  have w102_38 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m102]; exact w101_38
  have w102_44 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m102]; exact w101_44
  have w102_48 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m102]; exact w101_48
  have w102_4c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m102]; exact w101_4c
  have w102_50 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m102]; exact w101_50
  have w102_54 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m102]; exact w101_54
  have w102_58 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m102]; exact w101_58
  have w102_5c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m102]; exact w101_5c
  have w102_60 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m102]; exact w101_60
  have w102_64 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m102]; exact w101_64
  have w102_68 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m102]; exact w101_68
  have w102_6c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m102]; exact w101_6c
  have w102_70 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m102]; exact w101_70
  have w102_74 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m102]; exact w101_74
  have w102_78 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m102]; exact w101_78
  have w102_7c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m102]; exact w101_7c
  have w102_80 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m102]; exact w101_80
  have w102_84 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m102]; exact w101_84
  have w102_88 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m102]; exact w101_88
  have w102_8c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m102]; exact w101_8c
  have w102_90 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m102]; exact w101_90
  have w102_94 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m102]; exact w101_94
  have w102_98 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m102]; exact w101_98
  have w102_9c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m102]; exact w101_9c
  have w102_a0 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m102]; exact w101_a0
  have w102_a4 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m102]; exact w101_a4
  have w102_150 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m102]; exact w101_150
  have w102_154 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m102]; exact w101_154
  have w102_158 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m102]; exact w101_158
  have w102_15c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m102]; exact w101_15c
  have w102_380 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m102]; exact w101_380
  have w102_384 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m102]; exact w101_384
  have w102_388 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m102]; exact w101_388
  have w102_38c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m102]; exact w101_38c
  have w102_420 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m102]; exact w101_420
  have w102_424 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m102]; exact w101_424
  have w102_428 : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m102]; exact w101_428
  have w102_42c : memLoad32 n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m102]; exact w101_42c
  have b102_430 : n102.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m102]; exact b101_430
  clear b101_430 w101_42c w101_428 w101_424 w101_420 w101_38c w101_388 w101_384 w101_380 w101_15c w101_158 w101_154 w101_150 w101_a4 w101_a0 w101_9c w101_98 w101_94 w101_90 w101_8c w101_88 w101_84 w101_80 w101_7c w101_78 w101_74 w101_70 w101_6c w101_68 w101_64 w101_60 w101_5c w101_58 w101_54 w101_50 w101_4c w101_48 w101_44 w101_38 w101_34 w101_30 w101_2c g101_11 g101_27 g101_26 g101_25 g101_24 g101_23 g101_22 g101_21 g101_20 g101_19 g101_18 g101_12 g101_10 g101_9 g101_8 g101_4 g101_3 g101_2 V101 E101 fR101 t101 fr101 m101 s101 u101 d101
  -- 0x756: lw
  obtain ⟨n103, d103, u103⟩ := s102.lw E102.self sv_at_756 (off' := 0x75A) (by decide)
    (by rw [g102_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s103 : St n103.mem SV n103 0x75A (reg n103) := ⟨u103.pc, rfl, fun _ => rfl⟩
  have m103 : n103.mem = n102.mem := u103.mem
  have fr103 : ∀ x, SvR B x → n103.mem x = n102.mem x := fun x _ => by rw [m103]
  have t103 : Steps n0 n103 := t102.trans (.single d103)
  have fR103 : ∀ x, SvR B x → n103.mem x = M0 x := fun x hx => (fr103 x hx).trans (fR102 x hx)
  have E103 : SvCode n103.mem := E102.fr F fr103
  have V103 : SvSaves B n103.mem v := V102.same m103
  have g103_2 : reg n103 sp = B + 0x21A0 := by rw [u103.regs, upd_ne (by decide) (by decide), g102_2]
  have g103_3 : reg n103 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u103.regs, upd_ne (by decide) (by decide), g102_3]
  have g103_4 : reg n103 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u103.regs, upd_ne (by decide) (by decide), g102_4]
  have g103_8 : reg n103 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u103.regs, upd_ne (by decide) (by decide), g102_8]
  have g103_9 : reg n103 (9 : Fin 32) = tbp := by rw [u103.regs, upd_ne (by decide) (by decide), g102_9]
  have g103_10 : reg n103 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u103.regs, upd_ne (by decide) (by decide), g102_10]
  have g103_12 : reg n103 a2 = BitVec.ofNat 32 0xC := by rw [u103.regs, upd_ne (by decide) (by decide), g102_12]
  have g103_18 : reg n103 (18 : Fin 32) = out := by rw [u103.regs, upd_ne (by decide) (by decide), g102_18]
  have g103_19 : reg n103 (19 : Fin 32) = bp := by rw [u103.regs, upd_ne (by decide) (by decide), g102_19]
  have g103_20 : reg n103 (20 : Fin 32) = dg := by rw [u103.regs, upd_ne (by decide) (by decide), g102_20]
  have g103_21 : reg n103 (21 : Fin 32) = rootp := by rw [u103.regs, upd_ne (by decide) (by decide), g102_21]
  have g103_22 : reg n103 (22 : Fin 32) = ll := by rw [u103.regs, upd_ne (by decide) (by decide), g102_22]
  have g103_23 : reg n103 (23 : Fin 32) = sgp := by rw [u103.regs, upd_ne (by decide) (by decide), g102_23]
  have g103_24 : reg n103 (24 : Fin 32) = kp := by rw [u103.regs, upd_ne (by decide) (by decide), g102_24]
  have g103_25 : reg n103 (25 : Fin 32) = sgl := by rw [u103.regs, upd_ne (by decide) (by decide), g102_25]
  have g103_26 : reg n103 (26 : Fin 32) = BitVec.ofNat 32 (img% regionEndsAddress) := by rw [u103.regs, upd_ne (by decide) (by decide), g102_26]
  have g103_27 : reg n103 (27 : Fin 32) = tbl := by rw [u103.regs, upd_ne (by decide) (by decide), g102_27]
  have g103_11 : reg n103 a1 = BitVec.ofNat 32 tl95.len := by
    rw [u103.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g102_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w102_424]
  have keep_kk103 : SvKeepL B n0.mem n103.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m103]; exact keep_kk102
  clear keep_kk102
  have w103_2c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m103]; exact w102_2c
  have w103_30 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m103]; exact w102_30
  have w103_34 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m103]; exact w102_34
  have w103_38 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m103]; exact w102_38
  have w103_44 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m103]; exact w102_44
  have w103_48 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m103]; exact w102_48
  have w103_4c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m103]; exact w102_4c
  have w103_50 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m103]; exact w102_50
  have w103_54 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m103]; exact w102_54
  have w103_58 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m103]; exact w102_58
  have w103_5c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m103]; exact w102_5c
  have w103_60 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m103]; exact w102_60
  have w103_64 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m103]; exact w102_64
  have w103_68 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m103]; exact w102_68
  have w103_6c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m103]; exact w102_6c
  have w103_70 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m103]; exact w102_70
  have w103_74 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m103]; exact w102_74
  have w103_78 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m103]; exact w102_78
  have w103_7c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m103]; exact w102_7c
  have w103_80 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m103]; exact w102_80
  have w103_84 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m103]; exact w102_84
  have w103_88 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m103]; exact w102_88
  have w103_8c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m103]; exact w102_8c
  have w103_90 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m103]; exact w102_90
  have w103_94 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m103]; exact w102_94
  have w103_98 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m103]; exact w102_98
  have w103_9c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m103]; exact w102_9c
  have w103_a0 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m103]; exact w102_a0
  have w103_a4 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m103]; exact w102_a4
  have w103_150 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m103]; exact w102_150
  have w103_154 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m103]; exact w102_154
  have w103_158 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m103]; exact w102_158
  have w103_15c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m103]; exact w102_15c
  have w103_380 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m103]; exact w102_380
  have w103_384 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m103]; exact w102_384
  have w103_388 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m103]; exact w102_388
  have w103_38c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m103]; exact w102_38c
  have w103_420 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m103]; exact w102_420
  have w103_424 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m103]; exact w102_424
  have w103_428 : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m103]; exact w102_428
  have w103_42c : memLoad32 n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m103]; exact w102_42c
  have b103_430 : n103.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m103]; exact b102_430
  clear b102_430 w102_42c w102_428 w102_424 w102_420 w102_38c w102_388 w102_384 w102_380 w102_15c w102_158 w102_154 w102_150 w102_a4 w102_a0 w102_9c w102_98 w102_94 w102_90 w102_8c w102_88 w102_84 w102_80 w102_7c w102_78 w102_74 w102_70 w102_6c w102_68 w102_64 w102_60 w102_5c w102_58 w102_54 w102_50 w102_4c w102_48 w102_44 w102_38 w102_34 w102_30 w102_2c g102_27 g102_26 g102_25 g102_24 g102_23 g102_22 g102_21 g102_20 g102_19 g102_18 g102_12 g102_11 g102_10 g102_9 g102_8 g102_4 g102_3 g102_2 V102 E102 fR102 t102 fr102 m102 s102 u102 d102
  -- 0x75A: lw
  obtain ⟨n104, d104, u104⟩ := s103.lw E103.self sv_at_75a (off' := 0x75C) (by decide)
    (by rw [g103_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s104 : St n104.mem SV n104 0x75C (reg n104) := ⟨u104.pc, rfl, fun _ => rfl⟩
  have m104 : n104.mem = n103.mem := u104.mem
  have fr104 : ∀ x, SvR B x → n104.mem x = n103.mem x := fun x _ => by rw [m104]
  have t104 : Steps n0 n104 := t103.trans (.single d104)
  have fR104 : ∀ x, SvR B x → n104.mem x = M0 x := fun x hx => (fr104 x hx).trans (fR103 x hx)
  have E104 : SvCode n104.mem := E103.fr F fr104
  have V104 : SvSaves B n104.mem v := V103.same m104
  have g104_2 : reg n104 sp = B + 0x21A0 := by rw [u104.regs, upd_ne (by decide) (by decide), g103_2]
  have g104_3 : reg n104 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u104.regs, upd_ne (by decide) (by decide), g103_3]
  have g104_4 : reg n104 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u104.regs, upd_ne (by decide) (by decide), g103_4]
  have g104_8 : reg n104 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u104.regs, upd_ne (by decide) (by decide), g103_8]
  have g104_9 : reg n104 (9 : Fin 32) = tbp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_9]
  have g104_10 : reg n104 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u104.regs, upd_ne (by decide) (by decide), g103_10]
  have g104_11 : reg n104 a1 = BitVec.ofNat 32 tl95.len := by rw [u104.regs, upd_ne (by decide) (by decide), g103_11]
  have g104_12 : reg n104 a2 = BitVec.ofNat 32 0xC := by rw [u104.regs, upd_ne (by decide) (by decide), g103_12]
  have g104_18 : reg n104 (18 : Fin 32) = out := by rw [u104.regs, upd_ne (by decide) (by decide), g103_18]
  have g104_19 : reg n104 (19 : Fin 32) = bp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_19]
  have g104_20 : reg n104 (20 : Fin 32) = dg := by rw [u104.regs, upd_ne (by decide) (by decide), g103_20]
  have g104_21 : reg n104 (21 : Fin 32) = rootp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_21]
  have g104_22 : reg n104 (22 : Fin 32) = ll := by rw [u104.regs, upd_ne (by decide) (by decide), g103_22]
  have g104_23 : reg n104 (23 : Fin 32) = sgp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_23]
  have g104_24 : reg n104 (24 : Fin 32) = kp := by rw [u104.regs, upd_ne (by decide) (by decide), g103_24]
  have g104_25 : reg n104 (25 : Fin 32) = sgl := by rw [u104.regs, upd_ne (by decide) (by decide), g103_25]
  have g104_27 : reg n104 (27 : Fin 32) = tbl := by rw [u104.regs, upd_ne (by decide) (by decide), g103_27]
  have g104_26 : reg n104 (26 : Fin 32) = BitVec.ofNat 32 0x4 := by
    rw [u104.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g103_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w103_50]
  have keep_kk104 : SvKeepL B n0.mem n104.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m104]; exact keep_kk103
  clear keep_kk103
  have w104_2c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m104]; exact w103_2c
  have w104_30 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m104]; exact w103_30
  have w104_34 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m104]; exact w103_34
  have w104_38 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m104]; exact w103_38
  have w104_44 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m104]; exact w103_44
  have w104_48 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m104]; exact w103_48
  have w104_4c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m104]; exact w103_4c
  have w104_50 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m104]; exact w103_50
  have w104_54 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m104]; exact w103_54
  have w104_58 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m104]; exact w103_58
  have w104_5c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m104]; exact w103_5c
  have w104_60 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m104]; exact w103_60
  have w104_64 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m104]; exact w103_64
  have w104_68 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m104]; exact w103_68
  have w104_6c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m104]; exact w103_6c
  have w104_70 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m104]; exact w103_70
  have w104_74 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m104]; exact w103_74
  have w104_78 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m104]; exact w103_78
  have w104_7c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m104]; exact w103_7c
  have w104_80 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m104]; exact w103_80
  have w104_84 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m104]; exact w103_84
  have w104_88 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m104]; exact w103_88
  have w104_8c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m104]; exact w103_8c
  have w104_90 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m104]; exact w103_90
  have w104_94 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m104]; exact w103_94
  have w104_98 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m104]; exact w103_98
  have w104_9c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m104]; exact w103_9c
  have w104_a0 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m104]; exact w103_a0
  have w104_a4 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m104]; exact w103_a4
  have w104_150 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m104]; exact w103_150
  have w104_154 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m104]; exact w103_154
  have w104_158 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m104]; exact w103_158
  have w104_15c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m104]; exact w103_15c
  have w104_380 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m104]; exact w103_380
  have w104_384 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m104]; exact w103_384
  have w104_388 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m104]; exact w103_388
  have w104_38c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m104]; exact w103_38c
  have w104_420 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m104]; exact w103_420
  have w104_424 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m104]; exact w103_424
  have w104_428 : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m104]; exact w103_428
  have w104_42c : memLoad32 n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m104]; exact w103_42c
  have b104_430 : n104.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m104]; exact b103_430
  clear b103_430 w103_42c w103_428 w103_424 w103_420 w103_38c w103_388 w103_384 w103_380 w103_15c w103_158 w103_154 w103_150 w103_a4 w103_a0 w103_9c w103_98 w103_94 w103_90 w103_8c w103_88 w103_84 w103_80 w103_7c w103_78 w103_74 w103_70 w103_6c w103_68 w103_64 w103_60 w103_5c w103_58 w103_54 w103_50 w103_4c w103_48 w103_44 w103_38 w103_34 w103_30 w103_2c g103_11 g103_27 g103_26 g103_25 g103_24 g103_23 g103_22 g103_21 g103_20 g103_19 g103_18 g103_12 g103_10 g103_9 g103_8 g103_4 g103_3 g103_2 V103 E103 fR103 t103 fr103 m103 s103 u103 d103
  -- 0x75C
  obtain ⟨n105, c105, u105⟩ := s104.block svDp475c E104.self svDp475c_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m105 : n105.mem = n104.mem := u105.mem
  have s105 : St n105.mem SV n105 0x764 (reg n105) := ⟨u105.pc, rfl, fun _ => rfl⟩
  have rb105 : ∀ q, reg n105 q = (runBlock svDp475c (n104.mem, reg n104)).2 q := fun q => by rw [u105.regs]
  have fr105 : ∀ x, SvR B x → n105.mem x = n104.mem x := fun x _ => by rw [m105]
  have t105 : Steps n0 n105 := t104.trans c105
  have fR105 : ∀ x, SvR B x → n105.mem x = M0 x := fun x hx => (fr105 x hx).trans (fR104 x hx)
  have E105 : SvCode n105.mem := E104.fr F fr105
  have V105 : SvSaves B n105.mem v := V104.same m105
  have g105_2 : reg n105 sp = B + 0x21A0 := by
    rw [rb105, runBlock_reg _ _ _ sp s104.zero (by decide), g104_2]
  have g105_3 : reg n105 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb105, runBlock_reg _ _ _ (3 : Fin 32) s104.zero (by decide), g104_3]
  have g105_4 : reg n105 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb105, runBlock_reg _ _ _ (4 : Fin 32) s104.zero (by decide), g104_4]
  have g105_8 : reg n105 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb105, runBlock_reg _ _ _ (8 : Fin 32) s104.zero (by decide), g104_8]
  have g105_9 : reg n105 (9 : Fin 32) = tbp := by
    rw [rb105, runBlock_reg _ _ _ (9 : Fin 32) s104.zero (by decide), g104_9]
  have g105_10 : reg n105 a0 = (vp) + BitVec.ofNat 32 tl95.header := by
    rw [rb105, runBlock_reg _ _ _ a0 s104.zero (by decide), g104_10]
  have g105_11 : reg n105 a1 = BitVec.ofNat 32 tl95.len := by
    rw [rb105, runBlock_reg _ _ _ a1 s104.zero (by decide), g104_11]
  have g105_18 : reg n105 (18 : Fin 32) = out := by
    rw [rb105, runBlock_reg _ _ _ (18 : Fin 32) s104.zero (by decide), g104_18]
  have g105_19 : reg n105 (19 : Fin 32) = bp := by
    rw [rb105, runBlock_reg _ _ _ (19 : Fin 32) s104.zero (by decide), g104_19]
  have g105_20 : reg n105 (20 : Fin 32) = dg := by
    rw [rb105, runBlock_reg _ _ _ (20 : Fin 32) s104.zero (by decide), g104_20]
  have g105_21 : reg n105 (21 : Fin 32) = rootp := by
    rw [rb105, runBlock_reg _ _ _ (21 : Fin 32) s104.zero (by decide), g104_21]
  have g105_22 : reg n105 (22 : Fin 32) = ll := by
    rw [rb105, runBlock_reg _ _ _ (22 : Fin 32) s104.zero (by decide), g104_22]
  have g105_23 : reg n105 (23 : Fin 32) = sgp := by
    rw [rb105, runBlock_reg _ _ _ (23 : Fin 32) s104.zero (by decide), g104_23]
  have g105_24 : reg n105 (24 : Fin 32) = kp := by
    rw [rb105, runBlock_reg _ _ _ (24 : Fin 32) s104.zero (by decide), g104_24]
  have g105_25 : reg n105 (25 : Fin 32) = sgl := by
    rw [rb105, runBlock_reg _ _ _ (25 : Fin 32) s104.zero (by decide), g104_25]
  have g105_27 : reg n105 (27 : Fin 32) = tbl := by
    rw [rb105, runBlock_reg _ _ _ (27 : Fin 32) s104.zero (by decide), g104_27]
  have g105_12 : reg n105 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by
    rw [rb105]; simp +decide only [runBlock, BInstr.run, svDp475c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g104_2, g104_3, g104_4, g104_8, g104_9, g104_10, g104_11, g104_12, g104_18, g104_19, g104_20, g104_21, g104_22, g104_23, g104_24, g104_25, g104_26, g104_27, s104.zero])
    all_goals (try simp only [BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceHShiftLeft])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g105_26 : reg n105 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by
    rw [rb105]; simp +decide only [runBlock, BInstr.run, svDp475c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g104_2, g104_3, g104_4, g104_8, g104_9, g104_10, g104_11, g104_12, g104_18, g104_19, g104_20, g104_21, g104_22, g104_23, g104_24, g104_25, g104_26, g104_27, s104.zero])
    all_goals (try simp only [BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceHShiftLeft])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk105 : SvKeepL B n0.mem n105.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8)] := by rw [m105]; exact keep_kk104
  clear keep_kk104
  have w105_2c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m105]; exact w104_2c
  have w105_30 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m105]; exact w104_30
  have w105_34 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m105]; exact w104_34
  have w105_38 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m105]; exact w104_38
  have w105_44 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m105]; exact w104_44
  have w105_48 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m105]; exact w104_48
  have w105_4c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m105]; exact w104_4c
  have w105_50 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m105]; exact w104_50
  have w105_54 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m105]; exact w104_54
  have w105_58 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m105]; exact w104_58
  have w105_5c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m105]; exact w104_5c
  have w105_60 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m105]; exact w104_60
  have w105_64 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m105]; exact w104_64
  have w105_68 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m105]; exact w104_68
  have w105_6c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m105]; exact w104_6c
  have w105_70 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m105]; exact w104_70
  have w105_74 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m105]; exact w104_74
  have w105_78 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m105]; exact w104_78
  have w105_7c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m105]; exact w104_7c
  have w105_80 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m105]; exact w104_80
  have w105_84 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m105]; exact w104_84
  have w105_88 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m105]; exact w104_88
  have w105_8c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m105]; exact w104_8c
  have w105_90 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m105]; exact w104_90
  have w105_94 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m105]; exact w104_94
  have w105_98 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m105]; exact w104_98
  have w105_9c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m105]; exact w104_9c
  have w105_a0 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 := by rw [m105]; exact w104_a0
  have w105_a4 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := by rw [m105]; exact w104_a4
  have w105_150 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m105]; exact w104_150
  have w105_154 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m105]; exact w104_154
  have w105_158 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m105]; exact w104_158
  have w105_15c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m105]; exact w104_15c
  have w105_380 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m105]; exact w104_380
  have w105_384 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m105]; exact w104_384
  have w105_388 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m105]; exact w104_388
  have w105_38c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m105]; exact w104_38c
  have w105_420 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m105]; exact w104_420
  have w105_424 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m105]; exact w104_424
  have w105_428 : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m105]; exact w104_428
  have w105_42c : memLoad32 n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m105]; exact w104_42c
  have b105_430 : n105.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m105]; exact b104_430
  clear b104_430 w104_42c w104_428 w104_424 w104_420 w104_38c w104_388 w104_384 w104_380 w104_15c w104_158 w104_154 w104_150 w104_a4 w104_a0 w104_9c w104_98 w104_94 w104_90 w104_8c w104_88 w104_84 w104_80 w104_7c w104_78 w104_74 w104_70 w104_6c w104_68 w104_64 w104_60 w104_5c w104_58 w104_54 w104_50 w104_4c w104_48 w104_44 w104_38 w104_34 w104_30 w104_2c g104_26 g104_27 g104_25 g104_24 g104_23 g104_22 g104_21 g104_20 g104_19 g104_18 g104_12 g104_11 g104_10 g104_9 g104_8 g104_4 g104_3 g104_2 V104 E104 fR104 t104 fr104 m104 s104 u104 d104
  -- 0x764: sw
  obtain ⟨n106, d106, s106, fr106, K106, W106, rg106⟩ := sv_sw F E105 s105 sv_at_764 (off' := 0x766) (c := 0xA0)
    (by decide) (by rw [g105_12]; sv_addr) (by decide) (by decide)
  have t106 : Steps n0 n106 := t105.trans d106
  have fR106 : ∀ x, SvR B x → n106.mem x = M0 x := fun x hx => (fr106 x hx).trans (fR105 x hx)
  have E106 : SvCode n106.mem := E105.fr F fr106
  have V106 : SvSaves B n106.mem v := V105.keep K106 (by decide)
  have g106_2 : reg n106 sp = B + 0x21A0 := by rw [rg106 sp, g105_2]
  have g106_3 : reg n106 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg106 (3 : Fin 32), g105_3]
  have g106_4 : reg n106 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg106 (4 : Fin 32), g105_4]
  have g106_8 : reg n106 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg106 (8 : Fin 32), g105_8]
  have g106_9 : reg n106 (9 : Fin 32) = tbp := by rw [rg106 (9 : Fin 32), g105_9]
  have g106_10 : reg n106 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [rg106 a0, g105_10]
  have g106_11 : reg n106 a1 = BitVec.ofNat 32 tl95.len := by rw [rg106 a1, g105_11]
  have g106_12 : reg n106 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [rg106 a2, g105_12]
  have g106_18 : reg n106 (18 : Fin 32) = out := by rw [rg106 (18 : Fin 32), g105_18]
  have g106_19 : reg n106 (19 : Fin 32) = bp := by rw [rg106 (19 : Fin 32), g105_19]
  have g106_20 : reg n106 (20 : Fin 32) = dg := by rw [rg106 (20 : Fin 32), g105_20]
  have g106_21 : reg n106 (21 : Fin 32) = rootp := by rw [rg106 (21 : Fin 32), g105_21]
  have g106_22 : reg n106 (22 : Fin 32) = ll := by rw [rg106 (22 : Fin 32), g105_22]
  have g106_23 : reg n106 (23 : Fin 32) = sgp := by rw [rg106 (23 : Fin 32), g105_23]
  have g106_24 : reg n106 (24 : Fin 32) = kp := by rw [rg106 (24 : Fin 32), g105_24]
  have g106_25 : reg n106 (25 : Fin 32) = sgl := by rw [rg106 (25 : Fin 32), g105_25]
  have g106_26 : reg n106 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [rg106 (26 : Fin 32), g105_26]
  have g106_27 : reg n106 (27 : Fin 32) = tbl := by rw [rg106 (27 : Fin 32), g105_27]
  have keep_kk106 : SvKeepL B n0.mem n106.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0xA0, 0x4)] := keep_kk105.trans K106.toL
  clear keep_kk105
  have w106_2c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K106.w32 (by decide) (by decide)).trans w105_2c
  have w106_30 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K106.w32 (by decide) (by decide)).trans w105_30
  have w106_34 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K106.w32 (by decide) (by decide)).trans w105_34
  have w106_38 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K106.w32 (by decide) (by decide)).trans w105_38
  have w106_44 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K106.w32 (by decide) (by decide)).trans w105_44
  have w106_48 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K106.w32 (by decide) (by decide)).trans w105_48
  have w106_4c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K106.w32 (by decide) (by decide)).trans w105_4c
  have w106_50 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K106.w32 (by decide) (by decide)).trans w105_50
  have w106_54 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K106.w32 (by decide) (by decide)).trans w105_54
  have w106_58 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K106.w32 (by decide) (by decide)).trans w105_58
  have w106_5c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K106.w32 (by decide) (by decide)).trans w105_5c
  have w106_60 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K106.w32 (by decide) (by decide)).trans w105_60
  have w106_64 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K106.w32 (by decide) (by decide)).trans w105_64
  have w106_68 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K106.w32 (by decide) (by decide)).trans w105_68
  have w106_6c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K106.w32 (by decide) (by decide)).trans w105_6c
  have w106_70 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K106.w32 (by decide) (by decide)).trans w105_70
  have w106_74 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K106.w32 (by decide) (by decide)).trans w105_74
  have w106_78 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K106.w32 (by decide) (by decide)).trans w105_78
  have w106_7c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K106.w32 (by decide) (by decide)).trans w105_7c
  have w106_80 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K106.w32 (by decide) (by decide)).trans w105_80
  have w106_84 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K106.w32 (by decide) (by decide)).trans w105_84
  have w106_88 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K106.w32 (by decide) (by decide)).trans w105_88
  have w106_8c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K106.w32 (by decide) (by decide)).trans w105_8c
  have w106_90 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K106.w32 (by decide) (by decide)).trans w105_90
  have w106_94 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K106.w32 (by decide) (by decide)).trans w105_94
  have w106_98 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K106.w32 (by decide) (by decide)).trans w105_98
  have w106_9c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K106.w32 (by decide) (by decide)).trans w105_9c
  have w106_a4 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 := (K106.w32 (by decide) (by decide)).trans w105_a4
  have w106_150 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K106.w32 (by decide) (by decide)).trans w105_150
  have w106_154 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K106.w32 (by decide) (by decide)).trans w105_154
  have w106_158 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K106.w32 (by decide) (by decide)).trans w105_158
  have w106_15c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K106.w32 (by decide) (by decide)).trans w105_15c
  have w106_380 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K106.w32 (by decide) (by decide)).trans w105_380
  have w106_384 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K106.w32 (by decide) (by decide)).trans w105_384
  have w106_388 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := (K106.w32 (by decide) (by decide)).trans w105_388
  have w106_38c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := (K106.w32 (by decide) (by decide)).trans w105_38c
  have w106_420 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := (K106.w32 (by decide) (by decide)).trans w105_420
  have w106_424 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := (K106.w32 (by decide) (by decide)).trans w105_424
  have w106_428 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K106.w32 (by decide) (by decide)).trans w105_428
  have w106_42c : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := (K106.w32 (by decide) (by decide)).trans w105_42c
  have b106_430 : n106.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := (K106.b8 (by decide) (by decide)).trans b105_430
  have w106_a0 : memLoad32 n106.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = (vp) + BitVec.ofNat 32 tl95.header := by rw [W106, g105_10]
  clear b105_430 w105_42c w105_428 w105_424 w105_420 w105_38c w105_388 w105_384 w105_380 w105_15c w105_158 w105_154 w105_150 w105_a4 w105_a0 w105_9c w105_98 w105_94 w105_90 w105_8c w105_88 w105_84 w105_80 w105_7c w105_78 w105_74 w105_70 w105_6c w105_68 w105_64 w105_60 w105_5c w105_58 w105_54 w105_50 w105_4c w105_48 w105_44 w105_38 w105_34 w105_30 w105_2c g105_26 g105_12 g105_27 g105_25 g105_24 g105_23 g105_22 g105_21 g105_20 g105_19 g105_18 g105_11 g105_10 g105_9 g105_8 g105_4 g105_3 g105_2 V105 E105 fR105 t105 fr105 rb105 s105 m105 u105 c105
  -- 0x766: sw
  obtain ⟨n107, d107, s107, fr107, K107, W107, rg107⟩ := sv_sw F E106 s106 sv_at_766 (off' := 0x768) (c := 0xA4)
    (by decide) (by rw [g106_12]; sv_addr) (by decide) (by decide)
  have t107 : Steps n0 n107 := t106.trans d107
  have fR107 : ∀ x, SvR B x → n107.mem x = M0 x := fun x hx => (fr107 x hx).trans (fR106 x hx)
  have E107 : SvCode n107.mem := E106.fr F fr107
  have V107 : SvSaves B n107.mem v := V106.keep K107 (by decide)
  have g107_2 : reg n107 sp = B + 0x21A0 := by rw [rg107 sp, g106_2]
  have g107_3 : reg n107 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg107 (3 : Fin 32), g106_3]
  have g107_4 : reg n107 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg107 (4 : Fin 32), g106_4]
  have g107_8 : reg n107 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg107 (8 : Fin 32), g106_8]
  have g107_9 : reg n107 (9 : Fin 32) = tbp := by rw [rg107 (9 : Fin 32), g106_9]
  have g107_10 : reg n107 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [rg107 a0, g106_10]
  have g107_11 : reg n107 a1 = BitVec.ofNat 32 tl95.len := by rw [rg107 a1, g106_11]
  have g107_12 : reg n107 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [rg107 a2, g106_12]
  have g107_18 : reg n107 (18 : Fin 32) = out := by rw [rg107 (18 : Fin 32), g106_18]
  have g107_19 : reg n107 (19 : Fin 32) = bp := by rw [rg107 (19 : Fin 32), g106_19]
  have g107_20 : reg n107 (20 : Fin 32) = dg := by rw [rg107 (20 : Fin 32), g106_20]
  have g107_21 : reg n107 (21 : Fin 32) = rootp := by rw [rg107 (21 : Fin 32), g106_21]
  have g107_22 : reg n107 (22 : Fin 32) = ll := by rw [rg107 (22 : Fin 32), g106_22]
  have g107_23 : reg n107 (23 : Fin 32) = sgp := by rw [rg107 (23 : Fin 32), g106_23]
  have g107_24 : reg n107 (24 : Fin 32) = kp := by rw [rg107 (24 : Fin 32), g106_24]
  have g107_25 : reg n107 (25 : Fin 32) = sgl := by rw [rg107 (25 : Fin 32), g106_25]
  have g107_26 : reg n107 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [rg107 (26 : Fin 32), g106_26]
  have g107_27 : reg n107 (27 : Fin 32) = tbl := by rw [rg107 (27 : Fin 32), g106_27]
  have keep_kk107 : SvKeepL B n0.mem n107.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0xA0, 0x4), (0xA4, 0x4)] := keep_kk106.trans K107.toL
  clear keep_kk106
  have w107_2c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K107.w32 (by decide) (by decide)).trans w106_2c
  have w107_30 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K107.w32 (by decide) (by decide)).trans w106_30
  have w107_34 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K107.w32 (by decide) (by decide)).trans w106_34
  have w107_38 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K107.w32 (by decide) (by decide)).trans w106_38
  have w107_44 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K107.w32 (by decide) (by decide)).trans w106_44
  have w107_48 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K107.w32 (by decide) (by decide)).trans w106_48
  have w107_4c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K107.w32 (by decide) (by decide)).trans w106_4c
  have w107_50 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := (K107.w32 (by decide) (by decide)).trans w106_50
  have w107_54 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K107.w32 (by decide) (by decide)).trans w106_54
  have w107_58 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K107.w32 (by decide) (by decide)).trans w106_58
  have w107_5c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K107.w32 (by decide) (by decide)).trans w106_5c
  have w107_60 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K107.w32 (by decide) (by decide)).trans w106_60
  have w107_64 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K107.w32 (by decide) (by decide)).trans w106_64
  have w107_68 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K107.w32 (by decide) (by decide)).trans w106_68
  have w107_6c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K107.w32 (by decide) (by decide)).trans w106_6c
  have w107_70 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K107.w32 (by decide) (by decide)).trans w106_70
  have w107_74 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K107.w32 (by decide) (by decide)).trans w106_74
  have w107_78 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K107.w32 (by decide) (by decide)).trans w106_78
  have w107_7c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K107.w32 (by decide) (by decide)).trans w106_7c
  have w107_80 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K107.w32 (by decide) (by decide)).trans w106_80
  have w107_84 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K107.w32 (by decide) (by decide)).trans w106_84
  have w107_88 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K107.w32 (by decide) (by decide)).trans w106_88
  have w107_8c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K107.w32 (by decide) (by decide)).trans w106_8c
  have w107_90 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K107.w32 (by decide) (by decide)).trans w106_90
  have w107_94 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K107.w32 (by decide) (by decide)).trans w106_94
  have w107_98 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K107.w32 (by decide) (by decide)).trans w106_98
  have w107_9c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K107.w32 (by decide) (by decide)).trans w106_9c
  have w107_a0 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = (vp) + BitVec.ofNat 32 tl95.header := (K107.w32 (by decide) (by decide)).trans w106_a0
  have w107_150 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K107.w32 (by decide) (by decide)).trans w106_150
  have w107_154 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K107.w32 (by decide) (by decide)).trans w106_154
  have w107_158 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K107.w32 (by decide) (by decide)).trans w106_158
  have w107_15c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K107.w32 (by decide) (by decide)).trans w106_15c
  have w107_380 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K107.w32 (by decide) (by decide)).trans w106_380
  have w107_384 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K107.w32 (by decide) (by decide)).trans w106_384
  have w107_388 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := (K107.w32 (by decide) (by decide)).trans w106_388
  have w107_38c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := (K107.w32 (by decide) (by decide)).trans w106_38c
  have w107_420 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := (K107.w32 (by decide) (by decide)).trans w106_420
  have w107_424 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := (K107.w32 (by decide) (by decide)).trans w106_424
  have w107_428 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K107.w32 (by decide) (by decide)).trans w106_428
  have w107_42c : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := (K107.w32 (by decide) (by decide)).trans w106_42c
  have b107_430 : n107.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := (K107.b8 (by decide) (by decide)).trans b106_430
  have w107_a4 : memLoad32 n107.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = BitVec.ofNat 32 tl95.len := by rw [W107, g106_11]
  clear w106_a0 b106_430 w106_42c w106_428 w106_424 w106_420 w106_38c w106_388 w106_384 w106_380 w106_15c w106_158 w106_154 w106_150 w106_a4 w106_9c w106_98 w106_94 w106_90 w106_8c w106_88 w106_84 w106_80 w106_7c w106_78 w106_74 w106_70 w106_6c w106_68 w106_64 w106_60 w106_5c w106_58 w106_54 w106_50 w106_4c w106_48 w106_44 w106_38 w106_34 w106_30 w106_2c g106_27 g106_26 g106_25 g106_24 g106_23 g106_22 g106_21 g106_20 g106_19 g106_18 g106_12 g106_11 g106_10 g106_9 g106_8 g106_4 g106_3 g106_2 V106 E106 fR106 t106 rg106 W106 K106 fr106 s106 d106
  -- 0x768: j
  obtain ⟨n108, d108, u108⟩ := s107.jump E107.self sv_at_768 (off' := 0x798) (by decide)
    (by rw [s107.pc]; decide)
  have s108 : St n108.mem SV n108 0x798 (reg n108) := ⟨u108.pc, rfl, fun _ => rfl⟩
  have m108 : n108.mem = n107.mem := u108.mem
  have fr108 : ∀ x, SvR B x → n108.mem x = n107.mem x := fun x _ => by rw [m108]
  have t108 : Steps n0 n108 := t107.trans (.single d108)
  have fR108 : ∀ x, SvR B x → n108.mem x = M0 x := fun x hx => (fr108 x hx).trans (fR107 x hx)
  have E108 : SvCode n108.mem := E107.fr F fr108
  have V108 : SvSaves B n108.mem v := V107.same m108
  have g108_2 : reg n108 sp = B + 0x21A0 := by rw [u108.regs, g107_2]
  have g108_3 : reg n108 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u108.regs, g107_3]
  have g108_4 : reg n108 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u108.regs, g107_4]
  have g108_8 : reg n108 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u108.regs, g107_8]
  have g108_9 : reg n108 (9 : Fin 32) = tbp := by rw [u108.regs, g107_9]
  have g108_10 : reg n108 a0 = (vp) + BitVec.ofNat 32 tl95.header := by rw [u108.regs, g107_10]
  have g108_11 : reg n108 a1 = BitVec.ofNat 32 tl95.len := by rw [u108.regs, g107_11]
  have g108_12 : reg n108 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [u108.regs, g107_12]
  have g108_18 : reg n108 (18 : Fin 32) = out := by rw [u108.regs, g107_18]
  have g108_19 : reg n108 (19 : Fin 32) = bp := by rw [u108.regs, g107_19]
  have g108_20 : reg n108 (20 : Fin 32) = dg := by rw [u108.regs, g107_20]
  have g108_21 : reg n108 (21 : Fin 32) = rootp := by rw [u108.regs, g107_21]
  have g108_22 : reg n108 (22 : Fin 32) = ll := by rw [u108.regs, g107_22]
  have g108_23 : reg n108 (23 : Fin 32) = sgp := by rw [u108.regs, g107_23]
  have g108_24 : reg n108 (24 : Fin 32) = kp := by rw [u108.regs, g107_24]
  have g108_25 : reg n108 (25 : Fin 32) = sgl := by rw [u108.regs, g107_25]
  have g108_26 : reg n108 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [u108.regs, g107_26]
  have g108_27 : reg n108 (27 : Fin 32) = tbl := by rw [u108.regs, g107_27]
  have keep_kk108 : SvKeepL B n0.mem n108.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0xA0, 0x4), (0xA4, 0x4)] := by rw [m108]; exact keep_kk107
  clear keep_kk107
  have w108_2c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m108]; exact w107_2c
  have w108_30 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m108]; exact w107_30
  have w108_34 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m108]; exact w107_34
  have w108_38 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m108]; exact w107_38
  have w108_44 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m108]; exact w107_44
  have w108_48 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m108]; exact w107_48
  have w108_4c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m108]; exact w107_4c
  have w108_50 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m108]; exact w107_50
  have w108_54 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m108]; exact w107_54
  have w108_58 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m108]; exact w107_58
  have w108_5c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m108]; exact w107_5c
  have w108_60 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m108]; exact w107_60
  have w108_64 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m108]; exact w107_64
  have w108_68 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m108]; exact w107_68
  have w108_6c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m108]; exact w107_6c
  have w108_70 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m108]; exact w107_70
  have w108_74 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m108]; exact w107_74
  have w108_78 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m108]; exact w107_78
  have w108_7c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m108]; exact w107_7c
  have w108_80 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m108]; exact w107_80
  have w108_84 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m108]; exact w107_84
  have w108_88 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m108]; exact w107_88
  have w108_8c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m108]; exact w107_8c
  have w108_90 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m108]; exact w107_90
  have w108_94 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m108]; exact w107_94
  have w108_98 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m108]; exact w107_98
  have w108_9c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m108]; exact w107_9c
  have w108_a0 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m108]; exact w107_a0
  have w108_a4 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = BitVec.ofNat 32 tl95.len := by rw [m108]; exact w107_a4
  have w108_150 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m108]; exact w107_150
  have w108_154 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m108]; exact w107_154
  have w108_158 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m108]; exact w107_158
  have w108_15c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m108]; exact w107_15c
  have w108_380 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m108]; exact w107_380
  have w108_384 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m108]; exact w107_384
  have w108_388 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m108]; exact w107_388
  have w108_38c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m108]; exact w107_38c
  have w108_420 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m108]; exact w107_420
  have w108_424 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m108]; exact w107_424
  have w108_428 : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m108]; exact w107_428
  have w108_42c : memLoad32 n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m108]; exact w107_42c
  have b108_430 : n108.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m108]; exact b107_430
  clear w107_a4 b107_430 w107_42c w107_428 w107_424 w107_420 w107_38c w107_388 w107_384 w107_380 w107_15c w107_158 w107_154 w107_150 w107_a0 w107_9c w107_98 w107_94 w107_90 w107_8c w107_88 w107_84 w107_80 w107_7c w107_78 w107_74 w107_70 w107_6c w107_68 w107_64 w107_60 w107_5c w107_58 w107_54 w107_50 w107_4c w107_48 w107_44 w107_38 w107_34 w107_30 w107_2c g107_27 g107_26 g107_25 g107_24 g107_23 g107_22 g107_21 g107_20 g107_19 g107_18 g107_12 g107_11 g107_10 g107_9 g107_8 g107_4 g107_3 g107_2 V107 E107 fR107 t107 rg107 W107 K107 fr107 s107 d107
  -- 0x798: lw
  obtain ⟨n109, d109, u109⟩ := s108.lw E108.self sv_at_798 (off' := 0x79C) (by decide)
    (by rw [g108_2, show B + 0x21A0 + 0x15C = B + 0x21A0 + BitVec.ofNat 32 0x15C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s109 : St n109.mem SV n109 0x79C (reg n109) := ⟨u109.pc, rfl, fun _ => rfl⟩
  have m109 : n109.mem = n108.mem := u109.mem
  have fr109 : ∀ x, SvR B x → n109.mem x = n108.mem x := fun x _ => by rw [m109]
  have t109 : Steps n0 n109 := t108.trans (.single d109)
  have fR109 : ∀ x, SvR B x → n109.mem x = M0 x := fun x hx => (fr109 x hx).trans (fR108 x hx)
  have E109 : SvCode n109.mem := E108.fr F fr109
  have V109 : SvSaves B n109.mem v := V108.same m109
  have g109_2 : reg n109 sp = B + 0x21A0 := by rw [u109.regs, upd_ne (by decide) (by decide), g108_2]
  have g109_3 : reg n109 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u109.regs, upd_ne (by decide) (by decide), g108_3]
  have g109_4 : reg n109 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u109.regs, upd_ne (by decide) (by decide), g108_4]
  have g109_8 : reg n109 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u109.regs, upd_ne (by decide) (by decide), g108_8]
  have g109_9 : reg n109 (9 : Fin 32) = tbp := by rw [u109.regs, upd_ne (by decide) (by decide), g108_9]
  have g109_11 : reg n109 a1 = BitVec.ofNat 32 tl95.len := by rw [u109.regs, upd_ne (by decide) (by decide), g108_11]
  have g109_12 : reg n109 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [u109.regs, upd_ne (by decide) (by decide), g108_12]
  have g109_18 : reg n109 (18 : Fin 32) = out := by rw [u109.regs, upd_ne (by decide) (by decide), g108_18]
  have g109_19 : reg n109 (19 : Fin 32) = bp := by rw [u109.regs, upd_ne (by decide) (by decide), g108_19]
  have g109_20 : reg n109 (20 : Fin 32) = dg := by rw [u109.regs, upd_ne (by decide) (by decide), g108_20]
  have g109_21 : reg n109 (21 : Fin 32) = rootp := by rw [u109.regs, upd_ne (by decide) (by decide), g108_21]
  have g109_22 : reg n109 (22 : Fin 32) = ll := by rw [u109.regs, upd_ne (by decide) (by decide), g108_22]
  have g109_23 : reg n109 (23 : Fin 32) = sgp := by rw [u109.regs, upd_ne (by decide) (by decide), g108_23]
  have g109_24 : reg n109 (24 : Fin 32) = kp := by rw [u109.regs, upd_ne (by decide) (by decide), g108_24]
  have g109_25 : reg n109 (25 : Fin 32) = sgl := by rw [u109.regs, upd_ne (by decide) (by decide), g108_25]
  have g109_26 : reg n109 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [u109.regs, upd_ne (by decide) (by decide), g108_26]
  have g109_27 : reg n109 (27 : Fin 32) = tbl := by rw [u109.regs, upd_ne (by decide) (by decide), g108_27]
  have g109_10 : reg n109 a0 = rest := by
    rw [u109.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g108_2, show B + 0x21A0 + 0x15C = B + 0x21A0 + BitVec.ofNat 32 0x15C by sv_addr, w108_15c]
  have keep_kk109 : SvKeepL B n0.mem n109.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0xA0, 0x4), (0xA4, 0x4)] := by rw [m109]; exact keep_kk108
  clear keep_kk108
  have w109_2c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m109]; exact w108_2c
  have w109_30 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m109]; exact w108_30
  have w109_34 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m109]; exact w108_34
  have w109_38 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m109]; exact w108_38
  have w109_44 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m109]; exact w108_44
  have w109_48 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m109]; exact w108_48
  have w109_4c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m109]; exact w108_4c
  have w109_50 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 0x4 := by rw [m109]; exact w108_50
  have w109_54 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m109]; exact w108_54
  have w109_58 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m109]; exact w108_58
  have w109_5c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m109]; exact w108_5c
  have w109_60 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m109]; exact w108_60
  have w109_64 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m109]; exact w108_64
  have w109_68 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m109]; exact w108_68
  have w109_6c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m109]; exact w108_6c
  have w109_70 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m109]; exact w108_70
  have w109_74 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m109]; exact w108_74
  have w109_78 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m109]; exact w108_78
  have w109_7c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m109]; exact w108_7c
  have w109_80 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m109]; exact w108_80
  have w109_84 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m109]; exact w108_84
  have w109_88 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m109]; exact w108_88
  have w109_8c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m109]; exact w108_8c
  have w109_90 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m109]; exact w108_90
  have w109_94 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m109]; exact w108_94
  have w109_98 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m109]; exact w108_98
  have w109_9c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m109]; exact w108_9c
  have w109_a0 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m109]; exact w108_a0
  have w109_a4 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = BitVec.ofNat 32 tl95.len := by rw [m109]; exact w108_a4
  have w109_150 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m109]; exact w108_150
  have w109_154 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m109]; exact w108_154
  have w109_158 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m109]; exact w108_158
  have w109_15c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m109]; exact w108_15c
  have w109_380 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m109]; exact w108_380
  have w109_384 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m109]; exact w108_384
  have w109_388 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m109]; exact w108_388
  have w109_38c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m109]; exact w108_38c
  have w109_420 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m109]; exact w108_420
  have w109_424 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m109]; exact w108_424
  have w109_428 : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m109]; exact w108_428
  have w109_42c : memLoad32 n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m109]; exact w108_42c
  have b109_430 : n109.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m109]; exact b108_430
  clear b108_430 w108_42c w108_428 w108_424 w108_420 w108_38c w108_388 w108_384 w108_380 w108_15c w108_158 w108_154 w108_150 w108_a4 w108_a0 w108_9c w108_98 w108_94 w108_90 w108_8c w108_88 w108_84 w108_80 w108_7c w108_78 w108_74 w108_70 w108_6c w108_68 w108_64 w108_60 w108_5c w108_58 w108_54 w108_50 w108_4c w108_48 w108_44 w108_38 w108_34 w108_30 w108_2c g108_27 g108_26 g108_25 g108_24 g108_23 g108_22 g108_21 g108_20 g108_19 g108_18 g108_12 g108_11 g108_10 g108_9 g108_8 g108_4 g108_3 g108_2 V108 E108 fR108 t108 fr108 m108 s108 u108 d108
  -- 0x79C: sw
  obtain ⟨n110, d110, s110, fr110, K110, W110, rg110⟩ := sv_sw F E109 s109 sv_at_79c (off' := 0x79E) (c := 0x50)
    (by decide) (by rw [g109_2]; sv_addr) (by decide) (by decide)
  have t110 : Steps n0 n110 := t109.trans d110
  have fR110 : ∀ x, SvR B x → n110.mem x = M0 x := fun x hx => (fr110 x hx).trans (fR109 x hx)
  have E110 : SvCode n110.mem := E109.fr F fr110
  have V110 : SvSaves B n110.mem v := V109.keep K110 (by decide)
  have g110_2 : reg n110 sp = B + 0x21A0 := by rw [rg110 sp, g109_2]
  have g110_3 : reg n110 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg110 (3 : Fin 32), g109_3]
  have g110_4 : reg n110 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg110 (4 : Fin 32), g109_4]
  have g110_8 : reg n110 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg110 (8 : Fin 32), g109_8]
  have g110_9 : reg n110 (9 : Fin 32) = tbp := by rw [rg110 (9 : Fin 32), g109_9]
  have g110_10 : reg n110 a0 = rest := by rw [rg110 a0, g109_10]
  have g110_11 : reg n110 a1 = BitVec.ofNat 32 tl95.len := by rw [rg110 a1, g109_11]
  have g110_12 : reg n110 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [rg110 a2, g109_12]
  have g110_18 : reg n110 (18 : Fin 32) = out := by rw [rg110 (18 : Fin 32), g109_18]
  have g110_19 : reg n110 (19 : Fin 32) = bp := by rw [rg110 (19 : Fin 32), g109_19]
  have g110_20 : reg n110 (20 : Fin 32) = dg := by rw [rg110 (20 : Fin 32), g109_20]
  have g110_21 : reg n110 (21 : Fin 32) = rootp := by rw [rg110 (21 : Fin 32), g109_21]
  have g110_22 : reg n110 (22 : Fin 32) = ll := by rw [rg110 (22 : Fin 32), g109_22]
  have g110_23 : reg n110 (23 : Fin 32) = sgp := by rw [rg110 (23 : Fin 32), g109_23]
  have g110_24 : reg n110 (24 : Fin 32) = kp := by rw [rg110 (24 : Fin 32), g109_24]
  have g110_25 : reg n110 (25 : Fin 32) = sgl := by rw [rg110 (25 : Fin 32), g109_25]
  have g110_26 : reg n110 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [rg110 (26 : Fin 32), g109_26]
  have g110_27 : reg n110 (27 : Fin 32) = tbl := by rw [rg110 (27 : Fin 32), g109_27]
  have keep_kk110 : SvKeepL B n0.mem n110.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0xA0, 0x4), (0xA4, 0x4), (0x50, 0x4)] := keep_kk109.trans K110.toL
  clear keep_kk109
  have w110_2c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := (K110.w32 (by decide) (by decide)).trans w109_2c
  have w110_30 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K110.w32 (by decide) (by decide)).trans w109_30
  have w110_34 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := (K110.w32 (by decide) (by decide)).trans w109_34
  have w110_38 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := (K110.w32 (by decide) (by decide)).trans w109_38
  have w110_44 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := (K110.w32 (by decide) (by decide)).trans w109_44
  have w110_48 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K110.w32 (by decide) (by decide)).trans w109_48
  have w110_4c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := (K110.w32 (by decide) (by decide)).trans w109_4c
  have w110_54 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K110.w32 (by decide) (by decide)).trans w109_54
  have w110_58 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K110.w32 (by decide) (by decide)).trans w109_58
  have w110_5c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K110.w32 (by decide) (by decide)).trans w109_5c
  have w110_60 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K110.w32 (by decide) (by decide)).trans w109_60
  have w110_64 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K110.w32 (by decide) (by decide)).trans w109_64
  have w110_68 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K110.w32 (by decide) (by decide)).trans w109_68
  have w110_6c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K110.w32 (by decide) (by decide)).trans w109_6c
  have w110_70 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K110.w32 (by decide) (by decide)).trans w109_70
  have w110_74 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K110.w32 (by decide) (by decide)).trans w109_74
  have w110_78 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K110.w32 (by decide) (by decide)).trans w109_78
  have w110_7c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K110.w32 (by decide) (by decide)).trans w109_7c
  have w110_80 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := (K110.w32 (by decide) (by decide)).trans w109_80
  have w110_84 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := (K110.w32 (by decide) (by decide)).trans w109_84
  have w110_88 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := (K110.w32 (by decide) (by decide)).trans w109_88
  have w110_8c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := (K110.w32 (by decide) (by decide)).trans w109_8c
  have w110_90 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := (K110.w32 (by decide) (by decide)).trans w109_90
  have w110_94 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := (K110.w32 (by decide) (by decide)).trans w109_94
  have w110_98 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := (K110.w32 (by decide) (by decide)).trans w109_98
  have w110_9c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := (K110.w32 (by decide) (by decide)).trans w109_9c
  have w110_a0 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = (vp) + BitVec.ofNat 32 tl95.header := (K110.w32 (by decide) (by decide)).trans w109_a0
  have w110_a4 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = BitVec.ofNat 32 tl95.len := (K110.w32 (by decide) (by decide)).trans w109_a4
  have w110_150 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := (K110.w32 (by decide) (by decide)).trans w109_150
  have w110_154 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := (K110.w32 (by decide) (by decide)).trans w109_154
  have w110_158 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := (K110.w32 (by decide) (by decide)).trans w109_158
  have w110_15c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := (K110.w32 (by decide) (by decide)).trans w109_15c
  have w110_380 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := (K110.w32 (by decide) (by decide)).trans w109_380
  have w110_384 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := (K110.w32 (by decide) (by decide)).trans w109_384
  have w110_388 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := (K110.w32 (by decide) (by decide)).trans w109_388
  have w110_38c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := (K110.w32 (by decide) (by decide)).trans w109_38c
  have w110_420 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := (K110.w32 (by decide) (by decide)).trans w109_420
  have w110_424 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := (K110.w32 (by decide) (by decide)).trans w109_424
  have w110_428 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := (K110.w32 (by decide) (by decide)).trans w109_428
  have w110_42c : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := (K110.w32 (by decide) (by decide)).trans w109_42c
  have b110_430 : n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := (K110.b8 (by decide) (by decide)).trans b109_430
  have w110_50 : memLoad32 n110.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rest := by rw [W110, g109_10]
  clear b109_430 w109_42c w109_428 w109_424 w109_420 w109_38c w109_388 w109_384 w109_380 w109_15c w109_158 w109_154 w109_150 w109_a4 w109_a0 w109_9c w109_98 w109_94 w109_90 w109_8c w109_88 w109_84 w109_80 w109_7c w109_78 w109_74 w109_70 w109_6c w109_68 w109_64 w109_60 w109_5c w109_58 w109_54 w109_50 w109_4c w109_48 w109_44 w109_38 w109_34 w109_30 w109_2c g109_10 g109_27 g109_26 g109_25 g109_24 g109_23 g109_22 g109_21 g109_20 g109_19 g109_18 g109_12 g109_11 g109_9 g109_8 g109_4 g109_3 g109_2 V109 E109 fR109 t109 fr109 m109 s109 u109 d109
  -- 0x79E: j
  obtain ⟨n111, d111, u111⟩ := s110.jump E110.self sv_at_79e (off' := 0x3B8) (by decide)
    (by rw [s110.pc]; decide)
  have s111 : St n111.mem SV n111 0x3B8 (reg n111) := ⟨u111.pc, rfl, fun _ => rfl⟩
  have m111 : n111.mem = n110.mem := u111.mem
  have fr111 : ∀ x, SvR B x → n111.mem x = n110.mem x := fun x _ => by rw [m111]
  have t111 : Steps n0 n111 := t110.trans (.single d111)
  have fR111 : ∀ x, SvR B x → n111.mem x = M0 x := fun x hx => (fr111 x hx).trans (fR110 x hx)
  have E111 : SvCode n111.mem := E110.fr F fr111
  have V111 : SvSaves B n111.mem v := V110.same m111
  have g111_2 : reg n111 sp = B + 0x21A0 := by rw [u111.regs, g110_2]
  have g111_3 : reg n111 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u111.regs, g110_3]
  have g111_4 : reg n111 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u111.regs, g110_4]
  have g111_8 : reg n111 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u111.regs, g110_8]
  have g111_9 : reg n111 (9 : Fin 32) = tbp := by rw [u111.regs, g110_9]
  have g111_10 : reg n111 a0 = rest := by rw [u111.regs, g110_10]
  have g111_11 : reg n111 a1 = BitVec.ofNat 32 tl95.len := by rw [u111.regs, g110_11]
  have g111_12 : reg n111 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [u111.regs, g110_12]
  have g111_18 : reg n111 (18 : Fin 32) = out := by rw [u111.regs, g110_18]
  have g111_19 : reg n111 (19 : Fin 32) = bp := by rw [u111.regs, g110_19]
  have g111_20 : reg n111 (20 : Fin 32) = dg := by rw [u111.regs, g110_20]
  have g111_21 : reg n111 (21 : Fin 32) = rootp := by rw [u111.regs, g110_21]
  have g111_22 : reg n111 (22 : Fin 32) = ll := by rw [u111.regs, g110_22]
  have g111_23 : reg n111 (23 : Fin 32) = sgp := by rw [u111.regs, g110_23]
  have g111_24 : reg n111 (24 : Fin 32) = kp := by rw [u111.regs, g110_24]
  have g111_25 : reg n111 (25 : Fin 32) = sgl := by rw [u111.regs, g110_25]
  have g111_26 : reg n111 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA0 := by rw [u111.regs, g110_26]
  have g111_27 : reg n111 (27 : Fin 32) = tbl := by rw [u111.regs, g110_27]
  have keep_kk111 : SvKeepL B n0.mem n111.mem [(0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0xA0, 0x4), (0xA4, 0x4), (0x50, 0x4)] := by rw [m111]; exact keep_kk110
  clear keep_kk110
  have w111_2c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c := by rw [m111]; exact w110_2c
  have w111_30 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m111]; exact w110_30
  have w111_34 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl := by rw [m111]; exact w110_34
  have w111_38 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp := by rw [m111]; exact w110_38
  have w111_44 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m111]; exact w110_44
  have w111_48 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m111]; exact w110_48
  have w111_4c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op := by rw [m111]; exact w110_4c
  have w111_50 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rest := by rw [m111]; exact w110_50
  have w111_54 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m111]; exact w110_54
  have w111_58 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m111]; exact w110_58
  have w111_5c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m111]; exact w110_5c
  have w111_60 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m111]; exact w110_60
  have w111_64 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m111]; exact w110_64
  have w111_68 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m111]; exact w110_68
  have w111_6c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m111]; exact w110_6c
  have w111_70 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m111]; exact w110_70
  have w111_74 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m111]; exact w110_74
  have w111_78 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m111]; exact w110_78
  have w111_7c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m111]; exact w110_7c
  have w111_80 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 := by rw [m111]; exact w110_80
  have w111_84 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 := by rw [m111]; exact w110_84
  have w111_88 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 := by rw [m111]; exact w110_88
  have w111_8c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 := by rw [m111]; exact w110_8c
  have w111_90 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 := by rw [m111]; exact w110_90
  have w111_94 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 := by rw [m111]; exact w110_94
  have w111_98 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 := by rw [m111]; exact w110_98
  have w111_9c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 := by rw [m111]; exact w110_9c
  have w111_a0 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m111]; exact w110_a0
  have w111_a4 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = BitVec.ofNat 32 tl95.len := by rw [m111]; exact w110_a4
  have w111_150 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 := by rw [m111]; exact w110_150
  have w111_154 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L := by rw [m111]; exact w110_154
  have w111_158 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur := by rw [m111]; exact w110_158
  have w111_15c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest := by rw [m111]; exact w110_15c
  have w111_380 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = vp := by rw [m111]; exact w110_380
  have w111_384 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = vl := by rw [m111]; exact w110_384
  have w111_388 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (vp) + BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m111]; exact w110_388
  have w111_38c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (vl) - BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m111]; exact w110_38c
  have w111_420 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (vp) + BitVec.ofNat 32 tl95.header := by rw [m111]; exact w110_420
  have w111_424 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl95.len := by rw [m111]; exact w110_424
  have w111_428 : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = vp := by rw [m111]; exact w110_428
  have w111_42c : memLoad32 n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl95.header + tl95.len) := by rw [m111]; exact w110_42c
  have b111_430 : n111.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl95.tag := by rw [m111]; exact b110_430
  clear w110_50 b110_430 w110_42c w110_428 w110_424 w110_420 w110_38c w110_388 w110_384 w110_380 w110_15c w110_158 w110_154 w110_150 w110_a4 w110_a0 w110_9c w110_98 w110_94 w110_90 w110_8c w110_88 w110_84 w110_80 w110_7c w110_78 w110_74 w110_70 w110_6c w110_68 w110_64 w110_60 w110_5c w110_58 w110_54 w110_4c w110_48 w110_44 w110_38 w110_34 w110_30 w110_2c g110_27 g110_26 g110_25 g110_24 g110_23 g110_22 g110_21 g110_20 g110_19 g110_18 g110_12 g110_11 g110_10 g110_9 g110_8 g110_4 g110_3 g110_2 V110 E110 fR110 t110 rg110 W110 K110 fr110 s110 d110
  exact .inr ⟨tl95, hr95, hz_99, hz_101, n111, t111, s111, E111, V111, fR111, g111_2, g111_3, g111_4, g111_8, g111_9, g111_18, g111_19, g111_20, g111_21, g111_22, g111_23, g111_24, g111_25, g111_27, w111_2c, w111_30, w111_50, w111_54, w111_58, w111_5c, w111_60, w111_64, w111_68, w111_6c, w111_70, w111_74, w111_78, w111_7c, w111_80, w111_84, w111_88, w111_8c, w111_90, w111_94, w111_98, w111_9c, w111_a0, w111_a4, w111_150, w111_154, w111_158, w111_15c, keep_kk111.mono (by decide)⟩

end C3.RV32.Sv
