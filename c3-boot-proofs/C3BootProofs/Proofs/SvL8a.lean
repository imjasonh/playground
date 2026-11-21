import C3BootProofs.Proofs.SvFail

/-!
# `sigstore::verify`: the parsed leaf

From 0xA44 to the intermediates loop at 0xAE2: `sigstore::verify` copies the leaf's fields, with `r` and `s`, into its `Leaf` at offset 0x88 of the frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL8aa44 : List BInstr :=
  [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x223, .aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x5F]
theorem svL8aa44_end : blockEnd sigstoreVerifyCode 0xA44 svL8aa44 = some 0xA54 := by
  simp only [svL8aa44]
  rw [blockEnd, sv_at_a44]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a48]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a4c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a50]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL8aa5e : List BInstr :=
  [.aluImm .srl a0 (24 : Fin 32) 0x8]
theorem svL8aa5e_end : blockEnd sigstoreVerifyCode 0xA5E svL8aa5e = some 0xA62 := by
  simp only [svL8aa5e]
  rw [blockEnd, sv_at_a5e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL8aa62 : List BInstr :=
  [.aluImm .srl a1 (24 : Fin 32) 0x10]
theorem svL8aa62_end : blockEnd sigstoreVerifyCode 0xA62 svL8aa62 = some 0xA66 := by
  simp only [svL8aa62]
  rw [blockEnd, sv_at_a62]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL8aa66 : List BInstr :=
  [.aluImm .srl a2 (24 : Fin 32) 0x18]
theorem svL8aa66_end : blockEnd sigstoreVerifyCode 0xA66 svL8aa66 = some 0xA6A := by
  simp only [svL8aa66]
  rw [blockEnd, sv_at_a66]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL8aaa8 : List BInstr :=
  [.aluImm .add a0 sp 0xD1, .aluImm .add a1 sp 0x420, .aluImm .add a2 x0 0x5F]
theorem svL8aaa8_end : blockEnd sigstoreVerifyCode 0xAA8 svL8aaa8 = some 0xAB4 := by
  simp only [svL8aaa8]
  rw [blockEnd, sv_at_aa8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_aac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_ab0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL8aad8 : List BInstr :=
  [.aluImm .add a0 a0 0x3C]
theorem svL8aad8_end : blockEnd sigstoreVerifyCode 0xAD8 svL8aad8 = some 0xADC := by
  simp only [svL8aad8]
  rw [blockEnd, sv_at_ad8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL8aade : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x80]
theorem svL8aade_end : blockEnd sigstoreVerifyCode 0xADE svL8aade = some 0xAE2 := by
  simp only [svL8aade]
  rw [blockEnd, sv_at_ade]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_l8a {B out bp x9 x21 x25 x26 rootp trl sgp : Word} {sr ss : Bytes} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w84 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xA44 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (q0_a21 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0))
    (q0_a51 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0)) :
    (¬ (True) ∧ SvErrRet B out v n0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xAE2 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = x9 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x80 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (24 : Fin 32) = trl ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (rootp) + BitVec.ofNat 32 0x3C ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = x21 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4), (0xCC, 0x4), (0x130, 0x4), (0x7C, 0x4)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xA44
  obtain ⟨n1, c1, u1⟩ := s0.block svL8aa44 E0.self svL8aa44_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xA54 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svL8aa44 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_9 : reg n1 (9 : Fin 32) = x9 := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svL8aa44, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA22 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svL8aa44, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x5F := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svL8aa44, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m1]; exact w0_24
  have w1_28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m1]; exact w0_28
  have w1_2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m1]; exact w0_2c
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m1]; exact w0_34
  have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m1]; exact w0_38
  have w1_3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m1]; exact w0_3c
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m1]; exact w0_40
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have w1_54 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m1]; exact w0_54
  have w1_58 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m1]; exact w0_58
  have w1_5c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m1]; exact w0_5c
  have w1_60 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m1]; exact w0_60
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m1]; exact w0_64
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m1]; exact w0_68
  have w1_6c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m1]; exact w0_6c
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m1]; exact w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m1]; exact w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m1]; exact w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m1]; exact w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m1]; exact w0_84
  have q1_a21 : ∀ j, j < 48 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m1]; exact q0_a21 j hj
  have q1_a51 : ∀ j, j < 48 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m1]; exact q0_a51 j hj
  -- 0xA54: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := sv_mc (c := 0x420) (d := 0xA22) (N := 0x5F) F E1 s1 sv_at_a54 sv_at_a58
    (by decide) (by decide) g1_2 g1_10 g1_11 g1_12
    (by decide) (by decide) (by decide)
  have s2 := P2.st
  have fr2 := P2.fr
  have t2 : Steps n0 n2 := t1.trans P2.steps
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [P2.regs sp (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P2.regs (3 : Fin 32) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P2.regs (4 : Fin 32) (by decide), g1_4]
  have g2_9 : reg n2 (9 : Fin 32) = x9 := by rw [P2.regs (9 : Fin 32) (by decide), g1_9]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [P2.regs (18 : Fin 32) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [P2.regs (19 : Fin 32) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [P2.regs (20 : Fin 32) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [P2.regs (21 : Fin 32) (by decide), g1_21]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [P2.regs (25 : Fin 32) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [P2.regs (26 : Fin 32) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P2.regs (27 : Fin 32) (by decide), g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x5F)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K2.w32 (by decide) (by decide)).trans w1_24
  have w2_28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K2.w32 (by decide) (by decide)).trans w1_28
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K2.w32 (by decide) (by decide)).trans w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K2.w32 (by decide) (by decide)).trans w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K2.w32 (by decide) (by decide)).trans w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K2.w32 (by decide) (by decide)).trans w1_38
  have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K2.w32 (by decide) (by decide)).trans w1_3c
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K2.w32 (by decide) (by decide)).trans w1_40
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K2.w32 (by decide) (by decide)).trans w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K2.w32 (by decide) (by decide)).trans w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K2.w32 (by decide) (by decide)).trans w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K2.w32 (by decide) (by decide)).trans w1_50
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K2.w32 (by decide) (by decide)).trans w1_54
  have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K2.w32 (by decide) (by decide)).trans w1_58
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K2.w32 (by decide) (by decide)).trans w1_5c
  have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K2.w32 (by decide) (by decide)).trans w1_60
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K2.w32 (by decide) (by decide)).trans w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K2.w32 (by decide) (by decide)).trans w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K2.w32 (by decide) (by decide)).trans w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K2.w32 (by decide) (by decide)).trans w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K2.w32 (by decide) (by decide)).trans w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K2.w32 (by decide) (by decide)).trans w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K2.w32 (by decide) (by decide)).trans w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K2.w32 (by decide) (by decide)).trans w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K2.w32 (by decide) (by decide)).trans w1_84
  have q2_a21 : ∀ j, j < 48 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_a21 j hj)
  have q2_a51 : ∀ j, j < 48 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K2.range (by decide) (by decide) j hj).trans (q1_a51 j hj)
  have q2_420 : ∀ j, j < 47 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by
    rw [show 0x420 + j = 0x420 + (0x0 + j) by omega, X2 (0x0 + j) (by omega),
      show 0xA22 + (0x0 + j) = 0xA21 + (1 + j) by omega]; exact q1_a21 (1 + j) (by omega)
  have q2_44f : ∀ j, j < 48 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by
    rw [show 0x44F + j = 0x420 + (0x2F + j) by omega, X2 (0x2F + j) (by omega),
      show 0xA22 + (0x2F + j) = 0xA51 + j by omega]; exact q1_a51 j (by omega)
  clear q1_a51 q1_a21 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_21 g1_20 g1_19 g1_18 g1_9 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0xA5C: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_a5c (off' := 0xA5E) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0xA5E (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_9 : reg n3 (9 : Fin 32) = x9 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_24 : reg n3 (24 : Fin 32) = trl := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr, w2_78]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x5F)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m3]; exact w2_24
  have w3_28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m3]; exact w2_28
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m3]; exact w2_2c
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m3]; exact w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m3]; exact w2_38
  have w3_3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m3]; exact w2_3c
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m3]; exact w2_40
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m3]; exact w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m3]; exact w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m3]; exact w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m3]; exact w2_54
  have w3_58 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m3]; exact w2_58
  have w3_5c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m3]; exact w2_5c
  have w3_60 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m3]; exact w2_60
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m3]; exact w2_68
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m3]; exact w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m3]; exact w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m3]; exact w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m3]; exact w2_84
  have q3_420 : ∀ j, j < 47 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m3]; exact q2_420 j hj
  have q3_44f : ∀ j, j < 48 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m3]; exact q2_44f j hj
  have q3_a21 : ∀ j, j < 48 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m3]; exact q2_a21 j hj
  have q3_a51 : ∀ j, j < 48 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m3]; exact q2_a51 j hj
  clear q2_44f q2_420 q2_a51 q2_a21 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_44 w2_40 w2_3c w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 g2_27 g2_26 g2_25 g2_21 g2_20 g2_19 g2_18 g2_9 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0xA5E
  obtain ⟨n4, c4, u4⟩ := s3.block svL8aa5e E3.self svL8aa5e_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0xA62 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svL8aa5e (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_9 : reg n4 (9 : Fin 32) = x9 := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb4, runBlock_reg _ _ _ (20 : Fin 32) s3.zero (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_24 : reg n4 (24 : Fin 32) = trl := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_10 : reg n4 a0 = (trl) >>> 8 := by
    rw [rb4, ← g3_24]; rfl
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x5F)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m4]; exact w3_24
  have w4_28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m4]; exact w3_28
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m4]; exact w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m4]; exact w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m4]; exact w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m4]; exact w3_38
  have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m4]; exact w3_3c
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m4]; exact w3_40
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m4]; exact w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m4]; exact w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m4]; exact w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m4]; exact w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m4]; exact w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m4]; exact w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m4]; exact w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m4]; exact w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m4]; exact w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m4]; exact w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m4]; exact w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m4]; exact w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m4]; exact w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m4]; exact w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m4]; exact w3_84
  have q4_420 : ∀ j, j < 47 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m4]; exact q3_420 j hj
  have q4_44f : ∀ j, j < 48 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m4]; exact q3_44f j hj
  have q4_a21 : ∀ j, j < 48 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m4]; exact q3_a21 j hj
  have q4_a51 : ∀ j, j < 48 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m4]; exact q3_a51 j hj
  clear q3_a51 q3_a21 q3_44f q3_420 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 g3_24 g3_27 g3_26 g3_25 g3_21 g3_20 g3_19 g3_18 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xA62
  obtain ⟨n5, c5, u5⟩ := s4.block svL8aa62 E4.self svL8aa62_end
    ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0xA66 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svL8aa62 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by
    rw [rb5, runBlock_reg _ _ _ sp s4.zero (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (3 : Fin 32) s4.zero (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (4 : Fin 32) s4.zero (by decide), g4_4]
  have g5_9 : reg n5 (9 : Fin 32) = x9 := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_10 : reg n5 a0 = (trl) >>> 8 := by
    rw [rb5, runBlock_reg _ _ _ a0 s4.zero (by decide), g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_24 : reg n5 (24 : Fin 32) = trl := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_11 : reg n5 a1 = (trl) >>> 16 := by
    rw [rb5, ← g4_24]; rfl
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x5F)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m5]; exact w4_24
  have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m5]; exact w4_28
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m5]; exact w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m5]; exact w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m5]; exact w4_38
  have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m5]; exact w4_3c
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m5]; exact w4_40
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m5]; exact w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m5]; exact w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m5]; exact w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m5]; exact w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m5]; exact w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m5]; exact w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m5]; exact w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m5]; exact w4_84
  have q5_420 : ∀ j, j < 47 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_420 j hj
  have q5_44f : ∀ j, j < 48 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m5]; exact q4_44f j hj
  have q5_a21 : ∀ j, j < 48 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m5]; exact q4_a21 j hj
  have q5_a51 : ∀ j, j < 48 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m5]; exact q4_a51 j hj
  clear q4_a51 q4_a21 q4_44f q4_420 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 g4_10 g4_27 g4_26 g4_25 g4_24 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0xA66
  obtain ⟨n6, c6, u6⟩ := s5.block svL8aa66 E5.self svL8aa66_end
    ⟨trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0xA6A (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svL8aa66 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by
    rw [rb6, runBlock_reg _ _ _ sp s5.zero (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (3 : Fin 32) s5.zero (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (4 : Fin 32) s5.zero (by decide), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = x9 := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
  have g6_10 : reg n6 a0 = (trl) >>> 8 := by
    rw [rb6, runBlock_reg _ _ _ a0 s5.zero (by decide), g5_10]
  have g6_11 : reg n6 a1 = (trl) >>> 16 := by
    rw [rb6, runBlock_reg _ _ _ a1 s5.zero (by decide), g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb6, runBlock_reg _ _ _ (20 : Fin 32) s5.zero (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_24 : reg n6 (24 : Fin 32) = trl := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_12 : reg n6 a2 = (trl) >>> 24 := by
    rw [rb6, ← g5_24]; rfl
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x5F)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m6]; exact w5_24
  have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m6]; exact w5_28
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m6]; exact w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m6]; exact w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m6]; exact w5_38
  have w6_3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m6]; exact w5_3c
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m6]; exact w5_40
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m6]; exact w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m6]; exact w5_54
  have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m6]; exact w5_58
  have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m6]; exact w5_5c
  have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m6]; exact w5_60
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m6]; exact w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m6]; exact w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m6]; exact w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m6]; exact w5_84
  have q6_420 : ∀ j, j < 47 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_420 j hj
  have q6_44f : ∀ j, j < 48 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m6]; exact q5_44f j hj
  have q6_a21 : ∀ j, j < 48 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m6]; exact q5_a21 j hj
  have q6_a51 : ∀ j, j < 48 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m6]; exact q5_a51 j hj
  clear q5_a51 q5_a21 q5_44f q5_420 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 g5_11 g5_27 g5_26 g5_25 g5_24 g5_21 g5_20 g5_19 g5_18 g5_10 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0xA6A: sb
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sb F E6 s6 sv_at_a6a (off' := 0xA6E) (c := 0x8D)
    (by decide) (by rw [g6_2]; sv_addr) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_9 : reg n7 (9 : Fin 32) = x9 := by rw [rg7 (9 : Fin 32), g6_9]
  have g7_10 : reg n7 a0 = (trl) >>> 8 := by rw [rg7 a0, g6_10]
  have g7_11 : reg n7 a1 = (trl) >>> 16 := by rw [rg7 a1, g6_11]
  have g7_12 : reg n7 a2 = (trl) >>> 24 := by rw [rg7 a2, g6_12]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rg7 (19 : Fin 32), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg7 (20 : Fin 32), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [rg7 (21 : Fin 32), g6_21]
  have g7_24 : reg n7 (24 : Fin 32) = trl := by rw [rg7 (24 : Fin 32), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [rg7 (25 : Fin 32), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rg7 (26 : Fin 32), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg7 (27 : Fin 32), g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x5F), (0x8D, 0x1)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K7.w32 (by decide) (by decide)).trans w6_24
  have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K7.w32 (by decide) (by decide)).trans w6_28
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K7.w32 (by decide) (by decide)).trans w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K7.w32 (by decide) (by decide)).trans w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K7.w32 (by decide) (by decide)).trans w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K7.w32 (by decide) (by decide)).trans w6_38
  have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K7.w32 (by decide) (by decide)).trans w6_3c
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K7.w32 (by decide) (by decide)).trans w6_40
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K7.w32 (by decide) (by decide)).trans w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K7.w32 (by decide) (by decide)).trans w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K7.w32 (by decide) (by decide)).trans w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K7.w32 (by decide) (by decide)).trans w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K7.w32 (by decide) (by decide)).trans w6_54
  have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K7.w32 (by decide) (by decide)).trans w6_58
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K7.w32 (by decide) (by decide)).trans w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K7.w32 (by decide) (by decide)).trans w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K7.w32 (by decide) (by decide)).trans w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K7.w32 (by decide) (by decide)).trans w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K7.w32 (by decide) (by decide)).trans w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K7.w32 (by decide) (by decide)).trans w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K7.w32 (by decide) (by decide)).trans w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K7.w32 (by decide) (by decide)).trans w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K7.w32 (by decide) (by decide)).trans w6_84
  have b7_8d : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [W7, g6_10]
  have q7_420 : ∀ j, j < 47 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_420 j hj)
  have q7_44f : ∀ j, j < 48 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_44f j hj)
  have q7_a21 : ∀ j, j < 48 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_a21 j hj)
  have q7_a51 : ∀ j, j < 48 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_a51 j hj)
  clear q6_a51 q6_a21 q6_44f q6_420 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 g6_12 g6_27 g6_26 g6_25 g6_24 g6_21 g6_20 g6_19 g6_18 g6_11 g6_10 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0xA6E: sb
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sb F E7 s7 sv_at_a6e (off' := 0xA72) (c := 0x8E)
    (by decide) (by rw [g7_2]; sv_addr) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = x9 := by rw [rg8 (9 : Fin 32), g7_9]
  have g8_10 : reg n8 a0 = (trl) >>> 8 := by rw [rg8 a0, g7_10]
  have g8_11 : reg n8 a1 = (trl) >>> 16 := by rw [rg8 a1, g7_11]
  have g8_12 : reg n8 a2 = (trl) >>> 24 := by rw [rg8 a2, g7_12]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_24 : reg n8 (24 : Fin 32) = trl := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg8 (27 : Fin 32), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K8.w32 (by decide) (by decide)).trans w7_24
  have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K8.w32 (by decide) (by decide)).trans w7_28
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K8.w32 (by decide) (by decide)).trans w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K8.w32 (by decide) (by decide)).trans w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K8.w32 (by decide) (by decide)).trans w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K8.w32 (by decide) (by decide)).trans w7_38
  have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K8.w32 (by decide) (by decide)).trans w7_3c
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K8.w32 (by decide) (by decide)).trans w7_40
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K8.w32 (by decide) (by decide)).trans w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K8.w32 (by decide) (by decide)).trans w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K8.w32 (by decide) (by decide)).trans w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K8.w32 (by decide) (by decide)).trans w7_50
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K8.w32 (by decide) (by decide)).trans w7_54
  have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K8.w32 (by decide) (by decide)).trans w7_58
  have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K8.w32 (by decide) (by decide)).trans w7_5c
  have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K8.w32 (by decide) (by decide)).trans w7_60
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K8.w32 (by decide) (by decide)).trans w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K8.w32 (by decide) (by decide)).trans w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K8.w32 (by decide) (by decide)).trans w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K8.w32 (by decide) (by decide)).trans w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K8.w32 (by decide) (by decide)).trans w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K8.w32 (by decide) (by decide)).trans w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K8.w32 (by decide) (by decide)).trans w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K8.w32 (by decide) (by decide)).trans w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K8.w32 (by decide) (by decide)).trans w7_84
  have b8_8d : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K8.b8 (by decide) (by decide)).trans b7_8d
  have b8_8e : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [W8, g7_11]
  have q8_420 : ∀ j, j < 47 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_420 j hj)
  have q8_44f : ∀ j, j < 48 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_44f j hj)
  have q8_a21 : ∀ j, j < 48 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_a21 j hj)
  have q8_a51 : ∀ j, j < 48 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_a51 j hj)
  clear q7_a51 q7_a21 q7_44f q7_420 b7_8d w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 g7_27 g7_26 g7_25 g7_24 g7_21 g7_20 g7_19 g7_18 g7_12 g7_11 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0xA72: sb
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sb F E8 s8 sv_at_a72 (off' := 0xA76) (c := 0x8F)
    (by decide) (by rw [g8_2]; sv_addr) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_9 : reg n9 (9 : Fin 32) = x9 := by rw [rg9 (9 : Fin 32), g8_9]
  have g9_10 : reg n9 a0 = (trl) >>> 8 := by rw [rg9 a0, g8_10]
  have g9_11 : reg n9 a1 = (trl) >>> 16 := by rw [rg9 a1, g8_11]
  have g9_12 : reg n9 a2 = (trl) >>> 24 := by rw [rg9 a2, g8_12]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg9 (20 : Fin 32), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rg9 (21 : Fin 32), g8_21]
  have g9_24 : reg n9 (24 : Fin 32) = trl := by rw [rg9 (24 : Fin 32), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [rg9 (25 : Fin 32), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rg9 (26 : Fin 32), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg9 (27 : Fin 32), g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K9.w32 (by decide) (by decide)).trans w8_24
  have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K9.w32 (by decide) (by decide)).trans w8_28
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K9.w32 (by decide) (by decide)).trans w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K9.w32 (by decide) (by decide)).trans w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K9.w32 (by decide) (by decide)).trans w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K9.w32 (by decide) (by decide)).trans w8_38
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K9.w32 (by decide) (by decide)).trans w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K9.w32 (by decide) (by decide)).trans w8_40
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K9.w32 (by decide) (by decide)).trans w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K9.w32 (by decide) (by decide)).trans w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K9.w32 (by decide) (by decide)).trans w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K9.w32 (by decide) (by decide)).trans w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K9.w32 (by decide) (by decide)).trans w8_54
  have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K9.w32 (by decide) (by decide)).trans w8_58
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K9.w32 (by decide) (by decide)).trans w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K9.w32 (by decide) (by decide)).trans w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K9.w32 (by decide) (by decide)).trans w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K9.w32 (by decide) (by decide)).trans w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K9.w32 (by decide) (by decide)).trans w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K9.w32 (by decide) (by decide)).trans w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K9.w32 (by decide) (by decide)).trans w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K9.w32 (by decide) (by decide)).trans w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K9.w32 (by decide) (by decide)).trans w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K9.w32 (by decide) (by decide)).trans w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K9.w32 (by decide) (by decide)).trans w8_84
  have b9_8d : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K9.b8 (by decide) (by decide)).trans b8_8d
  have b9_8e : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K9.b8 (by decide) (by decide)).trans b8_8e
  have b9_8f : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [W9, g8_12]
  have q9_420 : ∀ j, j < 47 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_420 j hj)
  have q9_44f : ∀ j, j < 48 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_44f j hj)
  have q9_a21 : ∀ j, j < 48 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_a21 j hj)
  have q9_a51 : ∀ j, j < 48 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_a51 j hj)
  clear q8_a51 q8_a21 q8_44f q8_420 b8_8e b8_8d w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_3c w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 g8_27 g8_26 g8_25 g8_24 g8_21 g8_20 g8_19 g8_18 g8_12 g8_11 g8_10 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0xA76: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_a76 (off' := 0xA78) (by decide)
    (by rw [g9_2, show B + 0x21A0 + 0x5C = B + 0x21A0 + BitVec.ofNat 32 0x5C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s10 : St n10.mem SV n10 0xA78 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
  have g10_9 : reg n10 (9 : Fin 32) = x9 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
  have g10_11 : reg n10 a1 = (trl) >>> 16 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_11]
  have g10_12 : reg n10 a2 = (trl) >>> 24 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_12]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
  have g10_24 : reg n10 (24 : Fin 32) = trl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
  have g10_10 : reg n10 a0 = w5c := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_2, show B + 0x21A0 + 0x5C = B + 0x21A0 + BitVec.ofNat 32 0x5C by sv_addr, w9_5c]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m10]; exact w9_24
  have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m10]; exact w9_28
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m10]; exact w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m10]; exact w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m10]; exact w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m10]; exact w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m10]; exact w9_40
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m10]; exact w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m10]; exact w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m10]; exact w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m10]; exact w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m10]; exact w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m10]; exact w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m10]; exact w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m10]; exact w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m10]; exact w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m10]; exact w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m10]; exact w9_84
  have b10_8d : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m10]; exact b9_8d
  have b10_8e : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m10]; exact b9_8e
  have b10_8f : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m10]; exact b9_8f
  have q10_420 : ∀ j, j < 47 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_420 j hj
  have q10_44f : ∀ j, j < 48 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m10]; exact q9_44f j hj
  have q10_a21 : ∀ j, j < 48 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m10]; exact q9_a21 j hj
  have q10_a51 : ∀ j, j < 48 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m10]; exact q9_a51 j hj
  clear q9_a51 q9_a21 q9_44f q9_420 b9_8f b9_8e b9_8d w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_3c w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 g9_27 g9_26 g9_25 g9_24 g9_21 g9_20 g9_19 g9_18 g9_12 g9_11 g9_10 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  -- 0xA78: sw
  obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := sv_sw F E10 s10 sv_at_a78 (off' := 0xA7A) (c := 0x90)
    (by decide) (by rw [g10_2]; sv_addr) (by decide) (by decide)
  have t11 : Steps n0 n11 := t10.trans d11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
  have g11_9 : reg n11 (9 : Fin 32) = x9 := by rw [rg11 (9 : Fin 32), g10_9]
  have g11_10 : reg n11 a0 = w5c := by rw [rg11 a0, g10_10]
  have g11_11 : reg n11 a1 = (trl) >>> 16 := by rw [rg11 a1, g10_11]
  have g11_12 : reg n11 a2 = (trl) >>> 24 := by rw [rg11 a2, g10_12]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rg11 (18 : Fin 32), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rg11 (19 : Fin 32), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg11 (20 : Fin 32), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [rg11 (21 : Fin 32), g10_21]
  have g11_24 : reg n11 (24 : Fin 32) = trl := by rw [rg11 (24 : Fin 32), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [rg11 (25 : Fin 32), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [rg11 (26 : Fin 32), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg11 (27 : Fin 32), g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K11.w32 (by decide) (by decide)).trans w10_24
  have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K11.w32 (by decide) (by decide)).trans w10_28
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K11.w32 (by decide) (by decide)).trans w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K11.w32 (by decide) (by decide)).trans w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K11.w32 (by decide) (by decide)).trans w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K11.w32 (by decide) (by decide)).trans w10_38
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K11.w32 (by decide) (by decide)).trans w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K11.w32 (by decide) (by decide)).trans w10_40
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K11.w32 (by decide) (by decide)).trans w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K11.w32 (by decide) (by decide)).trans w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K11.w32 (by decide) (by decide)).trans w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K11.w32 (by decide) (by decide)).trans w10_50
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K11.w32 (by decide) (by decide)).trans w10_54
  have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K11.w32 (by decide) (by decide)).trans w10_58
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K11.w32 (by decide) (by decide)).trans w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K11.w32 (by decide) (by decide)).trans w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K11.w32 (by decide) (by decide)).trans w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K11.w32 (by decide) (by decide)).trans w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K11.w32 (by decide) (by decide)).trans w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K11.w32 (by decide) (by decide)).trans w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K11.w32 (by decide) (by decide)).trans w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K11.w32 (by decide) (by decide)).trans w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K11.w32 (by decide) (by decide)).trans w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K11.w32 (by decide) (by decide)).trans w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K11.w32 (by decide) (by decide)).trans w10_84
  have b11_8d : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_8d
  have b11_8e : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_8e
  have b11_8f : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_8f
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [W11, g10_10]
  have q11_420 : ∀ j, j < 47 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_420 j hj)
  have q11_44f : ∀ j, j < 48 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_44f j hj)
  have q11_a21 : ∀ j, j < 48 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_a21 j hj)
  have q11_a51 : ∀ j, j < 48 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_a51 j hj)
  clear q10_a51 q10_a21 q10_44f q10_420 b10_8f b10_8e b10_8d w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 g10_10 g10_27 g10_26 g10_25 g10_24 g10_21 g10_20 g10_19 g10_18 g10_12 g10_11 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0xA7A: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_a7a (off' := 0xA7C) (c := 0x94)
    (by decide) (by rw [g11_2]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_9 : reg n12 (9 : Fin 32) = x9 := by rw [rg12 (9 : Fin 32), g11_9]
  have g12_10 : reg n12 a0 = w5c := by rw [rg12 a0, g11_10]
  have g12_11 : reg n12 a1 = (trl) >>> 16 := by rw [rg12 a1, g11_11]
  have g12_12 : reg n12 a2 = (trl) >>> 24 := by rw [rg12 a2, g11_12]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg12 (20 : Fin 32), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_24 : reg n12 (24 : Fin 32) = trl := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K12.w32 (by decide) (by decide)).trans w11_24
  have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K12.w32 (by decide) (by decide)).trans w11_28
  have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K12.w32 (by decide) (by decide)).trans w11_2c
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K12.w32 (by decide) (by decide)).trans w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K12.w32 (by decide) (by decide)).trans w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K12.w32 (by decide) (by decide)).trans w11_38
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K12.w32 (by decide) (by decide)).trans w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K12.w32 (by decide) (by decide)).trans w11_40
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K12.w32 (by decide) (by decide)).trans w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K12.w32 (by decide) (by decide)).trans w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K12.w32 (by decide) (by decide)).trans w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K12.w32 (by decide) (by decide)).trans w11_50
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K12.w32 (by decide) (by decide)).trans w11_54
  have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K12.w32 (by decide) (by decide)).trans w11_58
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K12.w32 (by decide) (by decide)).trans w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K12.w32 (by decide) (by decide)).trans w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K12.w32 (by decide) (by decide)).trans w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K12.w32 (by decide) (by decide)).trans w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K12.w32 (by decide) (by decide)).trans w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K12.w32 (by decide) (by decide)).trans w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K12.w32 (by decide) (by decide)).trans w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K12.w32 (by decide) (by decide)).trans w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K12.w32 (by decide) (by decide)).trans w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K12.w32 (by decide) (by decide)).trans w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K12.w32 (by decide) (by decide)).trans w11_84
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K12.w32 (by decide) (by decide)).trans w11_90
  have b12_8d : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K12.b8 (by decide) (by decide)).trans b11_8d
  have b12_8e : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K12.b8 (by decide) (by decide)).trans b11_8e
  have b12_8f : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K12.b8 (by decide) (by decide)).trans b11_8f
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [W12, g11_25]
  have q12_420 : ∀ j, j < 47 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K12.range (by decide) (by decide) j hj).trans (q11_420 j hj)
  have q12_44f : ∀ j, j < 48 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K12.range (by decide) (by decide) j hj).trans (q11_44f j hj)
  have q12_a21 : ∀ j, j < 48 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K12.range (by decide) (by decide) j hj).trans (q11_a21 j hj)
  have q12_a51 : ∀ j, j < 48 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K12.range (by decide) (by decide) j hj).trans (q11_a51 j hj)
  clear q11_a51 q11_a21 q11_44f q11_420 w11_90 b11_8f b11_8e b11_8d w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 g11_27 g11_26 g11_25 g11_24 g11_21 g11_20 g11_19 g11_18 g11_12 g11_11 g11_10 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
  -- 0xA7C: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_a7c (off' := 0xA7E) (by decide)
    (by rw [g12_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0xA7E (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_9 : reg n13 (9 : Fin 32) = x9 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_9]
  have g13_11 : reg n13 a1 = (trl) >>> 16 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_11]
  have g13_12 : reg n13 a2 = (trl) >>> 24 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_12]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_24 : reg n13 (24 : Fin 32) = trl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_10 : reg n13 a0 = w48 := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w12_48]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m13]; exact w12_24
  have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m13]; exact w12_28
  have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m13]; exact w12_2c
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m13]; exact w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m13]; exact w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m13]; exact w12_38
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m13]; exact w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m13]; exact w12_40
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m13]; exact w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m13]; exact w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m13]; exact w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m13]; exact w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m13]; exact w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m13]; exact w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m13]; exact w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m13]; exact w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m13]; exact w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m13]; exact w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m13]; exact w12_84
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m13]; exact w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m13]; exact w12_94
  have b13_8d : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m13]; exact b12_8d
  have b13_8e : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m13]; exact b12_8e
  have b13_8f : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m13]; exact b12_8f
  have q13_420 : ∀ j, j < 47 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_420 j hj
  have q13_44f : ∀ j, j < 48 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m13]; exact q12_44f j hj
  have q13_a21 : ∀ j, j < 48 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m13]; exact q12_a21 j hj
  have q13_a51 : ∀ j, j < 48 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m13]; exact q12_a51 j hj
  clear q12_a51 q12_a21 q12_44f q12_420 w12_94 b12_8f b12_8e b12_8d w12_90 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_3c w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 g12_27 g12_26 g12_25 g12_24 g12_21 g12_20 g12_19 g12_18 g12_12 g12_11 g12_10 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0xA7E: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_a7e (off' := 0xA80) (c := 0x98)
    (by decide) (by rw [g13_2]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_9 : reg n14 (9 : Fin 32) = x9 := by rw [rg14 (9 : Fin 32), g13_9]
  have g14_10 : reg n14 a0 = w48 := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = (trl) >>> 16 := by rw [rg14 a1, g13_11]
  have g14_12 : reg n14 a2 = (trl) >>> 24 := by rw [rg14 a2, g13_12]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_24 : reg n14 (24 : Fin 32) = trl := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K14.w32 (by decide) (by decide)).trans w13_24
  have w14_28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K14.w32 (by decide) (by decide)).trans w13_28
  have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K14.w32 (by decide) (by decide)).trans w13_2c
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K14.w32 (by decide) (by decide)).trans w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K14.w32 (by decide) (by decide)).trans w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K14.w32 (by decide) (by decide)).trans w13_38
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K14.w32 (by decide) (by decide)).trans w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K14.w32 (by decide) (by decide)).trans w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K14.w32 (by decide) (by decide)).trans w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K14.w32 (by decide) (by decide)).trans w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K14.w32 (by decide) (by decide)).trans w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K14.w32 (by decide) (by decide)).trans w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K14.w32 (by decide) (by decide)).trans w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K14.w32 (by decide) (by decide)).trans w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K14.w32 (by decide) (by decide)).trans w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K14.w32 (by decide) (by decide)).trans w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K14.w32 (by decide) (by decide)).trans w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K14.w32 (by decide) (by decide)).trans w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K14.w32 (by decide) (by decide)).trans w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K14.w32 (by decide) (by decide)).trans w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K14.w32 (by decide) (by decide)).trans w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K14.w32 (by decide) (by decide)).trans w13_84
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K14.w32 (by decide) (by decide)).trans w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K14.w32 (by decide) (by decide)).trans w13_94
  have b14_8d : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_8d
  have b14_8e : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_8e
  have b14_8f : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_8f
  have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [W14, g13_10]
  have q14_420 : ∀ j, j < 47 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_420 j hj)
  have q14_44f : ∀ j, j < 48 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_44f j hj)
  have q14_a21 : ∀ j, j < 48 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_a21 j hj)
  have q14_a51 : ∀ j, j < 48 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_a51 j hj)
  clear q13_a51 q13_a21 q13_44f q13_420 b13_8f b13_8e b13_8d w13_94 w13_90 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_3c w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 g13_10 g13_27 g13_26 g13_25 g13_24 g13_21 g13_20 g13_19 g13_18 g13_12 g13_11 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0xA80: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_a80 (off' := 0xA82) (by decide)
    (by rw [g14_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0xA82 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_9 : reg n15 (9 : Fin 32) = x9 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
  have g15_11 : reg n15 a1 = (trl) >>> 16 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_11]
  have g15_12 : reg n15 a2 = (trl) >>> 24 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_12]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_24 : reg n15 (24 : Fin 32) = trl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_10 : reg n15 a0 = w34 := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr, w14_34]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m15]; exact w14_24
  have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m15]; exact w14_28
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m15]; exact w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m15]; exact w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m15]; exact w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m15]; exact w14_38
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m15]; exact w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m15]; exact w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m15]; exact w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m15]; exact w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m15]; exact w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m15]; exact w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m15]; exact w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m15]; exact w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m15]; exact w14_84
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m15]; exact w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m15]; exact w14_94
  have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m15]; exact w14_98
  have b15_8d : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m15]; exact b14_8d
  have b15_8e : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m15]; exact b14_8e
  have b15_8f : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m15]; exact b14_8f
  have q15_420 : ∀ j, j < 47 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m15]; exact q14_420 j hj
  have q15_44f : ∀ j, j < 48 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m15]; exact q14_44f j hj
  have q15_a21 : ∀ j, j < 48 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m15]; exact q14_a21 j hj
  have q15_a51 : ∀ j, j < 48 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m15]; exact q14_a51 j hj
  clear q14_a51 q14_a21 q14_44f q14_420 w14_98 b14_8f b14_8e b14_8d w14_94 w14_90 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 g14_27 g14_26 g14_25 g14_24 g14_21 g14_20 g14_19 g14_18 g14_12 g14_11 g14_10 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0xA82: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_a82 (off' := 0xA84) (c := 0x9C)
    (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_9 : reg n16 (9 : Fin 32) = x9 := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_10 : reg n16 a0 = w34 := by rw [rg16 a0, g15_10]
  have g16_11 : reg n16 a1 = (trl) >>> 16 := by rw [rg16 a1, g15_11]
  have g16_12 : reg n16 a2 = (trl) >>> 24 := by rw [rg16 a2, g15_12]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg16 (20 : Fin 32), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_24 : reg n16 (24 : Fin 32) = trl := by rw [rg16 (24 : Fin 32), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [rg16 (25 : Fin 32), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K16.w32 (by decide) (by decide)).trans w15_24
  have w16_28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K16.w32 (by decide) (by decide)).trans w15_28
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K16.w32 (by decide) (by decide)).trans w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K16.w32 (by decide) (by decide)).trans w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K16.w32 (by decide) (by decide)).trans w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K16.w32 (by decide) (by decide)).trans w15_38
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K16.w32 (by decide) (by decide)).trans w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K16.w32 (by decide) (by decide)).trans w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K16.w32 (by decide) (by decide)).trans w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K16.w32 (by decide) (by decide)).trans w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K16.w32 (by decide) (by decide)).trans w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K16.w32 (by decide) (by decide)).trans w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K16.w32 (by decide) (by decide)).trans w15_54
  have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K16.w32 (by decide) (by decide)).trans w15_58
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K16.w32 (by decide) (by decide)).trans w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K16.w32 (by decide) (by decide)).trans w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K16.w32 (by decide) (by decide)).trans w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K16.w32 (by decide) (by decide)).trans w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K16.w32 (by decide) (by decide)).trans w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K16.w32 (by decide) (by decide)).trans w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K16.w32 (by decide) (by decide)).trans w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K16.w32 (by decide) (by decide)).trans w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K16.w32 (by decide) (by decide)).trans w15_84
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K16.w32 (by decide) (by decide)).trans w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K16.w32 (by decide) (by decide)).trans w15_94
  have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K16.w32 (by decide) (by decide)).trans w15_98
  have b16_8d : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_8d
  have b16_8e : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_8e
  have b16_8f : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_8f
  have w16_9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [W16, g15_10]
  have q16_420 : ∀ j, j < 47 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_420 j hj)
  have q16_44f : ∀ j, j < 48 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_44f j hj)
  have q16_a21 : ∀ j, j < 48 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_a21 j hj)
  have q16_a51 : ∀ j, j < 48 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_a51 j hj)
  clear q15_a51 q15_a21 q15_44f q15_420 b15_8f b15_8e b15_8d w15_98 w15_94 w15_90 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_38 w15_34 w15_30 w15_2c w15_28 w15_24 g15_10 g15_27 g15_26 g15_25 g15_24 g15_21 g15_20 g15_19 g15_18 g15_12 g15_11 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0xA84: lw
  obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_a84 (off' := 0xA86) (by decide)
    (by rw [g16_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s17 : St n17.mem SV n17 0xA86 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
  have g17_9 : reg n17 (9 : Fin 32) = x9 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
  have g17_11 : reg n17 a1 = (trl) >>> 16 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_11]
  have g17_12 : reg n17 a2 = (trl) >>> 24 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_12]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
  have g17_24 : reg n17 (24 : Fin 32) = trl := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
  have g17_10 : reg n17 a0 = w44 := by
    rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g16_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w16_44]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m17]; exact w16_24
  have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m17]; exact w16_28
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m17]; exact w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m17]; exact w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m17]; exact w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m17]; exact w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m17]; exact w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m17]; exact w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m17]; exact w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m17]; exact w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m17]; exact w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m17]; exact w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m17]; exact w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m17]; exact w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m17]; exact w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m17]; exact w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m17]; exact w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m17]; exact w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m17]; exact w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m17]; exact w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m17]; exact w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m17]; exact w16_84
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m17]; exact w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m17]; exact w16_94
  have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m17]; exact w16_98
  have w17_9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m17]; exact w16_9c
  have b17_8d : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m17]; exact b16_8d
  have b17_8e : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m17]; exact b16_8e
  have b17_8f : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m17]; exact b16_8f
  have q17_420 : ∀ j, j < 47 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m17]; exact q16_420 j hj
  have q17_44f : ∀ j, j < 48 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m17]; exact q16_44f j hj
  have q17_a21 : ∀ j, j < 48 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m17]; exact q16_a21 j hj
  have q17_a51 : ∀ j, j < 48 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m17]; exact q16_a51 j hj
  clear q16_a51 q16_a21 q16_44f q16_420 w16_9c b16_8f b16_8e b16_8d w16_98 w16_94 w16_90 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 g16_27 g16_26 g16_25 g16_24 g16_21 g16_20 g16_19 g16_18 g16_12 g16_11 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0xA86: sw
  obtain ⟨n18, d18, s18, fr18, K18, W18, rg18⟩ := sv_sw F E17 s17 sv_at_a86 (off' := 0xA88) (c := 0xA0)
    (by decide) (by rw [g17_2]; sv_addr) (by decide) (by decide)
  have t18 : Steps n0 n18 := t17.trans d18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rg18 sp, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg18 (3 : Fin 32), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg18 (4 : Fin 32), g17_4]
  have g18_9 : reg n18 (9 : Fin 32) = x9 := by rw [rg18 (9 : Fin 32), g17_9]
  have g18_10 : reg n18 a0 = w44 := by rw [rg18 a0, g17_10]
  have g18_11 : reg n18 a1 = (trl) >>> 16 := by rw [rg18 a1, g17_11]
  have g18_12 : reg n18 a2 = (trl) >>> 24 := by rw [rg18 a2, g17_12]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rg18 (18 : Fin 32), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rg18 (19 : Fin 32), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg18 (20 : Fin 32), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [rg18 (21 : Fin 32), g17_21]
  have g18_24 : reg n18 (24 : Fin 32) = trl := by rw [rg18 (24 : Fin 32), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [rg18 (25 : Fin 32), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [rg18 (26 : Fin 32), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg18 (27 : Fin 32), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K18.w32 (by decide) (by decide)).trans w17_24
  have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K18.w32 (by decide) (by decide)).trans w17_28
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K18.w32 (by decide) (by decide)).trans w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K18.w32 (by decide) (by decide)).trans w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K18.w32 (by decide) (by decide)).trans w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K18.w32 (by decide) (by decide)).trans w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K18.w32 (by decide) (by decide)).trans w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K18.w32 (by decide) (by decide)).trans w17_40
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K18.w32 (by decide) (by decide)).trans w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K18.w32 (by decide) (by decide)).trans w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K18.w32 (by decide) (by decide)).trans w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K18.w32 (by decide) (by decide)).trans w17_50
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K18.w32 (by decide) (by decide)).trans w17_54
  have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K18.w32 (by decide) (by decide)).trans w17_58
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K18.w32 (by decide) (by decide)).trans w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K18.w32 (by decide) (by decide)).trans w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K18.w32 (by decide) (by decide)).trans w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K18.w32 (by decide) (by decide)).trans w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K18.w32 (by decide) (by decide)).trans w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K18.w32 (by decide) (by decide)).trans w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K18.w32 (by decide) (by decide)).trans w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K18.w32 (by decide) (by decide)).trans w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K18.w32 (by decide) (by decide)).trans w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K18.w32 (by decide) (by decide)).trans w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K18.w32 (by decide) (by decide)).trans w17_84
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K18.w32 (by decide) (by decide)).trans w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K18.w32 (by decide) (by decide)).trans w17_94
  have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K18.w32 (by decide) (by decide)).trans w17_98
  have w18_9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K18.w32 (by decide) (by decide)).trans w17_9c
  have b18_8d : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_8d
  have b18_8e : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_8e
  have b18_8f : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_8f
  have w18_a0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [W18, g17_10]
  have q18_420 : ∀ j, j < 47 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_420 j hj)
  have q18_44f : ∀ j, j < 48 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_44f j hj)
  have q18_a21 : ∀ j, j < 48 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_a21 j hj)
  have q18_a51 : ∀ j, j < 48 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_a51 j hj)
  clear q17_a51 q17_a21 q17_44f q17_420 b17_8f b17_8e b17_8d w17_9c w17_98 w17_94 w17_90 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 g17_10 g17_27 g17_26 g17_25 g17_24 g17_21 g17_20 g17_19 g17_18 g17_12 g17_11 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0xA88: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_a88 (off' := 0xA8A) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x30 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s19 : St n19.mem SV n19 0xA8A (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_9 : reg n19 (9 : Fin 32) = x9 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
  have g19_11 : reg n19 a1 = (trl) >>> 16 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_11]
  have g19_12 : reg n19 a2 = (trl) >>> 24 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_12]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_24 : reg n19 (24 : Fin 32) = trl := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_10 : reg n19 a0 = w30 := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x30 by sv_addr, w18_30]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m19]; exact w18_24
  have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m19]; exact w18_28
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m19]; exact w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m19]; exact w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m19]; exact w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m19]; exact w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m19]; exact w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m19]; exact w18_40
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m19]; exact w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m19]; exact w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m19]; exact w18_54
  have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m19]; exact w18_58
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m19]; exact w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m19]; exact w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m19]; exact w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m19]; exact w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m19]; exact w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m19]; exact w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m19]; exact w18_84
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m19]; exact w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m19]; exact w18_94
  have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m19]; exact w18_98
  have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m19]; exact w18_9c
  have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m19]; exact w18_a0
  have b19_8d : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m19]; exact b18_8d
  have b19_8e : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m19]; exact b18_8e
  have b19_8f : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m19]; exact b18_8f
  have q19_420 : ∀ j, j < 47 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m19]; exact q18_420 j hj
  have q19_44f : ∀ j, j < 48 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m19]; exact q18_44f j hj
  have q19_a21 : ∀ j, j < 48 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m19]; exact q18_a21 j hj
  have q19_a51 : ∀ j, j < 48 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m19]; exact q18_a51 j hj
  clear q18_a51 q18_a21 q18_44f q18_420 w18_a0 b18_8f b18_8e b18_8d w18_9c w18_98 w18_94 w18_90 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 g18_27 g18_26 g18_25 g18_24 g18_21 g18_20 g18_19 g18_18 g18_12 g18_11 g18_10 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
  -- 0xA8A: sw
  obtain ⟨n20, d20, s20, fr20, K20, W20, rg20⟩ := sv_sw F E19 s19 sv_at_a8a (off' := 0xA8C) (c := 0xA4)
    (by decide) (by rw [g19_2]; sv_addr) (by decide) (by decide)
  have t20 : Steps n0 n20 := t19.trans d20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keep K20 (by decide)
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [rg20 sp, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg20 (3 : Fin 32), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg20 (4 : Fin 32), g19_4]
  have g20_9 : reg n20 (9 : Fin 32) = x9 := by rw [rg20 (9 : Fin 32), g19_9]
  have g20_10 : reg n20 a0 = w30 := by rw [rg20 a0, g19_10]
  have g20_11 : reg n20 a1 = (trl) >>> 16 := by rw [rg20 a1, g19_11]
  have g20_12 : reg n20 a2 = (trl) >>> 24 := by rw [rg20 a2, g19_12]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rg20 (18 : Fin 32), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rg20 (19 : Fin 32), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg20 (20 : Fin 32), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [rg20 (21 : Fin 32), g19_21]
  have g20_24 : reg n20 (24 : Fin 32) = trl := by rw [rg20 (24 : Fin 32), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [rg20 (25 : Fin 32), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [rg20 (26 : Fin 32), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg20 (27 : Fin 32), g19_27]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4)] := keep_kk19.trans K20.toL
  clear keep_kk19
  have w20_24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K20.w32 (by decide) (by decide)).trans w19_24
  have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K20.w32 (by decide) (by decide)).trans w19_28
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K20.w32 (by decide) (by decide)).trans w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K20.w32 (by decide) (by decide)).trans w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K20.w32 (by decide) (by decide)).trans w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K20.w32 (by decide) (by decide)).trans w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K20.w32 (by decide) (by decide)).trans w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K20.w32 (by decide) (by decide)).trans w19_40
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K20.w32 (by decide) (by decide)).trans w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K20.w32 (by decide) (by decide)).trans w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K20.w32 (by decide) (by decide)).trans w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K20.w32 (by decide) (by decide)).trans w19_50
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K20.w32 (by decide) (by decide)).trans w19_54
  have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K20.w32 (by decide) (by decide)).trans w19_58
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K20.w32 (by decide) (by decide)).trans w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K20.w32 (by decide) (by decide)).trans w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K20.w32 (by decide) (by decide)).trans w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K20.w32 (by decide) (by decide)).trans w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K20.w32 (by decide) (by decide)).trans w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K20.w32 (by decide) (by decide)).trans w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K20.w32 (by decide) (by decide)).trans w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K20.w32 (by decide) (by decide)).trans w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K20.w32 (by decide) (by decide)).trans w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K20.w32 (by decide) (by decide)).trans w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K20.w32 (by decide) (by decide)).trans w19_84
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K20.w32 (by decide) (by decide)).trans w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K20.w32 (by decide) (by decide)).trans w19_94
  have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K20.w32 (by decide) (by decide)).trans w19_98
  have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K20.w32 (by decide) (by decide)).trans w19_9c
  have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K20.w32 (by decide) (by decide)).trans w19_a0
  have b20_8d : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_8d
  have b20_8e : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_8e
  have b20_8f : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_8f
  have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [W20, g19_10]
  have q20_420 : ∀ j, j < 47 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_420 j hj)
  have q20_44f : ∀ j, j < 48 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_44f j hj)
  have q20_a21 : ∀ j, j < 48 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_a21 j hj)
  have q20_a51 : ∀ j, j < 48 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_a51 j hj)
  clear q19_a51 q19_a21 q19_44f q19_420 b19_8f b19_8e b19_8d w19_a0 w19_9c w19_98 w19_94 w19_90 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 g19_10 g19_27 g19_26 g19_25 g19_24 g19_21 g19_20 g19_19 g19_18 g19_12 g19_11 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0xA8C: lw
  obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_a8c (off' := 0xA8E) (by decide)
    (by rw [g20_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s21 : St n21.mem SV n21 0xA8E (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_9 : reg n21 (9 : Fin 32) = x9 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
  have g21_11 : reg n21 a1 = (trl) >>> 16 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_11]
  have g21_12 : reg n21 a2 = (trl) >>> 24 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_12]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_24 : reg n21 (24 : Fin 32) = trl := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_10 : reg n21 a0 = w40 := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr, w20_40]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m21]; exact w20_24
  have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m21]; exact w20_28
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m21]; exact w20_2c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m21]; exact w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m21]; exact w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m21]; exact w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m21]; exact w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m21]; exact w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m21]; exact w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m21]; exact w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m21]; exact w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m21]; exact w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m21]; exact w20_54
  have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m21]; exact w20_58
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m21]; exact w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m21]; exact w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m21]; exact w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m21]; exact w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m21]; exact w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m21]; exact w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m21]; exact w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m21]; exact w20_84
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m21]; exact w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m21]; exact w20_94
  have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m21]; exact w20_98
  have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m21]; exact w20_9c
  have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m21]; exact w20_a0
  have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m21]; exact w20_a4
  have b21_8d : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m21]; exact b20_8d
  have b21_8e : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m21]; exact b20_8e
  have b21_8f : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m21]; exact b20_8f
  have q21_420 : ∀ j, j < 47 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m21]; exact q20_420 j hj
  have q21_44f : ∀ j, j < 48 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m21]; exact q20_44f j hj
  have q21_a21 : ∀ j, j < 48 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m21]; exact q20_a21 j hj
  have q21_a51 : ∀ j, j < 48 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m21]; exact q20_a51 j hj
  clear q20_a51 q20_a21 q20_44f q20_420 w20_a4 b20_8f b20_8e b20_8d w20_a0 w20_9c w20_98 w20_94 w20_90 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 g20_27 g20_26 g20_25 g20_24 g20_21 g20_20 g20_19 g20_18 g20_12 g20_11 g20_10 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 rg20 W20 K20 fr20 s20 d20
  -- 0xA8E: sw
  obtain ⟨n22, d22, s22, fr22, K22, W22, rg22⟩ := sv_sw F E21 s21 sv_at_a8e (off' := 0xA90) (c := 0xA8)
    (by decide) (by rw [g21_2]; sv_addr) (by decide) (by decide)
  have t22 : Steps n0 n22 := t21.trans d22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rg22 sp, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg22 (3 : Fin 32), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg22 (4 : Fin 32), g21_4]
  have g22_9 : reg n22 (9 : Fin 32) = x9 := by rw [rg22 (9 : Fin 32), g21_9]
  have g22_10 : reg n22 a0 = w40 := by rw [rg22 a0, g21_10]
  have g22_11 : reg n22 a1 = (trl) >>> 16 := by rw [rg22 a1, g21_11]
  have g22_12 : reg n22 a2 = (trl) >>> 24 := by rw [rg22 a2, g21_12]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rg22 (18 : Fin 32), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rg22 (19 : Fin 32), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg22 (20 : Fin 32), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [rg22 (21 : Fin 32), g21_21]
  have g22_24 : reg n22 (24 : Fin 32) = trl := by rw [rg22 (24 : Fin 32), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [rg22 (25 : Fin 32), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [rg22 (26 : Fin 32), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg22 (27 : Fin 32), g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4)] := keep_kk21.trans K22.toL
  clear keep_kk21
  have w22_24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K22.w32 (by decide) (by decide)).trans w21_24
  have w22_28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K22.w32 (by decide) (by decide)).trans w21_28
  have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K22.w32 (by decide) (by decide)).trans w21_2c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K22.w32 (by decide) (by decide)).trans w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K22.w32 (by decide) (by decide)).trans w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K22.w32 (by decide) (by decide)).trans w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K22.w32 (by decide) (by decide)).trans w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K22.w32 (by decide) (by decide)).trans w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K22.w32 (by decide) (by decide)).trans w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K22.w32 (by decide) (by decide)).trans w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K22.w32 (by decide) (by decide)).trans w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K22.w32 (by decide) (by decide)).trans w21_50
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K22.w32 (by decide) (by decide)).trans w21_54
  have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K22.w32 (by decide) (by decide)).trans w21_58
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K22.w32 (by decide) (by decide)).trans w21_5c
  have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K22.w32 (by decide) (by decide)).trans w21_60
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K22.w32 (by decide) (by decide)).trans w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K22.w32 (by decide) (by decide)).trans w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K22.w32 (by decide) (by decide)).trans w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K22.w32 (by decide) (by decide)).trans w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K22.w32 (by decide) (by decide)).trans w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K22.w32 (by decide) (by decide)).trans w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K22.w32 (by decide) (by decide)).trans w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K22.w32 (by decide) (by decide)).trans w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K22.w32 (by decide) (by decide)).trans w21_84
  have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K22.w32 (by decide) (by decide)).trans w21_90
  have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K22.w32 (by decide) (by decide)).trans w21_94
  have w22_98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K22.w32 (by decide) (by decide)).trans w21_98
  have w22_9c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K22.w32 (by decide) (by decide)).trans w21_9c
  have w22_a0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K22.w32 (by decide) (by decide)).trans w21_a0
  have w22_a4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K22.w32 (by decide) (by decide)).trans w21_a4
  have b22_8d : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K22.b8 (by decide) (by decide)).trans b21_8d
  have b22_8e : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K22.b8 (by decide) (by decide)).trans b21_8e
  have b22_8f : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K22.b8 (by decide) (by decide)).trans b21_8f
  have w22_a8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [W22, g21_10]
  have q22_420 : ∀ j, j < 47 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_420 j hj)
  have q22_44f : ∀ j, j < 48 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_44f j hj)
  have q22_a21 : ∀ j, j < 48 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_a21 j hj)
  have q22_a51 : ∀ j, j < 48 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_a51 j hj)
  clear q21_a51 q21_a21 q21_44f q21_420 b21_8f b21_8e b21_8d w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 w21_2c w21_28 w21_24 g21_10 g21_27 g21_26 g21_25 g21_24 g21_21 g21_20 g21_19 g21_18 g21_12 g21_11 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0xA90: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_a90 (off' := 0xA92) (by decide)
    (by rw [g22_2, show B + 0x21A0 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x2C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0xA92 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_9 : reg n23 (9 : Fin 32) = x9 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_11 : reg n23 a1 = (trl) >>> 16 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_11]
  have g23_12 : reg n23 a2 = (trl) >>> 24 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_12]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_24 : reg n23 (24 : Fin 32) = trl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_10 : reg n23 a0 = w2c := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_2, show B + 0x21A0 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x2C by sv_addr, w22_2c]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m23]; exact w22_24
  have w23_28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m23]; exact w22_28
  have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m23]; exact w22_2c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m23]; exact w22_38
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m23]; exact w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m23]; exact w22_40
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m23]; exact w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m23]; exact w22_54
  have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m23]; exact w22_58
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m23]; exact w22_5c
  have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m23]; exact w22_60
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m23]; exact w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m23]; exact w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m23]; exact w22_84
  have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m23]; exact w22_90
  have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m23]; exact w22_94
  have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m23]; exact w22_98
  have w23_9c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m23]; exact w22_9c
  have w23_a0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m23]; exact w22_a0
  have w23_a4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m23]; exact w22_a4
  have w23_a8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m23]; exact w22_a8
  have b23_8d : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m23]; exact b22_8d
  have b23_8e : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m23]; exact b22_8e
  have b23_8f : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m23]; exact b22_8f
  have q23_420 : ∀ j, j < 47 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m23]; exact q22_420 j hj
  have q23_44f : ∀ j, j < 48 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m23]; exact q22_44f j hj
  have q23_a21 : ∀ j, j < 48 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m23]; exact q22_a21 j hj
  have q23_a51 : ∀ j, j < 48 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m23]; exact q22_a51 j hj
  clear q22_a51 q22_a21 q22_44f q22_420 w22_a8 b22_8f b22_8e b22_8d w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 w22_2c w22_28 w22_24 g22_27 g22_26 g22_25 g22_24 g22_21 g22_20 g22_19 g22_18 g22_12 g22_11 g22_10 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 rg22 W22 K22 fr22 s22 d22
  -- 0xA92: sw
  obtain ⟨n24, d24, s24, fr24, K24, W24, rg24⟩ := sv_sw F E23 s23 sv_at_a92 (off' := 0xA94) (c := 0xAC)
    (by decide) (by rw [g23_2]; sv_addr) (by decide) (by decide)
  have t24 : Steps n0 n24 := t23.trans d24
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [rg24 sp, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg24 (3 : Fin 32), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg24 (4 : Fin 32), g23_4]
  have g24_9 : reg n24 (9 : Fin 32) = x9 := by rw [rg24 (9 : Fin 32), g23_9]
  have g24_10 : reg n24 a0 = w2c := by rw [rg24 a0, g23_10]
  have g24_11 : reg n24 a1 = (trl) >>> 16 := by rw [rg24 a1, g23_11]
  have g24_12 : reg n24 a2 = (trl) >>> 24 := by rw [rg24 a2, g23_12]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [rg24 (18 : Fin 32), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [rg24 (19 : Fin 32), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg24 (20 : Fin 32), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [rg24 (21 : Fin 32), g23_21]
  have g24_24 : reg n24 (24 : Fin 32) = trl := by rw [rg24 (24 : Fin 32), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [rg24 (25 : Fin 32), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [rg24 (26 : Fin 32), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg24 (27 : Fin 32), g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4)] := keep_kk23.trans K24.toL
  clear keep_kk23
  have w24_24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K24.w32 (by decide) (by decide)).trans w23_24
  have w24_28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K24.w32 (by decide) (by decide)).trans w23_28
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K24.w32 (by decide) (by decide)).trans w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K24.w32 (by decide) (by decide)).trans w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K24.w32 (by decide) (by decide)).trans w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K24.w32 (by decide) (by decide)).trans w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K24.w32 (by decide) (by decide)).trans w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K24.w32 (by decide) (by decide)).trans w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K24.w32 (by decide) (by decide)).trans w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K24.w32 (by decide) (by decide)).trans w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K24.w32 (by decide) (by decide)).trans w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K24.w32 (by decide) (by decide)).trans w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K24.w32 (by decide) (by decide)).trans w23_54
  have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K24.w32 (by decide) (by decide)).trans w23_58
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K24.w32 (by decide) (by decide)).trans w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K24.w32 (by decide) (by decide)).trans w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K24.w32 (by decide) (by decide)).trans w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K24.w32 (by decide) (by decide)).trans w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K24.w32 (by decide) (by decide)).trans w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K24.w32 (by decide) (by decide)).trans w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K24.w32 (by decide) (by decide)).trans w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K24.w32 (by decide) (by decide)).trans w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K24.w32 (by decide) (by decide)).trans w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K24.w32 (by decide) (by decide)).trans w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K24.w32 (by decide) (by decide)).trans w23_84
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K24.w32 (by decide) (by decide)).trans w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K24.w32 (by decide) (by decide)).trans w23_94
  have w24_98 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K24.w32 (by decide) (by decide)).trans w23_98
  have w24_9c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K24.w32 (by decide) (by decide)).trans w23_9c
  have w24_a0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K24.w32 (by decide) (by decide)).trans w23_a0
  have w24_a4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K24.w32 (by decide) (by decide)).trans w23_a4
  have w24_a8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K24.w32 (by decide) (by decide)).trans w23_a8
  have b24_8d : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_8d
  have b24_8e : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_8e
  have b24_8f : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_8f
  have w24_ac : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [W24, g23_10]
  have q24_420 : ∀ j, j < 47 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K24.range (by decide) (by decide) j hj).trans (q23_420 j hj)
  have q24_44f : ∀ j, j < 48 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K24.range (by decide) (by decide) j hj).trans (q23_44f j hj)
  have q24_a21 : ∀ j, j < 48 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K24.range (by decide) (by decide) j hj).trans (q23_a21 j hj)
  have q24_a51 : ∀ j, j < 48 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K24.range (by decide) (by decide) j hj).trans (q23_a51 j hj)
  clear q23_a51 q23_a21 q23_44f q23_420 b23_8f b23_8e b23_8d w23_a8 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 g23_10 g23_27 g23_26 g23_25 g23_24 g23_21 g23_20 g23_19 g23_18 g23_12 g23_11 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0xA94: lw
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_a94 (off' := 0xA96) (by decide)
    (by rw [g24_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s25 : St n25.mem SV n25 0xA96 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
  have g25_9 : reg n25 (9 : Fin 32) = x9 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
  have g25_11 : reg n25 a1 = (trl) >>> 16 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_11]
  have g25_12 : reg n25 a2 = (trl) >>> 24 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_12]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_24 : reg n25 (24 : Fin 32) = trl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
  have g25_10 : reg n25 a0 = w3c := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr, w24_3c]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m25]; exact w24_24
  have w25_28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m25]; exact w24_28
  have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m25]; exact w24_2c
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m25]; exact w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m25]; exact w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m25]; exact w24_38
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m25]; exact w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m25]; exact w24_40
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m25]; exact w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m25]; exact w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m25]; exact w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m25]; exact w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m25]; exact w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m25]; exact w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m25]; exact w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m25]; exact w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m25]; exact w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m25]; exact w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m25]; exact w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m25]; exact w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m25]; exact w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m25]; exact w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m25]; exact w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m25]; exact w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m25]; exact w24_84
  have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m25]; exact w24_90
  have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m25]; exact w24_94
  have w25_98 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m25]; exact w24_98
  have w25_9c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m25]; exact w24_9c
  have w25_a0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m25]; exact w24_a0
  have w25_a4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m25]; exact w24_a4
  have w25_a8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m25]; exact w24_a8
  have w25_ac : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m25]; exact w24_ac
  have b25_8d : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m25]; exact b24_8d
  have b25_8e : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m25]; exact b24_8e
  have b25_8f : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m25]; exact b24_8f
  have q25_420 : ∀ j, j < 47 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m25]; exact q24_420 j hj
  have q25_44f : ∀ j, j < 48 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m25]; exact q24_44f j hj
  have q25_a21 : ∀ j, j < 48 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m25]; exact q24_a21 j hj
  have q25_a51 : ∀ j, j < 48 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m25]; exact q24_a51 j hj
  clear q24_a51 q24_a21 q24_44f q24_420 w24_ac b24_8f b24_8e b24_8d w24_a8 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 g24_27 g24_26 g24_25 g24_24 g24_21 g24_20 g24_19 g24_18 g24_12 g24_11 g24_10 g24_9 g24_4 g24_3 g24_2 V24 E24 fR24 t24 rg24 W24 K24 fr24 s24 d24
  -- 0xA96: sw
  obtain ⟨n26, d26, s26, fr26, K26, W26, rg26⟩ := sv_sw F E25 s25 sv_at_a96 (off' := 0xA98) (c := 0xB0)
    (by decide) (by rw [g25_2]; sv_addr) (by decide) (by decide)
  have t26 : Steps n0 n26 := t25.trans d26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rg26 sp, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg26 (3 : Fin 32), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg26 (4 : Fin 32), g25_4]
  have g26_9 : reg n26 (9 : Fin 32) = x9 := by rw [rg26 (9 : Fin 32), g25_9]
  have g26_10 : reg n26 a0 = w3c := by rw [rg26 a0, g25_10]
  have g26_11 : reg n26 a1 = (trl) >>> 16 := by rw [rg26 a1, g25_11]
  have g26_12 : reg n26 a2 = (trl) >>> 24 := by rw [rg26 a2, g25_12]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rg26 (18 : Fin 32), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rg26 (19 : Fin 32), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg26 (20 : Fin 32), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [rg26 (21 : Fin 32), g25_21]
  have g26_24 : reg n26 (24 : Fin 32) = trl := by rw [rg26 (24 : Fin 32), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [rg26 (25 : Fin 32), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [rg26 (26 : Fin 32), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg26 (27 : Fin 32), g25_27]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4)] := keep_kk25.trans K26.toL
  clear keep_kk25
  have w26_24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K26.w32 (by decide) (by decide)).trans w25_24
  have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K26.w32 (by decide) (by decide)).trans w25_28
  have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K26.w32 (by decide) (by decide)).trans w25_2c
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K26.w32 (by decide) (by decide)).trans w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K26.w32 (by decide) (by decide)).trans w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K26.w32 (by decide) (by decide)).trans w25_38
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K26.w32 (by decide) (by decide)).trans w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K26.w32 (by decide) (by decide)).trans w25_40
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K26.w32 (by decide) (by decide)).trans w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K26.w32 (by decide) (by decide)).trans w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K26.w32 (by decide) (by decide)).trans w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K26.w32 (by decide) (by decide)).trans w25_50
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K26.w32 (by decide) (by decide)).trans w25_54
  have w26_58 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K26.w32 (by decide) (by decide)).trans w25_58
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K26.w32 (by decide) (by decide)).trans w25_5c
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K26.w32 (by decide) (by decide)).trans w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K26.w32 (by decide) (by decide)).trans w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K26.w32 (by decide) (by decide)).trans w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K26.w32 (by decide) (by decide)).trans w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K26.w32 (by decide) (by decide)).trans w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K26.w32 (by decide) (by decide)).trans w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K26.w32 (by decide) (by decide)).trans w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K26.w32 (by decide) (by decide)).trans w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K26.w32 (by decide) (by decide)).trans w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K26.w32 (by decide) (by decide)).trans w25_84
  have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K26.w32 (by decide) (by decide)).trans w25_90
  have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K26.w32 (by decide) (by decide)).trans w25_94
  have w26_98 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K26.w32 (by decide) (by decide)).trans w25_98
  have w26_9c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K26.w32 (by decide) (by decide)).trans w25_9c
  have w26_a0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K26.w32 (by decide) (by decide)).trans w25_a0
  have w26_a4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K26.w32 (by decide) (by decide)).trans w25_a4
  have w26_a8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K26.w32 (by decide) (by decide)).trans w25_a8
  have w26_ac : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K26.w32 (by decide) (by decide)).trans w25_ac
  have b26_8d : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_8d
  have b26_8e : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_8e
  have b26_8f : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_8f
  have w26_b0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [W26, g25_10]
  have q26_420 : ∀ j, j < 47 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_420 j hj)
  have q26_44f : ∀ j, j < 48 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_44f j hj)
  have q26_a21 : ∀ j, j < 48 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_a21 j hj)
  have q26_a51 : ∀ j, j < 48 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_a51 j hj)
  clear q25_a51 q25_a21 q25_44f q25_420 b25_8f b25_8e b25_8d w25_ac w25_a8 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_38 w25_34 w25_30 w25_2c w25_28 w25_24 g25_10 g25_27 g25_26 g25_25 g25_24 g25_21 g25_20 g25_19 g25_18 g25_12 g25_11 g25_9 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0xA98: lw
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_a98 (off' := 0xA9A) (by decide)
    (by rw [g26_2, show B + 0x21A0 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s27 : St n27.mem SV n27 0xA9A (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_9 : reg n27 (9 : Fin 32) = x9 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
  have g27_11 : reg n27 a1 = (trl) >>> 16 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_11]
  have g27_12 : reg n27 a2 = (trl) >>> 24 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_12]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_24 : reg n27 (24 : Fin 32) = trl := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
  have g27_10 : reg n27 a0 = w28 := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x28 by sv_addr, w26_28]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m27]; exact w26_24
  have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m27]; exact w26_28
  have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m27]; exact w26_2c
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m27]; exact w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m27]; exact w26_38
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m27]; exact w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m27]; exact w26_40
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m27]; exact w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m27]; exact w26_48
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m27]; exact w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m27]; exact w26_50
  have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m27]; exact w26_54
  have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m27]; exact w26_58
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m27]; exact w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m27]; exact w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m27]; exact w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m27]; exact w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m27]; exact w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m27]; exact w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m27]; exact w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m27]; exact w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m27]; exact w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m27]; exact w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m27]; exact w26_84
  have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m27]; exact w26_90
  have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m27]; exact w26_94
  have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m27]; exact w26_98
  have w27_9c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m27]; exact w26_9c
  have w27_a0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m27]; exact w26_a0
  have w27_a4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m27]; exact w26_a4
  have w27_a8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m27]; exact w26_a8
  have w27_ac : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m27]; exact w26_ac
  have w27_b0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m27]; exact w26_b0
  have b27_8d : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m27]; exact b26_8d
  have b27_8e : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m27]; exact b26_8e
  have b27_8f : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m27]; exact b26_8f
  have q27_420 : ∀ j, j < 47 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m27]; exact q26_420 j hj
  have q27_44f : ∀ j, j < 48 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m27]; exact q26_44f j hj
  have q27_a21 : ∀ j, j < 48 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m27]; exact q26_a21 j hj
  have q27_a51 : ∀ j, j < 48 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m27]; exact q26_a51 j hj
  clear q26_a51 q26_a21 q26_44f q26_420 w26_b0 b26_8f b26_8e b26_8d w26_ac w26_a8 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 g26_27 g26_26 g26_25 g26_24 g26_21 g26_20 g26_19 g26_18 g26_12 g26_11 g26_10 g26_9 g26_4 g26_3 g26_2 V26 E26 fR26 t26 rg26 W26 K26 fr26 s26 d26
  -- 0xA9A: sw
  obtain ⟨n28, d28, s28, fr28, K28, W28, rg28⟩ := sv_sw F E27 s27 sv_at_a9a (off' := 0xA9C) (c := 0xB4)
    (by decide) (by rw [g27_2]; sv_addr) (by decide) (by decide)
  have t28 : Steps n0 n28 := t27.trans d28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rg28 sp, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg28 (3 : Fin 32), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg28 (4 : Fin 32), g27_4]
  have g28_9 : reg n28 (9 : Fin 32) = x9 := by rw [rg28 (9 : Fin 32), g27_9]
  have g28_10 : reg n28 a0 = w28 := by rw [rg28 a0, g27_10]
  have g28_11 : reg n28 a1 = (trl) >>> 16 := by rw [rg28 a1, g27_11]
  have g28_12 : reg n28 a2 = (trl) >>> 24 := by rw [rg28 a2, g27_12]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rg28 (18 : Fin 32), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rg28 (19 : Fin 32), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg28 (20 : Fin 32), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [rg28 (21 : Fin 32), g27_21]
  have g28_24 : reg n28 (24 : Fin 32) = trl := by rw [rg28 (24 : Fin 32), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [rg28 (25 : Fin 32), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [rg28 (26 : Fin 32), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg28 (27 : Fin 32), g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have w28_24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K28.w32 (by decide) (by decide)).trans w27_24
  have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K28.w32 (by decide) (by decide)).trans w27_28
  have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K28.w32 (by decide) (by decide)).trans w27_2c
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K28.w32 (by decide) (by decide)).trans w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K28.w32 (by decide) (by decide)).trans w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K28.w32 (by decide) (by decide)).trans w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K28.w32 (by decide) (by decide)).trans w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K28.w32 (by decide) (by decide)).trans w27_40
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K28.w32 (by decide) (by decide)).trans w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K28.w32 (by decide) (by decide)).trans w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K28.w32 (by decide) (by decide)).trans w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K28.w32 (by decide) (by decide)).trans w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K28.w32 (by decide) (by decide)).trans w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K28.w32 (by decide) (by decide)).trans w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K28.w32 (by decide) (by decide)).trans w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K28.w32 (by decide) (by decide)).trans w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K28.w32 (by decide) (by decide)).trans w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K28.w32 (by decide) (by decide)).trans w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K28.w32 (by decide) (by decide)).trans w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K28.w32 (by decide) (by decide)).trans w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K28.w32 (by decide) (by decide)).trans w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K28.w32 (by decide) (by decide)).trans w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K28.w32 (by decide) (by decide)).trans w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K28.w32 (by decide) (by decide)).trans w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K28.w32 (by decide) (by decide)).trans w27_84
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K28.w32 (by decide) (by decide)).trans w27_90
  have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K28.w32 (by decide) (by decide)).trans w27_94
  have w28_98 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K28.w32 (by decide) (by decide)).trans w27_98
  have w28_9c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K28.w32 (by decide) (by decide)).trans w27_9c
  have w28_a0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K28.w32 (by decide) (by decide)).trans w27_a0
  have w28_a4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K28.w32 (by decide) (by decide)).trans w27_a4
  have w28_a8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K28.w32 (by decide) (by decide)).trans w27_a8
  have w28_ac : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K28.w32 (by decide) (by decide)).trans w27_ac
  have w28_b0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K28.w32 (by decide) (by decide)).trans w27_b0
  have b28_8d : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_8d
  have b28_8e : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_8e
  have b28_8f : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_8f
  have w28_b4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [W28, g27_10]
  have q28_420 : ∀ j, j < 47 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_420 j hj)
  have q28_44f : ∀ j, j < 48 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_44f j hj)
  have q28_a21 : ∀ j, j < 48 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_a21 j hj)
  have q28_a51 : ∀ j, j < 48 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_a51 j hj)
  clear q27_a51 q27_a21 q27_44f q27_420 b27_8f b27_8e b27_8d w27_b0 w27_ac w27_a8 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 g27_10 g27_27 g27_26 g27_25 g27_24 g27_21 g27_20 g27_19 g27_18 g27_12 g27_11 g27_9 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0xA9C: lw
  obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_a9c (off' := 0xA9E) (by decide)
    (by rw [g28_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s29 : St n29.mem SV n29 0xA9E (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_9 : reg n29 (9 : Fin 32) = x9 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
  have g29_11 : reg n29 a1 = (trl) >>> 16 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_11]
  have g29_12 : reg n29 a2 = (trl) >>> 24 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_12]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_24 : reg n29 (24 : Fin 32) = trl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_10 : reg n29 a0 = w38 := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr, w28_38]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m29]; exact w28_24
  have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m29]; exact w28_28
  have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m29]; exact w28_2c
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m29]; exact w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m29]; exact w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m29]; exact w28_38
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m29]; exact w28_3c
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m29]; exact w28_40
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m29]; exact w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m29]; exact w28_48
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m29]; exact w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
  have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m29]; exact w28_54
  have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m29]; exact w28_58
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m29]; exact w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m29]; exact w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m29]; exact w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m29]; exact w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m29]; exact w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m29]; exact w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m29]; exact w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m29]; exact w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m29]; exact w28_84
  have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m29]; exact w28_90
  have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m29]; exact w28_94
  have w29_98 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m29]; exact w28_98
  have w29_9c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m29]; exact w28_9c
  have w29_a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m29]; exact w28_a0
  have w29_a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m29]; exact w28_a4
  have w29_a8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m29]; exact w28_a8
  have w29_ac : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m29]; exact w28_ac
  have w29_b0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m29]; exact w28_b0
  have w29_b4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m29]; exact w28_b4
  have b29_8d : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m29]; exact b28_8d
  have b29_8e : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m29]; exact b28_8e
  have b29_8f : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m29]; exact b28_8f
  have q29_420 : ∀ j, j < 47 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_420 j hj
  have q29_44f : ∀ j, j < 48 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m29]; exact q28_44f j hj
  have q29_a21 : ∀ j, j < 48 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m29]; exact q28_a21 j hj
  have q29_a51 : ∀ j, j < 48 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m29]; exact q28_a51 j hj
  clear q28_a51 q28_a21 q28_44f q28_420 w28_b4 b28_8f b28_8e b28_8d w28_b0 w28_ac w28_a8 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 w28_2c w28_28 w28_24 g28_27 g28_26 g28_25 g28_24 g28_21 g28_20 g28_19 g28_18 g28_12 g28_11 g28_10 g28_9 g28_4 g28_3 g28_2 V28 E28 fR28 t28 rg28 W28 K28 fr28 s28 d28
  -- 0xA9E: sw
  obtain ⟨n30, d30, s30, fr30, K30, W30, rg30⟩ := sv_sw F E29 s29 sv_at_a9e (off' := 0xAA0) (c := 0xB8)
    (by decide) (by rw [g29_2]; sv_addr) (by decide) (by decide)
  have t30 : Steps n0 n30 := t29.trans d30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rg30 sp, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg30 (3 : Fin 32), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg30 (4 : Fin 32), g29_4]
  have g30_9 : reg n30 (9 : Fin 32) = x9 := by rw [rg30 (9 : Fin 32), g29_9]
  have g30_10 : reg n30 a0 = w38 := by rw [rg30 a0, g29_10]
  have g30_11 : reg n30 a1 = (trl) >>> 16 := by rw [rg30 a1, g29_11]
  have g30_12 : reg n30 a2 = (trl) >>> 24 := by rw [rg30 a2, g29_12]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rg30 (18 : Fin 32), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rg30 (19 : Fin 32), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg30 (20 : Fin 32), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [rg30 (21 : Fin 32), g29_21]
  have g30_24 : reg n30 (24 : Fin 32) = trl := by rw [rg30 (24 : Fin 32), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [rg30 (25 : Fin 32), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [rg30 (26 : Fin 32), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg30 (27 : Fin 32), g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have w30_24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K30.w32 (by decide) (by decide)).trans w29_24
  have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K30.w32 (by decide) (by decide)).trans w29_28
  have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K30.w32 (by decide) (by decide)).trans w29_2c
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K30.w32 (by decide) (by decide)).trans w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K30.w32 (by decide) (by decide)).trans w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K30.w32 (by decide) (by decide)).trans w29_38
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K30.w32 (by decide) (by decide)).trans w29_3c
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K30.w32 (by decide) (by decide)).trans w29_40
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K30.w32 (by decide) (by decide)).trans w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K30.w32 (by decide) (by decide)).trans w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K30.w32 (by decide) (by decide)).trans w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K30.w32 (by decide) (by decide)).trans w29_50
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K30.w32 (by decide) (by decide)).trans w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K30.w32 (by decide) (by decide)).trans w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K30.w32 (by decide) (by decide)).trans w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K30.w32 (by decide) (by decide)).trans w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K30.w32 (by decide) (by decide)).trans w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K30.w32 (by decide) (by decide)).trans w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K30.w32 (by decide) (by decide)).trans w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K30.w32 (by decide) (by decide)).trans w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K30.w32 (by decide) (by decide)).trans w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K30.w32 (by decide) (by decide)).trans w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K30.w32 (by decide) (by decide)).trans w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K30.w32 (by decide) (by decide)).trans w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K30.w32 (by decide) (by decide)).trans w29_84
  have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K30.w32 (by decide) (by decide)).trans w29_90
  have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K30.w32 (by decide) (by decide)).trans w29_94
  have w30_98 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K30.w32 (by decide) (by decide)).trans w29_98
  have w30_9c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K30.w32 (by decide) (by decide)).trans w29_9c
  have w30_a0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K30.w32 (by decide) (by decide)).trans w29_a0
  have w30_a4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K30.w32 (by decide) (by decide)).trans w29_a4
  have w30_a8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K30.w32 (by decide) (by decide)).trans w29_a8
  have w30_ac : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K30.w32 (by decide) (by decide)).trans w29_ac
  have w30_b0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K30.w32 (by decide) (by decide)).trans w29_b0
  have w30_b4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K30.w32 (by decide) (by decide)).trans w29_b4
  have b30_8d : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_8d
  have b30_8e : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_8e
  have b30_8f : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_8f
  have w30_b8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [W30, g29_10]
  have q30_420 : ∀ j, j < 47 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_420 j hj)
  have q30_44f : ∀ j, j < 48 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_44f j hj)
  have q30_a21 : ∀ j, j < 48 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_a21 j hj)
  have q30_a51 : ∀ j, j < 48 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_a51 j hj)
  clear q29_a51 q29_a21 q29_44f q29_420 b29_8f b29_8e b29_8d w29_b4 w29_b0 w29_ac w29_a8 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 w29_2c w29_28 w29_24 g29_10 g29_27 g29_26 g29_25 g29_24 g29_21 g29_20 g29_19 g29_18 g29_12 g29_11 g29_9 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0xAA0: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_aa0 (off' := 0xAA2) (by decide)
    (by rw [g30_2, show B + 0x21A0 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x24 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0xAA2 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_9 : reg n31 (9 : Fin 32) = x9 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
  have g31_11 : reg n31 a1 = (trl) >>> 16 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_11]
  have g31_12 : reg n31 a2 = (trl) >>> 24 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_12]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_24 : reg n31 (24 : Fin 32) = trl := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_10 : reg n31 a0 = w24 := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_2, show B + 0x21A0 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x24 by sv_addr, w30_24]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m31]; exact w30_24
  have w31_28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m31]; exact w30_28
  have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m31]; exact w30_2c
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m31]; exact w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m31]; exact w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m31]; exact w30_38
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m31]; exact w30_3c
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m31]; exact w30_40
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m31]; exact w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m31]; exact w30_48
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m31]; exact w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m31]; exact w30_50
  have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m31]; exact w30_54
  have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m31]; exact w30_58
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m31]; exact w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m31]; exact w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m31]; exact w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m31]; exact w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m31]; exact w30_70
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m31]; exact w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m31]; exact w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m31]; exact w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m31]; exact w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m31]; exact w30_84
  have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m31]; exact w30_90
  have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m31]; exact w30_94
  have w31_98 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m31]; exact w30_98
  have w31_9c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m31]; exact w30_9c
  have w31_a0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m31]; exact w30_a0
  have w31_a4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m31]; exact w30_a4
  have w31_a8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m31]; exact w30_a8
  have w31_ac : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m31]; exact w30_ac
  have w31_b0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m31]; exact w30_b0
  have w31_b4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m31]; exact w30_b4
  have w31_b8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [m31]; exact w30_b8
  have b31_8d : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m31]; exact b30_8d
  have b31_8e : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m31]; exact b30_8e
  have b31_8f : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m31]; exact b30_8f
  have q31_420 : ∀ j, j < 47 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_420 j hj
  have q31_44f : ∀ j, j < 48 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m31]; exact q30_44f j hj
  have q31_a21 : ∀ j, j < 48 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m31]; exact q30_a21 j hj
  have q31_a51 : ∀ j, j < 48 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m31]; exact q30_a51 j hj
  clear q30_a51 q30_a21 q30_44f q30_420 w30_b8 b30_8f b30_8e b30_8d w30_b4 w30_b0 w30_ac w30_a8 w30_a4 w30_a0 w30_9c w30_98 w30_94 w30_90 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_44 w30_40 w30_3c w30_38 w30_34 w30_30 w30_2c w30_28 w30_24 g30_27 g30_26 g30_25 g30_24 g30_21 g30_20 g30_19 g30_18 g30_12 g30_11 g30_10 g30_9 g30_4 g30_3 g30_2 V30 E30 fR30 t30 rg30 W30 K30 fr30 s30 d30
  -- 0xAA2: sw
  obtain ⟨n32, d32, s32, fr32, K32, W32, rg32⟩ := sv_sw F E31 s31 sv_at_aa2 (off' := 0xAA4) (c := 0xBC)
    (by decide) (by rw [g31_2]; sv_addr) (by decide) (by decide)
  have t32 : Steps n0 n32 := t31.trans d32
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.keep K32 (by decide)
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [rg32 sp, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg32 (3 : Fin 32), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg32 (4 : Fin 32), g31_4]
  have g32_9 : reg n32 (9 : Fin 32) = x9 := by rw [rg32 (9 : Fin 32), g31_9]
  have g32_10 : reg n32 a0 = w24 := by rw [rg32 a0, g31_10]
  have g32_11 : reg n32 a1 = (trl) >>> 16 := by rw [rg32 a1, g31_11]
  have g32_12 : reg n32 a2 = (trl) >>> 24 := by rw [rg32 a2, g31_12]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [rg32 (18 : Fin 32), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [rg32 (19 : Fin 32), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg32 (20 : Fin 32), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [rg32 (21 : Fin 32), g31_21]
  have g32_24 : reg n32 (24 : Fin 32) = trl := by rw [rg32 (24 : Fin 32), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [rg32 (25 : Fin 32), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [rg32 (26 : Fin 32), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg32 (27 : Fin 32), g31_27]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4)] := keep_kk31.trans K32.toL
  clear keep_kk31
  have w32_24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K32.w32 (by decide) (by decide)).trans w31_24
  have w32_28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K32.w32 (by decide) (by decide)).trans w31_28
  have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K32.w32 (by decide) (by decide)).trans w31_2c
  have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K32.w32 (by decide) (by decide)).trans w31_30
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K32.w32 (by decide) (by decide)).trans w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K32.w32 (by decide) (by decide)).trans w31_38
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K32.w32 (by decide) (by decide)).trans w31_3c
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K32.w32 (by decide) (by decide)).trans w31_40
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K32.w32 (by decide) (by decide)).trans w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K32.w32 (by decide) (by decide)).trans w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K32.w32 (by decide) (by decide)).trans w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K32.w32 (by decide) (by decide)).trans w31_50
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K32.w32 (by decide) (by decide)).trans w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K32.w32 (by decide) (by decide)).trans w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K32.w32 (by decide) (by decide)).trans w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K32.w32 (by decide) (by decide)).trans w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K32.w32 (by decide) (by decide)).trans w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K32.w32 (by decide) (by decide)).trans w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K32.w32 (by decide) (by decide)).trans w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K32.w32 (by decide) (by decide)).trans w31_70
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K32.w32 (by decide) (by decide)).trans w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K32.w32 (by decide) (by decide)).trans w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K32.w32 (by decide) (by decide)).trans w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K32.w32 (by decide) (by decide)).trans w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K32.w32 (by decide) (by decide)).trans w31_84
  have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K32.w32 (by decide) (by decide)).trans w31_90
  have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K32.w32 (by decide) (by decide)).trans w31_94
  have w32_98 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K32.w32 (by decide) (by decide)).trans w31_98
  have w32_9c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K32.w32 (by decide) (by decide)).trans w31_9c
  have w32_a0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K32.w32 (by decide) (by decide)).trans w31_a0
  have w32_a4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K32.w32 (by decide) (by decide)).trans w31_a4
  have w32_a8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K32.w32 (by decide) (by decide)).trans w31_a8
  have w32_ac : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K32.w32 (by decide) (by decide)).trans w31_ac
  have w32_b0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K32.w32 (by decide) (by decide)).trans w31_b0
  have w32_b4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K32.w32 (by decide) (by decide)).trans w31_b4
  have w32_b8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K32.w32 (by decide) (by decide)).trans w31_b8
  have b32_8d : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K32.b8 (by decide) (by decide)).trans b31_8d
  have b32_8e : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K32.b8 (by decide) (by decide)).trans b31_8e
  have b32_8f : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K32.b8 (by decide) (by decide)).trans b31_8f
  have w32_bc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := by rw [W32, g31_10]
  have q32_420 : ∀ j, j < 47 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_420 j hj)
  have q32_44f : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_44f j hj)
  have q32_a21 : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_a21 j hj)
  have q32_a51 : ∀ j, j < 48 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K32.range (by decide) (by decide) j hj).trans (q31_a51 j hj)
  clear q31_a51 q31_a21 q31_44f q31_420 b31_8f b31_8e b31_8d w31_b8 w31_b4 w31_b0 w31_ac w31_a8 w31_a4 w31_a0 w31_9c w31_98 w31_94 w31_90 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_44 w31_40 w31_3c w31_38 w31_34 w31_30 w31_2c w31_28 w31_24 g31_10 g31_27 g31_26 g31_25 g31_24 g31_21 g31_20 g31_19 g31_18 g31_12 g31_11 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0xAA4: sb
  obtain ⟨n33, d33, s33, fr33, K33, W33, rg33⟩ := sv_sb F E32 s32 sv_at_aa4 (off' := 0xAA8) (c := 0xD0)
    (by decide) (by rw [g32_2]; sv_addr) (by decide)
  have t33 : Steps n0 n33 := t32.trans d33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.keep K33 (by decide)
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [rg33 sp, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg33 (3 : Fin 32), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg33 (4 : Fin 32), g32_4]
  have g33_9 : reg n33 (9 : Fin 32) = x9 := by rw [rg33 (9 : Fin 32), g32_9]
  have g33_10 : reg n33 a0 = w24 := by rw [rg33 a0, g32_10]
  have g33_11 : reg n33 a1 = (trl) >>> 16 := by rw [rg33 a1, g32_11]
  have g33_12 : reg n33 a2 = (trl) >>> 24 := by rw [rg33 a2, g32_12]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [rg33 (18 : Fin 32), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [rg33 (19 : Fin 32), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg33 (20 : Fin 32), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [rg33 (21 : Fin 32), g32_21]
  have g33_24 : reg n33 (24 : Fin 32) = trl := by rw [rg33 (24 : Fin 32), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [rg33 (25 : Fin 32), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [rg33 (26 : Fin 32), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg33 (27 : Fin 32), g32_27]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1)] := keep_kk32.trans K33.toL
  clear keep_kk32
  have w33_24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K33.w32 (by decide) (by decide)).trans w32_24
  have w33_28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K33.w32 (by decide) (by decide)).trans w32_28
  have w33_2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K33.w32 (by decide) (by decide)).trans w32_2c
  have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K33.w32 (by decide) (by decide)).trans w32_30
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K33.w32 (by decide) (by decide)).trans w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K33.w32 (by decide) (by decide)).trans w32_38
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K33.w32 (by decide) (by decide)).trans w32_3c
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K33.w32 (by decide) (by decide)).trans w32_40
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K33.w32 (by decide) (by decide)).trans w32_44
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K33.w32 (by decide) (by decide)).trans w32_48
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K33.w32 (by decide) (by decide)).trans w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K33.w32 (by decide) (by decide)).trans w32_50
  have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K33.w32 (by decide) (by decide)).trans w32_54
  have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K33.w32 (by decide) (by decide)).trans w32_58
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K33.w32 (by decide) (by decide)).trans w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K33.w32 (by decide) (by decide)).trans w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K33.w32 (by decide) (by decide)).trans w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K33.w32 (by decide) (by decide)).trans w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K33.w32 (by decide) (by decide)).trans w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K33.w32 (by decide) (by decide)).trans w32_70
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K33.w32 (by decide) (by decide)).trans w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K33.w32 (by decide) (by decide)).trans w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K33.w32 (by decide) (by decide)).trans w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K33.w32 (by decide) (by decide)).trans w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K33.w32 (by decide) (by decide)).trans w32_84
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K33.w32 (by decide) (by decide)).trans w32_90
  have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K33.w32 (by decide) (by decide)).trans w32_94
  have w33_98 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K33.w32 (by decide) (by decide)).trans w32_98
  have w33_9c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K33.w32 (by decide) (by decide)).trans w32_9c
  have w33_a0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K33.w32 (by decide) (by decide)).trans w32_a0
  have w33_a4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K33.w32 (by decide) (by decide)).trans w32_a4
  have w33_a8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K33.w32 (by decide) (by decide)).trans w32_a8
  have w33_ac : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K33.w32 (by decide) (by decide)).trans w32_ac
  have w33_b0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K33.w32 (by decide) (by decide)).trans w32_b0
  have w33_b4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K33.w32 (by decide) (by decide)).trans w32_b4
  have w33_b8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K33.w32 (by decide) (by decide)).trans w32_b8
  have w33_bc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K33.w32 (by decide) (by decide)).trans w32_bc
  have b33_8d : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K33.b8 (by decide) (by decide)).trans b32_8d
  have b33_8e : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K33.b8 (by decide) (by decide)).trans b32_8e
  have b33_8f : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K33.b8 (by decide) (by decide)).trans b32_8f
  have b33_d0 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [W33, g32_20, lbu_low]
  have q33_420 : ∀ j, j < 47 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K33.range (by decide) (by decide) j hj).trans (q32_420 j hj)
  have q33_44f : ∀ j, j < 48 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K33.range (by decide) (by decide) j hj).trans (q32_44f j hj)
  have q33_a21 : ∀ j, j < 48 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K33.range (by decide) (by decide) j hj).trans (q32_a21 j hj)
  have q33_a51 : ∀ j, j < 48 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K33.range (by decide) (by decide) j hj).trans (q32_a51 j hj)
  clear q32_a51 q32_a21 q32_44f q32_420 w32_bc b32_8f b32_8e b32_8d w32_b8 w32_b4 w32_b0 w32_ac w32_a8 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 w32_2c w32_28 w32_24 g32_27 g32_26 g32_25 g32_24 g32_21 g32_20 g32_19 g32_18 g32_12 g32_11 g32_10 g32_9 g32_4 g32_3 g32_2 V32 E32 fR32 t32 rg32 W32 K32 fr32 s32 d32
  -- 0xAA8
  obtain ⟨n34, c34, u34⟩ := s33.block svL8aaa8 E33.self svL8aaa8_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have s34 : St n34.mem SV n34 0xAB4 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have rb34 : ∀ q, reg n34 q = (runBlock svL8aaa8 (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans c34
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by
    rw [rb34, runBlock_reg _ _ _ sp s33.zero (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb34, runBlock_reg _ _ _ (3 : Fin 32) s33.zero (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb34, runBlock_reg _ _ _ (4 : Fin 32) s33.zero (by decide), g33_4]
  have g34_9 : reg n34 (9 : Fin 32) = x9 := by
    rw [rb34, runBlock_reg _ _ _ (9 : Fin 32) s33.zero (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = out := by
    rw [rb34, runBlock_reg _ _ _ (18 : Fin 32) s33.zero (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by
    rw [rb34, runBlock_reg _ _ _ (19 : Fin 32) s33.zero (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb34, runBlock_reg _ _ _ (20 : Fin 32) s33.zero (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by
    rw [rb34, runBlock_reg _ _ _ (21 : Fin 32) s33.zero (by decide), g33_21]
  have g34_24 : reg n34 (24 : Fin 32) = trl := by
    rw [rb34, runBlock_reg _ _ _ (24 : Fin 32) s33.zero (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = x25 := by
    rw [rb34, runBlock_reg _ _ _ (25 : Fin 32) s33.zero (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by
    rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
  have g34_10 : reg n34 a0 = B + 0x21A0 + BitVec.ofNat 32 0xD1 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svL8aaa8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_9, g33_10, g33_11, g33_12, g33_18, g33_19, g33_20, g33_21, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g34_11 : reg n34 a1 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svL8aaa8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_9, g33_10, g33_11, g33_12, g33_18, g33_19, g33_20, g33_21, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g34_12 : reg n34 a2 = BitVec.ofNat 32 0x5F := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svL8aaa8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_9, g33_10, g33_11, g33_12, g33_18, g33_19, g33_20, g33_21, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m34]; exact w33_24
  have w34_28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m34]; exact w33_28
  have w34_2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m34]; exact w33_2c
  have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m34]; exact w33_30
  have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m34]; exact w33_34
  have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m34]; exact w33_38
  have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m34]; exact w33_3c
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m34]; exact w33_40
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m34]; exact w33_44
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m34]; exact w33_48
  have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m34]; exact w33_4c
  have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m34]; exact w33_50
  have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m34]; exact w33_54
  have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m34]; exact w33_58
  have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m34]; exact w33_5c
  have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m34]; exact w33_60
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m34]; exact w33_64
  have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m34]; exact w33_68
  have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m34]; exact w33_6c
  have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m34]; exact w33_70
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m34]; exact w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m34]; exact w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m34]; exact w33_7c
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m34]; exact w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m34]; exact w33_84
  have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m34]; exact w33_90
  have w34_94 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m34]; exact w33_94
  have w34_98 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m34]; exact w33_98
  have w34_9c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m34]; exact w33_9c
  have w34_a0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m34]; exact w33_a0
  have w34_a4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m34]; exact w33_a4
  have w34_a8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m34]; exact w33_a8
  have w34_ac : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m34]; exact w33_ac
  have w34_b0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m34]; exact w33_b0
  have w34_b4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m34]; exact w33_b4
  have w34_b8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [m34]; exact w33_b8
  have w34_bc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := by rw [m34]; exact w33_bc
  have b34_8d : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := by rw [m34]; exact b33_8d
  have b34_8e : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := by rw [m34]; exact b33_8e
  have b34_8f : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := by rw [m34]; exact b33_8f
  have b34_d0 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m34]; exact b33_d0
  have q34_420 : ∀ j, j < 47 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m34]; exact q33_420 j hj
  have q34_44f : ∀ j, j < 48 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m34]; exact q33_44f j hj
  have q34_a21 : ∀ j, j < 48 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m34]; exact q33_a21 j hj
  have q34_a51 : ∀ j, j < 48 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m34]; exact q33_a51 j hj
  clear q33_a51 q33_a21 q33_44f q33_420 b33_d0 b33_8f b33_8e b33_8d w33_bc w33_b8 w33_b4 w33_b0 w33_ac w33_a8 w33_a4 w33_a0 w33_9c w33_98 w33_94 w33_90 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_44 w33_40 w33_3c w33_38 w33_34 w33_30 w33_2c w33_28 w33_24 g33_27 g33_26 g33_25 g33_24 g33_21 g33_20 g33_19 g33_18 g33_12 g33_11 g33_10 g33_9 g33_4 g33_3 g33_2 V33 E33 fR33 t33 rg33 W33 K33 fr33 s33 d33
  -- 0xAB4: memcpy
  obtain ⟨n35, P35, K35, X35⟩ := sv_mc (c := 0xD1) (d := 0x420) (N := 0x5F) F E34 s34 sv_at_ab4 sv_at_ab8
    (by decide) (by decide) g34_2 g34_10 g34_11 g34_12
    (by decide) (by decide) (by decide)
  have s35 := P35.st
  have fr35 := P35.fr
  have t35 : Steps n0 n35 := t34.trans P35.steps
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.keep K35 (by decide)
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [P35.regs sp (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P35.regs (3 : Fin 32) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P35.regs (4 : Fin 32) (by decide), g34_4]
  have g35_9 : reg n35 (9 : Fin 32) = x9 := by rw [P35.regs (9 : Fin 32) (by decide), g34_9]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [P35.regs (18 : Fin 32) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [P35.regs (19 : Fin 32) (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [P35.regs (20 : Fin 32) (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [P35.regs (21 : Fin 32) (by decide), g34_21]
  have g35_24 : reg n35 (24 : Fin 32) = trl := by rw [P35.regs (24 : Fin 32) (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = x25 := by rw [P35.regs (25 : Fin 32) (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [P35.regs (26 : Fin 32) (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P35.regs (27 : Fin 32) (by decide), g34_27]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F)] := keep_kk34.trans K35.toL
  clear keep_kk34
  have w35_24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K35.w32 (by decide) (by decide)).trans w34_24
  have w35_28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K35.w32 (by decide) (by decide)).trans w34_28
  have w35_2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K35.w32 (by decide) (by decide)).trans w34_2c
  have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K35.w32 (by decide) (by decide)).trans w34_30
  have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K35.w32 (by decide) (by decide)).trans w34_34
  have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K35.w32 (by decide) (by decide)).trans w34_38
  have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K35.w32 (by decide) (by decide)).trans w34_3c
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K35.w32 (by decide) (by decide)).trans w34_40
  have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K35.w32 (by decide) (by decide)).trans w34_44
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K35.w32 (by decide) (by decide)).trans w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K35.w32 (by decide) (by decide)).trans w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K35.w32 (by decide) (by decide)).trans w34_50
  have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K35.w32 (by decide) (by decide)).trans w34_54
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K35.w32 (by decide) (by decide)).trans w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K35.w32 (by decide) (by decide)).trans w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K35.w32 (by decide) (by decide)).trans w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K35.w32 (by decide) (by decide)).trans w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K35.w32 (by decide) (by decide)).trans w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K35.w32 (by decide) (by decide)).trans w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K35.w32 (by decide) (by decide)).trans w34_70
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K35.w32 (by decide) (by decide)).trans w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K35.w32 (by decide) (by decide)).trans w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K35.w32 (by decide) (by decide)).trans w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K35.w32 (by decide) (by decide)).trans w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K35.w32 (by decide) (by decide)).trans w34_84
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K35.w32 (by decide) (by decide)).trans w34_90
  have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K35.w32 (by decide) (by decide)).trans w34_94
  have w35_98 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K35.w32 (by decide) (by decide)).trans w34_98
  have w35_9c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K35.w32 (by decide) (by decide)).trans w34_9c
  have w35_a0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K35.w32 (by decide) (by decide)).trans w34_a0
  have w35_a4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K35.w32 (by decide) (by decide)).trans w34_a4
  have w35_a8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K35.w32 (by decide) (by decide)).trans w34_a8
  have w35_ac : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K35.w32 (by decide) (by decide)).trans w34_ac
  have w35_b0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K35.w32 (by decide) (by decide)).trans w34_b0
  have w35_b4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K35.w32 (by decide) (by decide)).trans w34_b4
  have w35_b8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K35.w32 (by decide) (by decide)).trans w34_b8
  have w35_bc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K35.w32 (by decide) (by decide)).trans w34_bc
  have b35_8d : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K35.b8 (by decide) (by decide)).trans b34_8d
  have b35_8e : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K35.b8 (by decide) (by decide)).trans b34_8e
  have b35_8f : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K35.b8 (by decide) (by decide)).trans b34_8f
  have b35_d0 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := (K35.b8 (by decide) (by decide)).trans b34_d0
  have q35_420 : ∀ j, j < 47 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_420 j hj)
  have q35_44f : ∀ j, j < 48 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_44f j hj)
  have q35_a21 : ∀ j, j < 48 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_a21 j hj)
  have q35_a51 : ∀ j, j < 48 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K35.range (by decide) (by decide) j hj).trans (q34_a51 j hj)
  have q35_d1 : ∀ j, j < 47 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by
    rw [show 0xD1 + j = 0xD1 + (0x0 + j) by omega, X35 (0x0 + j) (by omega),
      show 0x420 + (0x0 + j) = 0x420 + j by omega]; exact q34_420 j (by omega)
  have q35_100 : ∀ j, j < 48 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by
    rw [show 0x100 + j = 0xD1 + (0x2F + j) by omega, X35 (0x2F + j) (by omega),
      show 0x420 + (0x2F + j) = 0x44F + j by omega]; exact q34_44f j (by omega)
  clear q34_a51 q34_a21 q34_44f q34_420 b34_d0 b34_8f b34_8e b34_8d w34_bc w34_b8 w34_b4 w34_b0 w34_ac w34_a8 w34_a4 w34_a0 w34_9c w34_98 w34_94 w34_90 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_44 w34_40 w34_3c w34_38 w34_34 w34_30 w34_2c w34_28 w34_24 g34_12 g34_11 g34_10 g34_27 g34_26 g34_25 g34_24 g34_21 g34_20 g34_19 g34_18 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
  -- 0xABC: sw
  obtain ⟨n36, d36, s36, fr36, K36, W36, rg36⟩ := sv_sw F E35 s35 sv_at_abc (off' := 0xABE) (c := 0x88)
    (by decide) (by rw [g35_2]; sv_addr) (by decide) (by decide)
  have t36 : Steps n0 n36 := t35.trans d36
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.keep K36 (by decide)
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [rg36 sp, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg36 (3 : Fin 32), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg36 (4 : Fin 32), g35_4]
  have g36_9 : reg n36 (9 : Fin 32) = x9 := by rw [rg36 (9 : Fin 32), g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [rg36 (18 : Fin 32), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [rg36 (19 : Fin 32), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg36 (20 : Fin 32), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [rg36 (21 : Fin 32), g35_21]
  have g36_24 : reg n36 (24 : Fin 32) = trl := by rw [rg36 (24 : Fin 32), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [rg36 (25 : Fin 32), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [rg36 (26 : Fin 32), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg36 (27 : Fin 32), g35_27]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4)] := keep_kk35.trans K36.toL
  clear keep_kk35
  have w36_24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K36.w32 (by decide) (by decide)).trans w35_24
  have w36_28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K36.w32 (by decide) (by decide)).trans w35_28
  have w36_2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K36.w32 (by decide) (by decide)).trans w35_2c
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K36.w32 (by decide) (by decide)).trans w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K36.w32 (by decide) (by decide)).trans w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K36.w32 (by decide) (by decide)).trans w35_38
  have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K36.w32 (by decide) (by decide)).trans w35_3c
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K36.w32 (by decide) (by decide)).trans w35_40
  have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K36.w32 (by decide) (by decide)).trans w35_44
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K36.w32 (by decide) (by decide)).trans w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K36.w32 (by decide) (by decide)).trans w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K36.w32 (by decide) (by decide)).trans w35_50
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K36.w32 (by decide) (by decide)).trans w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K36.w32 (by decide) (by decide)).trans w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K36.w32 (by decide) (by decide)).trans w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K36.w32 (by decide) (by decide)).trans w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K36.w32 (by decide) (by decide)).trans w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K36.w32 (by decide) (by decide)).trans w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K36.w32 (by decide) (by decide)).trans w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K36.w32 (by decide) (by decide)).trans w35_70
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K36.w32 (by decide) (by decide)).trans w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K36.w32 (by decide) (by decide)).trans w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K36.w32 (by decide) (by decide)).trans w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K36.w32 (by decide) (by decide)).trans w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K36.w32 (by decide) (by decide)).trans w35_84
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K36.w32 (by decide) (by decide)).trans w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K36.w32 (by decide) (by decide)).trans w35_94
  have w36_98 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K36.w32 (by decide) (by decide)).trans w35_98
  have w36_9c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K36.w32 (by decide) (by decide)).trans w35_9c
  have w36_a0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K36.w32 (by decide) (by decide)).trans w35_a0
  have w36_a4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K36.w32 (by decide) (by decide)).trans w35_a4
  have w36_a8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K36.w32 (by decide) (by decide)).trans w35_a8
  have w36_ac : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K36.w32 (by decide) (by decide)).trans w35_ac
  have w36_b0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K36.w32 (by decide) (by decide)).trans w35_b0
  have w36_b4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K36.w32 (by decide) (by decide)).trans w35_b4
  have w36_b8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K36.w32 (by decide) (by decide)).trans w35_b8
  have w36_bc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K36.w32 (by decide) (by decide)).trans w35_bc
  have b36_8d : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K36.b8 (by decide) (by decide)).trans b35_8d
  have b36_8e : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K36.b8 (by decide) (by decide)).trans b35_8e
  have b36_8f : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K36.b8 (by decide) (by decide)).trans b35_8f
  have b36_d0 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := (K36.b8 (by decide) (by decide)).trans b35_d0
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := by rw [W36, g35_9]
  have q36_d1 : ∀ j, j < 47 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K36.range (by decide) (by decide) j hj).trans (q35_d1 j hj)
  have q36_100 : ∀ j, j < 48 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K36.range (by decide) (by decide) j hj).trans (q35_100 j hj)
  have q36_420 : ∀ j, j < 47 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K36.range (by decide) (by decide) j hj).trans (q35_420 j hj)
  have q36_44f : ∀ j, j < 48 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K36.range (by decide) (by decide) j hj).trans (q35_44f j hj)
  have q36_a21 : ∀ j, j < 48 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K36.range (by decide) (by decide) j hj).trans (q35_a21 j hj)
  have q36_a51 : ∀ j, j < 48 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K36.range (by decide) (by decide) j hj).trans (q35_a51 j hj)
  clear q35_100 q35_d1 q35_a51 q35_a21 q35_44f q35_420 b35_d0 b35_8f b35_8e b35_8d w35_bc w35_b8 w35_b4 w35_b0 w35_ac w35_a8 w35_a4 w35_a0 w35_9c w35_98 w35_94 w35_90 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 w35_2c w35_28 w35_24 g35_27 g35_26 g35_25 g35_24 g35_21 g35_20 g35_19 g35_18 g35_9 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 s35 X35 K35 P35
  -- 0xABE: sb
  obtain ⟨n37, d37, s37, fr37, K37, W37, rg37⟩ := sv_sb F E36 s36 sv_at_abe (off' := 0xAC2) (c := 0x8C)
    (by decide) (by rw [g36_2]; sv_addr) (by decide)
  have t37 : Steps n0 n37 := t36.trans d37
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.keep K37 (by decide)
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [rg37 sp, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg37 (3 : Fin 32), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg37 (4 : Fin 32), g36_4]
  have g37_9 : reg n37 (9 : Fin 32) = x9 := by rw [rg37 (9 : Fin 32), g36_9]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [rg37 (18 : Fin 32), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [rg37 (19 : Fin 32), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg37 (20 : Fin 32), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [rg37 (21 : Fin 32), g36_21]
  have g37_24 : reg n37 (24 : Fin 32) = trl := by rw [rg37 (24 : Fin 32), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = x25 := by rw [rg37 (25 : Fin 32), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [rg37 (26 : Fin 32), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg37 (27 : Fin 32), g36_27]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1)] := keep_kk36.trans K37.toL
  clear keep_kk36
  have w37_24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K37.w32 (by decide) (by decide)).trans w36_24
  have w37_28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K37.w32 (by decide) (by decide)).trans w36_28
  have w37_2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K37.w32 (by decide) (by decide)).trans w36_2c
  have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K37.w32 (by decide) (by decide)).trans w36_30
  have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K37.w32 (by decide) (by decide)).trans w36_34
  have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K37.w32 (by decide) (by decide)).trans w36_38
  have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K37.w32 (by decide) (by decide)).trans w36_3c
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K37.w32 (by decide) (by decide)).trans w36_40
  have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K37.w32 (by decide) (by decide)).trans w36_44
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K37.w32 (by decide) (by decide)).trans w36_48
  have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K37.w32 (by decide) (by decide)).trans w36_4c
  have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K37.w32 (by decide) (by decide)).trans w36_50
  have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K37.w32 (by decide) (by decide)).trans w36_54
  have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K37.w32 (by decide) (by decide)).trans w36_58
  have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K37.w32 (by decide) (by decide)).trans w36_5c
  have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K37.w32 (by decide) (by decide)).trans w36_60
  have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K37.w32 (by decide) (by decide)).trans w36_64
  have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K37.w32 (by decide) (by decide)).trans w36_68
  have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K37.w32 (by decide) (by decide)).trans w36_6c
  have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K37.w32 (by decide) (by decide)).trans w36_70
  have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K37.w32 (by decide) (by decide)).trans w36_74
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K37.w32 (by decide) (by decide)).trans w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K37.w32 (by decide) (by decide)).trans w36_7c
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K37.w32 (by decide) (by decide)).trans w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K37.w32 (by decide) (by decide)).trans w36_84
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := (K37.w32 (by decide) (by decide)).trans w36_88
  have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K37.w32 (by decide) (by decide)).trans w36_90
  have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K37.w32 (by decide) (by decide)).trans w36_94
  have w37_98 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K37.w32 (by decide) (by decide)).trans w36_98
  have w37_9c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K37.w32 (by decide) (by decide)).trans w36_9c
  have w37_a0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K37.w32 (by decide) (by decide)).trans w36_a0
  have w37_a4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K37.w32 (by decide) (by decide)).trans w36_a4
  have w37_a8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K37.w32 (by decide) (by decide)).trans w36_a8
  have w37_ac : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K37.w32 (by decide) (by decide)).trans w36_ac
  have w37_b0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K37.w32 (by decide) (by decide)).trans w36_b0
  have w37_b4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K37.w32 (by decide) (by decide)).trans w36_b4
  have w37_b8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K37.w32 (by decide) (by decide)).trans w36_b8
  have w37_bc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K37.w32 (by decide) (by decide)).trans w36_bc
  have b37_8d : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8D) = ((trl) >>> 8).extractLsb' 0 8 := (K37.b8 (by decide) (by decide)).trans b36_8d
  have b37_8e : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8E) = ((trl) >>> 16).extractLsb' 0 8 := (K37.b8 (by decide) (by decide)).trans b36_8e
  have b37_8f : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8F) = ((trl) >>> 24).extractLsb' 0 8 := (K37.b8 (by decide) (by decide)).trans b36_8f
  have b37_d0 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := (K37.b8 (by decide) (by decide)).trans b36_d0
  have b37_8c : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (trl).extractLsb' 0 8 := by rw [W37, g36_24]
  have q37_d1 : ∀ j, j < 47 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K37.range (by decide) (by decide) j hj).trans (q36_d1 j hj)
  have q37_100 : ∀ j, j < 48 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K37.range (by decide) (by decide) j hj).trans (q36_100 j hj)
  have q37_420 : ∀ j, j < 47 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K37.range (by decide) (by decide) j hj).trans (q36_420 j hj)
  have q37_44f : ∀ j, j < 48 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K37.range (by decide) (by decide) j hj).trans (q36_44f j hj)
  have q37_a21 : ∀ j, j < 48 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K37.range (by decide) (by decide) j hj).trans (q36_a21 j hj)
  have q37_a51 : ∀ j, j < 48 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K37.range (by decide) (by decide) j hj).trans (q36_a51 j hj)
  clear q36_a51 q36_a21 q36_44f q36_420 q36_100 q36_d1 w36_88 b36_d0 b36_8f b36_8e b36_8d w36_bc w36_b8 w36_b4 w36_b0 w36_ac w36_a8 w36_a4 w36_a0 w36_9c w36_98 w36_94 w36_90 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 w36_2c w36_28 w36_24 g36_27 g36_26 g36_25 g36_24 g36_21 g36_20 g36_19 g36_18 g36_9 g36_4 g36_3 g36_2 V36 E36 fR36 t36 rg36 W36 K36 fr36 s36 d36
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := ld_of_shr_bytes b37_8c
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x8C + 1 = B + 0x21A0 + BitVec.ofNat 32 0x8D by sv_addr]; exact b37_8d)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x8C + 2 = B + 0x21A0 + BitVec.ofNat 32 0x8E by sv_addr]; exact b37_8e)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x8C + 3 = B + 0x21A0 + BitVec.ofNat 32 0x8F by sv_addr]; exact b37_8f)
  -- 0xAC2: lw
  obtain ⟨n38, d38, u38⟩ := s37.lw E37.self sv_at_ac2 (off' := 0xAC4) (by decide)
    (by rw [g37_2, show B + 0x21A0 + 0x58 = B + 0x21A0 + BitVec.ofNat 32 0x58 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s38 : St n38.mem SV n38 0xAC4 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans (.single d38)
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_4]
  have g38_9 : reg n38 (9 : Fin 32) = x9 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_9]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, upd_ne (by decide) (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_21]
  have g38_24 : reg n38 (24 : Fin 32) = trl := by rw [u38.regs, upd_ne (by decide) (by decide), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = x25 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_27]
  have g38_10 : reg n38 a0 = w58 := by
    rw [u38.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g37_2, show B + 0x21A0 + 0x58 = B + 0x21A0 + BitVec.ofNat 32 0x58 by sv_addr, w37_58]
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1)] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have w38_24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m38]; exact w37_24
  have w38_28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m38]; exact w37_28
  have w38_2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m38]; exact w37_2c
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m38]; exact w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m38]; exact w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m38]; exact w37_38
  have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m38]; exact w37_3c
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m38]; exact w37_40
  have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m38]; exact w37_44
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m38]; exact w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m38]; exact w37_4c
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m38]; exact w37_50
  have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m38]; exact w37_54
  have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m38]; exact w37_58
  have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m38]; exact w37_5c
  have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m38]; exact w37_60
  have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m38]; exact w37_64
  have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m38]; exact w37_68
  have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m38]; exact w37_6c
  have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m38]; exact w37_70
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m38]; exact w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m38]; exact w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m38]; exact w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m38]; exact w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m38]; exact w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := by rw [m38]; exact w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := by rw [m38]; exact w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m38]; exact w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m38]; exact w37_94
  have w38_98 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m38]; exact w37_98
  have w38_9c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m38]; exact w37_9c
  have w38_a0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m38]; exact w37_a0
  have w38_a4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m38]; exact w37_a4
  have w38_a8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m38]; exact w37_a8
  have w38_ac : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m38]; exact w37_ac
  have w38_b0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m38]; exact w37_b0
  have w38_b4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m38]; exact w37_b4
  have w38_b8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [m38]; exact w37_b8
  have w38_bc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := by rw [m38]; exact w37_bc
  have b38_d0 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m38]; exact b37_d0
  have q38_d1 : ∀ j, j < 47 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m38]; exact q37_d1 j hj
  have q38_100 : ∀ j, j < 48 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m38]; exact q37_100 j hj
  have q38_420 : ∀ j, j < 47 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m38]; exact q37_420 j hj
  have q38_44f : ∀ j, j < 48 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m38]; exact q37_44f j hj
  have q38_a21 : ∀ j, j < 48 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m38]; exact q37_a21 j hj
  have q38_a51 : ∀ j, j < 48 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m38]; exact q37_a51 j hj
  clear q37_a51 q37_a21 q37_44f q37_420 q37_100 q37_d1 b37_8c b37_d0 b37_8f b37_8e b37_8d w37_bc w37_b8 w37_b4 w37_b0 w37_ac w37_a8 w37_a4 w37_a0 w37_9c w37_98 w37_94 w37_90 w37_88 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_44 w37_40 w37_3c w37_38 w37_34 w37_30 w37_2c w37_28 w37_24 g37_27 g37_26 g37_25 g37_24 g37_21 g37_20 g37_19 g37_18 g37_9 g37_4 g37_3 g37_2 V37 E37 fR37 t37 rg37 W37 K37 fr37 s37 d37
  -- 0xAC4: sw
  obtain ⟨n39, d39, s39, fr39, K39, W39, rg39⟩ := sv_sw F E38 s38 sv_at_ac4 (off' := 0xAC6) (c := 0xC0)
    (by decide) (by rw [g38_2]; sv_addr) (by decide) (by decide)
  have t39 : Steps n0 n39 := t38.trans d39
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.keep K39 (by decide)
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [rg39 sp, g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg39 (3 : Fin 32), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg39 (4 : Fin 32), g38_4]
  have g39_9 : reg n39 (9 : Fin 32) = x9 := by rw [rg39 (9 : Fin 32), g38_9]
  have g39_10 : reg n39 a0 = w58 := by rw [rg39 a0, g38_10]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [rg39 (18 : Fin 32), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [rg39 (19 : Fin 32), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg39 (20 : Fin 32), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [rg39 (21 : Fin 32), g38_21]
  have g39_24 : reg n39 (24 : Fin 32) = trl := by rw [rg39 (24 : Fin 32), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = x25 := by rw [rg39 (25 : Fin 32), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [rg39 (26 : Fin 32), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg39 (27 : Fin 32), g38_27]
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4)] := keep_kk38.trans K39.toL
  clear keep_kk38
  have w39_24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K39.w32 (by decide) (by decide)).trans w38_24
  have w39_28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K39.w32 (by decide) (by decide)).trans w38_28
  have w39_2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K39.w32 (by decide) (by decide)).trans w38_2c
  have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K39.w32 (by decide) (by decide)).trans w38_30
  have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K39.w32 (by decide) (by decide)).trans w38_34
  have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K39.w32 (by decide) (by decide)).trans w38_38
  have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K39.w32 (by decide) (by decide)).trans w38_3c
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K39.w32 (by decide) (by decide)).trans w38_40
  have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K39.w32 (by decide) (by decide)).trans w38_44
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K39.w32 (by decide) (by decide)).trans w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K39.w32 (by decide) (by decide)).trans w38_4c
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K39.w32 (by decide) (by decide)).trans w38_50
  have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K39.w32 (by decide) (by decide)).trans w38_54
  have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K39.w32 (by decide) (by decide)).trans w38_58
  have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K39.w32 (by decide) (by decide)).trans w38_5c
  have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K39.w32 (by decide) (by decide)).trans w38_60
  have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K39.w32 (by decide) (by decide)).trans w38_64
  have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K39.w32 (by decide) (by decide)).trans w38_68
  have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K39.w32 (by decide) (by decide)).trans w38_6c
  have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K39.w32 (by decide) (by decide)).trans w38_70
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K39.w32 (by decide) (by decide)).trans w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K39.w32 (by decide) (by decide)).trans w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K39.w32 (by decide) (by decide)).trans w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K39.w32 (by decide) (by decide)).trans w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K39.w32 (by decide) (by decide)).trans w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := (K39.w32 (by decide) (by decide)).trans w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := (K39.w32 (by decide) (by decide)).trans w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K39.w32 (by decide) (by decide)).trans w38_90
  have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K39.w32 (by decide) (by decide)).trans w38_94
  have w39_98 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K39.w32 (by decide) (by decide)).trans w38_98
  have w39_9c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K39.w32 (by decide) (by decide)).trans w38_9c
  have w39_a0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K39.w32 (by decide) (by decide)).trans w38_a0
  have w39_a4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K39.w32 (by decide) (by decide)).trans w38_a4
  have w39_a8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K39.w32 (by decide) (by decide)).trans w38_a8
  have w39_ac : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K39.w32 (by decide) (by decide)).trans w38_ac
  have w39_b0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K39.w32 (by decide) (by decide)).trans w38_b0
  have w39_b4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K39.w32 (by decide) (by decide)).trans w38_b4
  have w39_b8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K39.w32 (by decide) (by decide)).trans w38_b8
  have w39_bc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K39.w32 (by decide) (by decide)).trans w38_bc
  have b39_d0 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := (K39.b8 (by decide) (by decide)).trans b38_d0
  have w39_c0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := by rw [W39, g38_10]
  have q39_d1 : ∀ j, j < 47 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_d1 j hj)
  have q39_100 : ∀ j, j < 48 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_100 j hj)
  have q39_420 : ∀ j, j < 47 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_420 j hj)
  have q39_44f : ∀ j, j < 48 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_44f j hj)
  have q39_a21 : ∀ j, j < 48 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_a21 j hj)
  have q39_a51 : ∀ j, j < 48 → n39.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K39.range (by decide) (by decide) j hj).trans (q38_a51 j hj)
  clear q38_a51 q38_a21 q38_44f q38_420 q38_100 q38_d1 b38_d0 w38_bc w38_b8 w38_b4 w38_b0 w38_ac w38_a8 w38_a4 w38_a0 w38_9c w38_98 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_44 w38_40 w38_3c w38_38 w38_34 w38_30 w38_2c w38_28 w38_24 g38_10 g38_27 g38_26 g38_25 g38_24 g38_21 g38_20 g38_19 g38_18 g38_9 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38 w37_8c
  -- 0xAC6: lw
  obtain ⟨n40, d40, u40⟩ := s39.lw E39.self sv_at_ac6 (off' := 0xAC8) (by decide)
    (by rw [g39_2, show B + 0x21A0 + 0x54 = B + 0x21A0 + BitVec.ofNat 32 0x54 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s40 : St n40.mem SV n40 0xAC8 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have fr40 : ∀ x, SvR B x → n40.mem x = n39.mem x := fun x _ => by rw [m40]
  have t40 : Steps n0 n40 := t39.trans (.single d40)
  have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.same m40
  have g40_2 : reg n40 sp = B + 0x21A0 := by rw [u40.regs, upd_ne (by decide) (by decide), g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u40.regs, upd_ne (by decide) (by decide), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u40.regs, upd_ne (by decide) (by decide), g39_4]
  have g40_9 : reg n40 (9 : Fin 32) = x9 := by rw [u40.regs, upd_ne (by decide) (by decide), g39_9]
  have g40_18 : reg n40 (18 : Fin 32) = out := by rw [u40.regs, upd_ne (by decide) (by decide), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [u40.regs, upd_ne (by decide) (by decide), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u40.regs, upd_ne (by decide) (by decide), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = x21 := by rw [u40.regs, upd_ne (by decide) (by decide), g39_21]
  have g40_24 : reg n40 (24 : Fin 32) = trl := by rw [u40.regs, upd_ne (by decide) (by decide), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = x25 := by rw [u40.regs, upd_ne (by decide) (by decide), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by rw [u40.regs, upd_ne (by decide) (by decide), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u40.regs, upd_ne (by decide) (by decide), g39_27]
  have g40_10 : reg n40 a0 = w54 := by
    rw [u40.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g39_2, show B + 0x21A0 + 0x54 = B + 0x21A0 + BitVec.ofNat 32 0x54 by sv_addr, w39_54]
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4)] := by rw [m40]; exact keep_kk39
  clear keep_kk39
  have w40_24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m40]; exact w39_24
  have w40_28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m40]; exact w39_28
  have w40_2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m40]; exact w39_2c
  have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m40]; exact w39_30
  have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m40]; exact w39_34
  have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m40]; exact w39_38
  have w40_3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m40]; exact w39_3c
  have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m40]; exact w39_40
  have w40_44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m40]; exact w39_44
  have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m40]; exact w39_48
  have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m40]; exact w39_4c
  have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m40]; exact w39_50
  have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m40]; exact w39_54
  have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m40]; exact w39_58
  have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m40]; exact w39_5c
  have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m40]; exact w39_60
  have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m40]; exact w39_64
  have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m40]; exact w39_68
  have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m40]; exact w39_6c
  have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m40]; exact w39_70
  have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m40]; exact w39_74
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m40]; exact w39_78
  have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m40]; exact w39_7c
  have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m40]; exact w39_80
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m40]; exact w39_84
  have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := by rw [m40]; exact w39_88
  have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := by rw [m40]; exact w39_8c
  have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m40]; exact w39_90
  have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m40]; exact w39_94
  have w40_98 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m40]; exact w39_98
  have w40_9c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m40]; exact w39_9c
  have w40_a0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m40]; exact w39_a0
  have w40_a4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m40]; exact w39_a4
  have w40_a8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m40]; exact w39_a8
  have w40_ac : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m40]; exact w39_ac
  have w40_b0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m40]; exact w39_b0
  have w40_b4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m40]; exact w39_b4
  have w40_b8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [m40]; exact w39_b8
  have w40_bc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := by rw [m40]; exact w39_bc
  have w40_c0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := by rw [m40]; exact w39_c0
  have b40_d0 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m40]; exact b39_d0
  have q40_d1 : ∀ j, j < 47 → n40.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m40]; exact q39_d1 j hj
  have q40_100 : ∀ j, j < 48 → n40.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m40]; exact q39_100 j hj
  have q40_420 : ∀ j, j < 47 → n40.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m40]; exact q39_420 j hj
  have q40_44f : ∀ j, j < 48 → n40.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m40]; exact q39_44f j hj
  have q40_a21 : ∀ j, j < 48 → n40.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m40]; exact q39_a21 j hj
  have q40_a51 : ∀ j, j < 48 → n40.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m40]; exact q39_a51 j hj
  clear q39_a51 q39_a21 q39_44f q39_420 q39_100 q39_d1 w39_c0 b39_d0 w39_bc w39_b8 w39_b4 w39_b0 w39_ac w39_a8 w39_a4 w39_a0 w39_9c w39_98 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_5c w39_58 w39_54 w39_50 w39_4c w39_48 w39_44 w39_40 w39_3c w39_38 w39_34 w39_30 w39_2c w39_28 w39_24 g39_27 g39_26 g39_25 g39_24 g39_21 g39_20 g39_19 g39_18 g39_10 g39_9 g39_4 g39_3 g39_2 V39 E39 fR39 t39 rg39 W39 K39 fr39 s39 d39
  -- 0xAC8: sw
  obtain ⟨n41, d41, s41, fr41, K41, W41, rg41⟩ := sv_sw F E40 s40 sv_at_ac8 (off' := 0xACA) (c := 0xC4)
    (by decide) (by rw [g40_2]; sv_addr) (by decide) (by decide)
  have t41 : Steps n0 n41 := t40.trans d41
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.keep K41 (by decide)
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [rg41 sp, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg41 (3 : Fin 32), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg41 (4 : Fin 32), g40_4]
  have g41_9 : reg n41 (9 : Fin 32) = x9 := by rw [rg41 (9 : Fin 32), g40_9]
  have g41_10 : reg n41 a0 = w54 := by rw [rg41 a0, g40_10]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [rg41 (18 : Fin 32), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [rg41 (19 : Fin 32), g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg41 (20 : Fin 32), g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [rg41 (21 : Fin 32), g40_21]
  have g41_24 : reg n41 (24 : Fin 32) = trl := by rw [rg41 (24 : Fin 32), g40_24]
  have g41_25 : reg n41 (25 : Fin 32) = x25 := by rw [rg41 (25 : Fin 32), g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [rg41 (26 : Fin 32), g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg41 (27 : Fin 32), g40_27]
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4)] := keep_kk40.trans K41.toL
  clear keep_kk40
  have w41_24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K41.w32 (by decide) (by decide)).trans w40_24
  have w41_28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K41.w32 (by decide) (by decide)).trans w40_28
  have w41_2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K41.w32 (by decide) (by decide)).trans w40_2c
  have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K41.w32 (by decide) (by decide)).trans w40_30
  have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K41.w32 (by decide) (by decide)).trans w40_34
  have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K41.w32 (by decide) (by decide)).trans w40_38
  have w41_3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K41.w32 (by decide) (by decide)).trans w40_3c
  have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K41.w32 (by decide) (by decide)).trans w40_40
  have w41_44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K41.w32 (by decide) (by decide)).trans w40_44
  have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K41.w32 (by decide) (by decide)).trans w40_48
  have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K41.w32 (by decide) (by decide)).trans w40_4c
  have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K41.w32 (by decide) (by decide)).trans w40_50
  have w41_54 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K41.w32 (by decide) (by decide)).trans w40_54
  have w41_58 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K41.w32 (by decide) (by decide)).trans w40_58
  have w41_5c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K41.w32 (by decide) (by decide)).trans w40_5c
  have w41_60 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K41.w32 (by decide) (by decide)).trans w40_60
  have w41_64 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K41.w32 (by decide) (by decide)).trans w40_64
  have w41_68 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K41.w32 (by decide) (by decide)).trans w40_68
  have w41_6c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K41.w32 (by decide) (by decide)).trans w40_6c
  have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K41.w32 (by decide) (by decide)).trans w40_70
  have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K41.w32 (by decide) (by decide)).trans w40_74
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K41.w32 (by decide) (by decide)).trans w40_78
  have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K41.w32 (by decide) (by decide)).trans w40_7c
  have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K41.w32 (by decide) (by decide)).trans w40_80
  have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K41.w32 (by decide) (by decide)).trans w40_84
  have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := (K41.w32 (by decide) (by decide)).trans w40_88
  have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := (K41.w32 (by decide) (by decide)).trans w40_8c
  have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K41.w32 (by decide) (by decide)).trans w40_90
  have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K41.w32 (by decide) (by decide)).trans w40_94
  have w41_98 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K41.w32 (by decide) (by decide)).trans w40_98
  have w41_9c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K41.w32 (by decide) (by decide)).trans w40_9c
  have w41_a0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K41.w32 (by decide) (by decide)).trans w40_a0
  have w41_a4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K41.w32 (by decide) (by decide)).trans w40_a4
  have w41_a8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K41.w32 (by decide) (by decide)).trans w40_a8
  have w41_ac : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K41.w32 (by decide) (by decide)).trans w40_ac
  have w41_b0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K41.w32 (by decide) (by decide)).trans w40_b0
  have w41_b4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K41.w32 (by decide) (by decide)).trans w40_b4
  have w41_b8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K41.w32 (by decide) (by decide)).trans w40_b8
  have w41_bc : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K41.w32 (by decide) (by decide)).trans w40_bc
  have w41_c0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := (K41.w32 (by decide) (by decide)).trans w40_c0
  have b41_d0 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := (K41.b8 (by decide) (by decide)).trans b40_d0
  have w41_c4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := by rw [W41, g40_10]
  have q41_d1 : ∀ j, j < 47 → n41.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K41.range (by decide) (by decide) j hj).trans (q40_d1 j hj)
  have q41_100 : ∀ j, j < 48 → n41.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K41.range (by decide) (by decide) j hj).trans (q40_100 j hj)
  have q41_420 : ∀ j, j < 47 → n41.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K41.range (by decide) (by decide) j hj).trans (q40_420 j hj)
  have q41_44f : ∀ j, j < 48 → n41.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K41.range (by decide) (by decide) j hj).trans (q40_44f j hj)
  have q41_a21 : ∀ j, j < 48 → n41.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K41.range (by decide) (by decide) j hj).trans (q40_a21 j hj)
  have q41_a51 : ∀ j, j < 48 → n41.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K41.range (by decide) (by decide) j hj).trans (q40_a51 j hj)
  clear q40_a51 q40_a21 q40_44f q40_420 q40_100 q40_d1 b40_d0 w40_c0 w40_bc w40_b8 w40_b4 w40_b0 w40_ac w40_a8 w40_a4 w40_a0 w40_9c w40_98 w40_94 w40_90 w40_8c w40_88 w40_84 w40_80 w40_7c w40_78 w40_74 w40_70 w40_6c w40_68 w40_64 w40_60 w40_5c w40_58 w40_54 w40_50 w40_4c w40_48 w40_44 w40_40 w40_3c w40_38 w40_34 w40_30 w40_2c w40_28 w40_24 g40_10 g40_27 g40_26 g40_25 g40_24 g40_21 g40_20 g40_19 g40_18 g40_9 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 m40 s40 u40 d40
  -- 0xACA: lw
  obtain ⟨n42, d42, u42⟩ := s41.lw E41.self sv_at_aca (off' := 0xACC) (by decide)
    (by rw [g41_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s42 : St n42.mem SV n42 0xACC (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
  have t42 : Steps n0 n42 := t41.trans (.single d42)
  have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : SvCode n42.mem := E41.fr F fr42
  have V42 : SvSaves B n42.mem v := V41.same m42
  have g42_2 : reg n42 sp = B + 0x21A0 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_2]
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u42.regs, upd_ne (by decide) (by decide), g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u42.regs, upd_ne (by decide) (by decide), g41_4]
  have g42_9 : reg n42 (9 : Fin 32) = x9 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_9]
  have g42_18 : reg n42 (18 : Fin 32) = out := by rw [u42.regs, upd_ne (by decide) (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [u42.regs, upd_ne (by decide) (by decide), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = x21 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_21]
  have g42_24 : reg n42 (24 : Fin 32) = trl := by rw [u42.regs, upd_ne (by decide) (by decide), g41_24]
  have g42_25 : reg n42 (25 : Fin 32) = x25 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = x26 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_27]
  have g42_10 : reg n42 a0 = w50 := by
    rw [u42.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g41_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w41_50]
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4)] := by rw [m42]; exact keep_kk41
  clear keep_kk41
  have w42_24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m42]; exact w41_24
  have w42_28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m42]; exact w41_28
  have w42_2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m42]; exact w41_2c
  have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m42]; exact w41_30
  have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m42]; exact w41_34
  have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m42]; exact w41_38
  have w42_3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m42]; exact w41_3c
  have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m42]; exact w41_40
  have w42_44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m42]; exact w41_44
  have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m42]; exact w41_48
  have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m42]; exact w41_4c
  have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m42]; exact w41_50
  have w42_54 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m42]; exact w41_54
  have w42_58 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m42]; exact w41_58
  have w42_5c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m42]; exact w41_5c
  have w42_60 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m42]; exact w41_60
  have w42_64 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m42]; exact w41_64
  have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m42]; exact w41_68
  have w42_6c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m42]; exact w41_6c
  have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m42]; exact w41_70
  have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m42]; exact w41_74
  have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m42]; exact w41_78
  have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m42]; exact w41_7c
  have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m42]; exact w41_80
  have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m42]; exact w41_84
  have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := by rw [m42]; exact w41_88
  have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := by rw [m42]; exact w41_8c
  have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m42]; exact w41_90
  have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m42]; exact w41_94
  have w42_98 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m42]; exact w41_98
  have w42_9c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m42]; exact w41_9c
  have w42_a0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m42]; exact w41_a0
  have w42_a4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m42]; exact w41_a4
  have w42_a8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m42]; exact w41_a8
  have w42_ac : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m42]; exact w41_ac
  have w42_b0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m42]; exact w41_b0
  have w42_b4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m42]; exact w41_b4
  have w42_b8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [m42]; exact w41_b8
  have w42_bc : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := by rw [m42]; exact w41_bc
  have w42_c0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := by rw [m42]; exact w41_c0
  have w42_c4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := by rw [m42]; exact w41_c4
  have b42_d0 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m42]; exact b41_d0
  have q42_d1 : ∀ j, j < 47 → n42.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m42]; exact q41_d1 j hj
  have q42_100 : ∀ j, j < 48 → n42.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m42]; exact q41_100 j hj
  have q42_420 : ∀ j, j < 47 → n42.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m42]; exact q41_420 j hj
  have q42_44f : ∀ j, j < 48 → n42.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m42]; exact q41_44f j hj
  have q42_a21 : ∀ j, j < 48 → n42.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m42]; exact q41_a21 j hj
  have q42_a51 : ∀ j, j < 48 → n42.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m42]; exact q41_a51 j hj
  clear q41_a51 q41_a21 q41_44f q41_420 q41_100 q41_d1 w41_c4 b41_d0 w41_c0 w41_bc w41_b8 w41_b4 w41_b0 w41_ac w41_a8 w41_a4 w41_a0 w41_9c w41_98 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_74 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_44 w41_40 w41_3c w41_38 w41_34 w41_30 w41_2c w41_28 w41_24 g41_27 g41_26 g41_25 g41_24 g41_21 g41_20 g41_19 g41_18 g41_10 g41_9 g41_4 g41_3 g41_2 V41 E41 fR41 t41 rg41 W41 K41 fr41 s41 d41
  -- 0xACC: sw
  obtain ⟨n43, d43, s43, fr43, K43, W43, rg43⟩ := sv_sw F E42 s42 sv_at_acc (off' := 0xACE) (c := 0xC8)
    (by decide) (by rw [g42_2]; sv_addr) (by decide) (by decide)
  have t43 : Steps n0 n43 := t42.trans d43
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.keep K43 (by decide)
  have g43_2 : reg n43 sp = B + 0x21A0 := by rw [rg43 sp, g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg43 (3 : Fin 32), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg43 (4 : Fin 32), g42_4]
  have g43_9 : reg n43 (9 : Fin 32) = x9 := by rw [rg43 (9 : Fin 32), g42_9]
  have g43_10 : reg n43 a0 = w50 := by rw [rg43 a0, g42_10]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [rg43 (18 : Fin 32), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [rg43 (19 : Fin 32), g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg43 (20 : Fin 32), g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [rg43 (21 : Fin 32), g42_21]
  have g43_24 : reg n43 (24 : Fin 32) = trl := by rw [rg43 (24 : Fin 32), g42_24]
  have g43_25 : reg n43 (25 : Fin 32) = x25 := by rw [rg43 (25 : Fin 32), g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [rg43 (26 : Fin 32), g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg43 (27 : Fin 32), g42_27]
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4)] := keep_kk42.trans K43.toL
  clear keep_kk42
  have w43_24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K43.w32 (by decide) (by decide)).trans w42_24
  have w43_28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K43.w32 (by decide) (by decide)).trans w42_28
  have w43_2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K43.w32 (by decide) (by decide)).trans w42_2c
  have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K43.w32 (by decide) (by decide)).trans w42_30
  have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K43.w32 (by decide) (by decide)).trans w42_34
  have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K43.w32 (by decide) (by decide)).trans w42_38
  have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K43.w32 (by decide) (by decide)).trans w42_3c
  have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K43.w32 (by decide) (by decide)).trans w42_40
  have w43_44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K43.w32 (by decide) (by decide)).trans w42_44
  have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K43.w32 (by decide) (by decide)).trans w42_48
  have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K43.w32 (by decide) (by decide)).trans w42_4c
  have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K43.w32 (by decide) (by decide)).trans w42_50
  have w43_54 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K43.w32 (by decide) (by decide)).trans w42_54
  have w43_58 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K43.w32 (by decide) (by decide)).trans w42_58
  have w43_5c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K43.w32 (by decide) (by decide)).trans w42_5c
  have w43_60 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K43.w32 (by decide) (by decide)).trans w42_60
  have w43_64 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K43.w32 (by decide) (by decide)).trans w42_64
  have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K43.w32 (by decide) (by decide)).trans w42_68
  have w43_6c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K43.w32 (by decide) (by decide)).trans w42_6c
  have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K43.w32 (by decide) (by decide)).trans w42_70
  have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K43.w32 (by decide) (by decide)).trans w42_74
  have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K43.w32 (by decide) (by decide)).trans w42_78
  have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K43.w32 (by decide) (by decide)).trans w42_7c
  have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K43.w32 (by decide) (by decide)).trans w42_80
  have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K43.w32 (by decide) (by decide)).trans w42_84
  have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := (K43.w32 (by decide) (by decide)).trans w42_88
  have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := (K43.w32 (by decide) (by decide)).trans w42_8c
  have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K43.w32 (by decide) (by decide)).trans w42_90
  have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K43.w32 (by decide) (by decide)).trans w42_94
  have w43_98 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K43.w32 (by decide) (by decide)).trans w42_98
  have w43_9c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K43.w32 (by decide) (by decide)).trans w42_9c
  have w43_a0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K43.w32 (by decide) (by decide)).trans w42_a0
  have w43_a4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K43.w32 (by decide) (by decide)).trans w42_a4
  have w43_a8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K43.w32 (by decide) (by decide)).trans w42_a8
  have w43_ac : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K43.w32 (by decide) (by decide)).trans w42_ac
  have w43_b0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K43.w32 (by decide) (by decide)).trans w42_b0
  have w43_b4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K43.w32 (by decide) (by decide)).trans w42_b4
  have w43_b8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K43.w32 (by decide) (by decide)).trans w42_b8
  have w43_bc : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K43.w32 (by decide) (by decide)).trans w42_bc
  have w43_c0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := (K43.w32 (by decide) (by decide)).trans w42_c0
  have w43_c4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := (K43.w32 (by decide) (by decide)).trans w42_c4
  have b43_d0 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := (K43.b8 (by decide) (by decide)).trans b42_d0
  have w43_c8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = w50 := by rw [W43, g42_10]
  have q43_d1 : ∀ j, j < 47 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K43.range (by decide) (by decide) j hj).trans (q42_d1 j hj)
  have q43_100 : ∀ j, j < 48 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K43.range (by decide) (by decide) j hj).trans (q42_100 j hj)
  have q43_420 : ∀ j, j < 47 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K43.range (by decide) (by decide) j hj).trans (q42_420 j hj)
  have q43_44f : ∀ j, j < 48 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K43.range (by decide) (by decide) j hj).trans (q42_44f j hj)
  have q43_a21 : ∀ j, j < 48 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K43.range (by decide) (by decide) j hj).trans (q42_a21 j hj)
  have q43_a51 : ∀ j, j < 48 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K43.range (by decide) (by decide) j hj).trans (q42_a51 j hj)
  clear q42_a51 q42_a21 q42_44f q42_420 q42_100 q42_d1 b42_d0 w42_c4 w42_c0 w42_bc w42_b8 w42_b4 w42_b0 w42_ac w42_a8 w42_a4 w42_a0 w42_9c w42_98 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_44 w42_40 w42_3c w42_38 w42_34 w42_30 w42_2c w42_28 w42_24 g42_10 g42_27 g42_26 g42_25 g42_24 g42_21 g42_20 g42_19 g42_18 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 m42 s42 u42 d42
  -- 0xACE: lw
  obtain ⟨n44, d44, u44⟩ := s43.lw E43.self sv_at_ace (off' := 0xAD0) (by decide)
    (by rw [g43_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s44 : St n44.mem SV n44 0xAD0 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
  have t44 : Steps n0 n44 := t43.trans (.single d44)
  have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : SvCode n44.mem := E43.fr F fr44
  have V44 : SvSaves B n44.mem v := V43.same m44
  have g44_2 : reg n44 sp = B + 0x21A0 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_4]
  have g44_9 : reg n44 (9 : Fin 32) = x9 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_9]
  have g44_18 : reg n44 (18 : Fin 32) = out := by rw [u44.regs, upd_ne (by decide) (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [u44.regs, upd_ne (by decide) (by decide), g43_19]
  have g44_20 : reg n44 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_20]
  have g44_21 : reg n44 (21 : Fin 32) = x21 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_21]
  have g44_24 : reg n44 (24 : Fin 32) = trl := by rw [u44.regs, upd_ne (by decide) (by decide), g43_24]
  have g44_25 : reg n44 (25 : Fin 32) = x25 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_27]
  have g44_10 : reg n44 a0 = w4c := by
    rw [u44.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g43_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w43_4c]
  have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4)] := by rw [m44]; exact keep_kk43
  clear keep_kk43
  have w44_24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m44]; exact w43_24
  have w44_28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m44]; exact w43_28
  have w44_2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m44]; exact w43_2c
  have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m44]; exact w43_30
  have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m44]; exact w43_34
  have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m44]; exact w43_38
  have w44_3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m44]; exact w43_3c
  have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m44]; exact w43_40
  have w44_44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m44]; exact w43_44
  have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m44]; exact w43_48
  have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m44]; exact w43_4c
  have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m44]; exact w43_50
  have w44_54 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m44]; exact w43_54
  have w44_58 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m44]; exact w43_58
  have w44_5c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m44]; exact w43_5c
  have w44_60 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m44]; exact w43_60
  have w44_64 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m44]; exact w43_64
  have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m44]; exact w43_68
  have w44_6c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m44]; exact w43_6c
  have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m44]; exact w43_70
  have w44_74 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m44]; exact w43_74
  have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m44]; exact w43_78
  have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m44]; exact w43_7c
  have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m44]; exact w43_80
  have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m44]; exact w43_84
  have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := by rw [m44]; exact w43_88
  have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := by rw [m44]; exact w43_8c
  have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m44]; exact w43_90
  have w44_94 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m44]; exact w43_94
  have w44_98 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m44]; exact w43_98
  have w44_9c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m44]; exact w43_9c
  have w44_a0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m44]; exact w43_a0
  have w44_a4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m44]; exact w43_a4
  have w44_a8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m44]; exact w43_a8
  have w44_ac : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m44]; exact w43_ac
  have w44_b0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m44]; exact w43_b0
  have w44_b4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m44]; exact w43_b4
  have w44_b8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [m44]; exact w43_b8
  have w44_bc : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := by rw [m44]; exact w43_bc
  have w44_c0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := by rw [m44]; exact w43_c0
  have w44_c4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := by rw [m44]; exact w43_c4
  have w44_c8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = w50 := by rw [m44]; exact w43_c8
  have b44_d0 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m44]; exact b43_d0
  have q44_d1 : ∀ j, j < 47 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m44]; exact q43_d1 j hj
  have q44_100 : ∀ j, j < 48 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m44]; exact q43_100 j hj
  have q44_420 : ∀ j, j < 47 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m44]; exact q43_420 j hj
  have q44_44f : ∀ j, j < 48 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m44]; exact q43_44f j hj
  have q44_a21 : ∀ j, j < 48 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m44]; exact q43_a21 j hj
  have q44_a51 : ∀ j, j < 48 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m44]; exact q43_a51 j hj
  clear q43_a51 q43_a21 q43_44f q43_420 q43_100 q43_d1 w43_c8 b43_d0 w43_c4 w43_c0 w43_bc w43_b8 w43_b4 w43_b0 w43_ac w43_a8 w43_a4 w43_a0 w43_9c w43_98 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_74 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_44 w43_40 w43_3c w43_38 w43_34 w43_30 w43_2c w43_28 w43_24 g43_27 g43_26 g43_25 g43_24 g43_21 g43_20 g43_19 g43_18 g43_10 g43_9 g43_4 g43_3 g43_2 V43 E43 fR43 t43 rg43 W43 K43 fr43 s43 d43
  -- 0xAD0: sw
  obtain ⟨n45, d45, s45, fr45, K45, W45, rg45⟩ := sv_sw F E44 s44 sv_at_ad0 (off' := 0xAD2) (c := 0xCC)
    (by decide) (by rw [g44_2]; sv_addr) (by decide) (by decide)
  have t45 : Steps n0 n45 := t44.trans d45
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.keep K45 (by decide)
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [rg45 sp, g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg45 (3 : Fin 32), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg45 (4 : Fin 32), g44_4]
  have g45_9 : reg n45 (9 : Fin 32) = x9 := by rw [rg45 (9 : Fin 32), g44_9]
  have g45_10 : reg n45 a0 = w4c := by rw [rg45 a0, g44_10]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [rg45 (18 : Fin 32), g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [rg45 (19 : Fin 32), g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg45 (20 : Fin 32), g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [rg45 (21 : Fin 32), g44_21]
  have g45_24 : reg n45 (24 : Fin 32) = trl := by rw [rg45 (24 : Fin 32), g44_24]
  have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [rg45 (25 : Fin 32), g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [rg45 (26 : Fin 32), g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg45 (27 : Fin 32), g44_27]
  have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4), (0xCC, 0x4)] := keep_kk44.trans K45.toL
  clear keep_kk44
  have w45_24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K45.w32 (by decide) (by decide)).trans w44_24
  have w45_28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K45.w32 (by decide) (by decide)).trans w44_28
  have w45_2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K45.w32 (by decide) (by decide)).trans w44_2c
  have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K45.w32 (by decide) (by decide)).trans w44_30
  have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K45.w32 (by decide) (by decide)).trans w44_34
  have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K45.w32 (by decide) (by decide)).trans w44_38
  have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K45.w32 (by decide) (by decide)).trans w44_3c
  have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K45.w32 (by decide) (by decide)).trans w44_40
  have w45_44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K45.w32 (by decide) (by decide)).trans w44_44
  have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K45.w32 (by decide) (by decide)).trans w44_48
  have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K45.w32 (by decide) (by decide)).trans w44_4c
  have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K45.w32 (by decide) (by decide)).trans w44_50
  have w45_54 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K45.w32 (by decide) (by decide)).trans w44_54
  have w45_58 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K45.w32 (by decide) (by decide)).trans w44_58
  have w45_5c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K45.w32 (by decide) (by decide)).trans w44_5c
  have w45_60 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K45.w32 (by decide) (by decide)).trans w44_60
  have w45_64 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K45.w32 (by decide) (by decide)).trans w44_64
  have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K45.w32 (by decide) (by decide)).trans w44_68
  have w45_6c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K45.w32 (by decide) (by decide)).trans w44_6c
  have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K45.w32 (by decide) (by decide)).trans w44_70
  have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K45.w32 (by decide) (by decide)).trans w44_74
  have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K45.w32 (by decide) (by decide)).trans w44_78
  have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K45.w32 (by decide) (by decide)).trans w44_7c
  have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K45.w32 (by decide) (by decide)).trans w44_80
  have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K45.w32 (by decide) (by decide)).trans w44_84
  have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := (K45.w32 (by decide) (by decide)).trans w44_88
  have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := (K45.w32 (by decide) (by decide)).trans w44_8c
  have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K45.w32 (by decide) (by decide)).trans w44_90
  have w45_94 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K45.w32 (by decide) (by decide)).trans w44_94
  have w45_98 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K45.w32 (by decide) (by decide)).trans w44_98
  have w45_9c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K45.w32 (by decide) (by decide)).trans w44_9c
  have w45_a0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K45.w32 (by decide) (by decide)).trans w44_a0
  have w45_a4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K45.w32 (by decide) (by decide)).trans w44_a4
  have w45_a8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K45.w32 (by decide) (by decide)).trans w44_a8
  have w45_ac : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K45.w32 (by decide) (by decide)).trans w44_ac
  have w45_b0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K45.w32 (by decide) (by decide)).trans w44_b0
  have w45_b4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K45.w32 (by decide) (by decide)).trans w44_b4
  have w45_b8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K45.w32 (by decide) (by decide)).trans w44_b8
  have w45_bc : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K45.w32 (by decide) (by decide)).trans w44_bc
  have w45_c0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := (K45.w32 (by decide) (by decide)).trans w44_c0
  have w45_c4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := (K45.w32 (by decide) (by decide)).trans w44_c4
  have w45_c8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = w50 := (K45.w32 (by decide) (by decide)).trans w44_c8
  have b45_d0 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := (K45.b8 (by decide) (by decide)).trans b44_d0
  have w45_cc : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = w4c := by rw [W45, g44_10]
  have q45_d1 : ∀ j, j < 47 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K45.range (by decide) (by decide) j hj).trans (q44_d1 j hj)
  have q45_100 : ∀ j, j < 48 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K45.range (by decide) (by decide) j hj).trans (q44_100 j hj)
  have q45_420 : ∀ j, j < 47 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K45.range (by decide) (by decide) j hj).trans (q44_420 j hj)
  have q45_44f : ∀ j, j < 48 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K45.range (by decide) (by decide) j hj).trans (q44_44f j hj)
  have q45_a21 : ∀ j, j < 48 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K45.range (by decide) (by decide) j hj).trans (q44_a21 j hj)
  have q45_a51 : ∀ j, j < 48 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K45.range (by decide) (by decide) j hj).trans (q44_a51 j hj)
  clear q44_a51 q44_a21 q44_44f q44_420 q44_100 q44_d1 b44_d0 w44_c8 w44_c4 w44_c0 w44_bc w44_b8 w44_b4 w44_b0 w44_ac w44_a8 w44_a4 w44_a0 w44_9c w44_98 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_74 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_44 w44_40 w44_3c w44_38 w44_34 w44_30 w44_2c w44_28 w44_24 g44_10 g44_27 g44_26 g44_25 g44_24 g44_21 g44_20 g44_19 g44_18 g44_9 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 m44 s44 u44 d44
  -- 0xAD2: sw
  obtain ⟨n46, d46, s46, fr46, K46, W46, rg46⟩ := sv_sw F E45 s45 sv_at_ad2 (off' := 0xAD6) (c := 0x130)
    (by decide) (by rw [g45_2]; sv_addr) (by decide) (by decide)
  have t46 : Steps n0 n46 := t45.trans d46
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.keep K46 (by decide)
  have g46_2 : reg n46 sp = B + 0x21A0 := by rw [rg46 sp, g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg46 (3 : Fin 32), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg46 (4 : Fin 32), g45_4]
  have g46_9 : reg n46 (9 : Fin 32) = x9 := by rw [rg46 (9 : Fin 32), g45_9]
  have g46_10 : reg n46 a0 = w4c := by rw [rg46 a0, g45_10]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [rg46 (18 : Fin 32), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [rg46 (19 : Fin 32), g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg46 (20 : Fin 32), g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [rg46 (21 : Fin 32), g45_21]
  have g46_24 : reg n46 (24 : Fin 32) = trl := by rw [rg46 (24 : Fin 32), g45_24]
  have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [rg46 (25 : Fin 32), g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [rg46 (26 : Fin 32), g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg46 (27 : Fin 32), g45_27]
  have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4), (0xCC, 0x4), (0x130, 0x4)] := keep_kk45.trans K46.toL
  clear keep_kk45
  have w46_24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K46.w32 (by decide) (by decide)).trans w45_24
  have w46_28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K46.w32 (by decide) (by decide)).trans w45_28
  have w46_2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K46.w32 (by decide) (by decide)).trans w45_2c
  have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K46.w32 (by decide) (by decide)).trans w45_30
  have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K46.w32 (by decide) (by decide)).trans w45_34
  have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K46.w32 (by decide) (by decide)).trans w45_38
  have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K46.w32 (by decide) (by decide)).trans w45_3c
  have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K46.w32 (by decide) (by decide)).trans w45_40
  have w46_44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K46.w32 (by decide) (by decide)).trans w45_44
  have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K46.w32 (by decide) (by decide)).trans w45_48
  have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K46.w32 (by decide) (by decide)).trans w45_4c
  have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K46.w32 (by decide) (by decide)).trans w45_50
  have w46_54 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K46.w32 (by decide) (by decide)).trans w45_54
  have w46_58 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K46.w32 (by decide) (by decide)).trans w45_58
  have w46_5c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K46.w32 (by decide) (by decide)).trans w45_5c
  have w46_60 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K46.w32 (by decide) (by decide)).trans w45_60
  have w46_64 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K46.w32 (by decide) (by decide)).trans w45_64
  have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K46.w32 (by decide) (by decide)).trans w45_68
  have w46_6c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K46.w32 (by decide) (by decide)).trans w45_6c
  have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K46.w32 (by decide) (by decide)).trans w45_70
  have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K46.w32 (by decide) (by decide)).trans w45_74
  have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K46.w32 (by decide) (by decide)).trans w45_78
  have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K46.w32 (by decide) (by decide)).trans w45_7c
  have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K46.w32 (by decide) (by decide)).trans w45_80
  have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K46.w32 (by decide) (by decide)).trans w45_84
  have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := (K46.w32 (by decide) (by decide)).trans w45_88
  have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := (K46.w32 (by decide) (by decide)).trans w45_8c
  have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K46.w32 (by decide) (by decide)).trans w45_90
  have w46_94 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K46.w32 (by decide) (by decide)).trans w45_94
  have w46_98 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K46.w32 (by decide) (by decide)).trans w45_98
  have w46_9c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K46.w32 (by decide) (by decide)).trans w45_9c
  have w46_a0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K46.w32 (by decide) (by decide)).trans w45_a0
  have w46_a4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K46.w32 (by decide) (by decide)).trans w45_a4
  have w46_a8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K46.w32 (by decide) (by decide)).trans w45_a8
  have w46_ac : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K46.w32 (by decide) (by decide)).trans w45_ac
  have w46_b0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K46.w32 (by decide) (by decide)).trans w45_b0
  have w46_b4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K46.w32 (by decide) (by decide)).trans w45_b4
  have w46_b8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K46.w32 (by decide) (by decide)).trans w45_b8
  have w46_bc : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K46.w32 (by decide) (by decide)).trans w45_bc
  have w46_c0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := (K46.w32 (by decide) (by decide)).trans w45_c0
  have w46_c4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := (K46.w32 (by decide) (by decide)).trans w45_c4
  have w46_c8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = w50 := (K46.w32 (by decide) (by decide)).trans w45_c8
  have w46_cc : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = w4c := (K46.w32 (by decide) (by decide)).trans w45_cc
  have b46_d0 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := (K46.b8 (by decide) (by decide)).trans b45_d0
  have w46_130 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = x21 := by rw [W46, g45_21]
  have q46_d1 : ∀ j, j < 47 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K46.range (by decide) (by decide) j hj).trans (q45_d1 j hj)
  have q46_100 : ∀ j, j < 48 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K46.range (by decide) (by decide) j hj).trans (q45_100 j hj)
  have q46_420 : ∀ j, j < 47 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K46.range (by decide) (by decide) j hj).trans (q45_420 j hj)
  have q46_44f : ∀ j, j < 48 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K46.range (by decide) (by decide) j hj).trans (q45_44f j hj)
  have q46_a21 : ∀ j, j < 48 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K46.range (by decide) (by decide) j hj).trans (q45_a21 j hj)
  have q46_a51 : ∀ j, j < 48 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K46.range (by decide) (by decide) j hj).trans (q45_a51 j hj)
  clear q45_a51 q45_a21 q45_44f q45_420 q45_100 q45_d1 w45_cc b45_d0 w45_c8 w45_c4 w45_c0 w45_bc w45_b8 w45_b4 w45_b0 w45_ac w45_a8 w45_a4 w45_a0 w45_9c w45_98 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_74 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_50 w45_4c w45_48 w45_44 w45_40 w45_3c w45_38 w45_34 w45_30 w45_2c w45_28 w45_24 g45_27 g45_26 g45_25 g45_24 g45_21 g45_20 g45_19 g45_18 g45_10 g45_9 g45_4 g45_3 g45_2 V45 E45 fR45 t45 rg45 W45 K45 fr45 s45 d45
  -- 0xAD6: lw
  obtain ⟨n47, d47, u47⟩ := s46.lw E46.self sv_at_ad6 (off' := 0xAD8) (by decide)
    (by rw [g46_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s47 : St n47.mem SV n47 0xAD8 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans (.single d47)
  have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, upd_ne (by decide) (by decide), g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, upd_ne (by decide) (by decide), g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, upd_ne (by decide) (by decide), g46_4]
  have g47_9 : reg n47 (9 : Fin 32) = x9 := by rw [u47.regs, upd_ne (by decide) (by decide), g46_9]
  have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, upd_ne (by decide) (by decide), g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, upd_ne (by decide) (by decide), g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u47.regs, upd_ne (by decide) (by decide), g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = x21 := by rw [u47.regs, upd_ne (by decide) (by decide), g46_21]
  have g47_24 : reg n47 (24 : Fin 32) = trl := by rw [u47.regs, upd_ne (by decide) (by decide), g46_24]
  have g47_25 : reg n47 (25 : Fin 32) = x25 := by rw [u47.regs, upd_ne (by decide) (by decide), g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = x26 := by rw [u47.regs, upd_ne (by decide) (by decide), g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u47.regs, upd_ne (by decide) (by decide), g46_27]
  have g47_10 : reg n47 a0 = rootp := by
    rw [u47.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g46_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w46_80]
  have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4), (0xCC, 0x4), (0x130, 0x4)] := by rw [m47]; exact keep_kk46
  clear keep_kk46
  have w47_24 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m47]; exact w46_24
  have w47_28 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m47]; exact w46_28
  have w47_2c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m47]; exact w46_2c
  have w47_30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m47]; exact w46_30
  have w47_34 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m47]; exact w46_34
  have w47_38 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m47]; exact w46_38
  have w47_3c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m47]; exact w46_3c
  have w47_40 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m47]; exact w46_40
  have w47_44 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m47]; exact w46_44
  have w47_48 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m47]; exact w46_48
  have w47_4c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m47]; exact w46_4c
  have w47_50 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m47]; exact w46_50
  have w47_54 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m47]; exact w46_54
  have w47_58 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m47]; exact w46_58
  have w47_5c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m47]; exact w46_5c
  have w47_60 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m47]; exact w46_60
  have w47_64 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m47]; exact w46_64
  have w47_68 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m47]; exact w46_68
  have w47_6c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m47]; exact w46_6c
  have w47_70 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m47]; exact w46_70
  have w47_74 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m47]; exact w46_74
  have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m47]; exact w46_78
  have w47_7c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m47]; exact w46_7c
  have w47_80 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m47]; exact w46_80
  have w47_84 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m47]; exact w46_84
  have w47_88 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := by rw [m47]; exact w46_88
  have w47_8c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := by rw [m47]; exact w46_8c
  have w47_90 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m47]; exact w46_90
  have w47_94 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m47]; exact w46_94
  have w47_98 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m47]; exact w46_98
  have w47_9c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m47]; exact w46_9c
  have w47_a0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m47]; exact w46_a0
  have w47_a4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m47]; exact w46_a4
  have w47_a8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m47]; exact w46_a8
  have w47_ac : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m47]; exact w46_ac
  have w47_b0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m47]; exact w46_b0
  have w47_b4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m47]; exact w46_b4
  have w47_b8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [m47]; exact w46_b8
  have w47_bc : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := by rw [m47]; exact w46_bc
  have w47_c0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := by rw [m47]; exact w46_c0
  have w47_c4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := by rw [m47]; exact w46_c4
  have w47_c8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = w50 := by rw [m47]; exact w46_c8
  have w47_cc : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = w4c := by rw [m47]; exact w46_cc
  have w47_130 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = x21 := by rw [m47]; exact w46_130
  have b47_d0 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m47]; exact b46_d0
  have q47_d1 : ∀ j, j < 47 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m47]; exact q46_d1 j hj
  have q47_100 : ∀ j, j < 48 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m47]; exact q46_100 j hj
  have q47_420 : ∀ j, j < 47 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m47]; exact q46_420 j hj
  have q47_44f : ∀ j, j < 48 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m47]; exact q46_44f j hj
  have q47_a21 : ∀ j, j < 48 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m47]; exact q46_a21 j hj
  have q47_a51 : ∀ j, j < 48 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m47]; exact q46_a51 j hj
  clear q46_a51 q46_a21 q46_44f q46_420 q46_100 q46_d1 w46_130 b46_d0 w46_cc w46_c8 w46_c4 w46_c0 w46_bc w46_b8 w46_b4 w46_b0 w46_ac w46_a8 w46_a4 w46_a0 w46_9c w46_98 w46_94 w46_90 w46_8c w46_88 w46_84 w46_80 w46_7c w46_78 w46_74 w46_70 w46_6c w46_68 w46_64 w46_60 w46_5c w46_58 w46_54 w46_50 w46_4c w46_48 w46_44 w46_40 w46_3c w46_38 w46_34 w46_30 w46_2c w46_28 w46_24 g46_27 g46_26 g46_25 g46_24 g46_21 g46_20 g46_19 g46_18 g46_10 g46_9 g46_4 g46_3 g46_2 V46 E46 fR46 t46 rg46 W46 K46 fr46 s46 d46
  -- 0xAD8
  obtain ⟨n48, c48, u48⟩ := s47.block svL8aad8 E47.self svL8aad8_end
    ⟨trivial, trivial⟩
  have m48 : n48.mem = n47.mem := u48.mem
  have s48 : St n48.mem SV n48 0xADC (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
  have rb48 : ∀ q, reg n48 q = (runBlock svL8aad8 (n47.mem, reg n47)).2 q := fun q => by rw [u48.regs]
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
  have g48_9 : reg n48 (9 : Fin 32) = x9 := by
    rw [rb48, runBlock_reg _ _ _ (9 : Fin 32) s47.zero (by decide), g47_9]
  have g48_18 : reg n48 (18 : Fin 32) = out := by
    rw [rb48, runBlock_reg _ _ _ (18 : Fin 32) s47.zero (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by
    rw [rb48, runBlock_reg _ _ _ (19 : Fin 32) s47.zero (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb48, runBlock_reg _ _ _ (20 : Fin 32) s47.zero (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = x21 := by
    rw [rb48, runBlock_reg _ _ _ (21 : Fin 32) s47.zero (by decide), g47_21]
  have g48_24 : reg n48 (24 : Fin 32) = trl := by
    rw [rb48, runBlock_reg _ _ _ (24 : Fin 32) s47.zero (by decide), g47_24]
  have g48_25 : reg n48 (25 : Fin 32) = x25 := by
    rw [rb48, runBlock_reg _ _ _ (25 : Fin 32) s47.zero (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = x26 := by
    rw [rb48, runBlock_reg _ _ _ (26 : Fin 32) s47.zero (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb48, runBlock_reg _ _ _ (27 : Fin 32) s47.zero (by decide), g47_27]
  have g48_10 : reg n48 a0 = (rootp) + BitVec.ofNat 32 0x3C := by
    rw [rb48, ← g47_10]; rfl
  have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4), (0xCC, 0x4), (0x130, 0x4)] := by rw [m48]; exact keep_kk47
  clear keep_kk47
  have w48_24 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m48]; exact w47_24
  have w48_28 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m48]; exact w47_28
  have w48_2c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m48]; exact w47_2c
  have w48_30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m48]; exact w47_30
  have w48_34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m48]; exact w47_34
  have w48_38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m48]; exact w47_38
  have w48_3c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m48]; exact w47_3c
  have w48_40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m48]; exact w47_40
  have w48_44 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m48]; exact w47_44
  have w48_48 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m48]; exact w47_48
  have w48_4c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m48]; exact w47_4c
  have w48_50 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m48]; exact w47_50
  have w48_54 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m48]; exact w47_54
  have w48_58 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m48]; exact w47_58
  have w48_5c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m48]; exact w47_5c
  have w48_60 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m48]; exact w47_60
  have w48_64 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m48]; exact w47_64
  have w48_68 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m48]; exact w47_68
  have w48_6c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m48]; exact w47_6c
  have w48_70 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m48]; exact w47_70
  have w48_74 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m48]; exact w47_74
  have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m48]; exact w47_78
  have w48_7c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m48]; exact w47_7c
  have w48_80 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m48]; exact w47_80
  have w48_84 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m48]; exact w47_84
  have w48_88 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := by rw [m48]; exact w47_88
  have w48_8c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := by rw [m48]; exact w47_8c
  have w48_90 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m48]; exact w47_90
  have w48_94 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m48]; exact w47_94
  have w48_98 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m48]; exact w47_98
  have w48_9c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m48]; exact w47_9c
  have w48_a0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m48]; exact w47_a0
  have w48_a4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m48]; exact w47_a4
  have w48_a8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m48]; exact w47_a8
  have w48_ac : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m48]; exact w47_ac
  have w48_b0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m48]; exact w47_b0
  have w48_b4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m48]; exact w47_b4
  have w48_b8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [m48]; exact w47_b8
  have w48_bc : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := by rw [m48]; exact w47_bc
  have w48_c0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := by rw [m48]; exact w47_c0
  have w48_c4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := by rw [m48]; exact w47_c4
  have w48_c8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = w50 := by rw [m48]; exact w47_c8
  have w48_cc : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = w4c := by rw [m48]; exact w47_cc
  have w48_130 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = x21 := by rw [m48]; exact w47_130
  have b48_d0 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m48]; exact b47_d0
  have q48_d1 : ∀ j, j < 47 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m48]; exact q47_d1 j hj
  have q48_100 : ∀ j, j < 48 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m48]; exact q47_100 j hj
  have q48_420 : ∀ j, j < 47 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m48]; exact q47_420 j hj
  have q48_44f : ∀ j, j < 48 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m48]; exact q47_44f j hj
  have q48_a21 : ∀ j, j < 48 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m48]; exact q47_a21 j hj
  have q48_a51 : ∀ j, j < 48 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m48]; exact q47_a51 j hj
  clear q47_a51 q47_a21 q47_44f q47_420 q47_100 q47_d1 b47_d0 w47_130 w47_cc w47_c8 w47_c4 w47_c0 w47_bc w47_b8 w47_b4 w47_b0 w47_ac w47_a8 w47_a4 w47_a0 w47_9c w47_98 w47_94 w47_90 w47_8c w47_88 w47_84 w47_80 w47_7c w47_78 w47_74 w47_70 w47_6c w47_68 w47_64 w47_60 w47_5c w47_58 w47_54 w47_50 w47_4c w47_48 w47_44 w47_40 w47_3c w47_38 w47_34 w47_30 w47_2c w47_28 w47_24 g47_10 g47_27 g47_26 g47_25 g47_24 g47_21 g47_20 g47_19 g47_18 g47_9 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
  -- 0xADC: sw
  obtain ⟨n49, d49, s49, fr49, K49, W49, rg49⟩ := sv_sw F E48 s48 sv_at_adc (off' := 0xADE) (c := 0x7C)
    (by decide) (by rw [g48_2]; sv_addr) (by decide) (by decide)
  have t49 : Steps n0 n49 := t48.trans d49
  have fR49 : ∀ x, SvR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.keep K49 (by decide)
  have g49_2 : reg n49 sp = B + 0x21A0 := by rw [rg49 sp, g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg49 (3 : Fin 32), g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg49 (4 : Fin 32), g48_4]
  have g49_9 : reg n49 (9 : Fin 32) = x9 := by rw [rg49 (9 : Fin 32), g48_9]
  have g49_10 : reg n49 a0 = (rootp) + BitVec.ofNat 32 0x3C := by rw [rg49 a0, g48_10]
  have g49_18 : reg n49 (18 : Fin 32) = out := by rw [rg49 (18 : Fin 32), g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [rg49 (19 : Fin 32), g48_19]
  have g49_20 : reg n49 (20 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rg49 (20 : Fin 32), g48_20]
  have g49_21 : reg n49 (21 : Fin 32) = x21 := by rw [rg49 (21 : Fin 32), g48_21]
  have g49_24 : reg n49 (24 : Fin 32) = trl := by rw [rg49 (24 : Fin 32), g48_24]
  have g49_25 : reg n49 (25 : Fin 32) = x25 := by rw [rg49 (25 : Fin 32), g48_25]
  have g49_26 : reg n49 (26 : Fin 32) = x26 := by rw [rg49 (26 : Fin 32), g48_26]
  have g49_27 : reg n49 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg49 (27 : Fin 32), g48_27]
  have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4), (0xCC, 0x4), (0x130, 0x4), (0x7C, 0x4)] := keep_kk48.trans K49.toL
  clear keep_kk48
  have w49_24 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K49.w32 (by decide) (by decide)).trans w48_24
  have w49_28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K49.w32 (by decide) (by decide)).trans w48_28
  have w49_2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K49.w32 (by decide) (by decide)).trans w48_2c
  have w49_30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K49.w32 (by decide) (by decide)).trans w48_30
  have w49_34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K49.w32 (by decide) (by decide)).trans w48_34
  have w49_38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K49.w32 (by decide) (by decide)).trans w48_38
  have w49_3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K49.w32 (by decide) (by decide)).trans w48_3c
  have w49_40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K49.w32 (by decide) (by decide)).trans w48_40
  have w49_44 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K49.w32 (by decide) (by decide)).trans w48_44
  have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K49.w32 (by decide) (by decide)).trans w48_48
  have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K49.w32 (by decide) (by decide)).trans w48_4c
  have w49_50 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K49.w32 (by decide) (by decide)).trans w48_50
  have w49_54 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K49.w32 (by decide) (by decide)).trans w48_54
  have w49_58 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K49.w32 (by decide) (by decide)).trans w48_58
  have w49_5c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K49.w32 (by decide) (by decide)).trans w48_5c
  have w49_60 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K49.w32 (by decide) (by decide)).trans w48_60
  have w49_64 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K49.w32 (by decide) (by decide)).trans w48_64
  have w49_68 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K49.w32 (by decide) (by decide)).trans w48_68
  have w49_6c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K49.w32 (by decide) (by decide)).trans w48_6c
  have w49_70 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K49.w32 (by decide) (by decide)).trans w48_70
  have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K49.w32 (by decide) (by decide)).trans w48_74
  have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K49.w32 (by decide) (by decide)).trans w48_78
  have w49_80 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K49.w32 (by decide) (by decide)).trans w48_80
  have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K49.w32 (by decide) (by decide)).trans w48_84
  have w49_88 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := (K49.w32 (by decide) (by decide)).trans w48_88
  have w49_8c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := (K49.w32 (by decide) (by decide)).trans w48_8c
  have w49_90 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := (K49.w32 (by decide) (by decide)).trans w48_90
  have w49_94 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := (K49.w32 (by decide) (by decide)).trans w48_94
  have w49_98 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := (K49.w32 (by decide) (by decide)).trans w48_98
  have w49_9c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := (K49.w32 (by decide) (by decide)).trans w48_9c
  have w49_a0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := (K49.w32 (by decide) (by decide)).trans w48_a0
  have w49_a4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := (K49.w32 (by decide) (by decide)).trans w48_a4
  have w49_a8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := (K49.w32 (by decide) (by decide)).trans w48_a8
  have w49_ac : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := (K49.w32 (by decide) (by decide)).trans w48_ac
  have w49_b0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := (K49.w32 (by decide) (by decide)).trans w48_b0
  have w49_b4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := (K49.w32 (by decide) (by decide)).trans w48_b4
  have w49_b8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := (K49.w32 (by decide) (by decide)).trans w48_b8
  have w49_bc : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := (K49.w32 (by decide) (by decide)).trans w48_bc
  have w49_c0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := (K49.w32 (by decide) (by decide)).trans w48_c0
  have w49_c4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := (K49.w32 (by decide) (by decide)).trans w48_c4
  have w49_c8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = w50 := (K49.w32 (by decide) (by decide)).trans w48_c8
  have w49_cc : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = w4c := (K49.w32 (by decide) (by decide)).trans w48_cc
  have w49_130 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = x21 := (K49.w32 (by decide) (by decide)).trans w48_130
  have b49_d0 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := (K49.b8 (by decide) (by decide)).trans b48_d0
  have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (rootp) + BitVec.ofNat 32 0x3C := by rw [W49, g48_10]
  have q49_d1 : ∀ j, j < 47 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_d1 j hj)
  have q49_100 : ∀ j, j < 48 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_100 j hj)
  have q49_420 : ∀ j, j < 47 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_420 j hj)
  have q49_44f : ∀ j, j < 48 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_44f j hj)
  have q49_a21 : ∀ j, j < 48 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_a21 j hj)
  have q49_a51 : ∀ j, j < 48 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_a51 j hj)
  clear q48_a51 q48_a21 q48_44f q48_420 q48_100 q48_d1 b48_d0 w48_130 w48_cc w48_c8 w48_c4 w48_c0 w48_bc w48_b8 w48_b4 w48_b0 w48_ac w48_a8 w48_a4 w48_a0 w48_9c w48_98 w48_94 w48_90 w48_8c w48_88 w48_84 w48_80 w48_7c w48_78 w48_74 w48_70 w48_6c w48_68 w48_64 w48_60 w48_5c w48_58 w48_54 w48_50 w48_4c w48_48 w48_44 w48_40 w48_3c w48_38 w48_34 w48_30 w48_2c w48_28 w48_24 g48_10 g48_27 g48_26 g48_25 g48_24 g48_21 g48_20 g48_19 g48_18 g48_9 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 rb48 s48 m48 u48 c48
  -- 0xADE
  obtain ⟨n50, c50, u50⟩ := s49.block svL8aade E49.self svL8aade_end
    ⟨trivial, trivial⟩
  have m50 : n50.mem = n49.mem := u50.mem
  have s50 : St n50.mem SV n50 0xAE2 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
  have rb50 : ∀ q, reg n50 q = (runBlock svL8aade (n49.mem, reg n49)).2 q := fun q => by rw [u50.regs]
  have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
  have t50 : Steps n0 n50 := t49.trans c50
  have fR50 : ∀ x, SvR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : SvCode n50.mem := E49.fr F fr50
  have V50 : SvSaves B n50.mem v := V49.same m50
  have g50_2 : reg n50 sp = B + 0x21A0 := by
    rw [rb50, runBlock_reg _ _ _ sp s49.zero (by decide), g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb50, runBlock_reg _ _ _ (3 : Fin 32) s49.zero (by decide), g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb50, runBlock_reg _ _ _ (4 : Fin 32) s49.zero (by decide), g49_4]
  have g50_9 : reg n50 (9 : Fin 32) = x9 := by
    rw [rb50, runBlock_reg _ _ _ (9 : Fin 32) s49.zero (by decide), g49_9]
  have g50_10 : reg n50 a0 = (rootp) + BitVec.ofNat 32 0x3C := by
    rw [rb50, runBlock_reg _ _ _ a0 s49.zero (by decide), g49_10]
  have g50_18 : reg n50 (18 : Fin 32) = out := by
    rw [rb50, runBlock_reg _ _ _ (18 : Fin 32) s49.zero (by decide), g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = bp := by
    rw [rb50, runBlock_reg _ _ _ (19 : Fin 32) s49.zero (by decide), g49_19]
  have g50_21 : reg n50 (21 : Fin 32) = x21 := by
    rw [rb50, runBlock_reg _ _ _ (21 : Fin 32) s49.zero (by decide), g49_21]
  have g50_24 : reg n50 (24 : Fin 32) = trl := by
    rw [rb50, runBlock_reg _ _ _ (24 : Fin 32) s49.zero (by decide), g49_24]
  have g50_25 : reg n50 (25 : Fin 32) = x25 := by
    rw [rb50, runBlock_reg _ _ _ (25 : Fin 32) s49.zero (by decide), g49_25]
  have g50_26 : reg n50 (26 : Fin 32) = x26 := by
    rw [rb50, runBlock_reg _ _ _ (26 : Fin 32) s49.zero (by decide), g49_26]
  have g50_27 : reg n50 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb50, runBlock_reg _ _ _ (27 : Fin 32) s49.zero (by decide), g49_27]
  have g50_20 : reg n50 (20 : Fin 32) = BitVec.ofNat 32 0x80 := by
    rw [rb50]; simp +decide only [runBlock, BInstr.run, svL8aade, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g49_2, g49_3, g49_4, g49_9, g49_10, g49_18, g49_19, g49_20, g49_21, g49_24, g49_25, g49_26, g49_27, s49.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk50 : SvKeepL B n0.mem n50.mem [(0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x88, 0x4), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4), (0xCC, 0x4), (0x130, 0x4), (0x7C, 0x4)] := by rw [m50]; exact keep_kk49
  clear keep_kk49
  have w50_24 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m50]; exact w49_24
  have w50_28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m50]; exact w49_28
  have w50_2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m50]; exact w49_2c
  have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m50]; exact w49_30
  have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m50]; exact w49_34
  have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m50]; exact w49_38
  have w50_3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m50]; exact w49_3c
  have w50_40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m50]; exact w49_40
  have w50_44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m50]; exact w49_44
  have w50_48 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m50]; exact w49_48
  have w50_4c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m50]; exact w49_4c
  have w50_50 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m50]; exact w49_50
  have w50_54 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m50]; exact w49_54
  have w50_58 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m50]; exact w49_58
  have w50_5c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m50]; exact w49_5c
  have w50_60 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m50]; exact w49_60
  have w50_64 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m50]; exact w49_64
  have w50_68 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m50]; exact w49_68
  have w50_6c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m50]; exact w49_6c
  have w50_70 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m50]; exact w49_70
  have w50_74 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m50]; exact w49_74
  have w50_78 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m50]; exact w49_78
  have w50_7c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (rootp) + BitVec.ofNat 32 0x3C := by rw [m50]; exact w49_7c
  have w50_80 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m50]; exact w49_80
  have w50_84 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m50]; exact w49_84
  have w50_88 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = x9 := by rw [m50]; exact w49_88
  have w50_8c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = trl := by rw [m50]; exact w49_8c
  have w50_90 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w5c := by rw [m50]; exact w49_90
  have w50_94 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = x25 := by rw [m50]; exact w49_94
  have w50_98 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w48 := by rw [m50]; exact w49_98
  have w50_9c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w34 := by rw [m50]; exact w49_9c
  have w50_a0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = w44 := by rw [m50]; exact w49_a0
  have w50_a4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = w30 := by rw [m50]; exact w49_a4
  have w50_a8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = w40 := by rw [m50]; exact w49_a8
  have w50_ac : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = w2c := by rw [m50]; exact w49_ac
  have w50_b0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = w3c := by rw [m50]; exact w49_b0
  have w50_b4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = w28 := by rw [m50]; exact w49_b4
  have w50_b8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = w38 := by rw [m50]; exact w49_b8
  have w50_bc : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = w24 := by rw [m50]; exact w49_bc
  have w50_c0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = w58 := by rw [m50]; exact w49_c0
  have w50_c4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = w54 := by rw [m50]; exact w49_c4
  have w50_c8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = w50 := by rw [m50]; exact w49_c8
  have w50_cc : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = w4c := by rw [m50]; exact w49_cc
  have w50_130 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = x21 := by rw [m50]; exact w49_130
  have b50_d0 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0) := by rw [m50]; exact b49_d0
  have q50_d1 : ∀ j, j < 47 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m50]; exact q49_d1 j hj
  have q50_100 : ∀ j, j < 48 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m50]; exact q49_100 j hj
  have q50_420 : ∀ j, j < 47 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m50]; exact q49_420 j hj
  have q50_44f : ∀ j, j < 48 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0x44F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m50]; exact q49_44f j hj
  have q50_a21 : ∀ j, j < 48 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0) := fun j hj => by rw [m50]; exact q49_a21 j hj
  have q50_a51 : ∀ j, j < 48 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m50]; exact q49_a51 j hj
  clear q49_a51 q49_a21 q49_44f q49_420 q49_100 q49_d1 w49_7c b49_d0 w49_130 w49_cc w49_c8 w49_c4 w49_c0 w49_bc w49_b8 w49_b4 w49_b0 w49_ac w49_a8 w49_a4 w49_a0 w49_9c w49_98 w49_94 w49_90 w49_8c w49_88 w49_84 w49_80 w49_78 w49_74 w49_70 w49_6c w49_68 w49_64 w49_60 w49_5c w49_58 w49_54 w49_50 w49_4c w49_48 w49_44 w49_40 w49_3c w49_38 w49_34 w49_30 w49_2c w49_28 w49_24 g49_27 g49_26 g49_25 g49_24 g49_21 g49_20 g49_19 g49_18 g49_10 g49_9 g49_4 g49_3 g49_2 V49 E49 fR49 t49 rg49 W49 K49 fr49 s49 d49
  exact .inr ⟨n50, t50, s50, E50, V50, fR50, g50_2, g50_3, g50_4, g50_9, g50_18, g50_19, g50_20, g50_21, g50_24, g50_25, g50_26, g50_27, w50_24, w50_28, w50_2c, w50_30, w50_34, w50_38, w50_3c, w50_40, w50_44, w50_48, w50_4c, w50_50, w50_54, w50_58, w50_5c, w50_60, w50_64, w50_68, w50_6c, w50_70, w50_74, w50_78, w50_7c, w50_80, w50_84, w50_88, w50_8c, w50_90, w50_94, w50_98, w50_9c, w50_a0, w50_a4, w50_a8, w50_ac, w50_b0, w50_b4, w50_b8, w50_bc, w50_c0, w50_c4, w50_c8, w50_cc, w50_130, b50_d0, q50_d1, q50_100, q50_420, q50_44f, q50_a21, q50_a51, keep_kk50.mono (by decide)⟩

end C3.RV32.Sv
