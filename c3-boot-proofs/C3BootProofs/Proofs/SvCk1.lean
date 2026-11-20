import C3BootProofs.Proofs.SvCkpt

/-!
# `sigstore::verify`: the checkpoint's lines

From 0x2B34 to 0x2BCA: the TSA's signature checked, and the checkpoint splits into an origin line, a size line, a root line, a blank line, and a nonempty rest.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCk12c5e : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x10]
theorem svCk12c5e_end : blockEnd sigstoreVerifyCode 0x2C5E svCk12c5e = some 0x2C60 := by
  simp only [svCk12c5e]
  rw [blockEnd, sv_at_2c5e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk12b40 : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svCk12b40_end : blockEnd sigstoreVerifyCode 0x2B40 svCk12b40 = some 0x2B44 := by
  simp only [svCk12b40]
  rw [blockEnd, sv_at_2b40]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk12b46 : List BInstr :=
  [.alu .add a2 x0 (25 : Fin 32)]
theorem svCk12b46_end : blockEnd sigstoreVerifyCode 0x2B46 svCk12b46 = some 0x2B48 := by
  simp only [svCk12b46]
  rw [blockEnd, sv_at_2b46]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk12b5a : List BInstr :=
  [.aluImm .add a3 sp 0x400]
theorem svCk12b5a_end : blockEnd sigstoreVerifyCode 0x2B5A svCk12b5a = some 0x2B5E := by
  simp only [svCk12b5a]
  rw [blockEnd, sv_at_2b5a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk12b66 : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svCk12b66_end : blockEnd sigstoreVerifyCode 0x2B66 svCk12b66 = some 0x2B6A := by
  simp only [svCk12b66]
  rw [blockEnd, sv_at_2b66]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk12b7a : List BInstr :=
  [.aluImm .add a0 sp 0x400]
theorem svCk12b7a_end : blockEnd sigstoreVerifyCode 0x2B7A svCk12b7a = some 0x2B7E := by
  simp only [svCk12b7a]
  rw [blockEnd, sv_at_2b7a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk12b84 : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svCk12b84_end : blockEnd sigstoreVerifyCode 0x2B84 svCk12b84 = some 0x2B88 := by
  simp only [svCk12b84]
  rw [blockEnd, sv_at_2b84]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk12b98 : List BInstr :=
  [.aluImm .add a0 sp 0x400]
theorem svCk12b98_end : blockEnd sigstoreVerifyCode 0x2B98 svCk12b98 = some 0x2B9C := by
  simp only [svCk12b98]
  rw [blockEnd, sv_at_2b98]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk12ba4 : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svCk12ba4_end : blockEnd sigstoreVerifyCode 0x2BA4 svCk12ba4 = some 0x2BA8 := by
  simp only [svCk12ba4]
  rw [blockEnd, sv_at_2ba4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCk12ff2 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x1A]
theorem svCk12ff2_end : blockEnd sigstoreVerifyCode 0x2FF2 svCk12ff2 = some 0x2FF4 := by
  simp only [svCk12ff2]
  rw [blockEnd, sv_at_2ff2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_ck1 {B out bp x21 x26 dg dp pv q ckp ckl : Word} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x2B34 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = pv)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = dp)
    (g0_23 : reg n0 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
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
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94)
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98)
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c)
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0)
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4)
    (w0_a8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8)
    (w0_ac : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac)
    (w0_b0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0)
    (w0_b4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4)
    (w0_b8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8)
    (w0_bc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc)
    (w0_c0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0)
    (w0_c4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4)
    (w0_c8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8)
    (w0_cc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc)
    (w0_d0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0)
    (w0_d4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4)
    (w0_d8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8)
    (w0_dc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc)
    (w0_e0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0)
    (w0_e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4)
    (w0_e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8)
    (w0_ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec)
    (w0_f0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0)
    (w0_f4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4)
    (w0_f8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8)
    (w0_fc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc)
    (w0_100 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100)
    (w0_104 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104)
    (w0_108 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108)
    (w0_10c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c)
    (w0_110 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110)
    (w0_114 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114)
    (w0_118 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118)
    (w0_11c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c)
    (w0_120 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120)
    (w0_124 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124)
    (w0_128 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128)
    (w0_12c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c)
    (w0_130 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130)
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78)
    (w0_aa0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp)
    (w0_aa4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg)
    (CK0 : SvCkCode M0)
    (hckp : memLoad32 M0 (bp + 0x18) = ckp)
    (hckl : memLoad32 M0 (bp + 0x1C) = ckl)
    (ckp_in4 : SvIn B (bp + 0x18) 4)
    (ckl_in4 : SvIn B (bp + 0x1C) 4)
    (a_ckp : (bp + 0x18).toNat % 4 = 0)
    (a_ckl : (bp + 0x1C).toNat % 4 = 0)
    (ck_in : SvIn B ckp ckl.toNat) :
    (¬ ((pv ≠ 0) ∧ ∃ ix7, nlScan M0 (ckp) 0 ((ckl).toNat) = some ix7 ∧ ∃ ix17, nlScan M0 ((ckp) + BitVec.ofNat 32 (ix7 + 1)) 0 (((ckl).toNat) - (ix7 + 1)) = some ix17 ∧ ∃ ix25, nlScan M0 (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) 0 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) = some ix25 ∧ ∃ ix33, nlScan M0 ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) 0 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) = some ix33 ∧ (BitVec.ofNat 32 ix33 = 0) ∧ (BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) ≠ 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((pv ≠ 0) ∧
    ∃ ix7, nlScan M0 (ckp) 0 ((ckl).toNat) = some ix7 ∧
    ∃ ix17, nlScan M0 ((ckp) + BitVec.ofNat 32 (ix7 + 1)) 0 (((ckl).toNat) - (ix7 + 1)) = some ix17 ∧
    ∃ ix25, nlScan M0 (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) 0 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) = some ix25 ∧
    ∃ ix33, nlScan M0 ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) 0 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) = some ix33 ∧
    (BitVec.ofNat 32 ix33 = 0) ∧
    (BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) ≠ 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x2BCA (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 ix17 ∧
        reg n' (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = BitVec.ofNat 32 ix25 ∧
        reg n' (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) ∧
        reg n' (24 : Fin 32) = dg ∧
        reg n' (25 : Fin 32) = ckl ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  by_cases hv : pv ≠ 0
  rotate_left
  · -- 0x2B34: branch, taken
    obtain ⟨n1, d1, u1⟩ := s0.taken E0.self 0x2C5E sv_at_2b34
      (by decide) (by rw [g0_10, s0.zero]; exact br_beq_t (Decidable.of_not_not hv))
    have s1 : St n1.mem SV n1 0x2C5E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
    have m1 : n1.mem = n0.mem := u1.mem
    have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
    have t1 : Steps n0 n1 := t0.trans (.single d1)
    have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
    have E1 : SvCode n1.mem := E0.fr F fr1
    have V1 : SvSaves B n1.mem v := V0.same m1
    have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
    have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
    have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
    have g1_10 : reg n1 a0 = pv := by rw [u1.regs, g0_10]
    have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
    have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
    have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, g0_21]
    have g1_22 : reg n1 (22 : Fin 32) = dp := by rw [u1.regs, g0_22]
    have g1_23 : reg n1 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u1.regs, g0_23]
    have g1_24 : reg n1 (24 : Fin 32) = dg := by rw [u1.regs, g0_24]
    have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, g0_26]
    have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u1.regs, g0_27]
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
    have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m1]; exact w0_74
    have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m1]; exact w0_78
    have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m1]; exact w0_7c
    have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m1]; exact w0_80
    have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m1]; exact w0_84
    have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m1]; exact w0_88
    have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m1]; exact w0_8c
    have w1_90 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m1]; exact w0_90
    have w1_94 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m1]; exact w0_94
    have w1_98 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m1]; exact w0_98
    have w1_9c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m1]; exact w0_9c
    have w1_a0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m1]; exact w0_a0
    have w1_a4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m1]; exact w0_a4
    have w1_a8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m1]; exact w0_a8
    have w1_ac : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m1]; exact w0_ac
    have w1_b0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m1]; exact w0_b0
    have w1_b4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m1]; exact w0_b4
    have w1_b8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m1]; exact w0_b8
    have w1_bc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m1]; exact w0_bc
    have w1_c0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m1]; exact w0_c0
    have w1_c4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m1]; exact w0_c4
    have w1_c8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m1]; exact w0_c8
    have w1_cc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m1]; exact w0_cc
    have w1_d0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m1]; exact w0_d0
    have w1_d4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m1]; exact w0_d4
    have w1_d8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m1]; exact w0_d8
    have w1_dc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m1]; exact w0_dc
    have w1_e0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m1]; exact w0_e0
    have w1_e4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m1]; exact w0_e4
    have w1_e8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m1]; exact w0_e8
    have w1_ec : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m1]; exact w0_ec
    have w1_f0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m1]; exact w0_f0
    have w1_f4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m1]; exact w0_f4
    have w1_f8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m1]; exact w0_f8
    have w1_fc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m1]; exact w0_fc
    have w1_100 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m1]; exact w0_100
    have w1_104 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m1]; exact w0_104
    have w1_108 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m1]; exact w0_108
    have w1_10c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m1]; exact w0_10c
    have w1_110 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m1]; exact w0_110
    have w1_114 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m1]; exact w0_114
    have w1_118 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m1]; exact w0_118
    have w1_11c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m1]; exact w0_11c
    have w1_120 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m1]; exact w0_120
    have w1_124 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m1]; exact w0_124
    have w1_128 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m1]; exact w0_128
    have w1_12c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m1]; exact w0_12c
    have w1_130 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m1]; exact w0_130
    have w1_a20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m1]; exact w0_a20
    have w1_a24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m1]; exact w0_a24
    have w1_a28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m1]; exact w0_a28
    have w1_a2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m1]; exact w0_a2c
    have w1_a30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m1]; exact w0_a30
    have w1_a34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m1]; exact w0_a34
    have w1_a38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m1]; exact w0_a38
    have w1_a3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m1]; exact w0_a3c
    have w1_aa0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m1]; exact w0_aa0
    have w1_aa4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m1]; exact w0_aa4
    -- 0x2C5E
    obtain ⟨n2, c2, u2⟩ := s1.block svCk12c5e E1.self svCk12c5e_end
      ⟨trivial, trivial⟩
    have m2 : n2.mem = n1.mem := u2.mem
    have s2 : St n2.mem SV n2 0x2C60 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
    have rb2 : ∀ q, reg n2 q = (runBlock svCk12c5e (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
    have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
    have t2 : Steps n0 n2 := t1.trans c2
    have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
    have E2 : SvCode n2.mem := E1.fr F fr2
    have V2 : SvSaves B n2.mem v := V1.same m2
    have g2_2 : reg n2 sp = B + 0x21A0 := by
      rw [rb2, runBlock_reg _ _ _ sp s1.zero (by decide), g1_2]
    have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb2, runBlock_reg _ _ _ (3 : Fin 32) s1.zero (by decide), g1_3]
    have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb2, runBlock_reg _ _ _ (4 : Fin 32) s1.zero (by decide), g1_4]
    have g2_10 : reg n2 a0 = pv := by
      rw [rb2, runBlock_reg _ _ _ a0 s1.zero (by decide), g1_10]
    have g2_18 : reg n2 (18 : Fin 32) = out := by
      rw [rb2, runBlock_reg _ _ _ (18 : Fin 32) s1.zero (by decide), g1_18]
    have g2_19 : reg n2 (19 : Fin 32) = bp := by
      rw [rb2, runBlock_reg _ _ _ (19 : Fin 32) s1.zero (by decide), g1_19]
    have g2_21 : reg n2 (21 : Fin 32) = x21 := by
      rw [rb2, runBlock_reg _ _ _ (21 : Fin 32) s1.zero (by decide), g1_21]
    have g2_22 : reg n2 (22 : Fin 32) = dp := by
      rw [rb2, runBlock_reg _ _ _ (22 : Fin 32) s1.zero (by decide), g1_22]
    have g2_23 : reg n2 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
      rw [rb2, runBlock_reg _ _ _ (23 : Fin 32) s1.zero (by decide), g1_23]
    have g2_24 : reg n2 (24 : Fin 32) = dg := by
      rw [rb2, runBlock_reg _ _ _ (24 : Fin 32) s1.zero (by decide), g1_24]
    have g2_26 : reg n2 (26 : Fin 32) = x26 := by
      rw [rb2, runBlock_reg _ _ _ (26 : Fin 32) s1.zero (by decide), g1_26]
    have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb2, runBlock_reg _ _ _ (27 : Fin 32) s1.zero (by decide), g1_27]
    have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x10 := by
      rw [rb2]; simp +decide only [runBlock, BInstr.run, svCk12c5e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g1_2, g1_3, g1_4, g1_10, g1_18, g1_19, g1_21, g1_22, g1_23, g1_24, g1_26, g1_27, s1.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w2_24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m2]; exact w1_24
    have w2_28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m2]; exact w1_28
    have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m2]; exact w1_2c
    have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m2]; exact w1_30
    have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m2]; exact w1_34
    have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m2]; exact w1_38
    have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m2]; exact w1_3c
    have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m2]; exact w1_40
    have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m2]; exact w1_44
    have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m2]; exact w1_48
    have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m2]; exact w1_4c
    have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
    have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m2]; exact w1_54
    have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m2]; exact w1_58
    have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m2]; exact w1_5c
    have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m2]; exact w1_60
    have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
    have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m2]; exact w1_68
    have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m2]; exact w1_6c
    have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m2]; exact w1_70
    have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m2]; exact w1_74
    have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m2]; exact w1_78
    have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m2]; exact w1_7c
    have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m2]; exact w1_80
    have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m2]; exact w1_84
    have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m2]; exact w1_88
    have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m2]; exact w1_8c
    have w2_90 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m2]; exact w1_90
    have w2_94 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m2]; exact w1_94
    have w2_98 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m2]; exact w1_98
    have w2_9c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m2]; exact w1_9c
    have w2_a0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m2]; exact w1_a0
    have w2_a4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m2]; exact w1_a4
    have w2_a8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m2]; exact w1_a8
    have w2_ac : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m2]; exact w1_ac
    have w2_b0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m2]; exact w1_b0
    have w2_b4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m2]; exact w1_b4
    have w2_b8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m2]; exact w1_b8
    have w2_bc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m2]; exact w1_bc
    have w2_c0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m2]; exact w1_c0
    have w2_c4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m2]; exact w1_c4
    have w2_c8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m2]; exact w1_c8
    have w2_cc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m2]; exact w1_cc
    have w2_d0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m2]; exact w1_d0
    have w2_d4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m2]; exact w1_d4
    have w2_d8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m2]; exact w1_d8
    have w2_dc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m2]; exact w1_dc
    have w2_e0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m2]; exact w1_e0
    have w2_e4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m2]; exact w1_e4
    have w2_e8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m2]; exact w1_e8
    have w2_ec : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m2]; exact w1_ec
    have w2_f0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m2]; exact w1_f0
    have w2_f4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m2]; exact w1_f4
    have w2_f8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m2]; exact w1_f8
    have w2_fc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m2]; exact w1_fc
    have w2_100 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m2]; exact w1_100
    have w2_104 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m2]; exact w1_104
    have w2_108 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m2]; exact w1_108
    have w2_10c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m2]; exact w1_10c
    have w2_110 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m2]; exact w1_110
    have w2_114 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m2]; exact w1_114
    have w2_118 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m2]; exact w1_118
    have w2_11c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m2]; exact w1_11c
    have w2_120 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m2]; exact w1_120
    have w2_124 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m2]; exact w1_124
    have w2_128 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m2]; exact w1_128
    have w2_12c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m2]; exact w1_12c
    have w2_130 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m2]; exact w1_130
    have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m2]; exact w1_a20
    have w2_a24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m2]; exact w1_a24
    have w2_a28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m2]; exact w1_a28
    have w2_a2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m2]; exact w1_a2c
    have w2_a30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m2]; exact w1_a30
    have w2_a34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m2]; exact w1_a34
    have w2_a38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m2]; exact w1_a38
    have w2_a3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m2]; exact w1_a3c
    have w2_aa0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m2]; exact w1_aa0
    have w2_aa4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m2]; exact w1_aa4
    clear w1_aa4 w1_aa0 w1_a3c w1_a38 w1_a34 w1_a30 w1_a2c w1_a28 w1_a24 w1_a20 w1_130 w1_12c w1_128 w1_124 w1_120 w1_11c w1_118 w1_114 w1_110 w1_10c w1_108 w1_104 w1_100 w1_fc w1_f8 w1_f4 w1_f0 w1_ec w1_e8 w1_e4 w1_e0 w1_dc w1_d8 w1_d4 w1_d0 w1_cc w1_c8 w1_c4 w1_c0 w1_bc w1_b8 w1_b4 w1_b0 w1_ac w1_a8 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 g1_27 g1_26 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hv h0'), sv_fail_2c60 F E2 s2 t2 (fun x hx => (fR2 x hx).trans (fM x hx).symm) V2 hret g2_2 g2_18 hO g2_3 g2_4⟩
  -- 0x2B34: branch, not taken
  obtain ⟨n1, d1, u1⟩ := s0.notTaken E0.self 0x2B38 sv_at_2b34
    (by decide) (by rw [g0_10, s0.zero]; exact br_beq_f hv)
  have s1 : St n1.mem SV n1 0x2B38 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
  have g1_10 : reg n1 a0 = pv := by rw [u1.regs, g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = dp := by rw [u1.regs, g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u1.regs, g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = dg := by rw [u1.regs, g0_24]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u1.regs, g0_27]
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
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m1]; exact w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m1]; exact w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m1]; exact w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m1]; exact w0_84
  have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m1]; exact w0_88
  have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m1]; exact w0_8c
  have w1_90 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m1]; exact w0_90
  have w1_94 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m1]; exact w0_94
  have w1_98 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m1]; exact w0_98
  have w1_9c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m1]; exact w0_9c
  have w1_a0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m1]; exact w0_a0
  have w1_a4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m1]; exact w0_a4
  have w1_a8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m1]; exact w0_a8
  have w1_ac : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m1]; exact w0_ac
  have w1_b0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m1]; exact w0_b0
  have w1_b4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m1]; exact w0_b4
  have w1_b8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m1]; exact w0_b8
  have w1_bc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m1]; exact w0_bc
  have w1_c0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m1]; exact w0_c0
  have w1_c4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m1]; exact w0_c4
  have w1_c8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m1]; exact w0_c8
  have w1_cc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m1]; exact w0_cc
  have w1_d0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m1]; exact w0_d0
  have w1_d4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m1]; exact w0_d4
  have w1_d8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m1]; exact w0_d8
  have w1_dc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m1]; exact w0_dc
  have w1_e0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m1]; exact w0_e0
  have w1_e4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m1]; exact w0_e4
  have w1_e8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m1]; exact w0_e8
  have w1_ec : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m1]; exact w0_ec
  have w1_f0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m1]; exact w0_f0
  have w1_f4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m1]; exact w0_f4
  have w1_f8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m1]; exact w0_f8
  have w1_fc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m1]; exact w0_fc
  have w1_100 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m1]; exact w0_100
  have w1_104 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m1]; exact w0_104
  have w1_108 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m1]; exact w0_108
  have w1_10c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m1]; exact w0_10c
  have w1_110 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m1]; exact w0_110
  have w1_114 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m1]; exact w0_114
  have w1_118 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m1]; exact w0_118
  have w1_11c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m1]; exact w0_11c
  have w1_120 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m1]; exact w0_120
  have w1_124 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m1]; exact w0_124
  have w1_128 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m1]; exact w0_128
  have w1_12c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m1]; exact w0_12c
  have w1_130 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m1]; exact w0_130
  have w1_a20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m1]; exact w0_a20
  have w1_a24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m1]; exact w0_a24
  have w1_a28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m1]; exact w0_a28
  have w1_a2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m1]; exact w0_a2c
  have w1_a30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m1]; exact w0_a30
  have w1_a34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m1]; exact w0_a34
  have w1_a38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m1]; exact w0_a38
  have w1_a3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m1]; exact w0_a3c
  have w1_aa0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m1]; exact w0_aa0
  have w1_aa4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m1]; exact w0_aa4
  -- 0x2B38: lw outside the stack
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_2b38 (off' := 0x2B3C) (by decide)
    (by rw [g1_19]; exact a_ckp)
  have s2 : St n2.mem SV n2 0x2B3C (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_10 : reg n2 a0 = pv := by rw [u2.regs, upd_ne (by decide) (by decide), g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = dp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_24]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_11 : reg n2 a1 = ckp := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_19, sv_ld fR1 ckp_in4, hckp]
  have w2_24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m2]; exact w1_24
  have w2_28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m2]; exact w1_28
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m2]; exact w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m2]; exact w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m2]; exact w1_38
  have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m2]; exact w1_3c
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m2]; exact w1_40
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m2]; exact w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m2]; exact w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m2]; exact w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m2]; exact w1_54
  have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m2]; exact w1_58
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m2]; exact w1_5c
  have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m2]; exact w1_60
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m2]; exact w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m2]; exact w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m2]; exact w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m2]; exact w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m2]; exact w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m2]; exact w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m2]; exact w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m2]; exact w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m2]; exact w1_8c
  have w2_90 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m2]; exact w1_90
  have w2_94 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m2]; exact w1_94
  have w2_98 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m2]; exact w1_98
  have w2_9c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m2]; exact w1_9c
  have w2_a0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m2]; exact w1_a0
  have w2_a4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m2]; exact w1_a4
  have w2_a8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m2]; exact w1_a8
  have w2_ac : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m2]; exact w1_ac
  have w2_b0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m2]; exact w1_b0
  have w2_b4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m2]; exact w1_b4
  have w2_b8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m2]; exact w1_b8
  have w2_bc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m2]; exact w1_bc
  have w2_c0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m2]; exact w1_c0
  have w2_c4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m2]; exact w1_c4
  have w2_c8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m2]; exact w1_c8
  have w2_cc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m2]; exact w1_cc
  have w2_d0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m2]; exact w1_d0
  have w2_d4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m2]; exact w1_d4
  have w2_d8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m2]; exact w1_d8
  have w2_dc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m2]; exact w1_dc
  have w2_e0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m2]; exact w1_e0
  have w2_e4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m2]; exact w1_e4
  have w2_e8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m2]; exact w1_e8
  have w2_ec : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m2]; exact w1_ec
  have w2_f0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m2]; exact w1_f0
  have w2_f4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m2]; exact w1_f4
  have w2_f8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m2]; exact w1_f8
  have w2_fc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m2]; exact w1_fc
  have w2_100 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m2]; exact w1_100
  have w2_104 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m2]; exact w1_104
  have w2_108 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m2]; exact w1_108
  have w2_10c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m2]; exact w1_10c
  have w2_110 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m2]; exact w1_110
  have w2_114 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m2]; exact w1_114
  have w2_118 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m2]; exact w1_118
  have w2_11c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m2]; exact w1_11c
  have w2_120 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m2]; exact w1_120
  have w2_124 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m2]; exact w1_124
  have w2_128 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m2]; exact w1_128
  have w2_12c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m2]; exact w1_12c
  have w2_130 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m2]; exact w1_130
  have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m2]; exact w1_a20
  have w2_a24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m2]; exact w1_a24
  have w2_a28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m2]; exact w1_a28
  have w2_a2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m2]; exact w1_a2c
  have w2_a30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m2]; exact w1_a30
  have w2_a34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m2]; exact w1_a34
  have w2_a38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m2]; exact w1_a38
  have w2_a3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m2]; exact w1_a3c
  have w2_aa0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m2]; exact w1_aa0
  have w2_aa4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m2]; exact w1_aa4
  clear w1_aa4 w1_aa0 w1_a3c w1_a38 w1_a34 w1_a30 w1_a2c w1_a28 w1_a24 w1_a20 w1_130 w1_12c w1_128 w1_124 w1_120 w1_11c w1_118 w1_114 w1_110 w1_10c w1_108 w1_104 w1_100 w1_fc w1_f8 w1_f4 w1_f0 w1_ec w1_e8 w1_e4 w1_e0 w1_dc w1_d8 w1_d4 w1_d0 w1_cc w1_c8 w1_c4 w1_c0 w1_bc w1_b8 w1_b4 w1_b0 w1_ac w1_a8 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 g1_27 g1_26 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x2B3C: lw outside the stack
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_2b3c (off' := 0x2B40) (by decide)
    (by rw [g2_19]; exact a_ckl)
  have s3 : St n3.mem SV n3 0x2B40 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_10 : reg n3 a0 = pv := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
  have g3_11 : reg n3 a1 = ckp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_11]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = dp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_25 : reg n3 (25 : Fin 32) = ckl := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_19, sv_ld fR2 ckl_in4, hckl]
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
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m3]; exact w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m3]; exact w2_8c
  have w3_90 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m3]; exact w2_90
  have w3_94 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m3]; exact w2_94
  have w3_98 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m3]; exact w2_98
  have w3_9c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m3]; exact w2_9c
  have w3_a0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m3]; exact w2_a0
  have w3_a4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m3]; exact w2_a4
  have w3_a8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m3]; exact w2_a8
  have w3_ac : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m3]; exact w2_ac
  have w3_b0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m3]; exact w2_b0
  have w3_b4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m3]; exact w2_b4
  have w3_b8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m3]; exact w2_b8
  have w3_bc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m3]; exact w2_bc
  have w3_c0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m3]; exact w2_c0
  have w3_c4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m3]; exact w2_c4
  have w3_c8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m3]; exact w2_c8
  have w3_cc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m3]; exact w2_cc
  have w3_d0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m3]; exact w2_d0
  have w3_d4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m3]; exact w2_d4
  have w3_d8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m3]; exact w2_d8
  have w3_dc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m3]; exact w2_dc
  have w3_e0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m3]; exact w2_e0
  have w3_e4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m3]; exact w2_e4
  have w3_e8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m3]; exact w2_e8
  have w3_ec : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m3]; exact w2_ec
  have w3_f0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m3]; exact w2_f0
  have w3_f4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m3]; exact w2_f4
  have w3_f8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m3]; exact w2_f8
  have w3_fc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m3]; exact w2_fc
  have w3_100 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m3]; exact w2_100
  have w3_104 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m3]; exact w2_104
  have w3_108 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m3]; exact w2_108
  have w3_10c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m3]; exact w2_10c
  have w3_110 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m3]; exact w2_110
  have w3_114 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m3]; exact w2_114
  have w3_118 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m3]; exact w2_118
  have w3_11c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m3]; exact w2_11c
  have w3_120 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m3]; exact w2_120
  have w3_124 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m3]; exact w2_124
  have w3_128 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m3]; exact w2_128
  have w3_12c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m3]; exact w2_12c
  have w3_130 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m3]; exact w2_130
  have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m3]; exact w2_a20
  have w3_a24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m3]; exact w2_a24
  have w3_a28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m3]; exact w2_a28
  have w3_a2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m3]; exact w2_a2c
  have w3_a30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m3]; exact w2_a30
  have w3_a34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m3]; exact w2_a34
  have w3_a38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m3]; exact w2_a38
  have w3_a3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m3]; exact w2_a3c
  have w3_aa0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m3]; exact w2_aa0
  have w3_aa4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m3]; exact w2_aa4
  clear w2_aa4 w2_aa0 w2_a3c w2_a38 w2_a34 w2_a30 w2_a2c w2_a28 w2_a24 w2_a20 w2_130 w2_12c w2_128 w2_124 w2_120 w2_11c w2_118 w2_114 w2_110 w2_10c w2_108 w2_104 w2_100 w2_fc w2_f8 w2_f4 w2_f0 w2_ec w2_e8 w2_e4 w2_e0 w2_dc w2_d8 w2_d4 w2_d0 w2_cc w2_c8 w2_c4 w2_c0 w2_bc w2_b8 w2_b4 w2_b0 w2_ac w2_a8 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_44 w2_40 w2_3c w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 g2_11 g2_27 g2_26 g2_24 g2_23 g2_22 g2_21 g2_19 g2_18 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x2B40
  obtain ⟨n4, c4, u4⟩ := s3.block svCk12b40 E3.self svCk12b40_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x2B44 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svCk12b40 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_11 : reg n4 a1 = ckp := by
    rw [rb4, runBlock_reg _ _ _ a1 s3.zero (by decide), g3_11]
  have g4_18 : reg n4 (18 : Fin 32) = out := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = dp := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb4, runBlock_reg _ _ _ (23 : Fin 32) s3.zero (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = dg := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = ckl := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCk12b40, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_10, g3_11, g3_18, g3_19, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m4]; exact w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m4]; exact w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m4]; exact w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m4]; exact w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m4]; exact w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m4]; exact w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m4]; exact w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m4]; exact w3_94
  have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m4]; exact w3_98
  have w4_9c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m4]; exact w3_9c
  have w4_a0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m4]; exact w3_a0
  have w4_a4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m4]; exact w3_a4
  have w4_a8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m4]; exact w3_a8
  have w4_ac : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m4]; exact w3_ac
  have w4_b0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m4]; exact w3_b0
  have w4_b4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m4]; exact w3_b4
  have w4_b8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m4]; exact w3_b8
  have w4_bc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m4]; exact w3_bc
  have w4_c0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m4]; exact w3_c0
  have w4_c4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m4]; exact w3_c4
  have w4_c8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m4]; exact w3_c8
  have w4_cc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m4]; exact w3_cc
  have w4_d0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m4]; exact w3_d0
  have w4_d4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m4]; exact w3_d4
  have w4_d8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m4]; exact w3_d8
  have w4_dc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m4]; exact w3_dc
  have w4_e0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m4]; exact w3_e0
  have w4_e4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m4]; exact w3_e4
  have w4_e8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m4]; exact w3_e8
  have w4_ec : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m4]; exact w3_ec
  have w4_f0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m4]; exact w3_f0
  have w4_f4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m4]; exact w3_f4
  have w4_f8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m4]; exact w3_f8
  have w4_fc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m4]; exact w3_fc
  have w4_100 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m4]; exact w3_100
  have w4_104 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m4]; exact w3_104
  have w4_108 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m4]; exact w3_108
  have w4_10c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m4]; exact w3_10c
  have w4_110 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m4]; exact w3_110
  have w4_114 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m4]; exact w3_114
  have w4_118 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m4]; exact w3_118
  have w4_11c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m4]; exact w3_11c
  have w4_120 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m4]; exact w3_120
  have w4_124 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m4]; exact w3_124
  have w4_128 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m4]; exact w3_128
  have w4_12c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m4]; exact w3_12c
  have w4_130 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m4]; exact w3_130
  have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m4]; exact w3_a20
  have w4_a24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m4]; exact w3_a24
  have w4_a28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m4]; exact w3_a28
  have w4_a2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m4]; exact w3_a2c
  have w4_a30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m4]; exact w3_a30
  have w4_a34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m4]; exact w3_a34
  have w4_a38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m4]; exact w3_a38
  have w4_a3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m4]; exact w3_a3c
  have w4_aa0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m4]; exact w3_aa0
  have w4_aa4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m4]; exact w3_aa4
  clear w3_aa4 w3_aa0 w3_a3c w3_a38 w3_a34 w3_a30 w3_a2c w3_a28 w3_a24 w3_a20 w3_130 w3_12c w3_128 w3_124 w3_120 w3_11c w3_118 w3_114 w3_110 w3_10c w3_108 w3_104 w3_100 w3_fc w3_f8 w3_f4 w3_f0 w3_ec w3_e8 w3_e4 w3_e0 w3_dc w3_d8 w3_d4 w3_d0 w3_cc w3_c8 w3_c4 w3_c0 w3_bc w3_b8 w3_b4 w3_b0 w3_ac w3_a8 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 g3_25 g3_27 g3_26 g3_24 g3_23 g3_22 g3_21 g3_19 g3_18 g3_11 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x2B44: sw
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := sv_sw F E4 s4 sv_at_2b44 (off' := 0x2B46) (c := 0x24)
    (by decide) (by rw [g4_2]; sv_addr) (by decide) (by decide)
  have t5 : Steps n0 n5 := t4.trans d5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keep K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rg5 sp, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg5 (3 : Fin 32), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg5 (4 : Fin 32), g4_4]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [rg5 a0, g4_10]
  have g5_11 : reg n5 a1 = ckp := by rw [rg5 a1, g4_11]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rg5 (18 : Fin 32), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rg5 (19 : Fin 32), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [rg5 (21 : Fin 32), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = dp := by rw [rg5 (22 : Fin 32), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg5 (23 : Fin 32), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = dg := by rw [rg5 (24 : Fin 32), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = ckl := by rw [rg5 (25 : Fin 32), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [rg5 (26 : Fin 32), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg5 (27 : Fin 32), g4_27]
  have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K5.w32 (by decide) (by decide)).trans w4_28
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K5.w32 (by decide) (by decide)).trans w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K5.w32 (by decide) (by decide)).trans w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K5.w32 (by decide) (by decide)).trans w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K5.w32 (by decide) (by decide)).trans w4_38
  have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K5.w32 (by decide) (by decide)).trans w4_3c
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K5.w32 (by decide) (by decide)).trans w4_40
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K5.w32 (by decide) (by decide)).trans w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K5.w32 (by decide) (by decide)).trans w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K5.w32 (by decide) (by decide)).trans w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K5.w32 (by decide) (by decide)).trans w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K5.w32 (by decide) (by decide)).trans w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K5.w32 (by decide) (by decide)).trans w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K5.w32 (by decide) (by decide)).trans w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K5.w32 (by decide) (by decide)).trans w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K5.w32 (by decide) (by decide)).trans w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K5.w32 (by decide) (by decide)).trans w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K5.w32 (by decide) (by decide)).trans w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K5.w32 (by decide) (by decide)).trans w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K5.w32 (by decide) (by decide)).trans w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K5.w32 (by decide) (by decide)).trans w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K5.w32 (by decide) (by decide)).trans w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K5.w32 (by decide) (by decide)).trans w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K5.w32 (by decide) (by decide)).trans w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K5.w32 (by decide) (by decide)).trans w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K5.w32 (by decide) (by decide)).trans w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K5.w32 (by decide) (by decide)).trans w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K5.w32 (by decide) (by decide)).trans w4_94
  have w5_98 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K5.w32 (by decide) (by decide)).trans w4_98
  have w5_9c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K5.w32 (by decide) (by decide)).trans w4_9c
  have w5_a0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K5.w32 (by decide) (by decide)).trans w4_a0
  have w5_a4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K5.w32 (by decide) (by decide)).trans w4_a4
  have w5_a8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K5.w32 (by decide) (by decide)).trans w4_a8
  have w5_ac : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K5.w32 (by decide) (by decide)).trans w4_ac
  have w5_b0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K5.w32 (by decide) (by decide)).trans w4_b0
  have w5_b4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K5.w32 (by decide) (by decide)).trans w4_b4
  have w5_b8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K5.w32 (by decide) (by decide)).trans w4_b8
  have w5_bc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K5.w32 (by decide) (by decide)).trans w4_bc
  have w5_c0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K5.w32 (by decide) (by decide)).trans w4_c0
  have w5_c4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K5.w32 (by decide) (by decide)).trans w4_c4
  have w5_c8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K5.w32 (by decide) (by decide)).trans w4_c8
  have w5_cc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K5.w32 (by decide) (by decide)).trans w4_cc
  have w5_d0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K5.w32 (by decide) (by decide)).trans w4_d0
  have w5_d4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K5.w32 (by decide) (by decide)).trans w4_d4
  have w5_d8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K5.w32 (by decide) (by decide)).trans w4_d8
  have w5_dc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K5.w32 (by decide) (by decide)).trans w4_dc
  have w5_e0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K5.w32 (by decide) (by decide)).trans w4_e0
  have w5_e4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K5.w32 (by decide) (by decide)).trans w4_e4
  have w5_e8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K5.w32 (by decide) (by decide)).trans w4_e8
  have w5_ec : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K5.w32 (by decide) (by decide)).trans w4_ec
  have w5_f0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K5.w32 (by decide) (by decide)).trans w4_f0
  have w5_f4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K5.w32 (by decide) (by decide)).trans w4_f4
  have w5_f8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K5.w32 (by decide) (by decide)).trans w4_f8
  have w5_fc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K5.w32 (by decide) (by decide)).trans w4_fc
  have w5_100 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K5.w32 (by decide) (by decide)).trans w4_100
  have w5_104 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K5.w32 (by decide) (by decide)).trans w4_104
  have w5_108 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K5.w32 (by decide) (by decide)).trans w4_108
  have w5_10c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K5.w32 (by decide) (by decide)).trans w4_10c
  have w5_110 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K5.w32 (by decide) (by decide)).trans w4_110
  have w5_114 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K5.w32 (by decide) (by decide)).trans w4_114
  have w5_118 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K5.w32 (by decide) (by decide)).trans w4_118
  have w5_11c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K5.w32 (by decide) (by decide)).trans w4_11c
  have w5_120 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K5.w32 (by decide) (by decide)).trans w4_120
  have w5_124 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K5.w32 (by decide) (by decide)).trans w4_124
  have w5_128 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K5.w32 (by decide) (by decide)).trans w4_128
  have w5_12c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K5.w32 (by decide) (by decide)).trans w4_12c
  have w5_130 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K5.w32 (by decide) (by decide)).trans w4_130
  have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K5.w32 (by decide) (by decide)).trans w4_a20
  have w5_a24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K5.w32 (by decide) (by decide)).trans w4_a24
  have w5_a28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K5.w32 (by decide) (by decide)).trans w4_a28
  have w5_a2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K5.w32 (by decide) (by decide)).trans w4_a2c
  have w5_a30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K5.w32 (by decide) (by decide)).trans w4_a30
  have w5_a34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K5.w32 (by decide) (by decide)).trans w4_a34
  have w5_a38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K5.w32 (by decide) (by decide)).trans w4_a38
  have w5_a3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K5.w32 (by decide) (by decide)).trans w4_a3c
  have w5_aa0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K5.w32 (by decide) (by decide)).trans w4_aa0
  have w5_aa4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K5.w32 (by decide) (by decide)).trans w4_aa4
  have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [W5, g4_11]
  clear w4_aa4 w4_aa0 w4_a3c w4_a38 w4_a34 w4_a30 w4_a2c w4_a28 w4_a24 w4_a20 w4_130 w4_12c w4_128 w4_124 w4_120 w4_11c w4_118 w4_114 w4_110 w4_10c w4_108 w4_104 w4_100 w4_fc w4_f8 w4_f4 w4_f0 w4_ec w4_e8 w4_e4 w4_e0 w4_dc w4_d8 w4_d4 w4_d0 w4_cc w4_c8 w4_c4 w4_c0 w4_bc w4_b8 w4_b4 w4_b0 w4_ac w4_a8 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_19 g4_18 g4_11 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x2B46
  obtain ⟨n6, c6, u6⟩ := s5.block svCk12b46 E5.self svCk12b46_end
    ⟨trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x2B48 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svCk12b46 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb6, runBlock_reg _ _ _ a0 s5.zero (by decide), g5_10]
  have g6_11 : reg n6 a1 = ckp := by
    rw [rb6, runBlock_reg _ _ _ a1 s5.zero (by decide), g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = dp := by
    rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = dg := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = ckl := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_12 : reg n6 a2 = ckl := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCk12b46, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_10, g5_11, g5_18, g5_19, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m6]; exact w5_24
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
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m6]; exact w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m6]; exact w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m6]; exact w5_8c
  have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m6]; exact w5_90
  have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m6]; exact w5_94
  have w6_98 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m6]; exact w5_98
  have w6_9c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m6]; exact w5_9c
  have w6_a0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m6]; exact w5_a0
  have w6_a4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m6]; exact w5_a4
  have w6_a8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m6]; exact w5_a8
  have w6_ac : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m6]; exact w5_ac
  have w6_b0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m6]; exact w5_b0
  have w6_b4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m6]; exact w5_b4
  have w6_b8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m6]; exact w5_b8
  have w6_bc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m6]; exact w5_bc
  have w6_c0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m6]; exact w5_c0
  have w6_c4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m6]; exact w5_c4
  have w6_c8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m6]; exact w5_c8
  have w6_cc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m6]; exact w5_cc
  have w6_d0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m6]; exact w5_d0
  have w6_d4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m6]; exact w5_d4
  have w6_d8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m6]; exact w5_d8
  have w6_dc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m6]; exact w5_dc
  have w6_e0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m6]; exact w5_e0
  have w6_e4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m6]; exact w5_e4
  have w6_e8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m6]; exact w5_e8
  have w6_ec : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m6]; exact w5_ec
  have w6_f0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m6]; exact w5_f0
  have w6_f4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m6]; exact w5_f4
  have w6_f8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m6]; exact w5_f8
  have w6_fc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m6]; exact w5_fc
  have w6_100 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m6]; exact w5_100
  have w6_104 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m6]; exact w5_104
  have w6_108 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m6]; exact w5_108
  have w6_10c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m6]; exact w5_10c
  have w6_110 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m6]; exact w5_110
  have w6_114 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m6]; exact w5_114
  have w6_118 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m6]; exact w5_118
  have w6_11c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m6]; exact w5_11c
  have w6_120 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m6]; exact w5_120
  have w6_124 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m6]; exact w5_124
  have w6_128 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m6]; exact w5_128
  have w6_12c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m6]; exact w5_12c
  have w6_130 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m6]; exact w5_130
  have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m6]; exact w5_a20
  have w6_a24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m6]; exact w5_a24
  have w6_a28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m6]; exact w5_a28
  have w6_a2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m6]; exact w5_a2c
  have w6_a30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m6]; exact w5_a30
  have w6_a34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m6]; exact w5_a34
  have w6_a38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m6]; exact w5_a38
  have w6_a3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m6]; exact w5_a3c
  have w6_aa0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m6]; exact w5_aa0
  have w6_aa4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m6]; exact w5_aa4
  clear w5_24 w5_aa4 w5_aa0 w5_a3c w5_a38 w5_a34 w5_a30 w5_a2c w5_a28 w5_a24 w5_a20 w5_130 w5_12c w5_128 w5_124 w5_120 w5_11c w5_118 w5_114 w5_110 w5_10c w5_108 w5_104 w5_100 w5_fc w5_f8 w5_f4 w5_f0 w5_ec w5_e8 w5_e4 w5_e0 w5_dc w5_d8 w5_d4 w5_d0 w5_cc w5_c8 w5_c4 w5_c0 w5_bc w5_b8 w5_b4 w5_b0 w5_ac w5_a8 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 w5_2c w5_28 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_11 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 rg5 W5 K5 fr5 s5 d5
  -- 0x2B48: sv_lineF
  obtain ⟨n7, c7, s7, rk7, K7, L7, fr7⟩ := sv_lineF (oc := 0x420) (nl := (ckl).toNat)
    F E6 (CK0.sv F fR6) s6 sv_at_2b48 sv_at_2b4c (by decide) (by decide)
    g6_10 g6_11 (by rw [g6_12, ofNat_toNat_self]) (by decide) (by decide) (.inl ck_in)
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keepL K7 (by decide)
  rw [nlScan_ro F fR6 (.inl ck_in)] at L7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rk7 sp (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk7 (3 : Fin 32) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk7 (4 : Fin 32) (by decide), g6_4]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rk7 (18 : Fin 32) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rk7 (19 : Fin 32) (by decide), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [rk7 (21 : Fin 32) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = dp := by rw [rk7 (22 : Fin 32) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rk7 (23 : Fin 32) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = dg := by rw [rk7 (24 : Fin 32) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = ckl := by rw [rk7 (25 : Fin 32) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rk7 (26 : Fin 32) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk7 (27 : Fin 32) (by decide), g6_27]
  obtain ⟨r7, hr7⟩ : ∃ r, nlScan M0 (ckp) 0 ((ckl).toNat) = r := ⟨_, rfl⟩
  rcases r7 with _ | ix7
  · rw [hr7] at L7
    obtain ⟨z0_7, z4_7⟩ := L7
    have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K7.w32 (by decide) (by decide)).trans w6_24
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
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K7.w32 (by decide) (by decide)).trans w6_74
    have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K7.w32 (by decide) (by decide)).trans w6_78
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K7.w32 (by decide) (by decide)).trans w6_7c
    have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K7.w32 (by decide) (by decide)).trans w6_80
    have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K7.w32 (by decide) (by decide)).trans w6_84
    have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K7.w32 (by decide) (by decide)).trans w6_88
    have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K7.w32 (by decide) (by decide)).trans w6_8c
    have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K7.w32 (by decide) (by decide)).trans w6_90
    have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K7.w32 (by decide) (by decide)).trans w6_94
    have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K7.w32 (by decide) (by decide)).trans w6_98
    have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K7.w32 (by decide) (by decide)).trans w6_9c
    have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K7.w32 (by decide) (by decide)).trans w6_a0
    have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K7.w32 (by decide) (by decide)).trans w6_a4
    have w7_a8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K7.w32 (by decide) (by decide)).trans w6_a8
    have w7_ac : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K7.w32 (by decide) (by decide)).trans w6_ac
    have w7_b0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K7.w32 (by decide) (by decide)).trans w6_b0
    have w7_b4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K7.w32 (by decide) (by decide)).trans w6_b4
    have w7_b8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K7.w32 (by decide) (by decide)).trans w6_b8
    have w7_bc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K7.w32 (by decide) (by decide)).trans w6_bc
    have w7_c0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K7.w32 (by decide) (by decide)).trans w6_c0
    have w7_c4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K7.w32 (by decide) (by decide)).trans w6_c4
    have w7_c8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K7.w32 (by decide) (by decide)).trans w6_c8
    have w7_cc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K7.w32 (by decide) (by decide)).trans w6_cc
    have w7_d0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K7.w32 (by decide) (by decide)).trans w6_d0
    have w7_d4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K7.w32 (by decide) (by decide)).trans w6_d4
    have w7_d8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K7.w32 (by decide) (by decide)).trans w6_d8
    have w7_dc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K7.w32 (by decide) (by decide)).trans w6_dc
    have w7_e0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K7.w32 (by decide) (by decide)).trans w6_e0
    have w7_e4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K7.w32 (by decide) (by decide)).trans w6_e4
    have w7_e8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K7.w32 (by decide) (by decide)).trans w6_e8
    have w7_ec : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K7.w32 (by decide) (by decide)).trans w6_ec
    have w7_f0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K7.w32 (by decide) (by decide)).trans w6_f0
    have w7_f4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K7.w32 (by decide) (by decide)).trans w6_f4
    have w7_f8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K7.w32 (by decide) (by decide)).trans w6_f8
    have w7_fc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K7.w32 (by decide) (by decide)).trans w6_fc
    have w7_100 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K7.w32 (by decide) (by decide)).trans w6_100
    have w7_104 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K7.w32 (by decide) (by decide)).trans w6_104
    have w7_108 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K7.w32 (by decide) (by decide)).trans w6_108
    have w7_10c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K7.w32 (by decide) (by decide)).trans w6_10c
    have w7_110 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K7.w32 (by decide) (by decide)).trans w6_110
    have w7_114 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K7.w32 (by decide) (by decide)).trans w6_114
    have w7_118 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K7.w32 (by decide) (by decide)).trans w6_118
    have w7_11c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K7.w32 (by decide) (by decide)).trans w6_11c
    have w7_120 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K7.w32 (by decide) (by decide)).trans w6_120
    have w7_124 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K7.w32 (by decide) (by decide)).trans w6_124
    have w7_128 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K7.w32 (by decide) (by decide)).trans w6_128
    have w7_12c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K7.w32 (by decide) (by decide)).trans w6_12c
    have w7_130 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K7.w32 (by decide) (by decide)).trans w6_130
    have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K7.w32 (by decide) (by decide)).trans w6_a20
    have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K7.w32 (by decide) (by decide)).trans w6_a24
    have w7_a28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K7.w32 (by decide) (by decide)).trans w6_a28
    have w7_a2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K7.w32 (by decide) (by decide)).trans w6_a2c
    have w7_a30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K7.w32 (by decide) (by decide)).trans w6_a30
    have w7_a34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K7.w32 (by decide) (by decide)).trans w6_a34
    have w7_a38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K7.w32 (by decide) (by decide)).trans w6_a38
    have w7_a3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K7.w32 (by decide) (by decide)).trans w6_a3c
    have w7_aa0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K7.w32 (by decide) (by decide)).trans w6_aa0
    have w7_aa4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K7.w32 (by decide) (by decide)).trans w6_aa4
    have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z0_7
    have b7_424 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := z4_7
    clear w6_aa4 w6_aa0 w6_a3c w6_a38 w6_a34 w6_a30 w6_a2c w6_a28 w6_a24 w6_a20 w6_130 w6_12c w6_128 w6_124 w6_120 w6_11c w6_118 w6_114 w6_110 w6_10c w6_108 w6_104 w6_100 w6_fc w6_f8 w6_f4 w6_f0 w6_ec w6_e8 w6_e4 w6_e0 w6_dc w6_d8 w6_d4 w6_d0 w6_cc w6_c8 w6_c4 w6_c0 w6_bc w6_b8 w6_b4 w6_b0 w6_ac w6_a8 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 g6_12 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_11 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    -- 0x2B50: lw
    obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_2b50 (off' := 0x2B54) (by decide)
      (by rw [g7_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s8 : St n8.mem SV n8 0x2B54 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = dp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = dg := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = ckl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
    have g8_10 : reg n8 a0 = 0 := by
      rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g7_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w7_420]
    have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m8]; exact w7_24
    have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m8]; exact w7_28
    have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m8]; exact w7_2c
    have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m8]; exact w7_30
    have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m8]; exact w7_34
    have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m8]; exact w7_38
    have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m8]; exact w7_3c
    have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m8]; exact w7_40
    have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
    have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m8]; exact w7_48
    have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m8]; exact w7_4c
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
    have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m8]; exact w7_54
    have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m8]; exact w7_58
    have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m8]; exact w7_5c
    have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m8]; exact w7_60
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
    have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m8]; exact w7_68
    have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m8]; exact w7_6c
    have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m8]; exact w7_70
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m8]; exact w7_74
    have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m8]; exact w7_78
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m8]; exact w7_7c
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m8]; exact w7_80
    have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m8]; exact w7_84
    have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m8]; exact w7_88
    have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m8]; exact w7_8c
    have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m8]; exact w7_90
    have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m8]; exact w7_94
    have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m8]; exact w7_98
    have w8_9c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m8]; exact w7_9c
    have w8_a0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m8]; exact w7_a0
    have w8_a4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m8]; exact w7_a4
    have w8_a8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m8]; exact w7_a8
    have w8_ac : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m8]; exact w7_ac
    have w8_b0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m8]; exact w7_b0
    have w8_b4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m8]; exact w7_b4
    have w8_b8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m8]; exact w7_b8
    have w8_bc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m8]; exact w7_bc
    have w8_c0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m8]; exact w7_c0
    have w8_c4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m8]; exact w7_c4
    have w8_c8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m8]; exact w7_c8
    have w8_cc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m8]; exact w7_cc
    have w8_d0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m8]; exact w7_d0
    have w8_d4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m8]; exact w7_d4
    have w8_d8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m8]; exact w7_d8
    have w8_dc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m8]; exact w7_dc
    have w8_e0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m8]; exact w7_e0
    have w8_e4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m8]; exact w7_e4
    have w8_e8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m8]; exact w7_e8
    have w8_ec : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m8]; exact w7_ec
    have w8_f0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m8]; exact w7_f0
    have w8_f4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m8]; exact w7_f4
    have w8_f8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m8]; exact w7_f8
    have w8_fc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m8]; exact w7_fc
    have w8_100 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m8]; exact w7_100
    have w8_104 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m8]; exact w7_104
    have w8_108 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m8]; exact w7_108
    have w8_10c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m8]; exact w7_10c
    have w8_110 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m8]; exact w7_110
    have w8_114 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m8]; exact w7_114
    have w8_118 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m8]; exact w7_118
    have w8_11c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m8]; exact w7_11c
    have w8_120 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m8]; exact w7_120
    have w8_124 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m8]; exact w7_124
    have w8_128 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m8]; exact w7_128
    have w8_12c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m8]; exact w7_12c
    have w8_130 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m8]; exact w7_130
    have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m8]; exact w7_420
    have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m8]; exact w7_a20
    have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m8]; exact w7_a24
    have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m8]; exact w7_a28
    have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m8]; exact w7_a2c
    have w8_a30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m8]; exact w7_a30
    have w8_a34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m8]; exact w7_a34
    have w8_a38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m8]; exact w7_a38
    have w8_a3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m8]; exact w7_a3c
    have w8_aa0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m8]; exact w7_aa0
    have w8_aa4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m8]; exact w7_aa4
    have b8_424 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m8]; exact b7_424
    clear b7_424 w7_420 w7_aa4 w7_aa0 w7_a3c w7_a38 w7_a34 w7_a30 w7_a2c w7_a28 w7_a24 w7_a20 w7_130 w7_12c w7_128 w7_124 w7_120 w7_11c w7_118 w7_114 w7_110 w7_10c w7_108 w7_104 w7_100 w7_fc w7_f8 w7_f4 w7_f0 w7_ec w7_e8 w7_e4 w7_e0 w7_dc w7_d8 w7_d4 w7_d0 w7_cc w7_c8 w7_c4 w7_c0 w7_bc w7_b8 w7_b4 w7_b0 w7_ac w7_a8 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 z4_7 z0_7
    -- 0x2B54: sw
    obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sw F E8 s8 sv_at_2b54 (off' := 0x2B56) (c := 0x48)
      (by decide) (by rw [g8_2]; sv_addr) (by decide) (by decide)
    have t9 : Steps n0 n9 := t8.trans d9
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
    have g9_10 : reg n9 a0 = 0 := by rw [rg9 a0, g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rg9 (21 : Fin 32), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = dp := by rw [rg9 (22 : Fin 32), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg9 (23 : Fin 32), g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = dg := by rw [rg9 (24 : Fin 32), g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = ckl := by rw [rg9 (25 : Fin 32), g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rg9 (26 : Fin 32), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg9 (27 : Fin 32), g8_27]
    have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K9.w32 (by decide) (by decide)).trans w8_24
    have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K9.w32 (by decide) (by decide)).trans w8_28
    have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K9.w32 (by decide) (by decide)).trans w8_2c
    have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K9.w32 (by decide) (by decide)).trans w8_30
    have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K9.w32 (by decide) (by decide)).trans w8_34
    have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K9.w32 (by decide) (by decide)).trans w8_38
    have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K9.w32 (by decide) (by decide)).trans w8_3c
    have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K9.w32 (by decide) (by decide)).trans w8_40
    have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K9.w32 (by decide) (by decide)).trans w8_44
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
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K9.w32 (by decide) (by decide)).trans w8_74
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K9.w32 (by decide) (by decide)).trans w8_78
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K9.w32 (by decide) (by decide)).trans w8_7c
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K9.w32 (by decide) (by decide)).trans w8_80
    have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K9.w32 (by decide) (by decide)).trans w8_84
    have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K9.w32 (by decide) (by decide)).trans w8_88
    have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K9.w32 (by decide) (by decide)).trans w8_8c
    have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K9.w32 (by decide) (by decide)).trans w8_90
    have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K9.w32 (by decide) (by decide)).trans w8_94
    have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K9.w32 (by decide) (by decide)).trans w8_98
    have w9_9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K9.w32 (by decide) (by decide)).trans w8_9c
    have w9_a0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K9.w32 (by decide) (by decide)).trans w8_a0
    have w9_a4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K9.w32 (by decide) (by decide)).trans w8_a4
    have w9_a8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K9.w32 (by decide) (by decide)).trans w8_a8
    have w9_ac : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K9.w32 (by decide) (by decide)).trans w8_ac
    have w9_b0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K9.w32 (by decide) (by decide)).trans w8_b0
    have w9_b4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K9.w32 (by decide) (by decide)).trans w8_b4
    have w9_b8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K9.w32 (by decide) (by decide)).trans w8_b8
    have w9_bc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K9.w32 (by decide) (by decide)).trans w8_bc
    have w9_c0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K9.w32 (by decide) (by decide)).trans w8_c0
    have w9_c4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K9.w32 (by decide) (by decide)).trans w8_c4
    have w9_c8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K9.w32 (by decide) (by decide)).trans w8_c8
    have w9_cc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K9.w32 (by decide) (by decide)).trans w8_cc
    have w9_d0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K9.w32 (by decide) (by decide)).trans w8_d0
    have w9_d4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K9.w32 (by decide) (by decide)).trans w8_d4
    have w9_d8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K9.w32 (by decide) (by decide)).trans w8_d8
    have w9_dc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K9.w32 (by decide) (by decide)).trans w8_dc
    have w9_e0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K9.w32 (by decide) (by decide)).trans w8_e0
    have w9_e4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K9.w32 (by decide) (by decide)).trans w8_e4
    have w9_e8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K9.w32 (by decide) (by decide)).trans w8_e8
    have w9_ec : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K9.w32 (by decide) (by decide)).trans w8_ec
    have w9_f0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K9.w32 (by decide) (by decide)).trans w8_f0
    have w9_f4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K9.w32 (by decide) (by decide)).trans w8_f4
    have w9_f8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K9.w32 (by decide) (by decide)).trans w8_f8
    have w9_fc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K9.w32 (by decide) (by decide)).trans w8_fc
    have w9_100 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K9.w32 (by decide) (by decide)).trans w8_100
    have w9_104 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K9.w32 (by decide) (by decide)).trans w8_104
    have w9_108 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K9.w32 (by decide) (by decide)).trans w8_108
    have w9_10c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K9.w32 (by decide) (by decide)).trans w8_10c
    have w9_110 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K9.w32 (by decide) (by decide)).trans w8_110
    have w9_114 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K9.w32 (by decide) (by decide)).trans w8_114
    have w9_118 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K9.w32 (by decide) (by decide)).trans w8_118
    have w9_11c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K9.w32 (by decide) (by decide)).trans w8_11c
    have w9_120 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K9.w32 (by decide) (by decide)).trans w8_120
    have w9_124 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K9.w32 (by decide) (by decide)).trans w8_124
    have w9_128 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K9.w32 (by decide) (by decide)).trans w8_128
    have w9_12c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K9.w32 (by decide) (by decide)).trans w8_12c
    have w9_130 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K9.w32 (by decide) (by decide)).trans w8_130
    have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K9.w32 (by decide) (by decide)).trans w8_420
    have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K9.w32 (by decide) (by decide)).trans w8_a20
    have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K9.w32 (by decide) (by decide)).trans w8_a24
    have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K9.w32 (by decide) (by decide)).trans w8_a28
    have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K9.w32 (by decide) (by decide)).trans w8_a2c
    have w9_a30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K9.w32 (by decide) (by decide)).trans w8_a30
    have w9_a34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K9.w32 (by decide) (by decide)).trans w8_a34
    have w9_a38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K9.w32 (by decide) (by decide)).trans w8_a38
    have w9_a3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K9.w32 (by decide) (by decide)).trans w8_a3c
    have w9_aa0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K9.w32 (by decide) (by decide)).trans w8_aa0
    have w9_aa4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K9.w32 (by decide) (by decide)).trans w8_aa4
    have b9_424 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := (K9.b8 (by decide) (by decide)).trans b8_424
    have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = 0 := by rw [W9, g8_10]
    clear b8_424 w8_aa4 w8_aa0 w8_a3c w8_a38 w8_a34 w8_a30 w8_a2c w8_a28 w8_a24 w8_a20 w8_420 w8_130 w8_12c w8_128 w8_124 w8_120 w8_11c w8_118 w8_114 w8_110 w8_10c w8_108 w8_104 w8_100 w8_fc w8_f8 w8_f4 w8_f0 w8_ec w8_e8 w8_e4 w8_e0 w8_dc w8_d8 w8_d4 w8_d0 w8_cc w8_c8 w8_c4 w8_c0 w8_bc w8_b8 w8_b4 w8_b0 w8_ac w8_a8 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_3c w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    -- 0x2B56: branch, taken
    obtain ⟨n10, d10, u10⟩ := s9.taken E9.self 0x2FEA sv_at_2b56
      (by decide) (by rw [g9_10, s9.zero]; rfl)
    have s10 : St n10.mem SV n10 0x2FEA (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
    have g10_10 : reg n10 a0 = 0 := by rw [u10.regs, g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = dp := by rw [u10.regs, g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u10.regs, g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = dg := by rw [u10.regs, g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = ckl := by rw [u10.regs, g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, g9_27]
    have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m10]; exact w9_24
    have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m10]; exact w9_28
    have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m10]; exact w9_2c
    have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m10]; exact w9_30
    have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m10]; exact w9_34
    have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
    have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m10]; exact w9_3c
    have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m10]; exact w9_40
    have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
    have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = 0 := by rw [m10]; exact w9_48
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
    have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m10]; exact w9_74
    have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m10]; exact w9_78
    have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m10]; exact w9_7c
    have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m10]; exact w9_80
    have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m10]; exact w9_84
    have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m10]; exact w9_88
    have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m10]; exact w9_8c
    have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m10]; exact w9_90
    have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m10]; exact w9_94
    have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m10]; exact w9_98
    have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m10]; exact w9_9c
    have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m10]; exact w9_a0
    have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m10]; exact w9_a4
    have w10_a8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m10]; exact w9_a8
    have w10_ac : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m10]; exact w9_ac
    have w10_b0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m10]; exact w9_b0
    have w10_b4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m10]; exact w9_b4
    have w10_b8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m10]; exact w9_b8
    have w10_bc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m10]; exact w9_bc
    have w10_c0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m10]; exact w9_c0
    have w10_c4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m10]; exact w9_c4
    have w10_c8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m10]; exact w9_c8
    have w10_cc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m10]; exact w9_cc
    have w10_d0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m10]; exact w9_d0
    have w10_d4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m10]; exact w9_d4
    have w10_d8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m10]; exact w9_d8
    have w10_dc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m10]; exact w9_dc
    have w10_e0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m10]; exact w9_e0
    have w10_e4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m10]; exact w9_e4
    have w10_e8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m10]; exact w9_e8
    have w10_ec : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m10]; exact w9_ec
    have w10_f0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m10]; exact w9_f0
    have w10_f4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m10]; exact w9_f4
    have w10_f8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m10]; exact w9_f8
    have w10_fc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m10]; exact w9_fc
    have w10_100 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m10]; exact w9_100
    have w10_104 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m10]; exact w9_104
    have w10_108 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m10]; exact w9_108
    have w10_10c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m10]; exact w9_10c
    have w10_110 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m10]; exact w9_110
    have w10_114 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m10]; exact w9_114
    have w10_118 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m10]; exact w9_118
    have w10_11c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m10]; exact w9_11c
    have w10_120 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m10]; exact w9_120
    have w10_124 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m10]; exact w9_124
    have w10_128 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m10]; exact w9_128
    have w10_12c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m10]; exact w9_12c
    have w10_130 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m10]; exact w9_130
    have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m10]; exact w9_420
    have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m10]; exact w9_a20
    have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m10]; exact w9_a24
    have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m10]; exact w9_a28
    have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m10]; exact w9_a2c
    have w10_a30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m10]; exact w9_a30
    have w10_a34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m10]; exact w9_a34
    have w10_a38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m10]; exact w9_a38
    have w10_a3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m10]; exact w9_a3c
    have w10_aa0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m10]; exact w9_aa0
    have w10_aa4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m10]; exact w9_aa4
    have b10_424 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m10]; exact b9_424
    clear w9_48 b9_424 w9_aa4 w9_aa0 w9_a3c w9_a38 w9_a34 w9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_420 w9_130 w9_12c w9_128 w9_124 w9_120 w9_11c w9_118 w9_114 w9_110 w9_10c w9_108 w9_104 w9_100 w9_fc w9_f8 w9_f4 w9_f0 w9_ec w9_e8 w9_e4 w9_e0 w9_dc w9_d8 w9_d4 w9_d0 w9_cc w9_c8 w9_c4 w9_c0 w9_bc w9_b8 w9_b4 w9_b0 w9_ac w9_a8 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_44 w9_40 w9_3c w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_10 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
    -- 0x2FEA: lbu
    obtain ⟨n11, d11, u11⟩ := s10.lbu E10.self sv_at_2fea (off' := 0x2FEE) (by decide)
    have s11 : St n11.mem SV n11 0x2FEE (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
    have g11_10 : reg n11 a0 = 0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = dp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = dg := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = ckl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
    have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m11]; exact w10_24
    have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m11]; exact w10_28
    have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m11]; exact w10_2c
    have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m11]; exact w10_30
    have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m11]; exact w10_34
    have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m11]; exact w10_38
    have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m11]; exact w10_3c
    have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m11]; exact w10_40
    have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m11]; exact w10_44
    have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = 0 := by rw [m11]; exact w10_48
    have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
    have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
    have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m11]; exact w10_54
    have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m11]; exact w10_58
    have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m11]; exact w10_5c
    have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m11]; exact w10_60
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
    have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m11]; exact w10_68
    have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m11]; exact w10_6c
    have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m11]; exact w10_70
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m11]; exact w10_74
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m11]; exact w10_78
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m11]; exact w10_7c
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m11]; exact w10_80
    have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m11]; exact w10_84
    have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m11]; exact w10_88
    have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m11]; exact w10_8c
    have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m11]; exact w10_90
    have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m11]; exact w10_94
    have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m11]; exact w10_98
    have w11_9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m11]; exact w10_9c
    have w11_a0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m11]; exact w10_a0
    have w11_a4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m11]; exact w10_a4
    have w11_a8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m11]; exact w10_a8
    have w11_ac : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m11]; exact w10_ac
    have w11_b0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m11]; exact w10_b0
    have w11_b4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m11]; exact w10_b4
    have w11_b8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m11]; exact w10_b8
    have w11_bc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m11]; exact w10_bc
    have w11_c0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m11]; exact w10_c0
    have w11_c4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m11]; exact w10_c4
    have w11_c8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m11]; exact w10_c8
    have w11_cc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m11]; exact w10_cc
    have w11_d0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m11]; exact w10_d0
    have w11_d4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m11]; exact w10_d4
    have w11_d8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m11]; exact w10_d8
    have w11_dc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m11]; exact w10_dc
    have w11_e0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m11]; exact w10_e0
    have w11_e4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m11]; exact w10_e4
    have w11_e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m11]; exact w10_e8
    have w11_ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m11]; exact w10_ec
    have w11_f0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m11]; exact w10_f0
    have w11_f4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m11]; exact w10_f4
    have w11_f8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m11]; exact w10_f8
    have w11_fc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m11]; exact w10_fc
    have w11_100 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m11]; exact w10_100
    have w11_104 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m11]; exact w10_104
    have w11_108 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m11]; exact w10_108
    have w11_10c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m11]; exact w10_10c
    have w11_110 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m11]; exact w10_110
    have w11_114 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m11]; exact w10_114
    have w11_118 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m11]; exact w10_118
    have w11_11c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m11]; exact w10_11c
    have w11_120 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m11]; exact w10_120
    have w11_124 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m11]; exact w10_124
    have w11_128 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m11]; exact w10_128
    have w11_12c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m11]; exact w10_12c
    have w11_130 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m11]; exact w10_130
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m11]; exact w10_420
    have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m11]; exact w10_a20
    have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m11]; exact w10_a24
    have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m11]; exact w10_a28
    have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m11]; exact w10_a2c
    have w11_a30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m11]; exact w10_a30
    have w11_a34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m11]; exact w10_a34
    have w11_a38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m11]; exact w10_a38
    have w11_a3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m11]; exact w10_a3c
    have w11_aa0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m11]; exact w10_aa0
    have w11_aa4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m11]; exact w10_aa4
    have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m11]; exact b10_424
    clear b10_424 w10_aa4 w10_aa0 w10_a3c w10_a38 w10_a34 w10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_420 w10_130 w10_12c w10_128 w10_124 w10_120 w10_11c w10_118 w10_114 w10_110 w10_10c w10_108 w10_104 w10_100 w10_fc w10_f8 w10_f4 w10_f0 w10_ec w10_e8 w10_e4 w10_e0 w10_dc w10_d8 w10_d4 w10_d0 w10_cc w10_c8 w10_c4 w10_c0 w10_bc w10_b8 w10_b4 w10_b0 w10_ac w10_a8 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_10 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x2FEE: j
    obtain ⟨n12, d12, u12⟩ := s11.jump E11.self sv_at_2fee (off' := 0x966) (by decide)
      (by rw [s11.pc]; decide)
    have s12 : St n12.mem SV n12 0x966 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
    have g12_10 : reg n12 a0 = 0 := by rw [u12.regs, g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = dp := by rw [u12.regs, g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u12.regs, g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = dg := by rw [u12.regs, g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = ckl := by rw [u12.regs, g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, g11_27]
    have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m12]; exact w11_24
    have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m12]; exact w11_28
    have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m12]; exact w11_2c
    have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m12]; exact w11_30
    have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m12]; exact w11_34
    have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m12]; exact w11_38
    have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m12]; exact w11_3c
    have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m12]; exact w11_40
    have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
    have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = 0 := by rw [m12]; exact w11_48
    have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
    have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
    have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m12]; exact w11_54
    have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m12]; exact w11_58
    have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m12]; exact w11_5c
    have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m12]; exact w11_60
    have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
    have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m12]; exact w11_68
    have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
    have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m12]; exact w11_70
    have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m12]; exact w11_74
    have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m12]; exact w11_78
    have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m12]; exact w11_7c
    have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m12]; exact w11_80
    have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m12]; exact w11_84
    have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m12]; exact w11_88
    have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m12]; exact w11_8c
    have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m12]; exact w11_90
    have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m12]; exact w11_94
    have w12_98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m12]; exact w11_98
    have w12_9c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m12]; exact w11_9c
    have w12_a0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m12]; exact w11_a0
    have w12_a4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m12]; exact w11_a4
    have w12_a8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m12]; exact w11_a8
    have w12_ac : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m12]; exact w11_ac
    have w12_b0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m12]; exact w11_b0
    have w12_b4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m12]; exact w11_b4
    have w12_b8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m12]; exact w11_b8
    have w12_bc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m12]; exact w11_bc
    have w12_c0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m12]; exact w11_c0
    have w12_c4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m12]; exact w11_c4
    have w12_c8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m12]; exact w11_c8
    have w12_cc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m12]; exact w11_cc
    have w12_d0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m12]; exact w11_d0
    have w12_d4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m12]; exact w11_d4
    have w12_d8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m12]; exact w11_d8
    have w12_dc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m12]; exact w11_dc
    have w12_e0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m12]; exact w11_e0
    have w12_e4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m12]; exact w11_e4
    have w12_e8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m12]; exact w11_e8
    have w12_ec : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m12]; exact w11_ec
    have w12_f0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m12]; exact w11_f0
    have w12_f4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m12]; exact w11_f4
    have w12_f8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m12]; exact w11_f8
    have w12_fc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m12]; exact w11_fc
    have w12_100 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m12]; exact w11_100
    have w12_104 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m12]; exact w11_104
    have w12_108 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m12]; exact w11_108
    have w12_10c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m12]; exact w11_10c
    have w12_110 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m12]; exact w11_110
    have w12_114 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m12]; exact w11_114
    have w12_118 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m12]; exact w11_118
    have w12_11c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m12]; exact w11_11c
    have w12_120 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m12]; exact w11_120
    have w12_124 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m12]; exact w11_124
    have w12_128 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m12]; exact w11_128
    have w12_12c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m12]; exact w11_12c
    have w12_130 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m12]; exact w11_130
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m12]; exact w11_420
    have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m12]; exact w11_a20
    have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m12]; exact w11_a24
    have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m12]; exact w11_a28
    have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m12]; exact w11_a2c
    have w12_a30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m12]; exact w11_a30
    have w12_a34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m12]; exact w11_a34
    have w12_a38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m12]; exact w11_a38
    have w12_a3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m12]; exact w11_a3c
    have w12_aa0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m12]; exact w11_aa0
    have w12_aa4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m12]; exact w11_aa4
    have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m12]; exact b11_424
    clear b11_424 w11_aa4 w11_aa0 w11_a3c w11_a38 w11_a34 w11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_420 w11_130 w11_12c w11_128 w11_124 w11_120 w11_11c w11_118 w11_114 w11_110 w11_10c w11_108 w11_104 w11_100 w11_fc w11_f8 w11_f4 w11_f0 w11_ec w11_e8 w11_e4 w11_e0 w11_dc w11_d8 w11_d4 w11_d0 w11_cc w11_c8 w11_c4 w11_c0 w11_bc w11_b8 w11_b4 w11_b0 w11_ac w11_a8 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    exact .inl ⟨(fun ⟨h0', ix7', h1', _⟩ => by rw [hr7] at h1'; cases h1'), sv_fail F E12 s12 t12 (fun x hx => (fR12 x hx).trans (fM x hx).symm) V12 hret g12_2 g12_18 hO g12_3 g12_4⟩
  have hix7 : ix7 < (ckl).toNat := by have := (nlScan_lt _ _ _ hr7).2; omega
  rw [hr7] at L7
  obtain ⟨y0_7, y4_7, y8_7, y12_7⟩ := L7
  have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K7.w32 (by decide) (by decide)).trans w6_24
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
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K7.w32 (by decide) (by decide)).trans w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K7.w32 (by decide) (by decide)).trans w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K7.w32 (by decide) (by decide)).trans w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K7.w32 (by decide) (by decide)).trans w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K7.w32 (by decide) (by decide)).trans w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K7.w32 (by decide) (by decide)).trans w6_8c
  have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K7.w32 (by decide) (by decide)).trans w6_90
  have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K7.w32 (by decide) (by decide)).trans w6_94
  have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K7.w32 (by decide) (by decide)).trans w6_98
  have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K7.w32 (by decide) (by decide)).trans w6_9c
  have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K7.w32 (by decide) (by decide)).trans w6_a0
  have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K7.w32 (by decide) (by decide)).trans w6_a4
  have w7_a8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K7.w32 (by decide) (by decide)).trans w6_a8
  have w7_ac : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K7.w32 (by decide) (by decide)).trans w6_ac
  have w7_b0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K7.w32 (by decide) (by decide)).trans w6_b0
  have w7_b4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K7.w32 (by decide) (by decide)).trans w6_b4
  have w7_b8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K7.w32 (by decide) (by decide)).trans w6_b8
  have w7_bc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K7.w32 (by decide) (by decide)).trans w6_bc
  have w7_c0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K7.w32 (by decide) (by decide)).trans w6_c0
  have w7_c4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K7.w32 (by decide) (by decide)).trans w6_c4
  have w7_c8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K7.w32 (by decide) (by decide)).trans w6_c8
  have w7_cc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K7.w32 (by decide) (by decide)).trans w6_cc
  have w7_d0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K7.w32 (by decide) (by decide)).trans w6_d0
  have w7_d4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K7.w32 (by decide) (by decide)).trans w6_d4
  have w7_d8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K7.w32 (by decide) (by decide)).trans w6_d8
  have w7_dc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K7.w32 (by decide) (by decide)).trans w6_dc
  have w7_e0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K7.w32 (by decide) (by decide)).trans w6_e0
  have w7_e4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K7.w32 (by decide) (by decide)).trans w6_e4
  have w7_e8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K7.w32 (by decide) (by decide)).trans w6_e8
  have w7_ec : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K7.w32 (by decide) (by decide)).trans w6_ec
  have w7_f0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K7.w32 (by decide) (by decide)).trans w6_f0
  have w7_f4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K7.w32 (by decide) (by decide)).trans w6_f4
  have w7_f8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K7.w32 (by decide) (by decide)).trans w6_f8
  have w7_fc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K7.w32 (by decide) (by decide)).trans w6_fc
  have w7_100 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K7.w32 (by decide) (by decide)).trans w6_100
  have w7_104 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K7.w32 (by decide) (by decide)).trans w6_104
  have w7_108 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K7.w32 (by decide) (by decide)).trans w6_108
  have w7_10c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K7.w32 (by decide) (by decide)).trans w6_10c
  have w7_110 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K7.w32 (by decide) (by decide)).trans w6_110
  have w7_114 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K7.w32 (by decide) (by decide)).trans w6_114
  have w7_118 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K7.w32 (by decide) (by decide)).trans w6_118
  have w7_11c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K7.w32 (by decide) (by decide)).trans w6_11c
  have w7_120 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K7.w32 (by decide) (by decide)).trans w6_120
  have w7_124 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K7.w32 (by decide) (by decide)).trans w6_124
  have w7_128 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K7.w32 (by decide) (by decide)).trans w6_128
  have w7_12c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K7.w32 (by decide) (by decide)).trans w6_12c
  have w7_130 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K7.w32 (by decide) (by decide)).trans w6_130
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K7.w32 (by decide) (by decide)).trans w6_a20
  have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K7.w32 (by decide) (by decide)).trans w6_a24
  have w7_a28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K7.w32 (by decide) (by decide)).trans w6_a28
  have w7_a2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K7.w32 (by decide) (by decide)).trans w6_a2c
  have w7_a30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K7.w32 (by decide) (by decide)).trans w6_a30
  have w7_a34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K7.w32 (by decide) (by decide)).trans w6_a34
  have w7_a38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K7.w32 (by decide) (by decide)).trans w6_a38
  have w7_a3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K7.w32 (by decide) (by decide)).trans w6_a3c
  have w7_aa0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K7.w32 (by decide) (by decide)).trans w6_aa0
  have w7_aa4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K7.w32 (by decide) (by decide)).trans w6_aa4
  have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := y0_7
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := y4_7
  have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := y8_7
  have w7_42c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := y12_7
  clear w6_aa4 w6_aa0 w6_a3c w6_a38 w6_a34 w6_a30 w6_a2c w6_a28 w6_a24 w6_a20 w6_130 w6_12c w6_128 w6_124 w6_120 w6_11c w6_118 w6_114 w6_110 w6_10c w6_108 w6_104 w6_100 w6_fc w6_f8 w6_f4 w6_f0 w6_ec w6_e8 w6_e4 w6_e0 w6_dc w6_d8 w6_d4 w6_d0 w6_cc w6_c8 w6_c4 w6_c0 w6_bc w6_b8 w6_b4 w6_b0 w6_ac w6_a8 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 g6_12 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_11 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x2B50: lw
  obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_2b50 (off' := 0x2B54) (by decide)
    (by rw [g7_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s8 : St n8.mem SV n8 0x2B54 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = dp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = dg := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = ckl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_10 : reg n8 a0 = ckp := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w7_420]
  have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m8]; exact w7_24
  have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m8]; exact w7_28
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m8]; exact w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m8]; exact w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m8]; exact w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m8]; exact w7_38
  have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m8]; exact w7_3c
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m8]; exact w7_40
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m8]; exact w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m8]; exact w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m8]; exact w7_54
  have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m8]; exact w7_58
  have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m8]; exact w7_5c
  have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m8]; exact w7_60
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m8]; exact w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m8]; exact w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m8]; exact w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m8]; exact w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m8]; exact w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m8]; exact w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m8]; exact w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m8]; exact w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m8]; exact w7_8c
  have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m8]; exact w7_90
  have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m8]; exact w7_94
  have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m8]; exact w7_98
  have w8_9c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m8]; exact w7_9c
  have w8_a0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m8]; exact w7_a0
  have w8_a4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m8]; exact w7_a4
  have w8_a8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m8]; exact w7_a8
  have w8_ac : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m8]; exact w7_ac
  have w8_b0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m8]; exact w7_b0
  have w8_b4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m8]; exact w7_b4
  have w8_b8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m8]; exact w7_b8
  have w8_bc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m8]; exact w7_bc
  have w8_c0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m8]; exact w7_c0
  have w8_c4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m8]; exact w7_c4
  have w8_c8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m8]; exact w7_c8
  have w8_cc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m8]; exact w7_cc
  have w8_d0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m8]; exact w7_d0
  have w8_d4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m8]; exact w7_d4
  have w8_d8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m8]; exact w7_d8
  have w8_dc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m8]; exact w7_dc
  have w8_e0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m8]; exact w7_e0
  have w8_e4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m8]; exact w7_e4
  have w8_e8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m8]; exact w7_e8
  have w8_ec : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m8]; exact w7_ec
  have w8_f0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m8]; exact w7_f0
  have w8_f4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m8]; exact w7_f4
  have w8_f8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m8]; exact w7_f8
  have w8_fc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m8]; exact w7_fc
  have w8_100 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m8]; exact w7_100
  have w8_104 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m8]; exact w7_104
  have w8_108 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m8]; exact w7_108
  have w8_10c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m8]; exact w7_10c
  have w8_110 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m8]; exact w7_110
  have w8_114 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m8]; exact w7_114
  have w8_118 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m8]; exact w7_118
  have w8_11c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m8]; exact w7_11c
  have w8_120 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m8]; exact w7_120
  have w8_124 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m8]; exact w7_124
  have w8_128 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m8]; exact w7_128
  have w8_12c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m8]; exact w7_12c
  have w8_130 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m8]; exact w7_130
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m8]; exact w7_420
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := by rw [m8]; exact w7_424
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m8]; exact w7_428
  have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := by rw [m8]; exact w7_42c
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m8]; exact w7_a20
  have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m8]; exact w7_a24
  have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m8]; exact w7_a28
  have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m8]; exact w7_a2c
  have w8_a30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m8]; exact w7_a30
  have w8_a34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m8]; exact w7_a34
  have w8_a38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m8]; exact w7_a38
  have w8_a3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m8]; exact w7_a3c
  have w8_aa0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m8]; exact w7_aa0
  have w8_aa4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m8]; exact w7_aa4
  clear w7_42c w7_428 w7_424 w7_420 w7_aa4 w7_aa0 w7_a3c w7_a38 w7_a34 w7_a30 w7_a2c w7_a28 w7_a24 w7_a20 w7_130 w7_12c w7_128 w7_124 w7_120 w7_11c w7_118 w7_114 w7_110 w7_10c w7_108 w7_104 w7_100 w7_fc w7_f8 w7_f4 w7_f0 w7_ec w7_e8 w7_e4 w7_e0 w7_dc w7_d8 w7_d4 w7_d0 w7_cc w7_c8 w7_c4 w7_c0 w7_bc w7_b8 w7_b4 w7_b0 w7_ac w7_a8 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 y12_7 y8_7 y4_7 y0_7 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 K7 rk7 s7 c7
  -- 0x2B54: sw
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sw F E8 s8 sv_at_2b54 (off' := 0x2B56) (c := 0x48)
    (by decide) (by rw [g8_2]; sv_addr) (by decide) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_10 : reg n9 a0 = ckp := by rw [rg9 a0, g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rg9 (21 : Fin 32), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = dp := by rw [rg9 (22 : Fin 32), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg9 (23 : Fin 32), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = dg := by rw [rg9 (24 : Fin 32), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = ckl := by rw [rg9 (25 : Fin 32), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rg9 (26 : Fin 32), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg9 (27 : Fin 32), g8_27]
  have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K9.w32 (by decide) (by decide)).trans w8_24
  have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K9.w32 (by decide) (by decide)).trans w8_28
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K9.w32 (by decide) (by decide)).trans w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K9.w32 (by decide) (by decide)).trans w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K9.w32 (by decide) (by decide)).trans w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K9.w32 (by decide) (by decide)).trans w8_38
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K9.w32 (by decide) (by decide)).trans w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K9.w32 (by decide) (by decide)).trans w8_40
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K9.w32 (by decide) (by decide)).trans w8_44
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
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K9.w32 (by decide) (by decide)).trans w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K9.w32 (by decide) (by decide)).trans w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K9.w32 (by decide) (by decide)).trans w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K9.w32 (by decide) (by decide)).trans w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K9.w32 (by decide) (by decide)).trans w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K9.w32 (by decide) (by decide)).trans w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K9.w32 (by decide) (by decide)).trans w8_8c
  have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K9.w32 (by decide) (by decide)).trans w8_90
  have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K9.w32 (by decide) (by decide)).trans w8_94
  have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K9.w32 (by decide) (by decide)).trans w8_98
  have w9_9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K9.w32 (by decide) (by decide)).trans w8_9c
  have w9_a0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K9.w32 (by decide) (by decide)).trans w8_a0
  have w9_a4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K9.w32 (by decide) (by decide)).trans w8_a4
  have w9_a8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K9.w32 (by decide) (by decide)).trans w8_a8
  have w9_ac : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K9.w32 (by decide) (by decide)).trans w8_ac
  have w9_b0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K9.w32 (by decide) (by decide)).trans w8_b0
  have w9_b4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K9.w32 (by decide) (by decide)).trans w8_b4
  have w9_b8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K9.w32 (by decide) (by decide)).trans w8_b8
  have w9_bc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K9.w32 (by decide) (by decide)).trans w8_bc
  have w9_c0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K9.w32 (by decide) (by decide)).trans w8_c0
  have w9_c4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K9.w32 (by decide) (by decide)).trans w8_c4
  have w9_c8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K9.w32 (by decide) (by decide)).trans w8_c8
  have w9_cc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K9.w32 (by decide) (by decide)).trans w8_cc
  have w9_d0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K9.w32 (by decide) (by decide)).trans w8_d0
  have w9_d4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K9.w32 (by decide) (by decide)).trans w8_d4
  have w9_d8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K9.w32 (by decide) (by decide)).trans w8_d8
  have w9_dc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K9.w32 (by decide) (by decide)).trans w8_dc
  have w9_e0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K9.w32 (by decide) (by decide)).trans w8_e0
  have w9_e4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K9.w32 (by decide) (by decide)).trans w8_e4
  have w9_e8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K9.w32 (by decide) (by decide)).trans w8_e8
  have w9_ec : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K9.w32 (by decide) (by decide)).trans w8_ec
  have w9_f0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K9.w32 (by decide) (by decide)).trans w8_f0
  have w9_f4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K9.w32 (by decide) (by decide)).trans w8_f4
  have w9_f8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K9.w32 (by decide) (by decide)).trans w8_f8
  have w9_fc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K9.w32 (by decide) (by decide)).trans w8_fc
  have w9_100 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K9.w32 (by decide) (by decide)).trans w8_100
  have w9_104 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K9.w32 (by decide) (by decide)).trans w8_104
  have w9_108 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K9.w32 (by decide) (by decide)).trans w8_108
  have w9_10c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K9.w32 (by decide) (by decide)).trans w8_10c
  have w9_110 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K9.w32 (by decide) (by decide)).trans w8_110
  have w9_114 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K9.w32 (by decide) (by decide)).trans w8_114
  have w9_118 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K9.w32 (by decide) (by decide)).trans w8_118
  have w9_11c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K9.w32 (by decide) (by decide)).trans w8_11c
  have w9_120 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K9.w32 (by decide) (by decide)).trans w8_120
  have w9_124 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K9.w32 (by decide) (by decide)).trans w8_124
  have w9_128 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K9.w32 (by decide) (by decide)).trans w8_128
  have w9_12c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K9.w32 (by decide) (by decide)).trans w8_12c
  have w9_130 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K9.w32 (by decide) (by decide)).trans w8_130
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := (K9.w32 (by decide) (by decide)).trans w8_420
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := (K9.w32 (by decide) (by decide)).trans w8_424
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := (K9.w32 (by decide) (by decide)).trans w8_428
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := (K9.w32 (by decide) (by decide)).trans w8_42c
  have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K9.w32 (by decide) (by decide)).trans w8_a20
  have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K9.w32 (by decide) (by decide)).trans w8_a24
  have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K9.w32 (by decide) (by decide)).trans w8_a28
  have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K9.w32 (by decide) (by decide)).trans w8_a2c
  have w9_a30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K9.w32 (by decide) (by decide)).trans w8_a30
  have w9_a34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K9.w32 (by decide) (by decide)).trans w8_a34
  have w9_a38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K9.w32 (by decide) (by decide)).trans w8_a38
  have w9_a3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K9.w32 (by decide) (by decide)).trans w8_a3c
  have w9_aa0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K9.w32 (by decide) (by decide)).trans w8_aa0
  have w9_aa4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K9.w32 (by decide) (by decide)).trans w8_aa4
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [W9, g8_10]
  clear w8_aa4 w8_aa0 w8_a3c w8_a38 w8_a34 w8_a30 w8_a2c w8_a28 w8_a24 w8_a20 w8_42c w8_428 w8_424 w8_420 w8_130 w8_12c w8_128 w8_124 w8_120 w8_11c w8_118 w8_114 w8_110 w8_10c w8_108 w8_104 w8_100 w8_fc w8_f8 w8_f4 w8_f0 w8_ec w8_e8 w8_e4 w8_e0 w8_dc w8_d8 w8_d4 w8_d0 w8_cc w8_c8 w8_c4 w8_c0 w8_bc w8_b8 w8_b4 w8_b0 w8_ac w8_a8 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_3c w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0x2B56: branch, not taken
  obtain ⟨n10, d10, u10⟩ := s9.notTaken E9.self 0x2B5A sv_at_2b56
    (by decide) (by rw [g9_10, s9.zero]; exact br_beq_f ck_in.pos_ne)
  have s10 : St n10.mem SV n10 0x2B5A (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_10 : reg n10 a0 = ckp := by rw [u10.regs, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = dp := by rw [u10.regs, g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u10.regs, g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = dg := by rw [u10.regs, g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = ckl := by rw [u10.regs, g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, g9_27]
  have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m10]; exact w9_24
  have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m10]; exact w9_28
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m10]; exact w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m10]; exact w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m10]; exact w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m10]; exact w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m10]; exact w9_40
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m10]; exact w9_48
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
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m10]; exact w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m10]; exact w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m10]; exact w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m10]; exact w9_94
  have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m10]; exact w9_98
  have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m10]; exact w9_9c
  have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m10]; exact w9_a0
  have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m10]; exact w9_a4
  have w10_a8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m10]; exact w9_a8
  have w10_ac : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m10]; exact w9_ac
  have w10_b0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m10]; exact w9_b0
  have w10_b4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m10]; exact w9_b4
  have w10_b8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m10]; exact w9_b8
  have w10_bc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m10]; exact w9_bc
  have w10_c0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m10]; exact w9_c0
  have w10_c4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m10]; exact w9_c4
  have w10_c8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m10]; exact w9_c8
  have w10_cc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m10]; exact w9_cc
  have w10_d0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m10]; exact w9_d0
  have w10_d4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m10]; exact w9_d4
  have w10_d8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m10]; exact w9_d8
  have w10_dc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m10]; exact w9_dc
  have w10_e0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m10]; exact w9_e0
  have w10_e4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m10]; exact w9_e4
  have w10_e8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m10]; exact w9_e8
  have w10_ec : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m10]; exact w9_ec
  have w10_f0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m10]; exact w9_f0
  have w10_f4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m10]; exact w9_f4
  have w10_f8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m10]; exact w9_f8
  have w10_fc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m10]; exact w9_fc
  have w10_100 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m10]; exact w9_100
  have w10_104 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m10]; exact w9_104
  have w10_108 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m10]; exact w9_108
  have w10_10c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m10]; exact w9_10c
  have w10_110 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m10]; exact w9_110
  have w10_114 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m10]; exact w9_114
  have w10_118 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m10]; exact w9_118
  have w10_11c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m10]; exact w9_11c
  have w10_120 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m10]; exact w9_120
  have w10_124 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m10]; exact w9_124
  have w10_128 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m10]; exact w9_128
  have w10_12c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m10]; exact w9_12c
  have w10_130 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m10]; exact w9_130
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m10]; exact w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := by rw [m10]; exact w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m10]; exact w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := by rw [m10]; exact w9_42c
  have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m10]; exact w9_a20
  have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m10]; exact w9_a24
  have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m10]; exact w9_a28
  have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m10]; exact w9_a2c
  have w10_a30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m10]; exact w9_a30
  have w10_a34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m10]; exact w9_a34
  have w10_a38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m10]; exact w9_a38
  have w10_a3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m10]; exact w9_a3c
  have w10_aa0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m10]; exact w9_aa0
  have w10_aa4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m10]; exact w9_aa4
  clear w9_48 w9_aa4 w9_aa0 w9_a3c w9_a38 w9_a34 w9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_42c w9_428 w9_424 w9_420 w9_130 w9_12c w9_128 w9_124 w9_120 w9_11c w9_118 w9_114 w9_110 w9_10c w9_108 w9_104 w9_100 w9_fc w9_f8 w9_f4 w9_f0 w9_ec w9_e8 w9_e4 w9_e0 w9_dc w9_d8 w9_d4 w9_d0 w9_cc w9_c8 w9_c4 w9_c0 w9_bc w9_b8 w9_b4 w9_b0 w9_ac w9_a8 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_44 w9_40 w9_3c w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_10 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  -- 0x2B5A
  obtain ⟨n11, c11, u11⟩ := s10.block svCk12b5a E10.self svCk12b5a_end
    ⟨trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x2B5E (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svCk12b5a (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by
    rw [rb11, runBlock_reg _ _ _ sp s10.zero (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (3 : Fin 32) s10.zero (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (4 : Fin 32) s10.zero (by decide), g10_4]
  have g11_10 : reg n11 a0 = ckp := by
    rw [rb11, runBlock_reg _ _ _ a0 s10.zero (by decide), g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = dp := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = dg := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = ckl := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_13 : reg n11 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svCk12b5a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_10, g10_18, g10_19, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m11]; exact w10_24
  have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m11]; exact w10_28
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m11]; exact w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m11]; exact w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m11]; exact w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m11]; exact w10_38
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m11]; exact w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m11]; exact w10_40
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m11]; exact w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m11]; exact w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m11]; exact w10_54
  have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m11]; exact w10_58
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m11]; exact w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m11]; exact w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m11]; exact w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m11]; exact w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m11]; exact w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m11]; exact w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m11]; exact w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m11]; exact w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m11]; exact w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m11]; exact w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m11]; exact w10_8c
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m11]; exact w10_90
  have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m11]; exact w10_94
  have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m11]; exact w10_98
  have w11_9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m11]; exact w10_9c
  have w11_a0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m11]; exact w10_a0
  have w11_a4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m11]; exact w10_a4
  have w11_a8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m11]; exact w10_a8
  have w11_ac : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m11]; exact w10_ac
  have w11_b0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m11]; exact w10_b0
  have w11_b4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m11]; exact w10_b4
  have w11_b8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m11]; exact w10_b8
  have w11_bc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m11]; exact w10_bc
  have w11_c0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m11]; exact w10_c0
  have w11_c4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m11]; exact w10_c4
  have w11_c8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m11]; exact w10_c8
  have w11_cc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m11]; exact w10_cc
  have w11_d0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m11]; exact w10_d0
  have w11_d4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m11]; exact w10_d4
  have w11_d8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m11]; exact w10_d8
  have w11_dc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m11]; exact w10_dc
  have w11_e0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m11]; exact w10_e0
  have w11_e4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m11]; exact w10_e4
  have w11_e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m11]; exact w10_e8
  have w11_ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m11]; exact w10_ec
  have w11_f0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m11]; exact w10_f0
  have w11_f4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m11]; exact w10_f4
  have w11_f8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m11]; exact w10_f8
  have w11_fc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m11]; exact w10_fc
  have w11_100 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m11]; exact w10_100
  have w11_104 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m11]; exact w10_104
  have w11_108 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m11]; exact w10_108
  have w11_10c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m11]; exact w10_10c
  have w11_110 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m11]; exact w10_110
  have w11_114 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m11]; exact w10_114
  have w11_118 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m11]; exact w10_118
  have w11_11c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m11]; exact w10_11c
  have w11_120 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m11]; exact w10_120
  have w11_124 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m11]; exact w10_124
  have w11_128 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m11]; exact w10_128
  have w11_12c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m11]; exact w10_12c
  have w11_130 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m11]; exact w10_130
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := by rw [m11]; exact w10_42c
  have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m11]; exact w10_a20
  have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m11]; exact w10_a24
  have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m11]; exact w10_a28
  have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m11]; exact w10_a2c
  have w11_a30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m11]; exact w10_a30
  have w11_a34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m11]; exact w10_a34
  have w11_a38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m11]; exact w10_a38
  have w11_a3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m11]; exact w10_a3c
  have w11_aa0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m11]; exact w10_aa0
  have w11_aa4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m11]; exact w10_aa4
  clear w10_aa4 w10_aa0 w10_a3c w10_a38 w10_a34 w10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_42c w10_428 w10_424 w10_420 w10_130 w10_12c w10_128 w10_124 w10_120 w10_11c w10_118 w10_114 w10_110 w10_10c w10_108 w10_104 w10_100 w10_fc w10_f8 w10_f4 w10_f0 w10_ec w10_e8 w10_e4 w10_e0 w10_dc w10_d8 w10_d4 w10_d0 w10_cc w10_c8 w10_c4 w10_c0 w10_bc w10_b8 w10_b4 w10_b0 w10_ac w10_a8 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_10 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x2B5E: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_2b5e (off' := 0x2B60) (by decide)
    (by rw [g11_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x2B60 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_13 : reg n12 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_13]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = dp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = dg := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = ckl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_10 : reg n12 a0 = BitVec.ofNat 32 ix7 := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w11_424]
  have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m12]; exact w11_24
  have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m12]; exact w11_28
  have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m12]; exact w11_2c
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m12]; exact w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m12]; exact w11_38
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m12]; exact w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m12]; exact w11_40
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m12]; exact w11_54
  have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m12]; exact w11_58
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m12]; exact w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m12]; exact w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m12]; exact w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m12]; exact w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m12]; exact w11_8c
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m12]; exact w11_90
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m12]; exact w11_94
  have w12_98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m12]; exact w11_98
  have w12_9c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m12]; exact w11_9c
  have w12_a0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m12]; exact w11_a0
  have w12_a4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m12]; exact w11_a4
  have w12_a8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m12]; exact w11_a8
  have w12_ac : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m12]; exact w11_ac
  have w12_b0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m12]; exact w11_b0
  have w12_b4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m12]; exact w11_b4
  have w12_b8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m12]; exact w11_b8
  have w12_bc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m12]; exact w11_bc
  have w12_c0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m12]; exact w11_c0
  have w12_c4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m12]; exact w11_c4
  have w12_c8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m12]; exact w11_c8
  have w12_cc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m12]; exact w11_cc
  have w12_d0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m12]; exact w11_d0
  have w12_d4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m12]; exact w11_d4
  have w12_d8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m12]; exact w11_d8
  have w12_dc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m12]; exact w11_dc
  have w12_e0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m12]; exact w11_e0
  have w12_e4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m12]; exact w11_e4
  have w12_e8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m12]; exact w11_e8
  have w12_ec : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m12]; exact w11_ec
  have w12_f0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m12]; exact w11_f0
  have w12_f4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m12]; exact w11_f4
  have w12_f8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m12]; exact w11_f8
  have w12_fc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m12]; exact w11_fc
  have w12_100 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m12]; exact w11_100
  have w12_104 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m12]; exact w11_104
  have w12_108 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m12]; exact w11_108
  have w12_10c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m12]; exact w11_10c
  have w12_110 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m12]; exact w11_110
  have w12_114 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m12]; exact w11_114
  have w12_118 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m12]; exact w11_118
  have w12_11c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m12]; exact w11_11c
  have w12_120 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m12]; exact w11_120
  have w12_124 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m12]; exact w11_124
  have w12_128 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m12]; exact w11_128
  have w12_12c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m12]; exact w11_12c
  have w12_130 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m12]; exact w11_130
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m12]; exact w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := by rw [m12]; exact w11_42c
  have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m12]; exact w11_a20
  have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m12]; exact w11_a24
  have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m12]; exact w11_a28
  have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m12]; exact w11_a2c
  have w12_a30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m12]; exact w11_a30
  have w12_a34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m12]; exact w11_a34
  have w12_a38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m12]; exact w11_a38
  have w12_a3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m12]; exact w11_a3c
  have w12_aa0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m12]; exact w11_aa0
  have w12_aa4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m12]; exact w11_aa4
  clear w11_aa4 w11_aa0 w11_a3c w11_a38 w11_a34 w11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_42c w11_428 w11_424 w11_420 w11_130 w11_12c w11_128 w11_124 w11_120 w11_11c w11_118 w11_114 w11_110 w11_10c w11_108 w11_104 w11_100 w11_fc w11_f8 w11_f4 w11_f0 w11_ec w11_e8 w11_e4 w11_e0 w11_dc w11_d8 w11_d4 w11_d0 w11_cc w11_c8 w11_c4 w11_c0 w11_bc w11_b8 w11_b4 w11_b0 w11_ac w11_a8 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 g11_13 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x2B60: sw
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sw F E12 s12 sv_at_2b60 (off' := 0x2B62) (c := 0x44)
    (by decide) (by rw [g12_2]; sv_addr) (by decide) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 ix7 := by rw [rg13 a0, g12_10]
  have g13_13 : reg n13 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg13 a3, g12_13]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [rg13 (21 : Fin 32), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = dp := by rw [rg13 (22 : Fin 32), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg13 (23 : Fin 32), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = dg := by rw [rg13 (24 : Fin 32), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = ckl := by rw [rg13 (25 : Fin 32), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rg13 (26 : Fin 32), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg13 (27 : Fin 32), g12_27]
  have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K13.w32 (by decide) (by decide)).trans w12_24
  have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K13.w32 (by decide) (by decide)).trans w12_28
  have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K13.w32 (by decide) (by decide)).trans w12_2c
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K13.w32 (by decide) (by decide)).trans w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K13.w32 (by decide) (by decide)).trans w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K13.w32 (by decide) (by decide)).trans w12_38
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K13.w32 (by decide) (by decide)).trans w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K13.w32 (by decide) (by decide)).trans w12_40
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K13.w32 (by decide) (by decide)).trans w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K13.w32 (by decide) (by decide)).trans w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K13.w32 (by decide) (by decide)).trans w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K13.w32 (by decide) (by decide)).trans w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K13.w32 (by decide) (by decide)).trans w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K13.w32 (by decide) (by decide)).trans w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K13.w32 (by decide) (by decide)).trans w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K13.w32 (by decide) (by decide)).trans w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K13.w32 (by decide) (by decide)).trans w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K13.w32 (by decide) (by decide)).trans w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K13.w32 (by decide) (by decide)).trans w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K13.w32 (by decide) (by decide)).trans w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K13.w32 (by decide) (by decide)).trans w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K13.w32 (by decide) (by decide)).trans w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K13.w32 (by decide) (by decide)).trans w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K13.w32 (by decide) (by decide)).trans w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K13.w32 (by decide) (by decide)).trans w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K13.w32 (by decide) (by decide)).trans w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K13.w32 (by decide) (by decide)).trans w12_94
  have w13_98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K13.w32 (by decide) (by decide)).trans w12_98
  have w13_9c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K13.w32 (by decide) (by decide)).trans w12_9c
  have w13_a0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K13.w32 (by decide) (by decide)).trans w12_a0
  have w13_a4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K13.w32 (by decide) (by decide)).trans w12_a4
  have w13_a8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K13.w32 (by decide) (by decide)).trans w12_a8
  have w13_ac : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K13.w32 (by decide) (by decide)).trans w12_ac
  have w13_b0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K13.w32 (by decide) (by decide)).trans w12_b0
  have w13_b4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K13.w32 (by decide) (by decide)).trans w12_b4
  have w13_b8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K13.w32 (by decide) (by decide)).trans w12_b8
  have w13_bc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K13.w32 (by decide) (by decide)).trans w12_bc
  have w13_c0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K13.w32 (by decide) (by decide)).trans w12_c0
  have w13_c4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K13.w32 (by decide) (by decide)).trans w12_c4
  have w13_c8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K13.w32 (by decide) (by decide)).trans w12_c8
  have w13_cc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K13.w32 (by decide) (by decide)).trans w12_cc
  have w13_d0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K13.w32 (by decide) (by decide)).trans w12_d0
  have w13_d4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K13.w32 (by decide) (by decide)).trans w12_d4
  have w13_d8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K13.w32 (by decide) (by decide)).trans w12_d8
  have w13_dc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K13.w32 (by decide) (by decide)).trans w12_dc
  have w13_e0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K13.w32 (by decide) (by decide)).trans w12_e0
  have w13_e4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K13.w32 (by decide) (by decide)).trans w12_e4
  have w13_e8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K13.w32 (by decide) (by decide)).trans w12_e8
  have w13_ec : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K13.w32 (by decide) (by decide)).trans w12_ec
  have w13_f0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K13.w32 (by decide) (by decide)).trans w12_f0
  have w13_f4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K13.w32 (by decide) (by decide)).trans w12_f4
  have w13_f8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K13.w32 (by decide) (by decide)).trans w12_f8
  have w13_fc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K13.w32 (by decide) (by decide)).trans w12_fc
  have w13_100 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K13.w32 (by decide) (by decide)).trans w12_100
  have w13_104 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K13.w32 (by decide) (by decide)).trans w12_104
  have w13_108 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K13.w32 (by decide) (by decide)).trans w12_108
  have w13_10c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K13.w32 (by decide) (by decide)).trans w12_10c
  have w13_110 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K13.w32 (by decide) (by decide)).trans w12_110
  have w13_114 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K13.w32 (by decide) (by decide)).trans w12_114
  have w13_118 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K13.w32 (by decide) (by decide)).trans w12_118
  have w13_11c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K13.w32 (by decide) (by decide)).trans w12_11c
  have w13_120 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K13.w32 (by decide) (by decide)).trans w12_120
  have w13_124 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K13.w32 (by decide) (by decide)).trans w12_124
  have w13_128 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K13.w32 (by decide) (by decide)).trans w12_128
  have w13_12c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K13.w32 (by decide) (by decide)).trans w12_12c
  have w13_130 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K13.w32 (by decide) (by decide)).trans w12_130
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := (K13.w32 (by decide) (by decide)).trans w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := (K13.w32 (by decide) (by decide)).trans w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := (K13.w32 (by decide) (by decide)).trans w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := (K13.w32 (by decide) (by decide)).trans w12_42c
  have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K13.w32 (by decide) (by decide)).trans w12_a20
  have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K13.w32 (by decide) (by decide)).trans w12_a24
  have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K13.w32 (by decide) (by decide)).trans w12_a28
  have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K13.w32 (by decide) (by decide)).trans w12_a2c
  have w13_a30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K13.w32 (by decide) (by decide)).trans w12_a30
  have w13_a34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K13.w32 (by decide) (by decide)).trans w12_a34
  have w13_a38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K13.w32 (by decide) (by decide)).trans w12_a38
  have w13_a3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K13.w32 (by decide) (by decide)).trans w12_a3c
  have w13_aa0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K13.w32 (by decide) (by decide)).trans w12_aa0
  have w13_aa4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K13.w32 (by decide) (by decide)).trans w12_aa4
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [W13, g12_10]
  clear w12_aa4 w12_aa0 w12_a3c w12_a38 w12_a34 w12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_42c w12_428 w12_424 w12_420 w12_130 w12_12c w12_128 w12_124 w12_120 w12_11c w12_118 w12_114 w12_110 w12_10c w12_108 w12_104 w12_100 w12_fc w12_f8 w12_f4 w12_f0 w12_ec w12_e8 w12_e4 w12_e0 w12_dc w12_d8 w12_d4 w12_d0 w12_cc w12_c8 w12_c4 w12_c0 w12_bc w12_b8 w12_b4 w12_b0 w12_ac w12_a8 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_3c w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_13 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x2B62: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_2b62 (off' := 0x2B64) (by decide)
    (by rw [g13_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0x2B64 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 ix7 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_10]
  have g14_13 : reg n14 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_13]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = dp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = dg := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = ckl := by rw [u14.regs, upd_ne (by decide) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
  have g14_11 : reg n14 a1 = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w13_428]
  have w14_24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m14]; exact w13_24
  have w14_28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m14]; exact w13_28
  have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m14]; exact w13_2c
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m14]; exact w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m14]; exact w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m14]; exact w13_38
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m14]; exact w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m14]; exact w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m14]; exact w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m14]; exact w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m14]; exact w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m14]; exact w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m14]; exact w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m14]; exact w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m14]; exact w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m14]; exact w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m14]; exact w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m14]; exact w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m14]; exact w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m14]; exact w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m14]; exact w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m14]; exact w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m14]; exact w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m14]; exact w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m14]; exact w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m14]; exact w13_94
  have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m14]; exact w13_98
  have w14_9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m14]; exact w13_9c
  have w14_a0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m14]; exact w13_a0
  have w14_a4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m14]; exact w13_a4
  have w14_a8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m14]; exact w13_a8
  have w14_ac : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m14]; exact w13_ac
  have w14_b0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m14]; exact w13_b0
  have w14_b4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m14]; exact w13_b4
  have w14_b8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m14]; exact w13_b8
  have w14_bc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m14]; exact w13_bc
  have w14_c0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m14]; exact w13_c0
  have w14_c4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m14]; exact w13_c4
  have w14_c8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m14]; exact w13_c8
  have w14_cc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m14]; exact w13_cc
  have w14_d0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m14]; exact w13_d0
  have w14_d4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m14]; exact w13_d4
  have w14_d8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m14]; exact w13_d8
  have w14_dc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m14]; exact w13_dc
  have w14_e0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m14]; exact w13_e0
  have w14_e4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m14]; exact w13_e4
  have w14_e8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m14]; exact w13_e8
  have w14_ec : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m14]; exact w13_ec
  have w14_f0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m14]; exact w13_f0
  have w14_f4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m14]; exact w13_f4
  have w14_f8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m14]; exact w13_f8
  have w14_fc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m14]; exact w13_fc
  have w14_100 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m14]; exact w13_100
  have w14_104 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m14]; exact w13_104
  have w14_108 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m14]; exact w13_108
  have w14_10c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m14]; exact w13_10c
  have w14_110 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m14]; exact w13_110
  have w14_114 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m14]; exact w13_114
  have w14_118 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m14]; exact w13_118
  have w14_11c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m14]; exact w13_11c
  have w14_120 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m14]; exact w13_120
  have w14_124 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m14]; exact w13_124
  have w14_128 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m14]; exact w13_128
  have w14_12c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m14]; exact w13_12c
  have w14_130 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m14]; exact w13_130
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := by rw [m14]; exact w13_42c
  have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m14]; exact w13_a20
  have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m14]; exact w13_a24
  have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m14]; exact w13_a28
  have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m14]; exact w13_a2c
  have w14_a30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m14]; exact w13_a30
  have w14_a34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m14]; exact w13_a34
  have w14_a38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m14]; exact w13_a38
  have w14_a3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m14]; exact w13_a3c
  have w14_aa0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m14]; exact w13_aa0
  have w14_aa4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m14]; exact w13_aa4
  clear w13_44 w13_aa4 w13_aa0 w13_a3c w13_a38 w13_a34 w13_a30 w13_a2c w13_a28 w13_a24 w13_a20 w13_42c w13_428 w13_424 w13_420 w13_130 w13_12c w13_128 w13_124 w13_120 w13_11c w13_118 w13_114 w13_110 w13_10c w13_108 w13_104 w13_100 w13_fc w13_f8 w13_f4 w13_f0 w13_ec w13_e8 w13_e4 w13_e0 w13_dc w13_d8 w13_d4 w13_d0 w13_cc w13_c8 w13_c4 w13_c0 w13_bc w13_b8 w13_b4 w13_b0 w13_ac w13_a8 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_40 w13_3c w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_13 g13_10 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0x2B64: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_2b64 (off' := 0x2B66) (by decide)
    (by rw [g14_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x2B66 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 ix7 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_10]
  have g15_11 : reg n15 a1 = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_11]
  have g15_13 : reg n15 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_13]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = dp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = dg := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = ckl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_12 : reg n15 a2 = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_13, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w14_42c]
  have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m15]; exact w14_24
  have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m15]; exact w14_28
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m15]; exact w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m15]; exact w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m15]; exact w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m15]; exact w14_38
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m15]; exact w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m15]; exact w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m15]; exact w14_48
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
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m15]; exact w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m15]; exact w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m15]; exact w14_8c
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m15]; exact w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m15]; exact w14_94
  have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m15]; exact w14_98
  have w15_9c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m15]; exact w14_9c
  have w15_a0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m15]; exact w14_a0
  have w15_a4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m15]; exact w14_a4
  have w15_a8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m15]; exact w14_a8
  have w15_ac : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m15]; exact w14_ac
  have w15_b0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m15]; exact w14_b0
  have w15_b4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m15]; exact w14_b4
  have w15_b8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m15]; exact w14_b8
  have w15_bc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m15]; exact w14_bc
  have w15_c0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m15]; exact w14_c0
  have w15_c4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m15]; exact w14_c4
  have w15_c8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m15]; exact w14_c8
  have w15_cc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m15]; exact w14_cc
  have w15_d0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m15]; exact w14_d0
  have w15_d4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m15]; exact w14_d4
  have w15_d8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m15]; exact w14_d8
  have w15_dc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m15]; exact w14_dc
  have w15_e0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m15]; exact w14_e0
  have w15_e4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m15]; exact w14_e4
  have w15_e8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m15]; exact w14_e8
  have w15_ec : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m15]; exact w14_ec
  have w15_f0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m15]; exact w14_f0
  have w15_f4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m15]; exact w14_f4
  have w15_f8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m15]; exact w14_f8
  have w15_fc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m15]; exact w14_fc
  have w15_100 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m15]; exact w14_100
  have w15_104 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m15]; exact w14_104
  have w15_108 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m15]; exact w14_108
  have w15_10c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m15]; exact w14_10c
  have w15_110 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m15]; exact w14_110
  have w15_114 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m15]; exact w14_114
  have w15_118 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m15]; exact w14_118
  have w15_11c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m15]; exact w14_11c
  have w15_120 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m15]; exact w14_120
  have w15_124 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m15]; exact w14_124
  have w15_128 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m15]; exact w14_128
  have w15_12c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m15]; exact w14_12c
  have w15_130 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m15]; exact w14_130
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m15]; exact w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := by rw [m15]; exact w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m15]; exact w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := by rw [m15]; exact w14_42c
  have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m15]; exact w14_a20
  have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m15]; exact w14_a24
  have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m15]; exact w14_a28
  have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m15]; exact w14_a2c
  have w15_a30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m15]; exact w14_a30
  have w15_a34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m15]; exact w14_a34
  have w15_a38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m15]; exact w14_a38
  have w15_a3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m15]; exact w14_a3c
  have w15_aa0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m15]; exact w14_aa0
  have w15_aa4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m15]; exact w14_aa4
  clear w14_aa4 w14_aa0 w14_a3c w14_a38 w14_a34 w14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_42c w14_428 w14_424 w14_420 w14_130 w14_12c w14_128 w14_124 w14_120 w14_11c w14_118 w14_114 w14_110 w14_10c w14_108 w14_104 w14_100 w14_fc w14_f8 w14_f4 w14_f0 w14_ec w14_e8 w14_e4 w14_e0 w14_dc w14_d8 w14_d4 w14_d0 w14_cc w14_c8 w14_c4 w14_c0 w14_bc w14_b8 w14_b4 w14_b0 w14_ac w14_a8 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 g14_11 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_13 g14_10 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x2B66
  obtain ⟨n16, c16, u16⟩ := s15.block svCk12b66 E15.self svCk12b66_end
    ⟨trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x2B6A (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svCk12b66 (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
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
  have g16_11 : reg n16 a1 = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by
    rw [rb16, runBlock_reg _ _ _ a1 s15.zero (by decide), g15_11]
  have g16_12 : reg n16 a2 = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := by
    rw [rb16, runBlock_reg _ _ _ a2 s15.zero (by decide), g15_12]
  have g16_13 : reg n16 a3 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb16, runBlock_reg _ _ _ a3 s15.zero (by decide), g15_13]
  have g16_18 : reg n16 (18 : Fin 32) = out := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by
    rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by
    rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = dp := by
    rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = dg := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = ckl := by
    rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
  have g16_10 : reg n16 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svCk12b66, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_10, g15_11, g15_12, g15_13, g15_18, g15_19, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w16_24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m16]; exact w15_24
  have w16_28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m16]; exact w15_28
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m16]; exact w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m16]; exact w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m16]; exact w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m16]; exact w15_38
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m16]; exact w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m16]; exact w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m16]; exact w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m16]; exact w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m16]; exact w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m16]; exact w15_54
  have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m16]; exact w15_58
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m16]; exact w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m16]; exact w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m16]; exact w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m16]; exact w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m16]; exact w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m16]; exact w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m16]; exact w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m16]; exact w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m16]; exact w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m16]; exact w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m16]; exact w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m16]; exact w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m16]; exact w15_8c
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m16]; exact w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m16]; exact w15_94
  have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m16]; exact w15_98
  have w16_9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m16]; exact w15_9c
  have w16_a0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m16]; exact w15_a0
  have w16_a4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m16]; exact w15_a4
  have w16_a8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m16]; exact w15_a8
  have w16_ac : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m16]; exact w15_ac
  have w16_b0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m16]; exact w15_b0
  have w16_b4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m16]; exact w15_b4
  have w16_b8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m16]; exact w15_b8
  have w16_bc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m16]; exact w15_bc
  have w16_c0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m16]; exact w15_c0
  have w16_c4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m16]; exact w15_c4
  have w16_c8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m16]; exact w15_c8
  have w16_cc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m16]; exact w15_cc
  have w16_d0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m16]; exact w15_d0
  have w16_d4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m16]; exact w15_d4
  have w16_d8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m16]; exact w15_d8
  have w16_dc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m16]; exact w15_dc
  have w16_e0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m16]; exact w15_e0
  have w16_e4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m16]; exact w15_e4
  have w16_e8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m16]; exact w15_e8
  have w16_ec : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m16]; exact w15_ec
  have w16_f0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m16]; exact w15_f0
  have w16_f4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m16]; exact w15_f4
  have w16_f8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m16]; exact w15_f8
  have w16_fc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m16]; exact w15_fc
  have w16_100 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m16]; exact w15_100
  have w16_104 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m16]; exact w15_104
  have w16_108 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m16]; exact w15_108
  have w16_10c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m16]; exact w15_10c
  have w16_110 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m16]; exact w15_110
  have w16_114 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m16]; exact w15_114
  have w16_118 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m16]; exact w15_118
  have w16_11c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m16]; exact w15_11c
  have w16_120 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m16]; exact w15_120
  have w16_124 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m16]; exact w15_124
  have w16_128 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m16]; exact w15_128
  have w16_12c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m16]; exact w15_12c
  have w16_130 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m16]; exact w15_130
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ckp := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix7 := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((ckl).toNat) - BitVec.ofNat 32 (ix7 + 1) := by rw [m16]; exact w15_42c
  have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m16]; exact w15_a20
  have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m16]; exact w15_a24
  have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m16]; exact w15_a28
  have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m16]; exact w15_a2c
  have w16_a30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m16]; exact w15_a30
  have w16_a34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m16]; exact w15_a34
  have w16_a38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m16]; exact w15_a38
  have w16_a3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m16]; exact w15_a3c
  have w16_aa0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m16]; exact w15_aa0
  have w16_aa4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m16]; exact w15_aa4
  clear w15_aa4 w15_aa0 w15_a3c w15_a38 w15_a34 w15_a30 w15_a2c w15_a28 w15_a24 w15_a20 w15_42c w15_428 w15_424 w15_420 w15_130 w15_12c w15_128 w15_124 w15_120 w15_11c w15_118 w15_114 w15_110 w15_10c w15_108 w15_104 w15_100 w15_fc w15_f8 w15_f4 w15_f0 w15_ec w15_e8 w15_e4 w15_e0 w15_dc w15_d8 w15_d4 w15_d0 w15_cc w15_c8 w15_c4 w15_c0 w15_bc w15_b8 w15_b4 w15_b0 w15_ac w15_a8 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_38 w15_34 w15_30 w15_2c w15_28 w15_24 g15_12 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_13 g15_11 g15_10 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x2B6A: sv_lineF
  obtain ⟨n17, c17, s17, rk17, K17, L17, fr17⟩ := sv_lineF (oc := 0x420) (nl := ((ckl).toNat) - (ix7 + 1))
    F E16 (CK0.sv F fR16) s16 sv_at_2b6a sv_at_2b6e (by decide) (by decide)
    g16_10 g16_11 (by rw [g16_12, sub_ofNat (Nat.succ_le_of_lt hix7) (by omega)]) (by decide) (by decide) (line_rest (.inl ck_in) hix7)
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keepL K17 (by decide)
  rw [nlScan_ro F fR16 (line_rest (.inl ck_in) hix7)] at L17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rk17 sp (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk17 (3 : Fin 32) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk17 (4 : Fin 32) (by decide), g16_4]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rk17 (18 : Fin 32) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rk17 (19 : Fin 32) (by decide), g16_19]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [rk17 (21 : Fin 32) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = dp := by rw [rk17 (22 : Fin 32) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rk17 (23 : Fin 32) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = dg := by rw [rk17 (24 : Fin 32) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = ckl := by rw [rk17 (25 : Fin 32) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [rk17 (26 : Fin 32) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk17 (27 : Fin 32) (by decide), g16_27]
  obtain ⟨r17, hr17⟩ : ∃ r, nlScan M0 ((ckp) + BitVec.ofNat 32 (ix7 + 1)) 0 (((ckl).toNat) - (ix7 + 1)) = r := ⟨_, rfl⟩
  rcases r17 with _ | ix17
  · rw [hr17] at L17
    obtain ⟨z0_17, z4_17⟩ := L17
    have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K17.w32 (by decide) (by decide)).trans w16_24
    have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K17.w32 (by decide) (by decide)).trans w16_28
    have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K17.w32 (by decide) (by decide)).trans w16_2c
    have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K17.w32 (by decide) (by decide)).trans w16_30
    have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K17.w32 (by decide) (by decide)).trans w16_34
    have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K17.w32 (by decide) (by decide)).trans w16_38
    have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K17.w32 (by decide) (by decide)).trans w16_3c
    have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K17.w32 (by decide) (by decide)).trans w16_40
    have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := (K17.w32 (by decide) (by decide)).trans w16_44
    have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K17.w32 (by decide) (by decide)).trans w16_48
    have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K17.w32 (by decide) (by decide)).trans w16_4c
    have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K17.w32 (by decide) (by decide)).trans w16_50
    have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K17.w32 (by decide) (by decide)).trans w16_54
    have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K17.w32 (by decide) (by decide)).trans w16_58
    have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K17.w32 (by decide) (by decide)).trans w16_5c
    have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K17.w32 (by decide) (by decide)).trans w16_60
    have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K17.w32 (by decide) (by decide)).trans w16_64
    have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K17.w32 (by decide) (by decide)).trans w16_68
    have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K17.w32 (by decide) (by decide)).trans w16_6c
    have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K17.w32 (by decide) (by decide)).trans w16_70
    have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K17.w32 (by decide) (by decide)).trans w16_74
    have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K17.w32 (by decide) (by decide)).trans w16_78
    have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K17.w32 (by decide) (by decide)).trans w16_7c
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K17.w32 (by decide) (by decide)).trans w16_80
    have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K17.w32 (by decide) (by decide)).trans w16_84
    have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K17.w32 (by decide) (by decide)).trans w16_88
    have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K17.w32 (by decide) (by decide)).trans w16_8c
    have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K17.w32 (by decide) (by decide)).trans w16_90
    have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K17.w32 (by decide) (by decide)).trans w16_94
    have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K17.w32 (by decide) (by decide)).trans w16_98
    have w17_9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K17.w32 (by decide) (by decide)).trans w16_9c
    have w17_a0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K17.w32 (by decide) (by decide)).trans w16_a0
    have w17_a4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K17.w32 (by decide) (by decide)).trans w16_a4
    have w17_a8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K17.w32 (by decide) (by decide)).trans w16_a8
    have w17_ac : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K17.w32 (by decide) (by decide)).trans w16_ac
    have w17_b0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K17.w32 (by decide) (by decide)).trans w16_b0
    have w17_b4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K17.w32 (by decide) (by decide)).trans w16_b4
    have w17_b8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K17.w32 (by decide) (by decide)).trans w16_b8
    have w17_bc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K17.w32 (by decide) (by decide)).trans w16_bc
    have w17_c0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K17.w32 (by decide) (by decide)).trans w16_c0
    have w17_c4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K17.w32 (by decide) (by decide)).trans w16_c4
    have w17_c8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K17.w32 (by decide) (by decide)).trans w16_c8
    have w17_cc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K17.w32 (by decide) (by decide)).trans w16_cc
    have w17_d0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K17.w32 (by decide) (by decide)).trans w16_d0
    have w17_d4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K17.w32 (by decide) (by decide)).trans w16_d4
    have w17_d8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K17.w32 (by decide) (by decide)).trans w16_d8
    have w17_dc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K17.w32 (by decide) (by decide)).trans w16_dc
    have w17_e0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K17.w32 (by decide) (by decide)).trans w16_e0
    have w17_e4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K17.w32 (by decide) (by decide)).trans w16_e4
    have w17_e8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K17.w32 (by decide) (by decide)).trans w16_e8
    have w17_ec : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K17.w32 (by decide) (by decide)).trans w16_ec
    have w17_f0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K17.w32 (by decide) (by decide)).trans w16_f0
    have w17_f4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K17.w32 (by decide) (by decide)).trans w16_f4
    have w17_f8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K17.w32 (by decide) (by decide)).trans w16_f8
    have w17_fc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K17.w32 (by decide) (by decide)).trans w16_fc
    have w17_100 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K17.w32 (by decide) (by decide)).trans w16_100
    have w17_104 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K17.w32 (by decide) (by decide)).trans w16_104
    have w17_108 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K17.w32 (by decide) (by decide)).trans w16_108
    have w17_10c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K17.w32 (by decide) (by decide)).trans w16_10c
    have w17_110 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K17.w32 (by decide) (by decide)).trans w16_110
    have w17_114 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K17.w32 (by decide) (by decide)).trans w16_114
    have w17_118 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K17.w32 (by decide) (by decide)).trans w16_118
    have w17_11c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K17.w32 (by decide) (by decide)).trans w16_11c
    have w17_120 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K17.w32 (by decide) (by decide)).trans w16_120
    have w17_124 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K17.w32 (by decide) (by decide)).trans w16_124
    have w17_128 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K17.w32 (by decide) (by decide)).trans w16_128
    have w17_12c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K17.w32 (by decide) (by decide)).trans w16_12c
    have w17_130 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K17.w32 (by decide) (by decide)).trans w16_130
    have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K17.w32 (by decide) (by decide)).trans w16_a20
    have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K17.w32 (by decide) (by decide)).trans w16_a24
    have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K17.w32 (by decide) (by decide)).trans w16_a28
    have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K17.w32 (by decide) (by decide)).trans w16_a2c
    have w17_a30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K17.w32 (by decide) (by decide)).trans w16_a30
    have w17_a34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K17.w32 (by decide) (by decide)).trans w16_a34
    have w17_a38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K17.w32 (by decide) (by decide)).trans w16_a38
    have w17_a3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K17.w32 (by decide) (by decide)).trans w16_a3c
    have w17_aa0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K17.w32 (by decide) (by decide)).trans w16_aa0
    have w17_aa4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K17.w32 (by decide) (by decide)).trans w16_aa4
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z0_17
    have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := z4_17
    clear w16_aa4 w16_aa0 w16_a3c w16_a38 w16_a34 w16_a30 w16_a2c w16_a28 w16_a24 w16_a20 w16_42c w16_428 w16_424 w16_420 w16_130 w16_12c w16_128 w16_124 w16_120 w16_11c w16_118 w16_114 w16_110 w16_10c w16_108 w16_104 w16_100 w16_fc w16_f8 w16_f4 w16_f0 w16_ec w16_e8 w16_e4 w16_e0 w16_dc w16_d8 w16_d4 w16_d0 w16_cc w16_c8 w16_c4 w16_c0 w16_bc w16_b8 w16_b4 w16_b0 w16_ac w16_a8 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_13 g16_12 g16_11 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
    -- 0x2B72: lw
    obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_2b72 (off' := 0x2B76) (by decide)
      (by rw [g17_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s18 : St n18.mem SV n18 0x2B76 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
    have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = dp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = dg := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = ckl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
    have g18_9 : reg n18 (9 : Fin 32) = 0 := by
      rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g17_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w17_420]
    have w18_24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m18]; exact w17_24
    have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m18]; exact w17_28
    have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m18]; exact w17_2c
    have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m18]; exact w17_30
    have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m18]; exact w17_34
    have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m18]; exact w17_38
    have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m18]; exact w17_3c
    have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m18]; exact w17_40
    have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m18]; exact w17_44
    have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m18]; exact w17_48
    have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m18]; exact w17_4c
    have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
    have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m18]; exact w17_54
    have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m18]; exact w17_58
    have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m18]; exact w17_5c
    have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m18]; exact w17_60
    have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
    have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
    have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
    have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
    have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m18]; exact w17_74
    have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m18]; exact w17_78
    have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m18]; exact w17_7c
    have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m18]; exact w17_80
    have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m18]; exact w17_84
    have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m18]; exact w17_88
    have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m18]; exact w17_8c
    have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m18]; exact w17_90
    have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m18]; exact w17_94
    have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m18]; exact w17_98
    have w18_9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m18]; exact w17_9c
    have w18_a0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m18]; exact w17_a0
    have w18_a4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m18]; exact w17_a4
    have w18_a8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m18]; exact w17_a8
    have w18_ac : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m18]; exact w17_ac
    have w18_b0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m18]; exact w17_b0
    have w18_b4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m18]; exact w17_b4
    have w18_b8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m18]; exact w17_b8
    have w18_bc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m18]; exact w17_bc
    have w18_c0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m18]; exact w17_c0
    have w18_c4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m18]; exact w17_c4
    have w18_c8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m18]; exact w17_c8
    have w18_cc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m18]; exact w17_cc
    have w18_d0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m18]; exact w17_d0
    have w18_d4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m18]; exact w17_d4
    have w18_d8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m18]; exact w17_d8
    have w18_dc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m18]; exact w17_dc
    have w18_e0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m18]; exact w17_e0
    have w18_e4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m18]; exact w17_e4
    have w18_e8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m18]; exact w17_e8
    have w18_ec : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m18]; exact w17_ec
    have w18_f0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m18]; exact w17_f0
    have w18_f4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m18]; exact w17_f4
    have w18_f8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m18]; exact w17_f8
    have w18_fc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m18]; exact w17_fc
    have w18_100 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m18]; exact w17_100
    have w18_104 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m18]; exact w17_104
    have w18_108 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m18]; exact w17_108
    have w18_10c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m18]; exact w17_10c
    have w18_110 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m18]; exact w17_110
    have w18_114 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m18]; exact w17_114
    have w18_118 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m18]; exact w17_118
    have w18_11c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m18]; exact w17_11c
    have w18_120 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m18]; exact w17_120
    have w18_124 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m18]; exact w17_124
    have w18_128 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m18]; exact w17_128
    have w18_12c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m18]; exact w17_12c
    have w18_130 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m18]; exact w17_130
    have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m18]; exact w17_420
    have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m18]; exact w17_a20
    have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m18]; exact w17_a24
    have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m18]; exact w17_a28
    have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m18]; exact w17_a2c
    have w18_a30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m18]; exact w17_a30
    have w18_a34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m18]; exact w17_a34
    have w18_a38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m18]; exact w17_a38
    have w18_a3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m18]; exact w17_a3c
    have w18_aa0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m18]; exact w17_aa0
    have w18_aa4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m18]; exact w17_aa4
    have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m18]; exact b17_424
    clear b17_424 w17_420 w17_aa4 w17_aa0 w17_a3c w17_a38 w17_a34 w17_a30 w17_a2c w17_a28 w17_a24 w17_a20 w17_130 w17_12c w17_128 w17_124 w17_120 w17_11c w17_118 w17_114 w17_110 w17_10c w17_108 w17_104 w17_100 w17_fc w17_f8 w17_f4 w17_f0 w17_ec w17_e8 w17_e4 w17_e0 w17_dc w17_d8 w17_d4 w17_d0 w17_cc w17_c8 w17_c4 w17_c0 w17_bc w17_b8 w17_b4 w17_b0 w17_ac w17_a8 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 z4_17 z0_17
    -- 0x2B76: branch, taken
    obtain ⟨n19, d19, u19⟩ := s18.taken E18.self 0x2FEA sv_at_2b76
      (by decide) (by rw [g18_9, s18.zero]; rfl)
    have s19 : St n19.mem SV n19 0x2FEA (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
    have g19_9 : reg n19 (9 : Fin 32) = 0 := by rw [u19.regs, g18_9]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
    have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = dp := by rw [u19.regs, g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u19.regs, g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = dg := by rw [u19.regs, g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = ckl := by rw [u19.regs, g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u19.regs, g18_27]
    have w19_24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m19]; exact w18_24
    have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m19]; exact w18_28
    have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m19]; exact w18_2c
    have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m19]; exact w18_30
    have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m19]; exact w18_34
    have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m19]; exact w18_38
    have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m19]; exact w18_3c
    have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m19]; exact w18_40
    have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m19]; exact w18_44
    have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m19]; exact w18_48
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
    have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m19]; exact w18_74
    have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m19]; exact w18_78
    have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m19]; exact w18_7c
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m19]; exact w18_80
    have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m19]; exact w18_84
    have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m19]; exact w18_88
    have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m19]; exact w18_8c
    have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m19]; exact w18_90
    have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m19]; exact w18_94
    have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m19]; exact w18_98
    have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m19]; exact w18_9c
    have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m19]; exact w18_a0
    have w19_a4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m19]; exact w18_a4
    have w19_a8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m19]; exact w18_a8
    have w19_ac : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m19]; exact w18_ac
    have w19_b0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m19]; exact w18_b0
    have w19_b4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m19]; exact w18_b4
    have w19_b8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m19]; exact w18_b8
    have w19_bc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m19]; exact w18_bc
    have w19_c0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m19]; exact w18_c0
    have w19_c4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m19]; exact w18_c4
    have w19_c8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m19]; exact w18_c8
    have w19_cc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m19]; exact w18_cc
    have w19_d0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m19]; exact w18_d0
    have w19_d4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m19]; exact w18_d4
    have w19_d8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m19]; exact w18_d8
    have w19_dc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m19]; exact w18_dc
    have w19_e0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m19]; exact w18_e0
    have w19_e4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m19]; exact w18_e4
    have w19_e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m19]; exact w18_e8
    have w19_ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m19]; exact w18_ec
    have w19_f0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m19]; exact w18_f0
    have w19_f4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m19]; exact w18_f4
    have w19_f8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m19]; exact w18_f8
    have w19_fc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m19]; exact w18_fc
    have w19_100 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m19]; exact w18_100
    have w19_104 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m19]; exact w18_104
    have w19_108 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m19]; exact w18_108
    have w19_10c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m19]; exact w18_10c
    have w19_110 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m19]; exact w18_110
    have w19_114 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m19]; exact w18_114
    have w19_118 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m19]; exact w18_118
    have w19_11c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m19]; exact w18_11c
    have w19_120 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m19]; exact w18_120
    have w19_124 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m19]; exact w18_124
    have w19_128 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m19]; exact w18_128
    have w19_12c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m19]; exact w18_12c
    have w19_130 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m19]; exact w18_130
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m19]; exact w18_420
    have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m19]; exact w18_a20
    have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m19]; exact w18_a24
    have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m19]; exact w18_a28
    have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m19]; exact w18_a2c
    have w19_a30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m19]; exact w18_a30
    have w19_a34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m19]; exact w18_a34
    have w19_a38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m19]; exact w18_a38
    have w19_a3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m19]; exact w18_a3c
    have w19_aa0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m19]; exact w18_aa0
    have w19_aa4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m19]; exact w18_aa4
    have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m19]; exact b18_424
    clear b18_424 w18_aa4 w18_aa0 w18_a3c w18_a38 w18_a34 w18_a30 w18_a2c w18_a28 w18_a24 w18_a20 w18_420 w18_130 w18_12c w18_128 w18_124 w18_120 w18_11c w18_118 w18_114 w18_110 w18_10c w18_108 w18_104 w18_100 w18_fc w18_f8 w18_f4 w18_f0 w18_ec w18_e8 w18_e4 w18_e0 w18_dc w18_d8 w18_d4 w18_d0 w18_cc w18_c8 w18_c4 w18_c0 w18_bc w18_b8 w18_b4 w18_b0 w18_ac w18_a8 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 g18_9 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    -- 0x2FEA: lbu
    obtain ⟨n20, d20, u20⟩ := s19.lbu E19.self sv_at_2fea (off' := 0x2FEE) (by decide)
    have s20 : St n20.mem SV n20 0x2FEE (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
    have g20_9 : reg n20 (9 : Fin 32) = 0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_9]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = dp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = dg := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = ckl := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
    have w20_24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m20]; exact w19_24
    have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m20]; exact w19_28
    have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m20]; exact w19_2c
    have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m20]; exact w19_30
    have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m20]; exact w19_34
    have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m20]; exact w19_38
    have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m20]; exact w19_3c
    have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m20]; exact w19_40
    have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m20]; exact w19_44
    have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m20]; exact w19_48
    have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
    have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
    have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m20]; exact w19_54
    have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m20]; exact w19_58
    have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m20]; exact w19_5c
    have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m20]; exact w19_60
    have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m20]; exact w19_64
    have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m20]; exact w19_68
    have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m20]; exact w19_6c
    have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m20]; exact w19_70
    have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m20]; exact w19_74
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m20]; exact w19_78
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m20]; exact w19_7c
    have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m20]; exact w19_80
    have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m20]; exact w19_84
    have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m20]; exact w19_88
    have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m20]; exact w19_8c
    have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m20]; exact w19_90
    have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m20]; exact w19_94
    have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m20]; exact w19_98
    have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m20]; exact w19_9c
    have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m20]; exact w19_a0
    have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m20]; exact w19_a4
    have w20_a8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m20]; exact w19_a8
    have w20_ac : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m20]; exact w19_ac
    have w20_b0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m20]; exact w19_b0
    have w20_b4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m20]; exact w19_b4
    have w20_b8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m20]; exact w19_b8
    have w20_bc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m20]; exact w19_bc
    have w20_c0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m20]; exact w19_c0
    have w20_c4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m20]; exact w19_c4
    have w20_c8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m20]; exact w19_c8
    have w20_cc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m20]; exact w19_cc
    have w20_d0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m20]; exact w19_d0
    have w20_d4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m20]; exact w19_d4
    have w20_d8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m20]; exact w19_d8
    have w20_dc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m20]; exact w19_dc
    have w20_e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m20]; exact w19_e0
    have w20_e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m20]; exact w19_e4
    have w20_e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m20]; exact w19_e8
    have w20_ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m20]; exact w19_ec
    have w20_f0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m20]; exact w19_f0
    have w20_f4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m20]; exact w19_f4
    have w20_f8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m20]; exact w19_f8
    have w20_fc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m20]; exact w19_fc
    have w20_100 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m20]; exact w19_100
    have w20_104 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m20]; exact w19_104
    have w20_108 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m20]; exact w19_108
    have w20_10c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m20]; exact w19_10c
    have w20_110 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m20]; exact w19_110
    have w20_114 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m20]; exact w19_114
    have w20_118 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m20]; exact w19_118
    have w20_11c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m20]; exact w19_11c
    have w20_120 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m20]; exact w19_120
    have w20_124 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m20]; exact w19_124
    have w20_128 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m20]; exact w19_128
    have w20_12c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m20]; exact w19_12c
    have w20_130 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m20]; exact w19_130
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m20]; exact w19_420
    have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m20]; exact w19_a20
    have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m20]; exact w19_a24
    have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m20]; exact w19_a28
    have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m20]; exact w19_a2c
    have w20_a30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m20]; exact w19_a30
    have w20_a34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m20]; exact w19_a34
    have w20_a38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m20]; exact w19_a38
    have w20_a3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m20]; exact w19_a3c
    have w20_aa0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m20]; exact w19_aa0
    have w20_aa4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m20]; exact w19_aa4
    have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m20]; exact b19_424
    clear b19_424 w19_aa4 w19_aa0 w19_a3c w19_a38 w19_a34 w19_a30 w19_a2c w19_a28 w19_a24 w19_a20 w19_420 w19_130 w19_12c w19_128 w19_124 w19_120 w19_11c w19_118 w19_114 w19_110 w19_10c w19_108 w19_104 w19_100 w19_fc w19_f8 w19_f4 w19_f0 w19_ec w19_e8 w19_e4 w19_e0 w19_dc w19_d8 w19_d4 w19_d0 w19_cc w19_c8 w19_c4 w19_c0 w19_bc w19_b8 w19_b4 w19_b0 w19_ac w19_a8 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_19 g19_18 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
    -- 0x2FEE: j
    obtain ⟨n21, d21, u21⟩ := s20.jump E20.self sv_at_2fee (off' := 0x966) (by decide)
      (by rw [s20.pc]; decide)
    have s21 : St n21.mem SV n21 0x966 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
    have g21_9 : reg n21 (9 : Fin 32) = 0 := by rw [u21.regs, g20_9]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = dp := by rw [u21.regs, g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u21.regs, g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = dg := by rw [u21.regs, g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = ckl := by rw [u21.regs, g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u21.regs, g20_27]
    have w21_24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m21]; exact w20_24
    have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m21]; exact w20_28
    have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m21]; exact w20_2c
    have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m21]; exact w20_30
    have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m21]; exact w20_34
    have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m21]; exact w20_38
    have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m21]; exact w20_3c
    have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m21]; exact w20_40
    have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m21]; exact w20_44
    have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m21]; exact w20_48
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
    have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m21]; exact w20_74
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m21]; exact w20_78
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m21]; exact w20_7c
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m21]; exact w20_80
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m21]; exact w20_84
    have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m21]; exact w20_88
    have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m21]; exact w20_8c
    have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m21]; exact w20_90
    have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m21]; exact w20_94
    have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m21]; exact w20_98
    have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m21]; exact w20_9c
    have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m21]; exact w20_a0
    have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m21]; exact w20_a4
    have w21_a8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m21]; exact w20_a8
    have w21_ac : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m21]; exact w20_ac
    have w21_b0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m21]; exact w20_b0
    have w21_b4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m21]; exact w20_b4
    have w21_b8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m21]; exact w20_b8
    have w21_bc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m21]; exact w20_bc
    have w21_c0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m21]; exact w20_c0
    have w21_c4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m21]; exact w20_c4
    have w21_c8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m21]; exact w20_c8
    have w21_cc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m21]; exact w20_cc
    have w21_d0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m21]; exact w20_d0
    have w21_d4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m21]; exact w20_d4
    have w21_d8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m21]; exact w20_d8
    have w21_dc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m21]; exact w20_dc
    have w21_e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m21]; exact w20_e0
    have w21_e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m21]; exact w20_e4
    have w21_e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m21]; exact w20_e8
    have w21_ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m21]; exact w20_ec
    have w21_f0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m21]; exact w20_f0
    have w21_f4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m21]; exact w20_f4
    have w21_f8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m21]; exact w20_f8
    have w21_fc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m21]; exact w20_fc
    have w21_100 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m21]; exact w20_100
    have w21_104 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m21]; exact w20_104
    have w21_108 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m21]; exact w20_108
    have w21_10c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m21]; exact w20_10c
    have w21_110 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m21]; exact w20_110
    have w21_114 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m21]; exact w20_114
    have w21_118 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m21]; exact w20_118
    have w21_11c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m21]; exact w20_11c
    have w21_120 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m21]; exact w20_120
    have w21_124 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m21]; exact w20_124
    have w21_128 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m21]; exact w20_128
    have w21_12c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m21]; exact w20_12c
    have w21_130 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m21]; exact w20_130
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m21]; exact w20_420
    have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m21]; exact w20_a20
    have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m21]; exact w20_a24
    have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m21]; exact w20_a28
    have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m21]; exact w20_a2c
    have w21_a30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m21]; exact w20_a30
    have w21_a34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m21]; exact w20_a34
    have w21_a38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m21]; exact w20_a38
    have w21_a3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m21]; exact w20_a3c
    have w21_aa0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m21]; exact w20_aa0
    have w21_aa4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m21]; exact w20_aa4
    have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m21]; exact b20_424
    clear b20_424 w20_aa4 w20_aa0 w20_a3c w20_a38 w20_a34 w20_a30 w20_a2c w20_a28 w20_a24 w20_a20 w20_420 w20_130 w20_12c w20_128 w20_124 w20_120 w20_11c w20_118 w20_114 w20_110 w20_10c w20_108 w20_104 w20_100 w20_fc w20_f8 w20_f4 w20_f0 w20_ec w20_e8 w20_e4 w20_e0 w20_dc w20_d8 w20_d4 w20_d0 w20_cc w20_c8 w20_c4 w20_c0 w20_bc w20_b8 w20_b4 w20_b0 w20_ac w20_a8 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
    exact .inl ⟨(fun ⟨h0', ix7', h1', ix17', h2', _⟩ => by rw [hr7] at h1'; cases h1'; rw [hr17] at h2'; cases h2'), sv_fail F E21 s21 t21 (fun x hx => (fR21 x hx).trans (fM x hx).symm) V21 hret g21_2 g21_18 hO g21_3 g21_4⟩
  have hix17 : ix17 < ((ckl).toNat) - (ix7 + 1) := by have := (nlScan_lt _ _ _ hr17).2; omega
  rw [hr17] at L17
  obtain ⟨y0_17, y4_17, y8_17, y12_17⟩ := L17
  have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K17.w32 (by decide) (by decide)).trans w16_24
  have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K17.w32 (by decide) (by decide)).trans w16_28
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K17.w32 (by decide) (by decide)).trans w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K17.w32 (by decide) (by decide)).trans w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K17.w32 (by decide) (by decide)).trans w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K17.w32 (by decide) (by decide)).trans w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K17.w32 (by decide) (by decide)).trans w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K17.w32 (by decide) (by decide)).trans w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := (K17.w32 (by decide) (by decide)).trans w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K17.w32 (by decide) (by decide)).trans w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K17.w32 (by decide) (by decide)).trans w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K17.w32 (by decide) (by decide)).trans w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K17.w32 (by decide) (by decide)).trans w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K17.w32 (by decide) (by decide)).trans w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K17.w32 (by decide) (by decide)).trans w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K17.w32 (by decide) (by decide)).trans w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K17.w32 (by decide) (by decide)).trans w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K17.w32 (by decide) (by decide)).trans w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K17.w32 (by decide) (by decide)).trans w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K17.w32 (by decide) (by decide)).trans w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K17.w32 (by decide) (by decide)).trans w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K17.w32 (by decide) (by decide)).trans w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K17.w32 (by decide) (by decide)).trans w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K17.w32 (by decide) (by decide)).trans w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K17.w32 (by decide) (by decide)).trans w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K17.w32 (by decide) (by decide)).trans w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K17.w32 (by decide) (by decide)).trans w16_8c
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K17.w32 (by decide) (by decide)).trans w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K17.w32 (by decide) (by decide)).trans w16_94
  have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K17.w32 (by decide) (by decide)).trans w16_98
  have w17_9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K17.w32 (by decide) (by decide)).trans w16_9c
  have w17_a0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K17.w32 (by decide) (by decide)).trans w16_a0
  have w17_a4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K17.w32 (by decide) (by decide)).trans w16_a4
  have w17_a8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K17.w32 (by decide) (by decide)).trans w16_a8
  have w17_ac : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K17.w32 (by decide) (by decide)).trans w16_ac
  have w17_b0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K17.w32 (by decide) (by decide)).trans w16_b0
  have w17_b4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K17.w32 (by decide) (by decide)).trans w16_b4
  have w17_b8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K17.w32 (by decide) (by decide)).trans w16_b8
  have w17_bc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K17.w32 (by decide) (by decide)).trans w16_bc
  have w17_c0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K17.w32 (by decide) (by decide)).trans w16_c0
  have w17_c4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K17.w32 (by decide) (by decide)).trans w16_c4
  have w17_c8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K17.w32 (by decide) (by decide)).trans w16_c8
  have w17_cc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K17.w32 (by decide) (by decide)).trans w16_cc
  have w17_d0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K17.w32 (by decide) (by decide)).trans w16_d0
  have w17_d4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K17.w32 (by decide) (by decide)).trans w16_d4
  have w17_d8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K17.w32 (by decide) (by decide)).trans w16_d8
  have w17_dc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K17.w32 (by decide) (by decide)).trans w16_dc
  have w17_e0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K17.w32 (by decide) (by decide)).trans w16_e0
  have w17_e4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K17.w32 (by decide) (by decide)).trans w16_e4
  have w17_e8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K17.w32 (by decide) (by decide)).trans w16_e8
  have w17_ec : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K17.w32 (by decide) (by decide)).trans w16_ec
  have w17_f0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K17.w32 (by decide) (by decide)).trans w16_f0
  have w17_f4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K17.w32 (by decide) (by decide)).trans w16_f4
  have w17_f8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K17.w32 (by decide) (by decide)).trans w16_f8
  have w17_fc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K17.w32 (by decide) (by decide)).trans w16_fc
  have w17_100 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K17.w32 (by decide) (by decide)).trans w16_100
  have w17_104 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K17.w32 (by decide) (by decide)).trans w16_104
  have w17_108 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K17.w32 (by decide) (by decide)).trans w16_108
  have w17_10c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K17.w32 (by decide) (by decide)).trans w16_10c
  have w17_110 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K17.w32 (by decide) (by decide)).trans w16_110
  have w17_114 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K17.w32 (by decide) (by decide)).trans w16_114
  have w17_118 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K17.w32 (by decide) (by decide)).trans w16_118
  have w17_11c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K17.w32 (by decide) (by decide)).trans w16_11c
  have w17_120 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K17.w32 (by decide) (by decide)).trans w16_120
  have w17_124 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K17.w32 (by decide) (by decide)).trans w16_124
  have w17_128 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K17.w32 (by decide) (by decide)).trans w16_128
  have w17_12c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K17.w32 (by decide) (by decide)).trans w16_12c
  have w17_130 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K17.w32 (by decide) (by decide)).trans w16_130
  have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K17.w32 (by decide) (by decide)).trans w16_a20
  have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K17.w32 (by decide) (by decide)).trans w16_a24
  have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K17.w32 (by decide) (by decide)).trans w16_a28
  have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K17.w32 (by decide) (by decide)).trans w16_a2c
  have w17_a30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K17.w32 (by decide) (by decide)).trans w16_a30
  have w17_a34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K17.w32 (by decide) (by decide)).trans w16_a34
  have w17_a38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K17.w32 (by decide) (by decide)).trans w16_a38
  have w17_a3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K17.w32 (by decide) (by decide)).trans w16_a3c
  have w17_aa0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K17.w32 (by decide) (by decide)).trans w16_aa0
  have w17_aa4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K17.w32 (by decide) (by decide)).trans w16_aa4
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := y0_17
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix17 := y4_17
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := y8_17
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := y12_17
  clear w16_aa4 w16_aa0 w16_a3c w16_a38 w16_a34 w16_a30 w16_a2c w16_a28 w16_a24 w16_a20 w16_42c w16_428 w16_424 w16_420 w16_130 w16_12c w16_128 w16_124 w16_120 w16_11c w16_118 w16_114 w16_110 w16_10c w16_108 w16_104 w16_100 w16_fc w16_f8 w16_f4 w16_f0 w16_ec w16_e8 w16_e4 w16_e0 w16_dc w16_d8 w16_d4 w16_d0 w16_cc w16_c8 w16_c4 w16_c0 w16_bc w16_b8 w16_b4 w16_b0 w16_ac w16_a8 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_13 g16_12 g16_11 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  -- 0x2B72: lw
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_2b72 (off' := 0x2B76) (by decide)
    (by rw [g17_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s18 : St n18.mem SV n18 0x2B76 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = dp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = dg := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = ckl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
  have g18_9 : reg n18 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w17_420]
  have w18_24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m18]; exact w17_24
  have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m18]; exact w17_28
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m18]; exact w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m18]; exact w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m18]; exact w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m18]; exact w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m18]; exact w17_40
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m18]; exact w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m18]; exact w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m18]; exact w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m18]; exact w17_54
  have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m18]; exact w17_58
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m18]; exact w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m18]; exact w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m18]; exact w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m18]; exact w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m18]; exact w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m18]; exact w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m18]; exact w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m18]; exact w17_8c
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m18]; exact w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m18]; exact w17_94
  have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m18]; exact w17_98
  have w18_9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m18]; exact w17_9c
  have w18_a0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m18]; exact w17_a0
  have w18_a4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m18]; exact w17_a4
  have w18_a8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m18]; exact w17_a8
  have w18_ac : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m18]; exact w17_ac
  have w18_b0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m18]; exact w17_b0
  have w18_b4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m18]; exact w17_b4
  have w18_b8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m18]; exact w17_b8
  have w18_bc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m18]; exact w17_bc
  have w18_c0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m18]; exact w17_c0
  have w18_c4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m18]; exact w17_c4
  have w18_c8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m18]; exact w17_c8
  have w18_cc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m18]; exact w17_cc
  have w18_d0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m18]; exact w17_d0
  have w18_d4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m18]; exact w17_d4
  have w18_d8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m18]; exact w17_d8
  have w18_dc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m18]; exact w17_dc
  have w18_e0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m18]; exact w17_e0
  have w18_e4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m18]; exact w17_e4
  have w18_e8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m18]; exact w17_e8
  have w18_ec : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m18]; exact w17_ec
  have w18_f0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m18]; exact w17_f0
  have w18_f4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m18]; exact w17_f4
  have w18_f8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m18]; exact w17_f8
  have w18_fc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m18]; exact w17_fc
  have w18_100 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m18]; exact w17_100
  have w18_104 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m18]; exact w17_104
  have w18_108 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m18]; exact w17_108
  have w18_10c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m18]; exact w17_10c
  have w18_110 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m18]; exact w17_110
  have w18_114 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m18]; exact w17_114
  have w18_118 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m18]; exact w17_118
  have w18_11c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m18]; exact w17_11c
  have w18_120 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m18]; exact w17_120
  have w18_124 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m18]; exact w17_124
  have w18_128 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m18]; exact w17_128
  have w18_12c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m18]; exact w17_12c
  have w18_130 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m18]; exact w17_130
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m18]; exact w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix17 := by rw [m18]; exact w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m18]; exact w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := by rw [m18]; exact w17_42c
  have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m18]; exact w17_a20
  have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m18]; exact w17_a24
  have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m18]; exact w17_a28
  have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m18]; exact w17_a2c
  have w18_a30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m18]; exact w17_a30
  have w18_a34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m18]; exact w17_a34
  have w18_a38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m18]; exact w17_a38
  have w18_a3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m18]; exact w17_a3c
  have w18_aa0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m18]; exact w17_aa0
  have w18_aa4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m18]; exact w17_aa4
  clear w17_42c w17_428 w17_424 w17_420 w17_aa4 w17_aa0 w17_a3c w17_a38 w17_a34 w17_a30 w17_a2c w17_a28 w17_a24 w17_a20 w17_130 w17_12c w17_128 w17_124 w17_120 w17_11c w17_118 w17_114 w17_110 w17_10c w17_108 w17_104 w17_100 w17_fc w17_f8 w17_f4 w17_f0 w17_ec w17_e8 w17_e4 w17_e0 w17_dc w17_d8 w17_d4 w17_d0 w17_cc w17_c8 w17_c4 w17_c0 w17_bc w17_b8 w17_b4 w17_b0 w17_ac w17_a8 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 y12_17 y8_17 y4_17 y0_17 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 K17 rk17 s17 c17
  -- 0x2B76: branch, not taken
  obtain ⟨n19, d19, u19⟩ := s18.notTaken E18.self 0x2B7A sv_at_2b76
    (by decide) (by rw [g18_9, s18.zero]; exact br_beq_f (line_rest (.inl ck_in) hix7).ne0)
  have s19 : St n19.mem SV n19 0x2B7A (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
  have g19_9 : reg n19 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u19.regs, g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, g18_19]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = dp := by rw [u19.regs, g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u19.regs, g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = dg := by rw [u19.regs, g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = ckl := by rw [u19.regs, g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u19.regs, g18_27]
  have w19_24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m19]; exact w18_24
  have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m19]; exact w18_28
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m19]; exact w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m19]; exact w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m19]; exact w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m19]; exact w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m19]; exact w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m19]; exact w18_40
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m19]; exact w18_48
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
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m19]; exact w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m19]; exact w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m19]; exact w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m19]; exact w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m19]; exact w18_8c
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m19]; exact w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m19]; exact w18_94
  have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m19]; exact w18_98
  have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m19]; exact w18_9c
  have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m19]; exact w18_a0
  have w19_a4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m19]; exact w18_a4
  have w19_a8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m19]; exact w18_a8
  have w19_ac : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m19]; exact w18_ac
  have w19_b0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m19]; exact w18_b0
  have w19_b4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m19]; exact w18_b4
  have w19_b8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m19]; exact w18_b8
  have w19_bc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m19]; exact w18_bc
  have w19_c0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m19]; exact w18_c0
  have w19_c4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m19]; exact w18_c4
  have w19_c8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m19]; exact w18_c8
  have w19_cc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m19]; exact w18_cc
  have w19_d0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m19]; exact w18_d0
  have w19_d4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m19]; exact w18_d4
  have w19_d8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m19]; exact w18_d8
  have w19_dc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m19]; exact w18_dc
  have w19_e0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m19]; exact w18_e0
  have w19_e4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m19]; exact w18_e4
  have w19_e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m19]; exact w18_e8
  have w19_ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m19]; exact w18_ec
  have w19_f0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m19]; exact w18_f0
  have w19_f4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m19]; exact w18_f4
  have w19_f8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m19]; exact w18_f8
  have w19_fc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m19]; exact w18_fc
  have w19_100 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m19]; exact w18_100
  have w19_104 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m19]; exact w18_104
  have w19_108 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m19]; exact w18_108
  have w19_10c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m19]; exact w18_10c
  have w19_110 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m19]; exact w18_110
  have w19_114 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m19]; exact w18_114
  have w19_118 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m19]; exact w18_118
  have w19_11c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m19]; exact w18_11c
  have w19_120 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m19]; exact w18_120
  have w19_124 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m19]; exact w18_124
  have w19_128 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m19]; exact w18_128
  have w19_12c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m19]; exact w18_12c
  have w19_130 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m19]; exact w18_130
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix17 := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := by rw [m19]; exact w18_42c
  have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m19]; exact w18_a20
  have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m19]; exact w18_a24
  have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m19]; exact w18_a28
  have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m19]; exact w18_a2c
  have w19_a30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m19]; exact w18_a30
  have w19_a34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m19]; exact w18_a34
  have w19_a38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m19]; exact w18_a38
  have w19_a3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m19]; exact w18_a3c
  have w19_aa0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m19]; exact w18_aa0
  have w19_aa4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m19]; exact w18_aa4
  clear w18_aa4 w18_aa0 w18_a3c w18_a38 w18_a34 w18_a30 w18_a2c w18_a28 w18_a24 w18_a20 w18_42c w18_428 w18_424 w18_420 w18_130 w18_12c w18_128 w18_124 w18_120 w18_11c w18_118 w18_114 w18_110 w18_10c w18_108 w18_104 w18_100 w18_fc w18_f8 w18_f4 w18_f0 w18_ec w18_e8 w18_e4 w18_e0 w18_dc w18_d8 w18_d4 w18_d0 w18_cc w18_c8 w18_c4 w18_c0 w18_bc w18_b8 w18_b4 w18_b0 w18_ac w18_a8 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 g18_9 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x2B7A
  obtain ⟨n20, c20, u20⟩ := s19.block svCk12b7a E19.self svCk12b7a_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x2B7E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svCk12b7a (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by
    rw [rb20, runBlock_reg _ _ _ sp s19.zero (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (3 : Fin 32) s19.zero (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (4 : Fin 32) s19.zero (by decide), g19_4]
  have g20_9 : reg n20 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = dp := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = dg := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = ckl := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svCk12b7a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_9, g19_18, g19_19, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w20_24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m20]; exact w19_24
  have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m20]; exact w19_28
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m20]; exact w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m20]; exact w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m20]; exact w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m20]; exact w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m20]; exact w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m20]; exact w19_40
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m20]; exact w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m20]; exact w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m20]; exact w19_54
  have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m20]; exact w19_58
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m20]; exact w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m20]; exact w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m20]; exact w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m20]; exact w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m20]; exact w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m20]; exact w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m20]; exact w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m20]; exact w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m20]; exact w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m20]; exact w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m20]; exact w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m20]; exact w19_8c
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m20]; exact w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m20]; exact w19_94
  have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m20]; exact w19_98
  have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m20]; exact w19_9c
  have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m20]; exact w19_a0
  have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m20]; exact w19_a4
  have w20_a8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m20]; exact w19_a8
  have w20_ac : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m20]; exact w19_ac
  have w20_b0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m20]; exact w19_b0
  have w20_b4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m20]; exact w19_b4
  have w20_b8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m20]; exact w19_b8
  have w20_bc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m20]; exact w19_bc
  have w20_c0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m20]; exact w19_c0
  have w20_c4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m20]; exact w19_c4
  have w20_c8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m20]; exact w19_c8
  have w20_cc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m20]; exact w19_cc
  have w20_d0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m20]; exact w19_d0
  have w20_d4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m20]; exact w19_d4
  have w20_d8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m20]; exact w19_d8
  have w20_dc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m20]; exact w19_dc
  have w20_e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m20]; exact w19_e0
  have w20_e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m20]; exact w19_e4
  have w20_e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m20]; exact w19_e8
  have w20_ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m20]; exact w19_ec
  have w20_f0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m20]; exact w19_f0
  have w20_f4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m20]; exact w19_f4
  have w20_f8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m20]; exact w19_f8
  have w20_fc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m20]; exact w19_fc
  have w20_100 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m20]; exact w19_100
  have w20_104 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m20]; exact w19_104
  have w20_108 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m20]; exact w19_108
  have w20_10c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m20]; exact w19_10c
  have w20_110 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m20]; exact w19_110
  have w20_114 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m20]; exact w19_114
  have w20_118 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m20]; exact w19_118
  have w20_11c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m20]; exact w19_11c
  have w20_120 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m20]; exact w19_120
  have w20_124 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m20]; exact w19_124
  have w20_128 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m20]; exact w19_128
  have w20_12c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m20]; exact w19_12c
  have w20_130 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m20]; exact w19_130
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix17 := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := by rw [m20]; exact w19_42c
  have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m20]; exact w19_a20
  have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m20]; exact w19_a24
  have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m20]; exact w19_a28
  have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m20]; exact w19_a2c
  have w20_a30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m20]; exact w19_a30
  have w20_a34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m20]; exact w19_a34
  have w20_a38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m20]; exact w19_a38
  have w20_a3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m20]; exact w19_a3c
  have w20_aa0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m20]; exact w19_aa0
  have w20_aa4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m20]; exact w19_aa4
  clear w19_aa4 w19_aa0 w19_a3c w19_a38 w19_a34 w19_a30 w19_a2c w19_a28 w19_a24 w19_a20 w19_42c w19_428 w19_424 w19_420 w19_130 w19_12c w19_128 w19_124 w19_120 w19_11c w19_118 w19_114 w19_110 w19_10c w19_108 w19_104 w19_100 w19_fc w19_f8 w19_f4 w19_f0 w19_ec w19_e8 w19_e4 w19_e0 w19_dc w19_d8 w19_d4 w19_d0 w19_cc w19_c8 w19_c4 w19_c0 w19_bc w19_b8 w19_b4 w19_b0 w19_ac w19_a8 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_19 g19_18 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x2B7E: lw
  obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_2b7e (off' := 0x2B80) (by decide)
    (by rw [g20_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s21 : St n21.mem SV n21 0x2B80 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_9 : reg n21 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_10]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = dp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = dg := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = ckl := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w20_424]
  have w21_24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m21]; exact w20_24
  have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m21]; exact w20_28
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m21]; exact w20_2c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m21]; exact w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m21]; exact w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m21]; exact w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m21]; exact w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m21]; exact w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m21]; exact w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m21]; exact w20_48
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
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m21]; exact w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m21]; exact w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m21]; exact w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m21]; exact w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m21]; exact w20_8c
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m21]; exact w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m21]; exact w20_94
  have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m21]; exact w20_98
  have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m21]; exact w20_9c
  have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m21]; exact w20_a0
  have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m21]; exact w20_a4
  have w21_a8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m21]; exact w20_a8
  have w21_ac : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m21]; exact w20_ac
  have w21_b0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m21]; exact w20_b0
  have w21_b4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m21]; exact w20_b4
  have w21_b8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m21]; exact w20_b8
  have w21_bc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m21]; exact w20_bc
  have w21_c0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m21]; exact w20_c0
  have w21_c4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m21]; exact w20_c4
  have w21_c8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m21]; exact w20_c8
  have w21_cc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m21]; exact w20_cc
  have w21_d0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m21]; exact w20_d0
  have w21_d4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m21]; exact w20_d4
  have w21_d8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m21]; exact w20_d8
  have w21_dc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m21]; exact w20_dc
  have w21_e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m21]; exact w20_e0
  have w21_e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m21]; exact w20_e4
  have w21_e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m21]; exact w20_e8
  have w21_ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m21]; exact w20_ec
  have w21_f0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m21]; exact w20_f0
  have w21_f4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m21]; exact w20_f4
  have w21_f8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m21]; exact w20_f8
  have w21_fc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m21]; exact w20_fc
  have w21_100 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m21]; exact w20_100
  have w21_104 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m21]; exact w20_104
  have w21_108 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m21]; exact w20_108
  have w21_10c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m21]; exact w20_10c
  have w21_110 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m21]; exact w20_110
  have w21_114 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m21]; exact w20_114
  have w21_118 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m21]; exact w20_118
  have w21_11c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m21]; exact w20_11c
  have w21_120 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m21]; exact w20_120
  have w21_124 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m21]; exact w20_124
  have w21_128 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m21]; exact w20_128
  have w21_12c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m21]; exact w20_12c
  have w21_130 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m21]; exact w20_130
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m21]; exact w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix17 := by rw [m21]; exact w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m21]; exact w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := by rw [m21]; exact w20_42c
  have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m21]; exact w20_a20
  have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m21]; exact w20_a24
  have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m21]; exact w20_a28
  have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m21]; exact w20_a2c
  have w21_a30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m21]; exact w20_a30
  have w21_a34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m21]; exact w20_a34
  have w21_a38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m21]; exact w20_a38
  have w21_a3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m21]; exact w20_a3c
  have w21_aa0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m21]; exact w20_aa0
  have w21_aa4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m21]; exact w20_aa4
  clear w20_aa4 w20_aa0 w20_a3c w20_a38 w20_a34 w20_a30 w20_a2c w20_a28 w20_a24 w20_a20 w20_42c w20_428 w20_424 w20_420 w20_130 w20_12c w20_128 w20_124 w20_120 w20_11c w20_118 w20_114 w20_110 w20_10c w20_108 w20_104 w20_100 w20_fc w20_f8 w20_f4 w20_f0 w20_ec w20_e8 w20_e4 w20_e0 w20_dc w20_d8 w20_d4 w20_d0 w20_cc w20_c8 w20_c4 w20_c0 w20_bc w20_b8 w20_b4 w20_b0 w20_ac w20_a8 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x2B80: lw
  obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_2b80 (off' := 0x2B82) (by decide)
    (by rw [g21_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s22 : St n22.mem SV n22 0x2B82 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
  have g22_10 : reg n22 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = dp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = dg := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = ckl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
  have g22_11 : reg n22 a1 = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w21_428]
  have w22_24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m22]; exact w21_24
  have w22_28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m22]; exact w21_28
  have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m22]; exact w21_2c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m22]; exact w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m22]; exact w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m22]; exact w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m22]; exact w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m22]; exact w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m22]; exact w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m22]; exact w21_54
  have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m22]; exact w21_58
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m22]; exact w21_5c
  have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m22]; exact w21_60
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m22]; exact w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m22]; exact w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m22]; exact w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m22]; exact w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m22]; exact w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m22]; exact w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m22]; exact w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m22]; exact w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m22]; exact w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m22]; exact w21_8c
  have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m22]; exact w21_90
  have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m22]; exact w21_94
  have w22_98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m22]; exact w21_98
  have w22_9c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m22]; exact w21_9c
  have w22_a0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m22]; exact w21_a0
  have w22_a4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m22]; exact w21_a4
  have w22_a8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m22]; exact w21_a8
  have w22_ac : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m22]; exact w21_ac
  have w22_b0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m22]; exact w21_b0
  have w22_b4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m22]; exact w21_b4
  have w22_b8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m22]; exact w21_b8
  have w22_bc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m22]; exact w21_bc
  have w22_c0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m22]; exact w21_c0
  have w22_c4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m22]; exact w21_c4
  have w22_c8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m22]; exact w21_c8
  have w22_cc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m22]; exact w21_cc
  have w22_d0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m22]; exact w21_d0
  have w22_d4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m22]; exact w21_d4
  have w22_d8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m22]; exact w21_d8
  have w22_dc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m22]; exact w21_dc
  have w22_e0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m22]; exact w21_e0
  have w22_e4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m22]; exact w21_e4
  have w22_e8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m22]; exact w21_e8
  have w22_ec : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m22]; exact w21_ec
  have w22_f0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m22]; exact w21_f0
  have w22_f4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m22]; exact w21_f4
  have w22_f8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m22]; exact w21_f8
  have w22_fc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m22]; exact w21_fc
  have w22_100 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m22]; exact w21_100
  have w22_104 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m22]; exact w21_104
  have w22_108 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m22]; exact w21_108
  have w22_10c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m22]; exact w21_10c
  have w22_110 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m22]; exact w21_110
  have w22_114 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m22]; exact w21_114
  have w22_118 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m22]; exact w21_118
  have w22_11c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m22]; exact w21_11c
  have w22_120 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m22]; exact w21_120
  have w22_124 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m22]; exact w21_124
  have w22_128 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m22]; exact w21_128
  have w22_12c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m22]; exact w21_12c
  have w22_130 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m22]; exact w21_130
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix17 := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := by rw [m22]; exact w21_42c
  have w22_a20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m22]; exact w21_a20
  have w22_a24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m22]; exact w21_a24
  have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m22]; exact w21_a28
  have w22_a2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m22]; exact w21_a2c
  have w22_a30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m22]; exact w21_a30
  have w22_a34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m22]; exact w21_a34
  have w22_a38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m22]; exact w21_a38
  have w22_a3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m22]; exact w21_a3c
  have w22_aa0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m22]; exact w21_aa0
  have w22_aa4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m22]; exact w21_aa4
  clear w21_aa4 w21_aa0 w21_a3c w21_a38 w21_a34 w21_a30 w21_a2c w21_a28 w21_a24 w21_a20 w21_42c w21_428 w21_424 w21_420 w21_130 w21_12c w21_128 w21_124 w21_120 w21_11c w21_118 w21_114 w21_110 w21_10c w21_108 w21_104 w21_100 w21_fc w21_f8 w21_f4 w21_f0 w21_ec w21_e8 w21_e4 w21_e0 w21_dc w21_d8 w21_d4 w21_d0 w21_cc w21_c8 w21_c4 w21_c0 w21_bc w21_b8 w21_b4 w21_b0 w21_ac w21_a8 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 w21_2c w21_28 w21_24 g21_8 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_10 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0x2B82: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_2b82 (off' := 0x2B84) (by decide)
    (by rw [g22_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x2B84 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_10]
  have g23_11 : reg n23 a1 = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_11]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = dp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = dg := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = ckl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w22_42c]
  have w23_24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m23]; exact w22_24
  have w23_28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m23]; exact w22_28
  have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m23]; exact w22_2c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m23]; exact w22_38
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m23]; exact w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m23]; exact w22_40
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m23]; exact w22_48
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
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m23]; exact w22_8c
  have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m23]; exact w22_90
  have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m23]; exact w22_94
  have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m23]; exact w22_98
  have w23_9c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m23]; exact w22_9c
  have w23_a0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m23]; exact w22_a0
  have w23_a4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m23]; exact w22_a4
  have w23_a8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m23]; exact w22_a8
  have w23_ac : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m23]; exact w22_ac
  have w23_b0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m23]; exact w22_b0
  have w23_b4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m23]; exact w22_b4
  have w23_b8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m23]; exact w22_b8
  have w23_bc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m23]; exact w22_bc
  have w23_c0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m23]; exact w22_c0
  have w23_c4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m23]; exact w22_c4
  have w23_c8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m23]; exact w22_c8
  have w23_cc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m23]; exact w22_cc
  have w23_d0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m23]; exact w22_d0
  have w23_d4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m23]; exact w22_d4
  have w23_d8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m23]; exact w22_d8
  have w23_dc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m23]; exact w22_dc
  have w23_e0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m23]; exact w22_e0
  have w23_e4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m23]; exact w22_e4
  have w23_e8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m23]; exact w22_e8
  have w23_ec : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m23]; exact w22_ec
  have w23_f0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m23]; exact w22_f0
  have w23_f4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m23]; exact w22_f4
  have w23_f8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m23]; exact w22_f8
  have w23_fc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m23]; exact w22_fc
  have w23_100 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m23]; exact w22_100
  have w23_104 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m23]; exact w22_104
  have w23_108 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m23]; exact w22_108
  have w23_10c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m23]; exact w22_10c
  have w23_110 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m23]; exact w22_110
  have w23_114 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m23]; exact w22_114
  have w23_118 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m23]; exact w22_118
  have w23_11c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m23]; exact w22_11c
  have w23_120 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m23]; exact w22_120
  have w23_124 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m23]; exact w22_124
  have w23_128 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m23]; exact w22_128
  have w23_12c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m23]; exact w22_12c
  have w23_130 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m23]; exact w22_130
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix17 := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := by rw [m23]; exact w22_42c
  have w23_a20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m23]; exact w22_a20
  have w23_a24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m23]; exact w22_a24
  have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m23]; exact w22_a28
  have w23_a2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m23]; exact w22_a2c
  have w23_a30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m23]; exact w22_a30
  have w23_a34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m23]; exact w22_a34
  have w23_a38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m23]; exact w22_a38
  have w23_a3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m23]; exact w22_a3c
  have w23_aa0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m23]; exact w22_aa0
  have w23_aa4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m23]; exact w22_aa4
  clear w22_aa4 w22_aa0 w22_a3c w22_a38 w22_a34 w22_a30 w22_a2c w22_a28 w22_a24 w22_a20 w22_42c w22_428 w22_424 w22_420 w22_130 w22_12c w22_128 w22_124 w22_120 w22_11c w22_118 w22_114 w22_110 w22_10c w22_108 w22_104 w22_100 w22_fc w22_f8 w22_f4 w22_f0 w22_ec w22_e8 w22_e4 w22_e0 w22_dc w22_d8 w22_d4 w22_d0 w22_cc w22_c8 w22_c4 w22_c0 w22_bc w22_b8 w22_b4 w22_b0 w22_ac w22_a8 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 w22_2c w22_28 w22_24 g22_11 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_19 g22_18 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x2B84
  obtain ⟨n24, c24, u24⟩ := s23.block svCk12b84 E23.self svCk12b84_end
    ⟨trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0x2B88 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svCk12b84 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans c24
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by
    rw [rb24, runBlock_reg _ _ _ sp s23.zero (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (3 : Fin 32) s23.zero (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (4 : Fin 32) s23.zero (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_11 : reg n24 a1 = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by
    rw [rb24, runBlock_reg _ _ _ a1 s23.zero (by decide), g23_11]
  have g24_12 : reg n24 a2 = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := by
    rw [rb24, runBlock_reg _ _ _ a2 s23.zero (by decide), g23_12]
  have g24_18 : reg n24 (18 : Fin 32) = out := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = dp := by
    rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = dg := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = ckl := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svCk12b84, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_11, g23_12, g23_18, g23_19, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w24_24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m24]; exact w23_24
  have w24_28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m24]; exact w23_28
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m24]; exact w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m24]; exact w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m24]; exact w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m24]; exact w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m24]; exact w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m24]; exact w23_54
  have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m24]; exact w23_58
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m24]; exact w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m24]; exact w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m24]; exact w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m24]; exact w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m24]; exact w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m24]; exact w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m24]; exact w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m24]; exact w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m24]; exact w23_8c
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m24]; exact w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m24]; exact w23_94
  have w24_98 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m24]; exact w23_98
  have w24_9c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m24]; exact w23_9c
  have w24_a0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m24]; exact w23_a0
  have w24_a4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m24]; exact w23_a4
  have w24_a8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m24]; exact w23_a8
  have w24_ac : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m24]; exact w23_ac
  have w24_b0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m24]; exact w23_b0
  have w24_b4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m24]; exact w23_b4
  have w24_b8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m24]; exact w23_b8
  have w24_bc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m24]; exact w23_bc
  have w24_c0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m24]; exact w23_c0
  have w24_c4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m24]; exact w23_c4
  have w24_c8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m24]; exact w23_c8
  have w24_cc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m24]; exact w23_cc
  have w24_d0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m24]; exact w23_d0
  have w24_d4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m24]; exact w23_d4
  have w24_d8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m24]; exact w23_d8
  have w24_dc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m24]; exact w23_dc
  have w24_e0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m24]; exact w23_e0
  have w24_e4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m24]; exact w23_e4
  have w24_e8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m24]; exact w23_e8
  have w24_ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m24]; exact w23_ec
  have w24_f0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m24]; exact w23_f0
  have w24_f4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m24]; exact w23_f4
  have w24_f8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m24]; exact w23_f8
  have w24_fc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m24]; exact w23_fc
  have w24_100 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m24]; exact w23_100
  have w24_104 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m24]; exact w23_104
  have w24_108 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m24]; exact w23_108
  have w24_10c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m24]; exact w23_10c
  have w24_110 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m24]; exact w23_110
  have w24_114 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m24]; exact w23_114
  have w24_118 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m24]; exact w23_118
  have w24_11c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m24]; exact w23_11c
  have w24_120 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m24]; exact w23_120
  have w24_124 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m24]; exact w23_124
  have w24_128 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m24]; exact w23_128
  have w24_12c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m24]; exact w23_12c
  have w24_130 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m24]; exact w23_130
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix17 := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((ckl).toNat) - (ix7 + 1)) - BitVec.ofNat 32 (ix17 + 1) := by rw [m24]; exact w23_42c
  have w24_a20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m24]; exact w23_a20
  have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m24]; exact w23_a24
  have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m24]; exact w23_a28
  have w24_a2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m24]; exact w23_a2c
  have w24_a30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m24]; exact w23_a30
  have w24_a34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m24]; exact w23_a34
  have w24_a38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m24]; exact w23_a38
  have w24_a3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m24]; exact w23_a3c
  have w24_aa0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m24]; exact w23_aa0
  have w24_aa4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m24]; exact w23_aa4
  clear w23_aa4 w23_aa0 w23_a3c w23_a38 w23_a34 w23_a30 w23_a2c w23_a28 w23_a24 w23_a20 w23_42c w23_428 w23_424 w23_420 w23_130 w23_12c w23_128 w23_124 w23_120 w23_11c w23_118 w23_114 w23_110 w23_10c w23_108 w23_104 w23_100 w23_fc w23_f8 w23_f4 w23_f0 w23_ec w23_e8 w23_e4 w23_e0 w23_dc w23_d8 w23_d4 w23_d0 w23_cc w23_c8 w23_c4 w23_c0 w23_bc w23_b8 w23_b4 w23_b0 w23_ac w23_a8 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 g23_12 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_19 g23_18 g23_11 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x2B88: sv_lineF
  obtain ⟨n25, c25, s25, rk25, K25, L25, fr25⟩ := sv_lineF (oc := 0x420) (nl := (((ckl).toNat) - (ix7 + 1)) - (ix17 + 1))
    F E24 (CK0.sv F fR24) s24 sv_at_2b88 sv_at_2b8c (by decide) (by decide)
    g24_10 g24_11 (by rw [g24_12, sub_ofNat (Nat.succ_le_of_lt hix17) (by omega)]) (by decide) (by decide) (line_rest (line_rest (.inl ck_in) hix7) hix17)
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keepL K25 (by decide)
  rw [nlScan_ro F fR24 (line_rest (line_rest (.inl ck_in) hix7) hix17)] at L25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rk25 sp (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk25 (3 : Fin 32) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk25 (4 : Fin 32) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [rk25 (8 : Fin 32) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [rk25 (9 : Fin 32) (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rk25 (18 : Fin 32) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rk25 (19 : Fin 32) (by decide), g24_19]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rk25 (21 : Fin 32) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = dp := by rw [rk25 (22 : Fin 32) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rk25 (23 : Fin 32) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = dg := by rw [rk25 (24 : Fin 32) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = ckl := by rw [rk25 (25 : Fin 32) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rk25 (26 : Fin 32) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk25 (27 : Fin 32) (by decide), g24_27]
  obtain ⟨r25, hr25⟩ : ∃ r, nlScan M0 (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) 0 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) = r := ⟨_, rfl⟩
  rcases r25 with _ | ix25
  · rw [hr25] at L25
    obtain ⟨z0_25, z4_25⟩ := L25
    have w25_24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K25.w32 (by decide) (by decide)).trans w24_24
    have w25_28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K25.w32 (by decide) (by decide)).trans w24_28
    have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K25.w32 (by decide) (by decide)).trans w24_2c
    have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K25.w32 (by decide) (by decide)).trans w24_30
    have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K25.w32 (by decide) (by decide)).trans w24_34
    have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K25.w32 (by decide) (by decide)).trans w24_38
    have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K25.w32 (by decide) (by decide)).trans w24_3c
    have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K25.w32 (by decide) (by decide)).trans w24_40
    have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := (K25.w32 (by decide) (by decide)).trans w24_44
    have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K25.w32 (by decide) (by decide)).trans w24_48
    have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K25.w32 (by decide) (by decide)).trans w24_4c
    have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K25.w32 (by decide) (by decide)).trans w24_50
    have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K25.w32 (by decide) (by decide)).trans w24_54
    have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K25.w32 (by decide) (by decide)).trans w24_58
    have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K25.w32 (by decide) (by decide)).trans w24_5c
    have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K25.w32 (by decide) (by decide)).trans w24_60
    have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K25.w32 (by decide) (by decide)).trans w24_64
    have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K25.w32 (by decide) (by decide)).trans w24_68
    have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K25.w32 (by decide) (by decide)).trans w24_6c
    have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K25.w32 (by decide) (by decide)).trans w24_70
    have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K25.w32 (by decide) (by decide)).trans w24_74
    have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K25.w32 (by decide) (by decide)).trans w24_78
    have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K25.w32 (by decide) (by decide)).trans w24_7c
    have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K25.w32 (by decide) (by decide)).trans w24_80
    have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K25.w32 (by decide) (by decide)).trans w24_84
    have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K25.w32 (by decide) (by decide)).trans w24_88
    have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K25.w32 (by decide) (by decide)).trans w24_8c
    have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K25.w32 (by decide) (by decide)).trans w24_90
    have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K25.w32 (by decide) (by decide)).trans w24_94
    have w25_98 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K25.w32 (by decide) (by decide)).trans w24_98
    have w25_9c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K25.w32 (by decide) (by decide)).trans w24_9c
    have w25_a0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K25.w32 (by decide) (by decide)).trans w24_a0
    have w25_a4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K25.w32 (by decide) (by decide)).trans w24_a4
    have w25_a8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K25.w32 (by decide) (by decide)).trans w24_a8
    have w25_ac : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K25.w32 (by decide) (by decide)).trans w24_ac
    have w25_b0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K25.w32 (by decide) (by decide)).trans w24_b0
    have w25_b4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K25.w32 (by decide) (by decide)).trans w24_b4
    have w25_b8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K25.w32 (by decide) (by decide)).trans w24_b8
    have w25_bc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K25.w32 (by decide) (by decide)).trans w24_bc
    have w25_c0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K25.w32 (by decide) (by decide)).trans w24_c0
    have w25_c4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K25.w32 (by decide) (by decide)).trans w24_c4
    have w25_c8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K25.w32 (by decide) (by decide)).trans w24_c8
    have w25_cc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K25.w32 (by decide) (by decide)).trans w24_cc
    have w25_d0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K25.w32 (by decide) (by decide)).trans w24_d0
    have w25_d4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K25.w32 (by decide) (by decide)).trans w24_d4
    have w25_d8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K25.w32 (by decide) (by decide)).trans w24_d8
    have w25_dc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K25.w32 (by decide) (by decide)).trans w24_dc
    have w25_e0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K25.w32 (by decide) (by decide)).trans w24_e0
    have w25_e4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K25.w32 (by decide) (by decide)).trans w24_e4
    have w25_e8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K25.w32 (by decide) (by decide)).trans w24_e8
    have w25_ec : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K25.w32 (by decide) (by decide)).trans w24_ec
    have w25_f0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K25.w32 (by decide) (by decide)).trans w24_f0
    have w25_f4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K25.w32 (by decide) (by decide)).trans w24_f4
    have w25_f8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K25.w32 (by decide) (by decide)).trans w24_f8
    have w25_fc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K25.w32 (by decide) (by decide)).trans w24_fc
    have w25_100 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K25.w32 (by decide) (by decide)).trans w24_100
    have w25_104 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K25.w32 (by decide) (by decide)).trans w24_104
    have w25_108 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K25.w32 (by decide) (by decide)).trans w24_108
    have w25_10c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K25.w32 (by decide) (by decide)).trans w24_10c
    have w25_110 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K25.w32 (by decide) (by decide)).trans w24_110
    have w25_114 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K25.w32 (by decide) (by decide)).trans w24_114
    have w25_118 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K25.w32 (by decide) (by decide)).trans w24_118
    have w25_11c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K25.w32 (by decide) (by decide)).trans w24_11c
    have w25_120 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K25.w32 (by decide) (by decide)).trans w24_120
    have w25_124 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K25.w32 (by decide) (by decide)).trans w24_124
    have w25_128 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K25.w32 (by decide) (by decide)).trans w24_128
    have w25_12c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K25.w32 (by decide) (by decide)).trans w24_12c
    have w25_130 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K25.w32 (by decide) (by decide)).trans w24_130
    have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K25.w32 (by decide) (by decide)).trans w24_a20
    have w25_a24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K25.w32 (by decide) (by decide)).trans w24_a24
    have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K25.w32 (by decide) (by decide)).trans w24_a28
    have w25_a2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K25.w32 (by decide) (by decide)).trans w24_a2c
    have w25_a30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K25.w32 (by decide) (by decide)).trans w24_a30
    have w25_a34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K25.w32 (by decide) (by decide)).trans w24_a34
    have w25_a38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K25.w32 (by decide) (by decide)).trans w24_a38
    have w25_a3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K25.w32 (by decide) (by decide)).trans w24_a3c
    have w25_aa0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K25.w32 (by decide) (by decide)).trans w24_aa0
    have w25_aa4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K25.w32 (by decide) (by decide)).trans w24_aa4
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z0_25
    have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := z4_25
    clear w24_aa4 w24_aa0 w24_a3c w24_a38 w24_a34 w24_a30 w24_a2c w24_a28 w24_a24 w24_a20 w24_42c w24_428 w24_424 w24_420 w24_130 w24_12c w24_128 w24_124 w24_120 w24_11c w24_118 w24_114 w24_110 w24_10c w24_108 w24_104 w24_100 w24_fc w24_f8 w24_f4 w24_f0 w24_ec w24_e8 w24_e4 w24_e0 w24_dc w24_d8 w24_d4 w24_d0 w24_cc w24_c8 w24_c4 w24_c0 w24_bc w24_b8 w24_b4 w24_b0 w24_ac w24_a8 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_19 g24_18 g24_12 g24_11 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
    -- 0x2B90: lw
    obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_2b90 (off' := 0x2B94) (by decide)
      (by rw [g25_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s26 : St n26.mem SV n26 0x2B94 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
    have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = dp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
    have g26_24 : reg n26 (24 : Fin 32) = dg := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = ckl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
    have g26_23 : reg n26 (23 : Fin 32) = 0 := by
      rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g25_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w25_420]
    have w26_24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m26]; exact w25_24
    have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m26]; exact w25_28
    have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m26]; exact w25_2c
    have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m26]; exact w25_30
    have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m26]; exact w25_34
    have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m26]; exact w25_38
    have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m26]; exact w25_3c
    have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m26]; exact w25_40
    have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m26]; exact w25_44
    have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m26]; exact w25_48
    have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m26]; exact w25_4c
    have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
    have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m26]; exact w25_54
    have w26_58 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m26]; exact w25_58
    have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m26]; exact w25_5c
    have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m26]; exact w25_60
    have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m26]; exact w25_64
    have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m26]; exact w25_68
    have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m26]; exact w25_6c
    have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m26]; exact w25_70
    have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m26]; exact w25_74
    have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m26]; exact w25_78
    have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m26]; exact w25_7c
    have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m26]; exact w25_80
    have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m26]; exact w25_84
    have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m26]; exact w25_88
    have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m26]; exact w25_8c
    have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m26]; exact w25_90
    have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m26]; exact w25_94
    have w26_98 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m26]; exact w25_98
    have w26_9c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m26]; exact w25_9c
    have w26_a0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m26]; exact w25_a0
    have w26_a4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m26]; exact w25_a4
    have w26_a8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m26]; exact w25_a8
    have w26_ac : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m26]; exact w25_ac
    have w26_b0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m26]; exact w25_b0
    have w26_b4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m26]; exact w25_b4
    have w26_b8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m26]; exact w25_b8
    have w26_bc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m26]; exact w25_bc
    have w26_c0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m26]; exact w25_c0
    have w26_c4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m26]; exact w25_c4
    have w26_c8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m26]; exact w25_c8
    have w26_cc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m26]; exact w25_cc
    have w26_d0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m26]; exact w25_d0
    have w26_d4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m26]; exact w25_d4
    have w26_d8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m26]; exact w25_d8
    have w26_dc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m26]; exact w25_dc
    have w26_e0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m26]; exact w25_e0
    have w26_e4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m26]; exact w25_e4
    have w26_e8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m26]; exact w25_e8
    have w26_ec : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m26]; exact w25_ec
    have w26_f0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m26]; exact w25_f0
    have w26_f4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m26]; exact w25_f4
    have w26_f8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m26]; exact w25_f8
    have w26_fc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m26]; exact w25_fc
    have w26_100 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m26]; exact w25_100
    have w26_104 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m26]; exact w25_104
    have w26_108 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m26]; exact w25_108
    have w26_10c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m26]; exact w25_10c
    have w26_110 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m26]; exact w25_110
    have w26_114 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m26]; exact w25_114
    have w26_118 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m26]; exact w25_118
    have w26_11c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m26]; exact w25_11c
    have w26_120 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m26]; exact w25_120
    have w26_124 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m26]; exact w25_124
    have w26_128 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m26]; exact w25_128
    have w26_12c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m26]; exact w25_12c
    have w26_130 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m26]; exact w25_130
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m26]; exact w25_420
    have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m26]; exact w25_a20
    have w26_a24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m26]; exact w25_a24
    have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m26]; exact w25_a28
    have w26_a2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m26]; exact w25_a2c
    have w26_a30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m26]; exact w25_a30
    have w26_a34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m26]; exact w25_a34
    have w26_a38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m26]; exact w25_a38
    have w26_a3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m26]; exact w25_a3c
    have w26_aa0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m26]; exact w25_aa0
    have w26_aa4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m26]; exact w25_aa4
    have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m26]; exact b25_424
    clear b25_424 w25_420 w25_aa4 w25_aa0 w25_a3c w25_a38 w25_a34 w25_a30 w25_a2c w25_a28 w25_a24 w25_a20 w25_130 w25_12c w25_128 w25_124 w25_120 w25_11c w25_118 w25_114 w25_110 w25_10c w25_108 w25_104 w25_100 w25_fc w25_f8 w25_f4 w25_f0 w25_ec w25_e8 w25_e4 w25_e0 w25_dc w25_d8 w25_d4 w25_d0 w25_cc w25_c8 w25_c4 w25_c0 w25_bc w25_b8 w25_b4 w25_b0 w25_ac w25_a8 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_38 w25_34 w25_30 w25_2c w25_28 w25_24 z4_25 z0_25
    -- 0x2B94: branch, taken
    obtain ⟨n27, d27, u27⟩ := s26.taken E26.self 0x2FEA sv_at_2b94
      (by decide) (by rw [g26_23, s26.zero]; rfl)
    have s27 : St n27.mem SV n27 0x2FEA (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u27.regs, g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u27.regs, g26_9]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
    have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = dp := by rw [u27.regs, g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = 0 := by rw [u27.regs, g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = dg := by rw [u27.regs, g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = ckl := by rw [u27.regs, g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u27.regs, g26_27]
    have w27_24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m27]; exact w26_24
    have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m27]; exact w26_28
    have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m27]; exact w26_2c
    have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m27]; exact w26_30
    have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m27]; exact w26_34
    have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m27]; exact w26_38
    have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m27]; exact w26_3c
    have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m27]; exact w26_40
    have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m27]; exact w26_44
    have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m27]; exact w26_48
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
    have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m27]; exact w26_74
    have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m27]; exact w26_78
    have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m27]; exact w26_7c
    have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m27]; exact w26_80
    have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m27]; exact w26_84
    have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m27]; exact w26_88
    have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m27]; exact w26_8c
    have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m27]; exact w26_90
    have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m27]; exact w26_94
    have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m27]; exact w26_98
    have w27_9c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m27]; exact w26_9c
    have w27_a0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m27]; exact w26_a0
    have w27_a4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m27]; exact w26_a4
    have w27_a8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m27]; exact w26_a8
    have w27_ac : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m27]; exact w26_ac
    have w27_b0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m27]; exact w26_b0
    have w27_b4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m27]; exact w26_b4
    have w27_b8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m27]; exact w26_b8
    have w27_bc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m27]; exact w26_bc
    have w27_c0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m27]; exact w26_c0
    have w27_c4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m27]; exact w26_c4
    have w27_c8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m27]; exact w26_c8
    have w27_cc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m27]; exact w26_cc
    have w27_d0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m27]; exact w26_d0
    have w27_d4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m27]; exact w26_d4
    have w27_d8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m27]; exact w26_d8
    have w27_dc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m27]; exact w26_dc
    have w27_e0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m27]; exact w26_e0
    have w27_e4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m27]; exact w26_e4
    have w27_e8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m27]; exact w26_e8
    have w27_ec : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m27]; exact w26_ec
    have w27_f0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m27]; exact w26_f0
    have w27_f4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m27]; exact w26_f4
    have w27_f8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m27]; exact w26_f8
    have w27_fc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m27]; exact w26_fc
    have w27_100 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m27]; exact w26_100
    have w27_104 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m27]; exact w26_104
    have w27_108 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m27]; exact w26_108
    have w27_10c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m27]; exact w26_10c
    have w27_110 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m27]; exact w26_110
    have w27_114 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m27]; exact w26_114
    have w27_118 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m27]; exact w26_118
    have w27_11c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m27]; exact w26_11c
    have w27_120 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m27]; exact w26_120
    have w27_124 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m27]; exact w26_124
    have w27_128 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m27]; exact w26_128
    have w27_12c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m27]; exact w26_12c
    have w27_130 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m27]; exact w26_130
    have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m27]; exact w26_420
    have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m27]; exact w26_a20
    have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m27]; exact w26_a24
    have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m27]; exact w26_a28
    have w27_a2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m27]; exact w26_a2c
    have w27_a30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m27]; exact w26_a30
    have w27_a34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m27]; exact w26_a34
    have w27_a38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m27]; exact w26_a38
    have w27_a3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m27]; exact w26_a3c
    have w27_aa0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m27]; exact w26_aa0
    have w27_aa4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m27]; exact w26_aa4
    have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m27]; exact b26_424
    clear b26_424 w26_aa4 w26_aa0 w26_a3c w26_a38 w26_a34 w26_a30 w26_a2c w26_a28 w26_a24 w26_a20 w26_420 w26_130 w26_12c w26_128 w26_124 w26_120 w26_11c w26_118 w26_114 w26_110 w26_10c w26_108 w26_104 w26_100 w26_fc w26_f8 w26_f4 w26_f0 w26_ec w26_e8 w26_e4 w26_e0 w26_dc w26_d8 w26_d4 w26_d0 w26_cc w26_c8 w26_c4 w26_c0 w26_bc w26_b8 w26_b4 w26_b0 w26_ac w26_a8 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 g26_23 g26_27 g26_26 g26_25 g26_24 g26_22 g26_21 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
    -- 0x2FEA: lbu
    obtain ⟨n28, d28, u28⟩ := s27.lbu E27.self sv_at_2fea (off' := 0x2FEE) (by decide)
    have s28 : St n28.mem SV n28 0x2FEE (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = dp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = 0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = dg := by rw [u28.regs, upd_ne (by decide) (by decide), g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = ckl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
    have w28_24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m28]; exact w27_24
    have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m28]; exact w27_28
    have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m28]; exact w27_2c
    have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m28]; exact w27_30
    have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m28]; exact w27_34
    have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m28]; exact w27_38
    have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m28]; exact w27_3c
    have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m28]; exact w27_40
    have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m28]; exact w27_44
    have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m28]; exact w27_48
    have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m28]; exact w27_4c
    have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m28]; exact w27_50
    have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m28]; exact w27_54
    have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m28]; exact w27_58
    have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m28]; exact w27_5c
    have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m28]; exact w27_60
    have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m28]; exact w27_64
    have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m28]; exact w27_68
    have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m28]; exact w27_6c
    have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m28]; exact w27_70
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m28]; exact w27_74
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m28]; exact w27_78
    have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m28]; exact w27_7c
    have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m28]; exact w27_80
    have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m28]; exact w27_84
    have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m28]; exact w27_88
    have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m28]; exact w27_8c
    have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m28]; exact w27_90
    have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m28]; exact w27_94
    have w28_98 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m28]; exact w27_98
    have w28_9c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m28]; exact w27_9c
    have w28_a0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m28]; exact w27_a0
    have w28_a4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m28]; exact w27_a4
    have w28_a8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m28]; exact w27_a8
    have w28_ac : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m28]; exact w27_ac
    have w28_b0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m28]; exact w27_b0
    have w28_b4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m28]; exact w27_b4
    have w28_b8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m28]; exact w27_b8
    have w28_bc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m28]; exact w27_bc
    have w28_c0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m28]; exact w27_c0
    have w28_c4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m28]; exact w27_c4
    have w28_c8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m28]; exact w27_c8
    have w28_cc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m28]; exact w27_cc
    have w28_d0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m28]; exact w27_d0
    have w28_d4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m28]; exact w27_d4
    have w28_d8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m28]; exact w27_d8
    have w28_dc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m28]; exact w27_dc
    have w28_e0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m28]; exact w27_e0
    have w28_e4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m28]; exact w27_e4
    have w28_e8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m28]; exact w27_e8
    have w28_ec : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m28]; exact w27_ec
    have w28_f0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m28]; exact w27_f0
    have w28_f4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m28]; exact w27_f4
    have w28_f8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m28]; exact w27_f8
    have w28_fc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m28]; exact w27_fc
    have w28_100 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m28]; exact w27_100
    have w28_104 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m28]; exact w27_104
    have w28_108 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m28]; exact w27_108
    have w28_10c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m28]; exact w27_10c
    have w28_110 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m28]; exact w27_110
    have w28_114 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m28]; exact w27_114
    have w28_118 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m28]; exact w27_118
    have w28_11c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m28]; exact w27_11c
    have w28_120 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m28]; exact w27_120
    have w28_124 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m28]; exact w27_124
    have w28_128 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m28]; exact w27_128
    have w28_12c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m28]; exact w27_12c
    have w28_130 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m28]; exact w27_130
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m28]; exact w27_420
    have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m28]; exact w27_a20
    have w28_a24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m28]; exact w27_a24
    have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m28]; exact w27_a28
    have w28_a2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m28]; exact w27_a2c
    have w28_a30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m28]; exact w27_a30
    have w28_a34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m28]; exact w27_a34
    have w28_a38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m28]; exact w27_a38
    have w28_a3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m28]; exact w27_a3c
    have w28_aa0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m28]; exact w27_aa0
    have w28_aa4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m28]; exact w27_aa4
    have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m28]; exact b27_424
    clear b27_424 w27_aa4 w27_aa0 w27_a3c w27_a38 w27_a34 w27_a30 w27_a2c w27_a28 w27_a24 w27_a20 w27_420 w27_130 w27_12c w27_128 w27_124 w27_120 w27_11c w27_118 w27_114 w27_110 w27_10c w27_108 w27_104 w27_100 w27_fc w27_f8 w27_f4 w27_f0 w27_ec w27_e8 w27_e4 w27_e0 w27_dc w27_d8 w27_d4 w27_d0 w27_cc w27_c8 w27_c4 w27_c0 w27_bc w27_b8 w27_b4 w27_b0 w27_ac w27_a8 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    -- 0x2FEE: j
    obtain ⟨n29, d29, u29⟩ := s28.jump E28.self sv_at_2fee (off' := 0x966) (by decide)
      (by rw [s28.pc]; decide)
    have s29 : St n29.mem SV n29 0x966 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u29.regs, g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u29.regs, g28_9]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
    have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = dp := by rw [u29.regs, g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = 0 := by rw [u29.regs, g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = dg := by rw [u29.regs, g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = ckl := by rw [u29.regs, g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, g28_27]
    have w29_24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m29]; exact w28_24
    have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m29]; exact w28_28
    have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m29]; exact w28_2c
    have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m29]; exact w28_30
    have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m29]; exact w28_34
    have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m29]; exact w28_38
    have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m29]; exact w28_3c
    have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m29]; exact w28_40
    have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m29]; exact w28_44
    have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m29]; exact w28_48
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
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m29]; exact w28_74
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m29]; exact w28_78
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m29]; exact w28_7c
    have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m29]; exact w28_80
    have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m29]; exact w28_84
    have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m29]; exact w28_88
    have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m29]; exact w28_8c
    have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m29]; exact w28_90
    have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m29]; exact w28_94
    have w29_98 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m29]; exact w28_98
    have w29_9c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m29]; exact w28_9c
    have w29_a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m29]; exact w28_a0
    have w29_a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m29]; exact w28_a4
    have w29_a8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m29]; exact w28_a8
    have w29_ac : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m29]; exact w28_ac
    have w29_b0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m29]; exact w28_b0
    have w29_b4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m29]; exact w28_b4
    have w29_b8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m29]; exact w28_b8
    have w29_bc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m29]; exact w28_bc
    have w29_c0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m29]; exact w28_c0
    have w29_c4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m29]; exact w28_c4
    have w29_c8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m29]; exact w28_c8
    have w29_cc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m29]; exact w28_cc
    have w29_d0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m29]; exact w28_d0
    have w29_d4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m29]; exact w28_d4
    have w29_d8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m29]; exact w28_d8
    have w29_dc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m29]; exact w28_dc
    have w29_e0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m29]; exact w28_e0
    have w29_e4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m29]; exact w28_e4
    have w29_e8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m29]; exact w28_e8
    have w29_ec : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m29]; exact w28_ec
    have w29_f0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m29]; exact w28_f0
    have w29_f4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m29]; exact w28_f4
    have w29_f8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m29]; exact w28_f8
    have w29_fc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m29]; exact w28_fc
    have w29_100 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m29]; exact w28_100
    have w29_104 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m29]; exact w28_104
    have w29_108 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m29]; exact w28_108
    have w29_10c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m29]; exact w28_10c
    have w29_110 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m29]; exact w28_110
    have w29_114 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m29]; exact w28_114
    have w29_118 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m29]; exact w28_118
    have w29_11c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m29]; exact w28_11c
    have w29_120 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m29]; exact w28_120
    have w29_124 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m29]; exact w28_124
    have w29_128 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m29]; exact w28_128
    have w29_12c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m29]; exact w28_12c
    have w29_130 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m29]; exact w28_130
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m29]; exact w28_420
    have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m29]; exact w28_a20
    have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m29]; exact w28_a24
    have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m29]; exact w28_a28
    have w29_a2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m29]; exact w28_a2c
    have w29_a30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m29]; exact w28_a30
    have w29_a34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m29]; exact w28_a34
    have w29_a38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m29]; exact w28_a38
    have w29_a3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m29]; exact w28_a3c
    have w29_aa0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m29]; exact w28_aa0
    have w29_aa4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m29]; exact w28_aa4
    have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m29]; exact b28_424
    clear b28_424 w28_aa4 w28_aa0 w28_a3c w28_a38 w28_a34 w28_a30 w28_a2c w28_a28 w28_a24 w28_a20 w28_420 w28_130 w28_12c w28_128 w28_124 w28_120 w28_11c w28_118 w28_114 w28_110 w28_10c w28_108 w28_104 w28_100 w28_fc w28_f8 w28_f4 w28_f0 w28_ec w28_e8 w28_e4 w28_e0 w28_dc w28_d8 w28_d4 w28_d0 w28_cc w28_c8 w28_c4 w28_c0 w28_bc w28_b8 w28_b4 w28_b0 w28_ac w28_a8 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 w28_2c w28_28 w28_24 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
    exact .inl ⟨(fun ⟨h0', ix7', h1', ix17', h2', ix25', h3', _⟩ => by rw [hr7] at h1'; cases h1'; rw [hr17] at h2'; cases h2'; rw [hr25] at h3'; cases h3'), sv_fail F E29 s29 t29 (fun x hx => (fR29 x hx).trans (fM x hx).symm) V29 hret g29_2 g29_18 hO g29_3 g29_4⟩
  have hix25 : ix25 < (((ckl).toNat) - (ix7 + 1)) - (ix17 + 1) := by have := (nlScan_lt _ _ _ hr25).2; omega
  rw [hr25] at L25
  obtain ⟨y0_25, y4_25, y8_25, y12_25⟩ := L25
  have w25_24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K25.w32 (by decide) (by decide)).trans w24_24
  have w25_28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K25.w32 (by decide) (by decide)).trans w24_28
  have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K25.w32 (by decide) (by decide)).trans w24_2c
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K25.w32 (by decide) (by decide)).trans w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K25.w32 (by decide) (by decide)).trans w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K25.w32 (by decide) (by decide)).trans w24_38
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K25.w32 (by decide) (by decide)).trans w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K25.w32 (by decide) (by decide)).trans w24_40
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := (K25.w32 (by decide) (by decide)).trans w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K25.w32 (by decide) (by decide)).trans w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K25.w32 (by decide) (by decide)).trans w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K25.w32 (by decide) (by decide)).trans w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K25.w32 (by decide) (by decide)).trans w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K25.w32 (by decide) (by decide)).trans w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K25.w32 (by decide) (by decide)).trans w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K25.w32 (by decide) (by decide)).trans w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K25.w32 (by decide) (by decide)).trans w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K25.w32 (by decide) (by decide)).trans w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K25.w32 (by decide) (by decide)).trans w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K25.w32 (by decide) (by decide)).trans w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K25.w32 (by decide) (by decide)).trans w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K25.w32 (by decide) (by decide)).trans w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K25.w32 (by decide) (by decide)).trans w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K25.w32 (by decide) (by decide)).trans w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K25.w32 (by decide) (by decide)).trans w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K25.w32 (by decide) (by decide)).trans w24_8c
  have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K25.w32 (by decide) (by decide)).trans w24_90
  have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K25.w32 (by decide) (by decide)).trans w24_94
  have w25_98 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K25.w32 (by decide) (by decide)).trans w24_98
  have w25_9c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K25.w32 (by decide) (by decide)).trans w24_9c
  have w25_a0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K25.w32 (by decide) (by decide)).trans w24_a0
  have w25_a4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K25.w32 (by decide) (by decide)).trans w24_a4
  have w25_a8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K25.w32 (by decide) (by decide)).trans w24_a8
  have w25_ac : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K25.w32 (by decide) (by decide)).trans w24_ac
  have w25_b0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K25.w32 (by decide) (by decide)).trans w24_b0
  have w25_b4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K25.w32 (by decide) (by decide)).trans w24_b4
  have w25_b8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K25.w32 (by decide) (by decide)).trans w24_b8
  have w25_bc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K25.w32 (by decide) (by decide)).trans w24_bc
  have w25_c0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K25.w32 (by decide) (by decide)).trans w24_c0
  have w25_c4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K25.w32 (by decide) (by decide)).trans w24_c4
  have w25_c8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K25.w32 (by decide) (by decide)).trans w24_c8
  have w25_cc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K25.w32 (by decide) (by decide)).trans w24_cc
  have w25_d0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K25.w32 (by decide) (by decide)).trans w24_d0
  have w25_d4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K25.w32 (by decide) (by decide)).trans w24_d4
  have w25_d8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K25.w32 (by decide) (by decide)).trans w24_d8
  have w25_dc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K25.w32 (by decide) (by decide)).trans w24_dc
  have w25_e0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K25.w32 (by decide) (by decide)).trans w24_e0
  have w25_e4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K25.w32 (by decide) (by decide)).trans w24_e4
  have w25_e8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K25.w32 (by decide) (by decide)).trans w24_e8
  have w25_ec : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K25.w32 (by decide) (by decide)).trans w24_ec
  have w25_f0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K25.w32 (by decide) (by decide)).trans w24_f0
  have w25_f4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K25.w32 (by decide) (by decide)).trans w24_f4
  have w25_f8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K25.w32 (by decide) (by decide)).trans w24_f8
  have w25_fc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K25.w32 (by decide) (by decide)).trans w24_fc
  have w25_100 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K25.w32 (by decide) (by decide)).trans w24_100
  have w25_104 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K25.w32 (by decide) (by decide)).trans w24_104
  have w25_108 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K25.w32 (by decide) (by decide)).trans w24_108
  have w25_10c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K25.w32 (by decide) (by decide)).trans w24_10c
  have w25_110 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K25.w32 (by decide) (by decide)).trans w24_110
  have w25_114 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K25.w32 (by decide) (by decide)).trans w24_114
  have w25_118 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K25.w32 (by decide) (by decide)).trans w24_118
  have w25_11c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K25.w32 (by decide) (by decide)).trans w24_11c
  have w25_120 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K25.w32 (by decide) (by decide)).trans w24_120
  have w25_124 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K25.w32 (by decide) (by decide)).trans w24_124
  have w25_128 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K25.w32 (by decide) (by decide)).trans w24_128
  have w25_12c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K25.w32 (by decide) (by decide)).trans w24_12c
  have w25_130 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K25.w32 (by decide) (by decide)).trans w24_130
  have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K25.w32 (by decide) (by decide)).trans w24_a20
  have w25_a24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K25.w32 (by decide) (by decide)).trans w24_a24
  have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K25.w32 (by decide) (by decide)).trans w24_a28
  have w25_a2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K25.w32 (by decide) (by decide)).trans w24_a2c
  have w25_a30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K25.w32 (by decide) (by decide)).trans w24_a30
  have w25_a34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K25.w32 (by decide) (by decide)).trans w24_a34
  have w25_a38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K25.w32 (by decide) (by decide)).trans w24_a38
  have w25_a3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K25.w32 (by decide) (by decide)).trans w24_a3c
  have w25_aa0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K25.w32 (by decide) (by decide)).trans w24_aa0
  have w25_aa4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K25.w32 (by decide) (by decide)).trans w24_aa4
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := y0_25
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix25 := y4_25
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := y8_25
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := y12_25
  clear w24_aa4 w24_aa0 w24_a3c w24_a38 w24_a34 w24_a30 w24_a2c w24_a28 w24_a24 w24_a20 w24_42c w24_428 w24_424 w24_420 w24_130 w24_12c w24_128 w24_124 w24_120 w24_11c w24_118 w24_114 w24_110 w24_10c w24_108 w24_104 w24_100 w24_fc w24_f8 w24_f4 w24_f0 w24_ec w24_e8 w24_e4 w24_e0 w24_dc w24_d8 w24_d4 w24_d0 w24_cc w24_c8 w24_c4 w24_c0 w24_bc w24_b8 w24_b4 w24_b0 w24_ac w24_a8 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_19 g24_18 g24_12 g24_11 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x2B90: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_2b90 (off' := 0x2B94) (by decide)
    (by rw [g25_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x2B94 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = dp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_24 : reg n26 (24 : Fin 32) = dg := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = ckl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_23 : reg n26 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w25_420]
  have w26_24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m26]; exact w25_24
  have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m26]; exact w25_28
  have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m26]; exact w25_2c
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m26]; exact w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m26]; exact w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m26]; exact w25_38
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m26]; exact w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m26]; exact w25_40
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m26]; exact w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m26]; exact w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m26]; exact w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m26]; exact w25_54
  have w26_58 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m26]; exact w25_58
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m26]; exact w25_5c
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m26]; exact w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m26]; exact w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m26]; exact w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m26]; exact w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m26]; exact w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m26]; exact w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m26]; exact w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m26]; exact w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m26]; exact w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m26]; exact w25_8c
  have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m26]; exact w25_90
  have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m26]; exact w25_94
  have w26_98 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m26]; exact w25_98
  have w26_9c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m26]; exact w25_9c
  have w26_a0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m26]; exact w25_a0
  have w26_a4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m26]; exact w25_a4
  have w26_a8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m26]; exact w25_a8
  have w26_ac : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m26]; exact w25_ac
  have w26_b0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m26]; exact w25_b0
  have w26_b4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m26]; exact w25_b4
  have w26_b8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m26]; exact w25_b8
  have w26_bc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m26]; exact w25_bc
  have w26_c0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m26]; exact w25_c0
  have w26_c4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m26]; exact w25_c4
  have w26_c8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m26]; exact w25_c8
  have w26_cc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m26]; exact w25_cc
  have w26_d0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m26]; exact w25_d0
  have w26_d4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m26]; exact w25_d4
  have w26_d8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m26]; exact w25_d8
  have w26_dc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m26]; exact w25_dc
  have w26_e0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m26]; exact w25_e0
  have w26_e4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m26]; exact w25_e4
  have w26_e8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m26]; exact w25_e8
  have w26_ec : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m26]; exact w25_ec
  have w26_f0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m26]; exact w25_f0
  have w26_f4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m26]; exact w25_f4
  have w26_f8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m26]; exact w25_f8
  have w26_fc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m26]; exact w25_fc
  have w26_100 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m26]; exact w25_100
  have w26_104 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m26]; exact w25_104
  have w26_108 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m26]; exact w25_108
  have w26_10c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m26]; exact w25_10c
  have w26_110 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m26]; exact w25_110
  have w26_114 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m26]; exact w25_114
  have w26_118 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m26]; exact w25_118
  have w26_11c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m26]; exact w25_11c
  have w26_120 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m26]; exact w25_120
  have w26_124 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m26]; exact w25_124
  have w26_128 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m26]; exact w25_128
  have w26_12c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m26]; exact w25_12c
  have w26_130 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m26]; exact w25_130
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m26]; exact w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix25 := by rw [m26]; exact w25_424
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m26]; exact w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := by rw [m26]; exact w25_42c
  have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m26]; exact w25_a20
  have w26_a24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m26]; exact w25_a24
  have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m26]; exact w25_a28
  have w26_a2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m26]; exact w25_a2c
  have w26_a30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m26]; exact w25_a30
  have w26_a34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m26]; exact w25_a34
  have w26_a38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m26]; exact w25_a38
  have w26_a3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m26]; exact w25_a3c
  have w26_aa0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m26]; exact w25_aa0
  have w26_aa4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m26]; exact w25_aa4
  clear w25_42c w25_428 w25_424 w25_420 w25_aa4 w25_aa0 w25_a3c w25_a38 w25_a34 w25_a30 w25_a2c w25_a28 w25_a24 w25_a20 w25_130 w25_12c w25_128 w25_124 w25_120 w25_11c w25_118 w25_114 w25_110 w25_10c w25_108 w25_104 w25_100 w25_fc w25_f8 w25_f4 w25_f0 w25_ec w25_e8 w25_e4 w25_e0 w25_dc w25_d8 w25_d4 w25_d0 w25_cc w25_c8 w25_c4 w25_c0 w25_bc w25_b8 w25_b4 w25_b0 w25_ac w25_a8 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_38 w25_34 w25_30 w25_2c w25_28 w25_24 y12_25 y8_25 y4_25 y0_25 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 K25 rk25 s25 c25
  -- 0x2B94: branch, not taken
  obtain ⟨n27, d27, u27⟩ := s26.notTaken E26.self 0x2B98 sv_at_2b94
    (by decide) (by rw [g26_23, s26.zero]; exact br_beq_f (line_rest (line_rest (.inl ck_in) hix7) hix17).ne0)
  have s27 : St n27.mem SV n27 0x2B98 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u27.regs, g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u27.regs, g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = dp := by rw [u27.regs, g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u27.regs, g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = dg := by rw [u27.regs, g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = ckl := by rw [u27.regs, g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u27.regs, g26_27]
  have w27_24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m27]; exact w26_24
  have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m27]; exact w26_28
  have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m27]; exact w26_2c
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m27]; exact w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m27]; exact w26_38
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m27]; exact w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m27]; exact w26_40
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m27]; exact w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m27]; exact w26_48
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
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m27]; exact w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m27]; exact w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m27]; exact w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m27]; exact w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m27]; exact w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m27]; exact w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m27]; exact w26_8c
  have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m27]; exact w26_90
  have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m27]; exact w26_94
  have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m27]; exact w26_98
  have w27_9c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m27]; exact w26_9c
  have w27_a0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m27]; exact w26_a0
  have w27_a4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m27]; exact w26_a4
  have w27_a8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m27]; exact w26_a8
  have w27_ac : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m27]; exact w26_ac
  have w27_b0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m27]; exact w26_b0
  have w27_b4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m27]; exact w26_b4
  have w27_b8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m27]; exact w26_b8
  have w27_bc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m27]; exact w26_bc
  have w27_c0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m27]; exact w26_c0
  have w27_c4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m27]; exact w26_c4
  have w27_c8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m27]; exact w26_c8
  have w27_cc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m27]; exact w26_cc
  have w27_d0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m27]; exact w26_d0
  have w27_d4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m27]; exact w26_d4
  have w27_d8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m27]; exact w26_d8
  have w27_dc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m27]; exact w26_dc
  have w27_e0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m27]; exact w26_e0
  have w27_e4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m27]; exact w26_e4
  have w27_e8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m27]; exact w26_e8
  have w27_ec : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m27]; exact w26_ec
  have w27_f0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m27]; exact w26_f0
  have w27_f4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m27]; exact w26_f4
  have w27_f8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m27]; exact w26_f8
  have w27_fc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m27]; exact w26_fc
  have w27_100 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m27]; exact w26_100
  have w27_104 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m27]; exact w26_104
  have w27_108 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m27]; exact w26_108
  have w27_10c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m27]; exact w26_10c
  have w27_110 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m27]; exact w26_110
  have w27_114 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m27]; exact w26_114
  have w27_118 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m27]; exact w26_118
  have w27_11c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m27]; exact w26_11c
  have w27_120 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m27]; exact w26_120
  have w27_124 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m27]; exact w26_124
  have w27_128 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m27]; exact w26_128
  have w27_12c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m27]; exact w26_12c
  have w27_130 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m27]; exact w26_130
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m27]; exact w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix25 := by rw [m27]; exact w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m27]; exact w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := by rw [m27]; exact w26_42c
  have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m27]; exact w26_a20
  have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m27]; exact w26_a24
  have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m27]; exact w26_a28
  have w27_a2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m27]; exact w26_a2c
  have w27_a30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m27]; exact w26_a30
  have w27_a34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m27]; exact w26_a34
  have w27_a38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m27]; exact w26_a38
  have w27_a3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m27]; exact w26_a3c
  have w27_aa0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m27]; exact w26_aa0
  have w27_aa4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m27]; exact w26_aa4
  clear w26_aa4 w26_aa0 w26_a3c w26_a38 w26_a34 w26_a30 w26_a2c w26_a28 w26_a24 w26_a20 w26_42c w26_428 w26_424 w26_420 w26_130 w26_12c w26_128 w26_124 w26_120 w26_11c w26_118 w26_114 w26_110 w26_10c w26_108 w26_104 w26_100 w26_fc w26_f8 w26_f4 w26_f0 w26_ec w26_e8 w26_e4 w26_e0 w26_dc w26_d8 w26_d4 w26_d0 w26_cc w26_c8 w26_c4 w26_c0 w26_bc w26_b8 w26_b4 w26_b0 w26_ac w26_a8 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 g26_23 g26_27 g26_26 g26_25 g26_24 g26_22 g26_21 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x2B98
  obtain ⟨n28, c28, u28⟩ := s27.block svCk12b98 E27.self svCk12b98_end
    ⟨trivial, trivial⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have s28 : St n28.mem SV n28 0x2B9C (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have rb28 : ∀ q, reg n28 q = (runBlock svCk12b98 (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by
    rw [rb28, runBlock_reg _ _ _ sp s27.zero (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (3 : Fin 32) s27.zero (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (4 : Fin 32) s27.zero (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by
    rw [rb28, runBlock_reg _ _ _ (8 : Fin 32) s27.zero (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by
    rw [rb28, runBlock_reg _ _ _ (9 : Fin 32) s27.zero (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by
    rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by
    rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by
    rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = dp := by
    rw [rb28, runBlock_reg _ _ _ (22 : Fin 32) s27.zero (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by
    rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = dg := by
    rw [rb28, runBlock_reg _ _ _ (24 : Fin 32) s27.zero (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = ckl := by
    rw [rb28, runBlock_reg _ _ _ (25 : Fin 32) s27.zero (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by
    rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
  have g28_10 : reg n28 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, svCk12b98, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_18, g27_19, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, s27.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w28_24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m28]; exact w27_24
  have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m28]; exact w27_28
  have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m28]; exact w27_2c
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m28]; exact w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m28]; exact w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m28]; exact w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m28]; exact w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m28]; exact w27_40
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m28]; exact w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m28]; exact w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m28]; exact w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m28]; exact w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m28]; exact w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m28]; exact w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m28]; exact w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m28]; exact w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m28]; exact w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m28]; exact w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m28]; exact w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m28]; exact w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m28]; exact w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m28]; exact w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m28]; exact w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m28]; exact w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m28]; exact w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m28]; exact w27_88
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m28]; exact w27_8c
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m28]; exact w27_90
  have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m28]; exact w27_94
  have w28_98 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m28]; exact w27_98
  have w28_9c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m28]; exact w27_9c
  have w28_a0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m28]; exact w27_a0
  have w28_a4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m28]; exact w27_a4
  have w28_a8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m28]; exact w27_a8
  have w28_ac : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m28]; exact w27_ac
  have w28_b0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m28]; exact w27_b0
  have w28_b4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m28]; exact w27_b4
  have w28_b8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m28]; exact w27_b8
  have w28_bc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m28]; exact w27_bc
  have w28_c0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m28]; exact w27_c0
  have w28_c4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m28]; exact w27_c4
  have w28_c8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m28]; exact w27_c8
  have w28_cc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m28]; exact w27_cc
  have w28_d0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m28]; exact w27_d0
  have w28_d4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m28]; exact w27_d4
  have w28_d8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m28]; exact w27_d8
  have w28_dc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m28]; exact w27_dc
  have w28_e0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m28]; exact w27_e0
  have w28_e4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m28]; exact w27_e4
  have w28_e8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m28]; exact w27_e8
  have w28_ec : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m28]; exact w27_ec
  have w28_f0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m28]; exact w27_f0
  have w28_f4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m28]; exact w27_f4
  have w28_f8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m28]; exact w27_f8
  have w28_fc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m28]; exact w27_fc
  have w28_100 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m28]; exact w27_100
  have w28_104 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m28]; exact w27_104
  have w28_108 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m28]; exact w27_108
  have w28_10c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m28]; exact w27_10c
  have w28_110 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m28]; exact w27_110
  have w28_114 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m28]; exact w27_114
  have w28_118 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m28]; exact w27_118
  have w28_11c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m28]; exact w27_11c
  have w28_120 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m28]; exact w27_120
  have w28_124 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m28]; exact w27_124
  have w28_128 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m28]; exact w27_128
  have w28_12c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m28]; exact w27_12c
  have w28_130 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m28]; exact w27_130
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m28]; exact w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix25 := by rw [m28]; exact w27_424
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m28]; exact w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := by rw [m28]; exact w27_42c
  have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m28]; exact w27_a20
  have w28_a24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m28]; exact w27_a24
  have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m28]; exact w27_a28
  have w28_a2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m28]; exact w27_a2c
  have w28_a30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m28]; exact w27_a30
  have w28_a34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m28]; exact w27_a34
  have w28_a38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m28]; exact w27_a38
  have w28_a3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m28]; exact w27_a3c
  have w28_aa0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m28]; exact w27_aa0
  have w28_aa4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m28]; exact w27_aa4
  clear w27_aa4 w27_aa0 w27_a3c w27_a38 w27_a34 w27_a30 w27_a2c w27_a28 w27_a24 w27_a20 w27_42c w27_428 w27_424 w27_420 w27_130 w27_12c w27_128 w27_124 w27_120 w27_11c w27_118 w27_114 w27_110 w27_10c w27_108 w27_104 w27_100 w27_fc w27_f8 w27_f4 w27_f0 w27_ec w27_e8 w27_e4 w27_e0 w27_dc w27_d8 w27_d4 w27_d0 w27_cc w27_c8 w27_c4 w27_c0 w27_bc w27_b8 w27_b4 w27_b0 w27_ac w27_a8 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0x2B9C: lw
  obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_2b9c (off' := 0x2BA0) (by decide)
    (by rw [g28_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s29 : St n29.mem SV n29 0x2BA0 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_10]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_23 : reg n29 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = dg := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = ckl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_22 : reg n29 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x24 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w28_424]
  have w29_24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m29]; exact w28_24
  have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m29]; exact w28_28
  have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m29]; exact w28_2c
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m29]; exact w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m29]; exact w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m29]; exact w28_38
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m29]; exact w28_3c
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m29]; exact w28_40
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m29]; exact w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m29]; exact w28_48
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
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m29]; exact w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m29]; exact w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m29]; exact w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m29]; exact w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m29]; exact w28_8c
  have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m29]; exact w28_90
  have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m29]; exact w28_94
  have w29_98 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m29]; exact w28_98
  have w29_9c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m29]; exact w28_9c
  have w29_a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m29]; exact w28_a0
  have w29_a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m29]; exact w28_a4
  have w29_a8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m29]; exact w28_a8
  have w29_ac : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m29]; exact w28_ac
  have w29_b0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m29]; exact w28_b0
  have w29_b4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m29]; exact w28_b4
  have w29_b8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m29]; exact w28_b8
  have w29_bc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m29]; exact w28_bc
  have w29_c0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m29]; exact w28_c0
  have w29_c4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m29]; exact w28_c4
  have w29_c8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m29]; exact w28_c8
  have w29_cc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m29]; exact w28_cc
  have w29_d0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m29]; exact w28_d0
  have w29_d4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m29]; exact w28_d4
  have w29_d8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m29]; exact w28_d8
  have w29_dc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m29]; exact w28_dc
  have w29_e0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m29]; exact w28_e0
  have w29_e4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m29]; exact w28_e4
  have w29_e8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m29]; exact w28_e8
  have w29_ec : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m29]; exact w28_ec
  have w29_f0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m29]; exact w28_f0
  have w29_f4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m29]; exact w28_f4
  have w29_f8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m29]; exact w28_f8
  have w29_fc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m29]; exact w28_fc
  have w29_100 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m29]; exact w28_100
  have w29_104 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m29]; exact w28_104
  have w29_108 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m29]; exact w28_108
  have w29_10c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m29]; exact w28_10c
  have w29_110 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m29]; exact w28_110
  have w29_114 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m29]; exact w28_114
  have w29_118 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m29]; exact w28_118
  have w29_11c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m29]; exact w28_11c
  have w29_120 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m29]; exact w28_120
  have w29_124 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m29]; exact w28_124
  have w29_128 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m29]; exact w28_128
  have w29_12c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m29]; exact w28_12c
  have w29_130 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m29]; exact w28_130
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix25 := by rw [m29]; exact w28_424
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m29]; exact w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := by rw [m29]; exact w28_42c
  have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m29]; exact w28_a20
  have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m29]; exact w28_a24
  have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m29]; exact w28_a28
  have w29_a2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m29]; exact w28_a2c
  have w29_a30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m29]; exact w28_a30
  have w29_a34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m29]; exact w28_a34
  have w29_a38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m29]; exact w28_a38
  have w29_a3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m29]; exact w28_a3c
  have w29_aa0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m29]; exact w28_aa0
  have w29_aa4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m29]; exact w28_aa4
  clear w28_aa4 w28_aa0 w28_a3c w28_a38 w28_a34 w28_a30 w28_a2c w28_a28 w28_a24 w28_a20 w28_42c w28_428 w28_424 w28_420 w28_130 w28_12c w28_128 w28_124 w28_120 w28_11c w28_118 w28_114 w28_110 w28_10c w28_108 w28_104 w28_100 w28_fc w28_f8 w28_f4 w28_f0 w28_ec w28_e8 w28_e4 w28_e0 w28_dc w28_d8 w28_d4 w28_d0 w28_cc w28_c8 w28_c4 w28_c0 w28_bc w28_b8 w28_b4 w28_b0 w28_ac w28_a8 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 w28_2c w28_28 w28_24 g28_10 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
  -- 0x2BA0: lw
  obtain ⟨n30, d30, u30⟩ := s29.lw E29.self sv_at_2ba0 (off' := 0x2BA2) (by decide)
    (by rw [g29_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s30 : St n30.mem SV n30 0x2BA2 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_9]
  have g30_10 : reg n30 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, upd_ne (by decide) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_19]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = dg := by rw [u30.regs, upd_ne (by decide) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = ckl := by rw [u30.regs, upd_ne (by decide) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_27]
  have g30_11 : reg n30 a1 = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by
    rw [u30.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g29_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w29_428]
  have w30_24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m30]; exact w29_24
  have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m30]; exact w29_28
  have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m30]; exact w29_2c
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m30]; exact w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m30]; exact w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m30]; exact w29_38
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m30]; exact w29_3c
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m30]; exact w29_40
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m30]; exact w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m30]; exact w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m30]; exact w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m30]; exact w29_50
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m30]; exact w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m30]; exact w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m30]; exact w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m30]; exact w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m30]; exact w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m30]; exact w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m30]; exact w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m30]; exact w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m30]; exact w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m30]; exact w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m30]; exact w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m30]; exact w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m30]; exact w29_84
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m30]; exact w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m30]; exact w29_8c
  have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m30]; exact w29_90
  have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m30]; exact w29_94
  have w30_98 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m30]; exact w29_98
  have w30_9c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m30]; exact w29_9c
  have w30_a0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m30]; exact w29_a0
  have w30_a4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m30]; exact w29_a4
  have w30_a8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m30]; exact w29_a8
  have w30_ac : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m30]; exact w29_ac
  have w30_b0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m30]; exact w29_b0
  have w30_b4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m30]; exact w29_b4
  have w30_b8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m30]; exact w29_b8
  have w30_bc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m30]; exact w29_bc
  have w30_c0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m30]; exact w29_c0
  have w30_c4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m30]; exact w29_c4
  have w30_c8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m30]; exact w29_c8
  have w30_cc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m30]; exact w29_cc
  have w30_d0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m30]; exact w29_d0
  have w30_d4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m30]; exact w29_d4
  have w30_d8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m30]; exact w29_d8
  have w30_dc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m30]; exact w29_dc
  have w30_e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m30]; exact w29_e0
  have w30_e4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m30]; exact w29_e4
  have w30_e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m30]; exact w29_e8
  have w30_ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m30]; exact w29_ec
  have w30_f0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m30]; exact w29_f0
  have w30_f4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m30]; exact w29_f4
  have w30_f8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m30]; exact w29_f8
  have w30_fc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m30]; exact w29_fc
  have w30_100 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m30]; exact w29_100
  have w30_104 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m30]; exact w29_104
  have w30_108 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m30]; exact w29_108
  have w30_10c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m30]; exact w29_10c
  have w30_110 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m30]; exact w29_110
  have w30_114 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m30]; exact w29_114
  have w30_118 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m30]; exact w29_118
  have w30_11c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m30]; exact w29_11c
  have w30_120 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m30]; exact w29_120
  have w30_124 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m30]; exact w29_124
  have w30_128 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m30]; exact w29_128
  have w30_12c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m30]; exact w29_12c
  have w30_130 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m30]; exact w29_130
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m30]; exact w29_420
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix25 := by rw [m30]; exact w29_424
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m30]; exact w29_428
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := by rw [m30]; exact w29_42c
  have w30_a20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m30]; exact w29_a20
  have w30_a24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m30]; exact w29_a24
  have w30_a28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m30]; exact w29_a28
  have w30_a2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m30]; exact w29_a2c
  have w30_a30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m30]; exact w29_a30
  have w30_a34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m30]; exact w29_a34
  have w30_a38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m30]; exact w29_a38
  have w30_a3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m30]; exact w29_a3c
  have w30_aa0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m30]; exact w29_aa0
  have w30_aa4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m30]; exact w29_aa4
  clear w29_aa4 w29_aa0 w29_a3c w29_a38 w29_a34 w29_a30 w29_a2c w29_a28 w29_a24 w29_a20 w29_42c w29_428 w29_424 w29_420 w29_130 w29_12c w29_128 w29_124 w29_120 w29_11c w29_118 w29_114 w29_110 w29_10c w29_108 w29_104 w29_100 w29_fc w29_f8 w29_f4 w29_f0 w29_ec w29_e8 w29_e4 w29_e0 w29_dc w29_d8 w29_d4 w29_d0 w29_cc w29_c8 w29_c4 w29_c0 w29_bc w29_b8 w29_b4 w29_b0 w29_ac w29_a8 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 w29_2c w29_28 w29_24 g29_22 g29_27 g29_26 g29_25 g29_24 g29_23 g29_21 g29_19 g29_18 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0x2BA2: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_2ba2 (off' := 0x2BA4) (by decide)
    (by rw [g30_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0x2BA4 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
  have g31_10 : reg n31 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_10]
  have g31_11 : reg n31 a1 = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_11]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = dg := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = ckl := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_12 : reg n31 a2 = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_10, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w30_42c]
  have w31_24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m31]; exact w30_24
  have w31_28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m31]; exact w30_28
  have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m31]; exact w30_2c
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m31]; exact w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m31]; exact w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m31]; exact w30_38
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m31]; exact w30_3c
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m31]; exact w30_40
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m31]; exact w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m31]; exact w30_48
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
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m31]; exact w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m31]; exact w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m31]; exact w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m31]; exact w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m31]; exact w30_84
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m31]; exact w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m31]; exact w30_8c
  have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m31]; exact w30_90
  have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m31]; exact w30_94
  have w31_98 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m31]; exact w30_98
  have w31_9c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m31]; exact w30_9c
  have w31_a0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m31]; exact w30_a0
  have w31_a4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m31]; exact w30_a4
  have w31_a8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m31]; exact w30_a8
  have w31_ac : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m31]; exact w30_ac
  have w31_b0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m31]; exact w30_b0
  have w31_b4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m31]; exact w30_b4
  have w31_b8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m31]; exact w30_b8
  have w31_bc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m31]; exact w30_bc
  have w31_c0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m31]; exact w30_c0
  have w31_c4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m31]; exact w30_c4
  have w31_c8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m31]; exact w30_c8
  have w31_cc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m31]; exact w30_cc
  have w31_d0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m31]; exact w30_d0
  have w31_d4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m31]; exact w30_d4
  have w31_d8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m31]; exact w30_d8
  have w31_dc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m31]; exact w30_dc
  have w31_e0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m31]; exact w30_e0
  have w31_e4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m31]; exact w30_e4
  have w31_e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m31]; exact w30_e8
  have w31_ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m31]; exact w30_ec
  have w31_f0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m31]; exact w30_f0
  have w31_f4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m31]; exact w30_f4
  have w31_f8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m31]; exact w30_f8
  have w31_fc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m31]; exact w30_fc
  have w31_100 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m31]; exact w30_100
  have w31_104 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m31]; exact w30_104
  have w31_108 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m31]; exact w30_108
  have w31_10c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m31]; exact w30_10c
  have w31_110 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m31]; exact w30_110
  have w31_114 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m31]; exact w30_114
  have w31_118 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m31]; exact w30_118
  have w31_11c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m31]; exact w30_11c
  have w31_120 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m31]; exact w30_120
  have w31_124 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m31]; exact w30_124
  have w31_128 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m31]; exact w30_128
  have w31_12c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m31]; exact w30_12c
  have w31_130 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m31]; exact w30_130
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m31]; exact w30_420
  have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix25 := by rw [m31]; exact w30_424
  have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m31]; exact w30_428
  have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := by rw [m31]; exact w30_42c
  have w31_a20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m31]; exact w30_a20
  have w31_a24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m31]; exact w30_a24
  have w31_a28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m31]; exact w30_a28
  have w31_a2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m31]; exact w30_a2c
  have w31_a30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m31]; exact w30_a30
  have w31_a34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m31]; exact w30_a34
  have w31_a38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m31]; exact w30_a38
  have w31_a3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m31]; exact w30_a3c
  have w31_aa0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m31]; exact w30_aa0
  have w31_aa4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m31]; exact w30_aa4
  clear w30_aa4 w30_aa0 w30_a3c w30_a38 w30_a34 w30_a30 w30_a2c w30_a28 w30_a24 w30_a20 w30_42c w30_428 w30_424 w30_420 w30_130 w30_12c w30_128 w30_124 w30_120 w30_11c w30_118 w30_114 w30_110 w30_10c w30_108 w30_104 w30_100 w30_fc w30_f8 w30_f4 w30_f0 w30_ec w30_e8 w30_e4 w30_e0 w30_dc w30_d8 w30_d4 w30_d0 w30_cc w30_c8 w30_c4 w30_c0 w30_bc w30_b8 w30_b4 w30_b0 w30_ac w30_a8 w30_a4 w30_a0 w30_9c w30_98 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_44 w30_40 w30_3c w30_38 w30_34 w30_30 w30_2c w30_28 w30_24 g30_11 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  -- 0x2BA4
  obtain ⟨n32, c32, u32⟩ := s31.block svCk12ba4 E31.self svCk12ba4_end
    ⟨trivial, trivial⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have s32 : St n32.mem SV n32 0x2BA8 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have rb32 : ∀ q, reg n32 q = (runBlock svCk12ba4 (n31.mem, reg n31)).2 q := fun q => by rw [u32.regs]
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans c32
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by
    rw [rb32, runBlock_reg _ _ _ sp s31.zero (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb32, runBlock_reg _ _ _ (3 : Fin 32) s31.zero (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb32, runBlock_reg _ _ _ (4 : Fin 32) s31.zero (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by
    rw [rb32, runBlock_reg _ _ _ (8 : Fin 32) s31.zero (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by
    rw [rb32, runBlock_reg _ _ _ (9 : Fin 32) s31.zero (by decide), g31_9]
  have g32_11 : reg n32 a1 = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by
    rw [rb32, runBlock_reg _ _ _ a1 s31.zero (by decide), g31_11]
  have g32_12 : reg n32 a2 = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := by
    rw [rb32, runBlock_reg _ _ _ a2 s31.zero (by decide), g31_12]
  have g32_18 : reg n32 (18 : Fin 32) = out := by
    rw [rb32, runBlock_reg _ _ _ (18 : Fin 32) s31.zero (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by
    rw [rb32, runBlock_reg _ _ _ (19 : Fin 32) s31.zero (by decide), g31_19]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by
    rw [rb32, runBlock_reg _ _ _ (21 : Fin 32) s31.zero (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by
    rw [rb32, runBlock_reg _ _ _ (22 : Fin 32) s31.zero (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by
    rw [rb32, runBlock_reg _ _ _ (23 : Fin 32) s31.zero (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = dg := by
    rw [rb32, runBlock_reg _ _ _ (24 : Fin 32) s31.zero (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = ckl := by
    rw [rb32, runBlock_reg _ _ _ (25 : Fin 32) s31.zero (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by
    rw [rb32, runBlock_reg _ _ _ (26 : Fin 32) s31.zero (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb32, runBlock_reg _ _ _ (27 : Fin 32) s31.zero (by decide), g31_27]
  have g32_10 : reg n32 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, svCk12ba4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_9, g31_10, g31_11, g31_12, g31_18, g31_19, g31_21, g31_22, g31_23, g31_24, g31_25, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w32_24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m32]; exact w31_24
  have w32_28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m32]; exact w31_28
  have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m32]; exact w31_2c
  have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m32]; exact w31_30
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m32]; exact w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m32]; exact w31_38
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m32]; exact w31_3c
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m32]; exact w31_40
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m32]; exact w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m32]; exact w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m32]; exact w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m32]; exact w31_50
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m32]; exact w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m32]; exact w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m32]; exact w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m32]; exact w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m32]; exact w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m32]; exact w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m32]; exact w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m32]; exact w31_70
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m32]; exact w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m32]; exact w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m32]; exact w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m32]; exact w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m32]; exact w31_84
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m32]; exact w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m32]; exact w31_8c
  have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m32]; exact w31_90
  have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m32]; exact w31_94
  have w32_98 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m32]; exact w31_98
  have w32_9c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m32]; exact w31_9c
  have w32_a0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m32]; exact w31_a0
  have w32_a4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m32]; exact w31_a4
  have w32_a8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m32]; exact w31_a8
  have w32_ac : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m32]; exact w31_ac
  have w32_b0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m32]; exact w31_b0
  have w32_b4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m32]; exact w31_b4
  have w32_b8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m32]; exact w31_b8
  have w32_bc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m32]; exact w31_bc
  have w32_c0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m32]; exact w31_c0
  have w32_c4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m32]; exact w31_c4
  have w32_c8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m32]; exact w31_c8
  have w32_cc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m32]; exact w31_cc
  have w32_d0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m32]; exact w31_d0
  have w32_d4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m32]; exact w31_d4
  have w32_d8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m32]; exact w31_d8
  have w32_dc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m32]; exact w31_dc
  have w32_e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m32]; exact w31_e0
  have w32_e4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m32]; exact w31_e4
  have w32_e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m32]; exact w31_e8
  have w32_ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m32]; exact w31_ec
  have w32_f0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m32]; exact w31_f0
  have w32_f4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m32]; exact w31_f4
  have w32_f8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m32]; exact w31_f8
  have w32_fc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m32]; exact w31_fc
  have w32_100 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m32]; exact w31_100
  have w32_104 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m32]; exact w31_104
  have w32_108 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m32]; exact w31_108
  have w32_10c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m32]; exact w31_10c
  have w32_110 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m32]; exact w31_110
  have w32_114 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m32]; exact w31_114
  have w32_118 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m32]; exact w31_118
  have w32_11c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m32]; exact w31_11c
  have w32_120 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m32]; exact w31_120
  have w32_124 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m32]; exact w31_124
  have w32_128 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m32]; exact w31_128
  have w32_12c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m32]; exact w31_12c
  have w32_130 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m32]; exact w31_130
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [m32]; exact w31_420
  have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix25 := by rw [m32]; exact w31_424
  have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m32]; exact w31_428
  have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - BitVec.ofNat 32 (ix25 + 1) := by rw [m32]; exact w31_42c
  have w32_a20 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m32]; exact w31_a20
  have w32_a24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m32]; exact w31_a24
  have w32_a28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m32]; exact w31_a28
  have w32_a2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m32]; exact w31_a2c
  have w32_a30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m32]; exact w31_a30
  have w32_a34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m32]; exact w31_a34
  have w32_a38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m32]; exact w31_a38
  have w32_a3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m32]; exact w31_a3c
  have w32_aa0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m32]; exact w31_aa0
  have w32_aa4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m32]; exact w31_aa4
  clear w31_aa4 w31_aa0 w31_a3c w31_a38 w31_a34 w31_a30 w31_a2c w31_a28 w31_a24 w31_a20 w31_42c w31_428 w31_424 w31_420 w31_130 w31_12c w31_128 w31_124 w31_120 w31_11c w31_118 w31_114 w31_110 w31_10c w31_108 w31_104 w31_100 w31_fc w31_f8 w31_f4 w31_f0 w31_ec w31_e8 w31_e4 w31_e0 w31_dc w31_d8 w31_d4 w31_d0 w31_cc w31_c8 w31_c4 w31_c0 w31_bc w31_b8 w31_b4 w31_b0 w31_ac w31_a8 w31_a4 w31_a0 w31_9c w31_98 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_44 w31_40 w31_3c w31_38 w31_34 w31_30 w31_2c w31_28 w31_24 g31_12 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_19 g31_18 g31_11 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x2BA8: sv_lineF
  obtain ⟨n33, c33, s33, rk33, K33, L33, fr33⟩ := sv_lineF (oc := 0x420) (nl := ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1))
    F E32 (CK0.sv F fR32) s32 sv_at_2ba8 sv_at_2bac (by decide) (by decide)
    g32_10 g32_11 (by rw [g32_12, sub_ofNat (Nat.succ_le_of_lt hix25) (by omega)]) (by decide) (by decide) (line_rest (line_rest (line_rest (.inl ck_in) hix7) hix17) hix25)
  have t33 : Steps n0 n33 := t32.trans c33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.keepL K33 (by decide)
  rw [nlScan_ro F fR32 (line_rest (line_rest (line_rest (.inl ck_in) hix7) hix17) hix25)] at L33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [rk33 sp (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk33 (3 : Fin 32) (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk33 (4 : Fin 32) (by decide), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [rk33 (8 : Fin 32) (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [rk33 (9 : Fin 32) (by decide), g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [rk33 (18 : Fin 32) (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [rk33 (19 : Fin 32) (by decide), g32_19]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [rk33 (21 : Fin 32) (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [rk33 (22 : Fin 32) (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [rk33 (23 : Fin 32) (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = dg := by rw [rk33 (24 : Fin 32) (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = ckl := by rw [rk33 (25 : Fin 32) (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [rk33 (26 : Fin 32) (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk33 (27 : Fin 32) (by decide), g32_27]
  obtain ⟨r33, hr33⟩ : ∃ r, nlScan M0 ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) 0 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) = r := ⟨_, rfl⟩
  rcases r33 with _ | ix33
  · rw [hr33] at L33
    obtain ⟨z0_33, z4_33⟩ := L33
    have w33_24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K33.w32 (by decide) (by decide)).trans w32_24
    have w33_28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K33.w32 (by decide) (by decide)).trans w32_28
    have w33_2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K33.w32 (by decide) (by decide)).trans w32_2c
    have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K33.w32 (by decide) (by decide)).trans w32_30
    have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K33.w32 (by decide) (by decide)).trans w32_34
    have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K33.w32 (by decide) (by decide)).trans w32_38
    have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K33.w32 (by decide) (by decide)).trans w32_3c
    have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K33.w32 (by decide) (by decide)).trans w32_40
    have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := (K33.w32 (by decide) (by decide)).trans w32_44
    have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K33.w32 (by decide) (by decide)).trans w32_48
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
    have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K33.w32 (by decide) (by decide)).trans w32_74
    have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K33.w32 (by decide) (by decide)).trans w32_78
    have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K33.w32 (by decide) (by decide)).trans w32_7c
    have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K33.w32 (by decide) (by decide)).trans w32_80
    have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K33.w32 (by decide) (by decide)).trans w32_84
    have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K33.w32 (by decide) (by decide)).trans w32_88
    have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K33.w32 (by decide) (by decide)).trans w32_8c
    have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K33.w32 (by decide) (by decide)).trans w32_90
    have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K33.w32 (by decide) (by decide)).trans w32_94
    have w33_98 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K33.w32 (by decide) (by decide)).trans w32_98
    have w33_9c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K33.w32 (by decide) (by decide)).trans w32_9c
    have w33_a0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K33.w32 (by decide) (by decide)).trans w32_a0
    have w33_a4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K33.w32 (by decide) (by decide)).trans w32_a4
    have w33_a8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K33.w32 (by decide) (by decide)).trans w32_a8
    have w33_ac : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K33.w32 (by decide) (by decide)).trans w32_ac
    have w33_b0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K33.w32 (by decide) (by decide)).trans w32_b0
    have w33_b4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K33.w32 (by decide) (by decide)).trans w32_b4
    have w33_b8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K33.w32 (by decide) (by decide)).trans w32_b8
    have w33_bc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K33.w32 (by decide) (by decide)).trans w32_bc
    have w33_c0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K33.w32 (by decide) (by decide)).trans w32_c0
    have w33_c4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K33.w32 (by decide) (by decide)).trans w32_c4
    have w33_c8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K33.w32 (by decide) (by decide)).trans w32_c8
    have w33_cc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K33.w32 (by decide) (by decide)).trans w32_cc
    have w33_d0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K33.w32 (by decide) (by decide)).trans w32_d0
    have w33_d4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K33.w32 (by decide) (by decide)).trans w32_d4
    have w33_d8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K33.w32 (by decide) (by decide)).trans w32_d8
    have w33_dc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K33.w32 (by decide) (by decide)).trans w32_dc
    have w33_e0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K33.w32 (by decide) (by decide)).trans w32_e0
    have w33_e4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K33.w32 (by decide) (by decide)).trans w32_e4
    have w33_e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K33.w32 (by decide) (by decide)).trans w32_e8
    have w33_ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K33.w32 (by decide) (by decide)).trans w32_ec
    have w33_f0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K33.w32 (by decide) (by decide)).trans w32_f0
    have w33_f4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K33.w32 (by decide) (by decide)).trans w32_f4
    have w33_f8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K33.w32 (by decide) (by decide)).trans w32_f8
    have w33_fc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K33.w32 (by decide) (by decide)).trans w32_fc
    have w33_100 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K33.w32 (by decide) (by decide)).trans w32_100
    have w33_104 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K33.w32 (by decide) (by decide)).trans w32_104
    have w33_108 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K33.w32 (by decide) (by decide)).trans w32_108
    have w33_10c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K33.w32 (by decide) (by decide)).trans w32_10c
    have w33_110 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K33.w32 (by decide) (by decide)).trans w32_110
    have w33_114 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K33.w32 (by decide) (by decide)).trans w32_114
    have w33_118 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K33.w32 (by decide) (by decide)).trans w32_118
    have w33_11c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K33.w32 (by decide) (by decide)).trans w32_11c
    have w33_120 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K33.w32 (by decide) (by decide)).trans w32_120
    have w33_124 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K33.w32 (by decide) (by decide)).trans w32_124
    have w33_128 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K33.w32 (by decide) (by decide)).trans w32_128
    have w33_12c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K33.w32 (by decide) (by decide)).trans w32_12c
    have w33_130 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K33.w32 (by decide) (by decide)).trans w32_130
    have w33_a20 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K33.w32 (by decide) (by decide)).trans w32_a20
    have w33_a24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K33.w32 (by decide) (by decide)).trans w32_a24
    have w33_a28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K33.w32 (by decide) (by decide)).trans w32_a28
    have w33_a2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K33.w32 (by decide) (by decide)).trans w32_a2c
    have w33_a30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K33.w32 (by decide) (by decide)).trans w32_a30
    have w33_a34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K33.w32 (by decide) (by decide)).trans w32_a34
    have w33_a38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K33.w32 (by decide) (by decide)).trans w32_a38
    have w33_a3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K33.w32 (by decide) (by decide)).trans w32_a3c
    have w33_aa0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K33.w32 (by decide) (by decide)).trans w32_aa0
    have w33_aa4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K33.w32 (by decide) (by decide)).trans w32_aa4
    have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z0_33
    have b33_424 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := z4_33
    clear w32_aa4 w32_aa0 w32_a3c w32_a38 w32_a34 w32_a30 w32_a2c w32_a28 w32_a24 w32_a20 w32_42c w32_428 w32_424 w32_420 w32_130 w32_12c w32_128 w32_124 w32_120 w32_11c w32_118 w32_114 w32_110 w32_10c w32_108 w32_104 w32_100 w32_fc w32_f8 w32_f4 w32_f0 w32_ec w32_e8 w32_e4 w32_e0 w32_dc w32_d8 w32_d4 w32_d0 w32_cc w32_c8 w32_c4 w32_c0 w32_bc w32_b8 w32_b4 w32_b0 w32_ac w32_a8 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 w32_2c w32_28 w32_24 g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_19 g32_18 g32_12 g32_11 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 rb32 s32 m32 u32 c32
    -- 0x2BB0: lw
    obtain ⟨n34, d34, u34⟩ := s33.lw E33.self sv_at_2bb0 (off' := 0x2BB4) (by decide)
      (by rw [g33_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s34 : St n34.mem SV n34 0x2BB4 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans (.single d34)
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
    have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_8]
    have g34_9 : reg n34 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
    have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
    have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = dg := by rw [u34.regs, upd_ne (by decide) (by decide), g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = ckl := by rw [u34.regs, upd_ne (by decide) (by decide), g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_27]
    have g34_10 : reg n34 a0 = 0 := by
      rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g33_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w33_420]
    have w34_24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m34]; exact w33_24
    have w34_28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m34]; exact w33_28
    have w34_2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m34]; exact w33_2c
    have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m34]; exact w33_30
    have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m34]; exact w33_34
    have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m34]; exact w33_38
    have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m34]; exact w33_3c
    have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m34]; exact w33_40
    have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m34]; exact w33_44
    have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m34]; exact w33_48
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
    have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m34]; exact w33_74
    have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m34]; exact w33_78
    have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m34]; exact w33_7c
    have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m34]; exact w33_80
    have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m34]; exact w33_84
    have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m34]; exact w33_88
    have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m34]; exact w33_8c
    have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m34]; exact w33_90
    have w34_94 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m34]; exact w33_94
    have w34_98 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m34]; exact w33_98
    have w34_9c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m34]; exact w33_9c
    have w34_a0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m34]; exact w33_a0
    have w34_a4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m34]; exact w33_a4
    have w34_a8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m34]; exact w33_a8
    have w34_ac : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m34]; exact w33_ac
    have w34_b0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m34]; exact w33_b0
    have w34_b4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m34]; exact w33_b4
    have w34_b8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m34]; exact w33_b8
    have w34_bc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m34]; exact w33_bc
    have w34_c0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m34]; exact w33_c0
    have w34_c4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m34]; exact w33_c4
    have w34_c8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m34]; exact w33_c8
    have w34_cc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m34]; exact w33_cc
    have w34_d0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m34]; exact w33_d0
    have w34_d4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m34]; exact w33_d4
    have w34_d8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m34]; exact w33_d8
    have w34_dc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m34]; exact w33_dc
    have w34_e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m34]; exact w33_e0
    have w34_e4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m34]; exact w33_e4
    have w34_e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m34]; exact w33_e8
    have w34_ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m34]; exact w33_ec
    have w34_f0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m34]; exact w33_f0
    have w34_f4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m34]; exact w33_f4
    have w34_f8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m34]; exact w33_f8
    have w34_fc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m34]; exact w33_fc
    have w34_100 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m34]; exact w33_100
    have w34_104 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m34]; exact w33_104
    have w34_108 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m34]; exact w33_108
    have w34_10c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m34]; exact w33_10c
    have w34_110 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m34]; exact w33_110
    have w34_114 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m34]; exact w33_114
    have w34_118 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m34]; exact w33_118
    have w34_11c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m34]; exact w33_11c
    have w34_120 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m34]; exact w33_120
    have w34_124 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m34]; exact w33_124
    have w34_128 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m34]; exact w33_128
    have w34_12c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m34]; exact w33_12c
    have w34_130 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m34]; exact w33_130
    have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m34]; exact w33_420
    have w34_a20 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m34]; exact w33_a20
    have w34_a24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m34]; exact w33_a24
    have w34_a28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m34]; exact w33_a28
    have w34_a2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m34]; exact w33_a2c
    have w34_a30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m34]; exact w33_a30
    have w34_a34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m34]; exact w33_a34
    have w34_a38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m34]; exact w33_a38
    have w34_a3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m34]; exact w33_a3c
    have w34_aa0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m34]; exact w33_aa0
    have w34_aa4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m34]; exact w33_aa4
    have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m34]; exact b33_424
    clear b33_424 w33_420 w33_aa4 w33_aa0 w33_a3c w33_a38 w33_a34 w33_a30 w33_a2c w33_a28 w33_a24 w33_a20 w33_130 w33_12c w33_128 w33_124 w33_120 w33_11c w33_118 w33_114 w33_110 w33_10c w33_108 w33_104 w33_100 w33_fc w33_f8 w33_f4 w33_f0 w33_ec w33_e8 w33_e4 w33_e0 w33_dc w33_d8 w33_d4 w33_d0 w33_cc w33_c8 w33_c4 w33_c0 w33_bc w33_b8 w33_b4 w33_b0 w33_ac w33_a8 w33_a4 w33_a0 w33_9c w33_98 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_44 w33_40 w33_3c w33_38 w33_34 w33_30 w33_2c w33_28 w33_24 z4_33 z0_33
    -- 0x2BB4: branch, taken
    obtain ⟨n35, d35, u35⟩ := s34.taken E34.self 0x2FEA sv_at_2bb4
      (by decide) (by rw [g34_10, s34.zero]; rfl)
    have s35 : St n35.mem SV n35 0x2FEA (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
    have m35 : n35.mem = n34.mem := u35.mem
    have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
    have t35 : Steps n0 n35 := t34.trans (.single d35)
    have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
    have E35 : SvCode n35.mem := E34.fr F fr35
    have V35 : SvSaves B n35.mem v := V34.same m35
    have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
    have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
    have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
    have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u35.regs, g34_8]
    have g35_9 : reg n35 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u35.regs, g34_9]
    have g35_10 : reg n35 a0 = 0 := by rw [u35.regs, g34_10]
    have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
    have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u35.regs, g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u35.regs, g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = dg := by rw [u35.regs, g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = ckl := by rw [u35.regs, g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [u35.regs, g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u35.regs, g34_27]
    have w35_24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m35]; exact w34_24
    have w35_28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m35]; exact w34_28
    have w35_2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m35]; exact w34_2c
    have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m35]; exact w34_30
    have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m35]; exact w34_34
    have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m35]; exact w34_38
    have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m35]; exact w34_3c
    have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m35]; exact w34_40
    have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m35]; exact w34_44
    have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m35]; exact w34_48
    have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m35]; exact w34_4c
    have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m35]; exact w34_50
    have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m35]; exact w34_54
    have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m35]; exact w34_58
    have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m35]; exact w34_5c
    have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m35]; exact w34_60
    have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m35]; exact w34_64
    have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m35]; exact w34_68
    have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m35]; exact w34_6c
    have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m35]; exact w34_70
    have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m35]; exact w34_74
    have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m35]; exact w34_78
    have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m35]; exact w34_7c
    have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m35]; exact w34_80
    have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m35]; exact w34_84
    have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m35]; exact w34_88
    have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m35]; exact w34_8c
    have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m35]; exact w34_90
    have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m35]; exact w34_94
    have w35_98 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m35]; exact w34_98
    have w35_9c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m35]; exact w34_9c
    have w35_a0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m35]; exact w34_a0
    have w35_a4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m35]; exact w34_a4
    have w35_a8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m35]; exact w34_a8
    have w35_ac : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m35]; exact w34_ac
    have w35_b0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m35]; exact w34_b0
    have w35_b4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m35]; exact w34_b4
    have w35_b8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m35]; exact w34_b8
    have w35_bc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m35]; exact w34_bc
    have w35_c0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m35]; exact w34_c0
    have w35_c4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m35]; exact w34_c4
    have w35_c8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m35]; exact w34_c8
    have w35_cc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m35]; exact w34_cc
    have w35_d0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m35]; exact w34_d0
    have w35_d4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m35]; exact w34_d4
    have w35_d8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m35]; exact w34_d8
    have w35_dc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m35]; exact w34_dc
    have w35_e0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m35]; exact w34_e0
    have w35_e4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m35]; exact w34_e4
    have w35_e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m35]; exact w34_e8
    have w35_ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m35]; exact w34_ec
    have w35_f0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m35]; exact w34_f0
    have w35_f4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m35]; exact w34_f4
    have w35_f8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m35]; exact w34_f8
    have w35_fc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m35]; exact w34_fc
    have w35_100 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m35]; exact w34_100
    have w35_104 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m35]; exact w34_104
    have w35_108 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m35]; exact w34_108
    have w35_10c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m35]; exact w34_10c
    have w35_110 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m35]; exact w34_110
    have w35_114 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m35]; exact w34_114
    have w35_118 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m35]; exact w34_118
    have w35_11c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m35]; exact w34_11c
    have w35_120 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m35]; exact w34_120
    have w35_124 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m35]; exact w34_124
    have w35_128 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m35]; exact w34_128
    have w35_12c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m35]; exact w34_12c
    have w35_130 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m35]; exact w34_130
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m35]; exact w34_420
    have w35_a20 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m35]; exact w34_a20
    have w35_a24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m35]; exact w34_a24
    have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m35]; exact w34_a28
    have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m35]; exact w34_a2c
    have w35_a30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m35]; exact w34_a30
    have w35_a34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m35]; exact w34_a34
    have w35_a38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m35]; exact w34_a38
    have w35_a3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m35]; exact w34_a3c
    have w35_aa0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m35]; exact w34_aa0
    have w35_aa4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m35]; exact w34_aa4
    have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m35]; exact b34_424
    clear b34_424 w34_aa4 w34_aa0 w34_a3c w34_a38 w34_a34 w34_a30 w34_a2c w34_a28 w34_a24 w34_a20 w34_420 w34_130 w34_12c w34_128 w34_124 w34_120 w34_11c w34_118 w34_114 w34_110 w34_10c w34_108 w34_104 w34_100 w34_fc w34_f8 w34_f4 w34_f0 w34_ec w34_e8 w34_e4 w34_e0 w34_dc w34_d8 w34_d4 w34_d0 w34_cc w34_c8 w34_c4 w34_c0 w34_bc w34_b8 w34_b4 w34_b0 w34_ac w34_a8 w34_a4 w34_a0 w34_9c w34_98 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_44 w34_40 w34_3c w34_38 w34_34 w34_30 w34_2c w34_28 w34_24 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
    -- 0x2FEA: lbu
    obtain ⟨n36, d36, u36⟩ := s35.lbu E35.self sv_at_2fea (off' := 0x2FEE) (by decide)
    have s36 : St n36.mem SV n36 0x2FEE (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans (.single d36)
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
    have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
    have g36_9 : reg n36 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
    have g36_10 : reg n36 a0 = 0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_10]
    have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
    have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = dg := by rw [u36.regs, upd_ne (by decide) (by decide), g35_24]
    have g36_25 : reg n36 (25 : Fin 32) = ckl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
    have w36_24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m36]; exact w35_24
    have w36_28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m36]; exact w35_28
    have w36_2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m36]; exact w35_2c
    have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m36]; exact w35_30
    have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m36]; exact w35_34
    have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m36]; exact w35_38
    have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m36]; exact w35_3c
    have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m36]; exact w35_40
    have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m36]; exact w35_44
    have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m36]; exact w35_48
    have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m36]; exact w35_4c
    have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m36]; exact w35_50
    have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m36]; exact w35_54
    have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m36]; exact w35_58
    have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m36]; exact w35_5c
    have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m36]; exact w35_60
    have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m36]; exact w35_64
    have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m36]; exact w35_68
    have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m36]; exact w35_6c
    have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m36]; exact w35_70
    have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m36]; exact w35_74
    have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m36]; exact w35_78
    have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m36]; exact w35_7c
    have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m36]; exact w35_80
    have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m36]; exact w35_84
    have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m36]; exact w35_88
    have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m36]; exact w35_8c
    have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m36]; exact w35_90
    have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m36]; exact w35_94
    have w36_98 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m36]; exact w35_98
    have w36_9c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m36]; exact w35_9c
    have w36_a0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m36]; exact w35_a0
    have w36_a4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m36]; exact w35_a4
    have w36_a8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m36]; exact w35_a8
    have w36_ac : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m36]; exact w35_ac
    have w36_b0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m36]; exact w35_b0
    have w36_b4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m36]; exact w35_b4
    have w36_b8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m36]; exact w35_b8
    have w36_bc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m36]; exact w35_bc
    have w36_c0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m36]; exact w35_c0
    have w36_c4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m36]; exact w35_c4
    have w36_c8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m36]; exact w35_c8
    have w36_cc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m36]; exact w35_cc
    have w36_d0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m36]; exact w35_d0
    have w36_d4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m36]; exact w35_d4
    have w36_d8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m36]; exact w35_d8
    have w36_dc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m36]; exact w35_dc
    have w36_e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m36]; exact w35_e0
    have w36_e4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m36]; exact w35_e4
    have w36_e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m36]; exact w35_e8
    have w36_ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m36]; exact w35_ec
    have w36_f0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m36]; exact w35_f0
    have w36_f4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m36]; exact w35_f4
    have w36_f8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m36]; exact w35_f8
    have w36_fc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m36]; exact w35_fc
    have w36_100 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m36]; exact w35_100
    have w36_104 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m36]; exact w35_104
    have w36_108 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m36]; exact w35_108
    have w36_10c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m36]; exact w35_10c
    have w36_110 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m36]; exact w35_110
    have w36_114 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m36]; exact w35_114
    have w36_118 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m36]; exact w35_118
    have w36_11c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m36]; exact w35_11c
    have w36_120 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m36]; exact w35_120
    have w36_124 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m36]; exact w35_124
    have w36_128 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m36]; exact w35_128
    have w36_12c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m36]; exact w35_12c
    have w36_130 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m36]; exact w35_130
    have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m36]; exact w35_420
    have w36_a20 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m36]; exact w35_a20
    have w36_a24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m36]; exact w35_a24
    have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m36]; exact w35_a28
    have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m36]; exact w35_a2c
    have w36_a30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m36]; exact w35_a30
    have w36_a34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m36]; exact w35_a34
    have w36_a38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m36]; exact w35_a38
    have w36_a3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m36]; exact w35_a3c
    have w36_aa0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m36]; exact w35_aa0
    have w36_aa4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m36]; exact w35_aa4
    have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m36]; exact b35_424
    clear b35_424 w35_aa4 w35_aa0 w35_a3c w35_a38 w35_a34 w35_a30 w35_a2c w35_a28 w35_a24 w35_a20 w35_420 w35_130 w35_12c w35_128 w35_124 w35_120 w35_11c w35_118 w35_114 w35_110 w35_10c w35_108 w35_104 w35_100 w35_fc w35_f8 w35_f4 w35_f0 w35_ec w35_e8 w35_e4 w35_e0 w35_dc w35_d8 w35_d4 w35_d0 w35_cc w35_c8 w35_c4 w35_c0 w35_bc w35_b8 w35_b4 w35_b0 w35_ac w35_a8 w35_a4 w35_a0 w35_9c w35_98 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 w35_2c w35_28 w35_24 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_19 g35_18 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
    -- 0x2FEE: j
    obtain ⟨n37, d37, u37⟩ := s36.jump E36.self sv_at_2fee (off' := 0x966) (by decide)
      (by rw [s36.pc]; decide)
    have s37 : St n37.mem SV n37 0x966 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
    have m37 : n37.mem = n36.mem := u37.mem
    have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
    have t37 : Steps n0 n37 := t36.trans (.single d37)
    have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
    have E37 : SvCode n37.mem := E36.fr F fr37
    have V37 : SvSaves B n37.mem v := V36.same m37
    have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
    have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
    have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
    have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u37.regs, g36_8]
    have g37_9 : reg n37 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u37.regs, g36_9]
    have g37_10 : reg n37 a0 = 0 := by rw [u37.regs, g36_10]
    have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
    have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
    have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, g36_21]
    have g37_22 : reg n37 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u37.regs, g36_22]
    have g37_23 : reg n37 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u37.regs, g36_23]
    have g37_24 : reg n37 (24 : Fin 32) = dg := by rw [u37.regs, g36_24]
    have g37_25 : reg n37 (25 : Fin 32) = ckl := by rw [u37.regs, g36_25]
    have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [u37.regs, g36_26]
    have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, g36_27]
    have w37_24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m37]; exact w36_24
    have w37_28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m37]; exact w36_28
    have w37_2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m37]; exact w36_2c
    have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m37]; exact w36_30
    have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m37]; exact w36_34
    have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m37]; exact w36_38
    have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m37]; exact w36_3c
    have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m37]; exact w36_40
    have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m37]; exact w36_44
    have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m37]; exact w36_48
    have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m37]; exact w36_4c
    have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m37]; exact w36_50
    have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
    have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
    have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
    have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m37]; exact w36_60
    have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m37]; exact w36_64
    have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m37]; exact w36_68
    have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
    have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m37]; exact w36_70
    have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m37]; exact w36_74
    have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m37]; exact w36_78
    have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m37]; exact w36_7c
    have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m37]; exact w36_80
    have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m37]; exact w36_84
    have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m37]; exact w36_88
    have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m37]; exact w36_8c
    have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m37]; exact w36_90
    have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m37]; exact w36_94
    have w37_98 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m37]; exact w36_98
    have w37_9c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m37]; exact w36_9c
    have w37_a0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m37]; exact w36_a0
    have w37_a4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m37]; exact w36_a4
    have w37_a8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m37]; exact w36_a8
    have w37_ac : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m37]; exact w36_ac
    have w37_b0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m37]; exact w36_b0
    have w37_b4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m37]; exact w36_b4
    have w37_b8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m37]; exact w36_b8
    have w37_bc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m37]; exact w36_bc
    have w37_c0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m37]; exact w36_c0
    have w37_c4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m37]; exact w36_c4
    have w37_c8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m37]; exact w36_c8
    have w37_cc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m37]; exact w36_cc
    have w37_d0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m37]; exact w36_d0
    have w37_d4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m37]; exact w36_d4
    have w37_d8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m37]; exact w36_d8
    have w37_dc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m37]; exact w36_dc
    have w37_e0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m37]; exact w36_e0
    have w37_e4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m37]; exact w36_e4
    have w37_e8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m37]; exact w36_e8
    have w37_ec : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m37]; exact w36_ec
    have w37_f0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m37]; exact w36_f0
    have w37_f4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m37]; exact w36_f4
    have w37_f8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m37]; exact w36_f8
    have w37_fc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m37]; exact w36_fc
    have w37_100 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m37]; exact w36_100
    have w37_104 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m37]; exact w36_104
    have w37_108 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m37]; exact w36_108
    have w37_10c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m37]; exact w36_10c
    have w37_110 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m37]; exact w36_110
    have w37_114 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m37]; exact w36_114
    have w37_118 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m37]; exact w36_118
    have w37_11c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m37]; exact w36_11c
    have w37_120 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m37]; exact w36_120
    have w37_124 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m37]; exact w36_124
    have w37_128 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m37]; exact w36_128
    have w37_12c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m37]; exact w36_12c
    have w37_130 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m37]; exact w36_130
    have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m37]; exact w36_420
    have w37_a20 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m37]; exact w36_a20
    have w37_a24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m37]; exact w36_a24
    have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m37]; exact w36_a28
    have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m37]; exact w36_a2c
    have w37_a30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m37]; exact w36_a30
    have w37_a34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m37]; exact w36_a34
    have w37_a38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m37]; exact w36_a38
    have w37_a3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m37]; exact w36_a3c
    have w37_aa0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m37]; exact w36_aa0
    have w37_aa4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m37]; exact w36_aa4
    have b37_424 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (0x1A : BitVec 8) := by rw [m37]; exact b36_424
    clear b36_424 w36_aa4 w36_aa0 w36_a3c w36_a38 w36_a34 w36_a30 w36_a2c w36_a28 w36_a24 w36_a20 w36_420 w36_130 w36_12c w36_128 w36_124 w36_120 w36_11c w36_118 w36_114 w36_110 w36_10c w36_108 w36_104 w36_100 w36_fc w36_f8 w36_f4 w36_f0 w36_ec w36_e8 w36_e4 w36_e0 w36_dc w36_d8 w36_d4 w36_d0 w36_cc w36_c8 w36_c4 w36_c0 w36_bc w36_b8 w36_b4 w36_b0 w36_ac w36_a8 w36_a4 w36_a0 w36_9c w36_98 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 w36_2c w36_28 w36_24 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_19 g36_18 g36_10 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
    exact .inl ⟨(fun ⟨h0', ix7', h1', ix17', h2', ix25', h3', ix33', h4', _⟩ => by rw [hr7] at h1'; cases h1'; rw [hr17] at h2'; cases h2'; rw [hr25] at h3'; cases h3'; rw [hr33] at h4'; cases h4'), sv_fail F E37 s37 t37 (fun x hx => (fR37 x hx).trans (fM x hx).symm) V37 hret g37_2 g37_18 hO g37_3 g37_4⟩
  have hix33 : ix33 < ((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1) := by have := (nlScan_lt _ _ _ hr33).2; omega
  rw [hr33] at L33
  obtain ⟨y0_33, y4_33, y8_33, y12_33⟩ := L33
  have w33_24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K33.w32 (by decide) (by decide)).trans w32_24
  have w33_28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K33.w32 (by decide) (by decide)).trans w32_28
  have w33_2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K33.w32 (by decide) (by decide)).trans w32_2c
  have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K33.w32 (by decide) (by decide)).trans w32_30
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K33.w32 (by decide) (by decide)).trans w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K33.w32 (by decide) (by decide)).trans w32_38
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K33.w32 (by decide) (by decide)).trans w32_3c
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K33.w32 (by decide) (by decide)).trans w32_40
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := (K33.w32 (by decide) (by decide)).trans w32_44
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K33.w32 (by decide) (by decide)).trans w32_48
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
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K33.w32 (by decide) (by decide)).trans w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K33.w32 (by decide) (by decide)).trans w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K33.w32 (by decide) (by decide)).trans w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K33.w32 (by decide) (by decide)).trans w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K33.w32 (by decide) (by decide)).trans w32_84
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K33.w32 (by decide) (by decide)).trans w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K33.w32 (by decide) (by decide)).trans w32_8c
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K33.w32 (by decide) (by decide)).trans w32_90
  have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K33.w32 (by decide) (by decide)).trans w32_94
  have w33_98 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K33.w32 (by decide) (by decide)).trans w32_98
  have w33_9c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K33.w32 (by decide) (by decide)).trans w32_9c
  have w33_a0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K33.w32 (by decide) (by decide)).trans w32_a0
  have w33_a4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K33.w32 (by decide) (by decide)).trans w32_a4
  have w33_a8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K33.w32 (by decide) (by decide)).trans w32_a8
  have w33_ac : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K33.w32 (by decide) (by decide)).trans w32_ac
  have w33_b0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K33.w32 (by decide) (by decide)).trans w32_b0
  have w33_b4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K33.w32 (by decide) (by decide)).trans w32_b4
  have w33_b8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K33.w32 (by decide) (by decide)).trans w32_b8
  have w33_bc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K33.w32 (by decide) (by decide)).trans w32_bc
  have w33_c0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K33.w32 (by decide) (by decide)).trans w32_c0
  have w33_c4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K33.w32 (by decide) (by decide)).trans w32_c4
  have w33_c8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K33.w32 (by decide) (by decide)).trans w32_c8
  have w33_cc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K33.w32 (by decide) (by decide)).trans w32_cc
  have w33_d0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K33.w32 (by decide) (by decide)).trans w32_d0
  have w33_d4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K33.w32 (by decide) (by decide)).trans w32_d4
  have w33_d8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K33.w32 (by decide) (by decide)).trans w32_d8
  have w33_dc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K33.w32 (by decide) (by decide)).trans w32_dc
  have w33_e0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K33.w32 (by decide) (by decide)).trans w32_e0
  have w33_e4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K33.w32 (by decide) (by decide)).trans w32_e4
  have w33_e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K33.w32 (by decide) (by decide)).trans w32_e8
  have w33_ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K33.w32 (by decide) (by decide)).trans w32_ec
  have w33_f0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K33.w32 (by decide) (by decide)).trans w32_f0
  have w33_f4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K33.w32 (by decide) (by decide)).trans w32_f4
  have w33_f8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K33.w32 (by decide) (by decide)).trans w32_f8
  have w33_fc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K33.w32 (by decide) (by decide)).trans w32_fc
  have w33_100 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K33.w32 (by decide) (by decide)).trans w32_100
  have w33_104 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K33.w32 (by decide) (by decide)).trans w32_104
  have w33_108 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K33.w32 (by decide) (by decide)).trans w32_108
  have w33_10c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K33.w32 (by decide) (by decide)).trans w32_10c
  have w33_110 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K33.w32 (by decide) (by decide)).trans w32_110
  have w33_114 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K33.w32 (by decide) (by decide)).trans w32_114
  have w33_118 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K33.w32 (by decide) (by decide)).trans w32_118
  have w33_11c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K33.w32 (by decide) (by decide)).trans w32_11c
  have w33_120 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K33.w32 (by decide) (by decide)).trans w32_120
  have w33_124 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K33.w32 (by decide) (by decide)).trans w32_124
  have w33_128 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K33.w32 (by decide) (by decide)).trans w32_128
  have w33_12c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K33.w32 (by decide) (by decide)).trans w32_12c
  have w33_130 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K33.w32 (by decide) (by decide)).trans w32_130
  have w33_a20 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K33.w32 (by decide) (by decide)).trans w32_a20
  have w33_a24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K33.w32 (by decide) (by decide)).trans w32_a24
  have w33_a28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K33.w32 (by decide) (by decide)).trans w32_a28
  have w33_a2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K33.w32 (by decide) (by decide)).trans w32_a2c
  have w33_a30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K33.w32 (by decide) (by decide)).trans w32_a30
  have w33_a34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K33.w32 (by decide) (by decide)).trans w32_a34
  have w33_a38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K33.w32 (by decide) (by decide)).trans w32_a38
  have w33_a3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K33.w32 (by decide) (by decide)).trans w32_a3c
  have w33_aa0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K33.w32 (by decide) (by decide)).trans w32_aa0
  have w33_aa4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K33.w32 (by decide) (by decide)).trans w32_aa4
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := y0_33
  have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := y4_33
  have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := y8_33
  have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := y12_33
  clear w32_aa4 w32_aa0 w32_a3c w32_a38 w32_a34 w32_a30 w32_a2c w32_a28 w32_a24 w32_a20 w32_42c w32_428 w32_424 w32_420 w32_130 w32_12c w32_128 w32_124 w32_120 w32_11c w32_118 w32_114 w32_110 w32_10c w32_108 w32_104 w32_100 w32_fc w32_f8 w32_f4 w32_f0 w32_ec w32_e8 w32_e4 w32_e0 w32_dc w32_d8 w32_d4 w32_d0 w32_cc w32_c8 w32_c4 w32_c0 w32_bc w32_b8 w32_b4 w32_b0 w32_ac w32_a8 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 w32_2c w32_28 w32_24 g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_19 g32_18 g32_12 g32_11 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 rb32 s32 m32 u32 c32
  -- 0x2BB0: lw
  obtain ⟨n34, d34, u34⟩ := s33.lw E33.self sv_at_2bb0 (off' := 0x2BB4) (by decide)
    (by rw [g33_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s34 : St n34.mem SV n34 0x2BB4 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = dg := by rw [u34.regs, upd_ne (by decide) (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = ckl := by rw [u34.regs, upd_ne (by decide) (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_27]
  have g34_10 : reg n34 a0 = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by
    rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g33_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w33_420]
  have w34_24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m34]; exact w33_24
  have w34_28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m34]; exact w33_28
  have w34_2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m34]; exact w33_2c
  have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m34]; exact w33_30
  have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m34]; exact w33_34
  have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m34]; exact w33_38
  have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m34]; exact w33_3c
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m34]; exact w33_40
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m34]; exact w33_44
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m34]; exact w33_48
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
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m34]; exact w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m34]; exact w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m34]; exact w33_7c
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m34]; exact w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m34]; exact w33_84
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m34]; exact w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m34]; exact w33_8c
  have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m34]; exact w33_90
  have w34_94 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m34]; exact w33_94
  have w34_98 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m34]; exact w33_98
  have w34_9c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m34]; exact w33_9c
  have w34_a0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m34]; exact w33_a0
  have w34_a4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m34]; exact w33_a4
  have w34_a8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m34]; exact w33_a8
  have w34_ac : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m34]; exact w33_ac
  have w34_b0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m34]; exact w33_b0
  have w34_b4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m34]; exact w33_b4
  have w34_b8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m34]; exact w33_b8
  have w34_bc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m34]; exact w33_bc
  have w34_c0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m34]; exact w33_c0
  have w34_c4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m34]; exact w33_c4
  have w34_c8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m34]; exact w33_c8
  have w34_cc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m34]; exact w33_cc
  have w34_d0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m34]; exact w33_d0
  have w34_d4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m34]; exact w33_d4
  have w34_d8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m34]; exact w33_d8
  have w34_dc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m34]; exact w33_dc
  have w34_e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m34]; exact w33_e0
  have w34_e4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m34]; exact w33_e4
  have w34_e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m34]; exact w33_e8
  have w34_ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m34]; exact w33_ec
  have w34_f0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m34]; exact w33_f0
  have w34_f4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m34]; exact w33_f4
  have w34_f8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m34]; exact w33_f8
  have w34_fc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m34]; exact w33_fc
  have w34_100 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m34]; exact w33_100
  have w34_104 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m34]; exact w33_104
  have w34_108 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m34]; exact w33_108
  have w34_10c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m34]; exact w33_10c
  have w34_110 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m34]; exact w33_110
  have w34_114 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m34]; exact w33_114
  have w34_118 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m34]; exact w33_118
  have w34_11c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m34]; exact w33_11c
  have w34_120 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m34]; exact w33_120
  have w34_124 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m34]; exact w33_124
  have w34_128 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m34]; exact w33_128
  have w34_12c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m34]; exact w33_12c
  have w34_130 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m34]; exact w33_130
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m34]; exact w33_420
  have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m34]; exact w33_424
  have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m34]; exact w33_428
  have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m34]; exact w33_42c
  have w34_a20 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m34]; exact w33_a20
  have w34_a24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m34]; exact w33_a24
  have w34_a28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m34]; exact w33_a28
  have w34_a2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m34]; exact w33_a2c
  have w34_a30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m34]; exact w33_a30
  have w34_a34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m34]; exact w33_a34
  have w34_a38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m34]; exact w33_a38
  have w34_a3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m34]; exact w33_a3c
  have w34_aa0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m34]; exact w33_aa0
  have w34_aa4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m34]; exact w33_aa4
  clear w33_42c w33_428 w33_424 w33_420 w33_aa4 w33_aa0 w33_a3c w33_a38 w33_a34 w33_a30 w33_a2c w33_a28 w33_a24 w33_a20 w33_130 w33_12c w33_128 w33_124 w33_120 w33_11c w33_118 w33_114 w33_110 w33_10c w33_108 w33_104 w33_100 w33_fc w33_f8 w33_f4 w33_f0 w33_ec w33_e8 w33_e4 w33_e0 w33_dc w33_d8 w33_d4 w33_d0 w33_cc w33_c8 w33_c4 w33_c0 w33_bc w33_b8 w33_b4 w33_b0 w33_ac w33_a8 w33_a4 w33_a0 w33_9c w33_98 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_44 w33_40 w33_3c w33_38 w33_34 w33_30 w33_2c w33_28 w33_24 y12_33 y8_33 y4_33 y0_33 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 K33 rk33 s33 c33
  -- 0x2BB4: branch, not taken
  obtain ⟨n35, d35, u35⟩ := s34.notTaken E34.self 0x2BB8 sv_at_2bb4
    (by decide) (by rw [g34_10, s34.zero]; exact br_beq_f (line_rest (line_rest (line_rest (.inl ck_in) hix7) hix17) hix25).ne0)
  have s35 : St n35.mem SV n35 0x2BB8 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans (.single d35)
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u35.regs, g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u35.regs, g34_9]
  have g35_10 : reg n35 a0 = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [u35.regs, g34_10]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [u35.regs, g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u35.regs, g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u35.regs, g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = dg := by rw [u35.regs, g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = ckl := by rw [u35.regs, g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [u35.regs, g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u35.regs, g34_27]
  have w35_24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m35]; exact w34_24
  have w35_28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m35]; exact w34_28
  have w35_2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m35]; exact w34_2c
  have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m35]; exact w34_30
  have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m35]; exact w34_34
  have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m35]; exact w34_38
  have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m35]; exact w34_3c
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m35]; exact w34_40
  have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m35]; exact w34_44
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m35]; exact w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m35]; exact w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m35]; exact w34_50
  have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m35]; exact w34_54
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m35]; exact w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m35]; exact w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m35]; exact w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m35]; exact w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m35]; exact w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m35]; exact w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m35]; exact w34_70
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m35]; exact w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m35]; exact w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m35]; exact w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m35]; exact w34_84
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m35]; exact w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m35]; exact w34_8c
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m35]; exact w34_90
  have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m35]; exact w34_94
  have w35_98 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m35]; exact w34_98
  have w35_9c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m35]; exact w34_9c
  have w35_a0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m35]; exact w34_a0
  have w35_a4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m35]; exact w34_a4
  have w35_a8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m35]; exact w34_a8
  have w35_ac : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m35]; exact w34_ac
  have w35_b0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m35]; exact w34_b0
  have w35_b4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m35]; exact w34_b4
  have w35_b8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m35]; exact w34_b8
  have w35_bc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m35]; exact w34_bc
  have w35_c0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m35]; exact w34_c0
  have w35_c4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m35]; exact w34_c4
  have w35_c8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m35]; exact w34_c8
  have w35_cc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m35]; exact w34_cc
  have w35_d0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m35]; exact w34_d0
  have w35_d4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m35]; exact w34_d4
  have w35_d8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m35]; exact w34_d8
  have w35_dc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m35]; exact w34_dc
  have w35_e0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m35]; exact w34_e0
  have w35_e4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m35]; exact w34_e4
  have w35_e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m35]; exact w34_e8
  have w35_ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m35]; exact w34_ec
  have w35_f0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m35]; exact w34_f0
  have w35_f4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m35]; exact w34_f4
  have w35_f8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m35]; exact w34_f8
  have w35_fc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m35]; exact w34_fc
  have w35_100 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m35]; exact w34_100
  have w35_104 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m35]; exact w34_104
  have w35_108 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m35]; exact w34_108
  have w35_10c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m35]; exact w34_10c
  have w35_110 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m35]; exact w34_110
  have w35_114 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m35]; exact w34_114
  have w35_118 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m35]; exact w34_118
  have w35_11c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m35]; exact w34_11c
  have w35_120 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m35]; exact w34_120
  have w35_124 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m35]; exact w34_124
  have w35_128 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m35]; exact w34_128
  have w35_12c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m35]; exact w34_12c
  have w35_130 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m35]; exact w34_130
  have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m35]; exact w34_420
  have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m35]; exact w34_424
  have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m35]; exact w34_428
  have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m35]; exact w34_42c
  have w35_a20 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m35]; exact w34_a20
  have w35_a24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m35]; exact w34_a24
  have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m35]; exact w34_a28
  have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m35]; exact w34_a2c
  have w35_a30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m35]; exact w34_a30
  have w35_a34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m35]; exact w34_a34
  have w35_a38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m35]; exact w34_a38
  have w35_a3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m35]; exact w34_a3c
  have w35_aa0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m35]; exact w34_aa0
  have w35_aa4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m35]; exact w34_aa4
  clear w34_aa4 w34_aa0 w34_a3c w34_a38 w34_a34 w34_a30 w34_a2c w34_a28 w34_a24 w34_a20 w34_42c w34_428 w34_424 w34_420 w34_130 w34_12c w34_128 w34_124 w34_120 w34_11c w34_118 w34_114 w34_110 w34_10c w34_108 w34_104 w34_100 w34_fc w34_f8 w34_f4 w34_f0 w34_ec w34_e8 w34_e4 w34_e0 w34_dc w34_d8 w34_d4 w34_d0 w34_cc w34_c8 w34_c4 w34_c0 w34_bc w34_b8 w34_b4 w34_b0 w34_ac w34_a8 w34_a4 w34_a0 w34_9c w34_98 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_44 w34_40 w34_3c w34_38 w34_34 w34_30 w34_2c w34_28 w34_24 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
  -- 0x2BB8: lw
  obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_2bb8 (off' := 0x2BBC) (by decide)
    (by rw [g35_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s36 : St n36.mem SV n36 0x2BBC (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = dg := by rw [u36.regs, upd_ne (by decide) (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = ckl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
  have g36_10 : reg n36 a0 = BitVec.ofNat 32 ix33 := by
    rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g35_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w35_424]
  have w36_24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m36]; exact w35_24
  have w36_28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m36]; exact w35_28
  have w36_2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m36]; exact w35_2c
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m36]; exact w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m36]; exact w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m36]; exact w35_38
  have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m36]; exact w35_3c
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m36]; exact w35_40
  have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m36]; exact w35_44
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m36]; exact w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m36]; exact w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m36]; exact w35_50
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m36]; exact w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m36]; exact w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m36]; exact w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m36]; exact w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m36]; exact w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m36]; exact w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m36]; exact w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m36]; exact w35_70
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m36]; exact w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m36]; exact w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m36]; exact w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m36]; exact w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m36]; exact w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m36]; exact w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m36]; exact w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m36]; exact w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m36]; exact w35_94
  have w36_98 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m36]; exact w35_98
  have w36_9c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m36]; exact w35_9c
  have w36_a0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m36]; exact w35_a0
  have w36_a4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m36]; exact w35_a4
  have w36_a8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m36]; exact w35_a8
  have w36_ac : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m36]; exact w35_ac
  have w36_b0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m36]; exact w35_b0
  have w36_b4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m36]; exact w35_b4
  have w36_b8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m36]; exact w35_b8
  have w36_bc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m36]; exact w35_bc
  have w36_c0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m36]; exact w35_c0
  have w36_c4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m36]; exact w35_c4
  have w36_c8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m36]; exact w35_c8
  have w36_cc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m36]; exact w35_cc
  have w36_d0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m36]; exact w35_d0
  have w36_d4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m36]; exact w35_d4
  have w36_d8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m36]; exact w35_d8
  have w36_dc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m36]; exact w35_dc
  have w36_e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m36]; exact w35_e0
  have w36_e4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m36]; exact w35_e4
  have w36_e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m36]; exact w35_e8
  have w36_ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m36]; exact w35_ec
  have w36_f0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m36]; exact w35_f0
  have w36_f4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m36]; exact w35_f4
  have w36_f8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m36]; exact w35_f8
  have w36_fc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m36]; exact w35_fc
  have w36_100 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m36]; exact w35_100
  have w36_104 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m36]; exact w35_104
  have w36_108 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m36]; exact w35_108
  have w36_10c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m36]; exact w35_10c
  have w36_110 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m36]; exact w35_110
  have w36_114 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m36]; exact w35_114
  have w36_118 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m36]; exact w35_118
  have w36_11c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m36]; exact w35_11c
  have w36_120 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m36]; exact w35_120
  have w36_124 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m36]; exact w35_124
  have w36_128 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m36]; exact w35_128
  have w36_12c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m36]; exact w35_12c
  have w36_130 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m36]; exact w35_130
  have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m36]; exact w35_420
  have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m36]; exact w35_424
  have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m36]; exact w35_428
  have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m36]; exact w35_42c
  have w36_a20 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m36]; exact w35_a20
  have w36_a24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m36]; exact w35_a24
  have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m36]; exact w35_a28
  have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m36]; exact w35_a2c
  have w36_a30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m36]; exact w35_a30
  have w36_a34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m36]; exact w35_a34
  have w36_a38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m36]; exact w35_a38
  have w36_a3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m36]; exact w35_a3c
  have w36_aa0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m36]; exact w35_aa0
  have w36_aa4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m36]; exact w35_aa4
  clear w35_aa4 w35_aa0 w35_a3c w35_a38 w35_a34 w35_a30 w35_a2c w35_a28 w35_a24 w35_a20 w35_42c w35_428 w35_424 w35_420 w35_130 w35_12c w35_128 w35_124 w35_120 w35_11c w35_118 w35_114 w35_110 w35_10c w35_108 w35_104 w35_100 w35_fc w35_f8 w35_f4 w35_f0 w35_ec w35_e8 w35_e4 w35_e0 w35_dc w35_d8 w35_d4 w35_d0 w35_cc w35_c8 w35_c4 w35_c0 w35_bc w35_b8 w35_b4 w35_b0 w35_ac w35_a8 w35_a4 w35_a0 w35_9c w35_98 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 w35_2c w35_28 w35_24 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_19 g35_18 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
  by_cases hblank : BitVec.ofNat 32 ix33 = 0
  rotate_left
  · -- 0x2BBC: branch, taken
    obtain ⟨n37, d37, u37⟩ := s36.taken E36.self 0x2FF2 sv_at_2bbc
      (by decide) (by rw [g36_10, s36.zero]; exact br_bne_t hblank)
    have s37 : St n37.mem SV n37 0x2FF2 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
    have m37 : n37.mem = n36.mem := u37.mem
    have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
    have t37 : Steps n0 n37 := t36.trans (.single d37)
    have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
    have E37 : SvCode n37.mem := E36.fr F fr37
    have V37 : SvSaves B n37.mem v := V36.same m37
    have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
    have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
    have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
    have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u37.regs, g36_8]
    have g37_9 : reg n37 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u37.regs, g36_9]
    have g37_10 : reg n37 a0 = BitVec.ofNat 32 ix33 := by rw [u37.regs, g36_10]
    have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
    have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
    have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, g36_21]
    have g37_22 : reg n37 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u37.regs, g36_22]
    have g37_23 : reg n37 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u37.regs, g36_23]
    have g37_24 : reg n37 (24 : Fin 32) = dg := by rw [u37.regs, g36_24]
    have g37_25 : reg n37 (25 : Fin 32) = ckl := by rw [u37.regs, g36_25]
    have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [u37.regs, g36_26]
    have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, g36_27]
    have w37_24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m37]; exact w36_24
    have w37_28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m37]; exact w36_28
    have w37_2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m37]; exact w36_2c
    have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m37]; exact w36_30
    have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m37]; exact w36_34
    have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m37]; exact w36_38
    have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m37]; exact w36_3c
    have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m37]; exact w36_40
    have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m37]; exact w36_44
    have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m37]; exact w36_48
    have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m37]; exact w36_4c
    have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m37]; exact w36_50
    have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
    have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
    have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
    have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m37]; exact w36_60
    have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m37]; exact w36_64
    have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m37]; exact w36_68
    have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
    have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m37]; exact w36_70
    have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m37]; exact w36_74
    have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m37]; exact w36_78
    have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m37]; exact w36_7c
    have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m37]; exact w36_80
    have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m37]; exact w36_84
    have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m37]; exact w36_88
    have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m37]; exact w36_8c
    have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m37]; exact w36_90
    have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m37]; exact w36_94
    have w37_98 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m37]; exact w36_98
    have w37_9c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m37]; exact w36_9c
    have w37_a0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m37]; exact w36_a0
    have w37_a4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m37]; exact w36_a4
    have w37_a8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m37]; exact w36_a8
    have w37_ac : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m37]; exact w36_ac
    have w37_b0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m37]; exact w36_b0
    have w37_b4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m37]; exact w36_b4
    have w37_b8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m37]; exact w36_b8
    have w37_bc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m37]; exact w36_bc
    have w37_c0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m37]; exact w36_c0
    have w37_c4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m37]; exact w36_c4
    have w37_c8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m37]; exact w36_c8
    have w37_cc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m37]; exact w36_cc
    have w37_d0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m37]; exact w36_d0
    have w37_d4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m37]; exact w36_d4
    have w37_d8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m37]; exact w36_d8
    have w37_dc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m37]; exact w36_dc
    have w37_e0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m37]; exact w36_e0
    have w37_e4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m37]; exact w36_e4
    have w37_e8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m37]; exact w36_e8
    have w37_ec : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m37]; exact w36_ec
    have w37_f0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m37]; exact w36_f0
    have w37_f4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m37]; exact w36_f4
    have w37_f8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m37]; exact w36_f8
    have w37_fc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m37]; exact w36_fc
    have w37_100 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m37]; exact w36_100
    have w37_104 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m37]; exact w36_104
    have w37_108 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m37]; exact w36_108
    have w37_10c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m37]; exact w36_10c
    have w37_110 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m37]; exact w36_110
    have w37_114 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m37]; exact w36_114
    have w37_118 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m37]; exact w36_118
    have w37_11c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m37]; exact w36_11c
    have w37_120 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m37]; exact w36_120
    have w37_124 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m37]; exact w36_124
    have w37_128 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m37]; exact w36_128
    have w37_12c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m37]; exact w36_12c
    have w37_130 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m37]; exact w36_130
    have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m37]; exact w36_420
    have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m37]; exact w36_424
    have w37_428 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m37]; exact w36_428
    have w37_42c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m37]; exact w36_42c
    have w37_a20 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m37]; exact w36_a20
    have w37_a24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m37]; exact w36_a24
    have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m37]; exact w36_a28
    have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m37]; exact w36_a2c
    have w37_a30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m37]; exact w36_a30
    have w37_a34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m37]; exact w36_a34
    have w37_a38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m37]; exact w36_a38
    have w37_a3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m37]; exact w36_a3c
    have w37_aa0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m37]; exact w36_aa0
    have w37_aa4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m37]; exact w36_aa4
    clear w36_aa4 w36_aa0 w36_a3c w36_a38 w36_a34 w36_a30 w36_a2c w36_a28 w36_a24 w36_a20 w36_42c w36_428 w36_424 w36_420 w36_130 w36_12c w36_128 w36_124 w36_120 w36_11c w36_118 w36_114 w36_110 w36_10c w36_108 w36_104 w36_100 w36_fc w36_f8 w36_f4 w36_f0 w36_ec w36_e8 w36_e4 w36_e0 w36_dc w36_d8 w36_d4 w36_d0 w36_cc w36_c8 w36_c4 w36_c0 w36_bc w36_b8 w36_b4 w36_b0 w36_ac w36_a8 w36_a4 w36_a0 w36_9c w36_98 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 w36_2c w36_28 w36_24 g36_10 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
    -- 0x2FF2
    obtain ⟨n38, c38, u38⟩ := s37.block svCk12ff2 E37.self svCk12ff2_end
      ⟨trivial, trivial⟩
    have m38 : n38.mem = n37.mem := u38.mem
    have s38 : St n38.mem SV n38 0x2FF4 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
    have rb38 : ∀ q, reg n38 q = (runBlock svCk12ff2 (n37.mem, reg n37)).2 q := fun q => by rw [u38.regs]
    have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
    have t38 : Steps n0 n38 := t37.trans c38
    have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
    have E38 : SvCode n38.mem := E37.fr F fr38
    have V38 : SvSaves B n38.mem v := V37.same m38
    have g38_2 : reg n38 sp = B + 0x21A0 := by
      rw [rb38, runBlock_reg _ _ _ sp s37.zero (by decide), g37_2]
    have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb38, runBlock_reg _ _ _ (3 : Fin 32) s37.zero (by decide), g37_3]
    have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb38, runBlock_reg _ _ _ (4 : Fin 32) s37.zero (by decide), g37_4]
    have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by
      rw [rb38, runBlock_reg _ _ _ (8 : Fin 32) s37.zero (by decide), g37_8]
    have g38_9 : reg n38 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by
      rw [rb38, runBlock_reg _ _ _ (9 : Fin 32) s37.zero (by decide), g37_9]
    have g38_10 : reg n38 a0 = BitVec.ofNat 32 ix33 := by
      rw [rb38, runBlock_reg _ _ _ a0 s37.zero (by decide), g37_10]
    have g38_18 : reg n38 (18 : Fin 32) = out := by
      rw [rb38, runBlock_reg _ _ _ (18 : Fin 32) s37.zero (by decide), g37_18]
    have g38_19 : reg n38 (19 : Fin 32) = bp := by
      rw [rb38, runBlock_reg _ _ _ (19 : Fin 32) s37.zero (by decide), g37_19]
    have g38_21 : reg n38 (21 : Fin 32) = x21 := by
      rw [rb38, runBlock_reg _ _ _ (21 : Fin 32) s37.zero (by decide), g37_21]
    have g38_22 : reg n38 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by
      rw [rb38, runBlock_reg _ _ _ (22 : Fin 32) s37.zero (by decide), g37_22]
    have g38_23 : reg n38 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by
      rw [rb38, runBlock_reg _ _ _ (23 : Fin 32) s37.zero (by decide), g37_23]
    have g38_24 : reg n38 (24 : Fin 32) = dg := by
      rw [rb38, runBlock_reg _ _ _ (24 : Fin 32) s37.zero (by decide), g37_24]
    have g38_25 : reg n38 (25 : Fin 32) = ckl := by
      rw [rb38, runBlock_reg _ _ _ (25 : Fin 32) s37.zero (by decide), g37_25]
    have g38_26 : reg n38 (26 : Fin 32) = x26 := by
      rw [rb38, runBlock_reg _ _ _ (26 : Fin 32) s37.zero (by decide), g37_26]
    have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb38, runBlock_reg _ _ _ (27 : Fin 32) s37.zero (by decide), g37_27]
    have g38_20 : reg n38 (20 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb38]; simp +decide only [runBlock, BInstr.run, svCk12ff2, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g37_2, g37_3, g37_4, g37_8, g37_9, g37_10, g37_18, g37_19, g37_21, g37_22, g37_23, g37_24, g37_25, g37_26, g37_27, s37.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w38_24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m38]; exact w37_24
    have w38_28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m38]; exact w37_28
    have w38_2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m38]; exact w37_2c
    have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m38]; exact w37_30
    have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m38]; exact w37_34
    have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m38]; exact w37_38
    have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m38]; exact w37_3c
    have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m38]; exact w37_40
    have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m38]; exact w37_44
    have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m38]; exact w37_48
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
    have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m38]; exact w37_74
    have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m38]; exact w37_78
    have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m38]; exact w37_7c
    have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m38]; exact w37_80
    have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m38]; exact w37_84
    have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m38]; exact w37_88
    have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m38]; exact w37_8c
    have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m38]; exact w37_90
    have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m38]; exact w37_94
    have w38_98 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m38]; exact w37_98
    have w38_9c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m38]; exact w37_9c
    have w38_a0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m38]; exact w37_a0
    have w38_a4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m38]; exact w37_a4
    have w38_a8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m38]; exact w37_a8
    have w38_ac : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m38]; exact w37_ac
    have w38_b0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m38]; exact w37_b0
    have w38_b4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m38]; exact w37_b4
    have w38_b8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m38]; exact w37_b8
    have w38_bc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m38]; exact w37_bc
    have w38_c0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m38]; exact w37_c0
    have w38_c4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m38]; exact w37_c4
    have w38_c8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m38]; exact w37_c8
    have w38_cc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m38]; exact w37_cc
    have w38_d0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m38]; exact w37_d0
    have w38_d4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m38]; exact w37_d4
    have w38_d8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m38]; exact w37_d8
    have w38_dc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m38]; exact w37_dc
    have w38_e0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m38]; exact w37_e0
    have w38_e4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m38]; exact w37_e4
    have w38_e8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m38]; exact w37_e8
    have w38_ec : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m38]; exact w37_ec
    have w38_f0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m38]; exact w37_f0
    have w38_f4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m38]; exact w37_f4
    have w38_f8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m38]; exact w37_f8
    have w38_fc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m38]; exact w37_fc
    have w38_100 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m38]; exact w37_100
    have w38_104 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m38]; exact w37_104
    have w38_108 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m38]; exact w37_108
    have w38_10c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m38]; exact w37_10c
    have w38_110 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m38]; exact w37_110
    have w38_114 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m38]; exact w37_114
    have w38_118 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m38]; exact w37_118
    have w38_11c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m38]; exact w37_11c
    have w38_120 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m38]; exact w37_120
    have w38_124 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m38]; exact w37_124
    have w38_128 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m38]; exact w37_128
    have w38_12c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m38]; exact w37_12c
    have w38_130 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m38]; exact w37_130
    have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m38]; exact w37_420
    have w38_424 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m38]; exact w37_424
    have w38_428 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m38]; exact w37_428
    have w38_42c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m38]; exact w37_42c
    have w38_a20 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m38]; exact w37_a20
    have w38_a24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m38]; exact w37_a24
    have w38_a28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m38]; exact w37_a28
    have w38_a2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m38]; exact w37_a2c
    have w38_a30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m38]; exact w37_a30
    have w38_a34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m38]; exact w37_a34
    have w38_a38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m38]; exact w37_a38
    have w38_a3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m38]; exact w37_a3c
    have w38_aa0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m38]; exact w37_aa0
    have w38_aa4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m38]; exact w37_aa4
    clear w37_aa4 w37_aa0 w37_a3c w37_a38 w37_a34 w37_a30 w37_a2c w37_a28 w37_a24 w37_a20 w37_42c w37_428 w37_424 w37_420 w37_130 w37_12c w37_128 w37_124 w37_120 w37_11c w37_118 w37_114 w37_110 w37_10c w37_108 w37_104 w37_100 w37_fc w37_f8 w37_f4 w37_f0 w37_ec w37_e8 w37_e4 w37_e0 w37_dc w37_d8 w37_d4 w37_d0 w37_cc w37_c8 w37_c4 w37_c0 w37_bc w37_b8 w37_b4 w37_b0 w37_ac w37_a8 w37_a4 w37_a0 w37_9c w37_98 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_44 w37_40 w37_3c w37_38 w37_34 w37_30 w37_2c w37_28 w37_24 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_19 g37_18 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
    -- 0x2FF4: j
    obtain ⟨n39, d39, u39⟩ := s38.jump E38.self sv_at_2ff4 (off' := 0x966) (by decide)
      (by rw [s38.pc]; decide)
    have s39 : St n39.mem SV n39 0x966 (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
    have m39 : n39.mem = n38.mem := u39.mem
    have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
    have t39 : Steps n0 n39 := t38.trans (.single d39)
    have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
    have E39 : SvCode n39.mem := E38.fr F fr39
    have V39 : SvSaves B n39.mem v := V38.same m39
    have g39_2 : reg n39 sp = B + 0x21A0 := by rw [u39.regs, g38_2]
    have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u39.regs, g38_3]
    have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u39.regs, g38_4]
    have g39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u39.regs, g38_8]
    have g39_9 : reg n39 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u39.regs, g38_9]
    have g39_10 : reg n39 a0 = BitVec.ofNat 32 ix33 := by rw [u39.regs, g38_10]
    have g39_18 : reg n39 (18 : Fin 32) = out := by rw [u39.regs, g38_18]
    have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [u39.regs, g38_19]
    have g39_20 : reg n39 (20 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u39.regs, g38_20]
    have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [u39.regs, g38_21]
    have g39_22 : reg n39 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u39.regs, g38_22]
    have g39_23 : reg n39 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u39.regs, g38_23]
    have g39_24 : reg n39 (24 : Fin 32) = dg := by rw [u39.regs, g38_24]
    have g39_25 : reg n39 (25 : Fin 32) = ckl := by rw [u39.regs, g38_25]
    have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [u39.regs, g38_26]
    have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u39.regs, g38_27]
    have w39_24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m39]; exact w38_24
    have w39_28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m39]; exact w38_28
    have w39_2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m39]; exact w38_2c
    have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m39]; exact w38_30
    have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m39]; exact w38_34
    have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m39]; exact w38_38
    have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m39]; exact w38_3c
    have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m39]; exact w38_40
    have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m39]; exact w38_44
    have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m39]; exact w38_48
    have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m39]; exact w38_4c
    have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m39]; exact w38_50
    have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m39]; exact w38_54
    have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m39]; exact w38_58
    have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m39]; exact w38_5c
    have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m39]; exact w38_60
    have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m39]; exact w38_64
    have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m39]; exact w38_68
    have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m39]; exact w38_6c
    have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m39]; exact w38_70
    have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m39]; exact w38_74
    have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m39]; exact w38_78
    have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m39]; exact w38_7c
    have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m39]; exact w38_80
    have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m39]; exact w38_84
    have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m39]; exact w38_88
    have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m39]; exact w38_8c
    have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m39]; exact w38_90
    have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m39]; exact w38_94
    have w39_98 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m39]; exact w38_98
    have w39_9c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m39]; exact w38_9c
    have w39_a0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m39]; exact w38_a0
    have w39_a4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m39]; exact w38_a4
    have w39_a8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m39]; exact w38_a8
    have w39_ac : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m39]; exact w38_ac
    have w39_b0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m39]; exact w38_b0
    have w39_b4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m39]; exact w38_b4
    have w39_b8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m39]; exact w38_b8
    have w39_bc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m39]; exact w38_bc
    have w39_c0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m39]; exact w38_c0
    have w39_c4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m39]; exact w38_c4
    have w39_c8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m39]; exact w38_c8
    have w39_cc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m39]; exact w38_cc
    have w39_d0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m39]; exact w38_d0
    have w39_d4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m39]; exact w38_d4
    have w39_d8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m39]; exact w38_d8
    have w39_dc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m39]; exact w38_dc
    have w39_e0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m39]; exact w38_e0
    have w39_e4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m39]; exact w38_e4
    have w39_e8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m39]; exact w38_e8
    have w39_ec : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m39]; exact w38_ec
    have w39_f0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m39]; exact w38_f0
    have w39_f4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m39]; exact w38_f4
    have w39_f8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m39]; exact w38_f8
    have w39_fc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m39]; exact w38_fc
    have w39_100 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m39]; exact w38_100
    have w39_104 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m39]; exact w38_104
    have w39_108 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m39]; exact w38_108
    have w39_10c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m39]; exact w38_10c
    have w39_110 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m39]; exact w38_110
    have w39_114 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m39]; exact w38_114
    have w39_118 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m39]; exact w38_118
    have w39_11c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m39]; exact w38_11c
    have w39_120 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m39]; exact w38_120
    have w39_124 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m39]; exact w38_124
    have w39_128 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m39]; exact w38_128
    have w39_12c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m39]; exact w38_12c
    have w39_130 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m39]; exact w38_130
    have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m39]; exact w38_420
    have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m39]; exact w38_424
    have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m39]; exact w38_428
    have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m39]; exact w38_42c
    have w39_a20 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m39]; exact w38_a20
    have w39_a24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m39]; exact w38_a24
    have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m39]; exact w38_a28
    have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m39]; exact w38_a2c
    have w39_a30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m39]; exact w38_a30
    have w39_a34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m39]; exact w38_a34
    have w39_a38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m39]; exact w38_a38
    have w39_a3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m39]; exact w38_a3c
    have w39_aa0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m39]; exact w38_aa0
    have w39_aa4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m39]; exact w38_aa4
    clear w38_aa4 w38_aa0 w38_a3c w38_a38 w38_a34 w38_a30 w38_a2c w38_a28 w38_a24 w38_a20 w38_42c w38_428 w38_424 w38_420 w38_130 w38_12c w38_128 w38_124 w38_120 w38_11c w38_118 w38_114 w38_110 w38_10c w38_108 w38_104 w38_100 w38_fc w38_f8 w38_f4 w38_f0 w38_ec w38_e8 w38_e4 w38_e0 w38_dc w38_d8 w38_d4 w38_d0 w38_cc w38_c8 w38_c4 w38_c0 w38_bc w38_b8 w38_b4 w38_b0 w38_ac w38_a8 w38_a4 w38_a0 w38_9c w38_98 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_44 w38_40 w38_3c w38_38 w38_34 w38_30 w38_2c w38_28 w38_24 g38_20 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_19 g38_18 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 rb38 s38 m38 u38 c38
    exact .inl ⟨(fun ⟨h0', ix7', h1', ix17', h2', ix25', h3', ix33', h4', h5', _⟩ => by rw [hr7] at h1'; cases h1'; rw [hr17] at h2'; cases h2'; rw [hr25] at h3'; cases h3'; rw [hr33] at h4'; cases h4'; exact hblank h5'), sv_fail F E39 s39 t39 (fun x hx => (fR39 x hx).trans (fM x hx).symm) V39 hret g39_2 g39_18 hO g39_3 g39_4⟩
  -- 0x2BBC: branch, not taken
  obtain ⟨n37, d37, u37⟩ := s36.notTaken E36.self 0x2BC0 sv_at_2bbc
    (by decide) (by rw [g36_10, s36.zero]; exact br_bne_f hblank)
  have s37 : St n37.mem SV n37 0x2BC0 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u37.regs, g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u37.regs, g36_9]
  have g37_10 : reg n37 a0 = BitVec.ofNat 32 ix33 := by rw [u37.regs, g36_10]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u37.regs, g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u37.regs, g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = dg := by rw [u37.regs, g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = ckl := by rw [u37.regs, g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [u37.regs, g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, g36_27]
  have w37_24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m37]; exact w36_24
  have w37_28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m37]; exact w36_28
  have w37_2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m37]; exact w36_2c
  have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m37]; exact w36_30
  have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m37]; exact w36_34
  have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m37]; exact w36_38
  have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m37]; exact w36_3c
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m37]; exact w36_40
  have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m37]; exact w36_44
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m37]; exact w36_48
  have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m37]; exact w36_4c
  have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m37]; exact w36_50
  have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
  have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
  have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
  have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m37]; exact w36_60
  have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m37]; exact w36_64
  have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m37]; exact w36_68
  have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
  have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m37]; exact w36_70
  have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m37]; exact w36_74
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m37]; exact w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m37]; exact w36_7c
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m37]; exact w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m37]; exact w36_84
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m37]; exact w36_88
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m37]; exact w36_8c
  have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m37]; exact w36_90
  have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m37]; exact w36_94
  have w37_98 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m37]; exact w36_98
  have w37_9c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m37]; exact w36_9c
  have w37_a0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m37]; exact w36_a0
  have w37_a4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m37]; exact w36_a4
  have w37_a8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m37]; exact w36_a8
  have w37_ac : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m37]; exact w36_ac
  have w37_b0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m37]; exact w36_b0
  have w37_b4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m37]; exact w36_b4
  have w37_b8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m37]; exact w36_b8
  have w37_bc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m37]; exact w36_bc
  have w37_c0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m37]; exact w36_c0
  have w37_c4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m37]; exact w36_c4
  have w37_c8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m37]; exact w36_c8
  have w37_cc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m37]; exact w36_cc
  have w37_d0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m37]; exact w36_d0
  have w37_d4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m37]; exact w36_d4
  have w37_d8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m37]; exact w36_d8
  have w37_dc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m37]; exact w36_dc
  have w37_e0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m37]; exact w36_e0
  have w37_e4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m37]; exact w36_e4
  have w37_e8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m37]; exact w36_e8
  have w37_ec : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m37]; exact w36_ec
  have w37_f0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m37]; exact w36_f0
  have w37_f4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m37]; exact w36_f4
  have w37_f8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m37]; exact w36_f8
  have w37_fc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m37]; exact w36_fc
  have w37_100 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m37]; exact w36_100
  have w37_104 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m37]; exact w36_104
  have w37_108 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m37]; exact w36_108
  have w37_10c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m37]; exact w36_10c
  have w37_110 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m37]; exact w36_110
  have w37_114 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m37]; exact w36_114
  have w37_118 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m37]; exact w36_118
  have w37_11c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m37]; exact w36_11c
  have w37_120 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m37]; exact w36_120
  have w37_124 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m37]; exact w36_124
  have w37_128 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m37]; exact w36_128
  have w37_12c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m37]; exact w36_12c
  have w37_130 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m37]; exact w36_130
  have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m37]; exact w36_420
  have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m37]; exact w36_424
  have w37_428 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m37]; exact w36_428
  have w37_42c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m37]; exact w36_42c
  have w37_a20 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m37]; exact w36_a20
  have w37_a24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m37]; exact w36_a24
  have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m37]; exact w36_a28
  have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m37]; exact w36_a2c
  have w37_a30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m37]; exact w36_a30
  have w37_a34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m37]; exact w36_a34
  have w37_a38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m37]; exact w36_a38
  have w37_a3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m37]; exact w36_a3c
  have w37_aa0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m37]; exact w36_aa0
  have w37_aa4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m37]; exact w36_aa4
  clear w36_aa4 w36_aa0 w36_a3c w36_a38 w36_a34 w36_a30 w36_a2c w36_a28 w36_a24 w36_a20 w36_42c w36_428 w36_424 w36_420 w36_130 w36_12c w36_128 w36_124 w36_120 w36_11c w36_118 w36_114 w36_110 w36_10c w36_108 w36_104 w36_100 w36_fc w36_f8 w36_f4 w36_f0 w36_ec w36_e8 w36_e4 w36_e0 w36_dc w36_d8 w36_d4 w36_d0 w36_cc w36_c8 w36_c4 w36_c0 w36_bc w36_b8 w36_b4 w36_b0 w36_ac w36_a8 w36_a4 w36_a0 w36_9c w36_98 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 w36_2c w36_28 w36_24 g36_10 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  -- 0x2BC0: lw
  obtain ⟨n38, d38, u38⟩ := s37.lw E37.self sv_at_2bc0 (off' := 0x2BC4) (by decide)
    (by rw [g37_2, show B + 0x21A0 + 0x42C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s38 : St n38.mem SV n38 0x2BC4 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans (.single d38)
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_9]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, upd_ne (by decide) (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_19]
  have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = dg := by rw [u38.regs, upd_ne (by decide) (by decide), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = ckl := by rw [u38.regs, upd_ne (by decide) (by decide), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_27]
  have g38_10 : reg n38 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by
    rw [u38.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g37_2, show B + 0x21A0 + 0x42C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w37_42c]
  have w38_24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m38]; exact w37_24
  have w38_28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m38]; exact w37_28
  have w38_2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m38]; exact w37_2c
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m38]; exact w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m38]; exact w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m38]; exact w37_38
  have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m38]; exact w37_3c
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m38]; exact w37_40
  have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m38]; exact w37_44
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m38]; exact w37_48
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
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m38]; exact w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m38]; exact w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m38]; exact w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m38]; exact w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m38]; exact w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m38]; exact w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m38]; exact w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m38]; exact w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m38]; exact w37_94
  have w38_98 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m38]; exact w37_98
  have w38_9c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m38]; exact w37_9c
  have w38_a0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m38]; exact w37_a0
  have w38_a4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m38]; exact w37_a4
  have w38_a8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m38]; exact w37_a8
  have w38_ac : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m38]; exact w37_ac
  have w38_b0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m38]; exact w37_b0
  have w38_b4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m38]; exact w37_b4
  have w38_b8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m38]; exact w37_b8
  have w38_bc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m38]; exact w37_bc
  have w38_c0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m38]; exact w37_c0
  have w38_c4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m38]; exact w37_c4
  have w38_c8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m38]; exact w37_c8
  have w38_cc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m38]; exact w37_cc
  have w38_d0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m38]; exact w37_d0
  have w38_d4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m38]; exact w37_d4
  have w38_d8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m38]; exact w37_d8
  have w38_dc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m38]; exact w37_dc
  have w38_e0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m38]; exact w37_e0
  have w38_e4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m38]; exact w37_e4
  have w38_e8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m38]; exact w37_e8
  have w38_ec : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m38]; exact w37_ec
  have w38_f0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m38]; exact w37_f0
  have w38_f4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m38]; exact w37_f4
  have w38_f8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m38]; exact w37_f8
  have w38_fc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m38]; exact w37_fc
  have w38_100 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m38]; exact w37_100
  have w38_104 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m38]; exact w37_104
  have w38_108 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m38]; exact w37_108
  have w38_10c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m38]; exact w37_10c
  have w38_110 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m38]; exact w37_110
  have w38_114 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m38]; exact w37_114
  have w38_118 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m38]; exact w37_118
  have w38_11c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m38]; exact w37_11c
  have w38_120 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m38]; exact w37_120
  have w38_124 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m38]; exact w37_124
  have w38_128 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m38]; exact w37_128
  have w38_12c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m38]; exact w37_12c
  have w38_130 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m38]; exact w37_130
  have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m38]; exact w37_420
  have w38_424 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m38]; exact w37_424
  have w38_428 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m38]; exact w37_428
  have w38_42c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m38]; exact w37_42c
  have w38_a20 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m38]; exact w37_a20
  have w38_a24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m38]; exact w37_a24
  have w38_a28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m38]; exact w37_a28
  have w38_a2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m38]; exact w37_a2c
  have w38_a30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m38]; exact w37_a30
  have w38_a34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m38]; exact w37_a34
  have w38_a38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m38]; exact w37_a38
  have w38_a3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m38]; exact w37_a3c
  have w38_aa0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m38]; exact w37_aa0
  have w38_aa4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m38]; exact w37_aa4
  clear w37_aa4 w37_aa0 w37_a3c w37_a38 w37_a34 w37_a30 w37_a2c w37_a28 w37_a24 w37_a20 w37_42c w37_428 w37_424 w37_420 w37_130 w37_12c w37_128 w37_124 w37_120 w37_11c w37_118 w37_114 w37_110 w37_10c w37_108 w37_104 w37_100 w37_fc w37_f8 w37_f4 w37_f0 w37_ec w37_e8 w37_e4 w37_e0 w37_dc w37_d8 w37_d4 w37_d0 w37_cc w37_c8 w37_c4 w37_c0 w37_bc w37_b8 w37_b4 w37_b0 w37_ac w37_a8 w37_a4 w37_a0 w37_9c w37_98 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_44 w37_40 w37_3c w37_38 w37_34 w37_30 w37_2c w37_28 w37_24 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_19 g37_18 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  -- 0x2BC4: sw
  obtain ⟨n39, d39, s39, fr39, K39, W39, rg39⟩ := sv_sw F E38 s38 sv_at_2bc4 (off' := 0x2BC6) (c := 0x5C)
    (by decide) (by rw [g38_2]; sv_addr) (by decide) (by decide)
  have t39 : Steps n0 n39 := t38.trans d39
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.keep K39 (by decide)
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [rg39 sp, g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg39 (3 : Fin 32), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg39 (4 : Fin 32), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [rg39 (8 : Fin 32), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [rg39 (9 : Fin 32), g38_9]
  have g39_10 : reg n39 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [rg39 a0, g38_10]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [rg39 (18 : Fin 32), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [rg39 (19 : Fin 32), g38_19]
  have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [rg39 (21 : Fin 32), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [rg39 (22 : Fin 32), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [rg39 (23 : Fin 32), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = dg := by rw [rg39 (24 : Fin 32), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = ckl := by rw [rg39 (25 : Fin 32), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [rg39 (26 : Fin 32), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg39 (27 : Fin 32), g38_27]
  have w39_24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := (K39.w32 (by decide) (by decide)).trans w38_24
  have w39_28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K39.w32 (by decide) (by decide)).trans w38_28
  have w39_2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K39.w32 (by decide) (by decide)).trans w38_2c
  have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K39.w32 (by decide) (by decide)).trans w38_30
  have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K39.w32 (by decide) (by decide)).trans w38_34
  have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K39.w32 (by decide) (by decide)).trans w38_38
  have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K39.w32 (by decide) (by decide)).trans w38_3c
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K39.w32 (by decide) (by decide)).trans w38_40
  have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := (K39.w32 (by decide) (by decide)).trans w38_44
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := (K39.w32 (by decide) (by decide)).trans w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K39.w32 (by decide) (by decide)).trans w38_4c
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K39.w32 (by decide) (by decide)).trans w38_50
  have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K39.w32 (by decide) (by decide)).trans w38_54
  have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K39.w32 (by decide) (by decide)).trans w38_58
  have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K39.w32 (by decide) (by decide)).trans w38_60
  have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K39.w32 (by decide) (by decide)).trans w38_64
  have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K39.w32 (by decide) (by decide)).trans w38_68
  have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K39.w32 (by decide) (by decide)).trans w38_6c
  have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K39.w32 (by decide) (by decide)).trans w38_70
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := (K39.w32 (by decide) (by decide)).trans w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K39.w32 (by decide) (by decide)).trans w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K39.w32 (by decide) (by decide)).trans w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K39.w32 (by decide) (by decide)).trans w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K39.w32 (by decide) (by decide)).trans w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K39.w32 (by decide) (by decide)).trans w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K39.w32 (by decide) (by decide)).trans w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K39.w32 (by decide) (by decide)).trans w38_90
  have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K39.w32 (by decide) (by decide)).trans w38_94
  have w39_98 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K39.w32 (by decide) (by decide)).trans w38_98
  have w39_9c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K39.w32 (by decide) (by decide)).trans w38_9c
  have w39_a0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K39.w32 (by decide) (by decide)).trans w38_a0
  have w39_a4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K39.w32 (by decide) (by decide)).trans w38_a4
  have w39_a8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K39.w32 (by decide) (by decide)).trans w38_a8
  have w39_ac : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K39.w32 (by decide) (by decide)).trans w38_ac
  have w39_b0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K39.w32 (by decide) (by decide)).trans w38_b0
  have w39_b4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K39.w32 (by decide) (by decide)).trans w38_b4
  have w39_b8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K39.w32 (by decide) (by decide)).trans w38_b8
  have w39_bc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K39.w32 (by decide) (by decide)).trans w38_bc
  have w39_c0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K39.w32 (by decide) (by decide)).trans w38_c0
  have w39_c4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K39.w32 (by decide) (by decide)).trans w38_c4
  have w39_c8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K39.w32 (by decide) (by decide)).trans w38_c8
  have w39_cc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K39.w32 (by decide) (by decide)).trans w38_cc
  have w39_d0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K39.w32 (by decide) (by decide)).trans w38_d0
  have w39_d4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K39.w32 (by decide) (by decide)).trans w38_d4
  have w39_d8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K39.w32 (by decide) (by decide)).trans w38_d8
  have w39_dc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K39.w32 (by decide) (by decide)).trans w38_dc
  have w39_e0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K39.w32 (by decide) (by decide)).trans w38_e0
  have w39_e4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K39.w32 (by decide) (by decide)).trans w38_e4
  have w39_e8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K39.w32 (by decide) (by decide)).trans w38_e8
  have w39_ec : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K39.w32 (by decide) (by decide)).trans w38_ec
  have w39_f0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K39.w32 (by decide) (by decide)).trans w38_f0
  have w39_f4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K39.w32 (by decide) (by decide)).trans w38_f4
  have w39_f8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K39.w32 (by decide) (by decide)).trans w38_f8
  have w39_fc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K39.w32 (by decide) (by decide)).trans w38_fc
  have w39_100 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K39.w32 (by decide) (by decide)).trans w38_100
  have w39_104 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K39.w32 (by decide) (by decide)).trans w38_104
  have w39_108 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K39.w32 (by decide) (by decide)).trans w38_108
  have w39_10c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K39.w32 (by decide) (by decide)).trans w38_10c
  have w39_110 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K39.w32 (by decide) (by decide)).trans w38_110
  have w39_114 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K39.w32 (by decide) (by decide)).trans w38_114
  have w39_118 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K39.w32 (by decide) (by decide)).trans w38_118
  have w39_11c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K39.w32 (by decide) (by decide)).trans w38_11c
  have w39_120 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K39.w32 (by decide) (by decide)).trans w38_120
  have w39_124 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K39.w32 (by decide) (by decide)).trans w38_124
  have w39_128 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K39.w32 (by decide) (by decide)).trans w38_128
  have w39_12c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K39.w32 (by decide) (by decide)).trans w38_12c
  have w39_130 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K39.w32 (by decide) (by decide)).trans w38_130
  have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := (K39.w32 (by decide) (by decide)).trans w38_420
  have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := (K39.w32 (by decide) (by decide)).trans w38_424
  have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := (K39.w32 (by decide) (by decide)).trans w38_428
  have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := (K39.w32 (by decide) (by decide)).trans w38_42c
  have w39_a20 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K39.w32 (by decide) (by decide)).trans w38_a20
  have w39_a24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K39.w32 (by decide) (by decide)).trans w38_a24
  have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K39.w32 (by decide) (by decide)).trans w38_a28
  have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K39.w32 (by decide) (by decide)).trans w38_a2c
  have w39_a30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K39.w32 (by decide) (by decide)).trans w38_a30
  have w39_a34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K39.w32 (by decide) (by decide)).trans w38_a34
  have w39_a38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K39.w32 (by decide) (by decide)).trans w38_a38
  have w39_a3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K39.w32 (by decide) (by decide)).trans w38_a3c
  have w39_aa0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K39.w32 (by decide) (by decide)).trans w38_aa0
  have w39_aa4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K39.w32 (by decide) (by decide)).trans w38_aa4
  have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [W39, g38_10]
  clear w38_aa4 w38_aa0 w38_a3c w38_a38 w38_a34 w38_a30 w38_a2c w38_a28 w38_a24 w38_a20 w38_42c w38_428 w38_424 w38_420 w38_130 w38_12c w38_128 w38_124 w38_120 w38_11c w38_118 w38_114 w38_110 w38_10c w38_108 w38_104 w38_100 w38_fc w38_f8 w38_f4 w38_f0 w38_ec w38_e8 w38_e4 w38_e0 w38_dc w38_d8 w38_d4 w38_d0 w38_cc w38_c8 w38_c4 w38_c0 w38_bc w38_b8 w38_b4 w38_b0 w38_ac w38_a8 w38_a4 w38_a0 w38_9c w38_98 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_44 w38_40 w38_3c w38_38 w38_34 w38_30 w38_2c w38_28 w38_24 g38_10 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38
  by_cases hsig : BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) ≠ 0
  rotate_left
  · -- 0x2BC6: branch, taken
    obtain ⟨n40, d40, u40⟩ := s39.taken E39.self 0x2FF2 sv_at_2bc6
      (by decide) (by rw [g39_10, s39.zero]; exact br_beq_t (Decidable.of_not_not hsig))
    have s40 : St n40.mem SV n40 0x2FF2 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
    have m40 : n40.mem = n39.mem := u40.mem
    have fr40 : ∀ x, SvR B x → n40.mem x = n39.mem x := fun x _ => by rw [m40]
    have t40 : Steps n0 n40 := t39.trans (.single d40)
    have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
    have E40 : SvCode n40.mem := E39.fr F fr40
    have V40 : SvSaves B n40.mem v := V39.same m40
    have g40_2 : reg n40 sp = B + 0x21A0 := by rw [u40.regs, g39_2]
    have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u40.regs, g39_3]
    have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u40.regs, g39_4]
    have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u40.regs, g39_8]
    have g40_9 : reg n40 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u40.regs, g39_9]
    have g40_10 : reg n40 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [u40.regs, g39_10]
    have g40_18 : reg n40 (18 : Fin 32) = out := by rw [u40.regs, g39_18]
    have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [u40.regs, g39_19]
    have g40_21 : reg n40 (21 : Fin 32) = x21 := by rw [u40.regs, g39_21]
    have g40_22 : reg n40 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u40.regs, g39_22]
    have g40_23 : reg n40 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u40.regs, g39_23]
    have g40_24 : reg n40 (24 : Fin 32) = dg := by rw [u40.regs, g39_24]
    have g40_25 : reg n40 (25 : Fin 32) = ckl := by rw [u40.regs, g39_25]
    have g40_26 : reg n40 (26 : Fin 32) = x26 := by rw [u40.regs, g39_26]
    have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u40.regs, g39_27]
    have w40_24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m40]; exact w39_24
    have w40_28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m40]; exact w39_28
    have w40_2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m40]; exact w39_2c
    have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m40]; exact w39_30
    have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m40]; exact w39_34
    have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m40]; exact w39_38
    have w40_3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m40]; exact w39_3c
    have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m40]; exact w39_40
    have w40_44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m40]; exact w39_44
    have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m40]; exact w39_48
    have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m40]; exact w39_4c
    have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m40]; exact w39_50
    have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m40]; exact w39_54
    have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m40]; exact w39_58
    have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m40]; exact w39_5c
    have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m40]; exact w39_60
    have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m40]; exact w39_64
    have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m40]; exact w39_68
    have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m40]; exact w39_6c
    have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m40]; exact w39_70
    have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m40]; exact w39_74
    have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m40]; exact w39_78
    have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m40]; exact w39_7c
    have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m40]; exact w39_80
    have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m40]; exact w39_84
    have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m40]; exact w39_88
    have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m40]; exact w39_8c
    have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m40]; exact w39_90
    have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m40]; exact w39_94
    have w40_98 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m40]; exact w39_98
    have w40_9c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m40]; exact w39_9c
    have w40_a0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m40]; exact w39_a0
    have w40_a4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m40]; exact w39_a4
    have w40_a8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m40]; exact w39_a8
    have w40_ac : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m40]; exact w39_ac
    have w40_b0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m40]; exact w39_b0
    have w40_b4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m40]; exact w39_b4
    have w40_b8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m40]; exact w39_b8
    have w40_bc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m40]; exact w39_bc
    have w40_c0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m40]; exact w39_c0
    have w40_c4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m40]; exact w39_c4
    have w40_c8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m40]; exact w39_c8
    have w40_cc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m40]; exact w39_cc
    have w40_d0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m40]; exact w39_d0
    have w40_d4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m40]; exact w39_d4
    have w40_d8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m40]; exact w39_d8
    have w40_dc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m40]; exact w39_dc
    have w40_e0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m40]; exact w39_e0
    have w40_e4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m40]; exact w39_e4
    have w40_e8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m40]; exact w39_e8
    have w40_ec : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m40]; exact w39_ec
    have w40_f0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m40]; exact w39_f0
    have w40_f4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m40]; exact w39_f4
    have w40_f8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m40]; exact w39_f8
    have w40_fc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m40]; exact w39_fc
    have w40_100 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m40]; exact w39_100
    have w40_104 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m40]; exact w39_104
    have w40_108 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m40]; exact w39_108
    have w40_10c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m40]; exact w39_10c
    have w40_110 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m40]; exact w39_110
    have w40_114 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m40]; exact w39_114
    have w40_118 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m40]; exact w39_118
    have w40_11c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m40]; exact w39_11c
    have w40_120 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m40]; exact w39_120
    have w40_124 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m40]; exact w39_124
    have w40_128 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m40]; exact w39_128
    have w40_12c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m40]; exact w39_12c
    have w40_130 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m40]; exact w39_130
    have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m40]; exact w39_420
    have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m40]; exact w39_424
    have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m40]; exact w39_428
    have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m40]; exact w39_42c
    have w40_a20 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m40]; exact w39_a20
    have w40_a24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m40]; exact w39_a24
    have w40_a28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m40]; exact w39_a28
    have w40_a2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m40]; exact w39_a2c
    have w40_a30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m40]; exact w39_a30
    have w40_a34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m40]; exact w39_a34
    have w40_a38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m40]; exact w39_a38
    have w40_a3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m40]; exact w39_a3c
    have w40_aa0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m40]; exact w39_aa0
    have w40_aa4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m40]; exact w39_aa4
    clear w39_5c w39_aa4 w39_aa0 w39_a3c w39_a38 w39_a34 w39_a30 w39_a2c w39_a28 w39_a24 w39_a20 w39_42c w39_428 w39_424 w39_420 w39_130 w39_12c w39_128 w39_124 w39_120 w39_11c w39_118 w39_114 w39_110 w39_10c w39_108 w39_104 w39_100 w39_fc w39_f8 w39_f4 w39_f0 w39_ec w39_e8 w39_e4 w39_e0 w39_dc w39_d8 w39_d4 w39_d0 w39_cc w39_c8 w39_c4 w39_c0 w39_bc w39_b8 w39_b4 w39_b0 w39_ac w39_a8 w39_a4 w39_a0 w39_9c w39_98 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_58 w39_54 w39_50 w39_4c w39_48 w39_44 w39_40 w39_3c w39_38 w39_34 w39_30 w39_2c w39_28 w39_24 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_19 g39_18 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 rg39 W39 K39 fr39 s39 d39
    -- 0x2FF2
    obtain ⟨n41, c41, u41⟩ := s40.block svCk12ff2 E40.self svCk12ff2_end
      ⟨trivial, trivial⟩
    have m41 : n41.mem = n40.mem := u41.mem
    have s41 : St n41.mem SV n41 0x2FF4 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
    have rb41 : ∀ q, reg n41 q = (runBlock svCk12ff2 (n40.mem, reg n40)).2 q := fun q => by rw [u41.regs]
    have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
    have t41 : Steps n0 n41 := t40.trans c41
    have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
    have E41 : SvCode n41.mem := E40.fr F fr41
    have V41 : SvSaves B n41.mem v := V40.same m41
    have g41_2 : reg n41 sp = B + 0x21A0 := by
      rw [rb41, runBlock_reg _ _ _ sp s40.zero (by decide), g40_2]
    have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb41, runBlock_reg _ _ _ (3 : Fin 32) s40.zero (by decide), g40_3]
    have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb41, runBlock_reg _ _ _ (4 : Fin 32) s40.zero (by decide), g40_4]
    have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by
      rw [rb41, runBlock_reg _ _ _ (8 : Fin 32) s40.zero (by decide), g40_8]
    have g41_9 : reg n41 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by
      rw [rb41, runBlock_reg _ _ _ (9 : Fin 32) s40.zero (by decide), g40_9]
    have g41_10 : reg n41 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by
      rw [rb41, runBlock_reg _ _ _ a0 s40.zero (by decide), g40_10]
    have g41_18 : reg n41 (18 : Fin 32) = out := by
      rw [rb41, runBlock_reg _ _ _ (18 : Fin 32) s40.zero (by decide), g40_18]
    have g41_19 : reg n41 (19 : Fin 32) = bp := by
      rw [rb41, runBlock_reg _ _ _ (19 : Fin 32) s40.zero (by decide), g40_19]
    have g41_21 : reg n41 (21 : Fin 32) = x21 := by
      rw [rb41, runBlock_reg _ _ _ (21 : Fin 32) s40.zero (by decide), g40_21]
    have g41_22 : reg n41 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by
      rw [rb41, runBlock_reg _ _ _ (22 : Fin 32) s40.zero (by decide), g40_22]
    have g41_23 : reg n41 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by
      rw [rb41, runBlock_reg _ _ _ (23 : Fin 32) s40.zero (by decide), g40_23]
    have g41_24 : reg n41 (24 : Fin 32) = dg := by
      rw [rb41, runBlock_reg _ _ _ (24 : Fin 32) s40.zero (by decide), g40_24]
    have g41_25 : reg n41 (25 : Fin 32) = ckl := by
      rw [rb41, runBlock_reg _ _ _ (25 : Fin 32) s40.zero (by decide), g40_25]
    have g41_26 : reg n41 (26 : Fin 32) = x26 := by
      rw [rb41, runBlock_reg _ _ _ (26 : Fin 32) s40.zero (by decide), g40_26]
    have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb41, runBlock_reg _ _ _ (27 : Fin 32) s40.zero (by decide), g40_27]
    have g41_20 : reg n41 (20 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb41]; simp +decide only [runBlock, BInstr.run, svCk12ff2, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g40_2, g40_3, g40_4, g40_8, g40_9, g40_10, g40_18, g40_19, g40_21, g40_22, g40_23, g40_24, g40_25, g40_26, g40_27, s40.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w41_24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m41]; exact w40_24
    have w41_28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m41]; exact w40_28
    have w41_2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m41]; exact w40_2c
    have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m41]; exact w40_30
    have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m41]; exact w40_34
    have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m41]; exact w40_38
    have w41_3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m41]; exact w40_3c
    have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m41]; exact w40_40
    have w41_44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m41]; exact w40_44
    have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m41]; exact w40_48
    have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m41]; exact w40_4c
    have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m41]; exact w40_50
    have w41_54 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m41]; exact w40_54
    have w41_58 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m41]; exact w40_58
    have w41_5c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m41]; exact w40_5c
    have w41_60 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m41]; exact w40_60
    have w41_64 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m41]; exact w40_64
    have w41_68 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m41]; exact w40_68
    have w41_6c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m41]; exact w40_6c
    have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m41]; exact w40_70
    have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m41]; exact w40_74
    have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m41]; exact w40_78
    have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m41]; exact w40_7c
    have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m41]; exact w40_80
    have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m41]; exact w40_84
    have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m41]; exact w40_88
    have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m41]; exact w40_8c
    have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m41]; exact w40_90
    have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m41]; exact w40_94
    have w41_98 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m41]; exact w40_98
    have w41_9c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m41]; exact w40_9c
    have w41_a0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m41]; exact w40_a0
    have w41_a4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m41]; exact w40_a4
    have w41_a8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m41]; exact w40_a8
    have w41_ac : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m41]; exact w40_ac
    have w41_b0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m41]; exact w40_b0
    have w41_b4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m41]; exact w40_b4
    have w41_b8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m41]; exact w40_b8
    have w41_bc : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m41]; exact w40_bc
    have w41_c0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m41]; exact w40_c0
    have w41_c4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m41]; exact w40_c4
    have w41_c8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m41]; exact w40_c8
    have w41_cc : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m41]; exact w40_cc
    have w41_d0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m41]; exact w40_d0
    have w41_d4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m41]; exact w40_d4
    have w41_d8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m41]; exact w40_d8
    have w41_dc : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m41]; exact w40_dc
    have w41_e0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m41]; exact w40_e0
    have w41_e4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m41]; exact w40_e4
    have w41_e8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m41]; exact w40_e8
    have w41_ec : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m41]; exact w40_ec
    have w41_f0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m41]; exact w40_f0
    have w41_f4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m41]; exact w40_f4
    have w41_f8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m41]; exact w40_f8
    have w41_fc : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m41]; exact w40_fc
    have w41_100 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m41]; exact w40_100
    have w41_104 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m41]; exact w40_104
    have w41_108 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m41]; exact w40_108
    have w41_10c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m41]; exact w40_10c
    have w41_110 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m41]; exact w40_110
    have w41_114 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m41]; exact w40_114
    have w41_118 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m41]; exact w40_118
    have w41_11c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m41]; exact w40_11c
    have w41_120 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m41]; exact w40_120
    have w41_124 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m41]; exact w40_124
    have w41_128 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m41]; exact w40_128
    have w41_12c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m41]; exact w40_12c
    have w41_130 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m41]; exact w40_130
    have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m41]; exact w40_420
    have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m41]; exact w40_424
    have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m41]; exact w40_428
    have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m41]; exact w40_42c
    have w41_a20 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m41]; exact w40_a20
    have w41_a24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m41]; exact w40_a24
    have w41_a28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m41]; exact w40_a28
    have w41_a2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m41]; exact w40_a2c
    have w41_a30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m41]; exact w40_a30
    have w41_a34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m41]; exact w40_a34
    have w41_a38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m41]; exact w40_a38
    have w41_a3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m41]; exact w40_a3c
    have w41_aa0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m41]; exact w40_aa0
    have w41_aa4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m41]; exact w40_aa4
    clear w40_aa4 w40_aa0 w40_a3c w40_a38 w40_a34 w40_a30 w40_a2c w40_a28 w40_a24 w40_a20 w40_42c w40_428 w40_424 w40_420 w40_130 w40_12c w40_128 w40_124 w40_120 w40_11c w40_118 w40_114 w40_110 w40_10c w40_108 w40_104 w40_100 w40_fc w40_f8 w40_f4 w40_f0 w40_ec w40_e8 w40_e4 w40_e0 w40_dc w40_d8 w40_d4 w40_d0 w40_cc w40_c8 w40_c4 w40_c0 w40_bc w40_b8 w40_b4 w40_b0 w40_ac w40_a8 w40_a4 w40_a0 w40_9c w40_98 w40_94 w40_90 w40_8c w40_88 w40_84 w40_80 w40_7c w40_78 w40_74 w40_70 w40_6c w40_68 w40_64 w40_60 w40_5c w40_58 w40_54 w40_50 w40_4c w40_48 w40_44 w40_40 w40_3c w40_38 w40_34 w40_30 w40_2c w40_28 w40_24 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_19 g40_18 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 m40 s40 u40 d40
    -- 0x2FF4: j
    obtain ⟨n42, d42, u42⟩ := s41.jump E41.self sv_at_2ff4 (off' := 0x966) (by decide)
      (by rw [s41.pc]; decide)
    have s42 : St n42.mem SV n42 0x966 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
    have t42 : Steps n0 n42 := t41.trans (.single d42)
    have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
    have E42 : SvCode n42.mem := E41.fr F fr42
    have V42 : SvSaves B n42.mem v := V41.same m42
    have g42_2 : reg n42 sp = B + 0x21A0 := by rw [u42.regs, g41_2]
    have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u42.regs, g41_3]
    have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u42.regs, g41_4]
    have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u42.regs, g41_8]
    have g42_9 : reg n42 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u42.regs, g41_9]
    have g42_10 : reg n42 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [u42.regs, g41_10]
    have g42_18 : reg n42 (18 : Fin 32) = out := by rw [u42.regs, g41_18]
    have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [u42.regs, g41_19]
    have g42_20 : reg n42 (20 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u42.regs, g41_20]
    have g42_21 : reg n42 (21 : Fin 32) = x21 := by rw [u42.regs, g41_21]
    have g42_22 : reg n42 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u42.regs, g41_22]
    have g42_23 : reg n42 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u42.regs, g41_23]
    have g42_24 : reg n42 (24 : Fin 32) = dg := by rw [u42.regs, g41_24]
    have g42_25 : reg n42 (25 : Fin 32) = ckl := by rw [u42.regs, g41_25]
    have g42_26 : reg n42 (26 : Fin 32) = x26 := by rw [u42.regs, g41_26]
    have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u42.regs, g41_27]
    have w42_24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m42]; exact w41_24
    have w42_28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m42]; exact w41_28
    have w42_2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m42]; exact w41_2c
    have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m42]; exact w41_30
    have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m42]; exact w41_34
    have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m42]; exact w41_38
    have w42_3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m42]; exact w41_3c
    have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m42]; exact w41_40
    have w42_44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m42]; exact w41_44
    have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m42]; exact w41_48
    have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m42]; exact w41_4c
    have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m42]; exact w41_50
    have w42_54 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m42]; exact w41_54
    have w42_58 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m42]; exact w41_58
    have w42_5c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m42]; exact w41_5c
    have w42_60 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m42]; exact w41_60
    have w42_64 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m42]; exact w41_64
    have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m42]; exact w41_68
    have w42_6c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m42]; exact w41_6c
    have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m42]; exact w41_70
    have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m42]; exact w41_74
    have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m42]; exact w41_78
    have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m42]; exact w41_7c
    have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m42]; exact w41_80
    have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m42]; exact w41_84
    have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m42]; exact w41_88
    have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m42]; exact w41_8c
    have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m42]; exact w41_90
    have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m42]; exact w41_94
    have w42_98 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m42]; exact w41_98
    have w42_9c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m42]; exact w41_9c
    have w42_a0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m42]; exact w41_a0
    have w42_a4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m42]; exact w41_a4
    have w42_a8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m42]; exact w41_a8
    have w42_ac : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m42]; exact w41_ac
    have w42_b0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m42]; exact w41_b0
    have w42_b4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m42]; exact w41_b4
    have w42_b8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m42]; exact w41_b8
    have w42_bc : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m42]; exact w41_bc
    have w42_c0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m42]; exact w41_c0
    have w42_c4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m42]; exact w41_c4
    have w42_c8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m42]; exact w41_c8
    have w42_cc : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m42]; exact w41_cc
    have w42_d0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m42]; exact w41_d0
    have w42_d4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m42]; exact w41_d4
    have w42_d8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m42]; exact w41_d8
    have w42_dc : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m42]; exact w41_dc
    have w42_e0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m42]; exact w41_e0
    have w42_e4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m42]; exact w41_e4
    have w42_e8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m42]; exact w41_e8
    have w42_ec : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m42]; exact w41_ec
    have w42_f0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m42]; exact w41_f0
    have w42_f4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m42]; exact w41_f4
    have w42_f8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m42]; exact w41_f8
    have w42_fc : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m42]; exact w41_fc
    have w42_100 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m42]; exact w41_100
    have w42_104 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m42]; exact w41_104
    have w42_108 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m42]; exact w41_108
    have w42_10c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m42]; exact w41_10c
    have w42_110 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m42]; exact w41_110
    have w42_114 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m42]; exact w41_114
    have w42_118 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m42]; exact w41_118
    have w42_11c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m42]; exact w41_11c
    have w42_120 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m42]; exact w41_120
    have w42_124 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m42]; exact w41_124
    have w42_128 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m42]; exact w41_128
    have w42_12c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m42]; exact w41_12c
    have w42_130 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m42]; exact w41_130
    have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m42]; exact w41_420
    have w42_424 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m42]; exact w41_424
    have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m42]; exact w41_428
    have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m42]; exact w41_42c
    have w42_a20 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m42]; exact w41_a20
    have w42_a24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m42]; exact w41_a24
    have w42_a28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m42]; exact w41_a28
    have w42_a2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m42]; exact w41_a2c
    have w42_a30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m42]; exact w41_a30
    have w42_a34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m42]; exact w41_a34
    have w42_a38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m42]; exact w41_a38
    have w42_a3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m42]; exact w41_a3c
    have w42_aa0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m42]; exact w41_aa0
    have w42_aa4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m42]; exact w41_aa4
    clear w41_aa4 w41_aa0 w41_a3c w41_a38 w41_a34 w41_a30 w41_a2c w41_a28 w41_a24 w41_a20 w41_42c w41_428 w41_424 w41_420 w41_130 w41_12c w41_128 w41_124 w41_120 w41_11c w41_118 w41_114 w41_110 w41_10c w41_108 w41_104 w41_100 w41_fc w41_f8 w41_f4 w41_f0 w41_ec w41_e8 w41_e4 w41_e0 w41_dc w41_d8 w41_d4 w41_d0 w41_cc w41_c8 w41_c4 w41_c0 w41_bc w41_b8 w41_b4 w41_b0 w41_ac w41_a8 w41_a4 w41_a0 w41_9c w41_98 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_74 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_44 w41_40 w41_3c w41_38 w41_34 w41_30 w41_2c w41_28 w41_24 g41_20 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_19 g41_18 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 rb41 s41 m41 u41 c41
    exact .inl ⟨(fun ⟨h0', ix7', h1', ix17', h2', ix25', h3', ix33', h4', h5', h6', _⟩ => by rw [hr7] at h1'; cases h1'; rw [hr17] at h2'; cases h2'; rw [hr25] at h3'; cases h3'; rw [hr33] at h4'; cases h4'; exact hsig h6'), sv_fail F E42 s42 t42 (fun x hx => (fR42 x hx).trans (fM x hx).symm) V42 hret g42_2 g42_18 hO g42_3 g42_4⟩
  -- 0x2BC6: branch, not taken
  obtain ⟨n40, d40, u40⟩ := s39.notTaken E39.self 0x2BCA sv_at_2bc6
    (by decide) (by rw [g39_10, s39.zero]; exact br_beq_f hsig)
  have s40 : St n40.mem SV n40 0x2BCA (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have fr40 : ∀ x, SvR B x → n40.mem x = n39.mem x := fun x _ => by rw [m40]
  have t40 : Steps n0 n40 := t39.trans (.single d40)
  have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.same m40
  have g40_2 : reg n40 sp = B + 0x21A0 := by rw [u40.regs, g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u40.regs, g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u40.regs, g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 ix17 := by rw [u40.regs, g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = (ckp) + BitVec.ofNat 32 (ix7 + 1) := by rw [u40.regs, g39_9]
  have g40_10 : reg n40 a0 = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [u40.regs, g39_10]
  have g40_18 : reg n40 (18 : Fin 32) = out := by rw [u40.regs, g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [u40.regs, g39_19]
  have g40_21 : reg n40 (21 : Fin 32) = x21 := by rw [u40.regs, g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = BitVec.ofNat 32 ix25 := by rw [u40.regs, g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1) := by rw [u40.regs, g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = dg := by rw [u40.regs, g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = ckl := by rw [u40.regs, g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by rw [u40.regs, g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u40.regs, g39_27]
  have w40_24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp := by rw [m40]; exact w39_24
  have w40_28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m40]; exact w39_28
  have w40_2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m40]; exact w39_2c
  have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m40]; exact w39_30
  have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m40]; exact w39_34
  have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m40]; exact w39_38
  have w40_3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m40]; exact w39_3c
  have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m40]; exact w39_40
  have w40_44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix7 := by rw [m40]; exact w39_44
  have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp := by rw [m40]; exact w39_48
  have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m40]; exact w39_4c
  have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m40]; exact w39_50
  have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m40]; exact w39_54
  have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m40]; exact w39_58
  have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m40]; exact w39_5c
  have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m40]; exact w39_60
  have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m40]; exact w39_64
  have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m40]; exact w39_68
  have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m40]; exact w39_6c
  have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m40]; exact w39_70
  have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q := by rw [m40]; exact w39_74
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m40]; exact w39_78
  have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m40]; exact w39_7c
  have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m40]; exact w39_80
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m40]; exact w39_84
  have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m40]; exact w39_88
  have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m40]; exact w39_8c
  have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m40]; exact w39_90
  have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m40]; exact w39_94
  have w40_98 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m40]; exact w39_98
  have w40_9c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m40]; exact w39_9c
  have w40_a0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m40]; exact w39_a0
  have w40_a4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m40]; exact w39_a4
  have w40_a8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m40]; exact w39_a8
  have w40_ac : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m40]; exact w39_ac
  have w40_b0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m40]; exact w39_b0
  have w40_b4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m40]; exact w39_b4
  have w40_b8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m40]; exact w39_b8
  have w40_bc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m40]; exact w39_bc
  have w40_c0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m40]; exact w39_c0
  have w40_c4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m40]; exact w39_c4
  have w40_c8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m40]; exact w39_c8
  have w40_cc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m40]; exact w39_cc
  have w40_d0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m40]; exact w39_d0
  have w40_d4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m40]; exact w39_d4
  have w40_d8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m40]; exact w39_d8
  have w40_dc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m40]; exact w39_dc
  have w40_e0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m40]; exact w39_e0
  have w40_e4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m40]; exact w39_e4
  have w40_e8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m40]; exact w39_e8
  have w40_ec : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m40]; exact w39_ec
  have w40_f0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m40]; exact w39_f0
  have w40_f4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m40]; exact w39_f4
  have w40_f8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m40]; exact w39_f8
  have w40_fc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m40]; exact w39_fc
  have w40_100 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m40]; exact w39_100
  have w40_104 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m40]; exact w39_104
  have w40_108 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m40]; exact w39_108
  have w40_10c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m40]; exact w39_10c
  have w40_110 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m40]; exact w39_110
  have w40_114 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m40]; exact w39_114
  have w40_118 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m40]; exact w39_118
  have w40_11c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m40]; exact w39_11c
  have w40_120 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m40]; exact w39_120
  have w40_124 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m40]; exact w39_124
  have w40_128 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m40]; exact w39_128
  have w40_12c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m40]; exact w39_12c
  have w40_130 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m40]; exact w39_130
  have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1) := by rw [m40]; exact w39_420
  have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 ix33 := by rw [m40]; exact w39_424
  have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((ckp) + BitVec.ofNat 32 (ix7 + 1)) + BitVec.ofNat 32 (ix17 + 1)) + BitVec.ofNat 32 (ix25 + 1)) + BitVec.ofNat 32 (ix33 + 1) := by rw [m40]; exact w39_428
  have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix7 + 1)) - (ix17 + 1)) - (ix25 + 1)) - BitVec.ofNat 32 (ix33 + 1) := by rw [m40]; exact w39_42c
  have w40_a20 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m40]; exact w39_a20
  have w40_a24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m40]; exact w39_a24
  have w40_a28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m40]; exact w39_a28
  have w40_a2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m40]; exact w39_a2c
  have w40_a30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m40]; exact w39_a30
  have w40_a34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m40]; exact w39_a34
  have w40_a38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m40]; exact w39_a38
  have w40_a3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m40]; exact w39_a3c
  have w40_aa0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m40]; exact w39_aa0
  have w40_aa4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m40]; exact w39_aa4
  clear w39_5c w39_aa4 w39_aa0 w39_a3c w39_a38 w39_a34 w39_a30 w39_a2c w39_a28 w39_a24 w39_a20 w39_42c w39_428 w39_424 w39_420 w39_130 w39_12c w39_128 w39_124 w39_120 w39_11c w39_118 w39_114 w39_110 w39_10c w39_108 w39_104 w39_100 w39_fc w39_f8 w39_f4 w39_f0 w39_ec w39_e8 w39_e4 w39_e0 w39_dc w39_d8 w39_d4 w39_d0 w39_cc w39_c8 w39_c4 w39_c0 w39_bc w39_b8 w39_b4 w39_b0 w39_ac w39_a8 w39_a4 w39_a0 w39_9c w39_98 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_58 w39_54 w39_50 w39_4c w39_48 w39_44 w39_40 w39_3c w39_38 w39_34 w39_30 w39_2c w39_28 w39_24 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_19 g39_18 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 rg39 W39 K39 fr39 s39 d39
  exact .inr ⟨hv, ix7, hr7, ix17, hr17, ix25, hr25, ix33, hr33, hblank, hsig, n40, t40, s40, E40, V40, fR40, g40_2, g40_3, g40_4, g40_8, g40_9, g40_18, g40_19, g40_21, g40_22, g40_23, g40_24, g40_25, g40_26, g40_27, w40_24, w40_28, w40_2c, w40_30, w40_34, w40_38, w40_3c, w40_40, w40_44, w40_48, w40_4c, w40_50, w40_54, w40_58, w40_5c, w40_60, w40_64, w40_68, w40_6c, w40_70, w40_74, w40_78, w40_7c, w40_80, w40_84, w40_88, w40_8c, w40_90, w40_94, w40_98, w40_9c, w40_a0, w40_a4, w40_a8, w40_ac, w40_b0, w40_b4, w40_b8, w40_bc, w40_c0, w40_c4, w40_c8, w40_cc, w40_d0, w40_d4, w40_d8, w40_dc, w40_e0, w40_e4, w40_e8, w40_ec, w40_f0, w40_f4, w40_f8, w40_fc, w40_100, w40_104, w40_108, w40_10c, w40_110, w40_114, w40_118, w40_11c, w40_120, w40_124, w40_128, w40_12c, w40_130, w40_428, w40_42c, w40_a20, w40_a24, w40_a28, w40_a2c, w40_a30, w40_a34, w40_a38, w40_a3c, w40_aa0, w40_aa4⟩

end C3.RV32.Sv
