import C3BootProofs.Proofs.SvCkpt

/-!
# `sigstore::verify`: the log key's hash

From the log's entry at 0x2D12 to the signature loop at 0x2D6E: the word at offset 0x14 is the first word of SHA-256 of the origin line, a newline, the Ed25519 key tag, and the log's key.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCs12d12 : List BInstr :=
  [.alu .add a1 x0 (25 : Fin 32)]
theorem svCs12d12_end : blockEnd sigstoreVerifyCode 0x2D12 svCs12d12 = some 0x2D14 := by
  simp only [svCs12d12]
  rw [blockEnd, sv_at_2d12]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCs12d1a : List BInstr :=
  [.lui a0 0x3FCC5000, .aluImm .add a0 a0 0xFFFFF850, .aluImm .add a1 x0 0x1]
theorem svCs12d1a_end : blockEnd sigstoreVerifyCode 0x2D1A svCs12d1a = some 0x2D24 := by
  simp only [svCs12d1a]
  rw [blockEnd, sv_at_2d1a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d1e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d22]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCs12d26 : List BInstr :=
  [.aluImm .add a4 sp 0x400]
theorem svCs12d26_end : blockEnd sigstoreVerifyCode 0x2D26 svCs12d26 = some 0x2D2A := by
  simp only [svCs12d26]
  rw [blockEnd, sv_at_2d26]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCs12d34 : List BInstr :=
  [.lui a0 0x3FCC4000, .aluImm .add a0 a0 0x7D7, .aluImm .add a2 x0 0x20]
theorem svCs12d34_end : blockEnd sigstoreVerifyCode 0x2D34 svCs12d34 = some 0x2D40 := by
  simp only [svCs12d34]
  rw [blockEnd, sv_at_2d34]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d38]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d3c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCs12d4a : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x380, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x420, .aluImm .add a2 x0 0x4]
theorem svCs12d4a_end : blockEnd sigstoreVerifyCode 0x2D4A svCs12d4a = some 0x2D58 := by
  simp only [svCs12d4a]
  rw [blockEnd, sv_at_2d4a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d4c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d50]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d52]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d56]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCs12d62 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add a0 a0 sp]
theorem svCs12d62_end : blockEnd sigstoreVerifyCode 0x2D62 svCs12d62 = some 0x2D6A := by
  simp only [svCs12d62]
  rw [blockEnd, sv_at_2d62]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d64]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d68]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_cs1 {B out bp x21 x26 dg c q rl rp sgp op ol kp kw : Word} {rt : Bytes} {w8 wc w10 w14 w18 w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x2D12 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = c)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = rl)
    (g0_23 : reg n0 (23 : Fin 32) = rp)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
    (g0_25 : reg n0 (25 : Fin 32) = q)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10)
    (w0_14 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18)
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32)
    (w0_20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20)
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
    (w0_428 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp)
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
    (q0_320 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (S2 : SvSha2Code M0)
    (KS : SvK2Sep B)
    (hkp : memLoad32 M0 (q + 0x18) = kp)
    (hkw : memLoad32 M0 (q + 0x1C) = kw)
    (kp_in4 : SvIn B (q + 0x18) 4)
    (kw_in4 : SvIn B (q + 0x1C) 4)
    (a_kp : (q + 0x18).toNat % 4 = 0)
    (a_kw : (q + 0x1C).toNat % 4 = 0)
    (kp_in : SvIn B kp 32)
    (l_in : SvIn B w48 w44.toNat) :
    (¬ (True) ∧ SvErrRet B out v n0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x2D6E (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = c ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = rl ∧
        reg n' (23 : Fin 32) = rp ∧
        reg n' (24 : Fin 32) = dg ∧
        reg n' (25 : Fin 32) = q ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x1380, 0x20), (0x30, 0x4), (0x14, 0x4)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x2D12
  obtain ⟨n1, c1, u1⟩ := s0.block svCs12d12 E0.self svCs12d12_end
    ⟨trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x2D14 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svCs12d12 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_9 : reg n1 (9 : Fin 32) = c := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = rl := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = rp := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = dg := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = q := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_11 : reg n1 a1 = q := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svCs12d12, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m1]; exact w0_8
  have w1_c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m1]; exact w0_c
  have w1_10 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m1]; exact w0_10
  have w1_14 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m1]; exact w0_14
  have w1_18 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18 := by rw [m1]; exact w0_18
  have w1_1c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m1]; exact w0_1c
  have w1_20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m1]; exact w0_20
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
  have w1_428 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m1]; exact w0_428
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
  have q1_320 : ∀ j, j < 31 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m1]; exact q0_320 j hj
  -- 0x2D14: lw outside the stack
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_2d14 (off' := 0x2D16) (by decide)
    (by rw [g1_11]; exact a_kp)
  have s2 : St n2.mem SV n2 0x2D16 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_9 : reg n2 (9 : Fin 32) = c := by rw [u2.regs, upd_ne (by decide) (by decide), g1_9]
  have g2_11 : reg n2 a1 = q := by rw [u2.regs, upd_ne (by decide) (by decide), g1_11]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = rl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = rp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = q := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_13 : reg n2 a3 = kp := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_11, sv_ld fR1 kp_in4, hkp]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m2]; exact w1_8
  have w2_c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m2]; exact w1_c
  have w2_10 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m2]; exact w1_10
  have w2_14 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m2]; exact w1_14
  have w2_18 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18 := by rw [m2]; exact w1_18
  have w2_1c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m2]; exact w1_1c
  have w2_20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m2]; exact w1_20
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
  have w2_428 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m2]; exact w1_428
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
  have q2_320 : ∀ j, j < 31 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m2]; exact q1_320 j hj
  clear q1_320 w1_aa4 w1_aa0 w1_a3c w1_a38 w1_a34 w1_a30 w1_a2c w1_a28 w1_a24 w1_a20 w1_428 w1_130 w1_12c w1_128 w1_124 w1_120 w1_11c w1_118 w1_114 w1_110 w1_10c w1_108 w1_104 w1_100 w1_fc w1_f8 w1_f4 w1_f0 w1_ec w1_e8 w1_e4 w1_e0 w1_dc w1_d8 w1_d4 w1_d0 w1_cc w1_c8 w1_c4 w1_c0 w1_bc w1_b8 w1_b4 w1_b0 w1_ac w1_a8 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 w1_20 w1_1c w1_18 w1_14 w1_10 w1_c w1_8 g1_11 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_9 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x2D16: lw outside the stack
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_2d16 (off' := 0x2D18) (by decide)
    (by rw [g2_11]; exact a_kw)
  have s3 : St n3.mem SV n3 0x2D18 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_9 : reg n3 (9 : Fin 32) = c := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_11 : reg n3 a1 = q := by rw [u3.regs, upd_ne (by decide) (by decide), g2_11]
  have g3_13 : reg n3 a3 = kp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_13]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = rl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = rp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = q := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = kw := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_11, sv_ld fR2 kw_in4, hkw]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m3]; exact w2_8
  have w3_c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m3]; exact w2_c
  have w3_10 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m3]; exact w2_10
  have w3_14 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m3]; exact w2_14
  have w3_18 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18 := by rw [m3]; exact w2_18
  have w3_1c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m3]; exact w2_1c
  have w3_20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m3]; exact w2_20
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
  have w3_428 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m3]; exact w2_428
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
  have q3_320 : ∀ j, j < 31 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m3]; exact q2_320 j hj
  clear q2_320 w2_aa4 w2_aa0 w2_a3c w2_a38 w2_a34 w2_a30 w2_a2c w2_a28 w2_a24 w2_a20 w2_428 w2_130 w2_12c w2_128 w2_124 w2_120 w2_11c w2_118 w2_114 w2_110 w2_10c w2_108 w2_104 w2_100 w2_fc w2_f8 w2_f4 w2_f0 w2_ec w2_e8 w2_e4 w2_e0 w2_dc w2_d8 w2_d4 w2_d0 w2_cc w2_c8 w2_c4 w2_c0 w2_bc w2_b8 w2_b4 w2_b0 w2_ac w2_a8 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_44 w2_40 w2_3c w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 w2_20 w2_1c w2_18 w2_14 w2_10 w2_c w2_8 g2_13 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_19 g2_18 g2_11 g2_9 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x2D18: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sw F E3 s3 sv_at_2d18 (off' := 0x2D1A) (c := 0x18)
    (by decide) (by rw [g3_2]; sv_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = c := by rw [rg4 (9 : Fin 32), g3_9]
  have g4_10 : reg n4 a0 = kw := by rw [rg4 a0, g3_10]
  have g4_11 : reg n4 a1 = q := by rw [rg4 a1, g3_11]
  have g4_13 : reg n4 a3 = kp := by rw [rg4 a3, g3_13]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rg4 (19 : Fin 32), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [rg4 (21 : Fin 32), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = rl := by rw [rg4 (22 : Fin 32), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = rp := by rw [rg4 (23 : Fin 32), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = dg := by rw [rg4 (24 : Fin 32), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = q := by rw [rg4 (25 : Fin 32), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [rg4 (26 : Fin 32), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg4 (27 : Fin 32), g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x18, 0x4)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have w4_8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K4.w32 (by decide) (by decide)).trans w3_8
  have w4_c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K4.w32 (by decide) (by decide)).trans w3_c
  have w4_10 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K4.w32 (by decide) (by decide)).trans w3_10
  have w4_14 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K4.w32 (by decide) (by decide)).trans w3_14
  have w4_1c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K4.w32 (by decide) (by decide)).trans w3_1c
  have w4_20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K4.w32 (by decide) (by decide)).trans w3_20
  have w4_24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K4.w32 (by decide) (by decide)).trans w3_24
  have w4_28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K4.w32 (by decide) (by decide)).trans w3_28
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K4.w32 (by decide) (by decide)).trans w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K4.w32 (by decide) (by decide)).trans w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K4.w32 (by decide) (by decide)).trans w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K4.w32 (by decide) (by decide)).trans w3_38
  have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K4.w32 (by decide) (by decide)).trans w3_3c
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K4.w32 (by decide) (by decide)).trans w3_40
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K4.w32 (by decide) (by decide)).trans w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K4.w32 (by decide) (by decide)).trans w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K4.w32 (by decide) (by decide)).trans w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K4.w32 (by decide) (by decide)).trans w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K4.w32 (by decide) (by decide)).trans w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K4.w32 (by decide) (by decide)).trans w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K4.w32 (by decide) (by decide)).trans w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K4.w32 (by decide) (by decide)).trans w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K4.w32 (by decide) (by decide)).trans w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K4.w32 (by decide) (by decide)).trans w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K4.w32 (by decide) (by decide)).trans w3_70
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K4.w32 (by decide) (by decide)).trans w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K4.w32 (by decide) (by decide)).trans w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K4.w32 (by decide) (by decide)).trans w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K4.w32 (by decide) (by decide)).trans w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K4.w32 (by decide) (by decide)).trans w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K4.w32 (by decide) (by decide)).trans w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K4.w32 (by decide) (by decide)).trans w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K4.w32 (by decide) (by decide)).trans w3_94
  have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K4.w32 (by decide) (by decide)).trans w3_98
  have w4_9c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K4.w32 (by decide) (by decide)).trans w3_9c
  have w4_a0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K4.w32 (by decide) (by decide)).trans w3_a0
  have w4_a4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K4.w32 (by decide) (by decide)).trans w3_a4
  have w4_a8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K4.w32 (by decide) (by decide)).trans w3_a8
  have w4_ac : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K4.w32 (by decide) (by decide)).trans w3_ac
  have w4_b0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K4.w32 (by decide) (by decide)).trans w3_b0
  have w4_b4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K4.w32 (by decide) (by decide)).trans w3_b4
  have w4_b8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K4.w32 (by decide) (by decide)).trans w3_b8
  have w4_bc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K4.w32 (by decide) (by decide)).trans w3_bc
  have w4_c0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K4.w32 (by decide) (by decide)).trans w3_c0
  have w4_c4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K4.w32 (by decide) (by decide)).trans w3_c4
  have w4_c8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K4.w32 (by decide) (by decide)).trans w3_c8
  have w4_cc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K4.w32 (by decide) (by decide)).trans w3_cc
  have w4_d0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K4.w32 (by decide) (by decide)).trans w3_d0
  have w4_d4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K4.w32 (by decide) (by decide)).trans w3_d4
  have w4_d8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K4.w32 (by decide) (by decide)).trans w3_d8
  have w4_dc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K4.w32 (by decide) (by decide)).trans w3_dc
  have w4_e0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K4.w32 (by decide) (by decide)).trans w3_e0
  have w4_e4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K4.w32 (by decide) (by decide)).trans w3_e4
  have w4_e8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K4.w32 (by decide) (by decide)).trans w3_e8
  have w4_ec : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K4.w32 (by decide) (by decide)).trans w3_ec
  have w4_f0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K4.w32 (by decide) (by decide)).trans w3_f0
  have w4_f4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K4.w32 (by decide) (by decide)).trans w3_f4
  have w4_f8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K4.w32 (by decide) (by decide)).trans w3_f8
  have w4_fc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K4.w32 (by decide) (by decide)).trans w3_fc
  have w4_100 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K4.w32 (by decide) (by decide)).trans w3_100
  have w4_104 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K4.w32 (by decide) (by decide)).trans w3_104
  have w4_108 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K4.w32 (by decide) (by decide)).trans w3_108
  have w4_10c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K4.w32 (by decide) (by decide)).trans w3_10c
  have w4_110 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K4.w32 (by decide) (by decide)).trans w3_110
  have w4_114 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K4.w32 (by decide) (by decide)).trans w3_114
  have w4_118 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K4.w32 (by decide) (by decide)).trans w3_118
  have w4_11c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K4.w32 (by decide) (by decide)).trans w3_11c
  have w4_120 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K4.w32 (by decide) (by decide)).trans w3_120
  have w4_124 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K4.w32 (by decide) (by decide)).trans w3_124
  have w4_128 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K4.w32 (by decide) (by decide)).trans w3_128
  have w4_12c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K4.w32 (by decide) (by decide)).trans w3_12c
  have w4_130 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K4.w32 (by decide) (by decide)).trans w3_130
  have w4_428 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := (K4.w32 (by decide) (by decide)).trans w3_428
  have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K4.w32 (by decide) (by decide)).trans w3_a20
  have w4_a24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K4.w32 (by decide) (by decide)).trans w3_a24
  have w4_a28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K4.w32 (by decide) (by decide)).trans w3_a28
  have w4_a2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K4.w32 (by decide) (by decide)).trans w3_a2c
  have w4_a30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K4.w32 (by decide) (by decide)).trans w3_a30
  have w4_a34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K4.w32 (by decide) (by decide)).trans w3_a34
  have w4_a38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K4.w32 (by decide) (by decide)).trans w3_a38
  have w4_a3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K4.w32 (by decide) (by decide)).trans w3_a3c
  have w4_aa0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K4.w32 (by decide) (by decide)).trans w3_aa0
  have w4_aa4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K4.w32 (by decide) (by decide)).trans w3_aa4
  have w4_18 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := by rw [W4, g3_10]
  have q4_320 : ∀ j, j < 31 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_320 j hj)
  clear q3_320 w3_aa4 w3_aa0 w3_a3c w3_a38 w3_a34 w3_a30 w3_a2c w3_a28 w3_a24 w3_a20 w3_428 w3_130 w3_12c w3_128 w3_124 w3_120 w3_11c w3_118 w3_114 w3_110 w3_10c w3_108 w3_104 w3_100 w3_fc w3_f8 w3_f4 w3_f0 w3_ec w3_e8 w3_e4 w3_e0 w3_dc w3_d8 w3_d4 w3_d0 w3_cc w3_c8 w3_c4 w3_c0 w3_bc w3_b8 w3_b4 w3_b0 w3_ac w3_a8 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 w3_20 w3_1c w3_18 w3_14 w3_10 w3_c w3_8 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_19 g3_18 g3_13 g3_11 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x2D1A
  obtain ⟨n5, c5, u5⟩ := s4.block svCs12d1a E4.self svCs12d1a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x2D24 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svCs12d1a (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_9 : reg n5 (9 : Fin 32) = c := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_13 : reg n5 a3 = kp := by
    rw [rb5, runBlock_reg _ _ _ a3 s4.zero (by decide), g4_13]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = rl := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = rp := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = dg := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = q := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 0x3FCC4850 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svCs12d1a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_10, g4_11, g4_13, g4_18, g4_19, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_11 : reg n5 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svCs12d1a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_10, g4_11, g4_13, g4_18, g4_19, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x18, 0x4)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m5]; exact w4_8
  have w5_c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m5]; exact w4_c
  have w5_10 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m5]; exact w4_10
  have w5_14 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m5]; exact w4_14
  have w5_18 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := by rw [m5]; exact w4_18
  have w5_1c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m5]; exact w4_1c
  have w5_20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m5]; exact w4_20
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
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m5]; exact w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m5]; exact w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m5]; exact w4_94
  have w5_98 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m5]; exact w4_98
  have w5_9c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m5]; exact w4_9c
  have w5_a0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m5]; exact w4_a0
  have w5_a4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m5]; exact w4_a4
  have w5_a8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m5]; exact w4_a8
  have w5_ac : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m5]; exact w4_ac
  have w5_b0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m5]; exact w4_b0
  have w5_b4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m5]; exact w4_b4
  have w5_b8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m5]; exact w4_b8
  have w5_bc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m5]; exact w4_bc
  have w5_c0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m5]; exact w4_c0
  have w5_c4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m5]; exact w4_c4
  have w5_c8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m5]; exact w4_c8
  have w5_cc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m5]; exact w4_cc
  have w5_d0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m5]; exact w4_d0
  have w5_d4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m5]; exact w4_d4
  have w5_d8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m5]; exact w4_d8
  have w5_dc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m5]; exact w4_dc
  have w5_e0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m5]; exact w4_e0
  have w5_e4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m5]; exact w4_e4
  have w5_e8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m5]; exact w4_e8
  have w5_ec : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m5]; exact w4_ec
  have w5_f0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m5]; exact w4_f0
  have w5_f4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m5]; exact w4_f4
  have w5_f8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m5]; exact w4_f8
  have w5_fc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m5]; exact w4_fc
  have w5_100 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m5]; exact w4_100
  have w5_104 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m5]; exact w4_104
  have w5_108 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m5]; exact w4_108
  have w5_10c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m5]; exact w4_10c
  have w5_110 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m5]; exact w4_110
  have w5_114 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m5]; exact w4_114
  have w5_118 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m5]; exact w4_118
  have w5_11c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m5]; exact w4_11c
  have w5_120 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m5]; exact w4_120
  have w5_124 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m5]; exact w4_124
  have w5_128 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m5]; exact w4_128
  have w5_12c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m5]; exact w4_12c
  have w5_130 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m5]; exact w4_130
  have w5_428 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m5]; exact w4_428
  have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m5]; exact w4_a20
  have w5_a24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m5]; exact w4_a24
  have w5_a28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m5]; exact w4_a28
  have w5_a2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m5]; exact w4_a2c
  have w5_a30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m5]; exact w4_a30
  have w5_a34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m5]; exact w4_a34
  have w5_a38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m5]; exact w4_a38
  have w5_a3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m5]; exact w4_a3c
  have w5_aa0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m5]; exact w4_aa0
  have w5_aa4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m5]; exact w4_aa4
  have q5_320 : ∀ j, j < 31 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_320 j hj
  clear q4_320 w4_18 w4_aa4 w4_aa0 w4_a3c w4_a38 w4_a34 w4_a30 w4_a2c w4_a28 w4_a24 w4_a20 w4_428 w4_130 w4_12c w4_128 w4_124 w4_120 w4_11c w4_118 w4_114 w4_110 w4_10c w4_108 w4_104 w4_100 w4_fc w4_f8 w4_f4 w4_f0 w4_ec w4_e8 w4_e4 w4_e0 w4_dc w4_d8 w4_d4 w4_d0 w4_cc w4_c8 w4_c4 w4_c0 w4_bc w4_b8 w4_b4 w4_b0 w4_ac w4_a8 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 w4_20 w4_1c w4_14 w4_10 w4_c w4_8 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_19 g4_18 g4_13 g4_11 g4_10 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  -- 0x2D24: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_2d24 (off' := 0x2D26) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x2D26 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = c := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 0x3FCC4850 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 0x1 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_11]
  have g6_13 : reg n6 a3 = kp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_13]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = rl := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = rp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = dg := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = q := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_12 : reg n6 a2 = w48 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w5_48]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x18, 0x4)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m6]; exact w5_8
  have w6_c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m6]; exact w5_c
  have w6_10 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m6]; exact w5_10
  have w6_14 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m6]; exact w5_14
  have w6_18 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := by rw [m6]; exact w5_18
  have w6_1c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m6]; exact w5_1c
  have w6_20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m6]; exact w5_20
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
  have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m6]; exact w5_428
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
  have q6_320 : ∀ j, j < 31 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_320 j hj
  clear q5_320 w5_aa4 w5_aa0 w5_a3c w5_a38 w5_a34 w5_a30 w5_a2c w5_a28 w5_a24 w5_a20 w5_428 w5_130 w5_12c w5_128 w5_124 w5_120 w5_11c w5_118 w5_114 w5_110 w5_10c w5_108 w5_104 w5_100 w5_fc w5_f8 w5_f4 w5_f0 w5_ec w5_e8 w5_e4 w5_e0 w5_dc w5_d8 w5_d4 w5_d0 w5_cc w5_c8 w5_c4 w5_c0 w5_bc w5_b8 w5_b4 w5_b0 w5_ac w5_a8 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 w5_20 w5_1c w5_18 w5_14 w5_10 w5_c w5_8 g5_11 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_13 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x2D26
  obtain ⟨n7, c7, u7⟩ := s6.block svCs12d26 E6.self svCs12d26_end
    ⟨trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x2D2A (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svCs12d26 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_9 : reg n7 (9 : Fin 32) = c := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 0x3FCC4850 := by
    rw [rb7, runBlock_reg _ _ _ a0 s6.zero (by decide), g6_10]
  have g7_11 : reg n7 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb7, runBlock_reg _ _ _ a1 s6.zero (by decide), g6_11]
  have g7_12 : reg n7 a2 = w48 := by
    rw [rb7, runBlock_reg _ _ _ a2 s6.zero (by decide), g6_12]
  have g7_13 : reg n7 a3 = kp := by
    rw [rb7, runBlock_reg _ _ _ a3 s6.zero (by decide), g6_13]
  have g7_18 : reg n7 (18 : Fin 32) = out := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = rl := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = rp := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = dg := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = q := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_14 : reg n7 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svCs12d26, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_9, g6_10, g6_11, g6_12, g6_13, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x18, 0x4)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m7]; exact w6_8
  have w7_c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m7]; exact w6_c
  have w7_10 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m7]; exact w6_10
  have w7_14 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m7]; exact w6_14
  have w7_18 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := by rw [m7]; exact w6_18
  have w7_1c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m7]; exact w6_1c
  have w7_20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m7]; exact w6_20
  have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m7]; exact w6_24
  have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m7]; exact w6_28
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m7]; exact w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m7]; exact w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m7]; exact w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m7]; exact w6_38
  have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m7]; exact w6_3c
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m7]; exact w6_40
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m7]; exact w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m7]; exact w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m7]; exact w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m7]; exact w6_54
  have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m7]; exact w6_58
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m7]; exact w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m7]; exact w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m7]; exact w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m7]; exact w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m7]; exact w6_70
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m7]; exact w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m7]; exact w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m7]; exact w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m7]; exact w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m7]; exact w6_8c
  have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m7]; exact w6_90
  have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m7]; exact w6_94
  have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m7]; exact w6_98
  have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m7]; exact w6_9c
  have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m7]; exact w6_a0
  have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m7]; exact w6_a4
  have w7_a8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m7]; exact w6_a8
  have w7_ac : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m7]; exact w6_ac
  have w7_b0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m7]; exact w6_b0
  have w7_b4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m7]; exact w6_b4
  have w7_b8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m7]; exact w6_b8
  have w7_bc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m7]; exact w6_bc
  have w7_c0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m7]; exact w6_c0
  have w7_c4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m7]; exact w6_c4
  have w7_c8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m7]; exact w6_c8
  have w7_cc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m7]; exact w6_cc
  have w7_d0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m7]; exact w6_d0
  have w7_d4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m7]; exact w6_d4
  have w7_d8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m7]; exact w6_d8
  have w7_dc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m7]; exact w6_dc
  have w7_e0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m7]; exact w6_e0
  have w7_e4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m7]; exact w6_e4
  have w7_e8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m7]; exact w6_e8
  have w7_ec : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m7]; exact w6_ec
  have w7_f0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m7]; exact w6_f0
  have w7_f4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m7]; exact w6_f4
  have w7_f8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m7]; exact w6_f8
  have w7_fc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m7]; exact w6_fc
  have w7_100 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m7]; exact w6_100
  have w7_104 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m7]; exact w6_104
  have w7_108 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m7]; exact w6_108
  have w7_10c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m7]; exact w6_10c
  have w7_110 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m7]; exact w6_110
  have w7_114 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m7]; exact w6_114
  have w7_118 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m7]; exact w6_118
  have w7_11c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m7]; exact w6_11c
  have w7_120 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m7]; exact w6_120
  have w7_124 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m7]; exact w6_124
  have w7_128 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m7]; exact w6_128
  have w7_12c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m7]; exact w6_12c
  have w7_130 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m7]; exact w6_130
  have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m7]; exact w6_428
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m7]; exact w6_a20
  have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m7]; exact w6_a24
  have w7_a28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m7]; exact w6_a28
  have w7_a2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m7]; exact w6_a2c
  have w7_a30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m7]; exact w6_a30
  have w7_a34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m7]; exact w6_a34
  have w7_a38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m7]; exact w6_a38
  have w7_a3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m7]; exact w6_a3c
  have w7_aa0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m7]; exact w6_aa0
  have w7_aa4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m7]; exact w6_aa4
  have q7_320 : ∀ j, j < 31 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_320 j hj
  clear q6_320 w6_aa4 w6_aa0 w6_a3c w6_a38 w6_a34 w6_a30 w6_a2c w6_a28 w6_a24 w6_a20 w6_428 w6_130 w6_12c w6_128 w6_124 w6_120 w6_11c w6_118 w6_114 w6_110 w6_10c w6_108 w6_104 w6_100 w6_fc w6_f8 w6_f4 w6_f0 w6_ec w6_e8 w6_e4 w6_e0 w6_dc w6_d8 w6_d4 w6_d0 w6_cc w6_c8 w6_c4 w6_c0 w6_bc w6_b8 w6_b4 w6_b0 w6_ac w6_a8 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 w6_20 w6_1c w6_18 w6_14 w6_10 w6_c w6_8 g6_12 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_13 g6_11 g6_10 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x2D2A: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_2d2a (off' := 0x2D2C) (c := 0x420)
    (by decide) (by rw [g7_14]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = c := by rw [rg8 (9 : Fin 32), g7_9]
  have g8_10 : reg n8 a0 = BitVec.ofNat 32 0x3FCC4850 := by rw [rg8 a0, g7_10]
  have g8_11 : reg n8 a1 = BitVec.ofNat 32 0x1 := by rw [rg8 a1, g7_11]
  have g8_12 : reg n8 a2 = w48 := by rw [rg8 a2, g7_12]
  have g8_13 : reg n8 a3 = kp := by rw [rg8 a3, g7_13]
  have g8_14 : reg n8 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg8 a4, g7_14]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = rl := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = rp := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = dg := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = q := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg8 (27 : Fin 32), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x18, 0x4), (0x420, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K8.w32 (by decide) (by decide)).trans w7_8
  have w8_c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K8.w32 (by decide) (by decide)).trans w7_c
  have w8_10 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K8.w32 (by decide) (by decide)).trans w7_10
  have w8_14 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K8.w32 (by decide) (by decide)).trans w7_14
  have w8_18 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K8.w32 (by decide) (by decide)).trans w7_18
  have w8_1c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K8.w32 (by decide) (by decide)).trans w7_1c
  have w8_20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K8.w32 (by decide) (by decide)).trans w7_20
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
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K8.w32 (by decide) (by decide)).trans w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K8.w32 (by decide) (by decide)).trans w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K8.w32 (by decide) (by decide)).trans w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K8.w32 (by decide) (by decide)).trans w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K8.w32 (by decide) (by decide)).trans w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K8.w32 (by decide) (by decide)).trans w7_8c
  have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K8.w32 (by decide) (by decide)).trans w7_90
  have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K8.w32 (by decide) (by decide)).trans w7_94
  have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K8.w32 (by decide) (by decide)).trans w7_98
  have w8_9c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K8.w32 (by decide) (by decide)).trans w7_9c
  have w8_a0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K8.w32 (by decide) (by decide)).trans w7_a0
  have w8_a4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K8.w32 (by decide) (by decide)).trans w7_a4
  have w8_a8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K8.w32 (by decide) (by decide)).trans w7_a8
  have w8_ac : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K8.w32 (by decide) (by decide)).trans w7_ac
  have w8_b0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K8.w32 (by decide) (by decide)).trans w7_b0
  have w8_b4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K8.w32 (by decide) (by decide)).trans w7_b4
  have w8_b8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K8.w32 (by decide) (by decide)).trans w7_b8
  have w8_bc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K8.w32 (by decide) (by decide)).trans w7_bc
  have w8_c0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K8.w32 (by decide) (by decide)).trans w7_c0
  have w8_c4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K8.w32 (by decide) (by decide)).trans w7_c4
  have w8_c8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K8.w32 (by decide) (by decide)).trans w7_c8
  have w8_cc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K8.w32 (by decide) (by decide)).trans w7_cc
  have w8_d0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K8.w32 (by decide) (by decide)).trans w7_d0
  have w8_d4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K8.w32 (by decide) (by decide)).trans w7_d4
  have w8_d8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K8.w32 (by decide) (by decide)).trans w7_d8
  have w8_dc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K8.w32 (by decide) (by decide)).trans w7_dc
  have w8_e0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K8.w32 (by decide) (by decide)).trans w7_e0
  have w8_e4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K8.w32 (by decide) (by decide)).trans w7_e4
  have w8_e8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K8.w32 (by decide) (by decide)).trans w7_e8
  have w8_ec : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K8.w32 (by decide) (by decide)).trans w7_ec
  have w8_f0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K8.w32 (by decide) (by decide)).trans w7_f0
  have w8_f4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K8.w32 (by decide) (by decide)).trans w7_f4
  have w8_f8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K8.w32 (by decide) (by decide)).trans w7_f8
  have w8_fc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K8.w32 (by decide) (by decide)).trans w7_fc
  have w8_100 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K8.w32 (by decide) (by decide)).trans w7_100
  have w8_104 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K8.w32 (by decide) (by decide)).trans w7_104
  have w8_108 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K8.w32 (by decide) (by decide)).trans w7_108
  have w8_10c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K8.w32 (by decide) (by decide)).trans w7_10c
  have w8_110 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K8.w32 (by decide) (by decide)).trans w7_110
  have w8_114 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K8.w32 (by decide) (by decide)).trans w7_114
  have w8_118 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K8.w32 (by decide) (by decide)).trans w7_118
  have w8_11c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K8.w32 (by decide) (by decide)).trans w7_11c
  have w8_120 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K8.w32 (by decide) (by decide)).trans w7_120
  have w8_124 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K8.w32 (by decide) (by decide)).trans w7_124
  have w8_128 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K8.w32 (by decide) (by decide)).trans w7_128
  have w8_12c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K8.w32 (by decide) (by decide)).trans w7_12c
  have w8_130 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K8.w32 (by decide) (by decide)).trans w7_130
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := (K8.w32 (by decide) (by decide)).trans w7_428
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K8.w32 (by decide) (by decide)).trans w7_a20
  have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K8.w32 (by decide) (by decide)).trans w7_a24
  have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K8.w32 (by decide) (by decide)).trans w7_a28
  have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K8.w32 (by decide) (by decide)).trans w7_a2c
  have w8_a30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K8.w32 (by decide) (by decide)).trans w7_a30
  have w8_a34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K8.w32 (by decide) (by decide)).trans w7_a34
  have w8_a38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K8.w32 (by decide) (by decide)).trans w7_a38
  have w8_a3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K8.w32 (by decide) (by decide)).trans w7_a3c
  have w8_aa0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K8.w32 (by decide) (by decide)).trans w7_aa0
  have w8_aa4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K8.w32 (by decide) (by decide)).trans w7_aa4
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [W8, g7_12]
  have q8_320 : ∀ j, j < 31 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K8.range (by decide) (by decide) j hj).trans (q7_320 j hj)
  clear q7_320 w7_aa4 w7_aa0 w7_a3c w7_a38 w7_a34 w7_a30 w7_a2c w7_a28 w7_a24 w7_a20 w7_428 w7_130 w7_12c w7_128 w7_124 w7_120 w7_11c w7_118 w7_114 w7_110 w7_10c w7_108 w7_104 w7_100 w7_fc w7_f8 w7_f4 w7_f0 w7_ec w7_e8 w7_e4 w7_e0 w7_dc w7_d8 w7_d4 w7_d0 w7_cc w7_c8 w7_c4 w7_c0 w7_bc w7_b8 w7_b4 w7_b0 w7_ac w7_a8 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 w7_20 w7_1c w7_18 w7_14 w7_10 w7_c w7_8 g7_14 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_13 g7_12 g7_11 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x2D2C: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_2d2c (off' := 0x2D2E) (by decide)
    (by rw [g8_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x2D2E (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_9 : reg n9 (9 : Fin 32) = c := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 0x3FCC4850 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_10]
  have g9_11 : reg n9 a1 = BitVec.ofNat 32 0x1 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_11]
  have g9_13 : reg n9 a3 = kp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_13]
  have g9_14 : reg n9 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_14]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = rl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = rp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = dg := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = q := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_12 : reg n9 a2 = w44 := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w8_44]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x18, 0x4), (0x420, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m9]; exact w8_8
  have w9_c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m9]; exact w8_c
  have w9_10 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m9]; exact w8_10
  have w9_14 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m9]; exact w8_14
  have w9_18 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := by rw [m9]; exact w8_18
  have w9_1c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m9]; exact w8_1c
  have w9_20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m9]; exact w8_20
  have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m9]; exact w8_24
  have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m9]; exact w8_28
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m9]; exact w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m9]; exact w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m9]; exact w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m9]; exact w8_38
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m9]; exact w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m9]; exact w8_40
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m9]; exact w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m9]; exact w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m9]; exact w8_54
  have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m9]; exact w8_58
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m9]; exact w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m9]; exact w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m9]; exact w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m9]; exact w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m9]; exact w8_70
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m9]; exact w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m9]; exact w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m9]; exact w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m9]; exact w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m9]; exact w8_8c
  have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m9]; exact w8_90
  have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m9]; exact w8_94
  have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m9]; exact w8_98
  have w9_9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m9]; exact w8_9c
  have w9_a0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m9]; exact w8_a0
  have w9_a4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m9]; exact w8_a4
  have w9_a8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m9]; exact w8_a8
  have w9_ac : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m9]; exact w8_ac
  have w9_b0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m9]; exact w8_b0
  have w9_b4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m9]; exact w8_b4
  have w9_b8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m9]; exact w8_b8
  have w9_bc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m9]; exact w8_bc
  have w9_c0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m9]; exact w8_c0
  have w9_c4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m9]; exact w8_c4
  have w9_c8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m9]; exact w8_c8
  have w9_cc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m9]; exact w8_cc
  have w9_d0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m9]; exact w8_d0
  have w9_d4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m9]; exact w8_d4
  have w9_d8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m9]; exact w8_d8
  have w9_dc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m9]; exact w8_dc
  have w9_e0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m9]; exact w8_e0
  have w9_e4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m9]; exact w8_e4
  have w9_e8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m9]; exact w8_e8
  have w9_ec : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m9]; exact w8_ec
  have w9_f0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m9]; exact w8_f0
  have w9_f4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m9]; exact w8_f4
  have w9_f8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m9]; exact w8_f8
  have w9_fc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m9]; exact w8_fc
  have w9_100 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m9]; exact w8_100
  have w9_104 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m9]; exact w8_104
  have w9_108 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m9]; exact w8_108
  have w9_10c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m9]; exact w8_10c
  have w9_110 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m9]; exact w8_110
  have w9_114 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m9]; exact w8_114
  have w9_118 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m9]; exact w8_118
  have w9_11c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m9]; exact w8_11c
  have w9_120 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m9]; exact w8_120
  have w9_124 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m9]; exact w8_124
  have w9_128 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m9]; exact w8_128
  have w9_12c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m9]; exact w8_12c
  have w9_130 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m9]; exact w8_130
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [m9]; exact w8_420
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := by rw [m9]; exact w8_428
  have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m9]; exact w8_a20
  have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m9]; exact w8_a24
  have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m9]; exact w8_a28
  have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m9]; exact w8_a2c
  have w9_a30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m9]; exact w8_a30
  have w9_a34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m9]; exact w8_a34
  have w9_a38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m9]; exact w8_a38
  have w9_a3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m9]; exact w8_a3c
  have w9_aa0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m9]; exact w8_aa0
  have w9_aa4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m9]; exact w8_aa4
  have q9_320 : ∀ j, j < 31 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m9]; exact q8_320 j hj
  clear q8_320 w8_420 w8_aa4 w8_aa0 w8_a3c w8_a38 w8_a34 w8_a30 w8_a2c w8_a28 w8_a24 w8_a20 w8_428 w8_130 w8_12c w8_128 w8_124 w8_120 w8_11c w8_118 w8_114 w8_110 w8_10c w8_108 w8_104 w8_100 w8_fc w8_f8 w8_f4 w8_f0 w8_ec w8_e8 w8_e4 w8_e0 w8_dc w8_d8 w8_d4 w8_d0 w8_cc w8_c8 w8_c4 w8_c0 w8_bc w8_b8 w8_b4 w8_b0 w8_ac w8_a8 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_3c w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 w8_20 w8_1c w8_18 w8_14 w8_10 w8_c w8_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_14 g8_13 g8_12 g8_11 g8_10 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0x2D2E: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_2d2e (off' := 0x2D30) (c := 0x424)
    (by decide) (by rw [g9_14]; sv_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_9 : reg n10 (9 : Fin 32) = c := by rw [rg10 (9 : Fin 32), g9_9]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 0x3FCC4850 := by rw [rg10 a0, g9_10]
  have g10_11 : reg n10 a1 = BitVec.ofNat 32 0x1 := by rw [rg10 a1, g9_11]
  have g10_12 : reg n10 a2 = w44 := by rw [rg10 a2, g9_12]
  have g10_13 : reg n10 a3 = kp := by rw [rg10 a3, g9_13]
  have g10_14 : reg n10 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg10 a4, g9_14]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rg10 (21 : Fin 32), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = rl := by rw [rg10 (22 : Fin 32), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = rp := by rw [rg10 (23 : Fin 32), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = dg := by rw [rg10 (24 : Fin 32), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = q := by rw [rg10 (25 : Fin 32), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rg10 (26 : Fin 32), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg10 (27 : Fin 32), g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K10.w32 (by decide) (by decide)).trans w9_8
  have w10_c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K10.w32 (by decide) (by decide)).trans w9_c
  have w10_10 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K10.w32 (by decide) (by decide)).trans w9_10
  have w10_14 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K10.w32 (by decide) (by decide)).trans w9_14
  have w10_18 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K10.w32 (by decide) (by decide)).trans w9_18
  have w10_1c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K10.w32 (by decide) (by decide)).trans w9_1c
  have w10_20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K10.w32 (by decide) (by decide)).trans w9_20
  have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K10.w32 (by decide) (by decide)).trans w9_24
  have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K10.w32 (by decide) (by decide)).trans w9_28
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K10.w32 (by decide) (by decide)).trans w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K10.w32 (by decide) (by decide)).trans w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K10.w32 (by decide) (by decide)).trans w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K10.w32 (by decide) (by decide)).trans w9_38
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K10.w32 (by decide) (by decide)).trans w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K10.w32 (by decide) (by decide)).trans w9_40
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K10.w32 (by decide) (by decide)).trans w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K10.w32 (by decide) (by decide)).trans w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K10.w32 (by decide) (by decide)).trans w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K10.w32 (by decide) (by decide)).trans w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K10.w32 (by decide) (by decide)).trans w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K10.w32 (by decide) (by decide)).trans w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K10.w32 (by decide) (by decide)).trans w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K10.w32 (by decide) (by decide)).trans w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K10.w32 (by decide) (by decide)).trans w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K10.w32 (by decide) (by decide)).trans w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K10.w32 (by decide) (by decide)).trans w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K10.w32 (by decide) (by decide)).trans w9_70
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K10.w32 (by decide) (by decide)).trans w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K10.w32 (by decide) (by decide)).trans w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K10.w32 (by decide) (by decide)).trans w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K10.w32 (by decide) (by decide)).trans w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K10.w32 (by decide) (by decide)).trans w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K10.w32 (by decide) (by decide)).trans w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K10.w32 (by decide) (by decide)).trans w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K10.w32 (by decide) (by decide)).trans w9_94
  have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K10.w32 (by decide) (by decide)).trans w9_98
  have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K10.w32 (by decide) (by decide)).trans w9_9c
  have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K10.w32 (by decide) (by decide)).trans w9_a0
  have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K10.w32 (by decide) (by decide)).trans w9_a4
  have w10_a8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K10.w32 (by decide) (by decide)).trans w9_a8
  have w10_ac : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K10.w32 (by decide) (by decide)).trans w9_ac
  have w10_b0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K10.w32 (by decide) (by decide)).trans w9_b0
  have w10_b4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K10.w32 (by decide) (by decide)).trans w9_b4
  have w10_b8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K10.w32 (by decide) (by decide)).trans w9_b8
  have w10_bc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K10.w32 (by decide) (by decide)).trans w9_bc
  have w10_c0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K10.w32 (by decide) (by decide)).trans w9_c0
  have w10_c4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K10.w32 (by decide) (by decide)).trans w9_c4
  have w10_c8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K10.w32 (by decide) (by decide)).trans w9_c8
  have w10_cc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K10.w32 (by decide) (by decide)).trans w9_cc
  have w10_d0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K10.w32 (by decide) (by decide)).trans w9_d0
  have w10_d4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K10.w32 (by decide) (by decide)).trans w9_d4
  have w10_d8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K10.w32 (by decide) (by decide)).trans w9_d8
  have w10_dc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K10.w32 (by decide) (by decide)).trans w9_dc
  have w10_e0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K10.w32 (by decide) (by decide)).trans w9_e0
  have w10_e4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K10.w32 (by decide) (by decide)).trans w9_e4
  have w10_e8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K10.w32 (by decide) (by decide)).trans w9_e8
  have w10_ec : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K10.w32 (by decide) (by decide)).trans w9_ec
  have w10_f0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K10.w32 (by decide) (by decide)).trans w9_f0
  have w10_f4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K10.w32 (by decide) (by decide)).trans w9_f4
  have w10_f8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K10.w32 (by decide) (by decide)).trans w9_f8
  have w10_fc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K10.w32 (by decide) (by decide)).trans w9_fc
  have w10_100 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K10.w32 (by decide) (by decide)).trans w9_100
  have w10_104 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K10.w32 (by decide) (by decide)).trans w9_104
  have w10_108 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K10.w32 (by decide) (by decide)).trans w9_108
  have w10_10c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K10.w32 (by decide) (by decide)).trans w9_10c
  have w10_110 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K10.w32 (by decide) (by decide)).trans w9_110
  have w10_114 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K10.w32 (by decide) (by decide)).trans w9_114
  have w10_118 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K10.w32 (by decide) (by decide)).trans w9_118
  have w10_11c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K10.w32 (by decide) (by decide)).trans w9_11c
  have w10_120 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K10.w32 (by decide) (by decide)).trans w9_120
  have w10_124 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K10.w32 (by decide) (by decide)).trans w9_124
  have w10_128 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K10.w32 (by decide) (by decide)).trans w9_128
  have w10_12c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K10.w32 (by decide) (by decide)).trans w9_12c
  have w10_130 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K10.w32 (by decide) (by decide)).trans w9_130
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K10.w32 (by decide) (by decide)).trans w9_420
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp := (K10.w32 (by decide) (by decide)).trans w9_428
  have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K10.w32 (by decide) (by decide)).trans w9_a20
  have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K10.w32 (by decide) (by decide)).trans w9_a24
  have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K10.w32 (by decide) (by decide)).trans w9_a28
  have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K10.w32 (by decide) (by decide)).trans w9_a2c
  have w10_a30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K10.w32 (by decide) (by decide)).trans w9_a30
  have w10_a34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K10.w32 (by decide) (by decide)).trans w9_a34
  have w10_a38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K10.w32 (by decide) (by decide)).trans w9_a38
  have w10_a3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K10.w32 (by decide) (by decide)).trans w9_a3c
  have w10_aa0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K10.w32 (by decide) (by decide)).trans w9_aa0
  have w10_aa4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K10.w32 (by decide) (by decide)).trans w9_aa4
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := by rw [W10, g9_12]
  have q10_320 : ∀ j, j < 31 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_320 j hj)
  clear q9_320 w9_aa4 w9_aa0 w9_a3c w9_a38 w9_a34 w9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_428 w9_420 w9_130 w9_12c w9_128 w9_124 w9_120 w9_11c w9_118 w9_114 w9_110 w9_10c w9_108 w9_104 w9_100 w9_fc w9_f8 w9_f4 w9_f0 w9_ec w9_e8 w9_e4 w9_e0 w9_dc w9_d8 w9_d4 w9_d0 w9_cc w9_c8 w9_c4 w9_c0 w9_bc w9_b8 w9_b4 w9_b0 w9_ac w9_a8 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_3c w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 w9_20 w9_1c w9_18 w9_14 w9_10 w9_c w9_8 g9_12 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_14 g9_13 g9_11 g9_10 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x2D30: sw
  obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := sv_sw F E10 s10 sv_at_2d30 (off' := 0x2D32) (c := 0x428)
    (by decide) (by rw [g10_14]; sv_addr) (by decide) (by decide)
  have t11 : Steps n0 n11 := t10.trans d11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
  have g11_9 : reg n11 (9 : Fin 32) = c := by rw [rg11 (9 : Fin 32), g10_9]
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x3FCC4850 := by rw [rg11 a0, g10_10]
  have g11_11 : reg n11 a1 = BitVec.ofNat 32 0x1 := by rw [rg11 a1, g10_11]
  have g11_12 : reg n11 a2 = w44 := by rw [rg11 a2, g10_12]
  have g11_13 : reg n11 a3 = kp := by rw [rg11 a3, g10_13]
  have g11_14 : reg n11 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg11 a4, g10_14]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rg11 (18 : Fin 32), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rg11 (19 : Fin 32), g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [rg11 (21 : Fin 32), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = rl := by rw [rg11 (22 : Fin 32), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = rp := by rw [rg11 (23 : Fin 32), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = dg := by rw [rg11 (24 : Fin 32), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = q := by rw [rg11 (25 : Fin 32), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [rg11 (26 : Fin 32), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg11 (27 : Fin 32), g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K11.w32 (by decide) (by decide)).trans w10_8
  have w11_c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K11.w32 (by decide) (by decide)).trans w10_c
  have w11_10 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K11.w32 (by decide) (by decide)).trans w10_10
  have w11_14 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K11.w32 (by decide) (by decide)).trans w10_14
  have w11_18 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K11.w32 (by decide) (by decide)).trans w10_18
  have w11_1c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K11.w32 (by decide) (by decide)).trans w10_1c
  have w11_20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K11.w32 (by decide) (by decide)).trans w10_20
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
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K11.w32 (by decide) (by decide)).trans w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K11.w32 (by decide) (by decide)).trans w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K11.w32 (by decide) (by decide)).trans w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K11.w32 (by decide) (by decide)).trans w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K11.w32 (by decide) (by decide)).trans w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K11.w32 (by decide) (by decide)).trans w10_8c
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K11.w32 (by decide) (by decide)).trans w10_90
  have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K11.w32 (by decide) (by decide)).trans w10_94
  have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K11.w32 (by decide) (by decide)).trans w10_98
  have w11_9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K11.w32 (by decide) (by decide)).trans w10_9c
  have w11_a0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K11.w32 (by decide) (by decide)).trans w10_a0
  have w11_a4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K11.w32 (by decide) (by decide)).trans w10_a4
  have w11_a8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K11.w32 (by decide) (by decide)).trans w10_a8
  have w11_ac : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K11.w32 (by decide) (by decide)).trans w10_ac
  have w11_b0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K11.w32 (by decide) (by decide)).trans w10_b0
  have w11_b4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K11.w32 (by decide) (by decide)).trans w10_b4
  have w11_b8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K11.w32 (by decide) (by decide)).trans w10_b8
  have w11_bc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K11.w32 (by decide) (by decide)).trans w10_bc
  have w11_c0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K11.w32 (by decide) (by decide)).trans w10_c0
  have w11_c4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K11.w32 (by decide) (by decide)).trans w10_c4
  have w11_c8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K11.w32 (by decide) (by decide)).trans w10_c8
  have w11_cc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K11.w32 (by decide) (by decide)).trans w10_cc
  have w11_d0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K11.w32 (by decide) (by decide)).trans w10_d0
  have w11_d4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K11.w32 (by decide) (by decide)).trans w10_d4
  have w11_d8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K11.w32 (by decide) (by decide)).trans w10_d8
  have w11_dc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K11.w32 (by decide) (by decide)).trans w10_dc
  have w11_e0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K11.w32 (by decide) (by decide)).trans w10_e0
  have w11_e4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K11.w32 (by decide) (by decide)).trans w10_e4
  have w11_e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K11.w32 (by decide) (by decide)).trans w10_e8
  have w11_ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K11.w32 (by decide) (by decide)).trans w10_ec
  have w11_f0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K11.w32 (by decide) (by decide)).trans w10_f0
  have w11_f4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K11.w32 (by decide) (by decide)).trans w10_f4
  have w11_f8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K11.w32 (by decide) (by decide)).trans w10_f8
  have w11_fc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K11.w32 (by decide) (by decide)).trans w10_fc
  have w11_100 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K11.w32 (by decide) (by decide)).trans w10_100
  have w11_104 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K11.w32 (by decide) (by decide)).trans w10_104
  have w11_108 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K11.w32 (by decide) (by decide)).trans w10_108
  have w11_10c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K11.w32 (by decide) (by decide)).trans w10_10c
  have w11_110 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K11.w32 (by decide) (by decide)).trans w10_110
  have w11_114 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K11.w32 (by decide) (by decide)).trans w10_114
  have w11_118 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K11.w32 (by decide) (by decide)).trans w10_118
  have w11_11c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K11.w32 (by decide) (by decide)).trans w10_11c
  have w11_120 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K11.w32 (by decide) (by decide)).trans w10_120
  have w11_124 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K11.w32 (by decide) (by decide)).trans w10_124
  have w11_128 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K11.w32 (by decide) (by decide)).trans w10_128
  have w11_12c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K11.w32 (by decide) (by decide)).trans w10_12c
  have w11_130 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K11.w32 (by decide) (by decide)).trans w10_130
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K11.w32 (by decide) (by decide)).trans w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K11.w32 (by decide) (by decide)).trans w10_424
  have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K11.w32 (by decide) (by decide)).trans w10_a20
  have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K11.w32 (by decide) (by decide)).trans w10_a24
  have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K11.w32 (by decide) (by decide)).trans w10_a28
  have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K11.w32 (by decide) (by decide)).trans w10_a2c
  have w11_a30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K11.w32 (by decide) (by decide)).trans w10_a30
  have w11_a34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K11.w32 (by decide) (by decide)).trans w10_a34
  have w11_a38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K11.w32 (by decide) (by decide)).trans w10_a38
  have w11_a3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K11.w32 (by decide) (by decide)).trans w10_a3c
  have w11_aa0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K11.w32 (by decide) (by decide)).trans w10_aa0
  have w11_aa4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K11.w32 (by decide) (by decide)).trans w10_aa4
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := by rw [W11, g10_10]
  have q11_320 : ∀ j, j < 31 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_320 j hj)
  clear q10_320 w10_424 w10_aa4 w10_aa0 w10_a3c w10_a38 w10_a34 w10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_428 w10_420 w10_130 w10_12c w10_128 w10_124 w10_120 w10_11c w10_118 w10_114 w10_110 w10_10c w10_108 w10_104 w10_100 w10_fc w10_f8 w10_f4 w10_f0 w10_ec w10_e8 w10_e4 w10_e0 w10_dc w10_d8 w10_d4 w10_d0 w10_cc w10_c8 w10_c4 w10_c0 w10_bc w10_b8 w10_b4 w10_b0 w10_ac w10_a8 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 w10_20 w10_1c w10_18 w10_14 w10_10 w10_c w10_8 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_14 g10_13 g10_12 g10_11 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0x2D32: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_2d32 (off' := 0x2D34) (c := 0x42C)
    (by decide) (by rw [g11_14]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_9 : reg n12 (9 : Fin 32) = c := by rw [rg12 (9 : Fin 32), g11_9]
  have g12_10 : reg n12 a0 = BitVec.ofNat 32 0x3FCC4850 := by rw [rg12 a0, g11_10]
  have g12_11 : reg n12 a1 = BitVec.ofNat 32 0x1 := by rw [rg12 a1, g11_11]
  have g12_12 : reg n12 a2 = w44 := by rw [rg12 a2, g11_12]
  have g12_13 : reg n12 a3 = kp := by rw [rg12 a3, g11_13]
  have g12_14 : reg n12 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg12 a4, g11_14]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = rl := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = rp := by rw [rg12 (23 : Fin 32), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = dg := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = q := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K12.w32 (by decide) (by decide)).trans w11_8
  have w12_c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K12.w32 (by decide) (by decide)).trans w11_c
  have w12_10 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K12.w32 (by decide) (by decide)).trans w11_10
  have w12_14 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K12.w32 (by decide) (by decide)).trans w11_14
  have w12_18 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K12.w32 (by decide) (by decide)).trans w11_18
  have w12_1c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K12.w32 (by decide) (by decide)).trans w11_1c
  have w12_20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K12.w32 (by decide) (by decide)).trans w11_20
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
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K12.w32 (by decide) (by decide)).trans w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K12.w32 (by decide) (by decide)).trans w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K12.w32 (by decide) (by decide)).trans w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K12.w32 (by decide) (by decide)).trans w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K12.w32 (by decide) (by decide)).trans w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K12.w32 (by decide) (by decide)).trans w11_8c
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K12.w32 (by decide) (by decide)).trans w11_90
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K12.w32 (by decide) (by decide)).trans w11_94
  have w12_98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K12.w32 (by decide) (by decide)).trans w11_98
  have w12_9c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K12.w32 (by decide) (by decide)).trans w11_9c
  have w12_a0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K12.w32 (by decide) (by decide)).trans w11_a0
  have w12_a4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K12.w32 (by decide) (by decide)).trans w11_a4
  have w12_a8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K12.w32 (by decide) (by decide)).trans w11_a8
  have w12_ac : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K12.w32 (by decide) (by decide)).trans w11_ac
  have w12_b0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K12.w32 (by decide) (by decide)).trans w11_b0
  have w12_b4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K12.w32 (by decide) (by decide)).trans w11_b4
  have w12_b8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K12.w32 (by decide) (by decide)).trans w11_b8
  have w12_bc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K12.w32 (by decide) (by decide)).trans w11_bc
  have w12_c0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K12.w32 (by decide) (by decide)).trans w11_c0
  have w12_c4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K12.w32 (by decide) (by decide)).trans w11_c4
  have w12_c8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K12.w32 (by decide) (by decide)).trans w11_c8
  have w12_cc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K12.w32 (by decide) (by decide)).trans w11_cc
  have w12_d0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K12.w32 (by decide) (by decide)).trans w11_d0
  have w12_d4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K12.w32 (by decide) (by decide)).trans w11_d4
  have w12_d8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K12.w32 (by decide) (by decide)).trans w11_d8
  have w12_dc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K12.w32 (by decide) (by decide)).trans w11_dc
  have w12_e0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K12.w32 (by decide) (by decide)).trans w11_e0
  have w12_e4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K12.w32 (by decide) (by decide)).trans w11_e4
  have w12_e8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K12.w32 (by decide) (by decide)).trans w11_e8
  have w12_ec : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K12.w32 (by decide) (by decide)).trans w11_ec
  have w12_f0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K12.w32 (by decide) (by decide)).trans w11_f0
  have w12_f4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K12.w32 (by decide) (by decide)).trans w11_f4
  have w12_f8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K12.w32 (by decide) (by decide)).trans w11_f8
  have w12_fc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K12.w32 (by decide) (by decide)).trans w11_fc
  have w12_100 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K12.w32 (by decide) (by decide)).trans w11_100
  have w12_104 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K12.w32 (by decide) (by decide)).trans w11_104
  have w12_108 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K12.w32 (by decide) (by decide)).trans w11_108
  have w12_10c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K12.w32 (by decide) (by decide)).trans w11_10c
  have w12_110 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K12.w32 (by decide) (by decide)).trans w11_110
  have w12_114 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K12.w32 (by decide) (by decide)).trans w11_114
  have w12_118 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K12.w32 (by decide) (by decide)).trans w11_118
  have w12_11c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K12.w32 (by decide) (by decide)).trans w11_11c
  have w12_120 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K12.w32 (by decide) (by decide)).trans w11_120
  have w12_124 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K12.w32 (by decide) (by decide)).trans w11_124
  have w12_128 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K12.w32 (by decide) (by decide)).trans w11_128
  have w12_12c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K12.w32 (by decide) (by decide)).trans w11_12c
  have w12_130 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K12.w32 (by decide) (by decide)).trans w11_130
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K12.w32 (by decide) (by decide)).trans w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K12.w32 (by decide) (by decide)).trans w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := (K12.w32 (by decide) (by decide)).trans w11_428
  have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K12.w32 (by decide) (by decide)).trans w11_a20
  have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K12.w32 (by decide) (by decide)).trans w11_a24
  have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K12.w32 (by decide) (by decide)).trans w11_a28
  have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K12.w32 (by decide) (by decide)).trans w11_a2c
  have w12_a30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K12.w32 (by decide) (by decide)).trans w11_a30
  have w12_a34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K12.w32 (by decide) (by decide)).trans w11_a34
  have w12_a38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K12.w32 (by decide) (by decide)).trans w11_a38
  have w12_a3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K12.w32 (by decide) (by decide)).trans w11_a3c
  have w12_aa0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K12.w32 (by decide) (by decide)).trans w11_aa0
  have w12_aa4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K12.w32 (by decide) (by decide)).trans w11_aa4
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := by rw [W12, g11_11]
  have q12_320 : ∀ j, j < 31 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K12.range (by decide) (by decide) j hj).trans (q11_320 j hj)
  clear q11_320 w11_428 w11_aa4 w11_aa0 w11_a3c w11_a38 w11_a34 w11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_424 w11_420 w11_130 w11_12c w11_128 w11_124 w11_120 w11_11c w11_118 w11_114 w11_110 w11_10c w11_108 w11_104 w11_100 w11_fc w11_f8 w11_f4 w11_f0 w11_ec w11_e8 w11_e4 w11_e0 w11_dc w11_d8 w11_d4 w11_d0 w11_cc w11_c8 w11_c4 w11_c0 w11_bc w11_b8 w11_b4 w11_b0 w11_ac w11_a8 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 w11_20 w11_1c w11_18 w11_14 w11_10 w11_c w11_8 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_14 g11_13 g11_12 g11_11 g11_10 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
  -- 0x2D34
  obtain ⟨n13, c13, u13⟩ := s12.block svCs12d34 E12.self svCs12d34_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x2D40 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svCs12d34 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_9 : reg n13 (9 : Fin 32) = c := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb13, runBlock_reg _ _ _ a1 s12.zero (by decide), g12_11]
  have g13_13 : reg n13 a3 = kp := by
    rw [rb13, runBlock_reg _ _ _ a3 s12.zero (by decide), g12_13]
  have g13_14 : reg n13 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb13, runBlock_reg _ _ _ a4 s12.zero (by decide), g12_14]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = rl := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = rp := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = dg := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = q := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 0x3FCC47D7 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svCs12d34, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_9, g12_10, g12_11, g12_12, g12_13, g12_14, g12_18, g12_19, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svCs12d34, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_9, g12_10, g12_11, g12_12, g12_13, g12_14, g12_18, g12_19, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m13]; exact w12_8
  have w13_c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m13]; exact w12_c
  have w13_10 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m13]; exact w12_10
  have w13_14 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m13]; exact w12_14
  have w13_18 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := by rw [m13]; exact w12_18
  have w13_1c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m13]; exact w12_1c
  have w13_20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m13]; exact w12_20
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
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m13]; exact w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m13]; exact w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m13]; exact w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m13]; exact w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m13]; exact w12_94
  have w13_98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m13]; exact w12_98
  have w13_9c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m13]; exact w12_9c
  have w13_a0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m13]; exact w12_a0
  have w13_a4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m13]; exact w12_a4
  have w13_a8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m13]; exact w12_a8
  have w13_ac : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m13]; exact w12_ac
  have w13_b0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m13]; exact w12_b0
  have w13_b4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m13]; exact w12_b4
  have w13_b8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m13]; exact w12_b8
  have w13_bc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m13]; exact w12_bc
  have w13_c0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m13]; exact w12_c0
  have w13_c4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m13]; exact w12_c4
  have w13_c8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m13]; exact w12_c8
  have w13_cc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m13]; exact w12_cc
  have w13_d0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m13]; exact w12_d0
  have w13_d4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m13]; exact w12_d4
  have w13_d8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m13]; exact w12_d8
  have w13_dc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m13]; exact w12_dc
  have w13_e0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m13]; exact w12_e0
  have w13_e4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m13]; exact w12_e4
  have w13_e8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m13]; exact w12_e8
  have w13_ec : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m13]; exact w12_ec
  have w13_f0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m13]; exact w12_f0
  have w13_f4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m13]; exact w12_f4
  have w13_f8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m13]; exact w12_f8
  have w13_fc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m13]; exact w12_fc
  have w13_100 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m13]; exact w12_100
  have w13_104 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m13]; exact w12_104
  have w13_108 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m13]; exact w12_108
  have w13_10c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m13]; exact w12_10c
  have w13_110 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m13]; exact w12_110
  have w13_114 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m13]; exact w12_114
  have w13_118 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m13]; exact w12_118
  have w13_11c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m13]; exact w12_11c
  have w13_120 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m13]; exact w12_120
  have w13_124 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m13]; exact w12_124
  have w13_128 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m13]; exact w12_128
  have w13_12c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m13]; exact w12_12c
  have w13_130 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m13]; exact w12_130
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [m13]; exact w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := by rw [m13]; exact w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := by rw [m13]; exact w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := by rw [m13]; exact w12_42c
  have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := by rw [m13]; exact w12_a20
  have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := by rw [m13]; exact w12_a24
  have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := by rw [m13]; exact w12_a28
  have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := by rw [m13]; exact w12_a2c
  have w13_a30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := by rw [m13]; exact w12_a30
  have w13_a34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := by rw [m13]; exact w12_a34
  have w13_a38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := by rw [m13]; exact w12_a38
  have w13_a3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := by rw [m13]; exact w12_a3c
  have w13_aa0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := by rw [m13]; exact w12_aa0
  have w13_aa4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := by rw [m13]; exact w12_aa4
  have q13_320 : ∀ j, j < 31 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_320 j hj
  clear q12_320 w12_42c w12_aa4 w12_aa0 w12_a3c w12_a38 w12_a34 w12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_428 w12_424 w12_420 w12_130 w12_12c w12_128 w12_124 w12_120 w12_11c w12_118 w12_114 w12_110 w12_10c w12_108 w12_104 w12_100 w12_fc w12_f8 w12_f4 w12_f0 w12_ec w12_e8 w12_e4 w12_e0 w12_dc w12_d8 w12_d4 w12_d0 w12_cc w12_c8 w12_c4 w12_c0 w12_bc w12_b8 w12_b4 w12_b0 w12_ac w12_a8 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_3c w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 w12_20 w12_1c w12_18 w12_14 w12_10 w12_c w12_8 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_14 g12_13 g12_12 g12_11 g12_10 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0x2D40: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_2d40 (off' := 0x2D42) (c := 0x430)
    (by decide) (by rw [g13_14]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_9 : reg n14 (9 : Fin 32) = c := by rw [rg14 (9 : Fin 32), g13_9]
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 0x3FCC47D7 := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 0x1 := by rw [rg14 a1, g13_11]
  have g14_12 : reg n14 a2 = BitVec.ofNat 32 0x20 := by rw [rg14 a2, g13_12]
  have g14_13 : reg n14 a3 = kp := by rw [rg14 a3, g13_13]
  have g14_14 : reg n14 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg14 a4, g13_14]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = rl := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = rp := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = dg := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = q := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K14.w32 (by decide) (by decide)).trans w13_8
  have w14_c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K14.w32 (by decide) (by decide)).trans w13_c
  have w14_10 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K14.w32 (by decide) (by decide)).trans w13_10
  have w14_14 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K14.w32 (by decide) (by decide)).trans w13_14
  have w14_18 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K14.w32 (by decide) (by decide)).trans w13_18
  have w14_1c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K14.w32 (by decide) (by decide)).trans w13_1c
  have w14_20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K14.w32 (by decide) (by decide)).trans w13_20
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
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K14.w32 (by decide) (by decide)).trans w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K14.w32 (by decide) (by decide)).trans w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K14.w32 (by decide) (by decide)).trans w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K14.w32 (by decide) (by decide)).trans w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K14.w32 (by decide) (by decide)).trans w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K14.w32 (by decide) (by decide)).trans w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K14.w32 (by decide) (by decide)).trans w13_94
  have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K14.w32 (by decide) (by decide)).trans w13_98
  have w14_9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K14.w32 (by decide) (by decide)).trans w13_9c
  have w14_a0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K14.w32 (by decide) (by decide)).trans w13_a0
  have w14_a4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K14.w32 (by decide) (by decide)).trans w13_a4
  have w14_a8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K14.w32 (by decide) (by decide)).trans w13_a8
  have w14_ac : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K14.w32 (by decide) (by decide)).trans w13_ac
  have w14_b0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K14.w32 (by decide) (by decide)).trans w13_b0
  have w14_b4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K14.w32 (by decide) (by decide)).trans w13_b4
  have w14_b8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K14.w32 (by decide) (by decide)).trans w13_b8
  have w14_bc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K14.w32 (by decide) (by decide)).trans w13_bc
  have w14_c0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K14.w32 (by decide) (by decide)).trans w13_c0
  have w14_c4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K14.w32 (by decide) (by decide)).trans w13_c4
  have w14_c8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K14.w32 (by decide) (by decide)).trans w13_c8
  have w14_cc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K14.w32 (by decide) (by decide)).trans w13_cc
  have w14_d0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K14.w32 (by decide) (by decide)).trans w13_d0
  have w14_d4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K14.w32 (by decide) (by decide)).trans w13_d4
  have w14_d8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K14.w32 (by decide) (by decide)).trans w13_d8
  have w14_dc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K14.w32 (by decide) (by decide)).trans w13_dc
  have w14_e0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K14.w32 (by decide) (by decide)).trans w13_e0
  have w14_e4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K14.w32 (by decide) (by decide)).trans w13_e4
  have w14_e8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K14.w32 (by decide) (by decide)).trans w13_e8
  have w14_ec : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K14.w32 (by decide) (by decide)).trans w13_ec
  have w14_f0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K14.w32 (by decide) (by decide)).trans w13_f0
  have w14_f4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K14.w32 (by decide) (by decide)).trans w13_f4
  have w14_f8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K14.w32 (by decide) (by decide)).trans w13_f8
  have w14_fc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K14.w32 (by decide) (by decide)).trans w13_fc
  have w14_100 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K14.w32 (by decide) (by decide)).trans w13_100
  have w14_104 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K14.w32 (by decide) (by decide)).trans w13_104
  have w14_108 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K14.w32 (by decide) (by decide)).trans w13_108
  have w14_10c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K14.w32 (by decide) (by decide)).trans w13_10c
  have w14_110 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K14.w32 (by decide) (by decide)).trans w13_110
  have w14_114 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K14.w32 (by decide) (by decide)).trans w13_114
  have w14_118 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K14.w32 (by decide) (by decide)).trans w13_118
  have w14_11c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K14.w32 (by decide) (by decide)).trans w13_11c
  have w14_120 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K14.w32 (by decide) (by decide)).trans w13_120
  have w14_124 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K14.w32 (by decide) (by decide)).trans w13_124
  have w14_128 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K14.w32 (by decide) (by decide)).trans w13_128
  have w14_12c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K14.w32 (by decide) (by decide)).trans w13_12c
  have w14_130 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K14.w32 (by decide) (by decide)).trans w13_130
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K14.w32 (by decide) (by decide)).trans w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K14.w32 (by decide) (by decide)).trans w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := (K14.w32 (by decide) (by decide)).trans w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K14.w32 (by decide) (by decide)).trans w13_42c
  have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K14.w32 (by decide) (by decide)).trans w13_a20
  have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K14.w32 (by decide) (by decide)).trans w13_a24
  have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K14.w32 (by decide) (by decide)).trans w13_a28
  have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K14.w32 (by decide) (by decide)).trans w13_a2c
  have w14_a30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K14.w32 (by decide) (by decide)).trans w13_a30
  have w14_a34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K14.w32 (by decide) (by decide)).trans w13_a34
  have w14_a38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K14.w32 (by decide) (by decide)).trans w13_a38
  have w14_a3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K14.w32 (by decide) (by decide)).trans w13_a3c
  have w14_aa0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K14.w32 (by decide) (by decide)).trans w13_aa0
  have w14_aa4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K14.w32 (by decide) (by decide)).trans w13_aa4
  have w14_430 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := by rw [W14, g13_10]
  have q14_320 : ∀ j, j < 31 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_320 j hj)
  clear q13_320 w13_aa4 w13_aa0 w13_a3c w13_a38 w13_a34 w13_a30 w13_a2c w13_a28 w13_a24 w13_a20 w13_42c w13_428 w13_424 w13_420 w13_130 w13_12c w13_128 w13_124 w13_120 w13_11c w13_118 w13_114 w13_110 w13_10c w13_108 w13_104 w13_100 w13_fc w13_f8 w13_f4 w13_f0 w13_ec w13_e8 w13_e4 w13_e0 w13_dc w13_d8 w13_d4 w13_d0 w13_cc w13_c8 w13_c4 w13_c0 w13_bc w13_b8 w13_b4 w13_b0 w13_ac w13_a8 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_3c w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 w13_20 w13_1c w13_18 w13_14 w13_10 w13_c w13_8 g13_12 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_14 g13_13 g13_11 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x2D42: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_2d42 (off' := 0x2D44) (c := 0x434)
    (by decide) (by rw [g14_14]; sv_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_9 : reg n15 (9 : Fin 32) = c := by rw [rg15 (9 : Fin 32), g14_9]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x3FCC47D7 := by rw [rg15 a0, g14_10]
  have g15_11 : reg n15 a1 = BitVec.ofNat 32 0x1 := by rw [rg15 a1, g14_11]
  have g15_12 : reg n15 a2 = BitVec.ofNat 32 0x20 := by rw [rg15 a2, g14_12]
  have g15_13 : reg n15 a3 = kp := by rw [rg15 a3, g14_13]
  have g15_14 : reg n15 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg15 a4, g14_14]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rg15 (21 : Fin 32), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = rl := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = rp := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = dg := by rw [rg15 (24 : Fin 32), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = q := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [rg15 (26 : Fin 32), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg15 (27 : Fin 32), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K15.w32 (by decide) (by decide)).trans w14_8
  have w15_c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K15.w32 (by decide) (by decide)).trans w14_c
  have w15_10 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K15.w32 (by decide) (by decide)).trans w14_10
  have w15_14 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K15.w32 (by decide) (by decide)).trans w14_14
  have w15_18 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K15.w32 (by decide) (by decide)).trans w14_18
  have w15_1c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K15.w32 (by decide) (by decide)).trans w14_1c
  have w15_20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K15.w32 (by decide) (by decide)).trans w14_20
  have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K15.w32 (by decide) (by decide)).trans w14_24
  have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K15.w32 (by decide) (by decide)).trans w14_28
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K15.w32 (by decide) (by decide)).trans w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K15.w32 (by decide) (by decide)).trans w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K15.w32 (by decide) (by decide)).trans w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K15.w32 (by decide) (by decide)).trans w14_38
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K15.w32 (by decide) (by decide)).trans w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K15.w32 (by decide) (by decide)).trans w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K15.w32 (by decide) (by decide)).trans w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K15.w32 (by decide) (by decide)).trans w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K15.w32 (by decide) (by decide)).trans w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K15.w32 (by decide) (by decide)).trans w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K15.w32 (by decide) (by decide)).trans w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K15.w32 (by decide) (by decide)).trans w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K15.w32 (by decide) (by decide)).trans w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K15.w32 (by decide) (by decide)).trans w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K15.w32 (by decide) (by decide)).trans w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K15.w32 (by decide) (by decide)).trans w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K15.w32 (by decide) (by decide)).trans w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K15.w32 (by decide) (by decide)).trans w14_70
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K15.w32 (by decide) (by decide)).trans w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K15.w32 (by decide) (by decide)).trans w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K15.w32 (by decide) (by decide)).trans w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K15.w32 (by decide) (by decide)).trans w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K15.w32 (by decide) (by decide)).trans w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K15.w32 (by decide) (by decide)).trans w14_8c
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K15.w32 (by decide) (by decide)).trans w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K15.w32 (by decide) (by decide)).trans w14_94
  have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K15.w32 (by decide) (by decide)).trans w14_98
  have w15_9c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K15.w32 (by decide) (by decide)).trans w14_9c
  have w15_a0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K15.w32 (by decide) (by decide)).trans w14_a0
  have w15_a4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K15.w32 (by decide) (by decide)).trans w14_a4
  have w15_a8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K15.w32 (by decide) (by decide)).trans w14_a8
  have w15_ac : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K15.w32 (by decide) (by decide)).trans w14_ac
  have w15_b0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K15.w32 (by decide) (by decide)).trans w14_b0
  have w15_b4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K15.w32 (by decide) (by decide)).trans w14_b4
  have w15_b8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K15.w32 (by decide) (by decide)).trans w14_b8
  have w15_bc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K15.w32 (by decide) (by decide)).trans w14_bc
  have w15_c0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K15.w32 (by decide) (by decide)).trans w14_c0
  have w15_c4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K15.w32 (by decide) (by decide)).trans w14_c4
  have w15_c8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K15.w32 (by decide) (by decide)).trans w14_c8
  have w15_cc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K15.w32 (by decide) (by decide)).trans w14_cc
  have w15_d0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K15.w32 (by decide) (by decide)).trans w14_d0
  have w15_d4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K15.w32 (by decide) (by decide)).trans w14_d4
  have w15_d8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K15.w32 (by decide) (by decide)).trans w14_d8
  have w15_dc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K15.w32 (by decide) (by decide)).trans w14_dc
  have w15_e0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K15.w32 (by decide) (by decide)).trans w14_e0
  have w15_e4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K15.w32 (by decide) (by decide)).trans w14_e4
  have w15_e8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K15.w32 (by decide) (by decide)).trans w14_e8
  have w15_ec : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K15.w32 (by decide) (by decide)).trans w14_ec
  have w15_f0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K15.w32 (by decide) (by decide)).trans w14_f0
  have w15_f4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K15.w32 (by decide) (by decide)).trans w14_f4
  have w15_f8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K15.w32 (by decide) (by decide)).trans w14_f8
  have w15_fc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K15.w32 (by decide) (by decide)).trans w14_fc
  have w15_100 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K15.w32 (by decide) (by decide)).trans w14_100
  have w15_104 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K15.w32 (by decide) (by decide)).trans w14_104
  have w15_108 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K15.w32 (by decide) (by decide)).trans w14_108
  have w15_10c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K15.w32 (by decide) (by decide)).trans w14_10c
  have w15_110 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K15.w32 (by decide) (by decide)).trans w14_110
  have w15_114 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K15.w32 (by decide) (by decide)).trans w14_114
  have w15_118 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K15.w32 (by decide) (by decide)).trans w14_118
  have w15_11c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K15.w32 (by decide) (by decide)).trans w14_11c
  have w15_120 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K15.w32 (by decide) (by decide)).trans w14_120
  have w15_124 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K15.w32 (by decide) (by decide)).trans w14_124
  have w15_128 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K15.w32 (by decide) (by decide)).trans w14_128
  have w15_12c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K15.w32 (by decide) (by decide)).trans w14_12c
  have w15_130 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K15.w32 (by decide) (by decide)).trans w14_130
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K15.w32 (by decide) (by decide)).trans w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K15.w32 (by decide) (by decide)).trans w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := (K15.w32 (by decide) (by decide)).trans w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K15.w32 (by decide) (by decide)).trans w14_42c
  have w15_430 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := (K15.w32 (by decide) (by decide)).trans w14_430
  have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K15.w32 (by decide) (by decide)).trans w14_a20
  have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K15.w32 (by decide) (by decide)).trans w14_a24
  have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K15.w32 (by decide) (by decide)).trans w14_a28
  have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K15.w32 (by decide) (by decide)).trans w14_a2c
  have w15_a30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K15.w32 (by decide) (by decide)).trans w14_a30
  have w15_a34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K15.w32 (by decide) (by decide)).trans w14_a34
  have w15_a38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K15.w32 (by decide) (by decide)).trans w14_a38
  have w15_a3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K15.w32 (by decide) (by decide)).trans w14_a3c
  have w15_aa0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K15.w32 (by decide) (by decide)).trans w14_aa0
  have w15_aa4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K15.w32 (by decide) (by decide)).trans w14_aa4
  have w15_434 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := by rw [W15, g14_11]
  have q15_320 : ∀ j, j < 31 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_320 j hj)
  clear q14_320 w14_430 w14_aa4 w14_aa0 w14_a3c w14_a38 w14_a34 w14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_42c w14_428 w14_424 w14_420 w14_130 w14_12c w14_128 w14_124 w14_120 w14_11c w14_118 w14_114 w14_110 w14_10c w14_108 w14_104 w14_100 w14_fc w14_f8 w14_f4 w14_f0 w14_ec w14_e8 w14_e4 w14_e0 w14_dc w14_d8 w14_d4 w14_d0 w14_cc w14_c8 w14_c4 w14_c0 w14_bc w14_b8 w14_b4 w14_b0 w14_ac w14_a8 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 w14_20 w14_1c w14_18 w14_14 w14_10 w14_c w14_8 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_14 g14_13 g14_12 g14_11 g14_10 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0x2D44: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_2d44 (off' := 0x2D46) (c := 0x34)
    (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_9 : reg n16 (9 : Fin 32) = c := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x3FCC47D7 := by rw [rg16 a0, g15_10]
  have g16_11 : reg n16 a1 = BitVec.ofNat 32 0x1 := by rw [rg16 a1, g15_11]
  have g16_12 : reg n16 a2 = BitVec.ofNat 32 0x20 := by rw [rg16 a2, g15_12]
  have g16_13 : reg n16 a3 = kp := by rw [rg16 a3, g15_13]
  have g16_14 : reg n16 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg16 a4, g15_14]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = rl := by rw [rg16 (22 : Fin 32), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = rp := by rw [rg16 (23 : Fin 32), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = dg := by rw [rg16 (24 : Fin 32), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = q := by rw [rg16 (25 : Fin 32), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K16.w32 (by decide) (by decide)).trans w15_8
  have w16_c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K16.w32 (by decide) (by decide)).trans w15_c
  have w16_10 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K16.w32 (by decide) (by decide)).trans w15_10
  have w16_14 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K16.w32 (by decide) (by decide)).trans w15_14
  have w16_18 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K16.w32 (by decide) (by decide)).trans w15_18
  have w16_1c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K16.w32 (by decide) (by decide)).trans w15_1c
  have w16_20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K16.w32 (by decide) (by decide)).trans w15_20
  have w16_24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K16.w32 (by decide) (by decide)).trans w15_24
  have w16_28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K16.w32 (by decide) (by decide)).trans w15_28
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K16.w32 (by decide) (by decide)).trans w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K16.w32 (by decide) (by decide)).trans w15_30
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
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K16.w32 (by decide) (by decide)).trans w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K16.w32 (by decide) (by decide)).trans w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K16.w32 (by decide) (by decide)).trans w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K16.w32 (by decide) (by decide)).trans w15_8c
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K16.w32 (by decide) (by decide)).trans w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K16.w32 (by decide) (by decide)).trans w15_94
  have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K16.w32 (by decide) (by decide)).trans w15_98
  have w16_9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K16.w32 (by decide) (by decide)).trans w15_9c
  have w16_a0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K16.w32 (by decide) (by decide)).trans w15_a0
  have w16_a4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K16.w32 (by decide) (by decide)).trans w15_a4
  have w16_a8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K16.w32 (by decide) (by decide)).trans w15_a8
  have w16_ac : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K16.w32 (by decide) (by decide)).trans w15_ac
  have w16_b0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K16.w32 (by decide) (by decide)).trans w15_b0
  have w16_b4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K16.w32 (by decide) (by decide)).trans w15_b4
  have w16_b8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K16.w32 (by decide) (by decide)).trans w15_b8
  have w16_bc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K16.w32 (by decide) (by decide)).trans w15_bc
  have w16_c0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K16.w32 (by decide) (by decide)).trans w15_c0
  have w16_c4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K16.w32 (by decide) (by decide)).trans w15_c4
  have w16_c8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K16.w32 (by decide) (by decide)).trans w15_c8
  have w16_cc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K16.w32 (by decide) (by decide)).trans w15_cc
  have w16_d0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K16.w32 (by decide) (by decide)).trans w15_d0
  have w16_d4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K16.w32 (by decide) (by decide)).trans w15_d4
  have w16_d8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K16.w32 (by decide) (by decide)).trans w15_d8
  have w16_dc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K16.w32 (by decide) (by decide)).trans w15_dc
  have w16_e0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K16.w32 (by decide) (by decide)).trans w15_e0
  have w16_e4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K16.w32 (by decide) (by decide)).trans w15_e4
  have w16_e8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K16.w32 (by decide) (by decide)).trans w15_e8
  have w16_ec : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K16.w32 (by decide) (by decide)).trans w15_ec
  have w16_f0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K16.w32 (by decide) (by decide)).trans w15_f0
  have w16_f4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K16.w32 (by decide) (by decide)).trans w15_f4
  have w16_f8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K16.w32 (by decide) (by decide)).trans w15_f8
  have w16_fc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K16.w32 (by decide) (by decide)).trans w15_fc
  have w16_100 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K16.w32 (by decide) (by decide)).trans w15_100
  have w16_104 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K16.w32 (by decide) (by decide)).trans w15_104
  have w16_108 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K16.w32 (by decide) (by decide)).trans w15_108
  have w16_10c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K16.w32 (by decide) (by decide)).trans w15_10c
  have w16_110 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K16.w32 (by decide) (by decide)).trans w15_110
  have w16_114 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K16.w32 (by decide) (by decide)).trans w15_114
  have w16_118 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K16.w32 (by decide) (by decide)).trans w15_118
  have w16_11c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K16.w32 (by decide) (by decide)).trans w15_11c
  have w16_120 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K16.w32 (by decide) (by decide)).trans w15_120
  have w16_124 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K16.w32 (by decide) (by decide)).trans w15_124
  have w16_128 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K16.w32 (by decide) (by decide)).trans w15_128
  have w16_12c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K16.w32 (by decide) (by decide)).trans w15_12c
  have w16_130 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K16.w32 (by decide) (by decide)).trans w15_130
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K16.w32 (by decide) (by decide)).trans w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K16.w32 (by decide) (by decide)).trans w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := (K16.w32 (by decide) (by decide)).trans w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K16.w32 (by decide) (by decide)).trans w15_42c
  have w16_430 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := (K16.w32 (by decide) (by decide)).trans w15_430
  have w16_434 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K16.w32 (by decide) (by decide)).trans w15_434
  have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K16.w32 (by decide) (by decide)).trans w15_a20
  have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K16.w32 (by decide) (by decide)).trans w15_a24
  have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K16.w32 (by decide) (by decide)).trans w15_a28
  have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K16.w32 (by decide) (by decide)).trans w15_a2c
  have w16_a30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K16.w32 (by decide) (by decide)).trans w15_a30
  have w16_a34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K16.w32 (by decide) (by decide)).trans w15_a34
  have w16_a38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K16.w32 (by decide) (by decide)).trans w15_a38
  have w16_a3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K16.w32 (by decide) (by decide)).trans w15_a3c
  have w16_aa0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K16.w32 (by decide) (by decide)).trans w15_aa0
  have w16_aa4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K16.w32 (by decide) (by decide)).trans w15_aa4
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [W16, g15_13]
  have q16_320 : ∀ j, j < 31 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_320 j hj)
  clear q15_320 w15_434 w15_aa4 w15_aa0 w15_a3c w15_a38 w15_a34 w15_a30 w15_a2c w15_a28 w15_a24 w15_a20 w15_430 w15_42c w15_428 w15_424 w15_420 w15_130 w15_12c w15_128 w15_124 w15_120 w15_11c w15_118 w15_114 w15_110 w15_10c w15_108 w15_104 w15_100 w15_fc w15_f8 w15_f4 w15_f0 w15_ec w15_e8 w15_e4 w15_e0 w15_dc w15_d8 w15_d4 w15_d0 w15_cc w15_c8 w15_c4 w15_c0 w15_bc w15_b8 w15_b4 w15_b0 w15_ac w15_a8 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_38 w15_34 w15_30 w15_2c w15_28 w15_24 w15_20 w15_1c w15_18 w15_14 w15_10 w15_c w15_8 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_14 g15_13 g15_12 g15_11 g15_10 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0x2D46: sw
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sw F E16 s16 sv_at_2d46 (off' := 0x2D48) (c := 0x438)
    (by decide) (by rw [g16_14]; sv_addr) (by decide) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_9 : reg n17 (9 : Fin 32) = c := by rw [rg17 (9 : Fin 32), g16_9]
  have g17_10 : reg n17 a0 = BitVec.ofNat 32 0x3FCC47D7 := by rw [rg17 a0, g16_10]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 0x1 := by rw [rg17 a1, g16_11]
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 0x20 := by rw [rg17 a2, g16_12]
  have g17_13 : reg n17 a3 = kp := by rw [rg17 a3, g16_13]
  have g17_14 : reg n17 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg17 a4, g16_14]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rg17 (18 : Fin 32), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rg17 (19 : Fin 32), g16_19]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [rg17 (21 : Fin 32), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = rl := by rw [rg17 (22 : Fin 32), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = rp := by rw [rg17 (23 : Fin 32), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = dg := by rw [rg17 (24 : Fin 32), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = q := by rw [rg17 (25 : Fin 32), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [rg17 (26 : Fin 32), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg17 (27 : Fin 32), g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K17.w32 (by decide) (by decide)).trans w16_8
  have w17_c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K17.w32 (by decide) (by decide)).trans w16_c
  have w17_10 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K17.w32 (by decide) (by decide)).trans w16_10
  have w17_14 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K17.w32 (by decide) (by decide)).trans w16_14
  have w17_18 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K17.w32 (by decide) (by decide)).trans w16_18
  have w17_1c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K17.w32 (by decide) (by decide)).trans w16_1c
  have w17_20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K17.w32 (by decide) (by decide)).trans w16_20
  have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K17.w32 (by decide) (by decide)).trans w16_24
  have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K17.w32 (by decide) (by decide)).trans w16_28
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K17.w32 (by decide) (by decide)).trans w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K17.w32 (by decide) (by decide)).trans w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K17.w32 (by decide) (by decide)).trans w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K17.w32 (by decide) (by decide)).trans w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K17.w32 (by decide) (by decide)).trans w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K17.w32 (by decide) (by decide)).trans w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K17.w32 (by decide) (by decide)).trans w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K17.w32 (by decide) (by decide)).trans w16_48
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
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K17.w32 (by decide) (by decide)).trans w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K17.w32 (by decide) (by decide)).trans w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := (K17.w32 (by decide) (by decide)).trans w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K17.w32 (by decide) (by decide)).trans w16_42c
  have w17_430 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := (K17.w32 (by decide) (by decide)).trans w16_430
  have w17_434 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K17.w32 (by decide) (by decide)).trans w16_434
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
  have w17_438 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := by rw [W17, g16_13]
  have q17_320 : ∀ j, j < 31 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K17.range (by decide) (by decide) j hj).trans (q16_320 j hj)
  clear q16_320 w16_34 w16_aa4 w16_aa0 w16_a3c w16_a38 w16_a34 w16_a30 w16_a2c w16_a28 w16_a24 w16_a20 w16_434 w16_430 w16_42c w16_428 w16_424 w16_420 w16_130 w16_12c w16_128 w16_124 w16_120 w16_11c w16_118 w16_114 w16_110 w16_10c w16_108 w16_104 w16_100 w16_fc w16_f8 w16_f4 w16_f0 w16_ec w16_e8 w16_e4 w16_e0 w16_dc w16_d8 w16_d4 w16_d0 w16_cc w16_c8 w16_c4 w16_c0 w16_bc w16_b8 w16_b4 w16_b0 w16_ac w16_a8 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_38 w16_30 w16_2c w16_28 w16_24 w16_20 w16_1c w16_18 w16_14 w16_10 w16_c w16_8 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_14 g16_13 g16_12 g16_11 g16_10 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x2D48: sw
  obtain ⟨n18, d18, s18, fr18, K18, W18, rg18⟩ := sv_sw F E17 s17 sv_at_2d48 (off' := 0x2D4A) (c := 0x43C)
    (by decide) (by rw [g17_14]; sv_addr) (by decide) (by decide)
  have t18 : Steps n0 n18 := t17.trans d18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rg18 sp, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg18 (3 : Fin 32), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg18 (4 : Fin 32), g17_4]
  have g18_9 : reg n18 (9 : Fin 32) = c := by rw [rg18 (9 : Fin 32), g17_9]
  have g18_10 : reg n18 a0 = BitVec.ofNat 32 0x3FCC47D7 := by rw [rg18 a0, g17_10]
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 0x1 := by rw [rg18 a1, g17_11]
  have g18_12 : reg n18 a2 = BitVec.ofNat 32 0x20 := by rw [rg18 a2, g17_12]
  have g18_13 : reg n18 a3 = kp := by rw [rg18 a3, g17_13]
  have g18_14 : reg n18 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg18 a4, g17_14]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rg18 (18 : Fin 32), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rg18 (19 : Fin 32), g17_19]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [rg18 (21 : Fin 32), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = rl := by rw [rg18 (22 : Fin 32), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = rp := by rw [rg18 (23 : Fin 32), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = dg := by rw [rg18 (24 : Fin 32), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = q := by rw [rg18 (25 : Fin 32), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [rg18 (26 : Fin 32), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg18 (27 : Fin 32), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K18.w32 (by decide) (by decide)).trans w17_8
  have w18_c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K18.w32 (by decide) (by decide)).trans w17_c
  have w18_10 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K18.w32 (by decide) (by decide)).trans w17_10
  have w18_14 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K18.w32 (by decide) (by decide)).trans w17_14
  have w18_18 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K18.w32 (by decide) (by decide)).trans w17_18
  have w18_1c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K18.w32 (by decide) (by decide)).trans w17_1c
  have w18_20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K18.w32 (by decide) (by decide)).trans w17_20
  have w18_24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K18.w32 (by decide) (by decide)).trans w17_24
  have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K18.w32 (by decide) (by decide)).trans w17_28
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K18.w32 (by decide) (by decide)).trans w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K18.w32 (by decide) (by decide)).trans w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K18.w32 (by decide) (by decide)).trans w17_34
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
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K18.w32 (by decide) (by decide)).trans w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K18.w32 (by decide) (by decide)).trans w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K18.w32 (by decide) (by decide)).trans w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K18.w32 (by decide) (by decide)).trans w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K18.w32 (by decide) (by decide)).trans w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K18.w32 (by decide) (by decide)).trans w17_8c
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K18.w32 (by decide) (by decide)).trans w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K18.w32 (by decide) (by decide)).trans w17_94
  have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K18.w32 (by decide) (by decide)).trans w17_98
  have w18_9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K18.w32 (by decide) (by decide)).trans w17_9c
  have w18_a0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K18.w32 (by decide) (by decide)).trans w17_a0
  have w18_a4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K18.w32 (by decide) (by decide)).trans w17_a4
  have w18_a8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K18.w32 (by decide) (by decide)).trans w17_a8
  have w18_ac : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K18.w32 (by decide) (by decide)).trans w17_ac
  have w18_b0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K18.w32 (by decide) (by decide)).trans w17_b0
  have w18_b4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K18.w32 (by decide) (by decide)).trans w17_b4
  have w18_b8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K18.w32 (by decide) (by decide)).trans w17_b8
  have w18_bc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K18.w32 (by decide) (by decide)).trans w17_bc
  have w18_c0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K18.w32 (by decide) (by decide)).trans w17_c0
  have w18_c4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K18.w32 (by decide) (by decide)).trans w17_c4
  have w18_c8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K18.w32 (by decide) (by decide)).trans w17_c8
  have w18_cc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K18.w32 (by decide) (by decide)).trans w17_cc
  have w18_d0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K18.w32 (by decide) (by decide)).trans w17_d0
  have w18_d4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K18.w32 (by decide) (by decide)).trans w17_d4
  have w18_d8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K18.w32 (by decide) (by decide)).trans w17_d8
  have w18_dc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K18.w32 (by decide) (by decide)).trans w17_dc
  have w18_e0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K18.w32 (by decide) (by decide)).trans w17_e0
  have w18_e4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K18.w32 (by decide) (by decide)).trans w17_e4
  have w18_e8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K18.w32 (by decide) (by decide)).trans w17_e8
  have w18_ec : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K18.w32 (by decide) (by decide)).trans w17_ec
  have w18_f0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K18.w32 (by decide) (by decide)).trans w17_f0
  have w18_f4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K18.w32 (by decide) (by decide)).trans w17_f4
  have w18_f8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K18.w32 (by decide) (by decide)).trans w17_f8
  have w18_fc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K18.w32 (by decide) (by decide)).trans w17_fc
  have w18_100 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K18.w32 (by decide) (by decide)).trans w17_100
  have w18_104 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K18.w32 (by decide) (by decide)).trans w17_104
  have w18_108 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K18.w32 (by decide) (by decide)).trans w17_108
  have w18_10c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K18.w32 (by decide) (by decide)).trans w17_10c
  have w18_110 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K18.w32 (by decide) (by decide)).trans w17_110
  have w18_114 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K18.w32 (by decide) (by decide)).trans w17_114
  have w18_118 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K18.w32 (by decide) (by decide)).trans w17_118
  have w18_11c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K18.w32 (by decide) (by decide)).trans w17_11c
  have w18_120 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K18.w32 (by decide) (by decide)).trans w17_120
  have w18_124 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K18.w32 (by decide) (by decide)).trans w17_124
  have w18_128 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K18.w32 (by decide) (by decide)).trans w17_128
  have w18_12c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K18.w32 (by decide) (by decide)).trans w17_12c
  have w18_130 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K18.w32 (by decide) (by decide)).trans w17_130
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K18.w32 (by decide) (by decide)).trans w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K18.w32 (by decide) (by decide)).trans w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := (K18.w32 (by decide) (by decide)).trans w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K18.w32 (by decide) (by decide)).trans w17_42c
  have w18_430 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := (K18.w32 (by decide) (by decide)).trans w17_430
  have w18_434 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K18.w32 (by decide) (by decide)).trans w17_434
  have w18_438 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := (K18.w32 (by decide) (by decide)).trans w17_438
  have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K18.w32 (by decide) (by decide)).trans w17_a20
  have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K18.w32 (by decide) (by decide)).trans w17_a24
  have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K18.w32 (by decide) (by decide)).trans w17_a28
  have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K18.w32 (by decide) (by decide)).trans w17_a2c
  have w18_a30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K18.w32 (by decide) (by decide)).trans w17_a30
  have w18_a34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K18.w32 (by decide) (by decide)).trans w17_a34
  have w18_a38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K18.w32 (by decide) (by decide)).trans w17_a38
  have w18_a3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K18.w32 (by decide) (by decide)).trans w17_a3c
  have w18_aa0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K18.w32 (by decide) (by decide)).trans w17_aa0
  have w18_aa4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K18.w32 (by decide) (by decide)).trans w17_aa4
  have w18_43c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := by rw [W18, g17_12]
  have q18_320 : ∀ j, j < 31 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_320 j hj)
  clear q17_320 w17_438 w17_aa4 w17_aa0 w17_a3c w17_a38 w17_a34 w17_a30 w17_a2c w17_a28 w17_a24 w17_a20 w17_434 w17_430 w17_42c w17_428 w17_424 w17_420 w17_130 w17_12c w17_128 w17_124 w17_120 w17_11c w17_118 w17_114 w17_110 w17_10c w17_108 w17_104 w17_100 w17_fc w17_f8 w17_f4 w17_f0 w17_ec w17_e8 w17_e4 w17_e0 w17_dc w17_d8 w17_d4 w17_d0 w17_cc w17_c8 w17_c4 w17_c0 w17_bc w17_b8 w17_b4 w17_b0 w17_ac w17_a8 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 w17_20 w17_1c w17_18 w17_14 w17_10 w17_c w17_8 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_14 g17_13 g17_12 g17_11 g17_10 g17_9 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0x2D4A
  obtain ⟨n19, c19, u19⟩ := s18.block svCs12d4a E18.self svCs12d4a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x2D58 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svCs12d4a (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_9 : reg n19 (9 : Fin 32) = c := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_13 : reg n19 a3 = kp := by
    rw [rb19, runBlock_reg _ _ _ a3 s18.zero (by decide), g18_13]
  have g19_14 : reg n19 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb19, runBlock_reg _ _ _ a4 s18.zero (by decide), g18_14]
  have g19_18 : reg n19 (18 : Fin 32) = out := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = rl := by
    rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = rp := by
    rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = dg := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = q := by
    rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svCs12d4a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_9, g18_10, g18_11, g18_12, g18_13, g18_14, g18_18, g18_19, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svCs12d4a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_9, g18_10, g18_11, g18_12, g18_13, g18_14, g18_18, g18_19, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g19_12 : reg n19 a2 = BitVec.ofNat 32 0x4 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svCs12d4a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_9, g18_10, g18_11, g18_12, g18_13, g18_14, g18_18, g18_19, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m19]; exact w18_8
  have w19_c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m19]; exact w18_c
  have w19_10 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m19]; exact w18_10
  have w19_14 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m19]; exact w18_14
  have w19_18 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := by rw [m19]; exact w18_18
  have w19_1c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m19]; exact w18_1c
  have w19_20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m19]; exact w18_20
  have w19_24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m19]; exact w18_24
  have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m19]; exact w18_28
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m19]; exact w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m19]; exact w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m19]; exact w18_34
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
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := by rw [m19]; exact w18_42c
  have w19_430 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := by rw [m19]; exact w18_430
  have w19_434 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := by rw [m19]; exact w18_434
  have w19_438 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := by rw [m19]; exact w18_438
  have w19_43c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := by rw [m19]; exact w18_43c
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
  have q19_320 : ∀ j, j < 31 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m19]; exact q18_320 j hj
  clear q18_320 w18_43c w18_aa4 w18_aa0 w18_a3c w18_a38 w18_a34 w18_a30 w18_a2c w18_a28 w18_a24 w18_a20 w18_438 w18_434 w18_430 w18_42c w18_428 w18_424 w18_420 w18_130 w18_12c w18_128 w18_124 w18_120 w18_11c w18_118 w18_114 w18_110 w18_10c w18_108 w18_104 w18_100 w18_fc w18_f8 w18_f4 w18_f0 w18_ec w18_e8 w18_e4 w18_e0 w18_dc w18_d8 w18_d4 w18_d0 w18_cc w18_c8 w18_c4 w18_c0 w18_bc w18_b8 w18_b4 w18_b0 w18_ac w18_a8 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 w18_20 w18_1c w18_18 w18_14 w18_10 w18_c w18_8 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_14 g18_13 g18_12 g18_11 g18_10 g18_9 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
  -- 0x2D58: sv_sha256P4F
  obtain ⟨n20, c20, s20, sp20, rk20, K20, D20, fr20⟩ := sv_sha256P4F (oc := 0x1380) (pc := 0x420) (l0 := (w44).toNat) (l1 := 1) (l2 := 1) (l3 := 32)
    F E19 (S2.sv F KS fR19) KS s19 sv_at_2d58 sv_at_2d5c (by decide) (by decide) g19_2
    g19_10 g19_11 g19_12 (by decide) (by decide) (by decide)
    w19_420 (by rw [w19_424, ofNat_toNat_self]) w19_428 w19_42c w19_430 w19_434 w19_438 w19_43c
    (.inl l_in) (.inr ⟨by decide, by decide⟩) (.inr ⟨by decide, by decide⟩) (.inl kp_in) (by have := l_in.lo; omega) (by decide) (by decide) (by decide)
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keepL K20 (by decide)
  rw [sv_mbRo F fR19 (.inl l_in), sv_mbRo F fR19 (.inr ⟨by decide, by decide⟩), sv_mbRo F fR19 (.inr ⟨by decide, by decide⟩), sv_mbRo F fR19 (.inl kp_in)] at D20
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk20 (3 : Fin 32) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk20 (4 : Fin 32) (by decide), g19_4]
  have g20_9 : reg n20 (9 : Fin 32) = c := by rw [rk20 (9 : Fin 32) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rk20 (18 : Fin 32) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rk20 (19 : Fin 32) (by decide), g19_19]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [rk20 (21 : Fin 32) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = rl := by rw [rk20 (22 : Fin 32) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = rp := by rw [rk20 (23 : Fin 32) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = dg := by rw [rk20 (24 : Fin 32) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = q := by rw [rk20 (25 : Fin 32) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [rk20 (26 : Fin 32) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk20 (27 : Fin 32) (by decide), g19_27]
  have g20_2 : reg n20 sp = B + 0x21A0 := sp20
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x1380, 0x20)] := keep_kk19.trans K20
  clear keep_kk19
  have w20_8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K20.w32 (by decide) (by decide)).trans w19_8
  have w20_c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K20.w32 (by decide) (by decide)).trans w19_c
  have w20_10 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K20.w32 (by decide) (by decide)).trans w19_10
  have w20_14 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K20.w32 (by decide) (by decide)).trans w19_14
  have w20_18 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K20.w32 (by decide) (by decide)).trans w19_18
  have w20_1c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K20.w32 (by decide) (by decide)).trans w19_1c
  have w20_20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K20.w32 (by decide) (by decide)).trans w19_20
  have w20_24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K20.w32 (by decide) (by decide)).trans w19_24
  have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K20.w32 (by decide) (by decide)).trans w19_28
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K20.w32 (by decide) (by decide)).trans w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K20.w32 (by decide) (by decide)).trans w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K20.w32 (by decide) (by decide)).trans w19_34
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
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K20.w32 (by decide) (by decide)).trans w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K20.w32 (by decide) (by decide)).trans w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K20.w32 (by decide) (by decide)).trans w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K20.w32 (by decide) (by decide)).trans w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K20.w32 (by decide) (by decide)).trans w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K20.w32 (by decide) (by decide)).trans w19_8c
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K20.w32 (by decide) (by decide)).trans w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K20.w32 (by decide) (by decide)).trans w19_94
  have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K20.w32 (by decide) (by decide)).trans w19_98
  have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K20.w32 (by decide) (by decide)).trans w19_9c
  have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K20.w32 (by decide) (by decide)).trans w19_a0
  have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K20.w32 (by decide) (by decide)).trans w19_a4
  have w20_a8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K20.w32 (by decide) (by decide)).trans w19_a8
  have w20_ac : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K20.w32 (by decide) (by decide)).trans w19_ac
  have w20_b0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K20.w32 (by decide) (by decide)).trans w19_b0
  have w20_b4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K20.w32 (by decide) (by decide)).trans w19_b4
  have w20_b8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K20.w32 (by decide) (by decide)).trans w19_b8
  have w20_bc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K20.w32 (by decide) (by decide)).trans w19_bc
  have w20_c0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K20.w32 (by decide) (by decide)).trans w19_c0
  have w20_c4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K20.w32 (by decide) (by decide)).trans w19_c4
  have w20_c8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K20.w32 (by decide) (by decide)).trans w19_c8
  have w20_cc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K20.w32 (by decide) (by decide)).trans w19_cc
  have w20_d0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K20.w32 (by decide) (by decide)).trans w19_d0
  have w20_d4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K20.w32 (by decide) (by decide)).trans w19_d4
  have w20_d8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K20.w32 (by decide) (by decide)).trans w19_d8
  have w20_dc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K20.w32 (by decide) (by decide)).trans w19_dc
  have w20_e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K20.w32 (by decide) (by decide)).trans w19_e0
  have w20_e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K20.w32 (by decide) (by decide)).trans w19_e4
  have w20_e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K20.w32 (by decide) (by decide)).trans w19_e8
  have w20_ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K20.w32 (by decide) (by decide)).trans w19_ec
  have w20_f0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K20.w32 (by decide) (by decide)).trans w19_f0
  have w20_f4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K20.w32 (by decide) (by decide)).trans w19_f4
  have w20_f8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K20.w32 (by decide) (by decide)).trans w19_f8
  have w20_fc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K20.w32 (by decide) (by decide)).trans w19_fc
  have w20_100 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K20.w32 (by decide) (by decide)).trans w19_100
  have w20_104 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K20.w32 (by decide) (by decide)).trans w19_104
  have w20_108 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K20.w32 (by decide) (by decide)).trans w19_108
  have w20_10c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K20.w32 (by decide) (by decide)).trans w19_10c
  have w20_110 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K20.w32 (by decide) (by decide)).trans w19_110
  have w20_114 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K20.w32 (by decide) (by decide)).trans w19_114
  have w20_118 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K20.w32 (by decide) (by decide)).trans w19_118
  have w20_11c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K20.w32 (by decide) (by decide)).trans w19_11c
  have w20_120 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K20.w32 (by decide) (by decide)).trans w19_120
  have w20_124 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K20.w32 (by decide) (by decide)).trans w19_124
  have w20_128 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K20.w32 (by decide) (by decide)).trans w19_128
  have w20_12c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K20.w32 (by decide) (by decide)).trans w19_12c
  have w20_130 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K20.w32 (by decide) (by decide)).trans w19_130
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K20.w32 (by decide) (by decide)).trans w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K20.w32 (by decide) (by decide)).trans w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := (K20.w32 (by decide) (by decide)).trans w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K20.w32 (by decide) (by decide)).trans w19_42c
  have w20_430 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := (K20.w32 (by decide) (by decide)).trans w19_430
  have w20_434 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K20.w32 (by decide) (by decide)).trans w19_434
  have w20_438 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := (K20.w32 (by decide) (by decide)).trans w19_438
  have w20_43c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := (K20.w32 (by decide) (by decide)).trans w19_43c
  have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K20.w32 (by decide) (by decide)).trans w19_a20
  have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K20.w32 (by decide) (by decide)).trans w19_a24
  have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K20.w32 (by decide) (by decide)).trans w19_a28
  have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K20.w32 (by decide) (by decide)).trans w19_a2c
  have w20_a30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K20.w32 (by decide) (by decide)).trans w19_a30
  have w20_a34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K20.w32 (by decide) (by decide)).trans w19_a34
  have w20_a38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K20.w32 (by decide) (by decide)).trans w19_a38
  have w20_a3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K20.w32 (by decide) (by decide)).trans w19_a3c
  have w20_aa0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K20.w32 (by decide) (by decide)).trans w19_aa0
  have w20_aa4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K20.w32 (by decide) (by decide)).trans w19_aa4
  have q20_320 : ∀ j, j < 31 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_320 j hj)
  clear q19_320 w19_aa4 w19_aa0 w19_a3c w19_a38 w19_a34 w19_a30 w19_a2c w19_a28 w19_a24 w19_a20 w19_43c w19_438 w19_434 w19_430 w19_42c w19_428 w19_424 w19_420 w19_130 w19_12c w19_128 w19_124 w19_120 w19_11c w19_118 w19_114 w19_110 w19_10c w19_108 w19_104 w19_100 w19_fc w19_f8 w19_f4 w19_f0 w19_ec w19_e8 w19_e4 w19_e0 w19_dc w19_d8 w19_d4 w19_d0 w19_cc w19_c8 w19_c4 w19_c0 w19_bc w19_b8 w19_b4 w19_b0 w19_ac w19_a8 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 w19_20 w19_1c w19_18 w19_14 w19_10 w19_c w19_8 g19_12 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_19 g19_18 g19_14 g19_13 g19_9 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  have w20_1380 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 := ld_digest D20 (by decide)
  -- 0x2D60: sw
  obtain ⟨n21, d21, s21, fr21, K21, W21, rg21⟩ := sv_sw F E20 s20 sv_at_2d60 (off' := 0x2D62) (c := 0x30)
    (by decide) (by rw [g20_2]; sv_addr) (by decide) (by decide)
  have t21 : Steps n0 n21 := t20.trans d21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rg21 sp, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg21 (3 : Fin 32), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg21 (4 : Fin 32), g20_4]
  have g21_9 : reg n21 (9 : Fin 32) = c := by rw [rg21 (9 : Fin 32), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rg21 (18 : Fin 32), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rg21 (19 : Fin 32), g20_19]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [rg21 (21 : Fin 32), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = rl := by rw [rg21 (22 : Fin 32), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = rp := by rw [rg21 (23 : Fin 32), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = dg := by rw [rg21 (24 : Fin 32), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = q := by rw [rg21 (25 : Fin 32), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [rg21 (26 : Fin 32), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg21 (27 : Fin 32), g20_27]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x1380, 0x20), (0x30, 0x4)] := keep_kk20.trans K21.toL
  clear keep_kk20
  have w21_8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K21.w32 (by decide) (by decide)).trans w20_8
  have w21_c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K21.w32 (by decide) (by decide)).trans w20_c
  have w21_10 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K21.w32 (by decide) (by decide)).trans w20_10
  have w21_14 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := (K21.w32 (by decide) (by decide)).trans w20_14
  have w21_18 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K21.w32 (by decide) (by decide)).trans w20_18
  have w21_1c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K21.w32 (by decide) (by decide)).trans w20_1c
  have w21_20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K21.w32 (by decide) (by decide)).trans w20_20
  have w21_24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K21.w32 (by decide) (by decide)).trans w20_24
  have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K21.w32 (by decide) (by decide)).trans w20_28
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K21.w32 (by decide) (by decide)).trans w20_2c
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K21.w32 (by decide) (by decide)).trans w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K21.w32 (by decide) (by decide)).trans w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K21.w32 (by decide) (by decide)).trans w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K21.w32 (by decide) (by decide)).trans w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K21.w32 (by decide) (by decide)).trans w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K21.w32 (by decide) (by decide)).trans w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K21.w32 (by decide) (by decide)).trans w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K21.w32 (by decide) (by decide)).trans w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K21.w32 (by decide) (by decide)).trans w20_54
  have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K21.w32 (by decide) (by decide)).trans w20_58
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K21.w32 (by decide) (by decide)).trans w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K21.w32 (by decide) (by decide)).trans w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K21.w32 (by decide) (by decide)).trans w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K21.w32 (by decide) (by decide)).trans w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K21.w32 (by decide) (by decide)).trans w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K21.w32 (by decide) (by decide)).trans w20_70
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K21.w32 (by decide) (by decide)).trans w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K21.w32 (by decide) (by decide)).trans w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K21.w32 (by decide) (by decide)).trans w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K21.w32 (by decide) (by decide)).trans w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K21.w32 (by decide) (by decide)).trans w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K21.w32 (by decide) (by decide)).trans w20_8c
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K21.w32 (by decide) (by decide)).trans w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K21.w32 (by decide) (by decide)).trans w20_94
  have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K21.w32 (by decide) (by decide)).trans w20_98
  have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K21.w32 (by decide) (by decide)).trans w20_9c
  have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K21.w32 (by decide) (by decide)).trans w20_a0
  have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K21.w32 (by decide) (by decide)).trans w20_a4
  have w21_a8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K21.w32 (by decide) (by decide)).trans w20_a8
  have w21_ac : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K21.w32 (by decide) (by decide)).trans w20_ac
  have w21_b0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K21.w32 (by decide) (by decide)).trans w20_b0
  have w21_b4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K21.w32 (by decide) (by decide)).trans w20_b4
  have w21_b8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K21.w32 (by decide) (by decide)).trans w20_b8
  have w21_bc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K21.w32 (by decide) (by decide)).trans w20_bc
  have w21_c0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K21.w32 (by decide) (by decide)).trans w20_c0
  have w21_c4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K21.w32 (by decide) (by decide)).trans w20_c4
  have w21_c8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K21.w32 (by decide) (by decide)).trans w20_c8
  have w21_cc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K21.w32 (by decide) (by decide)).trans w20_cc
  have w21_d0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K21.w32 (by decide) (by decide)).trans w20_d0
  have w21_d4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K21.w32 (by decide) (by decide)).trans w20_d4
  have w21_d8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K21.w32 (by decide) (by decide)).trans w20_d8
  have w21_dc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K21.w32 (by decide) (by decide)).trans w20_dc
  have w21_e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K21.w32 (by decide) (by decide)).trans w20_e0
  have w21_e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K21.w32 (by decide) (by decide)).trans w20_e4
  have w21_e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K21.w32 (by decide) (by decide)).trans w20_e8
  have w21_ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K21.w32 (by decide) (by decide)).trans w20_ec
  have w21_f0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K21.w32 (by decide) (by decide)).trans w20_f0
  have w21_f4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K21.w32 (by decide) (by decide)).trans w20_f4
  have w21_f8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K21.w32 (by decide) (by decide)).trans w20_f8
  have w21_fc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K21.w32 (by decide) (by decide)).trans w20_fc
  have w21_100 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K21.w32 (by decide) (by decide)).trans w20_100
  have w21_104 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K21.w32 (by decide) (by decide)).trans w20_104
  have w21_108 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K21.w32 (by decide) (by decide)).trans w20_108
  have w21_10c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K21.w32 (by decide) (by decide)).trans w20_10c
  have w21_110 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K21.w32 (by decide) (by decide)).trans w20_110
  have w21_114 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K21.w32 (by decide) (by decide)).trans w20_114
  have w21_118 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K21.w32 (by decide) (by decide)).trans w20_118
  have w21_11c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K21.w32 (by decide) (by decide)).trans w20_11c
  have w21_120 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K21.w32 (by decide) (by decide)).trans w20_120
  have w21_124 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K21.w32 (by decide) (by decide)).trans w20_124
  have w21_128 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K21.w32 (by decide) (by decide)).trans w20_128
  have w21_12c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K21.w32 (by decide) (by decide)).trans w20_12c
  have w21_130 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K21.w32 (by decide) (by decide)).trans w20_130
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K21.w32 (by decide) (by decide)).trans w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K21.w32 (by decide) (by decide)).trans w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := (K21.w32 (by decide) (by decide)).trans w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K21.w32 (by decide) (by decide)).trans w20_42c
  have w21_430 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := (K21.w32 (by decide) (by decide)).trans w20_430
  have w21_434 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K21.w32 (by decide) (by decide)).trans w20_434
  have w21_438 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := (K21.w32 (by decide) (by decide)).trans w20_438
  have w21_43c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := (K21.w32 (by decide) (by decide)).trans w20_43c
  have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K21.w32 (by decide) (by decide)).trans w20_a20
  have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K21.w32 (by decide) (by decide)).trans w20_a24
  have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K21.w32 (by decide) (by decide)).trans w20_a28
  have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K21.w32 (by decide) (by decide)).trans w20_a2c
  have w21_a30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K21.w32 (by decide) (by decide)).trans w20_a30
  have w21_a34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K21.w32 (by decide) (by decide)).trans w20_a34
  have w21_a38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K21.w32 (by decide) (by decide)).trans w20_a38
  have w21_a3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K21.w32 (by decide) (by decide)).trans w20_a3c
  have w21_aa0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K21.w32 (by decide) (by decide)).trans w20_aa0
  have w21_aa4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K21.w32 (by decide) (by decide)).trans w20_aa4
  have w21_1380 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 := (K21.w32 (by decide) (by decide)).trans w20_1380
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 := by rw [W21, s20.zero]; rfl
  have q21_320 : ∀ j, j < 31 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K21.range (by decide) (by decide) j hj).trans (q20_320 j hj)
  clear q20_320 w20_aa4 w20_aa0 w20_a3c w20_a38 w20_a34 w20_a30 w20_a2c w20_a28 w20_a24 w20_a20 w20_43c w20_438 w20_434 w20_430 w20_42c w20_428 w20_424 w20_420 w20_130 w20_12c w20_128 w20_124 w20_120 w20_11c w20_118 w20_114 w20_110 w20_10c w20_108 w20_104 w20_100 w20_fc w20_f8 w20_f4 w20_f0 w20_ec w20_e8 w20_e4 w20_e0 w20_dc w20_d8 w20_d4 w20_d0 w20_cc w20_c8 w20_c4 w20_c0 w20_bc w20_b8 w20_b4 w20_b0 w20_ac w20_a8 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 w20_20 w20_1c w20_18 w20_14 w20_10 w20_c w20_8 g20_2 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_9 g20_4 g20_3 V20 E20 fR20 t20 fr20 K20 rk20 sp20 s20 c20
  -- 0x2D62
  obtain ⟨n22, c22, u22⟩ := s21.block svCs12d62 E21.self svCs12d62_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0x2D6A (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svCs12d62 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
  have g22_9 : reg n22 (9 : Fin 32) = c := by
    rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by
    rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = rl := by
    rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = rp := by
    rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = dg := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = q := by
    rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_10 : reg n22 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svCs12d62, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_9, g21_18, g21_19, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x1380, 0x20), (0x30, 0x4)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m22]; exact w21_8
  have w22_c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m22]; exact w21_c
  have w22_10 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m22]; exact w21_10
  have w22_14 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m22]; exact w21_14
  have w22_18 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := by rw [m22]; exact w21_18
  have w22_1c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m22]; exact w21_1c
  have w22_20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m22]; exact w21_20
  have w22_24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m22]; exact w21_24
  have w22_28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m22]; exact w21_28
  have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m22]; exact w21_2c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m22]; exact w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m22]; exact w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m22]; exact w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m22]; exact w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m22]; exact w21_48
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
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := by rw [m22]; exact w21_42c
  have w22_430 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := by rw [m22]; exact w21_430
  have w22_434 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := by rw [m22]; exact w21_434
  have w22_438 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := by rw [m22]; exact w21_438
  have w22_43c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := by rw [m22]; exact w21_43c
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
  have w22_1380 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 := by rw [m22]; exact w21_1380
  have q22_320 : ∀ j, j < 31 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m22]; exact q21_320 j hj
  clear q21_320 w21_30 w21_1380 w21_aa4 w21_aa0 w21_a3c w21_a38 w21_a34 w21_a30 w21_a2c w21_a28 w21_a24 w21_a20 w21_43c w21_438 w21_434 w21_430 w21_42c w21_428 w21_424 w21_420 w21_130 w21_12c w21_128 w21_124 w21_120 w21_11c w21_118 w21_114 w21_110 w21_10c w21_108 w21_104 w21_100 w21_fc w21_f8 w21_f4 w21_f0 w21_ec w21_e8 w21_e4 w21_e0 w21_dc w21_d8 w21_d4 w21_d0 w21_cc w21_c8 w21_c4 w21_c0 w21_bc w21_b8 w21_b4 w21_b0 w21_ac w21_a8 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_2c w21_28 w21_24 w21_20 w21_1c w21_18 w21_14 w21_10 w21_c w21_8 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 rg21 W21 K21 fr21 s21 d21 w20_1380
  -- 0x2D6A: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_2d6a (off' := 0x2D6C) (by decide)
    (by rw [g22_10, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0x60 = B + 0x21A0 + BitVec.ofNat 32 0x1380 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x2D6C (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_9 : reg n23 (9 : Fin 32) = c := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = rl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = rp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = dg := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = q := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_10 : reg n23 a0 = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_10, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0x60 = B + 0x21A0 + BitVec.ofNat 32 0x1380 by sv_addr, w22_1380]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x1380, 0x20), (0x30, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m23]; exact w22_8
  have w23_c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m23]; exact w22_c
  have w23_10 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m23]; exact w22_10
  have w23_14 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 := by rw [m23]; exact w22_14
  have w23_18 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := by rw [m23]; exact w22_18
  have w23_1c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := by rw [m23]; exact w22_1c
  have w23_20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := by rw [m23]; exact w22_20
  have w23_24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m23]; exact w22_24
  have w23_28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m23]; exact w22_28
  have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m23]; exact w22_2c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m23]; exact w22_34
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
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := by rw [m23]; exact w22_42c
  have w23_430 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := by rw [m23]; exact w22_430
  have w23_434 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := by rw [m23]; exact w22_434
  have w23_438 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := by rw [m23]; exact w22_438
  have w23_43c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := by rw [m23]; exact w22_43c
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
  have w23_1380 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 := by rw [m23]; exact w22_1380
  have q23_320 : ∀ j, j < 31 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => by rw [m23]; exact q22_320 j hj
  clear q22_320 w22_1380 w22_aa4 w22_aa0 w22_a3c w22_a38 w22_a34 w22_a30 w22_a2c w22_a28 w22_a24 w22_a20 w22_43c w22_438 w22_434 w22_430 w22_42c w22_428 w22_424 w22_420 w22_130 w22_12c w22_128 w22_124 w22_120 w22_11c w22_118 w22_114 w22_110 w22_10c w22_108 w22_104 w22_100 w22_fc w22_f8 w22_f4 w22_f0 w22_ec w22_e8 w22_e4 w22_e0 w22_dc w22_d8 w22_d4 w22_d0 w22_cc w22_c8 w22_c4 w22_c0 w22_bc w22_b8 w22_b4 w22_b0 w22_ac w22_a8 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 w22_2c w22_28 w22_24 w22_20 w22_1c w22_18 w22_14 w22_10 w22_c w22_8 g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_19 g22_18 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0x2D6C: sw
  obtain ⟨n24, d24, s24, fr24, K24, W24, rg24⟩ := sv_sw F E23 s23 sv_at_2d6c (off' := 0x2D6E) (c := 0x14)
    (by decide) (by rw [g23_2]; sv_addr) (by decide) (by decide)
  have t24 : Steps n0 n24 := t23.trans d24
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [rg24 sp, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg24 (3 : Fin 32), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg24 (4 : Fin 32), g23_4]
  have g24_9 : reg n24 (9 : Fin 32) = c := by rw [rg24 (9 : Fin 32), g23_9]
  have g24_10 : reg n24 a0 = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 := by rw [rg24 a0, g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [rg24 (18 : Fin 32), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [rg24 (19 : Fin 32), g23_19]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [rg24 (21 : Fin 32), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = rl := by rw [rg24 (22 : Fin 32), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = rp := by rw [rg24 (23 : Fin 32), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = dg := by rw [rg24 (24 : Fin 32), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = q := by rw [rg24 (25 : Fin 32), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [rg24 (26 : Fin 32), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg24 (27 : Fin 32), g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x1380, 0x20), (0x30, 0x4), (0x14, 0x4)] := keep_kk23.trans K24.toL
  clear keep_kk23
  have w24_8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K24.w32 (by decide) (by decide)).trans w23_8
  have w24_c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K24.w32 (by decide) (by decide)).trans w23_c
  have w24_10 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K24.w32 (by decide) (by decide)).trans w23_10
  have w24_18 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kw := (K24.w32 (by decide) (by decide)).trans w23_18
  have w24_1c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 := (K24.w32 (by decide) (by decide)).trans w23_1c
  have w24_20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 := (K24.w32 (by decide) (by decide)).trans w23_20
  have w24_24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K24.w32 (by decide) (by decide)).trans w23_24
  have w24_28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K24.w32 (by decide) (by decide)).trans w23_28
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K24.w32 (by decide) (by decide)).trans w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 := (K24.w32 (by decide) (by decide)).trans w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K24.w32 (by decide) (by decide)).trans w23_34
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
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K24.w32 (by decide) (by decide)).trans w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K24.w32 (by decide) (by decide)).trans w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K24.w32 (by decide) (by decide)).trans w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K24.w32 (by decide) (by decide)).trans w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K24.w32 (by decide) (by decide)).trans w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K24.w32 (by decide) (by decide)).trans w23_8c
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K24.w32 (by decide) (by decide)).trans w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K24.w32 (by decide) (by decide)).trans w23_94
  have w24_98 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K24.w32 (by decide) (by decide)).trans w23_98
  have w24_9c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K24.w32 (by decide) (by decide)).trans w23_9c
  have w24_a0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K24.w32 (by decide) (by decide)).trans w23_a0
  have w24_a4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K24.w32 (by decide) (by decide)).trans w23_a4
  have w24_a8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K24.w32 (by decide) (by decide)).trans w23_a8
  have w24_ac : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K24.w32 (by decide) (by decide)).trans w23_ac
  have w24_b0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K24.w32 (by decide) (by decide)).trans w23_b0
  have w24_b4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K24.w32 (by decide) (by decide)).trans w23_b4
  have w24_b8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K24.w32 (by decide) (by decide)).trans w23_b8
  have w24_bc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K24.w32 (by decide) (by decide)).trans w23_bc
  have w24_c0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K24.w32 (by decide) (by decide)).trans w23_c0
  have w24_c4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K24.w32 (by decide) (by decide)).trans w23_c4
  have w24_c8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K24.w32 (by decide) (by decide)).trans w23_c8
  have w24_cc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K24.w32 (by decide) (by decide)).trans w23_cc
  have w24_d0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K24.w32 (by decide) (by decide)).trans w23_d0
  have w24_d4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K24.w32 (by decide) (by decide)).trans w23_d4
  have w24_d8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K24.w32 (by decide) (by decide)).trans w23_d8
  have w24_dc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K24.w32 (by decide) (by decide)).trans w23_dc
  have w24_e0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K24.w32 (by decide) (by decide)).trans w23_e0
  have w24_e4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K24.w32 (by decide) (by decide)).trans w23_e4
  have w24_e8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K24.w32 (by decide) (by decide)).trans w23_e8
  have w24_ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K24.w32 (by decide) (by decide)).trans w23_ec
  have w24_f0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K24.w32 (by decide) (by decide)).trans w23_f0
  have w24_f4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K24.w32 (by decide) (by decide)).trans w23_f4
  have w24_f8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K24.w32 (by decide) (by decide)).trans w23_f8
  have w24_fc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K24.w32 (by decide) (by decide)).trans w23_fc
  have w24_100 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K24.w32 (by decide) (by decide)).trans w23_100
  have w24_104 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K24.w32 (by decide) (by decide)).trans w23_104
  have w24_108 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K24.w32 (by decide) (by decide)).trans w23_108
  have w24_10c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K24.w32 (by decide) (by decide)).trans w23_10c
  have w24_110 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K24.w32 (by decide) (by decide)).trans w23_110
  have w24_114 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K24.w32 (by decide) (by decide)).trans w23_114
  have w24_118 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K24.w32 (by decide) (by decide)).trans w23_118
  have w24_11c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K24.w32 (by decide) (by decide)).trans w23_11c
  have w24_120 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K24.w32 (by decide) (by decide)).trans w23_120
  have w24_124 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K24.w32 (by decide) (by decide)).trans w23_124
  have w24_128 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K24.w32 (by decide) (by decide)).trans w23_128
  have w24_12c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K24.w32 (by decide) (by decide)).trans w23_12c
  have w24_130 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K24.w32 (by decide) (by decide)).trans w23_130
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K24.w32 (by decide) (by decide)).trans w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K24.w32 (by decide) (by decide)).trans w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 0x3FCC4850 := (K24.w32 (by decide) (by decide)).trans w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K24.w32 (by decide) (by decide)).trans w23_42c
  have w24_430 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 0x3FCC47D7 := (K24.w32 (by decide) (by decide)).trans w23_430
  have w24_434 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K24.w32 (by decide) (by decide)).trans w23_434
  have w24_438 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := (K24.w32 (by decide) (by decide)).trans w23_438
  have w24_43c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := (K24.w32 (by decide) (by decide)).trans w23_43c
  have w24_a20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 := (K24.w32 (by decide) (by decide)).trans w23_a20
  have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 := (K24.w32 (by decide) (by decide)).trans w23_a24
  have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c := (K24.w32 (by decide) (by decide)).trans w23_a28
  have w24_a2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 := (K24.w32 (by decide) (by decide)).trans w23_a2c
  have w24_a30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 := (K24.w32 (by decide) (by decide)).trans w23_a30
  have w24_a34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 := (K24.w32 (by decide) (by decide)).trans w23_a34
  have w24_a38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c := (K24.w32 (by decide) (by decide)).trans w23_a38
  have w24_a3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 := (K24.w32 (by decide) (by decide)).trans w23_a3c
  have w24_aa0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp := (K24.w32 (by decide) (by decide)).trans w23_aa0
  have w24_aa4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg := (K24.w32 (by decide) (by decide)).trans w23_aa4
  have w24_1380 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 := (K24.w32 (by decide) (by decide)).trans w23_1380
  have w24_14 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 (kp) (32))) 0 := by rw [W24, g23_10]
  have q24_320 : ∀ j, j < 31 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0) := fun j hj => (K24.range (by decide) (by decide) j hj).trans (q23_320 j hj)
  clear q23_320 w23_1380 w23_aa4 w23_aa0 w23_a3c w23_a38 w23_a34 w23_a30 w23_a2c w23_a28 w23_a24 w23_a20 w23_43c w23_438 w23_434 w23_430 w23_42c w23_428 w23_424 w23_420 w23_130 w23_12c w23_128 w23_124 w23_120 w23_11c w23_118 w23_114 w23_110 w23_10c w23_108 w23_104 w23_100 w23_fc w23_f8 w23_f4 w23_f0 w23_ec w23_e8 w23_e4 w23_e0 w23_dc w23_d8 w23_d4 w23_d0 w23_cc w23_c8 w23_c4 w23_c0 w23_bc w23_b8 w23_b4 w23_b0 w23_ac w23_a8 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 w23_20 w23_1c w23_18 w23_14 w23_10 w23_c w23_8 g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_19 g23_18 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  exact .inr ⟨n24, t24, s24, E24, V24, fR24, g24_2, g24_3, g24_4, g24_9, g24_18, g24_19, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, w24_8, w24_c, w24_10, w24_14, w24_18, w24_1c, w24_20, w24_24, w24_28, w24_2c, w24_30, w24_34, w24_38, w24_3c, w24_40, w24_44, w24_48, w24_4c, w24_50, w24_54, w24_58, w24_5c, w24_60, w24_64, w24_68, w24_6c, w24_70, w24_78, w24_7c, w24_80, w24_84, w24_88, w24_8c, w24_90, w24_94, w24_98, w24_9c, w24_a0, w24_a4, w24_a8, w24_ac, w24_b0, w24_b4, w24_b8, w24_bc, w24_c0, w24_c4, w24_c8, w24_cc, w24_d0, w24_d4, w24_d8, w24_dc, w24_e0, w24_e4, w24_e8, w24_ec, w24_f0, w24_f4, w24_f8, w24_fc, w24_100, w24_104, w24_108, w24_10c, w24_110, w24_114, w24_118, w24_11c, w24_120, w24_124, w24_128, w24_12c, w24_130, w24_420, w24_424, w24_428, w24_42c, w24_430, w24_434, w24_438, w24_43c, w24_a20, w24_a24, w24_a28, w24_a2c, w24_a30, w24_a34, w24_a38, w24_a3c, w24_aa0, w24_aa4, w24_1380, q24_320, keep_kk24.mono (by decide)⟩

end C3.RV32.Sv
