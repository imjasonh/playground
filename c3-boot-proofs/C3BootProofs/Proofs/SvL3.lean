import C3BootProofs.Proofs.SvCongr
import C3BootProofs.Image.BootloaderData3

/-!
# `sigstore::verify`: the serial number and the signature algorithm

From the serial number at 0x158 to 0x1CA: the serial number, a positive integer of at most 20 bytes, and the signature algorithm, which must be ecdsa-with-SHA384 with no parameters.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL3168 : List BInstr :=
  [.aluImm .add a1 x0 0x14]
theorem svL3168_end : blockEnd sigstoreVerifyCode 0x168 svL3168 = some 0x16A := by
  simp only [svL3168]
  rw [blockEnd, sv_at_168]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL316e : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x27C, .aluImm .add a2 x0 0x30]
theorem svL316e_end : blockEnd sigstoreVerifyCode 0x16E svL316e = some 0x176 := by
  simp only [svL316e]
  rw [blockEnd, sv_at_16e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_170]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_172]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL3188 : List BInstr :=
  [.aluImm .add a2 sp 0x400]
theorem svL3188_end : blockEnd sigstoreVerifyCode 0x188 svL3188 = some 0x18C := by
  simp only [svL3188]
  rw [blockEnd, sv_at_188]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL3198 : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x420]
theorem svL3198_end : blockEnd sigstoreVerifyCode 0x198 svL3198 = some 0x19E := by
  simp only [svL3198]
  rw [blockEnd, sv_at_198]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_19a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL31b0 : List BInstr :=
  [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0x738, .aluImm .add a3 x0 0x8]
theorem svL31b0_end : blockEnd sigstoreVerifyCode 0x1B0 svL31b0 = some 0x1BA := by
  simp only [svL31b0]
  rw [blockEnd, sv_at_1b0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_l3 {B out bp rootp dg lp ll rp rl tbp tbl sgp sgl sal sap : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x158 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x15)
    (g0_9 : reg n0 (9 : Fin 32) = tbp)
    (g0_10 : reg n0 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80)
    (g0_11 : reg n0 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_23 : reg n0 (23 : Fin 32) = sgp)
    (g0_25 : reg n0 (25 : Fin 32) = sgl)
    (g0_26 : reg n0 (26 : Fin 32) = lp)
    (g0_27 : reg n0 (27 : Fin 32) = tbl)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap)
    (w0_284 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = rp)
    (w0_288 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = rl)
    (tb_in : SvIn B (rp) (rl).toNat) :
    (¬ (∃ tl1, derElement 2 (memBytes M0 (rp) (rl).toNat) = .ok tl1 ∧ ∃ ip1 il1, derPosIntOf (memBytes M0 (rp) (rl).toNat) (rp) (.ok tl1) = .ok (ip1, il1) ∧ ((il1).toNat ≤ 20) ∧ ∃ tl8, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)).toNat) = .ok tl8 ∧ ∃ op21 ol21, derAlgOf M0 ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) (tl8.header + tl8.len) = .ok ((op21, ol21), none) ∧ (memBytes M0 op21 ol21 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcdsaSha384Address)) 8) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl1, derElement 2 (memBytes M0 (rp) (rl).toNat) = .ok tl1 ∧
    ∃ ip1 il1, derPosIntOf (memBytes M0 (rp) (rl).toNat) (rp) (.ok tl1) = .ok (ip1, il1) ∧
    ((il1).toNat ≤ 20) ∧
    ∃ tl8, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)).toNat) = .ok tl8 ∧
    ∃ op21 ol21, derAlgOf M0 ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) (tl8.header + tl8.len) = .ok ((op21, ol21), none) ∧
    (memBytes M0 op21 ol21 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcdsaSha384Address)) 8) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1CA (reg n') ∧
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
        reg n' (24 : Fin 32) = 0 ∧
        reg n' (25 : Fin 32) = sgl ∧
        reg n' (26 : Fin 32) = lp ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) ∧
        SvKeepL B n0.mem n'.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x158: sv_posF
  obtain ⟨n1, c1, s1, sp1, rk1, K1, A1, Ok1, Er1, fr1⟩ := sv_posF (oc := 0x80) (dc := 0x27C)
    F E0 s0 sv_at_158 sv_at_15c (by decide) (by decide) g0_2 g0_10 g0_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w0_284 w0_288 tb_in
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keepL K1 (by decide)
  rw [sv_mb fR0 tb_in] at A1 Ok1 Er1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rk1 sp (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk1 (3 : Fin 32) (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk1 (4 : Fin 32) (by decide) (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk1 (8 : Fin 32) (by decide) (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = tbp := by rw [rk1 (9 : Fin 32) (by decide) (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [rk1 (18 : Fin 32) (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [rk1 (19 : Fin 32) (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = dg := by rw [rk1 (20 : Fin 32) (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = rootp := by rw [rk1 (21 : Fin 32) (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = ll := by rw [rk1 (22 : Fin 32) (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = sgp := by rw [rk1 (23 : Fin 32) (by decide) (by decide), g0_23]
  have g1_25 : reg n1 (25 : Fin 32) = sgl := by rw [rk1 (25 : Fin 32) (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = lp := by rw [rk1 (26 : Fin 32) (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = tbl := by rw [rk1 (27 : Fin 32) (by decide) (by decide), g0_27]
  obtain ⟨r1, hr1⟩ : ∃ r, derElement 2 (memBytes M0 (rp) (rl).toNat) = r := ⟨_, rfl⟩
  rcases r1 with er1 | tl1
  · obtain ⟨zhr1, ezhr1⟩ := Er1 er1 (by rw [hr1]; rfl)
    have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x80, 0x8), (0x284, 0x8)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1
    have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K1.w32 (by decide) (by decide)).trans w0_78
    have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K1.w32 (by decide) (by decide)).trans w0_7c
    have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr1
    have b1_84 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er1 := ezhr1
    -- 0x160: lw
    obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_160 (off' := 0x162) (by decide)
      (by rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s2 : St n2.mem SV n2 0x162 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
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
    have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
    have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
    have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
    have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
    have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
    have g2_23 : reg n2 (23 : Fin 32) = sgp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
    have g2_25 : reg n2 (25 : Fin 32) = sgl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
    have g2_26 : reg n2 (26 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
    have g2_27 : reg n2 (27 : Fin 32) = tbl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
    have g2_10 : reg n2 a0 = 0 := by
      rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w1_80]
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m2]; exact keep_kk1
    clear keep_kk1
    have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m2]; exact w1_78
    have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m2]; exact w1_7c
    have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m2]; exact w1_80
    have b2_84 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er1 := by rw [m2]; exact b1_84
    clear b1_84 w1_80 w1_7c w1_78 ezhr1 zhr1
    -- 0x162: branch, taken
    obtain ⟨n3, d3, u3⟩ := s2.taken E2.self 0x7A0 sv_at_162
      (by decide) (by rw [g2_10, s2.zero]; rfl)
    have s3 : St n3.mem SV n3 0x7A0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u3.regs, g2_8]
    have g3_9 : reg n3 (9 : Fin 32) = tbp := by rw [u3.regs, g2_9]
    have g3_10 : reg n3 a0 = 0 := by rw [u3.regs, g2_10]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = sgp := by rw [u3.regs, g2_23]
    have g3_25 : reg n3 (25 : Fin 32) = sgl := by rw [u3.regs, g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [u3.regs, g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = tbl := by rw [u3.regs, g2_27]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m3]; exact w2_78
    have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m3]; exact w2_7c
    have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m3]; exact w2_80
    have b3_84 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er1 := by rw [m3]; exact b2_84
    clear b2_84 w2_80 w2_7c w2_78 g2_10 g2_27 g2_26 g2_25 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
    -- 0x7A0: lbu
    obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s4 : St n4.mem SV n4 0x7A4 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
    have g4_9 : reg n4 (9 : Fin 32) = tbp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
    have g4_10 : reg n4 a0 = 0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = sgp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
    have g4_25 : reg n4 (25 : Fin 32) = sgl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = tbl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
    have g4_8 : reg n4 (8 : Fin 32) = (derErrByte er1).zeroExtend 32 := by
      rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g3_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b3_84]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m4]; exact w3_78
    have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m4]; exact w3_7c
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m4]; exact w3_80
    have b4_84 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er1 := by rw [m4]; exact b3_84
    clear b3_84 w3_80 w3_7c w3_78 g3_27 g3_26 g3_25 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    exact .inl ⟨(fun ⟨tl1', h0', _⟩ => by rw [hr1] at h0'; cases h0'), sv_fail F E4 s4 t4 (fun x hx => (fR4 x hx).trans (fM x hx).symm) V4 hret g4_2 g4_18 hO g4_3 g4_4 (by rw [g4_8]; sv_code)⟩
  obtain ⟨r1b, hr1b⟩ : ∃ r, derPosIntOf (memBytes M0 (rp) (rl).toNat) (rp) (.ok tl1) = r := ⟨_, rfl⟩
  rcases r1b with er1b | ⟨ip1, il1⟩
  · obtain ⟨zhr1b, ezhr1b⟩ := Er1 er1b (by rw [hr1, hr1b])
    have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x80, 0x8), (0x284, 0x8)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1
    have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K1.w32 (by decide) (by decide)).trans w0_78
    have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K1.w32 (by decide) (by decide)).trans w0_7c
    have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr1b
    have b1_84 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er1b := ezhr1b
    -- 0x160: lw
    obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_160 (off' := 0x162) (by decide)
      (by rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s2 : St n2.mem SV n2 0x162 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
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
    have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
    have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
    have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
    have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
    have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
    have g2_23 : reg n2 (23 : Fin 32) = sgp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
    have g2_25 : reg n2 (25 : Fin 32) = sgl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
    have g2_26 : reg n2 (26 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
    have g2_27 : reg n2 (27 : Fin 32) = tbl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
    have g2_10 : reg n2 a0 = 0 := by
      rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w1_80]
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m2]; exact keep_kk1
    clear keep_kk1
    have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m2]; exact w1_78
    have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m2]; exact w1_7c
    have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m2]; exact w1_80
    have b2_84 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er1b := by rw [m2]; exact b1_84
    clear b1_84 w1_80 w1_7c w1_78 ezhr1b zhr1b
    -- 0x162: branch, taken
    obtain ⟨n3, d3, u3⟩ := s2.taken E2.self 0x7A0 sv_at_162
      (by decide) (by rw [g2_10, s2.zero]; rfl)
    have s3 : St n3.mem SV n3 0x7A0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u3.regs, g2_8]
    have g3_9 : reg n3 (9 : Fin 32) = tbp := by rw [u3.regs, g2_9]
    have g3_10 : reg n3 a0 = 0 := by rw [u3.regs, g2_10]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = sgp := by rw [u3.regs, g2_23]
    have g3_25 : reg n3 (25 : Fin 32) = sgl := by rw [u3.regs, g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [u3.regs, g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = tbl := by rw [u3.regs, g2_27]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m3]; exact w2_78
    have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m3]; exact w2_7c
    have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m3]; exact w2_80
    have b3_84 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er1b := by rw [m3]; exact b2_84
    clear b2_84 w2_80 w2_7c w2_78 g2_10 g2_27 g2_26 g2_25 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
    -- 0x7A0: lbu
    obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s4 : St n4.mem SV n4 0x7A4 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
    have g4_9 : reg n4 (9 : Fin 32) = tbp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
    have g4_10 : reg n4 a0 = 0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = sgp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
    have g4_25 : reg n4 (25 : Fin 32) = sgl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = tbl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
    have g4_8 : reg n4 (8 : Fin 32) = (derErrByte er1b).zeroExtend 32 := by
      rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g3_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b3_84]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m4]; exact w3_78
    have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m4]; exact w3_7c
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m4]; exact w3_80
    have b4_84 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er1b := by rw [m4]; exact b3_84
    clear b3_84 w3_80 w3_7c w3_78 g3_27 g3_26 g3_25 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    exact .inl ⟨(fun ⟨tl1', h0', ip1', il1', h1', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr1b] at h1'; cases h1'), sv_fail F E4 s4 t4 (fun x hx => (fR4 x hx).trans (fM x hx).symm) V4 hret g4_2 g4_18 hO g4_3 g4_4 (by rw [g4_8]; sv_code)⟩
  obtain ⟨p0_1, p4_1⟩ := Ok1 ip1 il1 (by rw [hr1, hr1b])
  obtain ⟨d8_1, d12_1⟩ := A1 tl1 hr1
  have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x80, 0x8), (0x284, 0x8)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K1.w32 (by decide) (by decide)).trans w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K1.w32 (by decide) (by decide)).trans w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ip1 := p0_1
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = il1 := p4_1
  have w1_284 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := d8_1
  have w1_288 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl1.header + tl1.len) := d12_1
  -- 0x160: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_160 (off' := 0x162) (by decide)
    (by rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0x162 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
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
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = sgp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
  have g2_25 : reg n2 (25 : Fin 32) = sgl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = tbl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_10 : reg n2 a0 = ip1 := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w1_80]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m2]; exact w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m2]; exact w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ip1 := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = il1 := by rw [m2]; exact w1_84
  have w2_284 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_284
  have w2_288 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_288
  clear w1_288 w1_284 w1_84 w1_80 w1_7c w1_78 d12_1 d8_1 p4_1 p0_1 g1_27 g1_26 g1_25 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 Er1 Ok1 A1 K1 rk1 sp1 s1 c1 g0_4 g0_3 fR0 t0
  -- 0x162: branch, not taken
  obtain ⟨n3, d3, u3⟩ := s2.notTaken E2.self 0x166 sv_at_162
    (by decide) (by rw [g2_10, s2.zero]; exact br_beq_f (tb_in.serial_ne hr1 hr1b))
  have s3 : St n3.mem SV n3 0x166 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u3.regs, g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = tbp := by rw [u3.regs, g2_9]
  have g3_10 : reg n3 a0 = ip1 := by rw [u3.regs, g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = sgp := by rw [u3.regs, g2_23]
  have g3_25 : reg n3 (25 : Fin 32) = sgl := by rw [u3.regs, g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [u3.regs, g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = tbl := by rw [u3.regs, g2_27]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m3]; exact w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ip1 := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = il1 := by rw [m3]; exact w2_84
  have w3_284 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_284
  have w3_288 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_288
  clear w2_288 w2_284 w2_84 w2_80 w2_7c w2_78 g2_10 g2_27 g2_26 g2_25 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x166: lw
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_166 (off' := 0x168) (by decide)
    (by rw [g3_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s4 : St n4.mem SV n4 0x168 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = tbp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = sgp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
  have g4_25 : reg n4 (25 : Fin 32) = sgl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = tbl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
  have g4_10 : reg n4 a0 = il1 := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w3_84]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m4]; exact w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m4]; exact w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ip1 := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = il1 := by rw [m4]; exact w3_84
  have w4_284 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_284
  have w4_288 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_288
  clear w3_288 w3_284 w3_84 w3_80 w3_7c w3_78 g3_27 g3_26 g3_25 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x168
  obtain ⟨n5, c5, u5⟩ := s4.block svL3168 E4.self svL3168_end
    ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x16A (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svL3168 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = tbp := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_10 : reg n5 a0 = il1 := by
    rw [rb5, runBlock_reg _ _ _ a0 s4.zero (by decide), g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = dg := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = rootp := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = ll := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = sgp := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_25 : reg n5 (25 : Fin 32) = sgl := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = lp := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = tbl := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_11 : reg n5 a1 = BitVec.ofNat 32 0x14 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL3168, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_10, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ip1 := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = il1 := by rw [m5]; exact w4_84
  have w5_284 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_284
  have w5_288 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_288
  clear w4_288 w4_284 w4_84 w4_80 w4_7c w4_78 g4_10 g4_27 g4_26 g4_25 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  by_cases hz_5 : (il1).toNat ≤ 20
  rotate_left
  · -- 0x16A: branch, taken
    obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0x7A4 sv_at_16a
      (by decide) (by rw [g5_10, g5_11]; exact br_bltu_t (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega))
    have s6 : St n6.mem SV n6 0x7A4 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
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
    have g6_10 : reg n6 a0 = il1 := by rw [u6.regs, g5_10]
    have g6_11 : reg n6 a1 = BitVec.ofNat 32 0x14 := by rw [u6.regs, g5_11]
    have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [u6.regs, g5_23]
    have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [u6.regs, g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = lp := by rw [u6.regs, g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [u6.regs, g5_27]
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m6]; exact w5_78
    have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m6]; exact w5_7c
    have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ip1 := by rw [m6]; exact w5_80
    have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = il1 := by rw [m6]; exact w5_84
    have w6_284 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_284
    have w6_288 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_288
    clear w5_288 w5_284 w5_84 w5_80 w5_7c w5_78 g5_11 g5_27 g5_26 g5_25 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
    exact .inl ⟨(fun ⟨tl1', h0', ip1', il1', h1', h2', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr1b] at h1'; cases h1'; exact hz_5 h2'), sv_fail F E6 s6 t6 (fun x hx => (fR6 x hx).trans (fM x hx).symm) V6 hret g6_2 g6_18 hO g6_3 g6_4 (by rw [g6_8]; sv_code)⟩
  -- 0x16A: branch, not taken
  obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0x16E sv_at_16a
    (by decide) (by rw [g5_10, g5_11]; exact br_bltu_f (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega))
  have s6 : St n6.mem SV n6 0x16E (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
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
  have g6_10 : reg n6 a0 = il1 := by rw [u6.regs, g5_10]
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 0x14 := by rw [u6.regs, g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [u6.regs, g5_23]
  have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [u6.regs, g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = lp := by rw [u6.regs, g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [u6.regs, g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ip1 := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = il1 := by rw [m6]; exact w5_84
  have w6_284 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_284
  have w6_288 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_288
  clear w5_288 w5_284 w5_84 w5_80 w5_7c w5_78 g5_11 g5_27 g5_26 g5_25 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x16E
  obtain ⟨n7, c7, u7⟩ := s6.block svL316e E6.self svL316e_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x176 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svL316e (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_25 : reg n7 (25 : Fin 32) = sgl := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = lp := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = tbl := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svL316e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_11, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g7_11 : reg n7 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svL316e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_11, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g7_12 : reg n7 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svL316e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_11, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x80, 0x8), (0x284, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m7]; exact w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m7]; exact w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ip1 := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = il1 := by rw [m7]; exact w6_84
  have w7_284 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_284
  have w7_288 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_288
  clear w6_288 w6_284 w6_84 w6_80 w6_7c w6_78 g6_27 g6_26 g6_25 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x176: sv_elemF
  obtain ⟨n8, c8, s8, rk8, K8, Ok8, Er8, fr8⟩ := sv_elemF (oc := 0x80) (dc := 0x27C) (tag := 0x30)
    F E7 s7 sv_at_176 sv_at_17a (by decide) (by decide) g7_10 g7_11 g7_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w7_284 w7_288
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keepL K8 (by decide)
  rw [sv_mb fR7 (tb_in.restW hr1)] at Ok8 Er8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rk8 sp (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk8 (3 : Fin 32) (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk8 (4 : Fin 32) (by decide) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk8 (8 : Fin 32) (by decide) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [rk8 (9 : Fin 32) (by decide) (by decide), g7_9]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [rk8 a0 (by decide) (by decide), g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rk8 (18 : Fin 32) (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rk8 (19 : Fin 32) (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [rk8 (20 : Fin 32) (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [rk8 (21 : Fin 32) (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [rk8 (22 : Fin 32) (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [rk8 (23 : Fin 32) (by decide) (by decide), g7_23]
  have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [rk8 (25 : Fin 32) (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = lp := by rw [rk8 (26 : Fin 32) (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [rk8 (27 : Fin 32) (by decide) (by decide), g7_27]
  obtain ⟨r8, hr8⟩ : ∃ r, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)).toNat) = r := ⟨_, rfl⟩
  rcases r8 with er8 | tl8
  · obtain ⟨zhr8, ezhr8⟩ := Er8 er8 hr8
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := keep_kk7.trans K8
    clear keep_kk7
    have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K8.w32 (by decide) (by decide)).trans w7_78
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K8.w32 (by decide) (by decide)).trans w7_7c
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr8
    have b8_84 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er8 := ezhr8
    clear w7_288 w7_284 w7_84 w7_80 w7_7c w7_78 g7_12 g7_11 g7_10 g7_27 g7_26 g7_25 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
    -- 0x17E: lw
    obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_17e (off' := 0x180) (by decide)
      (by rw [g8_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s9 : St n9.mem SV n9 0x180 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
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
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [u9.regs, upd_ne (by decide) (by decide), g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = sgp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
    have g9_25 : reg n9 (25 : Fin 32) = sgl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = lp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = tbl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
    have g9_10 : reg n9 a0 = 0 := by
      rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g8_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w8_80]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m9]; exact w8_78
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m9]; exact w8_7c
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m9]; exact w8_80
    have b9_84 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er8 := by rw [m9]; exact b8_84
    clear b8_84 w8_80 w8_7c w8_78 ezhr8 zhr8
    -- 0x180: branch, taken
    obtain ⟨n10, d10, u10⟩ := s9.taken E9.self 0x7A0 sv_at_180
      (by decide) (by rw [g9_10, s9.zero]; rfl)
    have s10 : St n10.mem SV n10 0x7A0 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u10.regs, g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = tbp := by rw [u10.regs, g9_9]
    have g10_10 : reg n10 a0 = 0 := by rw [u10.regs, g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = dg := by rw [u10.regs, g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = rootp := by rw [u10.regs, g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = ll := by rw [u10.regs, g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = sgp := by rw [u10.regs, g9_23]
    have g10_25 : reg n10 (25 : Fin 32) = sgl := by rw [u10.regs, g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = lp := by rw [u10.regs, g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = tbl := by rw [u10.regs, g9_27]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m10]; exact w9_78
    have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m10]; exact w9_7c
    have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m10]; exact w9_80
    have b10_84 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er8 := by rw [m10]; exact b9_84
    clear b9_84 w9_80 w9_7c w9_78 g9_10 g9_27 g9_26 g9_25 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
    -- 0x7A0: lbu
    obtain ⟨n11, d11, u11⟩ := s10.lbu E10.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s11 : St n11.mem SV n11 0x7A4 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
    have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
    have g11_10 : reg n11 a0 = 0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
    have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = lp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
    have g11_8 : reg n11 (8 : Fin 32) = (derErrByte er8).zeroExtend 32 := by
      rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g10_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b10_84]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m11]; exact w10_78
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m11]; exact w10_7c
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m11]; exact w10_80
    have b11_84 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er8 := by rw [m11]; exact b10_84
    clear b10_84 w10_80 w10_7c w10_78 g10_27 g10_26 g10_25 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    exact .inl ⟨(fun ⟨tl1', h0', ip1', il1', h1', h2', tl8', h3', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr1b] at h1'; cases h1'; rw [hr8] at h3'; cases h3'), sv_fail F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4 (by rw [g11_8]; sv_code)⟩
  obtain ⟨o0_8, o4_8, o8_8, o12_8, o16_8, d8_8, d12_8⟩ := Ok8 tl8 hr8
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := keep_kk7.trans K8
  clear keep_kk7
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K8.w32 (by decide) (by decide)).trans w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K8.w32 (by decide) (by decide)).trans w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := o0_8
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := o4_8
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := o8_8
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := o12_8
  have w8_284 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := d8_8
  have w8_288 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := d12_8
  have b8_90 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := o16_8
  clear w7_288 w7_284 w7_84 w7_80 w7_7c w7_78 g7_12 g7_11 g7_10 g7_27 g7_26 g7_25 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x17E: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_17e (off' := 0x180) (by decide)
    (by rw [g8_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x180 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
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
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [u9.regs, upd_ne (by decide) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = sgp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
  have g9_25 : reg n9 (25 : Fin 32) = sgl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = lp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = tbl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_10 : reg n9 a0 = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w8_80]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m9]; exact w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m9]; exact w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m9]; exact w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m9]; exact w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m9]; exact w8_8c
  have w9_284 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m9]; exact w8_284
  have w9_288 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m9]; exact w8_288
  have b9_90 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m9]; exact b8_90
  clear b8_90 w8_288 w8_284 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 d12_8 d8_8 o16_8 o12_8 o8_8 o4_8 o0_8 g8_27 g8_26 g8_25 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 Er8 Ok8 K8 rk8 s8 c8
  -- 0x180: branch, not taken
  obtain ⟨n10, d10, u10⟩ := s9.notTaken E9.self 0x184 sv_at_180
    (by decide) (by rw [g9_10, s9.zero]; exact br_beq_f ((tb_in.restW hr1).ok_ne hr8))
  have s10 : St n10.mem SV n10 0x184 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u10.regs, g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = tbp := by rw [u10.regs, g9_9]
  have g10_10 : reg n10 a0 = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [u10.regs, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = dg := by rw [u10.regs, g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = rootp := by rw [u10.regs, g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = ll := by rw [u10.regs, g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = sgp := by rw [u10.regs, g9_23]
  have g10_25 : reg n10 (25 : Fin 32) = sgl := by rw [u10.regs, g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = lp := by rw [u10.regs, g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = tbl := by rw [u10.regs, g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m10]; exact w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m10]; exact w9_8c
  have w10_284 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m10]; exact w9_284
  have w10_288 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m10]; exact w9_288
  have b10_90 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m10]; exact b9_90
  clear b9_90 w9_288 w9_284 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 g9_10 g9_27 g9_26 g9_25 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x184: lw
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_184 (off' := 0x186) (by decide)
    (by rw [g10_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s11 : St n11.mem SV n11 0x186 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
  have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = lp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_10 : reg n11 a0 = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w10_88]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m11]; exact w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m11]; exact w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m11]; exact w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m11]; exact w10_8c
  have w11_284 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m11]; exact w10_284
  have w11_288 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m11]; exact w10_288
  have b11_90 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m11]; exact b10_90
  clear b10_90 w10_288 w10_284 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 g10_27 g10_26 g10_25 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x186: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_186 (off' := 0x188) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x188 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_10 : reg n12 a0 = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = lp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_11 : reg n12 a1 = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr, w11_8c]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m12]; exact w11_8c
  have w12_284 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m12]; exact w11_284
  have w12_288 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m12]; exact w11_288
  have b12_90 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m12]; exact b11_90
  clear b11_90 w11_288 w11_284 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 g11_10 g11_27 g11_26 g11_25 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x188
  obtain ⟨n13, c13, u13⟩ := s12.block svL3188 E12.self svL3188_end
    ⟨trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x18C (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svL3188 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_10 : reg n13 a0 = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb13, runBlock_reg _ _ _ a0 s12.zero (by decide), g12_10]
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [rb13, runBlock_reg _ _ _ a1 s12.zero (by decide), g12_11]
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
  have g13_25 : reg n13 (25 : Fin 32) = sgl := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = lp := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = tbl := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_12 : reg n13 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svL3188, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_10, g12_11, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m13]; exact w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m13]; exact w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m13]; exact w12_8c
  have w13_284 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m13]; exact w12_284
  have w13_288 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m13]; exact w12_288
  have b13_90 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m13]; exact b12_90
  clear b12_90 w12_288 w12_284 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 g12_11 g12_27 g12_26 g12_25 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x18C: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_18c (off' := 0x18E) (c := 0x420)
    (by decide) (by rw [g13_12]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg14 (8 : Fin 32), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = tbp := by rw [rg14 (9 : Fin 32), g13_9]
  have g14_10 : reg n14 a0 = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg14 a1, g13_11]
  have g14_12 : reg n14 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg14 a2, g13_12]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = dg := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = rootp := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = ll := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = sgp := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_25 : reg n14 (25 : Fin 32) = sgl := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = lp := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = tbl := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K14.w32 (by decide) (by decide)).trans w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K14.w32 (by decide) (by decide)).trans w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := (K14.w32 (by decide) (by decide)).trans w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K14.w32 (by decide) (by decide)).trans w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K14.w32 (by decide) (by decide)).trans w13_8c
  have w14_284 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K14.w32 (by decide) (by decide)).trans w13_284
  have w14_288 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K14.w32 (by decide) (by decide)).trans w13_288
  have b14_90 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K14.b8 (by decide) (by decide)).trans b13_90
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [W14, g13_10]
  clear b13_90 w13_288 w13_284 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 g13_12 g13_27 g13_26 g13_25 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_11 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x18E: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_18e (off' := 0x190) (c := 0x424)
    (by decide) (by rw [g14_12]; sv_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg15 (8 : Fin 32), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = tbp := by rw [rg15 (9 : Fin 32), g14_9]
  have g15_10 : reg n15 a0 = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg15 a0, g14_10]
  have g15_11 : reg n15 a1 = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg15 a1, g14_11]
  have g15_12 : reg n15 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg15 a2, g14_12]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = dg := by rw [rg15 (20 : Fin 32), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = rootp := by rw [rg15 (21 : Fin 32), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = ll := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = sgp := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_25 : reg n15 (25 : Fin 32) = sgl := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = lp := by rw [rg15 (26 : Fin 32), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = tbl := by rw [rg15 (27 : Fin 32), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K15.w32 (by decide) (by decide)).trans w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K15.w32 (by decide) (by decide)).trans w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K15.w32 (by decide) (by decide)).trans w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := (K15.w32 (by decide) (by decide)).trans w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K15.w32 (by decide) (by decide)).trans w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K15.w32 (by decide) (by decide)).trans w14_8c
  have w15_284 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K15.w32 (by decide) (by decide)).trans w14_284
  have w15_288 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K15.w32 (by decide) (by decide)).trans w14_288
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K15.w32 (by decide) (by decide)).trans w14_420
  have b15_90 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K15.b8 (by decide) (by decide)).trans b14_90
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [W15, g14_11]
  clear w14_420 b14_90 w14_288 w14_284 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 g14_27 g14_26 g14_25 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_12 g14_11 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0x190: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_190 (off' := 0x192) (c := 0x74)
    (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg16 (8 : Fin 32), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = tbp := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_10 : reg n16 a0 = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg16 a0, g15_10]
  have g16_11 : reg n16 a1 = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg16 a1, g15_11]
  have g16_12 : reg n16 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg16 a2, g15_12]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [rg16 (20 : Fin 32), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [rg16 (22 : Fin 32), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = sgp := by rw [rg16 (23 : Fin 32), g15_23]
  have g16_25 : reg n16 (25 : Fin 32) = sgl := by rw [rg16 (25 : Fin 32), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = lp := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = tbl := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K16.w32 (by decide) (by decide)).trans w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := (K16.w32 (by decide) (by decide)).trans w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_8c
  have w16_284 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_284
  have w16_288 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_288
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_424
  have b16_90 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K16.b8 (by decide) (by decide)).trans b15_90
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [W16, g15_10]
  clear w15_424 b15_90 w15_420 w15_288 w15_284 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 g15_27 g15_26 g15_25 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_12 g15_11 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0x192: sw
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sw F E16 s16 sv_at_192 (off' := 0x194) (c := 0x428)
    (by decide) (by rw [g16_12]; sv_addr) (by decide) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg17 (8 : Fin 32), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = tbp := by rw [rg17 (9 : Fin 32), g16_9]
  have g17_10 : reg n17 a0 = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg17 a0, g16_10]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg17 a1, g16_11]
  have g17_12 : reg n17 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg17 a2, g16_12]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rg17 (18 : Fin 32), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rg17 (19 : Fin 32), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [rg17 (20 : Fin 32), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [rg17 (21 : Fin 32), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [rg17 (22 : Fin 32), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = sgp := by rw [rg17 (23 : Fin 32), g16_23]
  have g17_25 : reg n17 (25 : Fin 32) = sgl := by rw [rg17 (25 : Fin 32), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = lp := by rw [rg17 (26 : Fin 32), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = tbl := by rw [rg17 (27 : Fin 32), g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K17.w32 (by decide) (by decide)).trans w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K17.w32 (by decide) (by decide)).trans w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K17.w32 (by decide) (by decide)).trans w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K17.w32 (by decide) (by decide)).trans w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := (K17.w32 (by decide) (by decide)).trans w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K17.w32 (by decide) (by decide)).trans w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K17.w32 (by decide) (by decide)).trans w16_8c
  have w17_284 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K17.w32 (by decide) (by decide)).trans w16_284
  have w17_288 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K17.w32 (by decide) (by decide)).trans w16_288
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K17.w32 (by decide) (by decide)).trans w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K17.w32 (by decide) (by decide)).trans w16_424
  have b17_90 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K17.b8 (by decide) (by decide)).trans b16_90
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [W17, g16_10]
  clear w16_74 b16_90 w16_424 w16_420 w16_288 w16_284 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 g16_27 g16_26 g16_25 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_12 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x194: sw
  obtain ⟨n18, d18, s18, fr18, K18, W18, rg18⟩ := sv_sw F E17 s17 sv_at_194 (off' := 0x196) (c := 0x70)
    (by decide) (by rw [g17_2]; sv_addr) (by decide) (by decide)
  have t18 : Steps n0 n18 := t17.trans d18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rg18 sp, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg18 (3 : Fin 32), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg18 (4 : Fin 32), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg18 (8 : Fin 32), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = tbp := by rw [rg18 (9 : Fin 32), g17_9]
  have g18_10 : reg n18 a0 = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg18 a0, g17_10]
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg18 a1, g17_11]
  have g18_12 : reg n18 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg18 a2, g17_12]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rg18 (18 : Fin 32), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rg18 (19 : Fin 32), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [rg18 (20 : Fin 32), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [rg18 (21 : Fin 32), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [rg18 (22 : Fin 32), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = sgp := by rw [rg18 (23 : Fin 32), g17_23]
  have g18_25 : reg n18 (25 : Fin 32) = sgl := by rw [rg18 (25 : Fin 32), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = lp := by rw [rg18 (26 : Fin 32), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = tbl := by rw [rg18 (27 : Fin 32), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K18.w32 (by decide) (by decide)).trans w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K18.w32 (by decide) (by decide)).trans w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K18.w32 (by decide) (by decide)).trans w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K18.w32 (by decide) (by decide)).trans w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := (K18.w32 (by decide) (by decide)).trans w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K18.w32 (by decide) (by decide)).trans w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K18.w32 (by decide) (by decide)).trans w17_8c
  have w18_284 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K18.w32 (by decide) (by decide)).trans w17_284
  have w18_288 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K18.w32 (by decide) (by decide)).trans w17_288
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K18.w32 (by decide) (by decide)).trans w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K18.w32 (by decide) (by decide)).trans w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K18.w32 (by decide) (by decide)).trans w17_428
  have b18_90 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K18.b8 (by decide) (by decide)).trans b17_90
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [W18, g17_11]
  clear w17_428 b17_90 w17_424 w17_420 w17_288 w17_284 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 g17_27 g17_26 g17_25 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_12 g17_11 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0x196: sw
  obtain ⟨n19, d19, s19, fr19, K19, W19, rg19⟩ := sv_sw F E18 s18 sv_at_196 (off' := 0x198) (c := 0x42C)
    (by decide) (by rw [g18_12]; sv_addr) (by decide) (by decide)
  have t19 : Steps n0 n19 := t18.trans d19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rg19 sp, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg19 (3 : Fin 32), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg19 (4 : Fin 32), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg19 (8 : Fin 32), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = tbp := by rw [rg19 (9 : Fin 32), g18_9]
  have g19_10 : reg n19 a0 = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg19 a0, g18_10]
  have g19_11 : reg n19 a1 = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg19 a1, g18_11]
  have g19_12 : reg n19 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg19 a2, g18_12]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rg19 (18 : Fin 32), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rg19 (19 : Fin 32), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [rg19 (20 : Fin 32), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [rg19 (21 : Fin 32), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [rg19 (22 : Fin 32), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = sgp := by rw [rg19 (23 : Fin 32), g18_23]
  have g19_25 : reg n19 (25 : Fin 32) = sgl := by rw [rg19 (25 : Fin 32), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = lp := by rw [rg19 (26 : Fin 32), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = tbl := by rw [rg19 (27 : Fin 32), g18_27]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4)] := keep_kk18.trans K19.toL
  clear keep_kk18
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K19.w32 (by decide) (by decide)).trans w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K19.w32 (by decide) (by decide)).trans w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K19.w32 (by decide) (by decide)).trans w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K19.w32 (by decide) (by decide)).trans w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K19.w32 (by decide) (by decide)).trans w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := (K19.w32 (by decide) (by decide)).trans w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K19.w32 (by decide) (by decide)).trans w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K19.w32 (by decide) (by decide)).trans w18_8c
  have w19_284 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K19.w32 (by decide) (by decide)).trans w18_284
  have w19_288 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K19.w32 (by decide) (by decide)).trans w18_288
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K19.w32 (by decide) (by decide)).trans w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K19.w32 (by decide) (by decide)).trans w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K19.w32 (by decide) (by decide)).trans w18_428
  have b19_90 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := (K19.b8 (by decide) (by decide)).trans b18_90
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [W19, g18_11]
  clear w18_70 b18_90 w18_428 w18_424 w18_420 w18_288 w18_284 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 g18_27 g18_26 g18_25 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_12 g18_11 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
  -- 0x198
  obtain ⟨n20, c20, u20⟩ := s19.block svL3198 E19.self svL3198_end
    ⟨trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x19E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svL3198 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = tbp := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_12 : reg n20 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb20, runBlock_reg _ _ _ a2 s19.zero (by decide), g19_12]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = dg := by
    rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = rootp := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = ll := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = sgp := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_25 : reg n20 (25 : Fin 32) = sgl := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = lp := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = tbl := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svL3198, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_11, g19_12, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_11 : reg n20 a1 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svL3198, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_11, g19_12, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m20]; exact w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m20]; exact w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m20]; exact w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl8.len := by rw [m20]; exact w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m20]; exact w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_8c
  have w20_284 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_284
  have w20_288 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_288
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_42c
  have b20_90 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl8.tag := by rw [m20]; exact b19_90
  clear w19_42c b19_90 w19_428 w19_424 w19_420 w19_288 w19_284 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 g19_27 g19_26 g19_25 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_12 g19_11 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 rg19 W19 K19 fr19 s19 d19
  -- 0x19E: sv_algF
  obtain ⟨n21, c21, s21, sp21, rk21, K21, A21, R21, fr21⟩ := sv_algF (oc := 0x80) (dc := 0x420) (nl := tl8.header + tl8.len)
    F E20 s20 sv_at_19e sv_at_1a2 (by decide) (by decide) g20_2 g20_10 g20_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w20_428 w20_42c ((tb_in.restW hr1).rawN hr8)
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keepL K21 (by decide)
  rw [derAlgOf_congr (sv_pt fR20 ((tb_in.restW hr1).rawN hr8))] at R21
  rw [sv_mb fR20 ((tb_in.restW hr1).rawN hr8)] at A21
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk21 (3 : Fin 32) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk21 (4 : Fin 32) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk21 (8 : Fin 32) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = tbp := by rw [rk21 (9 : Fin 32) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rk21 (18 : Fin 32) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rk21 (19 : Fin 32) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [rk21 (20 : Fin 32) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [rk21 (21 : Fin 32) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [rk21 (22 : Fin 32) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = sgp := by rw [rk21 (23 : Fin 32) (by decide), g20_23]
  have g21_25 : reg n21 (25 : Fin 32) = sgl := by rw [rk21 (25 : Fin 32) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = lp := by rw [rk21 (26 : Fin 32) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = tbl := by rw [rk21 (27 : Fin 32) (by decide), g20_27]
  have g21_2 : reg n21 sp = B + 0x21A0 := sp21
  obtain ⟨r21, hr21⟩ : ∃ r, derAlgOf M0 ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) (tl8.header + tl8.len) = r := ⟨_, rfl⟩
  rcases r21 with ab21 | ⟨⟨op21, ol21⟩, _ | ⟨prp21, pu21⟩⟩
  · rw [hr21] at R21
    obtain ⟨y0_21, y1_21⟩ := R21
    obtain ⟨ec_21, ey_21, hz_c21⟩ : ∃ b : BitVec 8, n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = b ∧ b.toNat < 0x27 :=
      ⟨_, y1_21, by sv_eb hr21⟩
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := keep_kk20.trans K21
    clear keep_kk20
    have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_70
    have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K21.w32 (by decide) (by decide)).trans w20_74
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K21.w32 (by decide) (by decide)).trans w20_78
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K21.w32 (by decide) (by decide)).trans w20_7c
    have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_284
    have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_288
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K21.w32 (by decide) (by decide)).trans w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_424
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := y0_21
    have b21_84 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ec_21 := ey_21
    clear b20_90 w20_42c w20_428 w20_424 w20_420 w20_288 w20_284 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 g20_11 g20_10 g20_27 g20_26 g20_25 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_12 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    -- 0x1A6: lw
    obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_1a6 (off' := 0x1A8) (by decide)
      (by rw [g21_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s22 : St n22.mem SV n22 0x1A8 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
    have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = lp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
    have g22_10 : reg n22 a0 = 0 := by
      rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g21_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w21_80]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_70
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m22]; exact w21_74
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m22]; exact w21_78
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m22]; exact w21_7c
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m22]; exact w21_80
    have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_284
    have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_288
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m22]; exact w21_420
    have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_424
    have b22_84 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ec_21 := by rw [m22]; exact b21_84
    clear b21_84 w21_80 w21_424 w21_420 w21_288 w21_284 w21_7c w21_78 w21_74 w21_70 ey_21 y1_21 y0_21
    -- 0x1A8: branch, taken
    obtain ⟨n23, d23, u23⟩ := s22.taken E22.self 0x7A0 sv_at_1a8
      (by decide) (by rw [g22_10, s22.zero]; rfl)
    have s23 : St n23.mem SV n23 0x7A0 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, g22_4]
    have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u23.regs, g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [u23.regs, g22_9]
    have g23_10 : reg n23 a0 = 0 := by rw [u23.regs, g22_10]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [u23.regs, g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [u23.regs, g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [u23.regs, g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [u23.regs, g22_23]
    have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [u23.regs, g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = lp := by rw [u23.regs, g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [u23.regs, g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_70
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m23]; exact w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m23]; exact w22_78
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m23]; exact w22_7c
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m23]; exact w22_80
    have w23_284 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_284
    have w23_288 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_288
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m23]; exact w22_420
    have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_424
    have b23_84 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ec_21 := by rw [m23]; exact b22_84
    clear b22_84 w22_424 w22_420 w22_288 w22_284 w22_80 w22_7c w22_78 w22_74 w22_70 g22_10 g22_27 g22_26 g22_25 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0x7A0: lbu
    obtain ⟨n24, d24, u24⟩ := s23.lbu E23.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s24 : St n24.mem SV n24 0x7A4 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
    have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_9]
    have g24_10 : reg n24 a0 = 0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_10]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
    have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = lp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
    have g24_8 : reg n24 (8 : Fin 32) = (ec_21).zeroExtend 32 := by
      rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g23_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b23_84]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_70
    have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m24]; exact w23_74
    have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m24]; exact w23_78
    have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m24]; exact w23_7c
    have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m24]; exact w23_80
    have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_284
    have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_288
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m24]; exact w23_420
    have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_424
    have b24_84 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ec_21 := by rw [m24]; exact b23_84
    clear b23_84 w23_424 w23_420 w23_288 w23_284 w23_80 w23_7c w23_78 w23_74 w23_70 g23_27 g23_26 g23_25 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
    exact .inl ⟨(fun ⟨tl1', h0', ip1', il1', h1', h2', tl8', h3', op21', ol21', h4', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr1b] at h1'; cases h1'; rw [hr8] at h3'; cases h3'; rw [hr21] at h4'; cases h4'), sv_fail F E24 s24 t24 (fun x hx => (fR24 x hx).trans (fM x hx).symm) V24 hret g24_2 g24_18 hO g24_3 g24_4 (by rw [g24_8]; sv_code)⟩
  rotate_left
  · rw [hr21] at R21
    obtain ⟨y0_21, y4_21, y8_21, -, -⟩ := R21
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := keep_kk20.trans K21
    clear keep_kk20
    have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_70
    have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K21.w32 (by decide) (by decide)).trans w20_74
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K21.w32 (by decide) (by decide)).trans w20_78
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K21.w32 (by decide) (by decide)).trans w20_7c
    have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_284
    have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_288
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K21.w32 (by decide) (by decide)).trans w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_424
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := y0_21
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := y4_21
    have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := y8_21
    clear b20_90 w20_42c w20_428 w20_424 w20_420 w20_288 w20_284 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 g20_11 g20_10 g20_27 g20_26 g20_25 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_12 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    -- 0x1A6: lw
    obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_1a6 (off' := 0x1A8) (by decide)
      (by rw [g21_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s22 : St n22.mem SV n22 0x1A8 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
    have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = lp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
    have g22_10 : reg n22 a0 = op21 := by
      rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g21_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w21_80]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_70
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m22]; exact w21_74
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m22]; exact w21_78
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m22]; exact w21_7c
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m22]; exact w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m22]; exact w21_84
    have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := by rw [m22]; exact w21_88
    have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_284
    have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_288
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m22]; exact w21_420
    have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_424
    clear w21_88 w21_84 w21_80 w21_424 w21_420 w21_288 w21_284 w21_7c w21_78 w21_74 w21_70 y8_21 y4_21 y0_21
    -- 0x1A8: branch, not taken
    obtain ⟨n23, d23, u23⟩ := s22.notTaken E22.self 0x1AC sv_at_1a8
      (by decide) (by rw [g22_10, s22.zero]; exact br_beq_f (((tb_in.restW hr1).rawN hr8).algOid hr21).pos_ne)
    have s23 : St n23.mem SV n23 0x1AC (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, g22_4]
    have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u23.regs, g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [u23.regs, g22_9]
    have g23_10 : reg n23 a0 = op21 := by rw [u23.regs, g22_10]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [u23.regs, g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [u23.regs, g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [u23.regs, g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [u23.regs, g22_23]
    have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [u23.regs, g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = lp := by rw [u23.regs, g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [u23.regs, g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_70
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m23]; exact w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m23]; exact w22_78
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m23]; exact w22_7c
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m23]; exact w22_80
    have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m23]; exact w22_84
    have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := by rw [m23]; exact w22_88
    have w23_284 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_284
    have w23_288 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_288
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m23]; exact w22_420
    have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_424
    clear w22_424 w22_420 w22_288 w22_284 w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 g22_10 g22_27 g22_26 g22_25 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0x1AC: lw
    obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_1ac (off' := 0x1AE) (by decide)
      (by rw [g23_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s24 : St n24.mem SV n24 0x1AE (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
    have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_8]
    have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_9]
    have g24_10 : reg n24 a0 = op21 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_10]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
    have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = lp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
    have g24_11 : reg n24 a1 = BitVec.ofNat 32 ol21 := by
      rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g23_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w23_84]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_70
    have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m24]; exact w23_74
    have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m24]; exact w23_78
    have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m24]; exact w23_7c
    have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m24]; exact w23_80
    have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m24]; exact w23_84
    have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := by rw [m24]; exact w23_88
    have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_284
    have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_288
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m24]; exact w23_420
    have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_424
    clear w23_424 w23_420 w23_288 w23_284 w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 g23_27 g23_26 g23_25 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
    -- 0x1AE: lw
    obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_1ae (off' := 0x1B0) (by decide)
      (by rw [g24_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s25 : St n25.mem SV n25 0x1B0 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
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
    have g25_10 : reg n25 a0 = op21 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_10]
    have g25_11 : reg n25 a1 = BitVec.ofNat 32 ol21 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_11]
    have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
    have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
    have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
    have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
    have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
    have g25_23 : reg n25 (23 : Fin 32) = sgp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
    have g25_25 : reg n25 (25 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
    have g25_26 : reg n25 (26 : Fin 32) = lp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = tbl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
    have g25_24 : reg n25 (24 : Fin 32) = prp21 + BitVec.ofNat 32 pu21.header := by
      rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g24_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w24_88]
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m25]; exact keep_kk24
    clear keep_kk24
    have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m25]; exact w24_70
    have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m25]; exact w24_74
    have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m25]; exact w24_78
    have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m25]; exact w24_7c
    have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m25]; exact w24_80
    have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m25]; exact w24_84
    have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := by rw [m25]; exact w24_88
    have w25_284 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m25]; exact w24_284
    have w25_288 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m25]; exact w24_288
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m25]; exact w24_420
    have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m25]; exact w24_424
    clear w24_424 w24_420 w24_288 w24_284 w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 g24_11 g24_27 g24_26 g24_25 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
    -- 0x1B0
    obtain ⟨n26, c26, u26⟩ := s25.block svL31b0 E25.self svL31b0_end
      ⟨trivial, trivial, trivial, trivial⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have s26 : St n26.mem SV n26 0x1BA (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have rb26 : ∀ q, reg n26 q = (runBlock svL31b0 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
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
    have g26_10 : reg n26 a0 = op21 := by
      rw [rb26, runBlock_reg _ _ _ a0 s25.zero (by decide), g25_10]
    have g26_11 : reg n26 a1 = BitVec.ofNat 32 ol21 := by
      rw [rb26, runBlock_reg _ _ _ a1 s25.zero (by decide), g25_11]
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
    have g26_24 : reg n26 (24 : Fin 32) = prp21 + BitVec.ofNat 32 pu21.header := by
      rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = sgl := by
      rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = lp := by
      rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = tbl := by
      rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
    have g26_12 : reg n26 a2 = BitVec.ofNat 32 (img% svOidEcdsaSha384Address) := by
      rw [rb26]; simp +decide only [runBlock, BInstr.run, svL31b0, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g26_13 : reg n26 a3 = BitVec.ofNat 32 0x8 := by
      rw [rb26]; simp +decide only [runBlock, BInstr.run, svL31b0, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m26]; exact w25_70
    have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m26]; exact w25_74
    have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m26]; exact w25_78
    have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m26]; exact w25_7c
    have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m26]; exact w25_80
    have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m26]; exact w25_84
    have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := by rw [m26]; exact w25_88
    have w26_284 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m26]; exact w25_284
    have w26_288 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m26]; exact w25_288
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m26]; exact w25_420
    have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m26]; exact w25_424
    clear w25_424 w25_420 w25_288 w25_284 w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 g25_24 g25_27 g25_26 g25_25 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_11 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
    -- 0x1BA: sv_sneF
    obtain ⟨n27, c27, s27, rk27, a0_27, K27, fr27⟩ := sv_sneF (pl := ol21) (ql := 8)
      F E26 s26 sv_at_1ba sv_at_1be (by decide) (by decide) g26_2
      g26_10 g26_11 g26_12 g26_13 (.inl (((tb_in.restW hr1).rawN hr8).algOid hr21)) (.inr ⟨by decide, by decide⟩)
    have t27 : Steps n0 n27 := t26.trans c27
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.keepL K27 (by decide)
    rw [sv_mbRo FW fR26 (.inl (((tb_in.restW hr1).rawN hr8).algOid hr21)), sv_mbRo FW fR26 (.inr ⟨by decide, by decide⟩)] at a0_27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rk27 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk27 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk27 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk27 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = tbp := by rw [rk27 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_9]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rk27 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rk27 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = dg := by rw [rk27 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = rootp := by rw [rk27 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = ll := by rw [rk27 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = sgp := by rw [rk27 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = prp21 + BitVec.ofNat 32 pu21.header := by rw [rk27 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = sgl := by rw [rk27 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = lp := by rw [rk27 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = tbl := by rw [rk27 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_27]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := keep_kk26.trans K27
    clear keep_kk26
    have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K27.w32 (by decide) (by decide)).trans w26_70
    have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K27.w32 (by decide) (by decide)).trans w26_74
    have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K27.w32 (by decide) (by decide)).trans w26_78
    have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K27.w32 (by decide) (by decide)).trans w26_7c
    have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := (K27.w32 (by decide) (by decide)).trans w26_80
    have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := (K27.w32 (by decide) (by decide)).trans w26_84
    have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := (K27.w32 (by decide) (by decide)).trans w26_88
    have w27_284 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K27.w32 (by decide) (by decide)).trans w26_284
    have w27_288 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K27.w32 (by decide) (by decide)).trans w26_288
    have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K27.w32 (by decide) (by decide)).trans w26_420
    have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K27.w32 (by decide) (by decide)).trans w26_424
    clear w26_424 w26_420 w26_288 w26_284 w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 g26_13 g26_12 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
    by_cases ho_27 : memBytes M0 op21 ol21 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcdsaSha384Address)) 8
    · have g27_10 : reg n27 a0 = BitVec.ofNat 32 0 := by rw [a0_27, ite_eq_left ho_27]; rfl
      -- 0x1C2: branch, not taken
      obtain ⟨n28, d28, u28⟩ := s27.notTaken E27.self 0x1C6 sv_at_1c2
        (by decide) (by rw [g27_10, s27.zero]; decide)
      have s28 : St n28.mem SV n28 0x1C6 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
      have m28 : n28.mem = n27.mem := u28.mem
      have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
      have t28 : Steps n0 n28 := t27.trans (.single d28)
      have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
      have E28 : SvCode n28.mem := E27.fr F fr28
      have V28 : SvSaves B n28.mem v := V27.same m28
      have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
      have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
      have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
      have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u28.regs, g27_8]
      have g28_9 : reg n28 (9 : Fin 32) = tbp := by rw [u28.regs, g27_9]
      have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x0 := by rw [u28.regs, g27_10]
      have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
      have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
      have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [u28.regs, g27_20]
      have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [u28.regs, g27_21]
      have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [u28.regs, g27_22]
      have g28_23 : reg n28 (23 : Fin 32) = sgp := by rw [u28.regs, g27_23]
      have g28_24 : reg n28 (24 : Fin 32) = prp21 + BitVec.ofNat 32 pu21.header := by rw [u28.regs, g27_24]
      have g28_25 : reg n28 (25 : Fin 32) = sgl := by rw [u28.regs, g27_25]
      have g28_26 : reg n28 (26 : Fin 32) = lp := by rw [u28.regs, g27_26]
      have g28_27 : reg n28 (27 : Fin 32) = tbl := by rw [u28.regs, g27_27]
      have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m28]; exact keep_kk27
      clear keep_kk27
      have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_70
      have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m28]; exact w27_74
      have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m28]; exact w27_78
      have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m28]; exact w27_7c
      have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m28]; exact w27_80
      have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m28]; exact w27_84
      have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := by rw [m28]; exact w27_88
      have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_284
      have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_288
      have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m28]; exact w27_420
      have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_424
      clear w27_424 w27_420 w27_288 w27_284 w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 K27 a0_27 rk27 s27 c27
      -- 0x1C6: branch, taken
      obtain ⟨n29, d29, u29⟩ := s28.taken E28.self 0x7A4 sv_at_1c6
        (by decide) (by rw [g28_24, s28.zero]; exact br_bne_t (((tb_in.restW hr1).rawN hr8).algParams hr21))
      have s29 : St n29.mem SV n29 0x7A4 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
      have m29 : n29.mem = n28.mem := u29.mem
      have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
      have t29 : Steps n0 n29 := t28.trans (.single d29)
      have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
      have E29 : SvCode n29.mem := E28.fr F fr29
      have V29 : SvSaves B n29.mem v := V28.same m29
      have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
      have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
      have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
      have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u29.regs, g28_8]
      have g29_9 : reg n29 (9 : Fin 32) = tbp := by rw [u29.regs, g28_9]
      have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_10]
      have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
      have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
      have g29_20 : reg n29 (20 : Fin 32) = dg := by rw [u29.regs, g28_20]
      have g29_21 : reg n29 (21 : Fin 32) = rootp := by rw [u29.regs, g28_21]
      have g29_22 : reg n29 (22 : Fin 32) = ll := by rw [u29.regs, g28_22]
      have g29_23 : reg n29 (23 : Fin 32) = sgp := by rw [u29.regs, g28_23]
      have g29_24 : reg n29 (24 : Fin 32) = prp21 + BitVec.ofNat 32 pu21.header := by rw [u29.regs, g28_24]
      have g29_25 : reg n29 (25 : Fin 32) = sgl := by rw [u29.regs, g28_25]
      have g29_26 : reg n29 (26 : Fin 32) = lp := by rw [u29.regs, g28_26]
      have g29_27 : reg n29 (27 : Fin 32) = tbl := by rw [u29.regs, g28_27]
      have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m29]; exact keep_kk28
      clear keep_kk28
      have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_70
      have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m29]; exact w28_74
      have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m29]; exact w28_78
      have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m29]; exact w28_7c
      have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m29]; exact w28_80
      have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m29]; exact w28_84
      have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := by rw [m29]; exact w28_88
      have w29_284 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_284
      have w29_288 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_288
      have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m29]; exact w28_420
      have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_424
      clear w28_424 w28_420 w28_288 w28_284 w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28 g27_10
      exact .inl ⟨(fun ⟨tl1', h0', ip1', il1', h1', h2', tl8', h3', op21', ol21', h4', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr1b] at h1'; cases h1'; rw [hr8] at h3'; cases h3'; rw [hr21] at h4'; cases h4'), sv_fail F E29 s29 t29 (fun x hx => (fR29 x hx).trans (fM x hx).symm) V29 hret g29_2 g29_18 hO g29_3 g29_4 (by rw [g29_8]; sv_code)⟩
    have g27_10 : reg n27 a0 = BitVec.ofNat 32 1 := by rw [a0_27, ite_eq_right ho_27]; rfl
    -- 0x1C2: branch, taken
    obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x7A4 sv_at_1c2
      (by decide) (by rw [g27_10, s27.zero]; decide)
    have s28 : St n28.mem SV n28 0x7A4 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u28.regs, g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = tbp := by rw [u28.regs, g27_9]
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [u28.regs, g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = sgp := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = prp21 + BitVec.ofNat 32 pu21.header := by rw [u28.regs, g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = sgl := by rw [u28.regs, g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = lp := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = tbl := by rw [u28.regs, g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_70
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m28]; exact w27_74
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m28]; exact w27_78
    have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m28]; exact w27_7c
    have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m28]; exact w27_80
    have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m28]; exact w27_84
    have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp21 + BitVec.ofNat 32 pu21.header := by rw [m28]; exact w27_88
    have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_284
    have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_288
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m28]; exact w27_420
    have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_424
    clear w27_424 w27_420 w27_288 w27_284 w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 K27 a0_27 rk27 s27 c27
    exact .inl ⟨(fun ⟨tl1', h0', ip1', il1', h1', h2', tl8', h3', op21', ol21', h4', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr1b] at h1'; cases h1'; rw [hr8] at h3'; cases h3'; rw [hr21] at h4'; cases h4'), sv_fail F E28 s28 t28 (fun x hx => (fR28 x hx).trans (fM x hx).symm) V28 hret g28_2 g28_18 hO g28_3 g28_4 (by rw [g28_8]; sv_code)⟩
  rw [hr21] at R21
  obtain ⟨y0_21, y4_21, y8_21⟩ := R21
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := keep_kk20.trans K21
  clear keep_kk20
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K21.w32 (by decide) (by decide)).trans w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K21.w32 (by decide) (by decide)).trans w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K21.w32 (by decide) (by decide)).trans w20_7c
  have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_284
  have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_288
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K21.w32 (by decide) (by decide)).trans w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K21.w32 (by decide) (by decide)).trans w20_424
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := y0_21
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := y4_21
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := y8_21
  clear b20_90 w20_42c w20_428 w20_424 w20_420 w20_288 w20_284 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 g20_11 g20_10 g20_27 g20_26 g20_25 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_12 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x1A6: lw
  obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_1a6 (off' := 0x1A8) (by decide)
    (by rw [g21_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s22 : St n22.mem SV n22 0x1A8 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
  have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = lp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
  have g22_10 : reg n22 a0 = op21 := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w21_80]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m22]; exact w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m22]; exact w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m22]; exact w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m22]; exact w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m22]; exact w21_88
  have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_284
  have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_288
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m22]; exact w21_424
  clear w21_88 w21_84 w21_80 w21_424 w21_420 w21_288 w21_284 w21_7c w21_78 w21_74 w21_70 y8_21 y4_21 y0_21 g21_2 g21_27 g21_26 g21_25 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 V21 E21 fR21 t21 fr21 A21 K21 rk21 sp21 s21 c21
  -- 0x1A8: branch, not taken
  obtain ⟨n23, d23, u23⟩ := s22.notTaken E22.self 0x1AC sv_at_1a8
    (by decide) (by rw [g22_10, s22.zero]; exact br_beq_f (((tb_in.restW hr1).rawN hr8).algOid hr21).pos_ne)
  have s23 : St n23.mem SV n23 0x1AC (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u23.regs, g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [u23.regs, g22_9]
  have g23_10 : reg n23 a0 = op21 := by rw [u23.regs, g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [u23.regs, g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [u23.regs, g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [u23.regs, g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [u23.regs, g22_23]
  have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [u23.regs, g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = lp := by rw [u23.regs, g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [u23.regs, g22_27]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m23]; exact w22_88
  have w23_284 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_284
  have w23_288 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_288
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_424
  clear w22_424 w22_420 w22_288 w22_284 w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 g22_10 g22_27 g22_26 g22_25 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x1AC: lw
  obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_1ac (off' := 0x1AE) (by decide)
    (by rw [g23_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s24 : St n24.mem SV n24 0x1AE (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_9]
  have g24_10 : reg n24 a0 = op21 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
  have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = lp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
  have g24_11 : reg n24 a1 = BitVec.ofNat 32 ol21 := by
    rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g23_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w23_84]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m24]; exact w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m24]; exact w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m24]; exact w23_88
  have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_284
  have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_288
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m24]; exact w23_424
  clear w23_424 w23_420 w23_288 w23_284 w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 g23_27 g23_26 g23_25 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x1AE: lw
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_1ae (off' := 0x1B0) (by decide)
    (by rw [g24_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s25 : St n25.mem SV n25 0x1B0 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
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
  have g25_10 : reg n25 a0 = op21 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_10]
  have g25_11 : reg n25 a1 = BitVec.ofNat 32 ol21 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_11]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = sgp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
  have g25_25 : reg n25 (25 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = lp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = tbl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
  have g25_24 : reg n25 (24 : Fin 32) = 0 := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w24_88]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m25]; exact w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m25]; exact w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m25]; exact w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m25]; exact w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m25]; exact w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m25]; exact w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m25]; exact w24_88
  have w25_284 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m25]; exact w24_284
  have w25_288 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m25]; exact w24_288
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m25]; exact w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m25]; exact w24_424
  clear w24_424 w24_420 w24_288 w24_284 w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 g24_11 g24_27 g24_26 g24_25 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x1B0
  obtain ⟨n26, c26, u26⟩ := s25.block svL31b0 E25.self svL31b0_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem SV n26 0x1BA (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock svL31b0 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
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
  have g26_10 : reg n26 a0 = op21 := by
    rw [rb26, runBlock_reg _ _ _ a0 s25.zero (by decide), g25_10]
  have g26_11 : reg n26 a1 = BitVec.ofNat 32 ol21 := by
    rw [rb26, runBlock_reg _ _ _ a1 s25.zero (by decide), g25_11]
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
  have g26_24 : reg n26 (24 : Fin 32) = 0 := by
    rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = sgl := by
    rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = lp := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = tbl := by
    rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
  have g26_12 : reg n26 a2 = BitVec.ofNat 32 (img% svOidEcdsaSha384Address) := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svL31b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g26_13 : reg n26 a3 = BitVec.ofNat 32 0x8 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svL31b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m26]; exact w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m26]; exact w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m26]; exact w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m26]; exact w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m26]; exact w25_88
  have w26_284 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m26]; exact w25_284
  have w26_288 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m26]; exact w25_288
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m26]; exact w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m26]; exact w25_424
  clear w25_424 w25_420 w25_288 w25_284 w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 g25_24 g25_27 g25_26 g25_25 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_11 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x1BA: sv_sneF
  obtain ⟨n27, c27, s27, rk27, a0_27, K27, fr27⟩ := sv_sneF (pl := ol21) (ql := 8)
    F E26 s26 sv_at_1ba sv_at_1be (by decide) (by decide) g26_2
    g26_10 g26_11 g26_12 g26_13 (.inl (((tb_in.restW hr1).rawN hr8).algOid hr21)) (.inr ⟨by decide, by decide⟩)
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keepL K27 (by decide)
  rw [sv_mbRo FW fR26 (.inl (((tb_in.restW hr1).rawN hr8).algOid hr21)), sv_mbRo FW fR26 (.inr ⟨by decide, by decide⟩)] at a0_27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rk27 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk27 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk27 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk27 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = tbp := by rw [rk27 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rk27 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rk27 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = dg := by rw [rk27 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = rootp := by rw [rk27 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = ll := by rw [rk27 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = sgp := by rw [rk27 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = 0 := by rw [rk27 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = sgl := by rw [rk27 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = lp := by rw [rk27 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = tbl := by rw [rk27 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := keep_kk26.trans K27
  clear keep_kk26
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K27.w32 (by decide) (by decide)).trans w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K27.w32 (by decide) (by decide)).trans w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K27.w32 (by decide) (by decide)).trans w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K27.w32 (by decide) (by decide)).trans w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := (K27.w32 (by decide) (by decide)).trans w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := (K27.w32 (by decide) (by decide)).trans w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := (K27.w32 (by decide) (by decide)).trans w26_88
  have w27_284 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K27.w32 (by decide) (by decide)).trans w26_284
  have w27_288 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K27.w32 (by decide) (by decide)).trans w26_288
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K27.w32 (by decide) (by decide)).trans w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K27.w32 (by decide) (by decide)).trans w26_424
  clear w26_424 w26_420 w26_288 w26_284 w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 g26_13 g26_12 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
  by_cases hz_27 : memBytes M0 op21 ol21 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcdsaSha384Address)) 8
  rotate_left
  · have g27_10 : reg n27 a0 = BitVec.ofNat 32 1 := by rw [a0_27, ite_eq_right hz_27]; rfl
    -- 0x1C2: branch, taken
    obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x7A4 sv_at_1c2
      (by decide) (by rw [g27_10, s27.zero]; decide)
    have s28 : St n28.mem SV n28 0x7A4 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u28.regs, g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = tbp := by rw [u28.regs, g27_9]
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [u28.regs, g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = sgp := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = 0 := by rw [u28.regs, g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = sgl := by rw [u28.regs, g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = lp := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = tbl := by rw [u28.regs, g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_70
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m28]; exact w27_74
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m28]; exact w27_78
    have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m28]; exact w27_7c
    have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m28]; exact w27_80
    have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m28]; exact w27_84
    have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m28]; exact w27_88
    have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_284
    have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_288
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m28]; exact w27_420
    have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_424
    clear w27_424 w27_420 w27_288 w27_284 w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 K27 a0_27 rk27 s27 c27
    exact .inl ⟨(fun ⟨tl1', h0', ip1', il1', h1', h2', tl8', h3', op21', ol21', h4', h5', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr1b] at h1'; cases h1'; rw [hr8] at h3'; cases h3'; rw [hr21] at h4'; cases h4'; exact hz_27 h5'), sv_fail F E28 s28 t28 (fun x hx => (fR28 x hx).trans (fM x hx).symm) V28 hret g28_2 g28_18 hO g28_3 g28_4 (by rw [g28_8]; sv_code)⟩
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 0 := by rw [a0_27, ite_eq_left hz_27]; rfl
  -- 0x1C2: branch, not taken
  obtain ⟨n28, d28, u28⟩ := s27.notTaken E27.self 0x1C6 sv_at_1c2
    (by decide) (by rw [g27_10, s27.zero]; decide)
  have s28 : St n28.mem SV n28 0x1C6 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u28.regs, g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = tbp := by rw [u28.regs, g27_9]
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x0 := by rw [u28.regs, g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [u28.regs, g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [u28.regs, g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [u28.regs, g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = sgp := by rw [u28.regs, g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = 0 := by rw [u28.regs, g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = sgl := by rw [u28.regs, g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = lp := by rw [u28.regs, g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = tbl := by rw [u28.regs, g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m28]; exact w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m28]; exact w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m28]; exact w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m28]; exact w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m28]; exact w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m28]; exact w27_88
  have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_284
  have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_288
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m28]; exact w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_424
  clear w27_424 w27_420 w27_288 w27_284 w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 K27 a0_27 rk27 s27 c27
  -- 0x1C6: branch, not taken
  obtain ⟨n29, d29, u29⟩ := s28.notTaken E28.self 0x1CA sv_at_1c6
    (by decide) (by rw [g28_24, s28.zero]; decide)
  have s29 : St n29.mem SV n29 0x1CA (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u29.regs, g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = tbp := by rw [u29.regs, g28_9]
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_10]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = dg := by rw [u29.regs, g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = rootp := by rw [u29.regs, g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = ll := by rw [u29.regs, g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = sgp := by rw [u29.regs, g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = 0 := by rw [u29.regs, g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = sgl := by rw [u29.regs, g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = lp := by rw [u29.regs, g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = tbl := by rw [u29.regs, g28_27]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x80, 0x8), (0x284, 0x8), (0x80, 0x11), (0x284, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m29]; exact w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op21 := by rw [m29]; exact w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol21 := by rw [m29]; exact w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m29]; exact w28_88
  have w29_284 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_284
  have w29_288 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_288
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (rp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m29]; exact w28_424
  clear w28_424 w28_420 w28_288 w28_284 w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28 g27_10
  exact .inr ⟨tl1, hr1, ip1, il1, hr1b, hz_5, tl8, hr8, op21, ol21, hr21, hz_27, n29, t29, s29, E29, V29, fR29, g29_2, g29_3, g29_4, g29_8, g29_9, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_25, g29_26, g29_27, w29_70, w29_74, w29_78, w29_7c, w29_80, w29_84, w29_88, w29_284, w29_288, w29_420, w29_424, keep_kk29.mono (by decide)⟩

end C3.RV32.Sv
