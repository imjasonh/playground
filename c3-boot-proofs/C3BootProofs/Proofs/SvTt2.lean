import C3BootProofs.Proofs.SvGt

/-!
# `sigstore::verify`: the TSTInfo's serial number and time

From 0x119C to 0x1206: the TSTInfo's serial number is a positive integer of at most 20 bytes, not counting a leading zero, and its `genTime` is a `GeneralizedTime`, whose seconds go to the words at offsets 0x3C and 0x7C.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTt2119c : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x25C]
theorem svTt2119c_end : blockEnd sigstoreVerifyCode 0x119C svTt2119c = some 0x11A2 := by
  simp only [svTt2119c]
  rw [blockEnd, sv_at_119c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_11a0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt211ba : List BInstr :=
  [.aluImm .sltu a0 a0 0x1]
theorem svTt211ba_end : blockEnd sigstoreVerifyCode 0x11BA svTt211ba = some 0x11BE := by
  simp only [svTt211ba]
  rw [blockEnd, sv_at_11ba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt211be : List BInstr :=
  [.alu .sub a1 a1 a0]
theorem svTt211be_end : blockEnd sigstoreVerifyCode 0x11BE svTt211be = some 0x11C0 := by
  simp only [svTt211be]
  rw [blockEnd, sv_at_11be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt211c0 : List BInstr :=
  [.aluImm .add a0 x0 0x14]
theorem svTt211c0_end : blockEnd sigstoreVerifyCode 0x11C0 svTt211c0 = some 0x11C2 := by
  simp only [svTt211c0]
  rw [blockEnd, sv_at_11c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt211c6 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x25C, .aluImm .add a2 x0 0x18]
theorem svTt211c6_end : blockEnd sigstoreVerifyCode 0x11C6 svTt211c6 = some 0x11CE := by
  simp only [svTt211c6]
  rw [blockEnd, sv_at_11c6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_11ca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_11cc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt211e0 : List BInstr :=
  [.aluImm .add a0 sp 0x400]
theorem svTt211e0_end : blockEnd sigstoreVerifyCode 0x11E0 svTt211e0 = some 0x11E4 := by
  simp only [svTt211e0]
  rw [blockEnd, sv_at_11e0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tt2 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 rp rl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x119C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_264 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp)
    (w0_268 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl)
    (rd_in : SvIn B (rp) (rl).toNat)
    (D0 : SvData M0) :
    (¬ (∃ tl2, derElement 2 (memBytes M0 (rp) (rl).toNat) = .ok tl2 ∧ ∃ ip2 il2, derPosIntOf (memBytes M0 (rp) (rl).toNat) (rp) (.ok tl2) = .ok (ip2, il2) ∧ (((il2) - (aluEval .sltu ((M0 (ip2)).zeroExtend 32) 1)).toNat ≤ 20) ∧ ∃ tl13, derElement 0x18 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = .ok tl13 ∧ ∃ tm18, generalizedTime (memBytes M0 (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header) ((BitVec.ofNat 32 tl13.len).toNat)) = some tm18 ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl2, derElement 2 (memBytes M0 (rp) (rl).toNat) = .ok tl2 ∧
    ∃ ip2 il2, derPosIntOf (memBytes M0 (rp) (rl).toNat) (rp) (.ok tl2) = .ok (ip2, il2) ∧
    (((il2) - (aluEval .sltu ((M0 (ip2)).zeroExtend 32) 1)).toNat ≤ 20) ∧
    ∃ tl13, derElement 0x18 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = .ok tl13 ∧
    ∃ tm18, generalizedTime (memBytes M0 (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header) ((BitVec.ofNat 32 tl13.len).toNat)) = some tm18 ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1206 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = BitVec.ofNat 32 (tm18 % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 (tm18 / 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10), (0x3C, 0x4), (0x7C, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x119C
  obtain ⟨n1, c1, u1⟩ := s0.block svTt2119c E0.self svTt2119c_end
    ⟨trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x11A2 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTt2119c (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = x24 := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = x27 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTt2119c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTt2119c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_264 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := by rw [m1]; exact w0_264
  have w1_268 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := by rw [m1]; exact w0_268
  -- 0x11A2: sv_posF
  obtain ⟨n2, c2, s2, sp2, rk2, K2, A2, Ok2, Er2, fr2⟩ := sv_posF (oc := 0x420) (dc := 0x25C)
    F E1 s1 sv_at_11a2 sv_at_11a6 (by decide) (by decide) g1_2 g1_10 g1_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w1_264 w1_268 rd_in
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [sv_mb fR1 rd_in] at A2 Ok2 Er2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rk2 sp (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk2 (3 : Fin 32) (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk2 (4 : Fin 32) (by decide) (by decide), g1_4]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rk2 (18 : Fin 32) (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rk2 (19 : Fin 32) (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [rk2 (20 : Fin 32) (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [rk2 (21 : Fin 32) (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [rk2 (22 : Fin 32) (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [rk2 (23 : Fin 32) (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by rw [rk2 (24 : Fin 32) (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [rk2 (25 : Fin 32) (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [rk2 (26 : Fin 32) (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by rw [rk2 (27 : Fin 32) (by decide) (by decide), g1_27]
  obtain ⟨r2, hr2⟩ : ∃ r, derElement 2 (memBytes M0 (rp) (rl).toNat) = r := ⟨_, rfl⟩
  rcases r2 with er2 | tl2
  · obtain ⟨zhr2, -⟩ := Er2 er2 (by rw [hr2]; rfl)
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x8), (0x264, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_420 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := zhr2
    clear w1_268 w1_264 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0x11AA: lw
    obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_11aa (off' := 0x11AE) (by decide)
      (by rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s3 : St n3.mem SV n3 0x11AE (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
    have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
    have g3_10 : reg n3 a0 = 0 := by
      rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w2_420]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_420 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m3]; exact w2_420
    clear w2_420 zhr2
    -- 0x11AE: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x12AA sv_at_11ae
      (by decide) (by rw [g3_10, s3.zero]; rfl)
    have s4 : St n4.mem SV n4 0x12AA (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_10 : reg n4 a0 = 0 := by rw [u4.regs, g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, g3_23]
    have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [u4.regs, g3_24]
    have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [u4.regs, g3_27]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m4]; exact w3_420
    clear w3_420 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0x12AA: lbu
    obtain ⟨n5, d5, u5⟩ := s4.lbu E4.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s5 : St n5.mem SV n5 0x12AE (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
    have g5_10 : reg n5 a0 = 0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
    have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m5]; exact w4_420
    clear w4_420 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    -- 0x12AE: j
    obtain ⟨n6, d6, u6⟩ := s5.jump E5.self sv_at_12ae (off' := 0x7A4) (by decide)
      (by rw [s5.pc]; decide)
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
    have g6_10 : reg n6 a0 = 0 := by rw [u6.regs, g5_10]
    have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, g5_23]
    have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, g5_24]
    have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [u6.regs, g5_27]
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m6]; exact w5_420
    clear w5_420 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    exact .inl ⟨(fun ⟨tl2', h0', _⟩ => by rw [hr2] at h0'; cases h0'), sv_fail F E6 s6 t6 (fun x hx => (fR6 x hx).trans (fM x hx).symm) V6 hret g6_2 g6_18 hO g6_3 g6_4⟩
  obtain ⟨r2b, hr2b⟩ : ∃ r, derPosIntOf (memBytes M0 (rp) (rl).toNat) (rp) (.ok tl2) = r := ⟨_, rfl⟩
  rcases r2b with er2b | ⟨ip2, il2⟩
  · obtain ⟨zhr2b, -⟩ := Er2 er2b (by rw [hr2, hr2b])
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x8), (0x264, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_420 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := zhr2b
    clear w1_268 w1_264 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0x11AA: lw
    obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_11aa (off' := 0x11AE) (by decide)
      (by rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s3 : St n3.mem SV n3 0x11AE (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
    have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
    have g3_10 : reg n3 a0 = 0 := by
      rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w2_420]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_420 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m3]; exact w2_420
    clear w2_420 zhr2b
    -- 0x11AE: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x12AA sv_at_11ae
      (by decide) (by rw [g3_10, s3.zero]; rfl)
    have s4 : St n4.mem SV n4 0x12AA (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_10 : reg n4 a0 = 0 := by rw [u4.regs, g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, g3_23]
    have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [u4.regs, g3_24]
    have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [u4.regs, g3_27]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m4]; exact w3_420
    clear w3_420 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0x12AA: lbu
    obtain ⟨n5, d5, u5⟩ := s4.lbu E4.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s5 : St n5.mem SV n5 0x12AE (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
    have g5_10 : reg n5 a0 = 0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
    have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m5]; exact w4_420
    clear w4_420 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    -- 0x12AE: j
    obtain ⟨n6, d6, u6⟩ := s5.jump E5.self sv_at_12ae (off' := 0x7A4) (by decide)
      (by rw [s5.pc]; decide)
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
    have g6_10 : reg n6 a0 = 0 := by rw [u6.regs, g5_10]
    have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, g5_23]
    have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, g5_24]
    have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [u6.regs, g5_27]
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m6]; exact w5_420
    clear w5_420 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'), sv_fail F E6 s6 t6 (fun x hx => (fR6 x hx).trans (fM x hx).symm) V6 hret g6_2 g6_18 hO g6_3 g6_4⟩
  obtain ⟨p0_2, p4_2⟩ := Ok2 ip2 il2 (by rw [hr2, hr2b])
  obtain ⟨d8_2, d12_2⟩ := A2 tl2 hr2
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x8), (0x264, 0x8)] := keep_kk1.trans K2
  clear keep_kk1
  have w2_264 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := d8_2
  have w2_268 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := d12_2
  have w2_420 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := p0_2
  have w2_424 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := p4_2
  clear w1_268 w1_264 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  obtain ⟨ipin2, ilpos2⟩ := rd_in.posIntIn hr2 hr2b
  -- 0x11AA: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_11aa (off' := 0x11AE) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x11AE (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = ip2 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w2_420]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_264 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_264
  have w3_268 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_268
  have w3_420 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m3]; exact w2_420
  have w3_424 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m3]; exact w2_424
  clear w2_424 w2_420 w2_268 w2_264 d12_2 d8_2 p4_2 p0_2 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 Er2 Ok2 A2 K2 rk2 sp2 s2 c2
  -- 0x11AE: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0x11B0 sv_at_11ae
    (by decide) (by rw [g3_10, s3.zero]; exact br_beq_f (rd_in.serial_ne hr2 hr2b))
  have s4 : St n4.mem SV n4 0x11B0 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_10 : reg n4 a0 = ip2 := by rw [u4.regs, g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [u4.regs, g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [u4.regs, g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_264 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_264
  have w4_268 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_268
  have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m4]; exact w3_420
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m4]; exact w3_424
  clear w3_424 w3_420 w3_268 w3_264 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x11B0: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_11b0 (off' := 0x11B4) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0x11B4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_10 : reg n5 a0 = ip2 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_11 : reg n5 a1 = il2 := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w4_424]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_264 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_264
  have w5_268 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_268
  have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m5]; exact w4_420
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m5]; exact w4_424
  clear w4_424 w4_420 w4_268 w4_264 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x11B4: branch, not taken
  obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0x11B6 sv_at_11b4
    (by decide) (by rw [g5_11, s5.zero]; exact br_beq_f fun e => by rw [e] at ilpos2; exact absurd ilpos2 (by decide))
  have s6 : St n6.mem SV n6 0x11B6 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_10 : reg n6 a0 = ip2 := by rw [u6.regs, g5_10]
  have g6_11 : reg n6 a1 = il2 := by rw [u6.regs, g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [u6.regs, g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_264 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_264
  have w6_268 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_268
  have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m6]; exact w5_420
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m6]; exact w5_424
  clear w5_424 w5_420 w5_268 w5_264 g5_11 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x11B6: lbu from the bundle
  obtain ⟨n7, d7, u7⟩ := s6.lbu E6.self sv_at_11b6 (off' := 0x11BA) (by decide)
  have s7 : St n7.mem SV n7 0x11BA (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_11 : reg n7 a1 = il2 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_11]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_10 : reg n7 a0 = (M0 (ip2)).zeroExtend 32 := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_10, show (ip2) + 0x0 = ip2 from BitVec.add_zero _, fR6 _ (ipin2.r0 ilpos2)]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_264 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_264
  have w7_268 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_268
  have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m7]; exact w6_420
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m7]; exact w6_424
  clear w6_424 w6_420 w6_268 w6_264 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x11BA
  obtain ⟨n8, c8, u8⟩ := s7.block svTt211ba E7.self svTt211ba_end
    ⟨trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x11BE (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svTt211ba (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by
    rw [rb8, runBlock_reg _ _ _ sp s7.zero (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (3 : Fin 32) s7.zero (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (4 : Fin 32) s7.zero (by decide), g7_4]
  have g8_11 : reg n8 a1 = il2 := by
    rw [rb8, runBlock_reg _ _ _ a1 s7.zero (by decide), g7_11]
  have g8_18 : reg n8 (18 : Fin 32) = out := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by
    rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_10 : reg n8 a0 = aluEval .sltu ((M0 (ip2)).zeroExtend 32) 1 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svTt211ba, upd, ↓reduceIte]; rw [g7_10]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_264 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_264
  have w8_268 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_268
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m8]; exact w7_420
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m8]; exact w7_424
  clear w7_424 w7_420 w7_268 w7_264 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_11 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x11BE
  obtain ⟨n9, c9, u9⟩ := s8.block svTt211be E8.self svTt211be_end
    ⟨trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x11C0 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svTt211be (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by
    rw [rb9, runBlock_reg _ _ _ sp s8.zero (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (3 : Fin 32) s8.zero (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (4 : Fin 32) s8.zero (by decide), g8_4]
  have g9_10 : reg n9 a0 = aluEval .sltu ((M0 (ip2)).zeroExtend 32) 1 := by
    rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by
    rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_11 : reg n9 a1 = (il2) - (aluEval .sltu ((M0 (ip2)).zeroExtend 32) 1) := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svTt211be, upd, ↓reduceIte]; rw [g8_11, g8_10]; rfl
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_264 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_264
  have w9_268 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_268
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m9]; exact w8_420
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m9]; exact w8_424
  clear w8_424 w8_420 w8_268 w8_264 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_11 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x11C0
  obtain ⟨n10, c10, u10⟩ := s9.block svTt211c0 E9.self svTt211c0_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x11C2 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svTt211c0 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_11 : reg n10 a1 = (il2) - (aluEval .sltu ((M0 (ip2)).zeroExtend 32) 1) := by
    rw [rb10, runBlock_reg _ _ _ a1 s9.zero (by decide), g9_11]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 0x14 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svTt211c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_10, g9_11, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_264 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_264
  have w10_268 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_268
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m10]; exact w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m10]; exact w9_424
  clear w9_424 w9_420 w9_268 w9_264 g9_11 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  by_cases hser : ((il2) - (aluEval .sltu ((M0 (ip2)).zeroExtend 32) 1)).toNat ≤ 20
  rotate_left
  · -- 0x11C2: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x7A4 sv_at_11c2
      (by decide) (by rw [g10_10, g10_11]; exact br_bltu_t (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega))
    have s11 : St n11.mem SV n11 0x7A4 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x14 := by rw [u11.regs, g10_10]
    have g11_11 : reg n11 a1 = (il2) - (aluEval .sltu ((M0 (ip2)).zeroExtend 32) 1) := by rw [u11.regs, g10_11]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_264 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_264
    have w11_268 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_268
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m11]; exact w10_420
    have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m11]; exact w10_424
    clear w10_424 w10_420 w10_268 w10_264 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_11 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', h2', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'; exact hser h2'), sv_fail F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4⟩
  -- 0x11C2: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x11C6 sv_at_11c2
    (by decide) (by rw [g10_10, g10_11]; exact br_bltu_f (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega))
  have s11 : St n11.mem SV n11 0x11C6 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x14 := by rw [u11.regs, g10_10]
  have g11_11 : reg n11 a1 = (il2) - (aluEval .sltu ((M0 (ip2)).zeroExtend 32) 1) := by rw [u11.regs, g10_11]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_264 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_264
  have w11_268 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_268
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m11]; exact w10_424
  clear w10_424 w10_420 w10_268 w10_264 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_11 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x11C6
  obtain ⟨n12, c12, u12⟩ := s11.block svTt211c6 E11.self svTt211c6_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x11CE (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svTt211c6 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans c12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by
    rw [rb12, runBlock_reg _ _ _ sp s11.zero (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (3 : Fin 32) s11.zero (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (4 : Fin 32) s11.zero (by decide), g11_4]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTt211c6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_10, g11_11, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTt211c6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_10, g11_11, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_12 : reg n12 a2 = BitVec.ofNat 32 0x18 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTt211c6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_10, g11_11, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x8), (0x264, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_264 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_264
  have w12_268 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_268
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip2 := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il2 := by rw [m12]; exact w11_424
  clear w11_424 w11_420 w11_268 w11_264 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_11 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x11CE: sv_elemF
  obtain ⟨n13, c13, s13, rk13, K13, Ok13, Er13, fr13⟩ := sv_elemF (oc := 0x420) (dc := 0x25C) (tag := 0x18)
    F E12 s12 sv_at_11ce sv_at_11d2 (by decide) (by decide) g12_10 g12_11 g12_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w12_264 w12_268
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keepL K13 (by decide)
  rw [sv_mb fR12 (rd_in.restW hr2)] at Ok13 Er13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rk13 sp (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk13 (3 : Fin 32) (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk13 (4 : Fin 32) (by decide) (by decide), g12_4]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [rk13 a0 (by decide) (by decide), g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rk13 (18 : Fin 32) (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rk13 (19 : Fin 32) (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [rk13 (20 : Fin 32) (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [rk13 (21 : Fin 32) (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [rk13 (22 : Fin 32) (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [rk13 (23 : Fin 32) (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [rk13 (24 : Fin 32) (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [rk13 (25 : Fin 32) (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rk13 (26 : Fin 32) (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [rk13 (27 : Fin 32) (by decide) (by decide), g12_27]
  obtain ⟨r13, hr13⟩ : ∃ r, derElement 0x18 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = r := ⟨_, rfl⟩
  rcases r13 with er13 | tl13
  · obtain ⟨zhr13, -⟩ := Er13 er13 hr13
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := keep_kk12.trans K13
    clear keep_kk12
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := zhr13
    clear w12_424 w12_420 w12_268 w12_264 g12_12 g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    -- 0x11D6: lw
    obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_11d6 (off' := 0x11DA) (by decide)
      (by rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s14 : St n14.mem SV n14 0x11DA (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
    have t14 : Steps n0 n14 := t13.trans (.single d14)
    have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.same m14
    have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
    have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_10]
    have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
    have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_20]
    have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
    have g14_11 : reg n14 a1 = 0 := by
      rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w13_420]
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m14]; exact w13_420
    clear w13_420 zhr13
    -- 0x11DA: branch, taken
    obtain ⟨n15, d15, u15⟩ := s14.taken E14.self 0x12AA sv_at_11da
      (by decide) (by rw [g14_11, s14.zero]; rfl)
    have s15 : St n15.mem SV n15 0x12AA (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
    have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u15.regs, g14_10]
    have g15_11 : reg n15 a1 = 0 := by rw [u15.regs, g14_11]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, g14_27]
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m15]; exact w14_420
    clear w14_420 g14_11 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_10 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
    -- 0x12AA: lbu
    obtain ⟨n16, d16, u16⟩ := s15.lbu E15.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s16 : St n16.mem SV n16 0x12AE (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
    have g16_10 : reg n16 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_10]
    have g16_11 : reg n16 a1 = 0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_11]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m16]; exact w15_420
    clear w15_420 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_11 g15_10 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
    -- 0x12AE: j
    obtain ⟨n17, d17, u17⟩ := s16.jump E16.self sv_at_12ae (off' := 0x7A4) (by decide)
      (by rw [s16.pc]; decide)
    have s17 : St n17.mem SV n17 0x7A4 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u17.regs, g16_10]
    have g17_11 : reg n17 a1 = 0 := by rw [u17.regs, g16_11]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m17]; exact w16_420
    clear w16_420 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_11 g16_10 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', h2', tl13', h3', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'; rw [hr13] at h3'; cases h3'), sv_fail F E17 s17 t17 (fun x hx => (fR17 x hx).trans (fM x hx).symm) V17 hret g17_2 g17_18 hO g17_3 g17_4⟩
  obtain ⟨o0_13, o4_13, o8_13, o12_13, o16_13, d8_13, d12_13⟩ := Ok13 tl13 hr13
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := keep_kk12.trans K13
  clear keep_kk12
  have w13_264 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := d8_13
  have w13_268 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := d12_13
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := o0_13
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := o4_13
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := o8_13
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := o12_13
  have b13_430 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := o16_13
  clear w12_424 w12_420 w12_268 w12_264 g12_12 g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x11D6: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_11d6 (off' := 0x11DA) (by decide)
    (by rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0x11DA (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_10]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
  have g14_11 : reg n14 a1 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w13_420]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_264 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m14]; exact w13_264
  have w14_268 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m14]; exact w13_268
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m14]; exact w13_42c
  have b14_430 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m14]; exact b13_430
  clear b13_430 w13_42c w13_428 w13_424 w13_420 w13_268 w13_264 d12_13 d8_13 o16_13 o12_13 o8_13 o4_13 o0_13 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_10 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 Er13 Ok13 K13 rk13 s13 c13
  -- 0x11DA: branch, not taken
  obtain ⟨n15, d15, u15⟩ := s14.notTaken E14.self 0x11DC sv_at_11da
    (by decide) (by rw [g14_11, s14.zero]; exact br_beq_f ((rd_in.restW hr2).ok_ne hr13))
  have s15 : St n15.mem SV n15 0x11DC (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u15.regs, g14_10]
  have g15_11 : reg n15 a1 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [u15.regs, g14_11]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_264 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m15]; exact w14_264
  have w15_268 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m15]; exact w14_268
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m15]; exact w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m15]; exact w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m15]; exact w14_42c
  have b15_430 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m15]; exact b14_430
  clear b14_430 w14_42c w14_428 w14_424 w14_420 w14_268 w14_264 g14_11 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_10 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x11DC: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_11dc (off' := 0x11E0) (by decide)
    (by rw [g15_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0x11E0 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_10 : reg n16 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_10]
  have g16_11 : reg n16 a1 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [u16.regs, upd_ne (by decide) (by decide), g15_11]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
  have g16_12 : reg n16 a2 = BitVec.ofNat 32 tl13.len := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w15_424]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m16]; exact w15_264
  have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m16]; exact w15_268
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m16]; exact w15_42c
  have b16_430 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m16]; exact b15_430
  clear b15_430 w15_42c w15_428 w15_424 w15_420 w15_268 w15_264 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_11 g15_10 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x11E0
  obtain ⟨n17, c17, u17⟩ := s16.block svTt211e0 E16.self svTt211e0_end
    ⟨trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x11E4 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svTt211e0 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by
    rw [rb17, runBlock_reg _ _ _ sp s16.zero (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (3 : Fin 32) s16.zero (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (4 : Fin 32) s16.zero (by decide), g16_4]
  have g17_11 : reg n17 a1 = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by
    rw [rb17, runBlock_reg _ _ _ a1 s16.zero (by decide), g16_11]
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 tl13.len := by
    rw [rb17, runBlock_reg _ _ _ a2 s16.zero (by decide), g16_12]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svTt211e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_11, g16_12, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_264 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m17]; exact w16_264
  have w17_268 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m17]; exact w16_268
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m17]; exact w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m17]; exact w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m17]; exact w16_42c
  have b17_430 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m17]; exact b16_430
  clear b16_430 w16_42c w16_428 w16_424 w16_420 w16_268 w16_264 g16_12 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_11 g16_10 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x11E4: sv_gtF
  obtain ⟨n18, c18, s18, sp18, rk18, K18, Ok18, Er18, fr18⟩ := sv_gtF (oc := 0x400) (nl := (BitVec.ofNat 32 tl13.len).toNat)
    F E17 s17 sv_at_11e4 sv_at_11e8 (by decide) (by decide) g17_2
    g17_10 g17_11 (by rw [g17_12, ofNat_toNat_self]) (by decide) (by decide) ((rd_in.restW hr2).contentW hr13)
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keepL K18 (by decide)
  rw [sv_mb fR17 ((rd_in.restW hr2).contentW hr13)] at Ok18 Er18
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk18 (3 : Fin 32) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk18 (4 : Fin 32) (by decide), g17_4]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rk18 (18 : Fin 32) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rk18 (19 : Fin 32) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [rk18 (20 : Fin 32) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [rk18 (21 : Fin 32) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [rk18 (22 : Fin 32) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [rk18 (23 : Fin 32) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [rk18 (24 : Fin 32) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [rk18 (25 : Fin 32) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [rk18 (26 : Fin 32) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [rk18 (27 : Fin 32) (by decide), g17_27]
  have g18_2 : reg n18 sp = B + 0x21A0 := sp18
  obtain ⟨r18, hr18⟩ : ∃ r, generalizedTime (memBytes M0 (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header) ((BitVec.ofNat 32 tl13.len).toNat)) = r := ⟨_, rfl⟩
  rcases r18 with _ | tm18
  · obtain ⟨y0_18, y1_18⟩ := Er18 hr18
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10)] := keep_kk17.trans K18
    clear keep_kk17
    have w18_264 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_264
    have w18_268 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_268
    have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := (K18.w32 (by decide) (by decide)).trans w17_420
    have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K18.w32 (by decide) (by decide)).trans w17_424
    have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K18.w32 (by decide) (by decide)).trans w17_428
    have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_42c
    have b18_430 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := (K18.b8 (by decide) (by decide)).trans b17_430
    have b18_400 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := y0_18
    have b18_401 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x401) = (0x19 : BitVec 8) := y1_18
    clear b17_430 w17_42c w17_428 w17_424 w17_420 w17_268 w17_264 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_12 g17_11 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
    -- 0x11EC: lbu
    obtain ⟨n19, d19, u19⟩ := s18.lbu E18.self sv_at_11ec (off' := 0x11F0) (by decide)
    have s19 : St n19.mem SV n19 0x11F0 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
    have g19_10 : reg n19 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g18_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, b18_400]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_264 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m19]; exact w18_264
    have w19_268 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m19]; exact w18_268
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m19]; exact w18_420
    have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m19]; exact w18_424
    have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m19]; exact w18_428
    have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m19]; exact w18_42c
    have b19_400 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m19]; exact b18_400
    have b19_401 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x401) = (0x19 : BitVec 8) := by rw [m19]; exact b18_401
    have b19_430 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m19]; exact b18_430
    clear b18_401 b18_400 b18_430 w18_42c w18_428 w18_424 w18_420 w18_268 w18_264 y1_18 y0_18
    -- 0x11F0: branch, not taken
    obtain ⟨n20, d20, u20⟩ := s19.notTaken E19.self 0x11F2 sv_at_11f0
      (by decide) (by rw [g19_10, s19.zero]; decide)
    have s20 : St n20.mem SV n20 0x11F2 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
    have g20_10 : reg n20 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u20.regs, g19_10]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [u20.regs, g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, g19_27]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_264 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m20]; exact w19_264
    have w20_268 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m20]; exact w19_268
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m20]; exact w19_420
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m20]; exact w19_424
    have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_428
    have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m20]; exact w19_42c
    have b20_400 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m20]; exact b19_400
    have b20_401 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x401) = (0x19 : BitVec 8) := by rw [m20]; exact b19_401
    have b20_430 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m20]; exact b19_430
    clear b19_430 b19_401 b19_400 w19_42c w19_428 w19_424 w19_420 w19_268 w19_264 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
    -- 0x11F2: lbu
    obtain ⟨n21, d21, u21⟩ := s20.lbu E20.self sv_at_11f2 (off' := 0x11F6) (by decide)
    have s21 : St n21.mem SV n21 0x11F6 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
    have g21_10 : reg n21 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_10]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
    have g21_8 : reg n21 (8 : Fin 32) = ((0x19 : BitVec 8)).zeroExtend 32 := by
      rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g20_2, show B + 0x21A0 + 0x401 = B + 0x21A0 + BitVec.ofNat 32 0x401 by sv_addr, b20_401]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_264 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m21]; exact w20_264
    have w21_268 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m21]; exact w20_268
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m21]; exact w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m21]; exact w20_42c
    have b21_400 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m21]; exact b20_400
    have b21_401 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x401) = (0x19 : BitVec 8) := by rw [m21]; exact b20_401
    have b21_430 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m21]; exact b20_430
    clear b20_430 b20_401 b20_400 w20_42c w20_428 w20_424 w20_420 w20_268 w20_264 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
    -- 0x11F6: j
    obtain ⟨n22, d22, u22⟩ := s21.jump E21.self sv_at_11f6 (off' := 0x7A4) (by decide)
      (by rw [s21.pc]; decide)
    have s22 : St n22.mem SV n22 0x7A4 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = ((0x19 : BitVec 8)).zeroExtend 32 := by rw [u22.regs, g21_8]
    have g22_10 : reg n22 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u22.regs, g21_10]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_264 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m22]; exact w21_264
    have w22_268 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m22]; exact w21_268
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m22]; exact w21_420
    have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m22]; exact w21_424
    have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_428
    have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m22]; exact w21_42c
    have b22_400 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m22]; exact b21_400
    have b22_401 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x401) = (0x19 : BitVec 8) := by rw [m22]; exact b21_401
    have b22_430 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m22]; exact b21_430
    clear b21_430 b21_401 b21_400 w21_42c w21_428 w21_424 w21_420 w21_268 w21_264 g21_8 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    exact .inl ⟨(fun ⟨tl2', h0', ip2', il2', h1', h2', tl13', h3', tm18', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr2b] at h1'; cases h1'; rw [hr13] at h3'; cases h3'; rw [hr18] at h4'; cases h4'), sv_fail F E22 s22 t22 (fun x hx => (fR22 x hx).trans (fM x hx).symm) V22 hret g22_2 g22_18 hO g22_3 g22_4⟩
  obtain ⟨-, y0_18, y8_18, y12_18⟩ := Ok18 tm18 hr18
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10)] := keep_kk17.trans K18
  clear keep_kk17
  have w18_264 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_264
  have w18_268 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_268
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := (K18.w32 (by decide) (by decide)).trans w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K18.w32 (by decide) (by decide)).trans w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K18.w32 (by decide) (by decide)).trans w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_42c
  have b18_430 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := (K18.b8 (by decide) (by decide)).trans b17_430
  have w18_408 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := y8_18
  have w18_40c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 (tm18 / 2 ^ 32) := y12_18
  have b18_400 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := y0_18
  clear b17_430 w17_42c w17_428 w17_424 w17_420 w17_268 w17_264 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_12 g17_11 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x11EC: lbu
  obtain ⟨n19, d19, u19⟩ := s18.lbu E18.self sv_at_11ec (off' := 0x11F0) (by decide)
  have s19 : St n19.mem SV n19 0x11F0 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_10 : reg n19 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, b18_400]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_264 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m19]; exact w18_264
  have w19_268 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m19]; exact w18_268
  have w19_408 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := by rw [m19]; exact w18_408
  have w19_40c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 (tm18 / 2 ^ 32) := by rw [m19]; exact w18_40c
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m19]; exact w18_42c
  have b19_400 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m19]; exact b18_400
  have b19_430 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m19]; exact b18_430
  clear b18_400 w18_40c w18_408 b18_430 w18_42c w18_428 w18_424 w18_420 w18_268 w18_264 y12_18 y8_18 y0_18 g18_2 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_4 g18_3 V18 E18 fR18 t18 fr18 Er18 Ok18 K18 rk18 sp18 s18 c18
  -- 0x11F0: branch, taken
  obtain ⟨n20, d20, u20⟩ := s19.taken E19.self 0x11FA sv_at_11f0
    (by decide) (by rw [g19_10, s19.zero]; decide)
  have s20 : St n20.mem SV n20 0x11FA (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
  have g20_10 : reg n20 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u20.regs, g19_10]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [u20.regs, g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, g19_27]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_264 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m20]; exact w19_264
  have w20_268 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m20]; exact w19_268
  have w20_408 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := by rw [m20]; exact w19_408
  have w20_40c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 (tm18 / 2 ^ 32) := by rw [m20]; exact w19_40c
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m20]; exact w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m20]; exact w19_42c
  have b20_400 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m20]; exact b19_400
  have b20_430 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m20]; exact b19_430
  clear b19_430 b19_400 w19_42c w19_428 w19_424 w19_420 w19_40c w19_408 w19_268 w19_264 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x11FA: lw
  obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_11fa (off' := 0x11FE) (by decide)
    (by rw [g20_2, show B + 0x21A0 + 0x408 = B + 0x21A0 + BitVec.ofNat 32 0x408 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s21 : St n21.mem SV n21 0x11FE (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_10 : reg n21 a0 = BitVec.ofNat 32 (tm18 % 2 ^ 32) := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x408 = B + 0x21A0 + BitVec.ofNat 32 0x408 by sv_addr, w20_408]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_264 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m21]; exact w20_264
  have w21_268 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m21]; exact w20_268
  have w21_408 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := by rw [m21]; exact w20_408
  have w21_40c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 (tm18 / 2 ^ 32) := by rw [m21]; exact w20_40c
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m21]; exact w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m21]; exact w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m21]; exact w20_42c
  have b21_400 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m21]; exact b20_400
  have b21_430 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m21]; exact b20_430
  clear b20_430 b20_400 w20_42c w20_428 w20_424 w20_420 w20_40c w20_408 w20_268 w20_264 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0x11FE: sw
  obtain ⟨n22, d22, s22, fr22, K22, W22, rg22⟩ := sv_sw F E21 s21 sv_at_11fe (off' := 0x1200) (c := 0x3C)
    (by decide) (by rw [g21_2]; sv_addr) (by decide) (by decide)
  have t22 : Steps n0 n22 := t21.trans d22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rg22 sp, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg22 (3 : Fin 32), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg22 (4 : Fin 32), g21_4]
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 (tm18 % 2 ^ 32) := by rw [rg22 a0, g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rg22 (18 : Fin 32), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rg22 (19 : Fin 32), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [rg22 (20 : Fin 32), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [rg22 (21 : Fin 32), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [rg22 (22 : Fin 32), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [rg22 (23 : Fin 32), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [rg22 (24 : Fin 32), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [rg22 (25 : Fin 32), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [rg22 (26 : Fin 32), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [rg22 (27 : Fin 32), g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10), (0x3C, 0x4)] := keep_kk21.trans K22.toL
  clear keep_kk21
  have w22_264 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K22.w32 (by decide) (by decide)).trans w21_264
  have w22_268 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K22.w32 (by decide) (by decide)).trans w21_268
  have w22_408 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := (K22.w32 (by decide) (by decide)).trans w21_408
  have w22_40c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 (tm18 / 2 ^ 32) := (K22.w32 (by decide) (by decide)).trans w21_40c
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := (K22.w32 (by decide) (by decide)).trans w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K22.w32 (by decide) (by decide)).trans w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K22.w32 (by decide) (by decide)).trans w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := (K22.w32 (by decide) (by decide)).trans w21_42c
  have b22_400 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := (K22.b8 (by decide) (by decide)).trans b21_400
  have b22_430 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := (K22.b8 (by decide) (by decide)).trans b21_430
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := by rw [W22, g21_10]
  clear b21_430 b21_400 w21_42c w21_428 w21_424 w21_420 w21_40c w21_408 w21_268 w21_264 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0x1200: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_1200 (off' := 0x1204) (by decide)
    (by rw [g22_2, show B + 0x21A0 + 0x40C = B + 0x21A0 + BitVec.ofNat 32 0x40C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x1204 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 (tm18 / 2 ^ 32) := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_2, show B + 0x21A0 + 0x40C = B + 0x21A0 + BitVec.ofNat 32 0x40C by sv_addr, w22_40c]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10), (0x3C, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := by rw [m23]; exact w22_3c
  have w23_264 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_264
  have w23_268 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_268
  have w23_408 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := by rw [m23]; exact w22_408
  have w23_40c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 (tm18 / 2 ^ 32) := by rw [m23]; exact w22_40c
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_42c
  have b23_400 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m23]; exact b22_400
  have b23_430 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := by rw [m23]; exact b22_430
  clear w22_3c b22_430 b22_400 w22_42c w22_428 w22_424 w22_420 w22_40c w22_408 w22_268 w22_264 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_4 g22_3 g22_2 V22 E22 fR22 t22 rg22 W22 K22 fr22 s22 d22
  -- 0x1204: sw
  obtain ⟨n24, d24, s24, fr24, K24, W24, rg24⟩ := sv_sw F E23 s23 sv_at_1204 (off' := 0x1206) (c := 0x7C)
    (by decide) (by rw [g23_2]; sv_addr) (by decide) (by decide)
  have t24 : Steps n0 n24 := t23.trans d24
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [rg24 sp, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg24 (3 : Fin 32), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg24 (4 : Fin 32), g23_4]
  have g24_10 : reg n24 a0 = BitVec.ofNat 32 (tm18 / 2 ^ 32) := by rw [rg24 a0, g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [rg24 (18 : Fin 32), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [rg24 (19 : Fin 32), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [rg24 (20 : Fin 32), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [rg24 (21 : Fin 32), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [rg24 (22 : Fin 32), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [rg24 (23 : Fin 32), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [rg24 (24 : Fin 32), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [rg24 (25 : Fin 32), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [rg24 (26 : Fin 32), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [rg24 (27 : Fin 32), g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x8), (0x264, 0x8), (0x420, 0x11), (0x264, 0x8), (0x400, 0x10), (0x3C, 0x4), (0x7C, 0x4)] := keep_kk23.trans K24.toL
  clear keep_kk23
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := (K24.w32 (by decide) (by decide)).trans w23_3c
  have w24_264 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K24.w32 (by decide) (by decide)).trans w23_264
  have w24_268 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K24.w32 (by decide) (by decide)).trans w23_268
  have w24_408 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = BitVec.ofNat 32 (tm18 % 2 ^ 32) := (K24.w32 (by decide) (by decide)).trans w23_408
  have w24_40c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = BitVec.ofNat 32 (tm18 / 2 ^ 32) := (K24.w32 (by decide) (by decide)).trans w23_40c
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl13.header := (K24.w32 (by decide) (by decide)).trans w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K24.w32 (by decide) (by decide)).trans w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K24.w32 (by decide) (by decide)).trans w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl13.header + tl13.len) := (K24.w32 (by decide) (by decide)).trans w23_42c
  have b24_400 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := (K24.b8 (by decide) (by decide)).trans b23_400
  have b24_430 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl13.tag := (K24.b8 (by decide) (by decide)).trans b23_430
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 (tm18 / 2 ^ 32) := by rw [W24, g23_10]
  clear b23_430 b23_400 w23_42c w23_428 w23_424 w23_420 w23_40c w23_408 w23_268 w23_264 w23_3c g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  exact .inr ⟨tl2, hr2, ip2, il2, hr2b, hser, tl13, hr13, tm18, hr18, n24, t24, s24, E24, V24, fR24, g24_2, g24_3, g24_4, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, w24_3c, w24_7c, w24_264, w24_268, keep_kk24.mono (by decide)⟩

end C3.RV32.Sv
