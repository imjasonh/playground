import C3BootProofs.Proofs.SvGt

/-!
# `sigstore::verify`: the TSTInfo's extensions, absent

From 0x128A to 0x12BE: the TSTInfo's optional `[1]` extensions are absent, and nothing follows.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTt6n128a : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x25C, .aluImm .add a2 x0 0xA1]
theorem svTt6n128a_end : blockEnd sigstoreVerifyCode 0x128A svTt6n128a = some 0x1294 := by
  simp only [svTt6n128a]
  rw [blockEnd, sv_at_128a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_128e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1290]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt6n12b8 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTt6n12b8_end : blockEnd sigstoreVerifyCode 0x12B8 svTt6n12b8 = some 0x12BA := by
  simp only [svTt6n12b8]
  rw [blockEnd, sv_at_12b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tt6n {B out bp x20 x21 x22 x23 x24 x25 x26 x27 rp rl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x128A (reg n0))
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
    (D0 : SvData M0)
    (hce : derOptRes 0xA1 (memBytes M0 (rp) (rl).toNat) = none) :
    (¬ ((rl = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((rl = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x12BE (reg n') ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x18)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x128A
  obtain ⟨n1, c1, u1⟩ := s0.block svTt6n128a E0.self svTt6n128a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x1294 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTt6n128a (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTt6n128a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTt6n128a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0xA1 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTt6n128a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_264 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := by rw [m1]; exact w0_264
  have w1_268 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := by rw [m1]; exact w0_268
  -- 0x1294: sv_optF2
  obtain ⟨n2, c2, s2, sp2, rk2, K2, R2, N2, fr2⟩ := sv_optF2 (oc := 0x420) (dc := 0x25C) (tag := 0xA1)
    F E1 s1 sv_at_1294 sv_at_1298 (by decide) (by decide) g1_2 g1_10 g1_11 g1_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w1_264 w1_268 rd_in
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [sv_mb fR1 rd_in] at R2 N2
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
  rw [hce] at R2
  obtain ⟨y0_2, y4_2⟩ := R2
  replace K2 := N2 hce
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x18)] := keep_kk1.trans K2
  clear keep_kk1
  have w2_264 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := (K2.w32 (by decide) (by decide)).trans w1_264
  have w2_268 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := (K2.w32 (by decide) (by decide)).trans w1_268
  have w2_424 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := y4_2
  have b2_420 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := y0_2
  clear w1_268 w1_264 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x129C: lbu
  obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_129c (off' := 0x12A0) (by decide)
  have s3 : St n3.mem SV n3 0x12A0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
  have g3_10 : reg n3 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b2_420]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x18)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_264 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := by rw [m3]; exact w2_264
  have w3_268 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := by rw [m3]; exact w2_268
  have w3_424 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m3]; exact w2_424
  have b3_420 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m3]; exact b2_420
  clear b2_420 w2_424 w2_268 w2_264 y4_2 y0_2 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 N2 K2 rk2 sp2 s2 c2
  -- 0x12A0: branch, taken
  obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x12B2 sv_at_12a0
    (by decide) (by rw [g3_10, s3.zero]; decide)
  have s4 : St n4.mem SV n4 0x12B2 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_10 : reg n4 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u4.regs, g3_10]
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
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x18)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_264 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := by rw [m4]; exact w3_264
  have w4_268 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := by rw [m4]; exact w3_268
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m4]; exact w3_424
  have b4_420 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m4]; exact b3_420
  clear b3_420 w3_424 w3_268 w3_264 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x12B2: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_12b2 (off' := 0x12B6) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x268 = B + 0x21A0 + BitVec.ofNat 32 0x268 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0x12B6 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
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
  have g5_10 : reg n5 a0 = rl := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x268 = B + 0x21A0 + BitVec.ofNat 32 0x268 by sv_addr, w4_268]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x18)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_264 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := by rw [m5]; exact w4_264
  have w5_268 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := by rw [m5]; exact w4_268
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m5]; exact w4_424
  have b5_420 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m5]; exact b4_420
  clear b4_420 w4_424 w4_268 w4_264 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  by_cases hend : rl = 0
  rotate_left
  · -- 0x12B6: branch, not taken
    obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0x12B8 sv_at_12b6
      (by decide) (by rw [g5_10, s5.zero]; exact br_beq_f hend)
    have s6 : St n6.mem SV n6 0x12B8 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans (.single d6)
    have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : SvCode n6.mem := E5.fr F fr6
    have V6 : SvSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
    have g6_10 : reg n6 a0 = rl := by rw [u6.regs, g5_10]
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
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x18)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_264 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := by rw [m6]; exact w5_264
    have w6_268 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := by rw [m6]; exact w5_268
    have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m6]; exact w5_424
    have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m6]; exact b5_420
    clear b5_420 w5_424 w5_268 w5_264 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    -- 0x12B8
    obtain ⟨n7, c7, u7⟩ := s6.block svTt6n12b8 E6.self svTt6n12b8_end
      ⟨trivial, trivial⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have s7 : St n7.mem SV n7 0x12BA (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have rb7 : ∀ q, reg n7 q = (runBlock svTt6n12b8 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
    have g7_10 : reg n7 a0 = rl := by
      rw [rb7, runBlock_reg _ _ _ a0 s6.zero (by decide), g6_10]
    have g7_18 : reg n7 (18 : Fin 32) = out := by
      rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by
      rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = x20 := by
      rw [rb7, runBlock_reg _ _ _ (20 : Fin 32) s6.zero (by decide), g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by
      rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = x22 := by
      rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = x23 := by
      rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = x24 := by
      rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = x25 := by
      rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = x26 := by
      rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = x27 := by
      rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
    have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb7]; simp +decide only [runBlock, BInstr.run, svTt6n12b8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g6_2, g6_3, g6_4, g6_10, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x18)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_264 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := by rw [m7]; exact w6_264
    have w7_268 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := by rw [m7]; exact w6_268
    have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m7]; exact w6_424
    have b7_420 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m7]; exact b6_420
    clear b6_420 w6_424 w6_268 w6_264 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
    -- 0x12BA: j
    obtain ⟨n8, d8, u8⟩ := s7.jump E7.self sv_at_12ba (off' := 0x7A4) (by decide)
      (by rw [s7.pc]; decide)
    have s8 : St n8.mem SV n8 0x7A4 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
    have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u8.regs, g7_8]
    have g8_10 : reg n8 a0 = rl := by rw [u8.regs, g7_10]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [u8.regs, g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [u8.regs, g7_27]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x18)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_264 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := by rw [m8]; exact w7_264
    have w8_268 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := by rw [m8]; exact w7_268
    have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m8]; exact w7_424
    have b8_420 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m8]; exact b7_420
    clear b7_420 w7_424 w7_268 w7_264 g7_8 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hend h0'), sv_fail F E8 s8 t8 (fun x hx => (fR8 x hx).trans (fM x hx).symm) V8 hret g8_2 g8_18 hO g8_3 g8_4 (by rw [g8_8]; sv_code)⟩
  -- 0x12B6: branch, taken
  obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0x12BE sv_at_12b6
    (by decide) (by rw [g5_10, s5.zero]; exact br_beq_t hend)
  have s6 : St n6.mem SV n6 0x12BE (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_10 : reg n6 a0 = rl := by rw [u6.regs, g5_10]
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
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x18)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_264 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp := by rw [m6]; exact w5_264
  have w6_268 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl := by rw [m6]; exact w5_268
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m6]; exact w5_424
  have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m6]; exact b5_420
  clear b5_420 w5_424 w5_268 w5_264 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  exact .inr ⟨hend, n6, t6, s6, E6, V6, fR6, g6_2, g6_3, g6_4, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, w6_264, w6_268, keep_kk6.mono (by decide)⟩

end C3.RV32.Sv
