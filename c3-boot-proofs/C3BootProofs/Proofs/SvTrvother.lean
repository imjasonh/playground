import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: another signed attribute

From 0xF5C to 0xFF8: the attribute is neither contentType nor messageDigest, and is skipped.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTrvotherf5c : List BInstr :=
  [.aluImm .add a3 x0 0x9, .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (26 : Fin 32), .lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF856]
theorem svTrvotherf5c_end : blockEnd sigstoreVerifyCode 0xF5C svTrvotherf5c = some 0xF6A := by
  simp only [svTrvotherf5c]
  rw [blockEnd, sv_at_f5c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f5e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f60]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f62]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f66]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrvotherfb4 : List BInstr :=
  [.aluImm .add a3 x0 0x9, .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (26 : Fin 32), .lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF85F]
theorem svTrvotherfb4_end : blockEnd sigstoreVerifyCode 0xFB4 svTrvotherfb4 = some 0xFC2 := by
  simp only [svTrvotherfb4]
  rw [blockEnd, sv_at_fb4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_fb6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_fb8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_fba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_fbe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_trvother {B out bp x20 x21 x22 x23 x25 dg flag p0 L0 op ol vcp vcl x24 cp rem sip sil : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xF5C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = op)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = ol)
    (g0_27 : reg n0 (27 : Fin 32) = L0)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag)
    (w0_25c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0)
    (w0_260 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0)
    (w0_264 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp)
    (w0_268 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem)
    (w0_378 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip)
    (w0_37c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil)
    (w0_408 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = vcp)
    (w0_40c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = vcl)
    (cr_in : SvIn B (cp) (rem).toNat)
    (p0_in : SvIn B (p0) (L0).toNat)
    (si_in : SvIn B (sip) (sil).toNat)
    (vc_in : SvIn B (vcp) (vcl).toNat)
    (oid_in : SvIn B op ol.toNat)
    (hct : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)
    (hmd : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9) :
    (¬ (True) ∧ SvErrRet B out v n0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xFF8 (reg n') ∧
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
        reg n' (26 : Fin 32) = ol ∧
        reg n' (27 : Fin 32) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil ∧
        SvKeepL B n0.mem n'.mem []) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xF5C
  obtain ⟨n1, c1, u1⟩ := s0.block svTrvotherf5c E0.self svTrvotherf5c_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xF6A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTrvotherf5c (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_9 : reg n1 (9 : Fin 32) = op := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
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
  have g1_26 : reg n1 (26 : Fin 32) = ol := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = L0 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = op := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTrvotherf5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = ol := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTrvotherf5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x15) := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTrvotherf5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_13 : reg n1 a3 = BitVec.ofNat 32 0x9 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTrvotherf5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m1]; exact w0_64
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m1]; exact w0_7c
  have w1_25c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m1]; exact w0_25c
  have w1_260 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m1]; exact w0_260
  have w1_264 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m1]; exact w0_264
  have w1_268 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m1]; exact w0_268
  have w1_378 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m1]; exact w0_378
  have w1_37c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m1]; exact w0_37c
  have w1_408 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = vcp := by rw [m1]; exact w0_408
  have w1_40c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = vcl := by rw [m1]; exact w0_40c
  -- 0xF6A: sv_seqEqF
  obtain ⟨n2, c2, s2, rk2, a0_2, K2, fr2⟩ := sv_seqEqF (pl := ol.toNat) (ql := 9)
    F E1 s1 sv_at_f6a sv_at_f6e (by decide) (by decide) g1_2
    g1_10 (by rw [g1_11, ofNat_toNat_self]) g1_12 g1_13 (.inl oid_in) (.inr ⟨by decide, by decide⟩)
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [sv_mbRo FW fR1 (.inl oid_in), sv_mbRo FW fR1 (.inr ⟨by decide, by decide⟩)] at a0_2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rk2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk2 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk2 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_4]
  have g2_9 : reg n2 (9 : Fin 32) = op := by rw [rk2 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_9]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rk2 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rk2 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [rk2 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [rk2 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [rk2 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [rk2 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by rw [rk2 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [rk2 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = ol := by rw [rk2 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = L0 := by rw [rk2 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := keep_kk1.trans K2
  clear keep_kk1
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K2.w32 (by decide) (by decide)).trans w1_64
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K2.w32 (by decide) (by decide)).trans w1_7c
  have w2_25c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K2.w32 (by decide) (by decide)).trans w1_25c
  have w2_260 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K2.w32 (by decide) (by decide)).trans w1_260
  have w2_264 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K2.w32 (by decide) (by decide)).trans w1_264
  have w2_268 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K2.w32 (by decide) (by decide)).trans w1_268
  have w2_378 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K2.w32 (by decide) (by decide)).trans w1_378
  have w2_37c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K2.w32 (by decide) (by decide)).trans w1_37c
  have w2_408 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = vcp := (K2.w32 (by decide) (by decide)).trans w1_408
  have w2_40c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = vcl := (K2.w32 (by decide) (by decide)).trans w1_40c
  clear w1_40c w1_408 w1_37c w1_378 w1_268 w1_264 w1_260 w1_25c w1_7c w1_64 g1_13 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  have g2_10 : reg n2 a0 = BitVec.ofNat 32 0 := by rw [a0_2, ite_eq_right hct]; rfl
  -- 0xF72: branch, taken
  obtain ⟨n3, d3, u3⟩ := s2.taken E2.self 0xFB4 sv_at_f72
    (by decide) (by rw [g2_10, s2.zero]; decide)
  have s3 : St n3.mem SV n3 0xFB4 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
  have g3_9 : reg n3 (9 : Fin 32) = op := by rw [u3.regs, g2_9]
  have g3_10 : reg n3 a0 = BitVec.ofNat 32 0x0 := by rw [u3.regs, g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = ol := by rw [u3.regs, g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = L0 := by rw [u3.regs, g2_27]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m3]; exact w2_64
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m3]; exact w2_7c
  have w3_25c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m3]; exact w2_25c
  have w3_260 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m3]; exact w2_260
  have w3_264 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m3]; exact w2_264
  have w3_268 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m3]; exact w2_268
  have w3_378 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m3]; exact w2_378
  have w3_37c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m3]; exact w2_37c
  have w3_408 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = vcp := by rw [m3]; exact w2_408
  have w3_40c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = vcl := by rw [m3]; exact w2_40c
  clear w2_40c w2_408 w2_37c w2_378 w2_268 w2_264 w2_260 w2_25c w2_7c w2_64 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 K2 a0_2 rk2 s2 c2
  -- 0xFB4
  obtain ⟨n4, c4, u4⟩ := s3.block svTrvotherfb4 E3.self svTrvotherfb4_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0xFC2 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svTrvotherfb4 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_9 : reg n4 (9 : Fin 32) = op := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by
    rw [rb4, runBlock_reg _ _ _ (20 : Fin 32) s3.zero (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by
    rw [rb4, runBlock_reg _ _ _ (23 : Fin 32) s3.zero (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = ol := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = L0 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_10 : reg n4 a0 = op := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svTrvotherfb4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g4_11 : reg n4 a1 = ol := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svTrvotherfb4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g4_12 : reg n4 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E) := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svTrvotherfb4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g4_13 : reg n4 a3 = BitVec.ofNat 32 0x9 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svTrvotherfb4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m4]; exact w3_64
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m4]; exact w3_7c
  have w4_25c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m4]; exact w3_25c
  have w4_260 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m4]; exact w3_260
  have w4_264 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m4]; exact w3_264
  have w4_268 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m4]; exact w3_268
  have w4_378 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m4]; exact w3_378
  have w4_37c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m4]; exact w3_37c
  have w4_408 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = vcp := by rw [m4]; exact w3_408
  have w4_40c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = vcl := by rw [m4]; exact w3_40c
  clear w3_40c w3_408 w3_37c w3_378 w3_268 w3_264 w3_260 w3_25c w3_7c w3_64 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3 g2_10
  -- 0xFC2: sv_seqEqF
  obtain ⟨n5, c5, s5, rk5, a0_5, K5, fr5⟩ := sv_seqEqF (pl := ol.toNat) (ql := 9)
    F E4 s4 sv_at_fc2 sv_at_fc6 (by decide) (by decide) g4_2
    g4_10 (by rw [g4_11, ofNat_toNat_self]) g4_12 g4_13 (.inl oid_in) (.inr ⟨by decide, by decide⟩)
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keepL K5 (by decide)
  rw [sv_mbRo FW fR4 (.inl oid_in), sv_mbRo FW fR4 (.inr ⟨by decide, by decide⟩)] at a0_5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rk5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk5 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk5 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_4]
  have g5_9 : reg n5 (9 : Fin 32) = op := by rw [rk5 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rk5 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rk5 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [rk5 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [rk5 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [rk5 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [rk5 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [rk5 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [rk5 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = ol := by rw [rk5 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = L0 := by rw [rk5 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := keep_kk4.trans K5
  clear keep_kk4
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K5.w32 (by decide) (by decide)).trans w4_64
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K5.w32 (by decide) (by decide)).trans w4_7c
  have w5_25c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K5.w32 (by decide) (by decide)).trans w4_25c
  have w5_260 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K5.w32 (by decide) (by decide)).trans w4_260
  have w5_264 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K5.w32 (by decide) (by decide)).trans w4_264
  have w5_268 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K5.w32 (by decide) (by decide)).trans w4_268
  have w5_378 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K5.w32 (by decide) (by decide)).trans w4_378
  have w5_37c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K5.w32 (by decide) (by decide)).trans w4_37c
  have w5_408 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = vcp := (K5.w32 (by decide) (by decide)).trans w4_408
  have w5_40c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = vcl := (K5.w32 (by decide) (by decide)).trans w4_40c
  clear w4_40c w4_408 w4_37c w4_378 w4_268 w4_264 w4_260 w4_25c w4_7c w4_64 g4_13 g4_12 g4_11 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 0 := by rw [a0_5, ite_eq_right hmd]; rfl
  -- 0xFCA: branch, taken
  obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0xFF8 sv_at_fca
    (by decide) (by rw [g5_10, s5.zero]; decide)
  have s6 : St n6.mem SV n6 0xFF8 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = op := by rw [u6.regs, g5_9]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 0x0 := by rw [u6.regs, g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = ol := by rw [u6.regs, g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = L0 := by rw [u6.regs, g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m6]; exact w5_64
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m6]; exact w5_7c
  have w6_25c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m6]; exact w5_25c
  have w6_260 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m6]; exact w5_260
  have w6_264 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m6]; exact w5_264
  have w6_268 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m6]; exact w5_268
  have w6_378 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m6]; exact w5_378
  have w6_37c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m6]; exact w5_37c
  have w6_408 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = vcp := by rw [m6]; exact w5_408
  have w6_40c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = vcl := by rw [m6]; exact w5_40c
  clear w5_40c w5_408 w5_37c w5_378 w5_268 w5_264 w5_260 w5_25c w5_7c w5_64 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 K5 a0_5 rk5 s5 c5
  exact .inr ⟨n6, t6, s6, E6, V6, fR6, g6_2, g6_3, g6_4, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, w6_64, w6_7c, w6_25c, w6_260, w6_264, w6_268, w6_378, w6_37c, keep_kk6.mono (by decide)⟩

end C3.RV32.Sv
