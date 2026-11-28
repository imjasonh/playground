import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: a contentType attribute

From 0xF5C to 0xFF8: the attribute is contentType, whose value is the TSTInfo OID with nothing after it; frame offset 0x7C becomes 1.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTrvctf5c : List BInstr :=
  [.aluImm .add a3 x0 0x9, .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (26 : Fin 32), .lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF856]
theorem svTrvctf5c_end : blockEnd sigstoreVerifyCode 0xF5C svTrvctf5c = some 0xF6A := by
  simp only [svTrvctf5c]
  rw [blockEnd, sv_at_f5c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f5e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f60]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f62]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f66]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrvctf74 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x400]
theorem svTrvctf74_end : blockEnd sigstoreVerifyCode 0xF74 svTrvctf74 = some 0xF7C := by
  simp only [svTrvctf74]
  rw [blockEnd, sv_at_f74]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f78]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrvctf90 : List BInstr :=
  [.aluImm .add a3 x0 0xB, .lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF84A]
theorem svTrvctf90_end : blockEnd sigstoreVerifyCode 0xF90 svTrvctf90 = some 0xF9A := by
  simp only [svTrvctf90]
  rw [blockEnd, sv_at_f90]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f92]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_f96]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTrvctfae : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem svTrvctfae_end : blockEnd sigstoreVerifyCode 0xFAE svTrvctfae = some 0xFB0 := by
  simp only [svTrvctfae]
  rw [blockEnd, sv_at_fae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_trvct {B out bp x20 x21 x22 x23 x25 dg flag p0 L0 op ol vcp vcl x24 cp rem sip sil : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xF5C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x18)
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
    (hct : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9) :
    (¬ (∃ op5 ol5, derContent (vcp) (derOid (memBytes M0 (vcp) (vcl).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 (vcp) (vcl).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧ ((vcl) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ op5 ol5, derContent (vcp) (derOid (memBytes M0 (vcp) (vcl).toNat)) = .ok (op5, ol5) ∧
    ∃ to5, derOid (memBytes M0 (vcp) (vcl).toNat) = .ok to5 ∧
    (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧
    ((vcl) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x8), (0x408, 0x8), (0x7C, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xF5C
  obtain ⟨n1, c1, u1⟩ := s0.block svTrvctf5c E0.self svTrvctf5c_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xF6A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTrvctf5c (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_8 : reg n1 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
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
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTrvctf5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = ol := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTrvctf5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x15) := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTrvctf5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_13 : reg n1 a3 = BitVec.ofNat 32 0x9 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTrvctf5c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
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
  have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk2 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1_8]
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
  clear w1_40c w1_408 w1_37c w1_378 w1_268 w1_264 w1_260 w1_25c w1_7c w1_64 g1_13 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  have g2_10 : reg n2 a0 = BitVec.ofNat 32 1 := by rw [a0_2, ite_eq_left hct]; rfl
  -- 0xF72: branch, not taken
  obtain ⟨n3, d3, u3⟩ := s2.notTaken E2.self 0xF74 sv_at_f72
    (by decide) (by rw [g2_10, s2.zero]; decide)
  have s3 : St n3.mem SV n3 0xF74 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u3.regs, g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = op := by rw [u3.regs, g2_9]
  have g3_10 : reg n3 a0 = BitVec.ofNat 32 0x1 := by rw [u3.regs, g2_10]
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
  clear w2_40c w2_408 w2_37c w2_378 w2_268 w2_264 w2_260 w2_25c w2_7c w2_64 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 K2 a0_2 rk2 s2 c2
  -- 0xF74
  obtain ⟨n4, c4, u4⟩ := s3.block svTrvctf74 E3.self svTrvctf74_end
    ⟨trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0xF7C (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svTrvctf74 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
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
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svTrvctf74, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g4_11 : reg n4 a1 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svTrvctf74, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
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
  clear w3_40c w3_408 w3_37c w3_378 w3_268 w3_264 w3_260 w3_25c w3_7c w3_64 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3 g2_10
  -- 0xF7C: sv_oidF
  obtain ⟨n5, c5, s5, sp5, rk5, K5, A5, Ok5, Er5, fr5⟩ := sv_oidF (oc := 0x420) (dc := 0x400)
    F E4 s4 sv_at_f7c sv_at_f80 (by decide) (by decide) g4_2 g4_10 g4_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w4_408 w4_40c vc_in
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keepL K5 (by decide)
  rw [sv_mb fR4 vc_in] at A5 Ok5 Er5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rk5 sp (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk5 (3 : Fin 32) (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk5 (4 : Fin 32) (by decide) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk5 (8 : Fin 32) (by decide) (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = op := by rw [rk5 (9 : Fin 32) (by decide) (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rk5 (18 : Fin 32) (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rk5 (19 : Fin 32) (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [rk5 (20 : Fin 32) (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [rk5 (21 : Fin 32) (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [rk5 (22 : Fin 32) (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [rk5 (23 : Fin 32) (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [rk5 (24 : Fin 32) (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [rk5 (25 : Fin 32) (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = ol := by rw [rk5 (26 : Fin 32) (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = L0 := by rw [rk5 (27 : Fin 32) (by decide) (by decide), g4_27]
  obtain ⟨r5, hr5⟩ : ∃ r, derContent (vcp) (derOid (memBytes M0 (vcp) (vcl).toNat)) = r := ⟨_, rfl⟩
  rcases r5 with er5 | ⟨op5, ol5⟩
  · obtain ⟨z5, ez5⟩ := Er5 er5 hr5
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x8), (0x408, 0x8)] := keep_kk4.trans K5
    clear keep_kk4
    have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K5.w32 (by decide) (by decide)).trans w4_64
    have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K5.w32 (by decide) (by decide)).trans w4_7c
    have w5_25c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K5.w32 (by decide) (by decide)).trans w4_25c
    have w5_260 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K5.w32 (by decide) (by decide)).trans w4_260
    have w5_264 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K5.w32 (by decide) (by decide)).trans w4_264
    have w5_268 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K5.w32 (by decide) (by decide)).trans w4_268
    have w5_378 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K5.w32 (by decide) (by decide)).trans w4_378
    have w5_37c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K5.w32 (by decide) (by decide)).trans w4_37c
    have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z5
    have b5_424 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er5 := ez5
    clear w4_40c w4_408 w4_37c w4_378 w4_268 w4_264 w4_260 w4_25c w4_7c w4_64 g4_11 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
    -- 0xF84: lw
    obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_f84 (off' := 0xF88) (by decide)
      (by rw [g5_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s6 : St n6.mem SV n6 0xF88 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans (.single d6)
    have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : SvCode n6.mem := E5.fr F fr6
    have V6 : SvSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
    have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_8]
    have g6_9 : reg n6 (9 : Fin 32) = op := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
    have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
    have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
    have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = ol := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = L0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
    have g6_10 : reg n6 a0 = 0 := by
      rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g5_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w5_420]
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m6]; exact w5_64
    have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m6]; exact w5_7c
    have w6_25c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m6]; exact w5_25c
    have w6_260 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m6]; exact w5_260
    have w6_264 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m6]; exact w5_264
    have w6_268 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m6]; exact w5_268
    have w6_378 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m6]; exact w5_378
    have w6_37c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m6]; exact w5_37c
    have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m6]; exact w5_420
    have b6_424 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er5 := by rw [m6]; exact b5_424
    clear b5_424 w5_420 w5_37c w5_378 w5_268 w5_264 w5_260 w5_25c w5_7c w5_64 ez5 z5
    -- 0xF88: branch, taken
    obtain ⟨n7, d7, u7⟩ := s6.taken E6.self 0x12AA sv_at_f88
      (by decide) (by rw [g6_10, s6.zero]; rfl)
    have s7 : St n7.mem SV n7 0x12AA (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
    have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u7.regs, g6_8]
    have g7_9 : reg n7 (9 : Fin 32) = op := by rw [u7.regs, g6_9]
    have g7_10 : reg n7 a0 = 0 := by rw [u7.regs, g6_10]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [u7.regs, g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = ol := by rw [u7.regs, g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = L0 := by rw [u7.regs, g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m7]; exact w6_64
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m7]; exact w6_7c
    have w7_25c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m7]; exact w6_25c
    have w7_260 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m7]; exact w6_260
    have w7_264 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m7]; exact w6_264
    have w7_268 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m7]; exact w6_268
    have w7_378 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m7]; exact w6_378
    have w7_37c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m7]; exact w6_37c
    have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m7]; exact w6_420
    have b7_424 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er5 := by rw [m7]; exact b6_424
    clear b6_424 w6_420 w6_37c w6_378 w6_268 w6_264 w6_260 w6_25c w6_7c w6_64 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
    -- 0x12AA: lbu
    obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s8 : St n8.mem SV n8 0x12AE (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
    have g8_9 : reg n8 (9 : Fin 32) = op := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
    have g8_10 : reg n8 a0 = 0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_10]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = ol := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = L0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
    have g8_8 : reg n8 (8 : Fin 32) = (derErrByte er5).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g7_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b7_424]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m8]; exact w7_64
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m8]; exact w7_7c
    have w8_25c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m8]; exact w7_25c
    have w8_260 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m8]; exact w7_260
    have w8_264 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m8]; exact w7_264
    have w8_268 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m8]; exact w7_268
    have w8_378 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m8]; exact w7_378
    have w8_37c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m8]; exact w7_37c
    have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m8]; exact w7_420
    have b8_424 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er5 := by rw [m8]; exact b7_424
    clear b7_424 w7_420 w7_37c w7_378 w7_268 w7_264 w7_260 w7_25c w7_7c w7_64 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    -- 0x12AE: j
    obtain ⟨n9, d9, u9⟩ := s8.jump E8.self sv_at_12ae (off' := 0x7A4) (by decide)
      (by rw [s8.pc]; decide)
    have s9 : St n9.mem SV n9 0x7A4 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = (derErrByte er5).zeroExtend 32 := by rw [u9.regs, g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = op := by rw [u9.regs, g8_9]
    have g9_10 : reg n9 a0 = 0 := by rw [u9.regs, g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = ol := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = L0 := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m9]; exact w8_64
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m9]; exact w8_7c
    have w9_25c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m9]; exact w8_25c
    have w9_260 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m9]; exact w8_260
    have w9_264 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m9]; exact w8_264
    have w9_268 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m9]; exact w8_268
    have w9_378 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m9]; exact w8_378
    have w9_37c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m9]; exact w8_37c
    have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m9]; exact w8_420
    have b9_424 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = derErrByte er5 := by rw [m9]; exact b8_424
    clear b8_424 w8_420 w8_37c w8_378 w8_268 w8_264 w8_260 w8_25c w8_7c w8_64 g8_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    exact .inl ⟨(fun ⟨op5', ol5', h0', _⟩ => by rw [hr5] at h0'; cases h0'), sv_fail F E9 s9 t9 (fun x hx => (fR9 x hx).trans (fM x hx).symm) V9 hret g9_2 g9_18 hO g9_3 g9_4 (by rw [g9_8]; sv_code)⟩
  obtain ⟨to5, ht5, -, -⟩ := oid_ok_content hr5
  obtain ⟨p0_5, p4_5⟩ := Ok5 op5 ol5 hr5
  obtain ⟨d8_5, d12_5⟩ := A5 to5 (derOid_ok_elem ht5)
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x8), (0x408, 0x8)] := keep_kk4.trans K5
  clear keep_kk4
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K5.w32 (by decide) (by decide)).trans w4_64
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K5.w32 (by decide) (by decide)).trans w4_7c
  have w5_25c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K5.w32 (by decide) (by decide)).trans w4_25c
  have w5_260 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K5.w32 (by decide) (by decide)).trans w4_260
  have w5_264 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K5.w32 (by decide) (by decide)).trans w4_264
  have w5_268 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K5.w32 (by decide) (by decide)).trans w4_268
  have w5_378 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K5.w32 (by decide) (by decide)).trans w4_378
  have w5_37c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K5.w32 (by decide) (by decide)).trans w4_37c
  have w5_408 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := d8_5
  have w5_40c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := d12_5
  have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := p0_5
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := p4_5
  clear w4_40c w4_408 w4_37c w4_378 w4_268 w4_264 w4_260 w4_25c w4_7c w4_64 g4_11 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0xF84: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_f84 (off' := 0xF88) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0xF88 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = op := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = ol := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = L0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_10 : reg n6 a0 = op5 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w5_420]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m6]; exact w5_64
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m6]; exact w5_7c
  have w6_25c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m6]; exact w5_25c
  have w6_260 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m6]; exact w5_260
  have w6_264 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m6]; exact w5_264
  have w6_268 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m6]; exact w5_268
  have w6_378 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m6]; exact w5_378
  have w6_37c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m6]; exact w5_37c
  have w6_408 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m6]; exact w5_408
  have w6_40c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m6]; exact w5_40c
  have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m6]; exact w5_420
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m6]; exact w5_424
  clear w5_424 w5_420 w5_40c w5_408 w5_37c w5_378 w5_268 w5_264 w5_260 w5_25c w5_7c w5_64 d12_5 d8_5 p4_5 p0_5 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 Er5 Ok5 A5 K5 rk5 sp5 s5 c5
  -- 0xF88: branch, not taken
  obtain ⟨n7, d7, u7⟩ := s6.notTaken E6.self 0xF8C sv_at_f88
    (by decide) (by rw [g6_10, s6.zero]; exact br_beq_f ((vc_in.oidIn hr5).pos_ne))
  have s7 : St n7.mem SV n7 0xF8C (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u7.regs, g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = op := by rw [u7.regs, g6_9]
  have g7_10 : reg n7 a0 = op5 := by rw [u7.regs, g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [u7.regs, g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = ol := by rw [u7.regs, g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = L0 := by rw [u7.regs, g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m7]; exact w6_64
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m7]; exact w6_7c
  have w7_25c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m7]; exact w6_25c
  have w7_260 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m7]; exact w6_260
  have w7_264 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m7]; exact w6_264
  have w7_268 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m7]; exact w6_268
  have w7_378 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m7]; exact w6_378
  have w7_37c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m7]; exact w6_37c
  have w7_408 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m7]; exact w6_408
  have w7_40c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m7]; exact w6_40c
  have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m7]; exact w6_420
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m7]; exact w6_424
  clear w6_424 w6_420 w6_40c w6_408 w6_37c w6_378 w6_268 w6_264 w6_260 w6_25c w6_7c w6_64 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0xF8C: lw
  obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_f8c (off' := 0xF90) (by decide)
    (by rw [g7_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s8 : St n8.mem SV n8 0xF90 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = op := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
  have g8_10 : reg n8 a0 = op5 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = ol := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = L0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_11 : reg n8 a1 = ol5 := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w7_424]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m8]; exact w7_64
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m8]; exact w7_7c
  have w8_25c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m8]; exact w7_25c
  have w8_260 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m8]; exact w7_260
  have w8_264 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m8]; exact w7_264
  have w8_268 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m8]; exact w7_268
  have w8_378 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m8]; exact w7_378
  have w8_37c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m8]; exact w7_37c
  have w8_408 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m8]; exact w7_408
  have w8_40c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m8]; exact w7_40c
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m8]; exact w7_420
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m8]; exact w7_424
  clear w7_424 w7_420 w7_40c w7_408 w7_37c w7_378 w7_268 w7_264 w7_260 w7_25c w7_7c w7_64 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0xF90
  obtain ⟨n9, c9, u9⟩ := s8.block svTrvctf90 E8.self svTrvctf90_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0xF9A (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svTrvctf90 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = op := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_10 : reg n9 a0 = op5 := by
    rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
  have g9_11 : reg n9 a1 = ol5 := by
    rw [rb9, runBlock_reg _ _ _ a1 s8.zero (by decide), g8_11]
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
  have g9_26 : reg n9 (26 : Fin 32) = ol := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = L0 := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_12 : reg n9 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x9) := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svTrvctf90, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g9_13 : reg n9 a3 = BitVec.ofNat 32 0xB := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svTrvctf90, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m9]; exact w8_64
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m9]; exact w8_7c
  have w9_25c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m9]; exact w8_25c
  have w9_260 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m9]; exact w8_260
  have w9_264 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m9]; exact w8_264
  have w9_268 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m9]; exact w8_268
  have w9_378 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m9]; exact w8_378
  have w9_37c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m9]; exact w8_37c
  have w9_408 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m9]; exact w8_408
  have w9_40c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m9]; exact w8_40c
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m9]; exact w8_420
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m9]; exact w8_424
  clear w8_424 w8_420 w8_40c w8_408 w8_37c w8_378 w8_268 w8_264 w8_260 w8_25c w8_7c w8_64 g8_11 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0xF9A: sv_sneF
  obtain ⟨n10, c10, s10, rk10, a0_10, K10, fr10⟩ := sv_sneF (pl := ol5.toNat) (ql := 11)
    F E9 s9 sv_at_f9a sv_at_f9e (by decide) (by decide) g9_2
    g9_10 (by rw [g9_11, ofNat_toNat_self]) g9_12 g9_13 (.inl (vc_in.oidIn hr5)) (.inr ⟨by decide, by decide⟩)
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keepL K10 (by decide)
  rw [sv_mbRo FW fR9 (.inl (vc_in.oidIn hr5)), sv_mbRo FW fR9 (.inr ⟨by decide, by decide⟩)] at a0_10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rk10 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk10 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk10 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk10 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = op := by rw [rk10 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rk10 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rk10 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [rk10 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rk10 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [rk10 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [rk10 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [rk10 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rk10 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = ol := by rw [rk10 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = L0 := by rw [rk10 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x8), (0x408, 0x8)] := keep_kk9.trans K10
  clear keep_kk9
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K10.w32 (by decide) (by decide)).trans w9_64
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := (K10.w32 (by decide) (by decide)).trans w9_7c
  have w10_25c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K10.w32 (by decide) (by decide)).trans w9_25c
  have w10_260 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K10.w32 (by decide) (by decide)).trans w9_260
  have w10_264 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K10.w32 (by decide) (by decide)).trans w9_264
  have w10_268 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K10.w32 (by decide) (by decide)).trans w9_268
  have w10_378 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K10.w32 (by decide) (by decide)).trans w9_378
  have w10_37c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K10.w32 (by decide) (by decide)).trans w9_37c
  have w10_408 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := (K10.w32 (by decide) (by decide)).trans w9_408
  have w10_40c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := (K10.w32 (by decide) (by decide)).trans w9_40c
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := (K10.w32 (by decide) (by decide)).trans w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := (K10.w32 (by decide) (by decide)).trans w9_424
  clear w9_424 w9_420 w9_40c w9_408 w9_37c w9_378 w9_268 w9_264 w9_260 w9_25c w9_7c w9_64 g9_13 g9_12 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_11 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  by_cases htst : memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11
  rotate_left
  · have g10_10 : reg n10 a0 = BitVec.ofNat 32 1 := by rw [a0_10, ite_eq_right htst]; rfl
    -- 0xFA2: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x7A4 sv_at_fa2
      (by decide) (by rw [g10_10, s10.zero]; decide)
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
    have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = op := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x1 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = ol := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = L0 := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m11]; exact w10_64
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m11]; exact w10_7c
    have w11_25c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m11]; exact w10_25c
    have w11_260 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m11]; exact w10_260
    have w11_264 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m11]; exact w10_264
    have w11_268 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m11]; exact w10_268
    have w11_378 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m11]; exact w10_378
    have w11_37c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m11]; exact w10_37c
    have w11_408 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m11]; exact w10_408
    have w11_40c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m11]; exact w10_40c
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m11]; exact w10_420
    have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m11]; exact w10_424
    clear w10_424 w10_420 w10_40c w10_408 w10_37c w10_378 w10_268 w10_264 w10_260 w10_25c w10_7c w10_64 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 K10 a0_10 rk10 s10 c10
    exact .inl ⟨(fun ⟨op5', ol5', h0', to5', h1', h2', _⟩ => by rw [hr5] at h0'; cases h0'; rw [ht5] at h1'; cases h1'; exact htst h2'), sv_fail F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4 (by rw [g11_8]; sv_code)⟩
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 0 := by rw [a0_10, ite_eq_left htst]; rfl
  -- 0xFA2: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0xFA6 sv_at_fa2
    (by decide) (by rw [g10_10, s10.zero]; decide)
  have s11 : St n11.mem SV n11 0xFA6 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u11.regs, g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = op := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 0x0 := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = ol := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = L0 := by rw [u11.regs, g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m11]; exact w10_64
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m11]; exact w10_7c
  have w11_25c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m11]; exact w10_25c
  have w11_260 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m11]; exact w10_260
  have w11_264 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m11]; exact w10_264
  have w11_268 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m11]; exact w10_268
  have w11_378 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m11]; exact w10_378
  have w11_37c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m11]; exact w10_37c
  have w11_408 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m11]; exact w10_408
  have w11_40c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m11]; exact w10_40c
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m11]; exact w10_424
  clear w10_424 w10_420 w10_40c w10_408 w10_37c w10_378 w10_268 w10_264 w10_260 w10_25c w10_7c w10_64 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 K10 a0_10 rk10 s10 c10
  -- 0xFA6: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_fa6 (off' := 0xFAA) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x40C = B + 0x21A0 + BitVec.ofNat 32 0x40C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0xFAA (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = op := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = ol := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = L0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_10 : reg n12 a0 = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x40C = B + 0x21A0 + BitVec.ofNat 32 0x40C by sv_addr, w11_40c]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m12]; exact w11_64
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m12]; exact w11_7c
  have w12_25c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m12]; exact w11_25c
  have w12_260 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m12]; exact w11_260
  have w12_264 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m12]; exact w11_264
  have w12_268 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m12]; exact w11_268
  have w12_378 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m12]; exact w11_378
  have w12_37c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m12]; exact w11_37c
  have w12_408 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m12]; exact w11_408
  have w12_40c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m12]; exact w11_40c
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m12]; exact w11_424
  clear w11_424 w11_420 w11_40c w11_408 w11_37c w11_378 w11_268 w11_264 w11_260 w11_25c w11_7c w11_64 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11 g10_10
  by_cases hrest0 : (vcl) - BitVec.ofNat 32 (to5.header + to5.len) = 0
  rotate_left
  · -- 0xFAA: branch, taken
    obtain ⟨n13, d13, u13⟩ := s12.taken E12.self 0x7A4 sv_at_faa
      (by decide) (by rw [g12_10, s12.zero]; exact br_bne_t hrest0)
    have s13 : St n13.mem SV n13 0x7A4 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
    have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u13.regs, g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = op := by rw [u13.regs, g12_9]
    have g13_10 : reg n13 a0 = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [u13.regs, g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = ol := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = L0 := by rw [u13.regs, g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m13]; exact w12_64
    have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m13]; exact w12_7c
    have w13_25c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m13]; exact w12_25c
    have w13_260 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m13]; exact w12_260
    have w13_264 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m13]; exact w12_264
    have w13_268 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m13]; exact w12_268
    have w13_378 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m13]; exact w12_378
    have w13_37c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m13]; exact w12_37c
    have w13_408 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m13]; exact w12_408
    have w13_40c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m13]; exact w12_40c
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m13]; exact w12_420
    have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m13]; exact w12_424
    clear w12_424 w12_420 w12_40c w12_408 w12_37c w12_378 w12_268 w12_264 w12_260 w12_25c w12_7c w12_64 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    exact .inl ⟨(fun ⟨op5', ol5', h0', to5', h1', h2', h3', _⟩ => by rw [hr5] at h0'; cases h0'; rw [ht5] at h1'; cases h1'; exact hrest0 h3'), sv_fail F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4 (by rw [g13_8]; sv_code)⟩
  -- 0xFAA: branch, not taken
  obtain ⟨n13, d13, u13⟩ := s12.notTaken E12.self 0xFAE sv_at_faa
    (by decide) (by rw [g12_10, s12.zero]; exact br_bne_f hrest0)
  have s13 : St n13.mem SV n13 0xFAE (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u13.regs, g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = op := by rw [u13.regs, g12_9]
  have g13_10 : reg n13 a0 = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [u13.regs, g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = ol := by rw [u13.regs, g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = L0 := by rw [u13.regs, g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m13]; exact w12_64
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m13]; exact w12_7c
  have w13_25c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m13]; exact w12_25c
  have w13_260 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m13]; exact w12_260
  have w13_264 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m13]; exact w12_264
  have w13_268 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m13]; exact w12_268
  have w13_378 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m13]; exact w12_378
  have w13_37c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m13]; exact w12_37c
  have w13_408 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m13]; exact w12_408
  have w13_40c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m13]; exact w12_40c
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m13]; exact w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m13]; exact w12_424
  clear w12_424 w12_420 w12_40c w12_408 w12_37c w12_378 w12_268 w12_264 w12_260 w12_25c w12_7c w12_64 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0xFAE
  obtain ⟨n14, c14, u14⟩ := s13.block svTrvctfae E13.self svTrvctfae_end
    ⟨trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0xFB0 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svTrvctfae (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by
    rw [rb14, runBlock_reg _ _ _ sp s13.zero (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (3 : Fin 32) s13.zero (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (4 : Fin 32) s13.zero (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = op := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by
    rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by
    rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by
    rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by
    rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by
    rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = ol := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = L0 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTrvctfae, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_10, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x8), (0x408, 0x8)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m14]; exact w13_64
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag := by rw [m14]; exact w13_7c
  have w14_25c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m14]; exact w13_25c
  have w14_260 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m14]; exact w13_260
  have w14_264 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m14]; exact w13_264
  have w14_268 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m14]; exact w13_268
  have w14_378 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m14]; exact w13_378
  have w14_37c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m14]; exact w13_37c
  have w14_408 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m14]; exact w13_408
  have w14_40c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m14]; exact w13_40c
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m14]; exact w13_424
  clear w13_424 w13_420 w13_40c w13_408 w13_37c w13_378 w13_268 w13_264 w13_260 w13_25c w13_7c w13_64 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0xFB0: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_fb0 (off' := 0xFB2) (c := 0x7C)
    (by decide) (by rw [g14_2]; sv_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg15 (8 : Fin 32), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = op := by rw [rg15 (9 : Fin 32), g14_9]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x1 := by rw [rg15 a0, g14_10]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rg15 (20 : Fin 32), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rg15 (21 : Fin 32), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [rg15 (24 : Fin 32), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = ol := by rw [rg15 (26 : Fin 32), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = L0 := by rw [rg15 (27 : Fin 32), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x8), (0x408, 0x8), (0x7C, 0x4)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K15.w32 (by decide) (by decide)).trans w14_64
  have w15_25c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := (K15.w32 (by decide) (by decide)).trans w14_25c
  have w15_260 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := (K15.w32 (by decide) (by decide)).trans w14_260
  have w15_264 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := (K15.w32 (by decide) (by decide)).trans w14_264
  have w15_268 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := (K15.w32 (by decide) (by decide)).trans w14_268
  have w15_378 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K15.w32 (by decide) (by decide)).trans w14_378
  have w15_37c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K15.w32 (by decide) (by decide)).trans w14_37c
  have w15_408 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := (K15.w32 (by decide) (by decide)).trans w14_408
  have w15_40c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := (K15.w32 (by decide) (by decide)).trans w14_40c
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := (K15.w32 (by decide) (by decide)).trans w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := (K15.w32 (by decide) (by decide)).trans w14_424
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x1 := by rw [W15, g14_10]
  clear w14_424 w14_420 w14_40c w14_408 w14_37c w14_378 w14_268 w14_264 w14_260 w14_25c w14_7c w14_64 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0xFB2: j
  obtain ⟨n16, d16, u16⟩ := s15.jump E15.self sv_at_fb2 (off' := 0xFF8) (by decide)
    (by rw [s15.pc]; decide)
  have s16 : St n16.mem SV n16 0xFF8 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u16.regs, g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = op := by rw [u16.regs, g15_9]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x1 := by rw [u16.regs, g15_10]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = ol := by rw [u16.regs, g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = L0 := by rw [u16.regs, g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x8), (0x408, 0x8), (0x7C, 0x4)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m16]; exact w15_64
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x1 := by rw [m16]; exact w15_7c
  have w16_25c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 := by rw [m16]; exact w15_25c
  have w16_260 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 := by rw [m16]; exact w15_260
  have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp := by rw [m16]; exact w15_264
  have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem := by rw [m16]; exact w15_268
  have w16_378 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m16]; exact w15_378
  have w16_37c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m16]; exact w15_37c
  have w16_408 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) := by rw [m16]; exact w15_408
  have w16_40c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = (vcl) - BitVec.ofNat 32 (to5.header + to5.len) := by rw [m16]; exact w15_40c
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op5 := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol5 := by rw [m16]; exact w15_424
  clear w15_7c w15_424 w15_420 w15_40c w15_408 w15_37c w15_378 w15_268 w15_264 w15_260 w15_25c w15_64 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  exact .inr ⟨op5, ol5, hr5, to5, ht5, htst, hrest0, n16, t16, s16, E16, V16, fR16, g16_2, g16_3, g16_4, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, w16_64, w16_7c, w16_25c, w16_260, w16_264, w16_268, w16_378, w16_37c, keep_kk16.mono (by decide)⟩

end C3.RV32.Sv
