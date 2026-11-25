import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the timestamp's eContent

From 0xCC4 to 0xD3E: the encapsulated content has its `[0]` eContent with nothing after it, an octet string with nothing after it, whose address goes to frame offset 0x74 and length to 0x78.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTr4cc4 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x340, .aluImm .add a2 x0 0xA0]
theorem svTr4cc4_end : blockEnd sigstoreVerifyCode 0xCC4 svTr4cc4 = some 0xCCE := by
  simp only [svTr4cc4]
  rw [blockEnd, sv_at_cc4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_cc8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_cca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr4ce2 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTr4ce2_end : blockEnd sigstoreVerifyCode 0xCE2 svTr4ce2 = some 0xCE4 := by
  simp only [svTr4ce2]
  rw [blockEnd, sv_at_ce2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr4cec : List BInstr :=
  [.aluImm .add a5 sp 0x300]
theorem svTr4cec_end : blockEnd sigstoreVerifyCode 0xCEC svTr4cec = some 0xCEE := by
  simp only [svTr4cec]
  rw [blockEnd, sv_at_cec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr4cf0 : List BInstr :=
  [.aluImm .srl a3 a1 0x8, .aluImm .srl a4 a1 0x10]
theorem svTr4cf0_end : blockEnd sigstoreVerifyCode 0xCF0 svTr4cf0 = some 0xCF8 := by
  simp only [svTr4cf0]
  rw [blockEnd, sv_at_cf0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_cf4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr4d06 : List BInstr :=
  [.aluImm .srl a3 a1 0x18]
theorem svTr4d06_end : blockEnd sigstoreVerifyCode 0xD06 svTr4d06 = some 0xD0A := by
  simp only [svTr4d06]
  rw [blockEnd, sv_at_d06]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr4d12 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svTr4d12_end : blockEnd sigstoreVerifyCode 0xD12 svTr4d12 = some 0xD14 := by
  simp only [svTr4d12]
  rw [blockEnd, sv_at_d12]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr4d18 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x350]
theorem svTr4d18_end : blockEnd sigstoreVerifyCode 0xD18 svTr4d18 = some 0xD1E := by
  simp only [svTr4d18]
  rw [blockEnd, sv_at_d18]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_d1c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tr4 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 sdp sdl ecp ecl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xCC4 (reg n0))
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
    (w0_328 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp)
    (w0_32c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl)
    (w0_348 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = ecp)
    (w0_34c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = ecl)
    (sd_in : SvIn B (sdp) (sdl).toNat)
    (ec_in : SvIn B (ecp) (ecl).toNat) :
    (¬ (∃ tl2, derOptRes 0xA0 (memBytes M0 (ecp) (ecl).toNat) = some (.ok tl2) ∧ ((ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ ∃ vp23 vl23, derContent ((ecp) + BitVec.ofNat 32 tl2.header) (derElement 4 (memBytes M0 ((ecp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat)) = .ok (vp23, vl23) ∧ ∃ te23, derElement 4 (memBytes M0 ((ecp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat) = .ok te23 ∧ ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl2, derOptRes 0xA0 (memBytes M0 (ecp) (ecl).toNat) = some (.ok tl2) ∧
    ((ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧
    ∃ vp23 vl23, derContent ((ecp) + BitVec.ofNat 32 tl2.header) (derElement 4 (memBytes M0 ((ecp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat)) = .ok (vp23, vl23) ∧
    ∃ te23, derElement 4 (memBytes M0 ((ecp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat) = .ok te23 ∧
    ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xD3E (reg n') ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = vl23 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4), (0x78, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xCC4
  obtain ⟨n1, c1, u1⟩ := s0.block svTr4cc4 E0.self svTr4cc4_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xCCE (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTr4cc4 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr4cc4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x340 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr4cc4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0xA0 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr4cc4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_328 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m1]; exact w0_328
  have w1_32c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m1]; exact w0_32c
  have w1_348 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = ecp := by rw [m1]; exact w0_348
  have w1_34c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = ecl := by rw [m1]; exact w0_34c
  -- 0xCCE: sv_optF
  obtain ⟨n2, c2, s2, sp2, rk2, K2, R2, fr2⟩ := sv_optF (oc := 0x420) (dc := 0x340) (tag := 0xA0)
    F E1 s1 sv_at_cce sv_at_cd2 (by decide) (by decide) g1_2 g1_10 g1_11 g1_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w1_348 w1_34c ec_in
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [sv_mb fR1 ec_in] at R2
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
  obtain ⟨r2, hr2⟩ : ∃ r, derOptRes 0xA0 (memBytes M0 (ecp) (ecl).toNat) = r := ⟨_, rfl⟩
  rcases r2 with _ | (er2 | tl2)
  · rw [hr2] at R2
    obtain ⟨y0_2, y4_2⟩ := R2
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x18), (0x348, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_328 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K2.w32 (by decide) (by decide)).trans w1_328
    have w2_32c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K2.w32 (by decide) (by decide)).trans w1_32c
    have w2_424 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := y4_2
    have b2_420 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := y0_2
    clear w1_34c w1_348 w1_32c w1_328 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0xCD6: lbu
    obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_cd6 (off' := 0xCDA) (by decide)
    have s3 : St n3.mem SV n3 0xCDA (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_328 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m3]; exact w2_328
    have w3_32c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m3]; exact w2_32c
    have w3_424 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m3]; exact w2_424
    have b3_420 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m3]; exact b2_420
    clear b2_420 w2_424 w2_32c w2_328 y4_2 y0_2
    -- 0xCDA: branch, not taken
    obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0xCDE sv_at_cda
      (by decide) (by rw [g3_10, s3.zero]; decide)
    have s4 : St n4.mem SV n4 0xCDE (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
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
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_328 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m4]; exact w3_328
    have w4_32c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m4]; exact w3_32c
    have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m4]; exact w3_424
    have b4_420 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m4]; exact b3_420
    clear b3_420 w3_424 w3_32c w3_328 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0xCDE: lw
    obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_cde (off' := 0xCE2) (by decide)
      (by rw [g4_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s5 : St n5.mem SV n5 0xCE2 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
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
    have g5_10 : reg n5 a0 = 0 := by
      rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g4_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w4_424]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_328 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m5]; exact w4_328
    have w5_32c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m5]; exact w4_32c
    have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m5]; exact w4_424
    have b5_420 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m5]; exact b4_420
    clear b4_420 w4_424 w4_32c w4_328 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    -- 0xCE2
    obtain ⟨n6, c6, u6⟩ := s5.block svTr4ce2 E5.self svTr4ce2_end
      ⟨trivial, trivial⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have s6 : St n6.mem SV n6 0xCE4 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have rb6 : ∀ q, reg n6 q = (runBlock svTr4ce2 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
    have g6_10 : reg n6 a0 = 0 := by
      rw [rb6, runBlock_reg _ _ _ a0 s5.zero (by decide), g5_10]
    have g6_18 : reg n6 (18 : Fin 32) = out := by
      rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by
      rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = x20 := by
      rw [rb6, runBlock_reg _ _ _ (20 : Fin 32) s5.zero (by decide), g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = x21 := by
      rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = x22 := by
      rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = x23 := by
      rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
    have g6_24 : reg n6 (24 : Fin 32) = x24 := by
      rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
    have g6_25 : reg n6 (25 : Fin 32) = x25 := by
      rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = x26 := by
      rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = x27 := by
      rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
    have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr4ce2, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g5_2, g5_3, g5_4, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m6]; exact w5_328
    have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m6]; exact w5_32c
    have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m6]; exact w5_424
    have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m6]; exact b5_420
    clear b5_420 w5_424 w5_32c w5_328 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    -- 0xCE4: branch, taken
    obtain ⟨n7, d7, u7⟩ := s6.taken E6.self 0x7A4 sv_at_ce4
      (by decide) (by rw [g6_10, s6.zero]; rfl)
    have s7 : St n7.mem SV n7 0x7A4 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
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
    have g7_10 : reg n7 a0 = 0 := by rw [u7.regs, g6_10]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [u7.regs, g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [u7.regs, g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_328 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m7]; exact w6_328
    have w7_32c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m7]; exact w6_32c
    have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m7]; exact w6_424
    have b7_420 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m7]; exact b6_420
    clear b6_420 w6_424 w6_32c w6_328 g6_8 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    exact .inl ⟨(fun ⟨tl2', h0', _⟩ => by rw [hr2] at h0'; cases h0'), sv_fail F E7 s7 t7 (fun x hx => (fR7 x hx).trans (fM x hx).symm) V7 hret g7_2 g7_18 hO g7_3 g7_4⟩
  · rw [hr2] at R2
    obtain ⟨y0_2, -⟩ := R2
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x18), (0x348, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_328 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K2.w32 (by decide) (by decide)).trans w1_328
    have w2_32c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K2.w32 (by decide) (by decide)).trans w1_32c
    have b2_420 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := y0_2
    clear w1_34c w1_348 w1_32c w1_328 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0xCD6: lbu
    obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_cd6 (off' := 0xCDA) (by decide)
    have s3 : St n3.mem SV n3 0xCDA (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
    have g3_10 : reg n3 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b2_420]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_328 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m3]; exact w2_328
    have w3_32c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m3]; exact w2_32c
    have b3_420 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m3]; exact b2_420
    clear b2_420 w2_32c w2_328 y0_2
    -- 0xCDA: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x12A2 sv_at_cda
      (by decide) (by rw [g3_10, s3.zero]; decide)
    have s4 : St n4.mem SV n4 0x12A2 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_10 : reg n4 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u4.regs, g3_10]
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
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_328 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m4]; exact w3_328
    have w4_32c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m4]; exact w3_32c
    have b4_420 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m4]; exact b3_420
    clear b3_420 w3_32c w3_328 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0x12A2: lbu
    obtain ⟨n5, d5, u5⟩ := s4.lbu E4.self sv_at_12a2 (off' := 0x12A6) (by decide)
    have s5 : St n5.mem SV n5 0x12A6 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
    have g5_10 : reg n5 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
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
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_328 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m5]; exact w4_328
    have w5_32c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m5]; exact w4_32c
    have b5_420 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m5]; exact b4_420
    clear b4_420 w4_32c w4_328 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    -- 0x12A6: j
    obtain ⟨n6, d6, u6⟩ := s5.jump E5.self sv_at_12a6 (off' := 0x7A4) (by decide)
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
    have g6_10 : reg n6 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u6.regs, g5_10]
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
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m6]; exact w5_328
    have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m6]; exact w5_32c
    have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m6]; exact b5_420
    clear b5_420 w5_32c w5_328 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    exact .inl ⟨(fun ⟨tl2', h0', _⟩ => by rw [hr2] at h0'; cases h0'), sv_fail F E6 s6 t6 (fun x hx => (fR6 x hx).trans (fM x hx).symm) V6 hret g6_2 g6_18 hO g6_3 g6_4⟩
  rw [hr2] at R2
  obtain ⟨y0_2, y4_2, y8_2, y12_2, y16_2, y20_2, d8_2, d12_2⟩ := R2
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x18), (0x348, 0x8)] := keep_kk1.trans K2
  clear keep_kk1
  have w2_328 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K2.w32 (by decide) (by decide)).trans w1_328
  have w2_32c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K2.w32 (by decide) (by decide)).trans w1_32c
  have w2_348 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := d8_2
  have w2_34c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := d12_2
  have w2_424 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := y4_2
  have w2_428 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := y8_2
  have w2_42c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := y12_2
  have w2_430 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := y16_2
  have b2_420 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := y0_2
  have b2_434 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := y20_2
  clear w1_34c w1_348 w1_32c w1_328 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0xCD6: lbu
  obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_cd6 (off' := 0xCDA) (by decide)
  have s3 : St n3.mem SV n3 0xCDA (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_328 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m3]; exact w2_328
  have w3_32c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m3]; exact w2_32c
  have w3_348 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_348
  have w3_34c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_34c
  have w3_424 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m3]; exact w2_424
  have w3_428 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m3]; exact w2_428
  have w3_42c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m3]; exact w2_42c
  have w3_430 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_430
  have b3_420 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m3]; exact b2_420
  have b3_434 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m3]; exact b2_434
  clear b2_434 b2_420 w2_430 w2_42c w2_428 w2_424 w2_34c w2_348 w2_32c w2_328 d12_2 d8_2 y20_2 y16_2 y12_2 y8_2 y4_2 y0_2 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 K2 rk2 sp2 s2 c2
  -- 0xCDA: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0xCDE sv_at_cda
    (by decide) (by rw [g3_10, s3.zero]; decide)
  have s4 : St n4.mem SV n4 0xCDE (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
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
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_328 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m4]; exact w3_328
  have w4_32c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m4]; exact w3_32c
  have w4_348 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_348
  have w4_34c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_34c
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m4]; exact w3_424
  have w4_428 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m4]; exact w3_428
  have w4_42c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m4]; exact w3_42c
  have w4_430 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_430
  have b4_420 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m4]; exact b3_420
  have b4_434 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m4]; exact b3_434
  clear b3_434 b3_420 w3_430 w3_42c w3_428 w3_424 w3_34c w3_348 w3_32c w3_328 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xCDE: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_cde (off' := 0xCE2) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0xCE2 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
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
  have g5_10 : reg n5 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w4_424]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_328 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m5]; exact w4_328
  have w5_32c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m5]; exact w4_32c
  have w5_348 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_348
  have w5_34c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_34c
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m5]; exact w4_424
  have w5_428 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m5]; exact w4_428
  have w5_42c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m5]; exact w4_42c
  have w5_430 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_430
  have b5_420 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m5]; exact b4_420
  have b5_434 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m5]; exact b4_434
  clear b4_434 b4_420 w4_430 w4_42c w4_428 w4_424 w4_34c w4_348 w4_32c w4_328 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0xCE2
  obtain ⟨n6, c6, u6⟩ := s5.block svTr4ce2 E5.self svTr4ce2_end
    ⟨trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0xCE4 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svTr4ce2 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_10 : reg n6 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by
    rw [rb6, runBlock_reg _ _ _ a0 s5.zero (by decide), g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by
    rw [rb6, runBlock_reg _ _ _ (20 : Fin 32) s5.zero (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by
    rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by
    rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr4ce2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_10, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m6]; exact w5_328
  have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m6]; exact w5_32c
  have w6_348 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_348
  have w6_34c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_34c
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_424
  have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_428
  have w6_42c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m6]; exact w5_42c
  have w6_430 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_430
  have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m6]; exact b5_420
  have b6_434 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m6]; exact b5_434
  clear b5_434 b5_420 w5_430 w5_42c w5_428 w5_424 w5_34c w5_348 w5_32c w5_328 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0xCE4: branch, not taken
  obtain ⟨n7, d7, u7⟩ := s6.notTaken E6.self 0xCE8 sv_at_ce4
    (by decide) (by rw [g6_10, s6.zero]; exact br_beq_f (ec_in.ok_ne (opt_ok_elem hr2)))
  have s7 : St n7.mem SV n7 0xCE8 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
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
  have g7_10 : reg n7 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [u7.regs, g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [u7.regs, g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [u7.regs, g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_328 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m7]; exact w6_328
  have w7_32c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m7]; exact w6_32c
  have w7_348 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_348
  have w7_34c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_34c
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m7]; exact w6_424
  have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m7]; exact w6_428
  have w7_42c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m7]; exact w6_42c
  have w7_430 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_430
  have b7_420 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m7]; exact b6_420
  have b7_434 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m7]; exact b6_434
  clear b6_434 b6_420 w6_430 w6_42c w6_428 w6_424 w6_34c w6_348 w6_32c w6_328 g6_8 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0xCE8: lw
  obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_ce8 (off' := 0xCEC) (by decide)
    (by rw [g7_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s8 : St n8.mem SV n8 0xCEC (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
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
  have g8_10 : reg n8 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [u8.regs, upd_ne (by decide) (by decide), g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_11 : reg n8 a1 = BitVec.ofNat 32 tl2.len := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w7_428]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_328 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m8]; exact w7_328
  have w8_32c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m8]; exact w7_32c
  have w8_348 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_348
  have w8_34c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_34c
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m8]; exact w7_424
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m8]; exact w7_428
  have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m8]; exact w7_42c
  have w8_430 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_430
  have b8_420 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m8]; exact b7_420
  have b8_434 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m8]; exact b7_434
  clear b7_434 b7_420 w7_430 w7_42c w7_428 w7_424 w7_34c w7_348 w7_32c w7_328 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0xCEC
  obtain ⟨n9, c9, u9⟩ := s8.block svTr4cec E8.self svTr4cec_end
    ⟨trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0xCEE (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svTr4cec (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_10 : reg n9 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by
    rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
  have g9_11 : reg n9 a1 = BitVec.ofNat 32 tl2.len := by
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
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_15 : reg n9 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svTr4cec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_10, g8_11, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_328 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m9]; exact w8_328
  have w9_32c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m9]; exact w8_32c
  have w9_348 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_348
  have w9_34c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_34c
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m9]; exact w8_424
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m9]; exact w8_428
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m9]; exact w8_42c
  have w9_430 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_430
  have b9_420 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m9]; exact b8_420
  have b9_434 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m9]; exact b8_434
  clear b8_434 b8_420 w8_430 w8_42c w8_428 w8_424 w8_34c w8_348 w8_32c w8_328 g8_11 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0xCEE: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_cee (off' := 0xCF0) (by decide)
    (by rw [g9_15, show B + 0x21A0 + BitVec.ofNat 32 0x300 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x34C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s10 : St n10.mem SV n10 0xCF0 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
  have g10_10 : reg n10 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [u10.regs, upd_ne (by decide) (by decide), g9_10]
  have g10_11 : reg n10 a1 = BitVec.ofNat 32 tl2.len := by rw [u10.regs, upd_ne (by decide) (by decide), g9_11]
  have g10_15 : reg n10 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_15]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
  have g10_12 : reg n10 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_15, show B + 0x21A0 + BitVec.ofNat 32 0x300 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x34C by sv_addr, w9_34c]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_328 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m10]; exact w9_328
  have w10_32c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m10]; exact w9_32c
  have w10_348 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_348
  have w10_34c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_34c
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m10]; exact w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m10]; exact w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m10]; exact w9_42c
  have w10_430 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_430
  have b10_420 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m10]; exact b9_420
  have b10_434 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m10]; exact b9_434
  clear b9_434 b9_420 w9_430 w9_42c w9_428 w9_424 w9_34c w9_348 w9_32c w9_328 g9_15 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_11 g9_10 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0xCF0
  obtain ⟨n11, c11, u11⟩ := s10.block svTr4cf0 E10.self svTr4cf0_end
    ⟨trivial, trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0xCF8 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svTr4cf0 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb11, runBlock_reg _ _ _ (8 : Fin 32) s10.zero (by decide), g10_8]
  have g11_10 : reg n11 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by
    rw [rb11, runBlock_reg _ _ _ a0 s10.zero (by decide), g10_10]
  have g11_11 : reg n11 a1 = BitVec.ofNat 32 tl2.len := by
    rw [rb11, runBlock_reg _ _ _ a1 s10.zero (by decide), g10_11]
  have g11_12 : reg n11 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [rb11, runBlock_reg _ _ _ a2 s10.zero (by decide), g10_12]
  have g11_15 : reg n11 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb11, runBlock_reg _ _ _ a5 s10.zero (by decide), g10_15]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_13 : reg n11 a3 = (BitVec.ofNat 32 tl2.len) >>> 8 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svTr4cf0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_10, g10_11, g10_12, g10_15, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g11_14 : reg n11 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svTr4cf0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_10, g10_11, g10_12, g10_15, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x18), (0x348, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m11]; exact w10_328
  have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m11]; exact w10_32c
  have w11_348 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_348
  have w11_34c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_34c
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m11]; exact w10_42c
  have w11_430 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_430
  have b11_420 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m11]; exact b10_420
  have b11_434 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m11]; exact b10_434
  clear b10_434 b10_420 w10_430 w10_42c w10_428 w10_424 w10_34c w10_348 w10_32c w10_328 g10_12 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_15 g10_11 g10_10 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0xCF8: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_cf8 (off' := 0xCFA) (c := 0x350)
    (by decide) (by rw [g11_15]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg12 (8 : Fin 32), g11_8]
  have g12_10 : reg n12 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [rg12 a0, g11_10]
  have g12_11 : reg n12 a1 = BitVec.ofNat 32 tl2.len := by rw [rg12 a1, g11_11]
  have g12_12 : reg n12 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg12 a2, g11_12]
  have g12_13 : reg n12 a3 = (BitVec.ofNat 32 tl2.len) >>> 8 := by rw [rg12 a3, g11_13]
  have g12_14 : reg n12 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by rw [rg12 a4, g11_14]
  have g12_15 : reg n12 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg12 a5, g11_15]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [rg12 (20 : Fin 32), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [rg12 (23 : Fin 32), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K12.w32 (by decide) (by decide)).trans w11_328
  have w12_32c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K12.w32 (by decide) (by decide)).trans w11_32c
  have w12_348 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K12.w32 (by decide) (by decide)).trans w11_348
  have w12_34c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K12.w32 (by decide) (by decide)).trans w11_34c
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := (K12.w32 (by decide) (by decide)).trans w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K12.w32 (by decide) (by decide)).trans w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K12.w32 (by decide) (by decide)).trans w11_42c
  have w12_430 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K12.w32 (by decide) (by decide)).trans w11_430
  have b12_420 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K12.b8 (by decide) (by decide)).trans b11_420
  have b12_434 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K12.b8 (by decide) (by decide)).trans b11_434
  have w12_350 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [W12, g11_10]
  clear b11_434 b11_420 w11_430 w11_42c w11_428 w11_424 w11_34c w11_348 w11_32c w11_328 g11_14 g11_13 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_15 g11_12 g11_11 g11_10 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0xCFA: sb
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sb F E12 s12 sv_at_cfa (off' := 0xCFE) (c := 0x354)
    (by decide) (by rw [g12_2]; sv_addr) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg13 (8 : Fin 32), g12_8]
  have g13_10 : reg n13 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [rg13 a0, g12_10]
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 tl2.len := by rw [rg13 a1, g12_11]
  have g13_12 : reg n13 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg13 a2, g12_12]
  have g13_13 : reg n13 a3 = (BitVec.ofNat 32 tl2.len) >>> 8 := by rw [rg13 a3, g12_13]
  have g13_14 : reg n13 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by rw [rg13 a4, g12_14]
  have g13_15 : reg n13 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg13 a5, g12_15]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [rg13 (20 : Fin 32), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [rg13 (21 : Fin 32), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [rg13 (22 : Fin 32), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [rg13 (23 : Fin 32), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [rg13 (24 : Fin 32), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [rg13 (25 : Fin 32), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rg13 (26 : Fin 32), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [rg13 (27 : Fin 32), g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K13.w32 (by decide) (by decide)).trans w12_328
  have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K13.w32 (by decide) (by decide)).trans w12_32c
  have w13_348 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_348
  have w13_34c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_34c
  have w13_350 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K13.w32 (by decide) (by decide)).trans w12_350
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := (K13.w32 (by decide) (by decide)).trans w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K13.w32 (by decide) (by decide)).trans w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K13.w32 (by decide) (by decide)).trans w12_42c
  have w13_430 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_430
  have b13_420 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K13.b8 (by decide) (by decide)).trans b12_420
  have b13_434 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K13.b8 (by decide) (by decide)).trans b12_434
  have b13_354 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [W13, g12_11]
  clear w12_350 b12_434 b12_420 w12_430 w12_42c w12_428 w12_424 w12_34c w12_348 w12_32c w12_328 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_15 g12_14 g12_13 g12_12 g12_11 g12_10 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0xCFE: sb
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sb F E13 s13 sv_at_cfe (off' := 0xD02) (c := 0x355)
    (by decide) (by rw [g13_2]; sv_addr) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg14 (8 : Fin 32), g13_8]
  have g14_10 : reg n14 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 tl2.len := by rw [rg14 a1, g13_11]
  have g14_12 : reg n14 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg14 a2, g13_12]
  have g14_13 : reg n14 a3 = (BitVec.ofNat 32 tl2.len) >>> 8 := by rw [rg14 a3, g13_13]
  have g14_14 : reg n14 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by rw [rg14 a4, g13_14]
  have g14_15 : reg n14 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg14 a5, g13_15]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K14.w32 (by decide) (by decide)).trans w13_328
  have w14_32c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K14.w32 (by decide) (by decide)).trans w13_32c
  have w14_348 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K14.w32 (by decide) (by decide)).trans w13_348
  have w14_34c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K14.w32 (by decide) (by decide)).trans w13_34c
  have w14_350 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K14.w32 (by decide) (by decide)).trans w13_350
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := (K14.w32 (by decide) (by decide)).trans w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K14.w32 (by decide) (by decide)).trans w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K14.w32 (by decide) (by decide)).trans w13_42c
  have w14_430 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K14.w32 (by decide) (by decide)).trans w13_430
  have b14_354 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_354
  have b14_420 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K14.b8 (by decide) (by decide)).trans b13_420
  have b14_434 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K14.b8 (by decide) (by decide)).trans b13_434
  have b14_355 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x355) = ((BitVec.ofNat 32 tl2.len) >>> 8).extractLsb' 0 8 := by rw [W14, g13_13]
  clear b13_354 b13_434 b13_420 w13_430 w13_42c w13_428 w13_424 w13_350 w13_34c w13_348 w13_32c w13_328 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_15 g13_14 g13_13 g13_12 g13_11 g13_10 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0xD02: sb
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sb F E14 s14 sv_at_d02 (off' := 0xD06) (c := 0x356)
    (by decide) (by rw [g14_2]; sv_addr) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg15 (8 : Fin 32), g14_8]
  have g15_10 : reg n15 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [rg15 a0, g14_10]
  have g15_11 : reg n15 a1 = BitVec.ofNat 32 tl2.len := by rw [rg15 a1, g14_11]
  have g15_12 : reg n15 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg15 a2, g14_12]
  have g15_13 : reg n15 a3 = (BitVec.ofNat 32 tl2.len) >>> 8 := by rw [rg15 a3, g14_13]
  have g15_14 : reg n15 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by rw [rg15 a4, g14_14]
  have g15_15 : reg n15 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg15 a5, g14_15]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rg15 (20 : Fin 32), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rg15 (21 : Fin 32), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [rg15 (24 : Fin 32), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [rg15 (26 : Fin 32), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [rg15 (27 : Fin 32), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K15.w32 (by decide) (by decide)).trans w14_328
  have w15_32c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K15.w32 (by decide) (by decide)).trans w14_32c
  have w15_348 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K15.w32 (by decide) (by decide)).trans w14_348
  have w15_34c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K15.w32 (by decide) (by decide)).trans w14_34c
  have w15_350 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K15.w32 (by decide) (by decide)).trans w14_350
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := (K15.w32 (by decide) (by decide)).trans w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K15.w32 (by decide) (by decide)).trans w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K15.w32 (by decide) (by decide)).trans w14_42c
  have w15_430 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K15.w32 (by decide) (by decide)).trans w14_430
  have b15_354 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K15.b8 (by decide) (by decide)).trans b14_354
  have b15_355 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x355) = ((BitVec.ofNat 32 tl2.len) >>> 8).extractLsb' 0 8 := (K15.b8 (by decide) (by decide)).trans b14_355
  have b15_420 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K15.b8 (by decide) (by decide)).trans b14_420
  have b15_434 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K15.b8 (by decide) (by decide)).trans b14_434
  have b15_356 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x356) = ((BitVec.ofNat 32 tl2.len) >>> 16).extractLsb' 0 8 := by rw [W15, g14_14]
  clear b14_355 b14_434 b14_420 b14_354 w14_430 w14_42c w14_428 w14_424 w14_350 w14_34c w14_348 w14_32c w14_328 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_15 g14_14 g14_13 g14_12 g14_11 g14_10 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0xD06
  obtain ⟨n16, c16, u16⟩ := s15.block svTr4d06 E15.self svTr4d06_end
    ⟨trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0xD0A (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svTr4d06 (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
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
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb16, runBlock_reg _ _ _ (8 : Fin 32) s15.zero (by decide), g15_8]
  have g16_10 : reg n16 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by
    rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
  have g16_11 : reg n16 a1 = BitVec.ofNat 32 tl2.len := by
    rw [rb16, runBlock_reg _ _ _ a1 s15.zero (by decide), g15_11]
  have g16_12 : reg n16 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [rb16, runBlock_reg _ _ _ a2 s15.zero (by decide), g15_12]
  have g16_14 : reg n16 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by
    rw [rb16, runBlock_reg _ _ _ a4 s15.zero (by decide), g15_14]
  have g16_15 : reg n16 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb16, runBlock_reg _ _ _ a5 s15.zero (by decide), g15_15]
  have g16_18 : reg n16 (18 : Fin 32) = out := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by
    rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by
    rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by
    rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by
    rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by
    rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = x27 := by
    rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
  have g16_13 : reg n16 a3 = (BitVec.ofNat 32 tl2.len) >>> 24 := by
    rw [rb16, ← g15_11]; rfl
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_328 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m16]; exact w15_328
  have w16_32c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m16]; exact w15_32c
  have w16_348 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_348
  have w16_34c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_34c
  have w16_350 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_350
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m16]; exact w15_42c
  have w16_430 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_430
  have b16_354 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m16]; exact b15_354
  have b16_355 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x355) = ((BitVec.ofNat 32 tl2.len) >>> 8).extractLsb' 0 8 := by rw [m16]; exact b15_355
  have b16_356 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x356) = ((BitVec.ofNat 32 tl2.len) >>> 16).extractLsb' 0 8 := by rw [m16]; exact b15_356
  have b16_420 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m16]; exact b15_420
  have b16_434 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m16]; exact b15_434
  clear b15_356 b15_434 b15_420 b15_355 b15_354 w15_430 w15_42c w15_428 w15_424 w15_350 w15_34c w15_348 w15_32c w15_328 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_15 g15_14 g15_13 g15_12 g15_11 g15_10 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0xD0A: sb
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sb F E16 s16 sv_at_d0a (off' := 0xD0E) (c := 0x357)
    (by decide) (by rw [g16_2]; sv_addr) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg17 (8 : Fin 32), g16_8]
  have g17_10 : reg n17 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [rg17 a0, g16_10]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 tl2.len := by rw [rg17 a1, g16_11]
  have g17_12 : reg n17 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg17 a2, g16_12]
  have g17_13 : reg n17 a3 = (BitVec.ofNat 32 tl2.len) >>> 24 := by rw [rg17 a3, g16_13]
  have g17_14 : reg n17 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by rw [rg17 a4, g16_14]
  have g17_15 : reg n17 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg17 a5, g16_15]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rg17 (18 : Fin 32), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rg17 (19 : Fin 32), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [rg17 (20 : Fin 32), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [rg17 (21 : Fin 32), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [rg17 (22 : Fin 32), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [rg17 (23 : Fin 32), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [rg17 (24 : Fin 32), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [rg17 (25 : Fin 32), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [rg17 (26 : Fin 32), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [rg17 (27 : Fin 32), g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_328 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K17.w32 (by decide) (by decide)).trans w16_328
  have w17_32c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K17.w32 (by decide) (by decide)).trans w16_32c
  have w17_348 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K17.w32 (by decide) (by decide)).trans w16_348
  have w17_34c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K17.w32 (by decide) (by decide)).trans w16_34c
  have w17_350 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K17.w32 (by decide) (by decide)).trans w16_350
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := (K17.w32 (by decide) (by decide)).trans w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K17.w32 (by decide) (by decide)).trans w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K17.w32 (by decide) (by decide)).trans w16_42c
  have w17_430 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K17.w32 (by decide) (by decide)).trans w16_430
  have b17_354 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K17.b8 (by decide) (by decide)).trans b16_354
  have b17_355 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x355) = ((BitVec.ofNat 32 tl2.len) >>> 8).extractLsb' 0 8 := (K17.b8 (by decide) (by decide)).trans b16_355
  have b17_356 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x356) = ((BitVec.ofNat 32 tl2.len) >>> 16).extractLsb' 0 8 := (K17.b8 (by decide) (by decide)).trans b16_356
  have b17_420 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K17.b8 (by decide) (by decide)).trans b16_420
  have b17_434 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K17.b8 (by decide) (by decide)).trans b16_434
  have b17_357 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x357) = ((BitVec.ofNat 32 tl2.len) >>> 24).extractLsb' 0 8 := by rw [W17, g16_13]
  clear b16_434 b16_420 b16_356 b16_355 b16_354 w16_430 w16_42c w16_428 w16_424 w16_350 w16_34c w16_348 w16_32c w16_328 g16_13 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_15 g16_14 g16_12 g16_11 g16_10 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  -- 0xD0E: sw
  obtain ⟨n18, d18, s18, fr18, K18, W18, rg18⟩ := sv_sw F E17 s17 sv_at_d0e (off' := 0xD10) (c := 0x358)
    (by decide) (by rw [g17_15]; sv_addr) (by decide) (by decide)
  have t18 : Steps n0 n18 := t17.trans d18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rg18 sp, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg18 (3 : Fin 32), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg18 (4 : Fin 32), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg18 (8 : Fin 32), g17_8]
  have g18_10 : reg n18 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [rg18 a0, g17_10]
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 tl2.len := by rw [rg18 a1, g17_11]
  have g18_12 : reg n18 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg18 a2, g17_12]
  have g18_13 : reg n18 a3 = (BitVec.ofNat 32 tl2.len) >>> 24 := by rw [rg18 a3, g17_13]
  have g18_14 : reg n18 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by rw [rg18 a4, g17_14]
  have g18_15 : reg n18 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg18 a5, g17_15]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rg18 (18 : Fin 32), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rg18 (19 : Fin 32), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [rg18 (20 : Fin 32), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [rg18 (21 : Fin 32), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [rg18 (22 : Fin 32), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [rg18 (23 : Fin 32), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [rg18 (24 : Fin 32), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [rg18 (25 : Fin 32), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [rg18 (26 : Fin 32), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [rg18 (27 : Fin 32), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_328 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K18.w32 (by decide) (by decide)).trans w17_328
  have w18_32c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K18.w32 (by decide) (by decide)).trans w17_32c
  have w18_348 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K18.w32 (by decide) (by decide)).trans w17_348
  have w18_34c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K18.w32 (by decide) (by decide)).trans w17_34c
  have w18_350 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K18.w32 (by decide) (by decide)).trans w17_350
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := (K18.w32 (by decide) (by decide)).trans w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K18.w32 (by decide) (by decide)).trans w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K18.w32 (by decide) (by decide)).trans w17_42c
  have w18_430 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K18.w32 (by decide) (by decide)).trans w17_430
  have b18_354 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_354
  have b18_355 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x355) = ((BitVec.ofNat 32 tl2.len) >>> 8).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_355
  have b18_356 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x356) = ((BitVec.ofNat 32 tl2.len) >>> 16).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_356
  have b18_357 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x357) = ((BitVec.ofNat 32 tl2.len) >>> 24).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_357
  have b18_420 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K18.b8 (by decide) (by decide)).trans b17_420
  have b18_434 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K18.b8 (by decide) (by decide)).trans b17_434
  have w18_358 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [W18, g17_10]
  clear b17_357 b17_434 b17_420 b17_356 b17_355 b17_354 w17_430 w17_42c w17_428 w17_424 w17_350 w17_34c w17_348 w17_32c w17_328 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_15 g17_14 g17_13 g17_12 g17_11 g17_10 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0xD10: sw
  obtain ⟨n19, d19, s19, fr19, K19, W19, rg19⟩ := sv_sw F E18 s18 sv_at_d10 (off' := 0xD12) (c := 0x35C)
    (by decide) (by rw [g18_15]; sv_addr) (by decide) (by decide)
  have t19 : Steps n0 n19 := t18.trans d19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rg19 sp, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg19 (3 : Fin 32), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg19 (4 : Fin 32), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg19 (8 : Fin 32), g18_8]
  have g19_10 : reg n19 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [rg19 a0, g18_10]
  have g19_11 : reg n19 a1 = BitVec.ofNat 32 tl2.len := by rw [rg19 a1, g18_11]
  have g19_12 : reg n19 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg19 a2, g18_12]
  have g19_13 : reg n19 a3 = (BitVec.ofNat 32 tl2.len) >>> 24 := by rw [rg19 a3, g18_13]
  have g19_14 : reg n19 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by rw [rg19 a4, g18_14]
  have g19_15 : reg n19 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg19 a5, g18_15]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rg19 (18 : Fin 32), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rg19 (19 : Fin 32), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [rg19 (20 : Fin 32), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [rg19 (21 : Fin 32), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [rg19 (22 : Fin 32), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [rg19 (23 : Fin 32), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [rg19 (24 : Fin 32), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [rg19 (25 : Fin 32), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [rg19 (26 : Fin 32), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [rg19 (27 : Fin 32), g18_27]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4)] := keep_kk18.trans K19.toL
  clear keep_kk18
  have w19_328 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K19.w32 (by decide) (by decide)).trans w18_328
  have w19_32c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K19.w32 (by decide) (by decide)).trans w18_32c
  have w19_348 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K19.w32 (by decide) (by decide)).trans w18_348
  have w19_34c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K19.w32 (by decide) (by decide)).trans w18_34c
  have w19_350 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K19.w32 (by decide) (by decide)).trans w18_350
  have w19_358 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = (ecp) + BitVec.ofNat 32 tl2.header := (K19.w32 (by decide) (by decide)).trans w18_358
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := (K19.w32 (by decide) (by decide)).trans w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K19.w32 (by decide) (by decide)).trans w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K19.w32 (by decide) (by decide)).trans w18_42c
  have w19_430 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K19.w32 (by decide) (by decide)).trans w18_430
  have b19_354 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_354
  have b19_355 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x355) = ((BitVec.ofNat 32 tl2.len) >>> 8).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_355
  have b19_356 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x356) = ((BitVec.ofNat 32 tl2.len) >>> 16).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_356
  have b19_357 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x357) = ((BitVec.ofNat 32 tl2.len) >>> 24).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_357
  have b19_420 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := (K19.b8 (by decide) (by decide)).trans b18_420
  have b19_434 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K19.b8 (by decide) (by decide)).trans b18_434
  have w19_35c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = BitVec.ofNat 32 tl2.len := by rw [W19, g18_11]
  clear w18_358 b18_434 b18_420 b18_357 b18_356 b18_355 b18_354 w18_430 w18_42c w18_428 w18_424 w18_350 w18_34c w18_348 w18_32c w18_328 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_15 g18_14 g18_13 g18_12 g18_11 g18_10 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
  -- 0xD12
  obtain ⟨n20, c20, u20⟩ := s19.block svTr4d12 E19.self svTr4d12_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0xD14 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svTr4d12 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_10 : reg n20 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by
    rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 tl2.len := by
    rw [rb20, runBlock_reg _ _ _ a1 s19.zero (by decide), g19_11]
  have g20_12 : reg n20 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [rb20, runBlock_reg _ _ _ a2 s19.zero (by decide), g19_12]
  have g20_13 : reg n20 a3 = (BitVec.ofNat 32 tl2.len) >>> 24 := by
    rw [rb20, runBlock_reg _ _ _ a3 s19.zero (by decide), g19_13]
  have g20_14 : reg n20 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by
    rw [rb20, runBlock_reg _ _ _ a4 s19.zero (by decide), g19_14]
  have g20_15 : reg n20 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb20, runBlock_reg _ _ _ a5 s19.zero (by decide), g19_15]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by
    rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svTr4d12, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_10, g19_11, g19_12, g19_13, g19_14, g19_15, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_328 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m20]; exact w19_328
  have w20_32c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m20]; exact w19_32c
  have w20_348 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_348
  have w20_34c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_34c
  have w20_350 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m20]; exact w19_350
  have w20_358 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m20]; exact w19_358
  have w20_35c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = BitVec.ofNat 32 tl2.len := by rw [m20]; exact w19_35c
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m20]; exact w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m20]; exact w19_42c
  have w20_430 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m20]; exact w19_430
  have b20_354 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m20]; exact b19_354
  have b20_355 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x355) = ((BitVec.ofNat 32 tl2.len) >>> 8).extractLsb' 0 8 := by rw [m20]; exact b19_355
  have b20_356 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x356) = ((BitVec.ofNat 32 tl2.len) >>> 16).extractLsb' 0 8 := by rw [m20]; exact b19_356
  have b20_357 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x357) = ((BitVec.ofNat 32 tl2.len) >>> 24).extractLsb' 0 8 := by rw [m20]; exact b19_357
  have b20_420 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m20]; exact b19_420
  have b20_434 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m20]; exact b19_434
  clear w19_35c b19_434 b19_420 b19_357 b19_356 b19_355 b19_354 w19_430 w19_42c w19_428 w19_424 w19_358 w19_350 w19_34c w19_348 w19_32c w19_328 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_15 g19_14 g19_13 g19_12 g19_11 g19_10 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 rg19 W19 K19 fr19 s19 d19
  have w20_354 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := ld_of_shr_bytes b20_354
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x354 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x355 by sv_addr]; exact b20_355)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x354 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x356 by sv_addr]; exact b20_356)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x354 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x357 by sv_addr]; exact b20_357)
  by_cases hrest0 : (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0
  rotate_left
  · -- 0xD14: branch, taken
    obtain ⟨n21, d21, u21⟩ := s20.taken E20.self 0x7A4 sv_at_d14
      (by decide) (by rw [g20_12, s20.zero]; exact br_bne_t hrest0)
    have s21 : St n21.mem SV n21 0x7A4 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u21.regs, g20_8]
    have g21_10 : reg n21 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [u21.regs, g20_10]
    have g21_11 : reg n21 a1 = BitVec.ofNat 32 tl2.len := by rw [u21.regs, g20_11]
    have g21_12 : reg n21 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u21.regs, g20_12]
    have g21_13 : reg n21 a3 = (BitVec.ofNat 32 tl2.len) >>> 24 := by rw [u21.regs, g20_13]
    have g21_14 : reg n21 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by rw [u21.regs, g20_14]
    have g21_15 : reg n21 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u21.regs, g20_15]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [u21.regs, g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, g20_27]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m21]; exact w20_328
    have w21_32c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m21]; exact w20_32c
    have w21_348 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_348
    have w21_34c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_34c
    have w21_350 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_350
    have w21_354 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_354
    have w21_358 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_358
    have w21_35c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_35c
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m21]; exact w20_42c
    have w21_430 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_430
    have b21_420 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m21]; exact b20_420
    have b21_434 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m21]; exact b20_434
    clear b20_434 b20_420 b20_357 b20_356 b20_355 b20_354 w20_430 w20_42c w20_428 w20_424 w20_35c w20_358 w20_350 w20_34c w20_348 w20_32c w20_328 g20_8 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_15 g20_14 g20_13 g20_12 g20_11 g20_10 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    exact .inl ⟨(fun ⟨tl2', h0', h1', _⟩ => by rw [hr2] at h0'; cases h0'; exact hrest0 h1'), sv_fail F E21 s21 t21 (fun x hx => (fR21 x hx).trans (fM x hx).symm) V21 hret g21_2 g21_18 hO g21_3 g21_4⟩
  -- 0xD14: branch, not taken
  obtain ⟨n21, d21, u21⟩ := s20.notTaken E20.self 0xD18 sv_at_d14
    (by decide) (by rw [g20_12, s20.zero]; exact br_bne_f hrest0)
  have s21 : St n21.mem SV n21 0xD18 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u21.regs, g20_8]
  have g21_10 : reg n21 a0 = (ecp) + BitVec.ofNat 32 tl2.header := by rw [u21.regs, g20_10]
  have g21_11 : reg n21 a1 = BitVec.ofNat 32 tl2.len := by rw [u21.regs, g20_11]
  have g21_12 : reg n21 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u21.regs, g20_12]
  have g21_13 : reg n21 a3 = (BitVec.ofNat 32 tl2.len) >>> 24 := by rw [u21.regs, g20_13]
  have g21_14 : reg n21 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by rw [u21.regs, g20_14]
  have g21_15 : reg n21 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [u21.regs, g20_15]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [u21.regs, g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, g20_27]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m21]; exact w20_328
  have w21_32c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m21]; exact w20_32c
  have w21_348 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_348
  have w21_34c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_34c
  have w21_350 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_350
  have w21_354 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_354
  have w21_358 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_358
  have w21_35c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_35c
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m21]; exact w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m21]; exact w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m21]; exact w20_42c
  have w21_430 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m21]; exact w20_430
  have b21_420 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m21]; exact b20_420
  have b21_434 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m21]; exact b20_434
  clear b20_434 b20_420 b20_357 b20_356 b20_355 b20_354 w20_430 w20_42c w20_428 w20_424 w20_35c w20_358 w20_350 w20_34c w20_348 w20_32c w20_328 g20_8 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_15 g20_14 g20_13 g20_12 g20_11 g20_10 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0xD18
  obtain ⟨n22, c22, u22⟩ := s21.block svTr4d18 E21.self svTr4d18_end
    ⟨trivial, trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0xD1E (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svTr4d18 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
  have g22_12 : reg n22 a2 = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [rb22, runBlock_reg _ _ _ a2 s21.zero (by decide), g21_12]
  have g22_13 : reg n22 a3 = (BitVec.ofNat 32 tl2.len) >>> 24 := by
    rw [rb22, runBlock_reg _ _ _ a3 s21.zero (by decide), g21_13]
  have g22_14 : reg n22 a4 = (BitVec.ofNat 32 tl2.len) >>> 16 := by
    rw [rb22, runBlock_reg _ _ _ a4 s21.zero (by decide), g21_14]
  have g22_15 : reg n22 a5 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb22, runBlock_reg _ _ _ a5 s21.zero (by decide), g21_15]
  have g22_18 : reg n22 (18 : Fin 32) = out := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by
    rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by
    rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by
    rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by
    rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = x24 := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by
    rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_10 : reg n22 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svTr4d18, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_10, g21_11, g21_12, g21_13, g21_14, g21_15, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g22_11 : reg n22 a1 = B + 0x21A0 + BitVec.ofNat 32 0x350 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svTr4d18, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_10, g21_11, g21_12, g21_13, g21_14, g21_15, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m22]; exact w21_328
  have w22_32c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m22]; exact w21_32c
  have w22_348 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_348
  have w22_34c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_34c
  have w22_350 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m22]; exact w21_350
  have w22_354 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m22]; exact w21_354
  have w22_358 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m22]; exact w21_358
  have w22_35c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = BitVec.ofNat 32 tl2.len := by rw [m22]; exact w21_35c
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m22]; exact w21_42c
  have w22_430 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_430
  have b22_420 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m22]; exact b21_420
  have b22_434 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m22]; exact b21_434
  clear b21_434 b21_420 w21_430 w21_42c w21_428 w21_424 w21_35c w21_358 w21_354 w21_350 w21_34c w21_348 w21_32c w21_328 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_15 g21_14 g21_13 g21_12 g21_11 g21_10 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21 w20_354
  -- 0xD1E: sv_octF
  obtain ⟨n23, c23, s23, sp23, rk23, K23, A23, Ok23, Er23, fr23⟩ := sv_octF (oc := 0x420) (dc := 0x350)
    F E22 s22 sv_at_d1e sv_at_d22 (by decide) (by decide) g22_2 g22_10 g22_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w22_358 w22_35c (ec_in.contentW (opt_ok_elem hr2))
  have t23 : Steps n0 n23 := t22.trans c23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.keepL K23 (by decide)
  rw [sv_mb fR22 (ec_in.contentW (opt_ok_elem hr2))] at A23 Ok23 Er23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rk23 sp (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk23 (3 : Fin 32) (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk23 (4 : Fin 32) (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk23 (8 : Fin 32) (by decide) (by decide), g22_8]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rk23 (18 : Fin 32) (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rk23 (19 : Fin 32) (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [rk23 (20 : Fin 32) (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [rk23 (21 : Fin 32) (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [rk23 (22 : Fin 32) (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [rk23 (23 : Fin 32) (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [rk23 (24 : Fin 32) (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [rk23 (25 : Fin 32) (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [rk23 (26 : Fin 32) (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [rk23 (27 : Fin 32) (by decide) (by decide), g22_27]
  obtain ⟨r23, hr23⟩ : ∃ r, derContent ((ecp) + BitVec.ofNat 32 tl2.header) (derElement 4 (memBytes M0 ((ecp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat)) = r := ⟨_, rfl⟩
  rcases r23 with er23 | ⟨vp23, vl23⟩
  · obtain ⟨z23, -⟩ := Er23 er23 hr23
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8)] := keep_kk22.trans K23
    clear keep_kk22
    have w23_328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K23.w32 (by decide) (by decide)).trans w22_328
    have w23_32c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K23.w32 (by decide) (by decide)).trans w22_32c
    have w23_348 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K23.w32 (by decide) (by decide)).trans w22_348
    have w23_34c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K23.w32 (by decide) (by decide)).trans w22_34c
    have w23_350 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K23.w32 (by decide) (by decide)).trans w22_350
    have w23_354 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := (K23.w32 (by decide) (by decide)).trans w22_354
    have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K23.w32 (by decide) (by decide)).trans w22_428
    have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K23.w32 (by decide) (by decide)).trans w22_42c
    have w23_430 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K23.w32 (by decide) (by decide)).trans w22_430
    have b23_434 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K23.b8 (by decide) (by decide)).trans b22_434
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z23
    clear b22_434 b22_420 w22_430 w22_42c w22_428 w22_424 w22_35c w22_358 w22_354 w22_350 w22_34c w22_348 w22_32c w22_328 g22_11 g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_15 g22_14 g22_13 g22_12 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
    -- 0xD26: lw
    obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_d26 (off' := 0xD2A) (by decide)
      (by rw [g23_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s24 : St n24.mem SV n24 0xD2A (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
    have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_8]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
    have g24_10 : reg n24 a0 = 0 := by
      rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g23_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w23_420]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m24]; exact w23_328
    have w24_32c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m24]; exact w23_32c
    have w24_348 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_348
    have w24_34c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_34c
    have w24_350 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m24]; exact w23_350
    have w24_354 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m24]; exact w23_354
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m24]; exact w23_420
    have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m24]; exact w23_428
    have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m24]; exact w23_42c
    have w24_430 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_430
    have b24_434 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m24]; exact b23_434
    clear w23_420 b23_434 w23_430 w23_42c w23_428 w23_354 w23_350 w23_34c w23_348 w23_32c w23_328 z23
    -- 0xD2A: sw
    obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_d2a (off' := 0xD2C) (c := 0x74)
      (by decide) (by rw [g24_2]; sv_addr) (by decide) (by decide)
    have t25 : Steps n0 n25 := t24.trans d25
    have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
    have E25 : SvCode n25.mem := E24.fr F fr25
    have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
    have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
    have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
    have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
    have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg25 (8 : Fin 32), g24_8]
    have g25_10 : reg n25 a0 = 0 := by rw [rg25 a0, g24_10]
    have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
    have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
    have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [rg25 (20 : Fin 32), g24_20]
    have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rg25 (21 : Fin 32), g24_21]
    have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rg25 (22 : Fin 32), g24_22]
    have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rg25 (23 : Fin 32), g24_23]
    have g25_24 : reg n25 (24 : Fin 32) = x24 := by rw [rg25 (24 : Fin 32), g24_24]
    have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rg25 (25 : Fin 32), g24_25]
    have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rg25 (26 : Fin 32), g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = x27 := by rw [rg25 (27 : Fin 32), g24_27]
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := keep_kk24.trans K25.toL
    clear keep_kk24
    have w25_328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K25.w32 (by decide) (by decide)).trans w24_328
    have w25_32c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K25.w32 (by decide) (by decide)).trans w24_32c
    have w25_348 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_348
    have w25_34c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_34c
    have w25_350 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K25.w32 (by decide) (by decide)).trans w24_350
    have w25_354 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := (K25.w32 (by decide) (by decide)).trans w24_354
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := (K25.w32 (by decide) (by decide)).trans w24_420
    have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K25.w32 (by decide) (by decide)).trans w24_428
    have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K25.w32 (by decide) (by decide)).trans w24_42c
    have w25_430 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_430
    have b25_434 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K25.b8 (by decide) (by decide)).trans b24_434
    have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = 0 := by rw [W25, g24_10]
    clear b24_434 w24_430 w24_42c w24_428 w24_420 w24_354 w24_350 w24_34c w24_348 w24_32c w24_328 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
    -- 0xD2C: branch, taken
    obtain ⟨n26, d26, u26⟩ := s25.taken E25.self 0x12AA sv_at_d2c
      (by decide) (by rw [g25_10, s25.zero]; rfl)
    have s26 : St n26.mem SV n26 0x12AA (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u26.regs, g25_8]
    have g26_10 : reg n26 a0 = 0 := by rw [u26.regs, g25_10]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [u26.regs, g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [u26.regs, g25_27]
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = 0 := by rw [m26]; exact w25_74
    have w26_328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m26]; exact w25_328
    have w26_32c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m26]; exact w25_32c
    have w26_348 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_348
    have w26_34c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_34c
    have w26_350 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m26]; exact w25_350
    have w26_354 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m26]; exact w25_354
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m26]; exact w25_420
    have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m26]; exact w25_428
    have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m26]; exact w25_42c
    have w26_430 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_430
    have b26_434 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m26]; exact b25_434
    clear w25_74 b25_434 w25_430 w25_42c w25_428 w25_420 w25_354 w25_350 w25_34c w25_348 w25_32c w25_328 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_10 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
    -- 0x12AA: lbu
    obtain ⟨n27, d27, u27⟩ := s26.lbu E26.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s27 : St n27.mem SV n27 0x12AE (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
    have g27_10 : reg n27 a0 = 0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_10]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = 0 := by rw [m27]; exact w26_74
    have w27_328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m27]; exact w26_328
    have w27_32c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m27]; exact w26_32c
    have w27_348 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_348
    have w27_34c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_34c
    have w27_350 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m27]; exact w26_350
    have w27_354 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m27]; exact w26_354
    have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m27]; exact w26_420
    have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m27]; exact w26_428
    have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m27]; exact w26_42c
    have w27_430 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_430
    have b27_434 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m27]; exact b26_434
    clear b26_434 w26_430 w26_42c w26_428 w26_420 w26_354 w26_350 w26_34c w26_348 w26_32c w26_328 w26_74 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_10 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
    -- 0x12AE: j
    obtain ⟨n28, d28, u28⟩ := s27.jump E27.self sv_at_12ae (off' := 0x7A4) (by decide)
      (by rw [s27.pc]; decide)
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
    have g28_10 : reg n28 a0 = 0 := by rw [u28.regs, g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [u28.regs, g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = 0 := by rw [m28]; exact w27_74
    have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m28]; exact w27_328
    have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m28]; exact w27_32c
    have w28_348 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_348
    have w28_34c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_34c
    have w28_350 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m28]; exact w27_350
    have w28_354 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m28]; exact w27_354
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m28]; exact w27_420
    have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m28]; exact w27_428
    have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m28]; exact w27_42c
    have w28_430 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_430
    have b28_434 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m28]; exact b27_434
    clear b27_434 w27_430 w27_42c w27_428 w27_420 w27_354 w27_350 w27_34c w27_348 w27_32c w27_328 w27_74 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_10 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    exact .inl ⟨(fun ⟨tl2', h0', h1', vp23', vl23', h2', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr23] at h2'; cases h2'), sv_fail F E28 s28 t28 (fun x hx => (fR28 x hx).trans (fM x hx).symm) V28 hret g28_2 g28_18 hO g28_3 g28_4⟩
  obtain ⟨te23, ht23, -, -⟩ := content_ok_elem hr23
  obtain ⟨p0_23, p4_23⟩ := Ok23 vp23 vl23 hr23
  obtain ⟨d8_23, d12_23⟩ := A23 te23 ht23
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8)] := keep_kk22.trans K23
  clear keep_kk22
  have w23_328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K23.w32 (by decide) (by decide)).trans w22_328
  have w23_32c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K23.w32 (by decide) (by decide)).trans w22_32c
  have w23_348 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K23.w32 (by decide) (by decide)).trans w22_348
  have w23_34c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K23.w32 (by decide) (by decide)).trans w22_34c
  have w23_350 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K23.w32 (by decide) (by decide)).trans w22_350
  have w23_354 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := (K23.w32 (by decide) (by decide)).trans w22_354
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K23.w32 (by decide) (by decide)).trans w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K23.w32 (by decide) (by decide)).trans w22_42c
  have w23_430 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K23.w32 (by decide) (by decide)).trans w22_430
  have b23_434 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K23.b8 (by decide) (by decide)).trans b22_434
  have w23_358 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = ((ecp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te23.header + te23.len) := d8_23
  have w23_35c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := d12_23
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp23 := p0_23
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl23 := p4_23
  clear b22_434 b22_420 w22_430 w22_42c w22_428 w22_424 w22_35c w22_358 w22_354 w22_350 w22_34c w22_348 w22_32c w22_328 g22_11 g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_15 g22_14 g22_13 g22_12 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0xD26: lw
  obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_d26 (off' := 0xD2A) (by decide)
    (by rw [g23_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s24 : St n24.mem SV n24 0xD2A (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_8]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
  have g24_10 : reg n24 a0 = vp23 := by
    rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g23_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w23_420]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m24]; exact w23_328
  have w24_32c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m24]; exact w23_32c
  have w24_348 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_348
  have w24_34c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_34c
  have w24_350 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m24]; exact w23_350
  have w24_354 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m24]; exact w23_354
  have w24_358 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = ((ecp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te23.header + te23.len) := by rw [m24]; exact w23_358
  have w24_35c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := by rw [m24]; exact w23_35c
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp23 := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl23 := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m24]; exact w23_42c
  have w24_430 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_430
  have b24_434 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m24]; exact b23_434
  clear w23_424 w23_420 w23_35c w23_358 b23_434 w23_430 w23_42c w23_428 w23_354 w23_350 w23_34c w23_348 w23_32c w23_328 d12_23 d8_23 p4_23 p0_23 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 Er23 Ok23 A23 K23 rk23 sp23 s23 c23
  -- 0xD2A: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_d2a (off' := 0xD2C) (c := 0x74)
    (by decide) (by rw [g24_2]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg25 (8 : Fin 32), g24_8]
  have g25_10 : reg n25 a0 = vp23 := by rw [rg25 a0, g24_10]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [rg25 (20 : Fin 32), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rg25 (22 : Fin 32), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rg25 (23 : Fin 32), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by rw [rg25 (24 : Fin 32), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rg25 (25 : Fin 32), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by rw [rg25 (27 : Fin 32), g24_27]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K25.w32 (by decide) (by decide)).trans w24_328
  have w25_32c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K25.w32 (by decide) (by decide)).trans w24_32c
  have w25_348 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_348
  have w25_34c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_34c
  have w25_350 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K25.w32 (by decide) (by decide)).trans w24_350
  have w25_354 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := (K25.w32 (by decide) (by decide)).trans w24_354
  have w25_358 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = ((ecp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te23.header + te23.len) := (K25.w32 (by decide) (by decide)).trans w24_358
  have w25_35c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := (K25.w32 (by decide) (by decide)).trans w24_35c
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp23 := (K25.w32 (by decide) (by decide)).trans w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl23 := (K25.w32 (by decide) (by decide)).trans w24_424
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K25.w32 (by decide) (by decide)).trans w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K25.w32 (by decide) (by decide)).trans w24_42c
  have w25_430 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_430
  have b25_434 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K25.b8 (by decide) (by decide)).trans b24_434
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23 := by rw [W25, g24_10]
  clear b24_434 w24_430 w24_42c w24_428 w24_424 w24_420 w24_35c w24_358 w24_354 w24_350 w24_34c w24_348 w24_32c w24_328 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0xD2C: branch, not taken
  obtain ⟨n26, d26, u26⟩ := s25.notTaken E25.self 0xD30 sv_at_d2c
    (by decide) (by rw [g25_10, s25.zero]; exact br_beq_f (((ec_in.contentW (opt_ok_elem hr2)).contentIn hr23).pos_ne))
  have s26 : St n26.mem SV n26 0xD30 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u26.regs, g25_8]
  have g26_10 : reg n26 a0 = vp23 := by rw [u26.regs, g25_10]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [u26.regs, g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [u26.regs, g25_27]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23 := by rw [m26]; exact w25_74
  have w26_328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m26]; exact w25_328
  have w26_32c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m26]; exact w25_32c
  have w26_348 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_348
  have w26_34c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_34c
  have w26_350 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m26]; exact w25_350
  have w26_354 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m26]; exact w25_354
  have w26_358 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = ((ecp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te23.header + te23.len) := by rw [m26]; exact w25_358
  have w26_35c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := by rw [m26]; exact w25_35c
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp23 := by rw [m26]; exact w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl23 := by rw [m26]; exact w25_424
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m26]; exact w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m26]; exact w25_42c
  have w26_430 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_430
  have b26_434 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m26]; exact b25_434
  clear w25_74 b25_434 w25_430 w25_42c w25_428 w25_424 w25_420 w25_35c w25_358 w25_354 w25_350 w25_34c w25_348 w25_32c w25_328 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_10 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0xD30: lw
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_d30 (off' := 0xD34) (by decide)
    (by rw [g26_2, show B + 0x21A0 + 0x35C = B + 0x21A0 + BitVec.ofNat 32 0x35C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s27 : St n27.mem SV n27 0xD34 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
  have g27_10 : reg n27 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x35C = B + 0x21A0 + BitVec.ofNat 32 0x35C by sv_addr, w26_35c]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23 := by rw [m27]; exact w26_74
  have w27_328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m27]; exact w26_328
  have w27_32c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m27]; exact w26_32c
  have w27_348 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_348
  have w27_34c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_34c
  have w27_350 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m27]; exact w26_350
  have w27_354 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m27]; exact w26_354
  have w27_358 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = ((ecp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te23.header + te23.len) := by rw [m27]; exact w26_358
  have w27_35c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := by rw [m27]; exact w26_35c
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp23 := by rw [m27]; exact w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl23 := by rw [m27]; exact w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m27]; exact w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m27]; exact w26_42c
  have w27_430 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_430
  have b27_434 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m27]; exact b26_434
  clear b26_434 w26_430 w26_42c w26_428 w26_424 w26_420 w26_35c w26_358 w26_354 w26_350 w26_34c w26_348 w26_32c w26_328 w26_74 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_10 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  by_cases hrest1 : (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) = 0
  rotate_left
  · -- 0xD34: branch, taken
    obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x7A4 sv_at_d34
      (by decide) (by rw [g27_10, s27.zero]; exact br_bne_t hrest1)
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
    have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_8]
    have g28_10 : reg n28 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := by rw [u28.regs, g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [u28.regs, g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23 := by rw [m28]; exact w27_74
    have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m28]; exact w27_328
    have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m28]; exact w27_32c
    have w28_348 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_348
    have w28_34c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_34c
    have w28_350 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m28]; exact w27_350
    have w28_354 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m28]; exact w27_354
    have w28_358 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = ((ecp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te23.header + te23.len) := by rw [m28]; exact w27_358
    have w28_35c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := by rw [m28]; exact w27_35c
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp23 := by rw [m28]; exact w27_420
    have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl23 := by rw [m28]; exact w27_424
    have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m28]; exact w27_428
    have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m28]; exact w27_42c
    have w28_430 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_430
    have b28_434 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m28]; exact b27_434
    clear b27_434 w27_430 w27_42c w27_428 w27_424 w27_420 w27_35c w27_358 w27_354 w27_350 w27_34c w27_348 w27_32c w27_328 w27_74 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    exact .inl ⟨(fun ⟨tl2', h0', h1', vp23', vl23', h2', te23', h3', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr23] at h2'; cases h2'; rw [ht23] at h3'; cases h3'; exact hrest1 h4'), sv_fail F E28 s28 t28 (fun x hx => (fR28 x hx).trans (fM x hx).symm) V28 hret g28_2 g28_18 hO g28_3 g28_4⟩
  -- 0xD34: branch, not taken
  obtain ⟨n28, d28, u28⟩ := s27.notTaken E27.self 0xD38 sv_at_d34
    (by decide) (by rw [g27_10, s27.zero]; exact br_bne_f hrest1)
  have s28 : St n28.mem SV n28 0xD38 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_8]
  have g28_10 : reg n28 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := by rw [u28.regs, g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [u28.regs, g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23 := by rw [m28]; exact w27_74
  have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m28]; exact w27_328
  have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m28]; exact w27_32c
  have w28_348 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_348
  have w28_34c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_34c
  have w28_350 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m28]; exact w27_350
  have w28_354 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m28]; exact w27_354
  have w28_358 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = ((ecp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te23.header + te23.len) := by rw [m28]; exact w27_358
  have w28_35c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := by rw [m28]; exact w27_35c
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp23 := by rw [m28]; exact w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl23 := by rw [m28]; exact w27_424
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m28]; exact w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m28]; exact w27_42c
  have w28_430 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_430
  have b28_434 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m28]; exact b27_434
  clear b27_434 w27_430 w27_42c w27_428 w27_424 w27_420 w27_35c w27_358 w27_354 w27_350 w27_34c w27_348 w27_32c w27_328 w27_74 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0xD38: lw
  obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_d38 (off' := 0xD3C) (by decide)
    (by rw [g28_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s29 : St n29.mem SV n29 0xD3C (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_10 : reg n29 a0 = vl23 := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w28_424]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23 := by rw [m29]; exact w28_74
  have w29_328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m29]; exact w28_328
  have w29_32c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m29]; exact w28_32c
  have w29_348 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_348
  have w29_34c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_34c
  have w29_350 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := by rw [m29]; exact w28_350
  have w29_354 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := by rw [m29]; exact w28_354
  have w29_358 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = ((ecp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te23.header + te23.len) := by rw [m29]; exact w28_358
  have w29_35c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := by rw [m29]; exact w28_35c
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp23 := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl23 := by rw [m29]; exact w28_424
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m29]; exact w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := by rw [m29]; exact w28_42c
  have w29_430 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_430
  have b29_434 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m29]; exact b28_434
  clear b28_434 w28_430 w28_42c w28_428 w28_424 w28_420 w28_35c w28_358 w28_354 w28_350 w28_34c w28_348 w28_32c w28_328 w28_74 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0xD3C: sw
  obtain ⟨n30, d30, s30, fr30, K30, W30, rg30⟩ := sv_sw F E29 s29 sv_at_d3c (off' := 0xD3E) (c := 0x78)
    (by decide) (by rw [g29_2]; sv_addr) (by decide) (by decide)
  have t30 : Steps n0 n30 := t29.trans d30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rg30 sp, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg30 (3 : Fin 32), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg30 (4 : Fin 32), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg30 (8 : Fin 32), g29_8]
  have g30_10 : reg n30 a0 = vl23 := by rw [rg30 a0, g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rg30 (18 : Fin 32), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rg30 (19 : Fin 32), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [rg30 (20 : Fin 32), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [rg30 (21 : Fin 32), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [rg30 (22 : Fin 32), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [rg30 (23 : Fin 32), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = x24 := by rw [rg30 (24 : Fin 32), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [rg30 (25 : Fin 32), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [rg30 (26 : Fin 32), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [rg30 (27 : Fin 32), g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x18), (0x348, 0x8), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x420, 0x8), (0x358, 0x8), (0x74, 0x4), (0x78, 0x4)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23 := (K30.w32 (by decide) (by decide)).trans w29_74
  have w30_328 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := (K30.w32 (by decide) (by decide)).trans w29_328
  have w30_32c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := (K30.w32 (by decide) (by decide)).trans w29_32c
  have w30_348 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x348) = (ecp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K30.w32 (by decide) (by decide)).trans w29_348
  have w30_34c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34C) = (ecl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K30.w32 (by decide) (by decide)).trans w29_34c
  have w30_350 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x350) = (ecp) + BitVec.ofNat 32 tl2.header := (K30.w32 (by decide) (by decide)).trans w29_350
  have w30_354 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x354) = BitVec.ofNat 32 tl2.len := (K30.w32 (by decide) (by decide)).trans w29_354
  have w30_358 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x358) = ((ecp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (te23.header + te23.len) := (K30.w32 (by decide) (by decide)).trans w29_358
  have w30_35c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x35C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (te23.header + te23.len) := (K30.w32 (by decide) (by decide)).trans w29_35c
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp23 := (K30.w32 (by decide) (by decide)).trans w29_420
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl23 := (K30.w32 (by decide) (by decide)).trans w29_424
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := (K30.w32 (by decide) (by decide)).trans w29_428
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ecp := (K30.w32 (by decide) (by decide)).trans w29_42c
  have w30_430 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := (K30.w32 (by decide) (by decide)).trans w29_430
  have b30_434 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := (K30.b8 (by decide) (by decide)).trans b29_434
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = vl23 := by rw [W30, g29_10]
  clear b29_434 w29_430 w29_42c w29_428 w29_424 w29_420 w29_35c w29_358 w29_354 w29_350 w29_34c w29_348 w29_32c w29_328 w29_74 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  exact .inr ⟨tl2, hr2, hrest0, vp23, vl23, hr23, te23, ht23, hrest1, n30, t30, s30, E30, V30, fR30, g30_2, g30_3, g30_4, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, w30_74, w30_78, w30_328, w30_32c, keep_kk30.mono (by decide)⟩

end C3.RV32.Sv
