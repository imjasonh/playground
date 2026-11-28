import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the timestamp's certificates

From 0xD3E to 0xD70: the `SignedData`'s `[0]` certificates are present and well formed, and the next field isn't `[1]` CRLs.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTr5sd3e : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x320, .aluImm .add a2 x0 0xA0]
theorem svTr5sd3e_end : blockEnd sigstoreVerifyCode 0xD3E svTr5sd3e = some 0xD48 := by
  simp only [svTr5sd3e]
  rw [blockEnd, sv_at_d3e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_d42]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_d44]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr5sd66 : List BInstr :=
  [.aluImm .add a0 a0 0xFFFFFF5F]
theorem svTr5sd66_end : blockEnd sigstoreVerifyCode 0xD66 svTr5sd66 = some 0xD6A := by
  simp only [svTr5sd66]
  rw [blockEnd, sv_at_d66]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr5sd6a : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTr5sd6a_end : blockEnd sigstoreVerifyCode 0xD6A svTr5sd6a = some 0xD6C := by
  simp only [svTr5sd6a]
  rw [blockEnd, sv_at_d6a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tr5s {B out bp x20 x21 x22 x23 x24 x25 x26 x27 sdp sdl ecp ecl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xD3E (reg n0))
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
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl)
    (w0_328 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp)
    (w0_32c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl)
    (sd_in : SvIn B (sdp) (sdl).toNat)
    (hce : derOptRes 0xA0 (memBytes M0 (sdp) (sdl).toNat) ≠ none) :
    (¬ (∃ tl2, derOptRes 0xA0 (memBytes M0 (sdp) (sdl).toNat) = some (.ok tl2) ∧ ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 ∨ (M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl2, derOptRes 0xA0 (memBytes M0 (sdp) (sdl).toNat) = some (.ok tl2) ∧
    ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 ∨ (M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xD70 (reg n') ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x18), (0x328, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xD3E
  obtain ⟨n1, c1, u1⟩ := s0.block svTr5sd3e E0.self svTr5sd3e_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xD48 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTr5sd3e (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr5sd3e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr5sd3e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0xA0 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr5sd3e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m1]; exact w0_78
  have w1_328 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m1]; exact w0_328
  have w1_32c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m1]; exact w0_32c
  -- 0xD48: sv_optF2
  obtain ⟨n2, c2, s2, sp2, rk2, K2, R2, N2, fr2⟩ := sv_optF2 (oc := 0x420) (dc := 0x320) (tag := 0xA0)
    F E1 s1 sv_at_d48 sv_at_d4c (by decide) (by decide) g1_2 g1_10 g1_11 g1_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w1_328 w1_32c sd_in
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [sv_mb fR1 sd_in] at R2 N2
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
  obtain ⟨r2, hr2⟩ : ∃ r, derOptRes 0xA0 (memBytes M0 (sdp) (sdl).toNat) = r := ⟨_, rfl⟩
  rcases r2 with _ | (er2 | tl2)
  · exact absurd hr2 hce
  · rw [hr2] at R2
    obtain ⟨y0_2, y1_2⟩ := R2
    obtain ⟨ec_2, ey_2, hz_c2⟩ : ∃ b : BitVec 8, n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = b ∧ b.toNat < 0x27 :=
      ⟨_, y1_2, by sv_eb hr2⟩
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x18), (0x328, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K2.w32 (by decide) (by decide)).trans w1_74
    have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K2.w32 (by decide) (by decide)).trans w1_78
    have b2_420 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := y0_2
    have b2_421 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = ec_2 := ey_2
    clear w1_32c w1_328 w1_78 w1_74 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0xD50: lbu
    obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_d50 (off' := 0xD54) (by decide)
    have s3 : St n3.mem SV n3 0xD54 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m3]; exact w2_74
    have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m3]; exact w2_78
    have b3_420 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m3]; exact b2_420
    have b3_421 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = ec_2 := by rw [m3]; exact b2_421
    clear b2_421 b2_420 w2_78 w2_74 ey_2 y1_2 y0_2
    -- 0xD54: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x12A2 sv_at_d54
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
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m4]; exact w3_74
    have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m4]; exact w3_78
    have b4_420 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m4]; exact b3_420
    have b4_421 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = ec_2 := by rw [m4]; exact b3_421
    clear b3_421 b3_420 w3_78 w3_74 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
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
    have g5_8 : reg n5 (8 : Fin 32) = (ec_2).zeroExtend 32 := by
      rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g4_2, show B + 0x21A0 + 0x421 = B + 0x21A0 + BitVec.ofNat 32 0x421 by sv_addr, b4_421]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m5]; exact w4_74
    have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m5]; exact w4_78
    have b5_420 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m5]; exact b4_420
    have b5_421 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = ec_2 := by rw [m5]; exact b4_421
    clear b4_421 b4_420 w4_78 w4_74 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
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
    have g6_8 : reg n6 (8 : Fin 32) = (ec_2).zeroExtend 32 := by rw [u6.regs, g5_8]
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
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m6]; exact w5_74
    have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m6]; exact w5_78
    have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m6]; exact b5_420
    have b6_421 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = ec_2 := by rw [m6]; exact b5_421
    clear b5_421 b5_420 w5_78 w5_74 g5_8 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    exact .inl ⟨(fun ⟨tl2', h0', _⟩ => by rw [hr2] at h0'; cases h0'), sv_fail F E6 s6 t6 (fun x hx => (fR6 x hx).trans (fM x hx).symm) V6 hret g6_2 g6_18 hO g6_3 g6_4 (by rw [g6_8]; sv_code)⟩
  rw [hr2] at R2
  obtain ⟨y0_2, y4_2, y8_2, y12_2, y16_2, y20_2, d8_2, d12_2⟩ := R2
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x18), (0x328, 0x8)] := keep_kk1.trans K2
  clear keep_kk1
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K2.w32 (by decide) (by decide)).trans w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K2.w32 (by decide) (by decide)).trans w1_78
  have w2_328 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := d8_2
  have w2_32c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := d12_2
  have w2_424 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := y4_2
  have w2_428 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := y8_2
  have w2_42c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := y12_2
  have w2_430 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := y16_2
  have b2_420 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := y0_2
  have b2_434 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := y20_2
  clear w1_32c w1_328 w1_78 w1_74 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0xD50: lbu
  obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_d50 (off' := 0xD54) (by decide)
  have s3 : St n3.mem SV n3 0xD54 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m3]; exact w2_78
  have w3_328 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_328
  have w3_32c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_32c
  have w3_424 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m3]; exact w2_424
  have w3_428 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m3]; exact w2_428
  have w3_42c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m3]; exact w2_42c
  have w3_430 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_430
  have b3_420 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m3]; exact b2_420
  have b3_434 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m3]; exact b2_434
  clear b2_434 b2_420 w2_430 w2_42c w2_428 w2_424 w2_32c w2_328 w2_78 w2_74 d12_2 d8_2 y20_2 y16_2 y12_2 y8_2 y4_2 y0_2 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 N2 K2 rk2 sp2 s2 c2
  -- 0xD54: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0xD58 sv_at_d54
    (by decide) (by rw [g3_10, s3.zero]; decide)
  have s4 : St n4.mem SV n4 0xD58 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
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
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m4]; exact w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m4]; exact w3_78
  have w4_328 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_328
  have w4_32c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_32c
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m4]; exact w3_424
  have w4_428 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m4]; exact w3_428
  have w4_42c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m4]; exact w3_42c
  have w4_430 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_430
  have b4_420 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m4]; exact b3_420
  have b4_434 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m4]; exact b3_434
  clear b3_434 b3_420 w3_430 w3_42c w3_428 w3_424 w3_32c w3_328 w3_78 w3_74 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xD58: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_d58 (off' := 0xD5C) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x32C = B + 0x21A0 + BitVec.ofNat 32 0x32C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0xD5C (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
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
  have g5_10 : reg n5 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x32C = B + 0x21A0 + BitVec.ofNat 32 0x32C by sv_addr, w4_32c]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m5]; exact w4_78
  have w5_328 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_328
  have w5_32c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_32c
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m5]; exact w4_424
  have w5_428 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m5]; exact w4_428
  have w5_42c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m5]; exact w4_42c
  have w5_430 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_430
  have b5_420 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m5]; exact b4_420
  have b5_434 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m5]; exact b4_434
  clear b4_434 b4_420 w4_430 w4_42c w4_428 w4_424 w4_32c w4_328 w4_78 w4_74 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  by_cases hcrl : (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 ∨ (M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1
  rotate_left
  · have hnz : ¬ (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 := fun h => hcrl (.inl h)
    have ha1 : (M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat = 0xA1 := Decidable.of_not_not fun h => hcrl (.inr h)
    -- 0xD5C: branch, not taken
    obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0xD5E sv_at_d5c
      (by decide) (by rw [g5_10, s5.zero]; exact br_beq_f hnz)
    have s6 : St n6.mem SV n6 0xD5E (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans (.single d6)
    have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : SvCode n6.mem := E5.fr F fr6
    have V6 : SvSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
    have g6_10 : reg n6 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u6.regs, g5_10]
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
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m6]; exact w5_74
    have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m6]; exact w5_78
    have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_328
    have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_32c
    have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_424
    have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_428
    have w6_42c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m6]; exact w5_42c
    have w6_430 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_430
    have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m6]; exact b5_420
    have b6_434 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m6]; exact b5_434
    clear b5_434 b5_420 w5_430 w5_42c w5_428 w5_424 w5_32c w5_328 w5_78 w5_74 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    -- 0xD5E: lw
    obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_d5e (off' := 0xD62) (by decide)
      (by rw [g6_2, show B + 0x21A0 + 0x328 = B + 0x21A0 + BitVec.ofNat 32 0x328 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s7 : St n7.mem SV n7 0xD62 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
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
    have g7_10 : reg n7 a0 = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by
      rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g6_2, show B + 0x21A0 + 0x328 = B + 0x21A0 + BitVec.ofNat 32 0x328 by sv_addr, w6_328]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m7]; exact w6_74
    have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m7]; exact w6_78
    have w7_328 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_328
    have w7_32c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_32c
    have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m7]; exact w6_424
    have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m7]; exact w6_428
    have w7_42c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m7]; exact w6_42c
    have w7_430 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_430
    have b7_420 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m7]; exact b6_420
    have b7_434 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m7]; exact b6_434
    clear b6_434 b6_420 w6_430 w6_42c w6_428 w6_424 w6_32c w6_328 w6_78 w6_74 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
    -- 0xD62: lbu from the bundle
    obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_d62 (off' := 0xD66) (by decide)
    have s8 : St n8.mem SV n8 0xD66 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
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
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
    have g8_10 : reg n8 a0 = (M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g7_10, show ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + 0x0 = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) from BitVec.add_zero _, fR7 _ ((sd_in.restW (opt_ok_elem hr2)).r0 (toNat_pos_of_ne hnz))]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m8]; exact w7_74
    have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m8]; exact w7_78
    have w8_328 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_328
    have w8_32c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_32c
    have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m8]; exact w7_424
    have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m8]; exact w7_428
    have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m8]; exact w7_42c
    have w8_430 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_430
    have b8_420 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m8]; exact b7_420
    have b8_434 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m8]; exact b7_434
    clear b7_434 b7_420 w7_430 w7_42c w7_428 w7_424 w7_32c w7_328 w7_78 w7_74 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    -- 0xD66
    obtain ⟨n9, c9, u9⟩ := s8.block svTr5sd66 E8.self svTr5sd66_end
      ⟨trivial, trivial⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have s9 : St n9.mem SV n9 0xD6A (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have rb9 : ∀ q, reg n9 q = (runBlock svTr5sd66 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
    have g9_10 : reg n9 a0 = ((M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFF5F := by
      rw [rb9, ← g8_10]; rfl
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m9]; exact w8_74
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m9]; exact w8_78
    have w9_328 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_328
    have w9_32c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_32c
    have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m9]; exact w8_424
    have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m9]; exact w8_428
    have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m9]; exact w8_42c
    have w9_430 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_430
    have b9_420 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m9]; exact b8_420
    have b9_434 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m9]; exact b8_434
    clear b8_434 b8_420 w8_430 w8_42c w8_428 w8_424 w8_32c w8_328 w8_78 w8_74 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    -- 0xD6A
    obtain ⟨n10, c10, u10⟩ := s9.block svTr5sd6a E9.self svTr5sd6a_end
      ⟨trivial, trivial⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have s10 : St n10.mem SV n10 0xD6C (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have rb10 : ∀ q, reg n10 q = (runBlock svTr5sd6a (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
    have g10_10 : reg n10 a0 = ((M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFF5F := by
      rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
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
    have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb10]; simp +decide only [runBlock, BInstr.run, svTr5sd6a, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g9_2, g9_3, g9_4, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m10]; exact w9_74
    have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m10]; exact w9_78
    have w10_328 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_328
    have w10_32c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_32c
    have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m10]; exact w9_424
    have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m10]; exact w9_428
    have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m10]; exact w9_42c
    have w10_430 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_430
    have b10_420 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m10]; exact b9_420
    have b10_434 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m10]; exact b9_434
    clear b9_434 b9_420 w9_430 w9_42c w9_428 w9_424 w9_32c w9_328 w9_78 w9_74 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
    -- 0xD6C: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x7A4 sv_at_d6c
      (by decide) (by rw [g10_10, s10.zero]; exact br_tag_a1_t ha1)
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
    have g11_10 : reg n11 a0 = ((M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFF5F := by rw [u11.regs, g10_10]
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
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m11]; exact w10_74
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m11]; exact w10_78
    have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_328
    have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_32c
    have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_424
    have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_428
    have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m11]; exact w10_42c
    have w11_430 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_430
    have b11_420 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m11]; exact b10_420
    have b11_434 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m11]; exact b10_434
    clear b10_434 b10_420 w10_430 w10_42c w10_428 w10_424 w10_32c w10_328 w10_78 w10_74 g10_8 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
    exact .inl ⟨(fun ⟨tl2', h0', h1', _⟩ => by rw [hr2] at h0'; cases h0'; exact hcrl h1'), sv_fail F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4 (by rw [g11_8]; sv_code)⟩
  by_cases hz : (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0
  · -- 0xD5C: branch, taken
    obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0xD70 sv_at_d5c
      (by decide) (by rw [g5_10, s5.zero]; exact br_beq_t hz)
    have s6 : St n6.mem SV n6 0xD70 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans (.single d6)
    have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : SvCode n6.mem := E5.fr F fr6
    have V6 : SvSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
    have g6_10 : reg n6 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u6.regs, g5_10]
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
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m6]; exact w5_74
    have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m6]; exact w5_78
    have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_328
    have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_32c
    have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_424
    have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_428
    have w6_42c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m6]; exact w5_42c
    have w6_430 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_430
    have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m6]; exact b5_420
    have b6_434 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m6]; exact b5_434
    clear b5_434 b5_420 w5_430 w5_42c w5_428 w5_424 w5_32c w5_328 w5_78 w5_74 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    exact .inr ⟨tl2, hr2, hcrl, n6, t6, s6, E6, V6, fR6, g6_2, g6_3, g6_4, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, w6_74, w6_78, w6_328, w6_32c, keep_kk6.mono (by decide)⟩
  have ha1 : (M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1 := hcrl.resolve_left hz
  -- 0xD5C: branch, not taken
  obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0xD5E sv_at_d5c
    (by decide) (by rw [g5_10, s5.zero]; exact br_beq_f hz)
  have s6 : St n6.mem SV n6 0xD5E (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_10 : reg n6 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u6.regs, g5_10]
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
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m6]; exact w5_78
  have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_328
  have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_32c
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_424
  have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_428
  have w6_42c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m6]; exact w5_42c
  have w6_430 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_430
  have b6_420 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m6]; exact b5_420
  have b6_434 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m6]; exact b5_434
  clear b5_434 b5_420 w5_430 w5_42c w5_428 w5_424 w5_32c w5_328 w5_78 w5_74 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0xD5E: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_d5e (off' := 0xD62) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x328 = B + 0x21A0 + BitVec.ofNat 32 0x328 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0xD62 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
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
  have g7_10 : reg n7 a0 = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x328 = B + 0x21A0 + BitVec.ofNat 32 0x328 by sv_addr, w6_328]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m7]; exact w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m7]; exact w6_78
  have w7_328 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_328
  have w7_32c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_32c
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m7]; exact w6_424
  have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m7]; exact w6_428
  have w7_42c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m7]; exact w6_42c
  have w7_430 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m7]; exact w6_430
  have b7_420 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m7]; exact b6_420
  have b7_434 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m7]; exact b6_434
  clear b6_434 b6_420 w6_430 w6_42c w6_428 w6_424 w6_32c w6_328 w6_78 w6_74 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0xD62: lbu from the bundle
  obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_d62 (off' := 0xD66) (by decide)
  have s8 : St n8.mem SV n8 0xD66 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
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
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_10 : reg n8 a0 = (M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).zeroExtend 32 := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_10, show ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + 0x0 = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) from BitVec.add_zero _, fR7 _ ((sd_in.restW (opt_ok_elem hr2)).r0 (toNat_pos_of_ne hz))]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m8]; exact w7_78
  have w8_328 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_328
  have w8_32c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_32c
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m8]; exact w7_424
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m8]; exact w7_428
  have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m8]; exact w7_42c
  have w8_430 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_430
  have b8_420 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m8]; exact b7_420
  have b8_434 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m8]; exact b7_434
  clear b7_434 b7_420 w7_430 w7_42c w7_428 w7_424 w7_32c w7_328 w7_78 w7_74 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0xD66
  obtain ⟨n9, c9, u9⟩ := s8.block svTr5sd66 E8.self svTr5sd66_end
    ⟨trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0xD6A (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svTr5sd66 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_10 : reg n9 a0 = ((M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFF5F := by
    rw [rb9, ← g8_10]; rfl
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m9]; exact w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m9]; exact w8_78
  have w9_328 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_328
  have w9_32c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_32c
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m9]; exact w8_424
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m9]; exact w8_428
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m9]; exact w8_42c
  have w9_430 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m9]; exact w8_430
  have b9_420 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m9]; exact b8_420
  have b9_434 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m9]; exact b8_434
  clear b8_434 b8_420 w8_430 w8_42c w8_428 w8_424 w8_32c w8_328 w8_78 w8_74 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0xD6A
  obtain ⟨n10, c10, u10⟩ := s9.block svTr5sd6a E9.self svTr5sd6a_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0xD6C (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svTr5sd6a (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_10 : reg n10 a0 = ((M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFF5F := by
    rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
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
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svTr5sd6a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m10]; exact w9_78
  have w10_328 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_328
  have w10_32c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_32c
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m10]; exact w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m10]; exact w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m10]; exact w9_42c
  have w10_430 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m10]; exact w9_430
  have b10_420 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m10]; exact b9_420
  have b10_434 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m10]; exact b9_434
  clear b9_434 b9_420 w9_430 w9_42c w9_428 w9_424 w9_32c w9_328 w9_78 w9_74 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0xD6C: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0xD70 sv_at_d6c
    (by decide) (by rw [g10_10, s10.zero]; exact br_tag_a1_f ha1)
  have s11 : St n11.mem SV n11 0xD70 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
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
  have g11_10 : reg n11 a0 = ((M0 ((sdp) + BitVec.ofNat 32 (tl2.header + tl2.len))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFF5F := by rw [u11.regs, g10_10]
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
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x18), (0x328, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m11]; exact w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m11]; exact w10_78
  have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_328
  have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_32c
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = sdp := by rw [m11]; exact w10_42c
  have w11_430 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_430
  have b11_420 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m11]; exact b10_420
  have b11_434 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl2.tag := by rw [m11]; exact b10_434
  clear b10_434 b10_420 w10_430 w10_42c w10_428 w10_424 w10_32c w10_328 w10_78 w10_74 g10_8 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  exact .inr ⟨tl2, hr2, hcrl, n11, t11, s11, E11, V11, fR11, g11_2, g11_3, g11_4, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, w11_74, w11_78, w11_328, w11_32c, keep_kk11.mono (by decide)⟩

end C3.RV32.Sv
