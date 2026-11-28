import C3BootProofs.Proofs.SvCongr

/-!
# `sigstore::verify`: the certificate

From the call to `Der::sequence` over the leaf certificate at 0x5C to the call to `Der::element` for the `tbsCertificate` at 0x9A: the certificate is one `SEQUENCE` that fills the bytes.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL16e : List BInstr :=
  [.aluImm .add a1 sp 0x85, .aluImm .add a0 sp 0x375, .aluImm .add a2 x0 0xB]
theorem svL16e_end : blockEnd sigstoreVerifyCode 0x6E svL16e = some 0x78 := by
  simp only [svL16e]
  rw [blockEnd, sv_at_6e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_72]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_76]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL18c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svL18c_end : blockEnd sigstoreVerifyCode 0x8C svL18c = some 0x8E := by
  simp only [svL18c]
  rw [blockEnd, sv_at_8c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL192 : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x370, .aluImm .add a2 x0 0x30]
theorem svL192_end : blockEnd sigstoreVerifyCode 0x92 svL192 = some 0x9A := by
  simp only [svL192]
  rw [blockEnd, sv_at_92]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_94]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_96]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_l1 {B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x5C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80)
    (g0_11 : reg n0 a1 = B + 0x21A0 + BitVec.ofNat 32 0x360)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_26 : reg n0 (26 : Fin 32) = lp)
    (w0_360 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp)
    (w0_364 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll)
    (w0_368 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp)
    (w0_36c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll)
    (lc_in : SvIn B lp ll.toNat) :
    (¬ (∃ t, derElement 0x30 (memBytes M0 lp ll.toNat) = .ok t ∧ ll - BitVec.ofNat 32 (t.header + t.len) = 0) ∧ SvErrRet B out v n0) ∨
    (∃ t, derElement 0x30 (memBytes M0 lp ll.toNat) = .ok t ∧ ll - BitVec.ofNat 32 (t.header + t.len) = 0 ∧
      ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x9A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 ∧
        reg n' a1 = B + 0x21A0 + BitVec.ofNat 32 0x370 ∧
        reg n' a2 = BitVec.ofNat 32 0x30 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (26 : Fin 32) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 t.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 t.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 t.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 t.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (t.header + t.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (t.header + t.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = lp + BitVec.ofNat 32 t.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = lp + BitVec.ofNat 32 t.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 t.len ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 t.len).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 t.len).extractLsb' 8 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 t.len).extractLsb' 16 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 t.len).extractLsb' 24 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = (BitVec.ofNat 32 t.len).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 t.len).extractLsb' 8 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 t.len).extractLsb' 16 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 t.len).extractLsb' 24 8 ∧
        SvKeepL B n0.mem n'.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x5C: Der::sequence
  obtain ⟨n1, c1, s1, sp1, rk1, K1, Ok1, Er1, fr1⟩ := sv_seqF (oc := 0x80) (dc := 0x360)
    F E0 s0 sv_at_5c sv_at_60 (by decide) (by decide) g0_2
    g0_10 g0_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w0_368 w0_36c lc_in
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keepL K1 (by decide)
  rw [sv_mb fR0 lc_in] at Ok1 Er1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rk1 sp (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk1 (3 : Fin 32) (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk1 (4 : Fin 32) (by decide) (by decide), g0_4]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [rk1 (18 : Fin 32) (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [rk1 (19 : Fin 32) (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = dg := by rw [rk1 (20 : Fin 32) (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = rootp := by rw [rk1 (21 : Fin 32) (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = ll := by rw [rk1 (22 : Fin 32) (by decide) (by decide), g0_22]
  have g1_26 : reg n1 (26 : Fin 32) = lp := by rw [rk1 (26 : Fin 32) (by decide) (by decide), g0_26]
  obtain ⟨r1, hr1⟩ : ∃ r, derElement 0x30 (memBytes M0 lp ll.toNat) = r := ⟨_, rfl⟩
  rcases r1 with er | tl1
  · obtain ⟨z1, ez1⟩ := Er1 er hr1
    have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x80, 0x10), (0x368, 0x8)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1
    have w1_360 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := (K1.w32 (by decide) (by decide)).trans w0_360
    have w1_364 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := (K1.w32 (by decide) (by decide)).trans w0_364
    have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = BitVec.ofNat 32 0x0 := z1
    have b1_84 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er := ez1
    -- 0x64: lw
    obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_64 (off' := 0x66) (by decide)
      (by rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s2 : St n2.mem SV n2 0x66 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
    have m2 : n2.mem = n1.mem := u2.mem
    have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
    have t2 : Steps n0 n2 := t1.trans (.single d2)
    have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
    have E2 : SvCode n2.mem := E1.fr F fr2
    have V2 : SvSaves B n2.mem v := V1.same m2
    have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
    have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
    have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
    have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
    have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
    have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
    have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
    have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
    have g2_26 : reg n2 (26 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
    have g2_9 : reg n2 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w1_80]
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x80, 0x10), (0x368, 0x8)] := by rw [m2]; exact keep_kk1
    clear keep_kk1
    have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = BitVec.ofNat 32 0x0 := by rw [m2]; exact w1_80
    have w2_360 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m2]; exact w1_360
    have w2_364 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m2]; exact w1_364
    have b2_84 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er := by rw [m2]; exact b1_84
    clear b1_84 w1_80 w1_364 w1_360 ez1 z1
    -- 0x66: lbu
    obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_66 (off' := 0x6A) (by decide)
    have s3 : St n3.mem SV n3 0x6A (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
    have g3_9 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
    have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
    have g3_8 : reg n3 (8 : Fin 32) = (derErrByte er).zeroExtend 32 := by
      rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g2_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b2_84]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x80, 0x10), (0x368, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = BitVec.ofNat 32 0x0 := by rw [m3]; exact w2_80
    have w3_360 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m3]; exact w2_360
    have w3_364 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m3]; exact w2_364
    have b3_84 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er := by rw [m3]; exact b2_84
    clear b2_84 w2_364 w2_360 w2_80 g2_9 g2_26 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
    -- 0x6A: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x7A4 sv_at_6a
      (by decide) (by rw [g3_9, s3.zero]; rfl)
    have s4 : St n4.mem SV n4 0x7A4 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_8 : reg n4 (8 : Fin 32) = (derErrByte er).zeroExtend 32 := by rw [u4.regs, g3_8]
    have g4_9 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u4.regs, g3_9]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, g3_22]
    have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, g3_26]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x80, 0x10), (0x368, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = BitVec.ofNat 32 0x0 := by rw [m4]; exact w3_80
    have w4_360 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m4]; exact w3_360
    have w4_364 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m4]; exact w3_364
    have b4_84 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er := by rw [m4]; exact b3_84
    clear b3_84 w3_364 w3_360 w3_80 g3_8 g3_26 g3_22 g3_21 g3_20 g3_19 g3_18 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    exact .inl ⟨(fun ⟨t', h', _⟩ => by rw [hr1] at h'; cases h'), sv_fail F E4 s4 t4 (fun x hx => (fR4 x hx).trans (fM x hx).symm) V4 hret g4_2 g4_18 hO g4_3 g4_4 (by rw [g4_8]; sv_code)⟩
  obtain ⟨o0_1, o4_1, o8_1, o12_1, d8_1, d12_1⟩ := Ok1 tl1 hr1
  have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x80, 0x10), (0x368, 0x8)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1
  have w1_360 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := (K1.w32 (by decide) (by decide)).trans w0_360
  have w1_364 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := (K1.w32 (by decide) (by decide)).trans w0_364
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := o0_1
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := o4_1
  have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := o8_1
  have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := o12_1
  have w1_368 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := d8_1
  have w1_36c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := d12_1
  -- 0x64: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_64 (off' := 0x66) (by decide)
    (by rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0x66 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_26 : reg n2 (26 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_9 : reg n2 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w1_80]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x80, 0x10), (0x368, 0x8)] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m2]; exact w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := by rw [m2]; exact w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := by rw [m2]; exact w1_8c
  have w2_360 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m2]; exact w1_360
  have w2_364 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m2]; exact w1_364
  have w2_368 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_368
  have w2_36c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_36c
  clear w1_36c w1_368 w1_8c w1_88 w1_84 w1_80 w1_364 w1_360 d12_1 d8_1 o12_1 o8_1 o4_1 o0_1 g1_26 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 Er1 Ok1 K1 rk1 sp1 s1 c1 g0_4 g0_3 fR0 t0
  -- 0x66: lbu
  obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_66 (off' := 0x6A) (by decide)
  have b2_84 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by
    have h := byte_of_ld w2_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact h.1
  have s3 : St n3.mem SV n3 0x6A (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_9 : reg n3 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_8 : reg n3 (8 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b2_84]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x80, 0x10), (0x368, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := by rw [m3]; exact w2_8c
  have w3_360 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m3]; exact w2_360
  have w3_364 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m3]; exact w2_364
  have w3_368 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_368
  have w3_36c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_36c
  have b3_84 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m3]; exact b2_84
  clear w2_36c w2_368 w2_364 w2_360 w2_8c w2_88 w2_84 w2_80 g2_9 g2_26 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x6A: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0x6E sv_at_6a
    (by decide) (by rw [g3_9, s3.zero]; exact br_beq_f (lc_in.ok_ne hr1))
  have s4 : St n4.mem SV n4 0x6E (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [u4.regs, g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u4.regs, g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, g3_22]
  have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, g3_26]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x80, 0x10), (0x368, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m4]; exact w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := by rw [m4]; exact w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := by rw [m4]; exact w3_8c
  have w4_360 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m4]; exact w3_360
  have w4_364 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m4]; exact w3_364
  have w4_368 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_368
  have w4_36c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_36c
  have b4_84 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m4]; exact b3_84
  clear b3_84 w3_36c w3_368 w3_364 w3_360 w3_8c w3_88 w3_84 w3_80 g3_8 g3_26 g3_22 g3_21 g3_20 g3_19 g3_18 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 b2_84 u3 d3
  -- 0x6E
  obtain ⟨n5, c5, u5⟩ := s4.block svL16e E4.self svL16e_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x78 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svL16e (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_8 : reg n5 (8 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
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
  have g5_26 : reg n5 (26 : Fin 32) = lp := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x375 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL16e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_26, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_11 : reg n5 a1 = B + 0x21A0 + BitVec.ofNat 32 0x85 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL16e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_26, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_12 : reg n5 a2 = BitVec.ofNat 32 0xB := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL16e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_26, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x80, 0x10), (0x368, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := by rw [m5]; exact w4_8c
  have w5_360 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m5]; exact w4_360
  have w5_364 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m5]; exact w4_364
  have w5_368 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_368
  have w5_36c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_36c
  have b5_84 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m5]; exact b4_84
  clear b4_84 w4_36c w4_368 w4_364 w4_360 w4_8c w4_88 w4_84 w4_80 g4_26 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  have b5_85 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by
    have h := byte_of_ld w5_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x85 = B + 0x21A0 + BitVec.ofNat 32 0x84 + 1 by sv_addr]; exact h.2.1
  have b5_86 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by
    have h := byte_of_ld w5_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x86 = B + 0x21A0 + BitVec.ofNat 32 0x84 + 2 by sv_addr]; exact h.2.2.1
  have b5_87 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by
    have h := byte_of_ld w5_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x87 = B + 0x21A0 + BitVec.ofNat 32 0x84 + 3 by sv_addr]; exact h.2.2.2
  -- 0x78: memcpy
  obtain ⟨n6, P6, K6, X6⟩ := sv_mc (c := 0x375) (d := 0x85) (N := 0xB) F E5 s5 sv_at_78 sv_at_7c
    (by decide) (by decide) g5_2 g5_10 g5_11 g5_12
    (by decide) (by decide) (by decide)
  have s6 := P6.st
  have fr6 := P6.fr
  have t6 : Steps n0 n6 := t5.trans P6.steps
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [P6.regs sp (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P6.regs (3 : Fin 32) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P6.regs (4 : Fin 32) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [P6.regs (8 : Fin 32) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [P6.regs (9 : Fin 32) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [P6.regs (18 : Fin 32) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [P6.regs (19 : Fin 32) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [P6.regs (20 : Fin 32) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [P6.regs (21 : Fin 32) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [P6.regs (22 : Fin 32) (by decide), g5_22]
  have g6_26 : reg n6 (26 : Fin 32) = lp := by rw [P6.regs (26 : Fin 32) (by decide), g5_26]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := (K6.w32 (by decide) (by decide)).trans w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := (K6.w32 (by decide) (by decide)).trans w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := (K6.w32 (by decide) (by decide)).trans w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := (K6.w32 (by decide) (by decide)).trans w5_8c
  have w6_360 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := (K6.w32 (by decide) (by decide)).trans w5_360
  have w6_364 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := (K6.w32 (by decide) (by decide)).trans w5_364
  have w6_368 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := (K6.w32 (by decide) (by decide)).trans w5_368
  have w6_36c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := (K6.w32 (by decide) (by decide)).trans w5_36c
  have b6_84 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := (K6.b8 (by decide) (by decide)).trans b5_84
  have b6_85 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K6.b8 (by decide) (by decide)).trans b5_85
  have b6_86 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K6.b8 (by decide) (by decide)).trans b5_86
  have b6_87 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K6.b8 (by decide) (by decide)).trans b5_87
  have w6_378 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = lp + BitVec.ofNat 32 tl1.header := by
    rw [← w5_88]
    exact ld_cp fun q hq => by
      have := X6 (0x3 + q) (by omega)
      rwa [show 0x375 + (0x3 + q) = 0x378 + q by omega,
        show 0x85 + (0x3 + q) = 0x88 + q by omega] at this
  have w6_37c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl1.len := by
    rw [← w5_8c]
    exact ld_cp fun q hq => by
      have := X6 (0x7 + q) (by omega)
      rwa [show 0x375 + (0x7 + q) = 0x37C + q by omega,
        show 0x85 + (0x7 + q) = 0x8C + q by omega] at this
  have b6_375 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [show 0x375 = 0x375 + 0x0 from rfl, X6 0x0 (by decide)]; exact b5_85
  have b6_376 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [show 0x376 = 0x375 + 0x1 from rfl, X6 0x1 (by decide)]; exact b5_86
  have b6_377 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [show 0x377 = 0x375 + 0x2 from rfl, X6 0x2 (by decide)]; exact b5_87
  clear b5_84 w5_36c w5_368 w5_364 w5_360 w5_8c w5_88 w5_84 w5_80 g5_12 g5_11 g5_10 g5_26 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x80: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_80 (off' := 0x84) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x36C = B + 0x21A0 + BitVec.ofNat 32 0x36C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0x84 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = dg := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = rootp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = ll := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
  have g7_26 : reg n7 (26 : Fin 32) = lp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_10 : reg n7 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x36C = B + 0x21A0 + BitVec.ofNat 32 0x36C by sv_addr, w6_36c]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m7]; exact w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := by rw [m7]; exact w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := by rw [m7]; exact w6_8c
  have w7_360 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m7]; exact w6_360
  have w7_364 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m7]; exact w6_364
  have w7_368 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_368
  have w7_36c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_36c
  have w7_378 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = lp + BitVec.ofNat 32 tl1.header := by rw [m7]; exact w6_378
  have w7_37c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl1.len := by rw [m7]; exact w6_37c
  have b7_84 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m7]; exact b6_84
  have b7_85 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m7]; exact b6_85
  have b7_86 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m7]; exact b6_86
  have b7_87 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m7]; exact b6_87
  have b7_375 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m7]; exact b6_375
  have b7_376 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m7]; exact b6_376
  have b7_377 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m7]; exact b6_377
  clear b6_377 b6_376 b6_375 w6_37c w6_378 b6_87 b6_86 b6_85 b6_84 w6_36c w6_368 w6_364 w6_360 w6_8c w6_88 w6_84 w6_80 g6_26 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 s6 X6 K6 P6 b5_87 b5_86 b5_85
  -- 0x84: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_84 (off' := 0x88) (c := 0x370)
    (by decide) (by rw [g7_2]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg8 (8 : Fin 32), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [rg8 (9 : Fin 32), g7_9]
  have g8_10 : reg n8 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg8 a0, g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_26 : reg n8 (26 : Fin 32) = lp := by rw [rg8 (26 : Fin 32), g7_26]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := (K8.w32 (by decide) (by decide)).trans w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := (K8.w32 (by decide) (by decide)).trans w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := (K8.w32 (by decide) (by decide)).trans w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := (K8.w32 (by decide) (by decide)).trans w7_8c
  have w8_360 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := (K8.w32 (by decide) (by decide)).trans w7_360
  have w8_364 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := (K8.w32 (by decide) (by decide)).trans w7_364
  have w8_368 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := (K8.w32 (by decide) (by decide)).trans w7_368
  have w8_36c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := (K8.w32 (by decide) (by decide)).trans w7_36c
  have w8_378 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = lp + BitVec.ofNat 32 tl1.header := (K8.w32 (by decide) (by decide)).trans w7_378
  have w8_37c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl1.len := (K8.w32 (by decide) (by decide)).trans w7_37c
  have b8_84 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := (K8.b8 (by decide) (by decide)).trans b7_84
  have b8_85 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K8.b8 (by decide) (by decide)).trans b7_85
  have b8_86 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K8.b8 (by decide) (by decide)).trans b7_86
  have b8_87 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K8.b8 (by decide) (by decide)).trans b7_87
  have b8_375 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K8.b8 (by decide) (by decide)).trans b7_375
  have b8_376 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K8.b8 (by decide) (by decide)).trans b7_376
  have b8_377 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K8.b8 (by decide) (by decide)).trans b7_377
  have w8_370 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = lp + BitVec.ofNat 32 tl1.header := by rw [W8, g7_9]
  clear b7_377 b7_376 b7_375 b7_87 b7_86 b7_85 b7_84 w7_37c w7_378 w7_36c w7_368 w7_364 w7_360 w7_8c w7_88 w7_84 w7_80 g7_10 g7_26 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x88: sb
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sb F E8 s8 sv_at_88 (off' := 0x8C) (c := 0x374)
    (by decide) (by rw [g8_2]; sv_addr) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg9 (8 : Fin 32), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [rg9 (9 : Fin 32), g8_9]
  have g9_10 : reg n9 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg9 a0, g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [rg9 (20 : Fin 32), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [rg9 (21 : Fin 32), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [rg9 (22 : Fin 32), g8_22]
  have g9_26 : reg n9 (26 : Fin 32) = lp := by rw [rg9 (26 : Fin 32), g8_26]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := (K9.w32 (by decide) (by decide)).trans w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := (K9.w32 (by decide) (by decide)).trans w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := (K9.w32 (by decide) (by decide)).trans w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := (K9.w32 (by decide) (by decide)).trans w8_8c
  have w9_360 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := (K9.w32 (by decide) (by decide)).trans w8_360
  have w9_364 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := (K9.w32 (by decide) (by decide)).trans w8_364
  have w9_368 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := (K9.w32 (by decide) (by decide)).trans w8_368
  have w9_36c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := (K9.w32 (by decide) (by decide)).trans w8_36c
  have w9_370 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = lp + BitVec.ofNat 32 tl1.header := (K9.w32 (by decide) (by decide)).trans w8_370
  have w9_378 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = lp + BitVec.ofNat 32 tl1.header := (K9.w32 (by decide) (by decide)).trans w8_378
  have w9_37c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl1.len := (K9.w32 (by decide) (by decide)).trans w8_37c
  have b9_84 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := (K9.b8 (by decide) (by decide)).trans b8_84
  have b9_85 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_85
  have b9_86 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_86
  have b9_87 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_87
  have b9_375 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_375
  have b9_376 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_376
  have b9_377 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_377
  have b9_374 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [W9, g8_8, lbu_low]
  clear w8_370 b8_377 b8_376 b8_375 b8_87 b8_86 b8_85 b8_84 w8_37c w8_378 w8_36c w8_368 w8_364 w8_360 w8_8c w8_88 w8_84 w8_80 g8_26 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0x8C
  obtain ⟨n10, c10, u10⟩ := s9.block svL18c E9.self svL18c_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x8E (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svL18c (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_9 : reg n10 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_10 : reg n10 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = dg := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = rootp := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = ll := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_26 : reg n10 (26 : Fin 32) = lp := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svL18c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_26, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := by rw [m10]; exact w9_8c
  have w10_360 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m10]; exact w9_360
  have w10_364 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m10]; exact w9_364
  have w10_368 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m10]; exact w9_368
  have w10_36c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m10]; exact w9_36c
  have w10_370 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = lp + BitVec.ofNat 32 tl1.header := by rw [m10]; exact w9_370
  have w10_378 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = lp + BitVec.ofNat 32 tl1.header := by rw [m10]; exact w9_378
  have w10_37c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl1.len := by rw [m10]; exact w9_37c
  have b10_84 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m10]; exact b9_84
  have b10_85 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m10]; exact b9_85
  have b10_86 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m10]; exact b9_86
  have b10_87 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m10]; exact b9_87
  have b10_374 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m10]; exact b9_374
  have b10_375 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m10]; exact b9_375
  have b10_376 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m10]; exact b9_376
  have b10_377 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m10]; exact b9_377
  clear b9_374 b9_377 b9_376 b9_375 b9_87 b9_86 b9_85 b9_84 w9_37c w9_378 w9_370 w9_36c w9_368 w9_364 w9_360 w9_8c w9_88 w9_84 w9_80 g9_26 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  by_cases hz_10 : ll - BitVec.ofNat 32 (tl1.header + tl1.len) = 0
  rotate_left
  · -- the reader has bytes left
    -- 0x8E: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x7A4 sv_at_8e
      (by decide) (by rw [g10_10, s10.zero]; exact br_bne_t hz_10)
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
    have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, g10_22]
    have g11_26 : reg n11 (26 : Fin 32) = lp := by rw [u11.regs, g10_26]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_80
    have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_84
    have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_88
    have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_8c
    have w11_360 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m11]; exact w10_360
    have w11_364 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m11]; exact w10_364
    have w11_368 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_368
    have w11_36c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_36c
    have w11_370 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_370
    have w11_378 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_378
    have w11_37c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_37c
    have b11_84 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m11]; exact b10_84
    have b11_85 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m11]; exact b10_85
    have b11_86 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m11]; exact b10_86
    have b11_87 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m11]; exact b10_87
    have b11_374 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m11]; exact b10_374
    have b11_375 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m11]; exact b10_375
    have b11_376 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m11]; exact b10_376
    have b11_377 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m11]; exact b10_377
    clear b10_377 b10_376 b10_375 b10_374 b10_87 b10_86 b10_85 b10_84 w10_37c w10_378 w10_370 w10_36c w10_368 w10_364 w10_360 w10_8c w10_88 w10_84 w10_80 g10_8 g10_26 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
    exact .inl ⟨(fun ⟨t', h', hz'⟩ => by rw [hr1] at h'; cases h'; exact hz_10 hz'), sv_fail F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4 (by rw [g11_8]; sv_code)⟩
  -- 0x8E: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x92 sv_at_8e
    (by decide) (by rw [g10_10, s10.zero]; exact br_bne_f hz_10)
  have s11 : St n11.mem SV n11 0x92 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u11.regs, g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [u11.regs, g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [u11.regs, g10_22]
  have g11_26 : reg n11 (26 : Fin 32) = lp := by rw [u11.regs, g10_26]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_8c
  have w11_360 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m11]; exact w10_360
  have w11_364 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m11]; exact w10_364
  have w11_368 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_368
  have w11_36c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_36c
  have w11_370 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_370
  have w11_378 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_378
  have w11_37c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_37c
  have b11_84 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m11]; exact b10_84
  have b11_85 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m11]; exact b10_85
  have b11_86 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m11]; exact b10_86
  have b11_87 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m11]; exact b10_87
  have b11_374 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m11]; exact b10_374
  have b11_375 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m11]; exact b10_375
  have b11_376 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m11]; exact b10_376
  have b11_377 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m11]; exact b10_377
  clear b10_377 b10_376 b10_375 b10_374 b10_87 b10_86 b10_85 b10_84 w10_37c w10_378 w10_370 w10_36c w10_368 w10_364 w10_360 w10_8c w10_88 w10_84 w10_80 g10_8 g10_26 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x92
  obtain ⟨n12, c12, u12⟩ := s11.block svL192 E11.self svL192_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x9A (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svL192 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = dg := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = rootp := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = ll := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_26 : reg n12 (26 : Fin 32) = lp := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svL192, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_26, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svL192, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_26, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_12 : reg n12 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svL192, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_26, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = lp + BitVec.ofNat 32 tl1.header := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl1.len := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = lp + BitVec.ofNat 32 tl1.header := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl1.len := by rw [m12]; exact w11_8c
  have w12_360 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp := by rw [m12]; exact w11_360
  have w12_364 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll := by rw [m12]; exact w11_364
  have w12_368 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m12]; exact w11_368
  have w12_36c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m12]; exact w11_36c
  have w12_370 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = lp + BitVec.ofNat 32 tl1.header := by rw [m12]; exact w11_370
  have w12_378 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = lp + BitVec.ofNat 32 tl1.header := by rw [m12]; exact w11_378
  have w12_37c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl1.len := by rw [m12]; exact w11_37c
  have b12_84 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m12]; exact b11_84
  have b12_85 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m12]; exact b11_85
  have b12_86 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m12]; exact b11_86
  have b12_87 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m12]; exact b11_87
  have b12_374 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m12]; exact b11_374
  have b12_375 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m12]; exact b11_375
  have b12_376 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m12]; exact b11_376
  have b12_377 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m12]; exact b11_377
  clear b11_377 b11_376 b11_375 b11_374 b11_87 b11_86 b11_85 b11_84 w11_37c w11_378 w11_370 w11_36c w11_368 w11_364 w11_360 w11_8c w11_88 w11_84 w11_80 g11_26 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  exact .inr ⟨tl1, hr1, hz_10, n12, t12, s12, E12, V12, fR12, g12_2, g12_3, g12_4, g12_8, g12_10, g12_11, g12_12, g12_18, g12_19, g12_20, g12_21, g12_22, g12_26, w12_80, w12_84, w12_88, w12_8c, w12_360, w12_364, w12_368, w12_36c, w12_370, w12_378, w12_37c, b12_84, b12_85, b12_86, b12_87, b12_374, b12_375, b12_376, b12_377, keep_kk12.mono (by decide)⟩

end C3.RV32.Sv
