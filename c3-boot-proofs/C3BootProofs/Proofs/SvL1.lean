import C3BootProofs.Proofs.SvDer

/-!
# `sigstore::verify`: the certificate

From the call to `Der::sequence` over the leaf certificate at 0x72 to the call to `Der::element` for the `tbsCertificate` at 0xD0: the certificate is one `SEQUENCE` that fills the bytes.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL186 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add (9 : Fin 32) sp a0, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x226, .lui a0 0x1000, .aluImm .add a0 a0 0x58D, .alu .add a0 a0 sp, .aluImm .add a2 x0 0xB]
set_option maxRecDepth 100000 in
theorem svL186_end : blockEnd sigstoreVerifyCode 0x86 svL186 = some 0xA2 := by decide

def svL1b6 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x1]
set_option maxRecDepth 100000 in
theorem svL1b6_end : blockEnd sigstoreVerifyCode 0xB6 svL1b6 = some 0xB8 := by decide

def svL1bc : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .lui a1 0x1000, .aluImm .add a1 a1 0x588, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x30]
set_option maxRecDepth 100000 in
theorem svL1bc_end : blockEnd sigstoreVerifyCode 0xBC svL1bc = some 0xD0 := by decide

set_option maxHeartbeats 0 in
theorem sv_l1 {B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x72 (reg n0))
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (g0_11 : reg n0 a1 = B + 0x21A0 + BitVec.ofNat 32 0x2E0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = lp)
    (g0_22 : reg n0 (22 : Fin 32) = dg)
    (g0_25 : reg n0 (25 : Fin 32) = rootp)
    (g0_26 : reg n0 (26 : Fin 32) = ll)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_2e0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp)
    (w0_2e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll)
    (w0_2e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp)
    (w0_2ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll)
    (lc_in : SvIn B lp ll.toNat) :
    (¬ (∃ t, derElement 0x30 (memBytes n0.mem lp ll.toNat) = .ok t ∧ ll - BitVec.ofNat 32 (t.header + t.len) = 0) ∧ SvErrRet B out v n0) ∨
    (∃ t, derElement 0x30 (memBytes n0.mem lp ll.toNat) = .ok t ∧ ll - BitVec.ofNat 32 (t.header + t.len) = 0 ∧
      ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xD0 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = n0.mem x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        reg n' a1 = B + 0x21A0 + BitVec.ofNat 32 0x1588 ∧
        reg n' a2 = BitVec.ofNat 32 0x30 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (22 : Fin 32) = dg ∧
        reg n' (25 : Fin 32) = rootp ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (t.header + t.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (t.header + t.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 t.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 t.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 t.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 t.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = lp + BitVec.ofNat 32 t.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = lp + BitVec.ofNat 32 t.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = BitVec.ofNat 32 t.len ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 t.len).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 t.len).extractLsb' 8 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 t.len).extractLsb' 16 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 t.len).extractLsb' 24 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158C) = (BitVec.ofNat 32 t.len).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 t.len).extractLsb' 8 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 t.len).extractLsb' 16 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 t.len).extractLsb' 24 8) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = n0.mem x := fun _ _ => rfl
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x72: Der::sequence
  obtain ⟨n1, c1, s1, sp1, rk1, K1, Ok1, Er1, fr1⟩ := sv_seqF (oc := 0xA20) (dc := 0x2E0)
    F E0 s0 sv_at_72 sv_at_76 (by decide) (by decide) g0_2
    g0_10 g0_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w0_2e8 w0_2ec lc_in
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keepL K1 (by decide)
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rk1 sp (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk1 (3 : Fin 32) (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk1 (4 : Fin 32) (by decide) (by decide), g0_4]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [rk1 (18 : Fin 32) (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [rk1 (19 : Fin 32) (by decide) (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = lp := by rw [rk1 (21 : Fin 32) (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = dg := by rw [rk1 (22 : Fin 32) (by decide) (by decide), g0_22]
  have g1_25 : reg n1 (25 : Fin 32) = rootp := by rw [rk1 (25 : Fin 32) (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = ll := by rw [rk1 (26 : Fin 32) (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk1 (27 : Fin 32) (by decide) (by decide), g0_27]
  obtain ⟨r1, hr1⟩ : ∃ r, derElement 0x30 (memBytes n0.mem lp ll.toNat) = r := ⟨_, rfl⟩
  rcases r1 with er | tl1
  · obtain ⟨z1, -⟩ := Er1 er hr1
    have w1_2e0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := (K1.w32 (by decide) (by decide)).trans w0_2e0
    have w1_2e4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := (K1.w32 (by decide) (by decide)).trans w0_2e4
    have w1_a20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := z1
    -- 0x7A: lw
    obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_7a (off' := 0x7E) (by decide)
      (by rw [g1_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s2 : St n2.mem SV n2 0x7E (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
    have m2 : n2.mem = n1.mem := u2.mem
    have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
    have t2 : Steps n0 n2 := t1.trans (.single d2)
    have fR2 : ∀ x, SvR B x → n2.mem x = n0.mem x := fun x hx => (fr2 x hx).trans (fR1 x hx)
    have E2 : SvCode n2.mem := E1.fr F fr2
    have V2 : SvSaves B n2.mem v := V1.same m2
    have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
    have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
    have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
    have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
    have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
    have g2_21 : reg n2 (21 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
    have g2_22 : reg n2 (22 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
    have g2_25 : reg n2 (25 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
    have g2_26 : reg n2 (26 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
    have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
    have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g1_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w1_a20]
    have w2_2e0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m2]; exact w1_2e0
    have w2_2e4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m2]; exact w1_2e4
    have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m2]; exact w1_a20
    clear w1_a20 w1_2e4 w1_2e0 z1
    -- 0x7E: lbu
    obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_7e (off' := 0x82) (by decide)
    have s3 : St n3.mem SV n3 0x82 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = n0.mem x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
    have g3_21 : reg n3 (21 : Fin 32) = lp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
    have g3_25 : reg n3 (25 : Fin 32) = rootp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
    have w3_2e0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m3]; exact w2_2e0
    have w3_2e4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m3]; exact w2_2e4
    have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m3]; exact w2_a20
    clear w2_a20 w2_2e4 w2_2e0 g2_8 g2_27 g2_26 g2_25 g2_22 g2_21 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
    -- 0x82: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x966 sv_at_82
      (by decide) (by rw [g3_8, s3.zero]; rfl)
    have s4 : St n4.mem SV n4 0x966 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = n0.mem x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u4.regs, g3_8]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
    have g4_21 : reg n4 (21 : Fin 32) = lp := by rw [u4.regs, g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = dg := by rw [u4.regs, g3_22]
    have g4_25 : reg n4 (25 : Fin 32) = rootp := by rw [u4.regs, g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = ll := by rw [u4.regs, g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, g3_27]
    have w4_2e0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m4]; exact w3_2e0
    have w4_2e4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m4]; exact w3_2e4
    have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m4]; exact w3_a20
    clear w3_a20 w3_2e4 w3_2e0 g3_27 g3_26 g3_25 g3_22 g3_21 g3_19 g3_18 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    exact .inl ⟨(fun ⟨t', h', _⟩ => by rw [hr1] at h'; cases h'), sv_fail F E4 s4 t4 fR4 V4 hret g4_2 g4_18 hO g4_3 g4_4⟩
  obtain ⟨o0_1, o4_1, o8_1, o12_1, d8_1, d12_1⟩ := Ok1 tl1 hr1
  have w1_2e0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := (K1.w32 (by decide) (by decide)).trans w0_2e0
  have w1_2e4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := (K1.w32 (by decide) (by decide)).trans w0_2e4
  have w1_a20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := o0_1
  have w1_a24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := o4_1
  have w1_a28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := o8_1
  have w1_a2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := o12_1
  have w1_2e8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := d8_1
  have w1_2ec : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := d12_1
  -- 0x7A: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_7a (off' := 0x7E) (by decide)
    (by rw [g1_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0x7E (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = n0.mem x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_25 : reg n2 (25 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_8 : reg n2 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w1_a20]
  have w2_2e0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m2]; exact w1_2e0
  have w2_2e4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m2]; exact w1_2e4
  have w2_2e8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_2e8
  have w2_2ec : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_2ec
  have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := by rw [m2]; exact w1_a20
  have w2_a24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m2]; exact w1_a24
  have w2_a28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := by rw [m2]; exact w1_a28
  have w2_a2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := by rw [m2]; exact w1_a2c
  clear w1_2ec w1_2e8 w1_a2c w1_a28 w1_a24 w1_a20 w1_2e4 w1_2e0 d12_1 d8_1 o12_1 o8_1 o4_1 o0_1 g1_27 g1_26 g1_25 g1_22 g1_21 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 Er1 Ok1 K1 rk1 sp1 s1 c1 g0_4 g0_3 fR0 t0
  -- 0x7E: lbu
  obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_7e (off' := 0x82) (by decide)
  have b2_a24 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by
    have h := byte_of_ld w2_a24
    rw [show B + 0x21A0 + BitVec.ofNat 32 0xA24 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact h.1
  have s3 : St n3.mem SV n3 0x82 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = n0.mem x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = lp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_25 : reg n3 (25 : Fin 32) = rootp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_20 : reg n3 (20 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, b2_a24]
  have w3_2e0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m3]; exact w2_2e0
  have w3_2e4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m3]; exact w2_2e4
  have w3_2e8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_2e8
  have w3_2ec : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_2ec
  have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := by rw [m3]; exact w2_a20
  have w3_a24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m3]; exact w2_a24
  have w3_a28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := by rw [m3]; exact w2_a28
  have w3_a2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := by rw [m3]; exact w2_a2c
  have b3_a24 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m3]; exact b2_a24
  clear w2_a2c w2_a28 w2_a24 w2_a20 w2_2ec w2_2e8 w2_2e4 w2_2e0 g2_8 g2_27 g2_26 g2_25 g2_22 g2_21 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x82: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0x86 sv_at_82
    (by decide) (by rw [g3_8, s3.zero]; exact br_beq_f (lc_in.ok_ne hr1))
  have s4 : St n4.mem SV n4 0x86 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = n0.mem x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u4.regs, g3_8]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [u4.regs, g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = lp := by rw [u4.regs, g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = dg := by rw [u4.regs, g3_22]
  have g4_25 : reg n4 (25 : Fin 32) = rootp := by rw [u4.regs, g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = ll := by rw [u4.regs, g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, g3_27]
  have w4_2e0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m4]; exact w3_2e0
  have w4_2e4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m4]; exact w3_2e4
  have w4_2e8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_2e8
  have w4_2ec : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_2ec
  have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := by rw [m4]; exact w3_a20
  have w4_a24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m4]; exact w3_a24
  have w4_a28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := by rw [m4]; exact w3_a28
  have w4_a2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := by rw [m4]; exact w3_a2c
  have b4_a24 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m4]; exact b3_a24
  clear b3_a24 w3_a2c w3_a28 w3_a24 w3_a20 w3_2ec w3_2e8 w3_2e4 w3_2e0 g3_20 g3_27 g3_26 g3_25 g3_22 g3_21 g3_19 g3_18 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 b2_a24 u3 d3
  -- 0x86
  obtain ⟨n5, c5, u5⟩ := s4.block svL186 E4.self svL186_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0xA2 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svL186 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = n0.mem x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by
    rw [rb5, runBlock_reg _ _ _ sp s4.zero (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (3 : Fin 32) s4.zero (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (4 : Fin 32) s4.zero (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = lp := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = dg := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_25 : reg n5 (25 : Fin 32) = rootp := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = ll := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_9 : reg n5 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL186, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_18, g4_19, g4_20, g4_21, g4_22, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | decide | sv_addr
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x158D := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL186, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_18, g4_19, g4_20, g4_21, g4_22, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | decide | sv_addr
  have g5_11 : reg n5 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA25 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL186, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_18, g4_19, g4_20, g4_21, g4_22, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | decide | sv_addr
  have g5_12 : reg n5 a2 = BitVec.ofNat 32 0xB := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL186, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_18, g4_19, g4_20, g4_21, g4_22, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | decide | sv_addr
  have w5_2e0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m5]; exact w4_2e0
  have w5_2e4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m5]; exact w4_2e4
  have w5_2e8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_2e8
  have w5_2ec : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_2ec
  have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := by rw [m5]; exact w4_a20
  have w5_a24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m5]; exact w4_a24
  have w5_a28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := by rw [m5]; exact w4_a28
  have w5_a2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := by rw [m5]; exact w4_a2c
  have b5_a24 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m5]; exact b4_a24
  clear b4_a24 w4_a2c w4_a28 w4_a24 w4_a20 w4_2ec w4_2e8 w4_2e4 w4_2e0 g4_27 g4_26 g4_25 g4_22 g4_21 g4_20 g4_19 g4_18 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  have b5_a25 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by
    have h := byte_of_ld w5_a24
    rw [show B + 0x21A0 + BitVec.ofNat 32 0xA25 = B + 0x21A0 + BitVec.ofNat 32 0xA24 + 1 by sv_addr]; exact h.2.1
  have b5_a26 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by
    have h := byte_of_ld w5_a24
    rw [show B + 0x21A0 + BitVec.ofNat 32 0xA26 = B + 0x21A0 + BitVec.ofNat 32 0xA24 + 2 by sv_addr]; exact h.2.2.1
  have b5_a27 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by
    have h := byte_of_ld w5_a24
    rw [show B + 0x21A0 + BitVec.ofNat 32 0xA27 = B + 0x21A0 + BitVec.ofNat 32 0xA24 + 3 by sv_addr]; exact h.2.2.2
  -- 0xA2: memcpy
  obtain ⟨n6, P6, K6, X6⟩ := sv_mc (c := 0x158D) (d := 0xA25) (N := 0xB) F E5 s5 sv_at_a2 sv_at_a6
    (by decide) (by decide) g5_2 g5_10 g5_11 g5_12
    (by decide) (by decide) (by decide)
  have s6 := P6.st
  have fr6 := P6.fr
  have t6 : Steps n0 n6 := t5.trans P6.steps
  have fR6 : ∀ x, SvR B x → n6.mem x = n0.mem x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [P6.regs sp (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P6.regs (3 : Fin 32) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P6.regs (4 : Fin 32) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [P6.regs (8 : Fin 32) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [P6.regs (9 : Fin 32) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [P6.regs (18 : Fin 32) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [P6.regs (19 : Fin 32) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [P6.regs (20 : Fin 32) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = lp := by rw [P6.regs (21 : Fin 32) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = dg := by rw [P6.regs (22 : Fin 32) (by decide), g5_22]
  have g6_25 : reg n6 (25 : Fin 32) = rootp := by rw [P6.regs (25 : Fin 32) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = ll := by rw [P6.regs (26 : Fin 32) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P6.regs (27 : Fin 32) (by decide), g5_27]
  have w6_2e0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := (K6.w32 (by decide) (by decide)).trans w5_2e0
  have w6_2e4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := (K6.w32 (by decide) (by decide)).trans w5_2e4
  have w6_2e8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := (K6.w32 (by decide) (by decide)).trans w5_2e8
  have w6_2ec : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := (K6.w32 (by decide) (by decide)).trans w5_2ec
  have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := (K6.w32 (by decide) (by decide)).trans w5_a20
  have w6_a24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := (K6.w32 (by decide) (by decide)).trans w5_a24
  have w6_a28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := (K6.w32 (by decide) (by decide)).trans w5_a28
  have w6_a2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := (K6.w32 (by decide) (by decide)).trans w5_a2c
  have b6_a24 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := (K6.b8 (by decide) (by decide)).trans b5_a24
  have b6_a25 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K6.b8 (by decide) (by decide)).trans b5_a25
  have b6_a26 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K6.b8 (by decide) (by decide)).trans b5_a26
  have b6_a27 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K6.b8 (by decide) (by decide)).trans b5_a27
  have w6_1590 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = lp + BitVec.ofNat 32 tl1.header := by
    rw [← w5_a28]
    exact ld_cp fun q hq => by
      have := X6 (0x3 + q) (by omega)
      rwa [show 0x158D + (0x3 + q) = 0x1590 + q by omega,
        show 0xA25 + (0x3 + q) = 0xA28 + q by omega] at this
  have w6_1594 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = BitVec.ofNat 32 tl1.len := by
    rw [← w5_a2c]
    exact ld_cp fun q hq => by
      have := X6 (0x7 + q) (by omega)
      rwa [show 0x158D + (0x7 + q) = 0x1594 + q by omega,
        show 0xA25 + (0x7 + q) = 0xA2C + q by omega] at this
  have b6_158d : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [show 0x158D = 0x158D + 0x0 from rfl, X6 0x0 (by decide)]; exact b5_a25
  have b6_158e : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [show 0x158E = 0x158D + 0x1 from rfl, X6 0x1 (by decide)]; exact b5_a26
  have b6_158f : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [show 0x158F = 0x158D + 0x2 from rfl, X6 0x2 (by decide)]; exact b5_a27
  clear b5_a24 w5_a2c w5_a28 w5_a24 w5_a20 w5_2ec w5_2e8 w5_2e4 w5_2e0 g5_12 g5_11 g5_10 g5_9 g5_27 g5_26 g5_25 g5_22 g5_21 g5_20 g5_19 g5_18 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0xAA: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_aa (off' := 0xAE) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x2EC = B + 0x21A0 + BitVec.ofNat 32 0x2EC by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0xAE (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = n0.mem x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u7.regs, upd_ne (by decide) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = lp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = dg := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
  have g7_25 : reg n7 (25 : Fin 32) = rootp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = ll := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_10 : reg n7 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x2EC = B + 0x21A0 + BitVec.ofNat 32 0x2EC by sv_addr, w6_2ec]
  have w7_2e0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m7]; exact w6_2e0
  have w7_2e4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m7]; exact w6_2e4
  have w7_2e8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_2e8
  have w7_2ec : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_2ec
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := by rw [m7]; exact w6_a20
  have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m7]; exact w6_a24
  have w7_a28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := by rw [m7]; exact w6_a28
  have w7_a2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := by rw [m7]; exact w6_a2c
  have w7_1590 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = lp + BitVec.ofNat 32 tl1.header := by rw [m7]; exact w6_1590
  have w7_1594 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = BitVec.ofNat 32 tl1.len := by rw [m7]; exact w6_1594
  have b7_a24 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m7]; exact b6_a24
  have b7_a25 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m7]; exact b6_a25
  have b7_a26 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m7]; exact b6_a26
  have b7_a27 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m7]; exact b6_a27
  have b7_158d : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m7]; exact b6_158d
  have b7_158e : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m7]; exact b6_158e
  have b7_158f : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m7]; exact b6_158f
  clear b6_158f b6_158e b6_158d w6_1594 w6_1590 b6_a27 b6_a26 b6_a25 b6_a24 w6_a2c w6_a28 w6_a24 w6_a20 w6_2ec w6_2e8 w6_2e4 w6_2e0 g6_27 g6_26 g6_25 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 s6 X6 K6 P6 b5_a27 b5_a26 b5_a25
  -- 0xAE: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_ae (off' := 0xB2) (c := 0x1588)
    (by decide) (by rw [g7_9]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = n0.mem x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [rg8 (8 : Fin 32), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg8 (9 : Fin 32), g7_9]
  have g8_10 : reg n8 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg8 a0, g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = lp := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = dg := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_25 : reg n8 (25 : Fin 32) = rootp := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = ll := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg8 (27 : Fin 32), g7_27]
  have w8_2e0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := (K8.w32 (by decide) (by decide)).trans w7_2e0
  have w8_2e4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := (K8.w32 (by decide) (by decide)).trans w7_2e4
  have w8_2e8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := (K8.w32 (by decide) (by decide)).trans w7_2e8
  have w8_2ec : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := (K8.w32 (by decide) (by decide)).trans w7_2ec
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := (K8.w32 (by decide) (by decide)).trans w7_a20
  have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := (K8.w32 (by decide) (by decide)).trans w7_a24
  have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := (K8.w32 (by decide) (by decide)).trans w7_a28
  have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := (K8.w32 (by decide) (by decide)).trans w7_a2c
  have w8_1590 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = lp + BitVec.ofNat 32 tl1.header := (K8.w32 (by decide) (by decide)).trans w7_1590
  have w8_1594 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = BitVec.ofNat 32 tl1.len := (K8.w32 (by decide) (by decide)).trans w7_1594
  have b8_a24 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := (K8.b8 (by decide) (by decide)).trans b7_a24
  have b8_a25 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K8.b8 (by decide) (by decide)).trans b7_a25
  have b8_a26 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K8.b8 (by decide) (by decide)).trans b7_a26
  have b8_a27 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K8.b8 (by decide) (by decide)).trans b7_a27
  have b8_158d : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K8.b8 (by decide) (by decide)).trans b7_158d
  have b8_158e : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K8.b8 (by decide) (by decide)).trans b7_158e
  have b8_158f : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K8.b8 (by decide) (by decide)).trans b7_158f
  have w8_1588 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = lp + BitVec.ofNat 32 tl1.header := by rw [W8, g7_8]
  clear b7_158f b7_158e b7_158d b7_a27 b7_a26 b7_a25 b7_a24 w7_1594 w7_1590 w7_a2c w7_a28 w7_a24 w7_a20 w7_2ec w7_2e8 w7_2e4 w7_2e0 g7_10 g7_27 g7_26 g7_25 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0xB2: sb
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sb F E8 s8 sv_at_b2 (off' := 0xB6) (c := 0x158C)
    (by decide) (by rw [g8_9]; sv_addr) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = n0.mem x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [rg9 (8 : Fin 32), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg9 (9 : Fin 32), g8_9]
  have g9_10 : reg n9 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg9 a0, g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = ((BitVec.ofNat 32 tl1.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg9 (20 : Fin 32), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = lp := by rw [rg9 (21 : Fin 32), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = dg := by rw [rg9 (22 : Fin 32), g8_22]
  have g9_25 : reg n9 (25 : Fin 32) = rootp := by rw [rg9 (25 : Fin 32), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = ll := by rw [rg9 (26 : Fin 32), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg9 (27 : Fin 32), g8_27]
  have w9_2e0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := (K9.w32 (by decide) (by decide)).trans w8_2e0
  have w9_2e4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := (K9.w32 (by decide) (by decide)).trans w8_2e4
  have w9_2e8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := (K9.w32 (by decide) (by decide)).trans w8_2e8
  have w9_2ec : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := (K9.w32 (by decide) (by decide)).trans w8_2ec
  have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := (K9.w32 (by decide) (by decide)).trans w8_a20
  have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := (K9.w32 (by decide) (by decide)).trans w8_a24
  have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := (K9.w32 (by decide) (by decide)).trans w8_a28
  have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := (K9.w32 (by decide) (by decide)).trans w8_a2c
  have w9_1588 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = lp + BitVec.ofNat 32 tl1.header := (K9.w32 (by decide) (by decide)).trans w8_1588
  have w9_1590 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = lp + BitVec.ofNat 32 tl1.header := (K9.w32 (by decide) (by decide)).trans w8_1590
  have w9_1594 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = BitVec.ofNat 32 tl1.len := (K9.w32 (by decide) (by decide)).trans w8_1594
  have b9_a24 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := (K9.b8 (by decide) (by decide)).trans b8_a24
  have b9_a25 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_a25
  have b9_a26 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_a26
  have b9_a27 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_a27
  have b9_158d : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_158d
  have b9_158e : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_158e
  have b9_158f : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_158f
  have b9_158c : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x158C) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [W9, g8_20, lbu_low]
  clear w8_1588 b8_158f b8_158e b8_158d b8_a27 b8_a26 b8_a25 b8_a24 w8_1594 w8_1590 w8_a2c w8_a28 w8_a24 w8_a20 w8_2ec w8_2e8 w8_2e4 w8_2e0 g8_27 g8_26 g8_25 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0xB6
  obtain ⟨n10, c10, u10⟩ := s9.block svL1b6 E9.self svL1b6_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0xB8 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svL1b6 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, SvR B x → n10.mem x = n0.mem x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by
    rw [rb10, runBlock_reg _ _ _ sp s9.zero (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (3 : Fin 32) s9.zero (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (4 : Fin 32) s9.zero (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_10 : reg n10 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = lp := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = dg := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_25 : reg n10 (25 : Fin 32) = rootp := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = ll := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svL1b6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | decide | sv_addr
  have w10_2e0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m10]; exact w9_2e0
  have w10_2e4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m10]; exact w9_2e4
  have w10_2e8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m10]; exact w9_2e8
  have w10_2ec : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m10]; exact w9_2ec
  have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := by rw [m10]; exact w9_a20
  have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m10]; exact w9_a24
  have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := by rw [m10]; exact w9_a28
  have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := by rw [m10]; exact w9_a2c
  have w10_1588 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = lp + BitVec.ofNat 32 tl1.header := by rw [m10]; exact w9_1588
  have w10_1590 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = lp + BitVec.ofNat 32 tl1.header := by rw [m10]; exact w9_1590
  have w10_1594 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = BitVec.ofNat 32 tl1.len := by rw [m10]; exact w9_1594
  have b10_a24 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m10]; exact b9_a24
  have b10_a25 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m10]; exact b9_a25
  have b10_a26 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m10]; exact b9_a26
  have b10_a27 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m10]; exact b9_a27
  have b10_158c : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x158C) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m10]; exact b9_158c
  have b10_158d : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m10]; exact b9_158d
  have b10_158e : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m10]; exact b9_158e
  have b10_158f : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m10]; exact b9_158f
  clear b9_158c b9_158f b9_158e b9_158d b9_a27 b9_a26 b9_a25 b9_a24 w9_1594 w9_1590 w9_1588 w9_a2c w9_a28 w9_a24 w9_a20 w9_2ec w9_2e8 w9_2e4 w9_2e0 g9_27 g9_26 g9_25 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  by_cases hz_10 : ll - BitVec.ofNat 32 (tl1.header + tl1.len) = 0
  rotate_left
  · -- the reader has bytes left
    -- 0xB8: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x966 sv_at_b8
      (by decide) (by rw [g10_10, s10.zero]; exact br_bne_t hz_10)
    have s11 : St n11.mem SV n11 0x966 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = n0.mem x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = lp := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = dg := by rw [u11.regs, g10_22]
    have g11_25 : reg n11 (25 : Fin 32) = rootp := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
    have w11_2e0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m11]; exact w10_2e0
    have w11_2e4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m11]; exact w10_2e4
    have w11_2e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_2e8
    have w11_2ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_2ec
    have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_a20
    have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_a24
    have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_a28
    have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_a2c
    have w11_1588 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_1588
    have w11_1590 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_1590
    have w11_1594 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_1594
    have b11_a24 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m11]; exact b10_a24
    have b11_a25 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m11]; exact b10_a25
    have b11_a26 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m11]; exact b10_a26
    have b11_a27 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m11]; exact b10_a27
    have b11_158c : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158C) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m11]; exact b10_158c
    have b11_158d : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m11]; exact b10_158d
    have b11_158e : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m11]; exact b10_158e
    have b11_158f : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m11]; exact b10_158f
    clear b10_158f b10_158e b10_158d b10_158c b10_a27 b10_a26 b10_a25 b10_a24 w10_1594 w10_1590 w10_1588 w10_a2c w10_a28 w10_a24 w10_a20 w10_2ec w10_2e8 w10_2e4 w10_2e0 g10_20 g10_27 g10_26 g10_25 g10_22 g10_21 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
    exact .inl ⟨(fun ⟨t', h', hz'⟩ => by rw [hr1] at h'; cases h'; exact hz_10 hz'), sv_fail F E11 s11 t11 fR11 V11 hret g11_2 g11_18 hO g11_3 g11_4⟩
  -- 0xB8: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0xBC sv_at_b8
    (by decide) (by rw [g10_10, s10.zero]; exact br_bne_f hz_10)
  have s11 : St n11.mem SV n11 0xBC (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = n0.mem x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by rw [u11.regs, g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u11.regs, g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = lp := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = dg := by rw [u11.regs, g10_22]
  have g11_25 : reg n11 (25 : Fin 32) = rootp := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
  have w11_2e0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m11]; exact w10_2e0
  have w11_2e4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m11]; exact w10_2e4
  have w11_2e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_2e8
  have w11_2ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m11]; exact w10_2ec
  have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_a20
  have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_a24
  have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_a28
  have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_a2c
  have w11_1588 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_1588
  have w11_1590 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = lp + BitVec.ofNat 32 tl1.header := by rw [m11]; exact w10_1590
  have w11_1594 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = BitVec.ofNat 32 tl1.len := by rw [m11]; exact w10_1594
  have b11_a24 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m11]; exact b10_a24
  have b11_a25 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m11]; exact b10_a25
  have b11_a26 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m11]; exact b10_a26
  have b11_a27 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m11]; exact b10_a27
  have b11_158c : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158C) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m11]; exact b10_158c
  have b11_158d : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m11]; exact b10_158d
  have b11_158e : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m11]; exact b10_158e
  have b11_158f : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m11]; exact b10_158f
  clear b10_158f b10_158e b10_158d b10_158c b10_a27 b10_a26 b10_a25 b10_a24 w10_1594 w10_1590 w10_1588 w10_a2c w10_a28 w10_a24 w10_a20 w10_2ec w10_2e8 w10_2e4 w10_2e0 g10_20 g10_27 g10_26 g10_25 g10_22 g10_21 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0xBC
  obtain ⟨n12, c12, u12⟩ := s11.block svL1bc E11.self svL1bc_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0xD0 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svL1bc (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans c12
  have fR12 : ∀ x, SvR B x → n12.mem x = n0.mem x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by
    rw [rb12, runBlock_reg _ _ _ sp s11.zero (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (3 : Fin 32) s11.zero (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (4 : Fin 32) s11.zero (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = lp + BitVec.ofNat 32 tl1.header := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = lp := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = dg := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_25 : reg n12 (25 : Fin 32) = rootp := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = ll := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svL1bc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | decide | sv_addr
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1588 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svL1bc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | decide | sv_addr
  have g12_12 : reg n12 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svL1bc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | decide | sv_addr
  have w12_2e0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp := by rw [m12]; exact w11_2e0
  have w12_2e4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll := by rw [m12]; exact w11_2e4
  have w12_2e8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m12]; exact w11_2e8
  have w12_2ec : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m12]; exact w11_2ec
  have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = lp + BitVec.ofNat 32 tl1.header := by rw [m12]; exact w11_a20
  have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m12]; exact w11_a24
  have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = lp + BitVec.ofNat 32 tl1.header := by rw [m12]; exact w11_a28
  have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl1.len := by rw [m12]; exact w11_a2c
  have w12_1588 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = lp + BitVec.ofNat 32 tl1.header := by rw [m12]; exact w11_1588
  have w12_1590 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = lp + BitVec.ofNat 32 tl1.header := by rw [m12]; exact w11_1590
  have w12_1594 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = BitVec.ofNat 32 tl1.len := by rw [m12]; exact w11_1594
  have b12_a24 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m12]; exact b11_a24
  have b12_a25 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m12]; exact b11_a25
  have b12_a26 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m12]; exact b11_a26
  have b12_a27 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m12]; exact b11_a27
  have b12_158c : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x158C) = (BitVec.ofNat 32 tl1.len).extractLsb' 0 8 := by rw [m12]; exact b11_158c
  have b12_158d : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 tl1.len).extractLsb' 8 8 := by rw [m12]; exact b11_158d
  have b12_158e : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 tl1.len).extractLsb' 16 8 := by rw [m12]; exact b11_158e
  have b12_158f : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 tl1.len).extractLsb' 24 8 := by rw [m12]; exact b11_158f
  clear b11_158f b11_158e b11_158d b11_158c b11_a27 b11_a26 b11_a25 b11_a24 w11_1594 w11_1590 w11_1588 w11_a2c w11_a28 w11_a24 w11_a20 w11_2ec w11_2e8 w11_2e4 w11_2e0 g11_27 g11_26 g11_25 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  exact .inr ⟨tl1, hr1, hz_10, n12, t12, s12, E12, V12, fR12, g12_2, g12_3, g12_4, g12_10, g12_11, g12_12, g12_18, g12_19, g12_22, g12_25, g12_27, w12_2e0, w12_2e4, w12_2e8, w12_2ec, w12_a20, w12_a24, w12_a28, w12_a2c, w12_1588, w12_1590, w12_1594, b12_a24, b12_a25, b12_a26, b12_a27, b12_158c, b12_158d, b12_158e, b12_158f⟩

end C3.RV32.Sv
